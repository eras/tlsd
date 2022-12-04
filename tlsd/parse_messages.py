#!/usr/bin/env python3

import json
import fileinput
import re
import textwrap
from dataclasses import dataclass, field
from typing import *

import drawSvg as draw

state_id_re              = re.compile(r"^State ([0-9][0-9]*): <([^ ]*)")
variable_re              = re.compile(r"^(/\\ )?([^ ]*_json) = \"(.*)\"$")
quoted_dquote_re         = re.compile(r"\\\"")
error_starts_re          = re.compile(r"^Error: (.*)")
error_occurred_re        = re.compile(r"Error: The error occurred when TLC was evaluating the nested")

NodeId = Tuple[str, int]

# from https://github.com/python/typing/issues/182#issuecomment-899624078
if TYPE_CHECKING:
    class JSONArray(list[JSONType], Protocol):  # type: ignore
        __class__: Type[list[JSONType]]  # type: ignore

    class JSONObject(dict[str, JSONType], Protocol):  # type: ignore
        __class__: Type[dict[str, JSONType]]  # type: ignore

    JSONType = Union[None, int, float, str, JSONArray, JSONObject]
else:
    JSONType = Any

def make_node_id_key_comparison(node_comparison_values: Dict[str, int]):
    def node_id_key(node_id: NodeId) -> Tuple[Union[str, int], int]:
        if node_id[0] in node_comparison_values:
            return (node_comparison_values[node_id[0]], node_id[1])
        else:
            return node_id
    return node_id_key

class UnreadableInput:
    """An input that can unread lines. Lines pushed to the unread queue are
    returned next before consulting the underlying input."""
    _input: fileinput.FileInput
    _buffer: List[str]

    def __init__(self, stream: fileinput.FileInput) -> None:
        self._input = stream
        self._buffer = []

    def __iter__(self) -> "UnreadableInput":
        return self

    def unread(self, line: str):
        self._buffer.append(line)

    def has_unread(self) -> bool:
        return bool(self._buffer)

    def __next__(self) -> str:
        if self._buffer:
            return self._buffer.pop(0)
        else:
            return self._input.__next__()

class Environment:
    nodes      : Dict[NodeId, "Node"]
    lane_order : Dict[str, int]

    def __init__(self) -> None:
        self.nodes = {}
        self.lane_order = {}

    def get_node(self, node_id: NodeId) -> "Node":
        if node_id not in self.nodes:
            self.nodes[node_id] = Node(self, node_id)
        return self.nodes[node_id]

    def get_lane(self, node_id: NodeId) -> int:
        # slow :). could be cached.
        return [index
                for index, cur_node_id
                in enumerate(sorted(self.nodes.keys(), key=make_node_id_key_comparison(self.lane_order)))
                if node_id == cur_node_id][0]


Message = Dict[str, JSONType]
State = Dict[str, JSONType]

StateId = int

STATE_ID_WIDTH = 100
LANE_WIDTH     = 10
LANE_GAP       = 250
STATE_HEIGHT   = 80
STATE_WIDTH    = 160

@dataclass
class StateMessage:
    state_id: StateId
    message: Message

@dataclass
class MessageInfo:
    message: Message
    sent_at: StateId
    received_at: Optional[StateId]

@dataclass
class PeerReceived:
    peer: NodeId
    sent_at: StateId

@dataclass
class Diff:
    fragment: str
    different: bool = False # this was the smallest different component in the subtree

T = TypeVar("T")
def default(value: T, x: Optional[T]) -> T:
    if x is None:
        return value
    else:
        return x

U = TypeVar("U")
def invert_dict(kvs: Dict[T, U]) -> Dict[U, T]:
    result: Dict[U, T] = {}
    for key, value in kvs.items():
        result[value] = key
    return result

def compare(old: JSONType, new: JSONType) -> List[Diff]:
    diff = []
    if isinstance(old, dict) or isinstance(new, dict):
        if new is None:
            diff.append(Diff(fragment="None", different=True))
        else:
            assert(isinstance(default(old, {}), dict))
            assert(isinstance(new, dict))
            old2: Dict[str, JSONType] = {}
            if old is not None:
                assert(isinstance(old, dict))
                old2 = old
            first = True
            diff.append(Diff(fragment="{ "))
            assert(isinstance(new, dict))
            for key, new_value in new.items():
                if not first:
                    diff.append(Diff(fragment=", "))
                first = False
                diff.append(Diff(fragment=f"{key}:"))
                if key in old2:
                    old_value = old2[key]
                    diff.extend(compare(old_value, new_value))
                else:
                    diff.extend(compare(None, new_value))
            diff.append(Diff(fragment=" }"))
    elif isinstance(old, str) or isinstance(new, str):
        assert(isinstance(default(old, ""), str))
        # TODO: quoting
        if new is None:
            diff.append(Diff(fragment="None", different=True))
        else:
            assert(isinstance(new, str))
            diff.append(Diff(fragment="\"" + new + "\"",
                             different=old != new))
    elif isinstance(old, int) or isinstance(new, int):
        assert(isinstance(default(old, 0), int))
        assert(isinstance(default(new, 0), int))
        if new is None:
            diff.append(Diff(fragment="None", different=True))
        else:
            diff.append(Diff(fragment=str(new),
                             different=old != new))
    elif isinstance(old, list) or isinstance(new, list):
        assert(isinstance(default(old, []), list))
        assert(isinstance(default(new, []), list))
        assert False, f"Unsupported data type list: {old} vs {new}"
    else:
        assert False, f"Unsupported data type: {old} vs {new}"

    return diff

def json_to_tspans(data: Dict[str, JSONType], x: float) -> List[draw.TSpan]:
    lines = []
    for key, value in data.items():
        content = f"{key} = {json.dumps(value)}"
        for line in textwrap.wrap(content, width=30):
            lines.append(draw.TSpan(line, x=x, dy="1em"))
    return lines

def diff_to_tspans(diffs: List[Diff], x: float) -> List[draw.TSpan]:
    spans = []
    cur_line_len = 0
    max_len = 30
    for diff in diffs:
        do_wrap = len(diff.fragment) + cur_line_len > max_len
        font_style = "italic" if diff.different else "normal"
        if do_wrap:
            cur_line_len = 0
            spans.append(draw.TSpan(diff.fragment, x=x, dy="1.1em", font_style=font_style))
        else:
            cur_line_len += len(diff.fragment)
            spans.append(draw.TSpan(diff.fragment, font_style=font_style))
    return spans

class TextTSpans(draw.Text):
    def __init__(self, lines: List[draw.TSpan], fontSize: float, x: float, y: float, **kwargs) -> None:
        super().__init__([], fontSize, x, y, **kwargs)
        for line in lines:
            self.append(line)

def arrowSymbol():
    return draw.Lines(-0.1, -0.5, -0.1, 0.5, 0.9, 0, fill='green', close=True)

def crossSymbol():
    """
9  A             K
8 ...           ...
7B....         ....J
6 .....       .....
5  .....     .....
4   .....   .....
3    ..... . ...
2     ....L....
1      .......
0       C.*.I
1      .......
2     ....F....
3    ..... .....
4   .....   .....
5  .....     .....
6 .....       .....
7D....         ....H
8 ...           ...
9  E             G
 9876543210123456789
"""
    return draw.Lines(-0.9, 0.7,
                      -0.2, 0.0,
                      -0.9, -0.7,
                      -0.7, -0.9,
                      0.0, -0.2,
                      0.7, -0.9,
                      0.9, -0.7,
                      0.2, 0.0,
                      0.9, 0.7,
                      0.7, 0.9,
                      0.0, 0.2,
                      -0.7, 0.9,
                      fill='red', close=True)

class Node:
    node_id        : NodeId
    active_send    : Dict[NodeId, StateMessage]
    active_receive : Dict[NodeId, StateMessage]
    state_id_range : Optional[Tuple[StateId, StateId]]
    action_names   : Dict[StateId, str]
    env            : Environment
    messages_sent  : Dict[StateId, Dict[NodeId, MessageInfo]]
    states         : Dict[StateId, State]

    # used to map from state ids to their predecessors
    prev_state_id_cache : Optional[Dict[StateId, StateId]]

    def __init__(self, env: Environment, node_id: NodeId) -> None:
        self.env = env
        self.node_id = node_id
        self.active_send = {}
        self.active_receive = {}
        self.state_id_range = None
        self.action_names = {}
        self.messages_sent = {}
        self.states = {}
        self.prev_state_id_cache = None

    def prev_state_id(self, state_id: StateId) -> Optional[StateId]:
        if not self.prev_state_id_cache:
            self.prev_state_id_cache = {}
            prev: Optional[StateId] = None
            for key in sorted(self.states.keys()):
                if prev:
                    self.prev_state_id_cache[key] = prev
                prev = key
        return self.prev_state_id_cache.get(state_id)

    def prev_state(self, state_id: StateId) -> Optional[State]:
        prev_state_id = self.prev_state_id(state_id)
        if prev_state_id is not None:
            return self.states[prev_state_id]
        else:
            return None

    def update_state(self, state_id: StateId, state: State, action_name: str) -> None:
        self.prev_state_id_cache = None
        self.states[state_id] = state
        if self.states[state_id] != self.states.get(state_id - 1):
            self.action_names[state_id] = action_name

    def update_state_id_range(self, state_id: StateId) -> None:
        if self.state_id_range is None:
            self.state_id_range = (state_id, state_id)
        else:
            self.state_id_range = (self.state_id_range[0], state_id)

    def send_active(self, state_id: StateId, action_name: str, peer: NodeId, message: Message) -> None:
        self.update_state_id_range(state_id)
        if peer not in self.active_send:
            sent = StateMessage(state_id=state_id, message=message)
            print(f"st {state_id}\t{self.node_id}\tsends to\t{peer}\t@ st {sent.state_id}\t: {sent.message}")
            if not state_id in self.messages_sent:
                self.messages_sent[state_id] = {}
            self.action_names[state_id] = action_name
            self.messages_sent[state_id][peer] = MessageInfo(message=message,
                                                             sent_at=state_id,
                                                             received_at=None)
            self.active_send[peer] = sent
    def send_inactive(self, state_id: StateId, action_name: str, peer: NodeId) -> None:
        self.update_state_id_range(state_id)
        if peer in self.active_send:
            sent = self.active_send[peer]
            assert sent.state_id < state_id, f"Message received from {self.node_id} to {peer} in earlier state than it was sent. sent: {sent.state_id} now {state_id}. active sends: {self.active_send}"
            if sent.state_id in self.messages_sent and peer in self.messages_sent[sent.state_id]:
                self.messages_sent[sent.state_id][peer].received_at = state_id
            print(f"st {state_id}\t{peer}\trecvs from\t{self.node_id}\t@ st {sent.state_id}\t: {sent.message}")
            del self.active_send[peer]

    def recv_active(self, state_id: StateId, action_name: str, peer: NodeId, message: Message) -> None:
        self.update_state_id_range(state_id)
        if peer not in self.active_receive:
            received = StateMessage(state_id=state_id, message=message)
            self.active_receive[peer] = received
        #self.action_names[state_id] = action_name
        # TODO: maybe do something here?

    def recv_inactive(self, state_id: StateId, action_name: str, peer: NodeId) -> None:
        self.update_state_id_range(state_id)
        if peer in self.active_receive:
            received = self.active_receive[peer]
            del self.active_receive[peer]
            self.action_names[state_id] = action_name
        pass

    def draw_states(self, svg) -> None:
        self.draw_lane(svg)
        for state_id, _ in self.states.items():
            if (state_id in self.action_names or
                self.states[state_id] != self.states.get(state_id - 1)):
                self.draw_state(svg, state_id)

    def draw_transitions(self, svg) -> None:
        for state_id, messages in self.messages_sent.items():
            for peer, message_info in messages.items():
                self.draw_message(svg, state_id, self.env.get_node(peer), message_info)

    def lane(self) -> int:
        return self.env.get_lane(self.node_id)

    def lane_base_x(self) -> float:
        return STATE_ID_WIDTH + STATE_WIDTH + self.lane() * (LANE_WIDTH + LANE_GAP) + (LANE_WIDTH - STATE_WIDTH) / 2

    def draw_state(self, svg, state_id: StateId) -> None:
        state_x = self.lane_base_x()
        state_y = - ((state_id - 1) * STATE_HEIGHT + STATE_HEIGHT)
        svg.append(draw.Rectangle(state_x, state_y,
                                  STATE_WIDTH, STATE_HEIGHT,
                                  stroke='black', stroke_width='1',
                                  fill='white'))

        delta_y = -8

        if state_id in self.action_names:
            svg.append(draw.Text(self.action_names[state_id], 10,
                                 state_x + STATE_WIDTH / 2.0, state_y + STATE_HEIGHT + delta_y,
                                 text_anchor='middle', dominant_baseline='hanging'))
            delta_y -= 12

        state = self.states.get(state_id)
        if state is not None:
            prev_state = self.prev_state(state_id)
            x = state_x + STATE_WIDTH / 2.0
            diff = compare(convert_tla_function_to_json(prev_state),
                           convert_tla_function_to_json(state))
            svg.append(TextTSpans(diff_to_tspans(diff, x=x), 8,
                                  x, state_y + STATE_HEIGHT + delta_y,
                                  text_anchor='middle', dominant_baseline='hanging'))


    def draw_message(self, svg, state_id: StateId, peer: "Node", message_info: MessageInfo) -> None:
        arrow_right = self.lane_base_x() < peer.lane_base_x()
        adjust_source_x = STATE_WIDTH / 2 + 5
        adjust_peer_x = -STATE_WIDTH / 2 - 15
        if not arrow_right:
            adjust_source_x = -adjust_source_x
            adjust_peer_x = -adjust_peer_x
        arrow = draw.Marker(-0.1, -0.5, 0.9, 0.5, scale=15, orient='auto')

        if message_info.received_at is not None:
            arrow.append(arrowSymbol())
        else:
            arrow.append(crossSymbol())

        a = (self.lane_base_x() + STATE_WIDTH / 2 + adjust_source_x,
             - (((message_info.sent_at - 1) + 0.9) * STATE_HEIGHT))

        if message_info.received_at is not None:
            arrow_y = message_info.received_at - 1.0
        else:
            arrow_y = message_info.sent_at + 0.5

        b = (peer.lane_base_x() + STATE_WIDTH / 2 + adjust_peer_x,
             - ((arrow_y + 0.1) * STATE_HEIGHT))

        path = draw.Lines(a[0], a[1],
                          b[0], b[1],
                          close=False,
                          fill='#eeee00',
                          stroke='black',
                          marker_end=arrow)
        svg.append(path)

        x = (a[0] + b[0]) / 2
        svg.append(TextTSpans(json_to_tspans(message_info.message, x=x), 10,
                              x, (a[1] + b[1]) / 2,
                              text_anchor="middle"))

    def draw_lane(self, svg) -> None:
        assert self.state_id_range is not None
        state_id_min = self.state_id_range[0]
        state_id_max = self.state_id_range[1]
        height = (state_id_max - state_id_min + 1) * STATE_HEIGHT + 20
        base_x = STATE_ID_WIDTH + STATE_WIDTH + self.lane() * (LANE_WIDTH + LANE_GAP)
        svg.append(draw.Rectangle(base_x,
                                  - ((state_id_min - 1) * STATE_HEIGHT + height - 10),
                                  LANE_WIDTH, height,
                                  stroke='black', stroke_width='1',
                                  fill='none'))

        svg.append(draw.Text(f"{self.node_id}", 20,
                             base_x, -0 + 1,
                             text_anchor='middle'))

        if self.states.get(1):
            self.draw_state(svg, 1)

def unquote(s: str) -> str:
    return quoted_dquote_re.sub("\"", s)

def node_id_of(json: JSONType) -> NodeId:
    assert isinstance(json, list)
    assert len(json) == 2
    assert isinstance(json[0], str)
    assert isinstance(json[1], int)
    return (json[0], json[1])

def convert_tla_function_to_dict(data: Union[list, dict]) -> Dict[int, JSONType]:
    if isinstance(data, list):
        return {index + 1: data[index] for index in range(0, len(data))}
    elif isinstance(data, dict):
        return {int(key): data[key] for key in data.keys()}
    else:
        assert False, "Expected list or dict"

def convert_tla_function_to_json(data: JSONType) -> JSONType:
    if data is None:
        return None
    elif isinstance(data, int):
        return data
    elif isinstance(data, float):
        return data
    elif isinstance(data, str):
        return data
    elif isinstance(data, list):
        return {str(index + 1): convert_tla_function_to_json(data[index]) for index in range(0, len(data))}
    elif isinstance(data, dict):
        return {key: convert_tla_function_to_json(data[key]) for key in data.keys()}
    else:
        assert False, f"Unexpected data: {data}"

@dataclass
class Data:
    env      : Environment
    state_id : StateId
    error    : List[str]

def process_state(env: Environment, state_id: int, action_name: str, json: JSONType) -> None:
    assert isinstance(json, dict)
    for name, nodes in json.items():
        assert isinstance(nodes, dict) or isinstance(nodes, list)
        for index, state in convert_tla_function_to_dict(nodes).items():
            node_id = node_id_of([name, index])
            assert isinstance(state, dict), f"Expected dictionary but got {state}"
            env.get_node(node_id).update_state(state_id, state, action_name)

def process_messages(env: Environment, state_id: int, action_name: str, json: JSONType) -> None:
    messages: Dict[Tuple[NodeId, NodeId], Message] = {}
    assert isinstance(json, list)
    for message in json:
        # developer convenience to filter these empty messages here
        if not message or not message[0]:
            continue
        assert isinstance(message, list) and len(message) == 1 and isinstance(message[0], list) and len(message[0]) == 3, \
            f"Expected message be of structure [[from, id], [to, id], message], got {message}"
        source = node_id_of(message[0][0])
        target = node_id_of(message[0][1])
        # print(f"chan: {chan} sending: {sending} index: {index} message[0]: {message[0]}")
        # print(f"  {source}->{target} message[0]: {message[0]}")
        messages[(source, target)] = message[0][2]
        env.get_node(source)
        env.get_node(target)
    for source in env.nodes.keys():
        for target in env.nodes.keys():
            if (source, target) not in messages:
                # print(f"source={source}, target={target}")
                env.get_node(source).send_inactive(state_id, action_name, target)
                env.get_node(target).recv_inactive(state_id, action_name, source)

    # actually there is no causality in the TLA+ model, but IRL there is :)
    for source in env.nodes.keys():
        for target in env.nodes.keys():
            if (source, target) in messages:
                message = messages[(source, target)]
                env.get_node(source).send_active(state_id, action_name, target, message)
                env.get_node(target).recv_active(state_id, action_name, source, message)

def process_lane_order(env: Environment, json: JSONType) -> None:
    def is_list(json: JSONType) -> list:
        assert isinstance(json, list)
        return json
    def is_str(json: JSONType) -> str:
        assert isinstance(json, str)
        return json
    env.lane_order = {is_str(json): index for index, json in convert_tla_function_to_dict(is_list(json)).items()}

def read_variables(env: Environment, state_id: int, action_name: str, input: UnreadableInput):
    """Reads the variables of one state"""
    variables: Dict[str, JSONType] = {}
    for orig_line in input:
        line = orig_line.rstrip()
        variable_match = variable_re.match(line)

        if variable_match:
            variables[variable_match[2]] = json.loads(unquote(variable_match[3]))
        else:
            input.unread(orig_line)
            break

    if "lane_order_json" in variables:
        process_lane_order(env, variables["lane_order_json"])
    if "state_json" in variables:
        process_state(env, state_id, action_name, variables["state_json"])
    if "messages_json" in variables:
        process_messages(env, state_id, action_name, variables["messages_json"])

def process_data(input: UnreadableInput) -> Optional[Data]:
    env = Environment()

    state_id = None
    error: List[str] = []
    error_handled = False
    for orig_line in input:
        line = orig_line.rstrip()
        state_id_match = state_id_re.match(line)
        if state_id_match:
            state_id = int(state_id_match[1])
            action_name = state_id_match[2]

            read_variables(env, state_id, action_name, input)

        if state_id is None and not error_handled:
            if error == []:
                error_match = error_starts_re.match(line)
                if error_match:
                    error.append(error_match[1])
            else:
                error_match = error_starts_re.match(line)
                if error_match:
                    error_handled = True
                else:
                    error.append(line)

        if state_id is not None and \
           error_starts_re.match(line) and \
           not error_occurred_re.match(line):
            input.unread(orig_line)
            break

    if state_id is None:
        return None
    else:
        return Data(env=env, state_id=state_id, error=error)

def draw_data(filename: str, data: Data) -> None:
    env = data.env
    height = STATE_HEIGHT * (data.state_id + 1)
    svg = draw.Drawing(STATE_ID_WIDTH + (LANE_WIDTH + LANE_GAP) * len(env.nodes),
                       height + 20 + 100,
                       origin=(0, -height), displayInline=False)
    svg.append(draw.Rectangle(0, -svg.height + (20 + 100), svg.width, svg.height, stroke='none', fill='white'))

    svg.append(draw.Text(data.error, 20,
                         svg.width / 2.0, STATE_HEIGHT,
                         text_anchor='middle', valign='middle'))

    for cur_state_id in range(1, data.state_id + 1):
        svg.append(draw.Rectangle(0, -(cur_state_id * STATE_HEIGHT),
                                  STATE_ID_WIDTH, STATE_HEIGHT,
                                  stroke='black', stroke_width='1',
                                  fill='none'))
        svg.append(draw.Text(f"State {cur_state_id}", 20,
                             STATE_ID_WIDTH / 2, -((cur_state_id - 0.5) * STATE_HEIGHT),
                             text_anchor='middle', valign='middle'))


    for source in env.nodes.values():
        source.draw_states(svg)
    for source in env.nodes.values():
        source.draw_transitions(svg)

    print(f"Saved {filename}")
    svg.saveSvg(filename)

def main():
    input = UnreadableInput(fileinput.input())
    count = 0
    while True:
        results = process_data(input)
        more_data = input.has_unread()
        multiple = more_data or count
        if results is not None:
            filename = "sequence" + (f"-{(count+1):04}" if multiple else "") + ".svg"
            draw_data(filename, results)
        else:
            print("No applicable input?")
        if not more_data:
            break
        count += 1
