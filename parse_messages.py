#!/usr/bin/env python3

import json
import fileinput
import re
import textwrap
from dataclasses import dataclass
from typing import *

import drawSvg as draw

state_id_re              = re.compile(r"^State ([0-9][0-9]*): <([^ ]*)")
messages_re              = re.compile(r"^(/\\ )messages_json = \"(.*)\"$")
state_re                 = re.compile(r"^(/\\ )state_json = \"(.*)\"$")
quoted_dquote_re         = re.compile(r"\\\"")
channel_source_target_re = re.compile(r"^chans_([^_]*)_to_([^_]*)$")
error_starts_re          = re.compile(r"^Error: (.*)")

NodeId = Tuple[str, int]

node_comparison_values = {"client":0, "as": 1, "ms": 2, "mc": 3}

# from https://github.com/python/typing/issues/182#issuecomment-899624078
if TYPE_CHECKING:
    class JSONArray(list[JSONType], Protocol):  # type: ignore
        __class__: Type[list[JSONType]]  # type: ignore

    class JSONObject(dict[str, JSONType], Protocol):  # type: ignore
        __class__: Type[dict[str, JSONType]]  # type: ignore

    JSONType = Union[None, int, float, str, JSONArray, JSONObject]
else:
    JSONType = Any

def node_id_key(node_id: NodeId) -> Tuple[Union[str, int], int]:
    if node_id[0] in node_comparison_values:
        return (node_comparison_values[node_id[0]], node_id[1])
    else:
        return node_id

class Environment:
    nodes: Dict[NodeId, "Node"]

    def __init__(self) -> None:
        self.nodes = {}

    def get_node(self, node_id: NodeId) -> "Node":
        if node_id not in self.nodes:
            self.nodes[node_id] = Node(self, node_id)
        return self.nodes[node_id]

    def get_lane(self, node_id: NodeId) -> int:
        # slow :). could be cached.
        return [index
                for index, cur_node_id
                in enumerate(sorted(self.nodes.keys(), key=node_id_key))
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

def json_to_tspans(data: Dict[str, JSONType], x: float) -> List[draw.TSpan]:
    lines = []
    for key, value in data.items():
        content = f"{key} = {json.dumps(value)}"
        for line in textwrap.wrap(content, width=30):
            lines.append(draw.TSpan(line, x=x, dy="1em"))
    return lines

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
    state_names    : Dict[StateId, str]
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
        self.state_names = {}
        self.messages_sent = {}
        self.states = {}
        self.prev_state_id_cache = None

    def prev_state_id(self, state_id: StateId) -> Optional[StateId]:
        if not self.prev_state_id_cache:
            self.prev_state_id_cache = {}
            prev = None
            for key in sorted(self.states.keys()):
                if prev:
                    # mypy gets confused here with warn_unreachable
                    self.prev_state_id_cache[key] = prev # type: ignore
                prev = key
        return self.prev_state_id_cache.get(state_id)

    def prev_state(self, state_id: StateId) -> Optional[State]:
        prev_state_id = self.prev_state_id(state_id)
        if prev_state_id is not None:
            return self.states[prev_state_id]
        else:
            return None

    def update_state(self, state_id: StateId, state: State) -> None:
        self.prev_state_id_cache = None
        self.states[state_id] = state

    def update_state_id_range(self, state_id: StateId) -> None:
        if self.state_id_range is None:
            self.state_id_range = (state_id, state_id)
        else:
            self.state_id_range = (self.state_id_range[0], state_id)

    def send_active(self, state_id: StateId, state_name: str, peer: NodeId, message: Message) -> None:
        self.update_state_id_range(state_id)
        if peer not in self.active_send:
            sent = StateMessage(state_id=state_id, message=message)
            print(f"st {state_id}\t{self.node_id}\tsends to\t{peer}\t@ st {sent.state_id}\t: {sent.message}")
            if not state_id in self.messages_sent:
                self.messages_sent[state_id] = {}
            self.state_names[state_id] = state_name
            self.messages_sent[state_id][peer] = MessageInfo(message=message,
                                                             sent_at=state_id,
                                                             received_at=None)
            self.active_send[peer] = sent
    def send_inactive(self, state_id: StateId, state_name: str, peer: NodeId) -> None:
        self.update_state_id_range(state_id)
        if peer in self.active_send:
            sent = self.active_send[peer]
            assert sent.state_id < state_id, f"Message received from {self.node_id} to {peer} in earlier state than it was sent. sent: {sent.state_id} now {state_id}. active sends: {self.active_send}"
            if sent.state_id in self.messages_sent and peer in self.messages_sent[sent.state_id]:
                self.messages_sent[sent.state_id][peer].received_at = state_id
            print(f"st {state_id}\t{peer}\trecvs from\t{self.node_id}\t@ st {sent.state_id}\t: {sent.message}")
            del self.active_send[peer]

    def recv_active(self, state_id: StateId, state_name: str, peer: NodeId, message: Message) -> None:
        self.update_state_id_range(state_id)
        if peer not in self.active_receive:
            received = StateMessage(state_id=state_id, message=message)
            self.active_receive[peer] = received
        #self.state_names[state_id] = state_name
        # TODO: maybe do something here?

    def recv_inactive(self, state_id: StateId, state_name: str, peer: NodeId) -> None:
        self.update_state_id_range(state_id)
        if peer in self.active_receive:
            received = self.active_receive[peer]
            del self.active_receive[peer]
            self.state_names[state_id] = state_name
        pass

    def draw_states(self, svg) -> None:
        self.draw_lane(svg)
        for state_id, _ in self.state_names.items():
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

        if state_id in self.state_names:
            svg.append(draw.Text(self.state_names[state_id], 10,
                                 state_x + STATE_WIDTH / 2.0, state_y + STATE_HEIGHT + delta_y,
                                 text_anchor='middle', dominant_baseline='hanging'))
            delta_y -= 12

        state = self.states.get(state_id)
        if state is not None and state != self.prev_state(state_id):
            x = state_x + STATE_WIDTH / 2.0
            svg.append(TextTSpans(json_to_tspans(state, x=x), 8,
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

def node_id_of(name: str, index: int) -> NodeId:
    return (name, index)

def convert_tla_function_json(data: Union[list, dict]) -> Dict[int, Message]:
    if isinstance(data, list):
        return {index + 1: data[index] for index in range(0, len(data))}
    elif isinstance(data, dict):
        return {int(key): data[key] for key in data.keys()}
    else:
        assert False, "Expected list or dict"


@dataclass
class Data:
    env      : Environment
    state_id : StateId
    error    : List[str]

def process_data() -> Optional[Data]:
    env = Environment()

    state_id = None
    error: List[str] = []
    error_handled = False
    for line in fileinput.input():
        line = line.rstrip()
        state_id_match = state_id_re.match(line)
        if state_id_match:
            state_id = int(state_id_match[1])
            state_name = state_id_match[2]

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

        state_match = state_re.match(line)
        if state_match and state_id is not None:
            state_cur = json.loads(unquote(state_match[2]))
            for name, nodes in state_cur.items():
                for index, state in convert_tla_function_json(nodes).items():
                    node_id = node_id_of(name, index)
                    env.get_node(node_id).update_state(state_id, state)

        messages_match = messages_re.match(line)
        if messages_match and state_id is not None:
            messages_cur = json.loads(unquote(messages_match[2]))
            # print(f"state {state_id}")
            messages: Dict[Tuple[NodeId, NodeId], Message] = {}
            for chan, data in messages_cur.items():
                channel_source_target_match = channel_source_target_re.match(chan)
                assert channel_source_target_match is not None, "Failed to parse source/target name"
                sending = data['sending']
                if sending:
                    # print(f"sending: {sending}")
                    for index, message in convert_tla_function_json(sending).items():
                        source = node_id_of(channel_source_target_match[1], index)
                        target = node_id_of(channel_source_target_match[2], index)
                        # print(f"chan: {chan} sending: {sending} index: {index} message: {message}")
                        # print(f"  {source}->{target} message: {message}")
                        messages[(source, target)] = message
                        env.get_node(source)
                        env.get_node(target)
            for source in env.nodes.keys():
                for target in env.nodes.keys():
                    if (source, target) not in messages:
                        # print(f"source={source}, target={target}")
                        env.get_node(source).send_inactive(state_id, state_name, target)
                        env.get_node(target).recv_inactive(state_id, state_name, source)

            # actually there is no causality in the TLA+ model, but IRL there is :)
            for source in env.nodes.keys():
                for target in env.nodes.keys():
                    if (source, target) in messages:
                        message = messages[(source, target)]
                        env.get_node(source).send_active(state_id, state_name, target, message)
                        env.get_node(target).recv_active(state_id, state_name, source, message)

    if state_id is None:
        return None
    else:
        return Data(env=env, state_id=state_id, error=error)

def draw_data(data: Data) -> None:
    env = data.env
    height = STATE_HEIGHT * (data.state_id + 1)
    svg = draw.Drawing(STATE_ID_WIDTH + (LANE_WIDTH + LANE_GAP) * len(env.nodes),
                       height + 20 + 100,
                       origin=(0, -height), displayInline=False)
    svg.append(draw.Rectangle(0, 0, svg.width, svg.height, stroke='none', fill='white'))

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

    svg_filename = "sequence.svg"
    png_filename = "sequence.png"
    print(f"Saved {svg_filename}")
    svg.saveSvg(svg_filename)
    print(f"Saved {png_filename}")
    svg.savePng(png_filename)

results = process_data()
if results is not None:
    draw_data(results)
else:
    print("No applicable input?")
