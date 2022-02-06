#!/usr/bin/env python3

import json
import fileinput
import re
import textwrap
from dataclasses import dataclass
from typing import *

import drawSvg as draw

state_re = re.compile(r"^State ([0-9][0-9]*): <([^ ]*)")
messages_re = re.compile(r"^messages_json = \"(.*)\"$")
quoted_dquote_re = re.compile(r"\\\"")
channel_source_target_re = re.compile(r"^chans_([^_]*)_to_([^_]*)$")

NodeId = Tuple[str, int]

class Environment:
    nodes: Dict[NodeId, "Node"]
    next_lane: int

    def __init__(self) -> None:
        self.nodes = {}
        self.next_lane = 0

    def get_node(self, node_id: NodeId) -> "Node":
        if node_id not in self.nodes:
            self.nodes[node_id] = Node(self, node_id, self.next_lane)
            self.next_lane += 1
        return self.nodes[node_id]

# TODO: determine a bit more precise type.
Message = Dict[str, Any]

StateId = int

STATE_ID_WIDTH = 100
LANE_WIDTH     = 10
LANE_GAP       = 300
STATE_HEIGHT   = 50
STATE_WIDTH    = 80

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

def split_string(s: str, len: int) -> List[str]:
    return textwrap.wrap(s, width=len)

def arrowSymbol():
    return draw.Lines(-0.1, -0.5, -0.1, 0.5, 0.9, 0, fill='green', close=True)

def crossSymbol():
    """
9  x             x
8 xxx           xxx
7xxxxx         xxxxx
6 xxxxx       xxxxx
5  xxxxx     xxxxx
4   xxxxx   xxxxx
3    xxxxx x xxx
2     xxxxxxxxx
1      xxxxxxx
0       xxOxx
1      xxxxxxx
2     xxxxxxxxx
3    xxxxx xxxxx
4   xxxxx   xxxxx
5  xxxxx     xxxxx
6 xxxxx       xxxxx
7xxxxx         xxxxx
8 xxx           xxx
9  x             x
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
    state_id_range : Optional[Tuple[StateId, StateId]]
    state_names    : Dict[StateId, str]
    env            : Environment
    messages_sent  : Dict[StateId, Dict[NodeId, MessageInfo]]

    def __init__(self, env: Environment, node_id: NodeId, lane: int) -> None:
        self.env = env
        self.node_id = node_id
        self.active_send = {}
        self.lane = lane
        self.state_id_range = None
        self.state_names = {}
        self.messages_sent = {}

    def update_state_id_range(self, state_id: StateId) -> None:
        if self.state_id_range is None:
            self.state_id_range = (state_id, state_id)
        else:
            self.state_id_range = (self.state_id_range[0], state_id)

    def send_active(self, state_id: StateId, state_name: str, peer: NodeId, message: Message) -> None:
        self.update_state_id_range(state_id)
        if not peer in self.active_send:
            sent = StateMessage(state_id=state_id, message=message)
            print(f"{self.node_id}\tsends to\t{peer}\t@ state {sent.state_id}\t: {sent.message}")
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
            if sent.state_id in self.messages_sent and peer in self.messages_sent[sent.state_id]:
                self.messages_sent[sent.state_id][peer].received_at = state_id
            print(f"{peer}\trecvs from\t{self.node_id}\t@ state {sent.state_id}\t: {sent.message}")
            del self.active_send[peer]

    def recv_active(self, state_id: StateId, state_name: str, peer: NodeId, message: Message) -> None:
        self.update_state_id_range(state_id)
        #self.state_names[state_id] = state_name
        # TODO: maybe do something here?

    def recv_inactive(self, state_id: StateId, state_name: str, peer: NodeId) -> None:
        self.update_state_id_range(state_id)
        # TODO: maybe do something here?
        pass

    def draw(self, svg) -> None:
        self.draw_lane(svg)
        for state_id, _ in self.state_names.items():
            self.draw_state(svg, state_id)
        for state_id, messages in self.messages_sent.items():
            for peer, message_info in messages.items():
                self.draw_message(svg, state_id, self.env.get_node(peer), message_info)

    def lane_base_x(self) -> float:
        return STATE_ID_WIDTH + LANE_GAP / 2 + self.lane * (LANE_WIDTH + LANE_GAP) + (LANE_WIDTH - STATE_WIDTH) / 2

    def draw_state(self, svg, state_id: StateId) -> None:
        state_x = self.lane_base_x()
        state_y = - ((state_id - 1) * STATE_HEIGHT + STATE_HEIGHT)
        svg.append(draw.Rectangle(state_x, state_y,
                                  STATE_WIDTH, STATE_HEIGHT,
                                  stroke='black', stroke_width='1',
                                  fill='white'))

        svg.append(draw.Text(self.state_names[state_id], 10,
                             state_x + STATE_WIDTH / 2.0, state_y + STATE_HEIGHT / 2.0,
                             text_anchor='middle'))


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

        contents = split_string(json.dumps(message_info.message), len=40)
        svg.append(draw.Text(contents, 10, (a[0] + b[0]) / 2, (a[1] + b[1]) / 2, text_anchor="middle"))

    def draw_lane(self, svg) -> None:
        assert self.state_id_range is not None
        state_id_min = self.state_id_range[0]
        state_id_max = self.state_id_range[1]
        height = (state_id_max - state_id_min + 1) * STATE_HEIGHT + 20
        base_x = STATE_ID_WIDTH + LANE_GAP / 2 + self.lane * (LANE_WIDTH + LANE_GAP)
        svg.append(draw.Rectangle(base_x,
                                  - ((state_id_min - 1) * STATE_HEIGHT + height - 10),
                                  LANE_WIDTH, height,
                                  stroke='black', stroke_width='1',
                                  fill='none'))

        svg.append(draw.Text(f"{self.node_id}", 20,
                             base_x, -0 + 1,
                             text_anchor='middle'))


env = Environment()

def unquote(s: str) -> str:
    return quoted_dquote_re.sub("\"", s)

def node_id_of(name: str, index: int) -> NodeId:
    if name == "as":
        return ("as", 0)
    else:
        return (name, index)

def convert_tla_function_json(data: Union[list, dict]) -> Dict[int, Message]:
    if isinstance(data, list):
        return {index + 1: data[index] for index in range(0, len(data))}
    elif isinstance(data, dict):
        return {int(key): data[key] for key in data.keys()}
    else:
        assert False, "Expected list or dict"


def process_data():
    state_id = None
    for line in fileinput.input():
        line = line.rstrip()
        state_match = state_re.match(line)
        if state_match:
            state_id = int(state_match[1])
            state_name = state_match[2]

        messages_match = messages_re.match(line)
        if messages_match:
            messages_cur = json.loads(unquote(messages_match[1]))
            # print(f"state {state_id}")
            for chan, data in messages_cur.items():
                channel_source_target_match = channel_source_target_re.match(chan)
                assert channel_source_target_match is not None, "Failed to parse source/target name"
                sending = data['sending']
                if sending:
                    # print(f"sending: {sending}")
                    messages: Dict[Tuple[NodeId, NodeId], Tuple[int, Message]] = {}
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
                                env.get_node(source).send_inactive(state_id, state_name, target)
                                env.get_node(target).recv_inactive(state_id, state_name, source)

                    # actually there is no causality in the TLA+ model, but IRL there is :)
                    for source in env.nodes.keys():
                        for target in env.nodes.keys():
                            if (source, target) in messages:
                                message = messages[(source, target)]
                                env.get_node(source).send_active(state_id, state_name, target, message)
                                env.get_node(target).recv_active(state_id, state_name, source, message)
    if state_id is not None:
        height = STATE_HEIGHT * (state_id + 1)
        svg = draw.Drawing((LANE_WIDTH + LANE_GAP) * (len(env.nodes) + 1),
                           height + 20 + 100,
                           origin=(0, -height), displayInline=False)
        svg.append(draw.Rectangle(0, 0, svg.width, svg.height, stroke='none', fill='white'))
        for cur_state_id in range(1, state_id + 1):
            svg.append(draw.Rectangle(0, -(cur_state_id * STATE_HEIGHT),
                                      STATE_ID_WIDTH, STATE_HEIGHT,
                                      stroke='black', stroke_width='1',
                                      fill='none'))
            svg.append(draw.Text(f"State {cur_state_id}", 20,
                                 STATE_ID_WIDTH / 2, -((cur_state_id - 0.5) * STATE_HEIGHT),
                                 text_anchor='middle', valign='middle'))


        for source in env.nodes.values():
            source.draw(svg)

        svg_filename = "sequence.svg"
        png_filename = "sequence.png"
        print(f"Saved {svg_filename}")
        svg.saveSvg(svg_filename)
        print(f"Saved {png_filename}")
        svg.savePng(png_filename)
    else:
        print("No applicable input?")

process_data()
