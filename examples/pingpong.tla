---- MODULE pingpong -----------------------------------------------------------

(* pingpong is a model where there exists one server and multiple
   clients. The server my send the clients a "ping" message, which
   they will always respond with a "pong" message.

   Once NumberOfPings pings have been sent and the same number of
   pongs have been received by the server, is the INVARIANT
   NotFinished violated and a state trace is produced. The state trace
   is transformed from the actual system state via the ALIAS
   AliasMessage, which only shows the messages in a format expected by
   the tool.

   Copyright 2022 Erkki Seppälä <erkki.seppala@vincit.fi>
*)

--------------------------------------------------------------------------------

LOCAL INSTANCE Naturals         (* .. *)
LOCAL INSTANCE Json             (* ToJson *)

CONSTANT
   NumberOfClients
   (* Number of pings the server sends and receives before we consider the
      scenario Finished *)
 , NumberOfPings

VARIABLES
   server_to_client             (* channels from the server to the clients *)
 , client_to_server             (* channels from the clients to the server *)
 , num_pings_sent               (* number of pings sent by the server *)
 , num_pongs_received           (* number of pongs received by the server *)

ClientIds == 1..NumberOfClients

vars == <<server_to_client, client_to_server, num_pings_sent, num_pongs_received>>

Data == [message: {"ping"}] \cup [message: {"pong"}]

(* Channels for messages from the server to the clients *)
ServerToClientChannel(Id) == INSTANCE MChannel WITH channels <- server_to_client
(* Channels for messages from the clients to the server *)
ClientToServerChannel(Id) == INSTANCE MChannel WITH channels <- client_to_server

(* Server sends ping to a client *)
ServerSendPing ==
   /\ \E client_id \in ClientIds:
      ServerToClientChannel(client_id)!Send([message |-> "ping"])
   /\ num_pings_sent' = num_pings_sent + 1
   /\ UNCHANGED<<client_to_server, num_pongs_received>>

(* Server receives a ping from a client *)
ServerHandlePong ==
   /\ \E client_id \in ClientIds:
      /\ ClientToServerChannel(client_id)!Recv([message |-> "pong"])
   /\ num_pongs_received' = num_pongs_received + 1
   /\ UNCHANGED<<server_to_client, num_pings_sent>>

(* Handle pings one client at a time: upon receiving ping, respond with pong *)
ClientHandlePing(client_id) ==
   /\ ServerToClientChannel(client_id)!Recv([message |-> "ping"])
   /\ ClientToServerChannel(client_id)!Send([message |-> "pong"])
   /\ UNCHANGED<<num_pings_sent, num_pongs_received>>

Next ==
   \/ ServerSendPing
   \/ ServerHandlePong
   \/ \E client_id \in ClientIds:
      ClientHandlePing(client_id)

Init ==
   /\ server_to_client = [client_id \in ClientIds |-> ServerToClientChannel(client_id)!InitValue]
   /\ client_to_server = [client_id \in ClientIds |-> ClientToServerChannel(client_id)!InitValue]
   /\ num_pings_sent = 0
   /\ num_pongs_received = 0

Spec ==
   /\ Init
   /\ [][Next]_vars

TypeOK ==
   /\ num_pings_sent \in Nat
   /\ num_pongs_received \in Nat
   /\ \A client_id \in ClientIds:
      /\ ServerToClientChannel(client_id)!TypeOK
      /\ ClientToServerChannel(client_id)!TypeOK

Finished ==
   /\ num_pings_sent = num_pongs_received
   /\ num_pings_sent = NumberOfPings

NotFinished == \lnot Finished

AliasMessage == [messages_json |-> ToJson([
                   chans_server_to_client |-> ServerToClientChannel(1)!Alias(ClientIds),
                   chans_client_to_server |-> ClientToServerChannel(1)!Alias(ClientIds)])]

================================================================================
