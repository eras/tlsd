---- MODULE pingpong -----------------------------------------------------------
LOCAL INSTANCE Naturals         (* .. *)
LOCAL INSTANCE Json             (* ToJson *)
LOCAL INSTANCE TLC              (* PrintT *)

CONSTANT
   NumberOfClients
 , NumberOfPings

VARIABLES
   server_to_client
 , client_to_server
 , num_pings_sent
 , num_pongs_received

ClientIds == 1..NumberOfClients

vars == <<server_to_client, client_to_server, num_pings_sent, num_pongs_received>>

Data == [message: {"ping"}] \cup [message: {"pong"}]

(* Channels for messages from the server to the clients *)
ServerToClientChannel(Id) == INSTANCE MChannel WITH channels <- server_to_client
(* Channel for messages from the clients to the server *)
ClientToServerChannel(Id) == INSTANCE MChannel WITH channels <- client_to_server

(* Server sends ping to a client *)
SendPing ==
   /\ \E client_id \in ClientIds:
      ServerToClientChannel(client_id)!Send([message |-> "ping"])
   /\ num_pings_sent' = num_pings_sent + 1
   /\ UNCHANGED<<client_to_server, num_pongs_received>>

(* Server receives a ping from a client *)
HandlePong ==
   /\ \E client_id \in ClientIds:
      /\ ClientToServerChannel(client_id)!Recv([message |-> "pong"])
   /\ num_pongs_received' = num_pongs_received + 1
   /\ UNCHANGED<<server_to_client, num_pings_sent>>

(* Handle pings one client at a time *)
HandlePings ==
   /\ \E client_id \in ClientIds:
      /\ ServerToClientChannel(client_id)!Recv([message |-> "ping"])
      /\ ClientToServerChannel(client_id)!Send([message |-> "pong"])
   /\ UNCHANGED<<num_pings_sent, num_pongs_received>>

Next ==
   \/ SendPing
   \/ HandlePong
   \/ HandlePings

Init ==
   /\ server_to_client = [client_id \in ClientIds |-> ServerToClientChannel(client_id)!Reset(<<>>)]
   /\ client_to_server = [client_id \in ClientIds |-> ClientToServerChannel(client_id)!Reset(<<>>)]
   /\ num_pings_sent = 0
   /\ num_pongs_received = 0

Finished ==
   /\ num_pings_sent = num_pongs_received
   /\ num_pings_sent = NumberOfPings

NotFinished == \lnot Finished

Spec ==
   /\ Init
   /\ [][Next]_vars

AliasMessage == [messages_json |-> ToJson([
                   chans_server_to_client |-> ServerToClientChannel(1)!Alias(ClientIds),
                   chans_client_to_server |-> ClientToServerChannel(1)!Alias(ClientIds)])]

================================================================================
