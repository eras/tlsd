------------------------------ MODULE MChannel ------------------------------

(* MChannel is an synchronous channel between with a buffer of at most
   one message.

   The state is stored in the channels function. Channels maps via Id to the
   actual channels.

   Copyright 2022 Erkki Seppälä <erkki.seppala@vincit.fi>
*)

----------------------------------------------------------------------------
LOCAL INSTANCE TLC              (* Assert *)

CONSTANT Id                     (* Id is used to find this instance from channels *)
CONSTANT Data                   (* Data constrains the kind of messages this module processes*)

VARIABLE channels               (* A function of channels: [Id -> Channel] *)

(* When a channel is not busy, it has this value. Redundant really to
   have the 'busy' flag at all, but maybe it makes things more clear
*)
Null == <<>>

Channel == [val: Data \cup {Null}, busy: BOOLEAN]

TypeOK == channels[Id] \in Channel

Send(data) ==
   /\ Assert(data \in Data, <<"Sending invalid data", data, "while expecting", Data>>)
   /\ \lnot channels[Id].busy
   /\ channels' = [channels EXCEPT ![Id] = [@ EXCEPT !.val = data, !.busy = TRUE]]

Recv(data) ==
   /\ Assert(data \in Data, <<"Receiving invalid data", data, "while expecting", Data>>)
   /\ channels[Id].busy
   /\ data = channels[Id].val
   /\ channels' = [channels EXCEPT ![Id] = [@ EXCEPT !.val=Null, !.busy = FALSE]]

AliasSending(Ids) ==
   LET pending == {id \in Ids: channels[id].busy} IN
   [id \in pending |-> channels[id].val]

Alias(Ids) ==
   [sending |-> AliasSending(Ids)]

InitValue == [val |-> Null, busy |-> FALSE]

=============================================================================
