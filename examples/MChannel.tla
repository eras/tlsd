------------------------------ MODULE MChannel ------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC

CONSTANT Id
CONSTANT Data

VARIABLE channels

Null == <<>>

TypeOK == channels[Id] \in [val: Data \cup {Null}, busy: BOOLEAN]

Send(data) ==
   /\ Assert(data \in Data, <<"Sending invalid data", data, "while expecting", Data>>)
   /\ \lnot channels[Id].busy
   /\ channels' = [channels EXCEPT ![Id] = [@ EXCEPT !.val = data, !.busy = TRUE]]

Recv(data) ==
   /\ Assert(data \in Data, <<"Receiving invalid data", data, "while expecting", Data>>)
   /\ channels[Id].busy
   /\ data = channels[Id].val
   /\ channels' = [channels EXCEPT ![Id] = [@ EXCEPT !.val=Null, !.busy = FALSE]]

SendAction == \E data \in Data: Send(data)

ReceiveAction == \E data \in Data: Recv(data)

Next == SendAction \/ ReceiveAction

AliasSending(Ids) ==
   LET pending == {id \in Ids: channels[id].busy} IN
   [id \in pending |-> channels[id].val]

Alias(Ids) ==
   [sending |-> AliasSending(Ids)]

Reset(value) == [val |-> value, busy |-> FALSE]

=============================================================================
