------------------------------ MODULE samutex ------------------------------
EXTENDS Naturals
CONSTANTS Processes

VARIABLES sent, received, in_cs, self_t
vars == <<sent, received, in_cs, self_t>>

Times == {0, 1}\*Nat

Send(m) == sent' = [sent EXCEPT ![m.from] = sent[m.from] \cup {m}]
Receive(m, p) ==
  /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
  /\ p \in m.to

Greater(m1, m2) ==
  \/ m1[1] > m2[1]
  \/ m1[1] = m2[1] /\ m1[2] > m2[2]

Request(self) ==
  \E t \in Times:
    /\ \A m \in received[self] \cup sent[self]: m.type = "request" => t >= m.time
    /\ \/ \E m \in received[self] \cup sent[self]: m.type = "request" /\ t = m.time 
       \/ /\ ~ \E m \in received[self] \cup sent[self]: m.type = "request"
          /\ t = 0
    /\ Send([type |-> "request", time |-> t + 1, from |-> self, to |-> Processes])
    /\ UNCHANGED <<received, in_cs, self_t>>

Reply(self) ==
  \E m \in received[self]:
    /\ m.type = "request"
    /\ Send([type |-> "ack", time |-> m.time, from |-> self, to |-> {m.from}])
    /\ UNCHANGED <<received, in_cs, self_t>>

Enter(self) ==
  \E m \in sent[self]:
    /\ m.type = "request"
    /\ ~ \E m2 \in sent[self]: m2.type = "release" /\ m2.time = m.time
    /\ \A p \in Processes: \E m2 \in received[self]: m2.type = "ack" /\ m2.time = m.time /\ m2.from = p
    /\ \A m2 \in received[self]: m2.type = "request"
        =>
        \/ Greater(<<m2.time, m2.from>>, <<m.time, self>>)
        \/ \E m3 \in received[self]: m3.type = "release" /\ m3.time = m2.time /\ m3.from = m2.from
    /\ in_cs' = [in_cs EXCEPT![self] = TRUE]
    /\ self_t' = [self_t EXCEPT![self] = m.time]
    /\ UNCHANGED <<sent, received>>

Exit(self) ==
  /\ in_cs[self]
  /\ in_cs' = [in_cs EXCEPT![self] = FALSE]
  /\ Send([type |-> "release", time |-> self_t, from |-> self, to |-> Processes])
  /\ UNCHANGED <<received, self_t>>

ReceiveMsg(self) ==
  /\ \E p \in Processes: \E m \in sent[p]: Receive(m, self)
  /\ /\ UNCHANGED <<sent, in_cs, self_t>>

Init ==
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ in_cs = [p \in Processes |-> FALSE]
  /\ self_t = [p \in Processes |-> 0]

Next == \E p \in Processes: \/ Request(p)
                            \/ Reply(p)
                            \/ Enter(p)
                            \/ Exit(p)
                            \/ ReceiveMsg(p)

Spec == Init /\ [][Next]_vars
Safety == \A p1, p2 \in Processes: in_cs[p1] /\ in_cs[p2] => p1 = p2
=============================================================================
\* Modification History
\* Last modified Mon May 21 17:18:41 EDT 2018 by saksh
\* Created Thu Mar 01 17:23:29 EST 2018 by saksh
