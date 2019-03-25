------------------------------ MODULE payments ------------------------------

EXTENDS TLC, FiniteSets, Integers, Sequences

Servers == {<<"server1", 1>>, <<"server2",2>>}
Syncers == {<<"sync1", 1>>, <<"sync2", 2>>}


(*--algorithm payments
variables
  db = [s \in {s[2] : s \in Servers} |-> {}],
  broadcast = {};
  
define
  SomeInvariant == <>(\A x \in Servers : db[x[2]] = Servers)
end define;

fair process server \in Servers
begin ServerStart:
  broadcast := broadcast \union {self}
end process;

fair process syncer \in Syncers
begin SyncStart:
  while TRUE do
    SyncStep:
    db[self[2]] := db[self[2]] \union broadcast
  end while;
end process;

end algorithm--*)
\* BEGIN TRANSLATION
VARIABLES db, broadcast, pc

(* define statement *)
SomeInvariant == <>(\A x \in Servers : db[x[2]] = Servers)


vars == << db, broadcast, pc >>

ProcSet == (Servers) \cup (Syncers)

Init == (* Global variables *)
        /\ db = [s \in {s[2] : s \in Servers} |-> {}]
        /\ broadcast = {}
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "ServerStart"
                                        [] self \in Syncers -> "SyncStart"]

ServerStart(self) == /\ pc[self] = "ServerStart"
                     /\ broadcast' = (broadcast \union {self})
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ db' = db

server(self) == ServerStart(self)

SyncStart(self) == /\ pc[self] = "SyncStart"
                   /\ pc' = [pc EXCEPT ![self] = "SyncStep"]
                   /\ UNCHANGED << db, broadcast >>

SyncStep(self) == /\ pc[self] = "SyncStep"
                  /\ db' = [db EXCEPT ![self[2]] = db[self[2]] \union broadcast]
                  /\ pc' = [pc EXCEPT ![self] = "SyncStart"]
                  /\ UNCHANGED broadcast

syncer(self) == SyncStart(self) \/ SyncStep(self)

Next == (\E self \in Servers: server(self))
           \/ (\E self \in Syncers: syncer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(server(self))
        /\ \A self \in Syncers : WF_vars(syncer(self))

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Mar 25 19:36:24 AEDT 2019 by xavier
\* Created Mon Mar 25 17:57:06 AEDT 2019 by xavier
