------------------------------ MODULE payments ------------------------------

EXTENDS TLC, FiniteSets, Integers, Sequences

Servers == {<<"server1", 1>>, <<"server2",2>>}
Syncers == {<<"sync1", 1>>, <<"sync2", 2>>}


(*--algorithm payments
variables
  dcs = {s[2] : s \in Servers},
  db = [dc \in dcs |-> <<>>],
  broadcast = [dc \in dcs |-> <<>>];
  
define
  \* SomeInvariant == <>(\A x \in Servers : db[x[2]] = Servers)
  SomeInvariant == <>(db = [dc \in dcs |-> <<{3}>>])
  
  \* SomeInvariant == <>(db = [dc \in dcs |-> <<>>])
end define;

fair process server \in Servers
variables
  serverid = self[2],
  others = dcs \ {serverid};
begin ServerStart:
  broadcast := [dc \in dcs |->
    IF dc = serverid
    THEN broadcast[dc]
    ELSE Append(broadcast[dc], {3})
  ]
end process;

fair process syncer \in Syncers
variables
  local = {},
  serverid = self[2];
begin SyncStart:
  while TRUE do
    await Len(broadcast[serverid]) > 0;
    SyncStep:
        local := Head(broadcast[serverid]);
        broadcast[serverid] := Tail(broadcast[serverid]);
        db[serverid] := Append(db[serverid], local);
  end while;
end process;

end algorithm--*)
\* BEGIN TRANSLATION
\* Process variable serverid of process server at line 24 col 3 changed to serverid_
VARIABLES dcs, db, broadcast, pc

(* define statement *)
SomeInvariant == <>(db = [dc \in dcs |-> <<{3}>>])

VARIABLES serverid_, others, local, serverid

vars == << dcs, db, broadcast, pc, serverid_, others, local, serverid >>

ProcSet == (Servers) \cup (Syncers)

Init == (* Global variables *)
        /\ dcs = {s[2] : s \in Servers}
        /\ db = [dc \in dcs |-> <<>>]
        /\ broadcast = [dc \in dcs |-> <<>>]
        (* Process server *)
        /\ serverid_ = [self \in Servers |-> self[2]]
        /\ others = [self \in Servers |-> dcs \ {serverid_[self]}]
        (* Process syncer *)
        /\ local = [self \in Syncers |-> {}]
        /\ serverid = [self \in Syncers |-> self[2]]
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "ServerStart"
                                        [] self \in Syncers -> "SyncStart"]

ServerStart(self) == /\ pc[self] = "ServerStart"
                     /\ broadcast' =              [dc \in dcs |->
                                       IF dc = serverid_[self]
                                       THEN broadcast[dc]
                                       ELSE Append(broadcast[dc], {3})
                                     ]
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << dcs, db, serverid_, others, local, 
                                     serverid >>

server(self) == ServerStart(self)

SyncStart(self) == /\ pc[self] = "SyncStart"
                   /\ Len(broadcast[serverid[self]]) > 0
                   /\ pc' = [pc EXCEPT ![self] = "SyncStep"]
                   /\ UNCHANGED << dcs, db, broadcast, serverid_, others, 
                                   local, serverid >>

SyncStep(self) == /\ pc[self] = "SyncStep"
                  /\ local' = [local EXCEPT ![self] = Head(broadcast[serverid[self]])]
                  /\ broadcast' = [broadcast EXCEPT ![serverid[self]] = Tail(broadcast[serverid[self]])]
                  /\ db' = [db EXCEPT ![serverid[self]] = Append(db[serverid[self]], local'[self])]
                  /\ pc' = [pc EXCEPT ![self] = "SyncStart"]
                  /\ UNCHANGED << dcs, serverid_, others, serverid >>

syncer(self) == SyncStart(self) \/ SyncStep(self)

Next == (\E self \in Servers: server(self))
           \/ (\E self \in Syncers: syncer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(server(self))
        /\ \A self \in Syncers : WF_vars(syncer(self))

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Mar 27 14:46:09 AEDT 2019 by xavier
\* Created Mon Mar 25 17:57:06 AEDT 2019 by xavier
