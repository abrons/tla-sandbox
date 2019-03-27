------------------------------ MODULE payments ------------------------------

EXTENDS TLC, FiniteSets, Integers, Sequences

Servers == {<<"server1", 1>>, <<"server2",2>>}
Syncers == {<<"sync1", 1>>, <<"sync2", 2>>}


(*--algorithm payments
variables
  dcs = {s[2] : s \in Servers},
  db = [dc \in dcs |-> <<>>],
  msgs = [dc \in dcs |-> <<>>],
  auths = {},
  captures = {},
  broadcast = [dc \in dcs |-> <<>>];
  
define

  \* Not technically required since auths expire, but for user friendliness we
  \* explicitly void any redundant auths.
  VoidRedundantAuths == Cardinality(auths) > 1 ~> <>(Cardinality(auths) = 1)
  
  \* Double capturing is bad under any circumstances, because it could cause overdrafts.
  NoDoubleCapture == Cardinality(captures) <= 1
  
  \* If we auth something, ensure that we eventually capture it. (This model doesn't
  \* handle client voids or refunds, which would complicated this)
  EventualCapture == Cardinality(auths) >= 1 ~> <>(Cardinality(captures) = 1)
  
  \* A client must never send an auth with the same ID to more than one DC
  DistinctIds == \A dc1 \in dcs, dc2 \in dcs :
       dc1 = dc2 
    \/ Len(SelectSeq(msgs[dc1], LAMBDA x1 : Len(SelectSeq(msgs[dc2], LAMBDA x2 : x1.id = x2.id)) > 0)) = 0
  
end define;

fair process client = <<"client", 1>>
begin InitialAuth:
  msgs[1] := Append(msgs[1], [id |-> 1, token |-> "abc", home |-> {1}]);
  Retry:
  msgs[2] := Append(msgs[2], [id |-> 2, token |-> "abc", home |-> {1}]);
end process;

fair process server \in Servers
variables
  serverid = self[2],
  others = dcs \ {serverid};
begin ServerStart:
    while TRUE do
      await Len(msgs[serverid]) > 0;
      
      with local = Head(msgs[serverid]) do
          \* If we already have an auth for this token, then ignore
          if Len(SelectSeq(db[serverid], LAMBDA x : x.token = local.token)) > 0 then
            skip;
          else
              \* Auth it!
              auths := auths \union {local};
              
              if serverid \in local.home then
                \* We own this auth, so capture it!
                captures := captures \union {local};
              else
                skip;
              end if;
              
              \* Store locally (Only actually needed for this proof if home DC)
              db[serverid] := Append(db[serverid], local);
              
              \* Broadcast msg to home dcs (excluding self)
              broadcast := [dc \in dcs |->
                  IF dc \in local.home /\ dc /= serverid
                  THEN Append(broadcast[dc], local)
                  ELSE broadcast[dc]
              ];
          end if;
          
          msgs[serverid] := Tail(msgs[serverid]);         
      end with;
    end while;
end process;

fair process syncer \in Syncers
variables
  serverid = self[2];
begin SyncStart:
  while TRUE do
    await Len(broadcast[serverid]) > 0;
    SyncStep:
        with local = Head(broadcast[serverid]) do
          \* If our local db includes an auth with matching token
          if Len(SelectSeq(db[serverid], LAMBDA x : x.token = local.token)) > 0 then
            \* ... then void this newly received auth
            auths := auths \ {local};
          else
            \* If not, we just got a new auth, which we own and will need to capture.
            db[serverid] := Append(db[serverid], local);
            captures := captures \union {local};
          end if;
          
          broadcast[serverid] := Tail(broadcast[serverid]); 
        end with;   
  end while;
end process;

end algorithm--*)
\* BEGIN TRANSLATION
\* Process variable serverid of process server at line 46 col 3 changed to serverid_
VARIABLES dcs, db, msgs, auths, captures, broadcast, pc

(* define statement *)
VoidRedundantAuths == Cardinality(auths) > 1 ~> <>(Cardinality(auths) = 1)


NoDoubleCapture == Cardinality(captures) <= 1



EventualCapture == Cardinality(auths) >= 1 ~> <>(Cardinality(captures) = 1)


DistinctIds == \A dc1 \in dcs, dc2 \in dcs :
     dc1 = dc2
  \/ Len(SelectSeq(msgs[dc1], LAMBDA x1 : Len(SelectSeq(msgs[dc2], LAMBDA x2 : x1.id = x2.id)) > 0)) = 0

VARIABLES serverid_, others, serverid

vars == << dcs, db, msgs, auths, captures, broadcast, pc, serverid_, others, 
           serverid >>

ProcSet == {<<"client", 1>>} \cup (Servers) \cup (Syncers)

Init == (* Global variables *)
        /\ dcs = {s[2] : s \in Servers}
        /\ db = [dc \in dcs |-> <<>>]
        /\ msgs = [dc \in dcs |-> <<>>]
        /\ auths = {}
        /\ captures = {}
        /\ broadcast = [dc \in dcs |-> <<>>]
        (* Process server *)
        /\ serverid_ = [self \in Servers |-> self[2]]
        /\ others = [self \in Servers |-> dcs \ {serverid_[self]}]
        (* Process syncer *)
        /\ serverid = [self \in Syncers |-> self[2]]
        /\ pc = [self \in ProcSet |-> CASE self = <<"client", 1>> -> "InitialAuth"
                                        [] self \in Servers -> "ServerStart"
                                        [] self \in Syncers -> "SyncStart"]

InitialAuth == /\ pc[<<"client", 1>>] = "InitialAuth"
               /\ msgs' = [msgs EXCEPT ![1] = Append(msgs[1], [id |-> 1, token |-> "abc", home |-> {1}])]
               /\ pc' = [pc EXCEPT ![<<"client", 1>>] = "Retry"]
               /\ UNCHANGED << dcs, db, auths, captures, broadcast, serverid_, 
                               others, serverid >>

Retry == /\ pc[<<"client", 1>>] = "Retry"
         /\ msgs' = [msgs EXCEPT ![2] = Append(msgs[2], [id |-> 2, token |-> "abc", home |-> {1}])]
         /\ pc' = [pc EXCEPT ![<<"client", 1>>] = "Done"]
         /\ UNCHANGED << dcs, db, auths, captures, broadcast, serverid_, 
                         others, serverid >>

client == InitialAuth \/ Retry

ServerStart(self) == /\ pc[self] = "ServerStart"
                     /\ Len(msgs[serverid_[self]]) > 0
                     /\ LET local == Head(msgs[serverid_[self]]) IN
                          /\ IF Len(SelectSeq(db[serverid_[self]], LAMBDA x : x.token = local.token)) > 0
                                THEN /\ TRUE
                                     /\ UNCHANGED << db, auths, captures, 
                                                     broadcast >>
                                ELSE /\ auths' = (auths \union {local})
                                     /\ IF serverid_[self] \in local.home
                                           THEN /\ captures' = (captures \union {local})
                                           ELSE /\ TRUE
                                                /\ UNCHANGED captures
                                     /\ db' = [db EXCEPT ![serverid_[self]] = Append(db[serverid_[self]], local)]
                                     /\ broadcast' =              [dc \in dcs |->
                                                         IF dc \in local.home /\ dc /= serverid_[self]
                                                         THEN Append(broadcast[dc], local)
                                                         ELSE broadcast[dc]
                                                     ]
                          /\ msgs' = [msgs EXCEPT ![serverid_[self]] = Tail(msgs[serverid_[self]])]
                     /\ pc' = [pc EXCEPT ![self] = "ServerStart"]
                     /\ UNCHANGED << dcs, serverid_, others, serverid >>

server(self) == ServerStart(self)

SyncStart(self) == /\ pc[self] = "SyncStart"
                   /\ Len(broadcast[serverid[self]]) > 0
                   /\ pc' = [pc EXCEPT ![self] = "SyncStep"]
                   /\ UNCHANGED << dcs, db, msgs, auths, captures, broadcast, 
                                   serverid_, others, serverid >>

SyncStep(self) == /\ pc[self] = "SyncStep"
                  /\ LET local == Head(broadcast[serverid[self]]) IN
                       /\ IF Len(SelectSeq(db[serverid[self]], LAMBDA x : x.token = local.token)) > 0
                             THEN /\ auths' = auths \ {local}
                                  /\ UNCHANGED << db, captures >>
                             ELSE /\ db' = [db EXCEPT ![serverid[self]] = Append(db[serverid[self]], local)]
                                  /\ captures' = (captures \union {local})
                                  /\ auths' = auths
                       /\ broadcast' = [broadcast EXCEPT ![serverid[self]] = Tail(broadcast[serverid[self]])]
                  /\ pc' = [pc EXCEPT ![self] = "SyncStart"]
                  /\ UNCHANGED << dcs, msgs, serverid_, others, serverid >>

syncer(self) == SyncStart(self) \/ SyncStep(self)

Next == client
           \/ (\E self \in Servers: server(self))
           \/ (\E self \in Syncers: syncer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(client)
        /\ \A self \in Servers : WF_vars(server(self))
        /\ \A self \in Syncers : WF_vars(syncer(self))

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Mar 27 15:47:27 AEDT 2019 by xavier
\* Created Mon Mar 25 17:57:06 AEDT 2019 by xavier
