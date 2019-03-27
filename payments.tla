A simplistic model of multi-datacenter redundancy for a pass-through payments processor. There are three actors in the system:

1. A single client who wants to charge a card.
2. A single processor who is able to charge the card.
3. N redundant datacenters (DCs), one of which will be in the middle of the request, which presumably adds value in some way.

A datacenter consists of an API processor and a background "sync" process.

This model makes some reasonable assumptions:
* The processor supports the following Auth/Capture semantics:
  * "Auth" reserves an amount to be captured.
  * "Capture" causes the actual debit of a previous "Auth".
  * "Void" cancels a previous "Auth", or does nothing if no previous matching "Auth".
* The client will retry against all DCs until it receives a successful response. (The exactly retry schedule is not relevant.)

It also makes some unreasonable ones. More work is required to specify these for a real world system:
* A datacenter can always successfully communicate with the processor.
* A datacenter will always become available if it goes down.
* Each datacenter is able to broadcast reliably to other datacenters with exactly-once semantics.
* A client will only send a single message to each datacenter. In practice, same-DC retries should be supported.

(The first two would be a decent amount fo work, the latter two should be pretty straight forward TODOs.)

Ultimately, we are trying to ensure that a client is able to send an "Auth" to multiple DCs without resulting in a duplicate charge.

------------------------------ MODULE payments ------------------------------

EXTENDS TLC, FiniteSets, Integers, Sequences

CONSTANT NumDatacenters
ASSUME NumDatacenters > 0

Datacenters == 1..NumDatacenters
Servers == {<<"server", dc>> : dc \in Datacenters}
Syncers == {<<"sync", dc>> : dc \in Datacenters}

(*--algorithm payments
variables
  \* DATACENTER LOCAL VARIABLES
  \* These are shared between a server and a syncer in the same DC

  \* Local database
  db        = [dc \in Datacenters |-> <<>>],
  \* Messages from the client
  msgs      = [dc \in Datacenters |-> <<>>],
  \* Broadcast messages from other DCs
  broadcast = [dc \in Datacenters |-> <<>>],

  \* PROCESSOR VARIABLES
  auths    = {},
  captures = {},

  \* Whether or not a successful response has been returned to the client
  \* This isn't really necessary with the current assumptions, but makes invariants clearer.
  Success = FALSE
  ;

\* INVARIANTS AND TEMPORAL PROPERTIES
define

  \* Double capturing is bad under any circumstances, because it could cause overdrafts.
  NoDoubleCapture == Cardinality(captures) <= 1

  \* If we auth something, ensure that we eventually capture it. (This model doesn't
  \* handle client voids or refunds, which would complicated this)
  EventualCapture == Success ~> <>(Cardinality(captures) = 1)

  \* Not technically required since auths expire, but for user friendliness we
  \* explicitly void any redundant auths.
  VoidRedundantAuths == Success ~> <>(Cardinality(auths) = 1)

  \* A client must never send an auth with the same ID to more than one DC
  DistinctIds == \A dc1 \in Datacenters, dc2 \in Datacenters :
       dc1 = dc2
    \/ Len(SelectSeq(msgs[dc1], LAMBDA x1 : Len(SelectSeq(msgs[dc2], LAMBDA x2 : x1.id = x2.id)) > 0)) = 0


  \* Helper function
  Min(S) == CHOOSE x \in S:
            \A y \in S \ {x}:
              y > x
end define;

\* A client starts by sending a payment to an arbitrarily chosen "home" datacenter.
\* It then retries to every other datacenter so long as it hasn't received a successful response.
fair process client = <<"client", 1>>
variables
  id = 1,
  token = "abc",
  homedc = Min(Datacenters),
  others = Datacenters \ {homedc};
begin InitialAuth:
  msgs[homedc] := Append(msgs[homedc], [id |-> id, token |-> token, home |-> {homedc}]);
  id := id + 1;

  RetryLoop:
  while others /= {} /\ ~Success do
    Retry:
    with nextdc = Min(others) do
      msgs[nextdc] := Append(msgs[nextdc], [id |-> id, token |-> token, home |-> {homedc}]);
      id := id + 1;
      others := others \ {nextdc};
    end with;
  end while;
end process;

fair process server \in Servers
variables
  serverid = self[2];
begin ServerStart:
    while TRUE do
      await Len(msgs[serverid]) > 0;

      HandleRequest:
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

              \* Broadcast msg to home DCs (excluding self)
              broadcast := [dc \in Datacenters |->
                  IF dc \in local.home /\ dc /= serverid
                  THEN Append(broadcast[dc], local)
                  ELSE broadcast[dc]
              ];
          end if;

          msgs[serverid] := Tail(msgs[serverid]);
      end with;

      \* Tell client we succeeded
      \* TODO: How to simulate response being dropped? Adding an either here or a label collapses model to a single state...
      Success := TRUE;

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
\* Process variable serverid of process server at line 95 col 3 changed to serverid_
VARIABLES db, msgs, broadcast, auths, captures, Success, pc

(* define statement *)
NoDoubleCapture == Cardinality(captures) <= 1



EventualCapture == Success ~> <>(Cardinality(captures) = 1)



VoidRedundantAuths == Success ~> <>(Cardinality(auths) = 1)


DistinctIds == \A dc1 \in Datacenters, dc2 \in Datacenters :
     dc1 = dc2
  \/ Len(SelectSeq(msgs[dc1], LAMBDA x1 : Len(SelectSeq(msgs[dc2], LAMBDA x2 : x1.id = x2.id)) > 0)) = 0



Min(S) == CHOOSE x \in S:
          \A y \in S \ {x}:
            y > x

VARIABLES id, token, homedc, others, serverid_, serverid

vars == << db, msgs, broadcast, auths, captures, Success, pc, id, token,
           homedc, others, serverid_, serverid >>

ProcSet == {<<"client", 1>>} \cup (Servers) \cup (Syncers)

Init == (* Global variables *)
        /\ db = [dc \in Datacenters |-> <<>>]
        /\ msgs = [dc \in Datacenters |-> <<>>]
        /\ broadcast = [dc \in Datacenters |-> <<>>]
        /\ auths = {}
        /\ captures = {}
        /\ Success = FALSE
        (* Process client *)
        /\ id = 1
        /\ token = "abc"
        /\ homedc = Min(Datacenters)
        /\ others = Datacenters \ {homedc}
        (* Process server *)
        /\ serverid_ = [self \in Servers |-> self[2]]
        (* Process syncer *)
        /\ serverid = [self \in Syncers |-> self[2]]
        /\ pc = [self \in ProcSet |-> CASE self = <<"client", 1>> -> "InitialAuth"
                                        [] self \in Servers -> "ServerStart"
                                        [] self \in Syncers -> "SyncStart"]

InitialAuth == /\ pc[<<"client", 1>>] = "InitialAuth"
               /\ msgs' = [msgs EXCEPT ![homedc] = Append(msgs[homedc], [id |-> id, token |-> token, home |-> {homedc}])]
               /\ id' = id + 1
               /\ pc' = [pc EXCEPT ![<<"client", 1>>] = "RetryLoop"]
               /\ UNCHANGED << db, broadcast, auths, captures, Success, token,
                               homedc, others, serverid_, serverid >>

RetryLoop == /\ pc[<<"client", 1>>] = "RetryLoop"
             /\ IF others /= {} /\ ~Success
                   THEN /\ pc' = [pc EXCEPT ![<<"client", 1>>] = "Retry"]
                   ELSE /\ pc' = [pc EXCEPT ![<<"client", 1>>] = "Done"]
             /\ UNCHANGED << db, msgs, broadcast, auths, captures, Success, id,
                             token, homedc, others, serverid_, serverid >>

Retry == /\ pc[<<"client", 1>>] = "Retry"
         /\ LET nextdc == Min(others) IN
              /\ msgs' = [msgs EXCEPT ![nextdc] = Append(msgs[nextdc], [id |-> id, token |-> token, home |-> {homedc}])]
              /\ id' = id + 1
              /\ others' = others \ {nextdc}
         /\ pc' = [pc EXCEPT ![<<"client", 1>>] = "RetryLoop"]
         /\ UNCHANGED << db, broadcast, auths, captures, Success, token,
                         homedc, serverid_, serverid >>

client == InitialAuth \/ RetryLoop \/ Retry

ServerStart(self) == /\ pc[self] = "ServerStart"
                     /\ Len(msgs[serverid_[self]]) > 0
                     /\ pc' = [pc EXCEPT ![self] = "HandleRequest"]
                     /\ UNCHANGED << db, msgs, broadcast, auths, captures,
                                     Success, id, token, homedc, others,
                                     serverid_, serverid >>

HandleRequest(self) == /\ pc[self] = "HandleRequest"
                       /\ LET local == Head(msgs[serverid_[self]]) IN
                            /\ IF Len(SelectSeq(db[serverid_[self]], LAMBDA x : x.token = local.token)) > 0
                                  THEN /\ TRUE
                                       /\ UNCHANGED << db, broadcast, auths,
                                                       captures >>
                                  ELSE /\ auths' = (auths \union {local})
                                       /\ IF serverid_[self] \in local.home
                                             THEN /\ captures' = (captures \union {local})
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED captures
                                       /\ db' = [db EXCEPT ![serverid_[self]] = Append(db[serverid_[self]], local)]
                                       /\ broadcast' =              [dc \in Datacenters |->
                                                           IF dc \in local.home /\ dc /= serverid_[self]
                                                           THEN Append(broadcast[dc], local)
                                                           ELSE broadcast[dc]
                                                       ]
                            /\ msgs' = [msgs EXCEPT ![serverid_[self]] = Tail(msgs[serverid_[self]])]
                       /\ Success' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "ServerStart"]
                       /\ UNCHANGED << id, token, homedc, others, serverid_,
                                       serverid >>

server(self) == ServerStart(self) \/ HandleRequest(self)

SyncStart(self) == /\ pc[self] = "SyncStart"
                   /\ Len(broadcast[serverid[self]]) > 0
                   /\ pc' = [pc EXCEPT ![self] = "SyncStep"]
                   /\ UNCHANGED << db, msgs, broadcast, auths, captures,
                                   Success, id, token, homedc, others,
                                   serverid_, serverid >>

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
                  /\ UNCHANGED << msgs, Success, id, token, homedc, others,
                                  serverid_, serverid >>

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
\* Last modified Wed Mar 27 16:42:13 AEDT 2019 by xavier
\* Created Mon Mar 25 17:57:06 AEDT 2019 by xavier
