--------------------------- MODULE MajorityCommit ---------------------------
(***************************************************************************)
(* reference 6 (Majority Commit)                                           *)
(*                                                                         *)
(* This module implements Majority Commit, which attempts to solve the     *)
(* transaction commit problem in a fault-tolerant way by using multiple    *)
(* transaction managers and taking the decision made by a majority.        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT RM, Acceptor

VARIABLES rmState, aState, msgs

(***************************************************************************)
(* a tuple containing the variables                                        *)
(* easier than writing the tuple several times later                       *)
(***************************************************************************)
vars == <<rmState, aState, msgs>>

(***************************************************************************)
(* the set of subsets of Acceptor                                          *)
(* whose cardinality is just over half that of Acceptor                    *)
(***************************************************************************)
Majority == {MS \in SUBSET Acceptor :
                Cardinality(MS) = Cardinality(Acceptor) \div 2 + 1}

(***************************************************************************)
(* the set of legal messages                                               *)
(* it consists of records with two fields: sender and value                *)
(***************************************************************************)
Messages == [sender: RM, value: {"prepared", "aborted"}]
            \union [sender: Acceptor, value: {"committed", "aborted"}]

(***************************************************************************)
(* type invariant                                                          *)
(***************************************************************************)
MCTypeOK == /\ rmState \in
                 [RM -> {"working", "prepared", "committed", "aborted"}]
            /\ aState \in [Acceptor -> {"initial", "committed", "aborted"}]
            /\ msgs \subseteq Messages

(***************************************************************************)
(* assertion that all resource managers have committed or aborted          *)
(***************************************************************************)
MCDecideOK == \/ rmState = [r \in RM |-> "committed"]
              \/ rmState = [r \in RM |-> "aborted"] 

(***************************************************************************)
(* defines sending a message as                                            *)
(* adding it to a set of all messages ever sent                            *)
(***************************************************************************)
Send(m) == msgs' = msgs \union {m}

(***************************************************************************)
(* a resource manager in the working state can choose to move              *)
(* to the prepared state or the aborted state                              *)
(***************************************************************************)
RMDecide(r, val) == /\ rmState[r] = "working"
                    /\ rmState' = [rmState EXCEPT ![r] = val]
                    /\ Send([sender |-> r, value |-> val])
                    /\ UNCHANGED aState

(***************************************************************************)
(* if all resource managers are prepared                                   *)
(* an acceptor can broadcast a commit message                              *)
(***************************************************************************)
AcceptorCommit(ac) == /\ aState[ac] = "initial"
                      /\ \A r \in RM :
                            [sender |-> r, value |-> "prepared"] \in msgs
                      /\ aState' = [aState EXCEPT ![ac] = "committed"]
                      /\ Send([sender |-> ac, value |-> "committed"])
                      /\ UNCHANGED rmState

(***************************************************************************)
(* if not all resource managers are prepared,                              *)
(* an acceptor can choose to broadcast an abort message                    *)
(***************************************************************************)
AcceptorAbort(ac) == /\ aState[ac] = "initial"
                     /\ \E r \in RM :
                            [sender |-> r, value |-> "prepared"] \notin msgs
                     /\ aState' = [aState EXCEPT ![ac] = "aborted"]
                     /\ Send([sender |-> ac, value |-> "aborted"])
                     /\ UNCHANGED rmState

(***************************************************************************)
(* if a majority of acceptors has made the same decision,                  *)
(* the resource managers will follow it                                    *)
(***************************************************************************)
RMRcvMessage(r, val) == /\ \E MS \in Majority : \A ac \in MS:
                              [sender |-> ac, value |-> val] \in msgs
                        /\ rmState' = [rmState EXCEPT ![r] = val]
                        /\ UNCHANGED <<aState, msgs>>

(***************************************************************************)
(* initial state of the system                                             *)
(***************************************************************************)
MCInit == /\ rmState = [r \in RM |-> "working"]
          /\ aState = [ac \in Acceptor |-> "initial"]
          /\ msgs = {}

(***************************************************************************)
(* legal state transitions must satisfy this formula                       *)
(***************************************************************************)
MCNext == \/ \E r \in RM : \/ \E val \in {"prepared", "aborted"} :
                                   RMDecide(r, val)
                          \/ \E val \in {"committed", "aborted"} :
                                   RMRcvMessage(r, val)
         \/ \E ac \in Acceptor : AcceptorCommit(ac) \/ AcceptorAbort(ac)

(***************************************************************************)
(* temporal formula specifying properties of a legal behavior              *)
(* a legal behavior has an initial state satisfying MCInit,                *)
(* each state transition satisfies MCNext with respect to the variables,   *)
(* and there are weak fairness conditions on some actions                  *)
(***************************************************************************)
MCSpec == /\ MCInit
          /\ [][MCNext]_vars
          /\ \A r \in RM, val \in {"committed", "aborted"} :
                WF_vars(RMRcvMessage(r, val))
          /\ (* \A ac \in Acceptor : *) \E MS \in Majority : \A ac \in MS :
                WF_vars(AcceptorCommit(ac)) /\ WF_vars(AcceptorAbort(ac))
=============================================================================
\* Modification History
\* Last modified Fri Nov 23 17:56:02 EST 2018 by steve
\* Created Fri Nov 16 16:23:44 EST 2018 by steve
