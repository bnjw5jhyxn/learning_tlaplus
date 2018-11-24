----------------------- MODULE OptimizedPaxosCommit ------------------------
(***************************************************************************)
(* reference 5 (optimized Paxos Commit with liveness properties)           *)
(*                                                                         *)
(* This module specifies the Paxos Commit algorithm.  We specify both      *)
(* safety properties and liveness properties.  We also implement an        *)
(* optimization described in Lamport and Gray's paper.                     *)
(*                                                                         *)
(* This specification is discussed in "Paxos Commit", Lecture 6 of the     *)
(* TLA+ Video Course.                                                      *)
(*                                                                         *)
(* This module specifies the Paxos Commit algorithm.  We specify only      *)
(* safety properties, not liveness properties.  We simplify the            *)
(* specification in the following ways.                                    *)
(*                                                                         *)
(*  - As in the specification of module TwoPhase, and for the same         *)
(*    reasons, we let the variable msgs be the set of all messages that    *)
(*    have ever been sent.  If a message is sent to a set of recipients,   *)
(*    only one copy of the message appears in msgs.                        *)
(*                                                                         *)
(*  - We do not explicitly model the receipt of messages.  If an           *)
(*    operation can be performed when a process has received a certain set *)
(*    of messages, then the operation is represented by an action that is  *)
(*    enabled when those messages are in the set msgs of sent messages.    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

Maximum(S) == 
  (*************************************************************************)
  (* If S is a set of numbers, then this define Maximum(S) to be the       *)
  (* maximum of those numbers, or -1 if S is empty.                        *)
  (*************************************************************************)
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n \geq m

CONSTANT RM,             \* The set of resource managers.
         Acceptor,       \* The set of acceptors.
         Ballot          \* The set of ballot numbers

Majority == {MS \in SUBSET Acceptor :
                Cardinality(MS) = Cardinality(Acceptor) \div 2 + 1}

(***************************************************************************)
(* We assume the following properties of the declared constants.           *)
(***************************************************************************)
ASSUME  
  /\ Ballot \subseteq Nat
  /\ 0 \in Ballot
  /\ Majority \subseteq SUBSET Acceptor
  /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}
       (********************************************************************)
       (* All we assume about the set Majority of majorities is that any   *)
       (* two majorities have non-empty intersection.                      *)
       (********************************************************************)
       
Messages ==
  (*************************************************************************)
  (* The set of all possible messages.  There are messages of type         *)
  (* "Commit" and "Abort" to announce the decision, as well as messages    *)
  (* for each phase of each instance of ins of the Paxos consensus         *)
  (* algorithm.  The acc field indicates the sender of a message from an   *)
  (* acceptor to the leader; messages from a leader are broadcast to all   *)
  (* acceptors.                                                            *)
  (*************************************************************************)
  [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}] 
      \cup
  [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
   val : {"prepared", "aborted", "none"}, acc : Acceptor] 
      \cup
  [type : {"phase2a"}, ins : RM, bal : Ballot, val : {"prepared", "aborted"}]
      \cup                              
  [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,  
   val : {"prepared", "aborted"}] 
      \cup
  [type : {"Commit", "Abort"}]
-----------------------------------------------------------------------------
VARIABLES
  rmState,  \* rmState[r] is the state of resource manager r.
  aState,   \* aState[ins][ac] is the state of acceptor ac for instance 
            \* ins of the Paxos algorithm. 
  msgs      \* The set of all messages ever sent.

vars == <<rmState, aState, msgs>>

PCTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant.  Each acceptor maintains the values   *)
  (* mbal, bal, and val for each instance of the Paxos consensus           *)
  (* algorithm.                                                            *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState  \in [RM -> [Acceptor -> [mbal : Ballot,
                                      bal  : Ballot \cup {-1},
                                      val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \subseteq Messages

(* asserts that all RMs have committed or aborted *)
PCDecideOK == \/ rmState = [r \in RM |-> "committed"]
              \/ rmState = [r \in RM |-> "aborted"]

PCInit ==  \* The initial predicate.
  /\ rmState = [r \in RM |-> "working"]
  /\ aState  = [r \in RM |-> 
                 [ac \in Acceptor 
                    |-> [mbal |-> 0, bal  |-> -1, val  |-> "none"]]]
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(*                                THE ACTIONS                              *)
(***************************************************************************)
Send(m) == msgs' = msgs \cup {m}
  (*************************************************************************)
  (* An action expression that describes the sending of message m.         *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                               RM ACTIONS                                *)
(***************************************************************************)
RMPrepare(r) == 
  (*************************************************************************)
  (* Resource manager r prepares by sending a phase 2a message for ballot  *)
  (* number 0 with value "prepared".                                       *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "prepared"])
  /\ UNCHANGED aState
  
RMChooseToAbort(r) ==
  (*************************************************************************)
  (* Resource manager r spontaneously decides to abort.  It may (but need  *)
  (* not) send a phase 2a message for ballot number 0 with value           *)
  (* "aborted".                                                            *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "aborted"])
  /\ UNCHANGED aState

PCDecision == 
  (*************************************************************************)
  (* each resource manager can tell from the acceptors' messages           *)
  (* whether the acceptors have collectively decided to commit or abort    *)
  (*************************************************************************)
  LET Decided(r, v) ==
        \E b \in Ballot, MS \in Majority : 
          \A ac \in MS : [type |-> "phase2b", ins |-> r, 
                           bal |-> b, val |-> v, acc |-> ac ] \in msgs
  IN IF \A r \in RM : /\ Decided(r, "prepared")
                      /\ rmState[r] = "prepared" \/ rmState[r] = "committed"
     THEN "committed"
     ELSE IF \E r \in RM : Decided(r, "aborted")
     THEN "aborted"
     ELSE "undecided"

RMInferDecision(r) == /\ PCDecision /= "undecided"
                      /\ rmState' = [rmState EXCEPT ![r] = PCDecision]
                      /\ UNCHANGED <<aState, msgs>>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            LEADER ACTIONS                               *)
(*                                                                         *)
(* The following actions are performed by any process that believes itself *)
(* to be the current leader.  Since leader selection is not assumed to be  *)
(* reliable, multiple processes could simultaneously consider themselves   *)
(* to be the leader.                                                       *)
(***************************************************************************)
Phase1a(bal, r) ==
  (*************************************************************************)
  (* If the leader times out without learning that a decision has been     *)
  (* reached on resource manager r's prepare/abort decision, it can        *)
  (* perform this action to initiate a new ballot bal.  (Sending duplicate *)
  (* phase 1a messages is harmless.)                                       *)
  (*************************************************************************)
  /\ Send([type |-> "phase1a", ins |-> r, bal |-> bal])
  /\ UNCHANGED <<rmState, aState>>

Phase2a(bal, r) ==
  (*************************************************************************)
  (* The action in which a leader sends a phase 2a message with ballot     *)
  (* bal > 0 in instance r, if it has received phase 1b messages for       *)
  (* ballot number bal from a majority of acceptors.  If the leader        *)
  (* received a phase 1b message from some acceptor that had sent a phase  *)
  (* 2b message for this instance, then maxbal \geq 0 and the value val    *)
  (* the leader sends is determined by the phase 1b messages.  (If         *)
  (* val = "prepared", then r must have prepared.) Otherwise, maxbal = -1  *)
  (* and the leader sends the value "aborted".                             *)
  (*                                                                       *)
  (* The first conjunct asserts that the action is disabled if any commit  *)
  (* leader has already sent a phase 2a message with ballot number bal.    *)
  (* In practice, this is implemented by having ballot numbers partitioned *)
  (* among potential leaders, and having a leader record in stable storage *)
  (* the largest ballot number for which it sent a phase 2a message.       *)
  (*************************************************************************)
  /\ ~\E m \in msgs : /\ m.type = "phase2a"
                      /\ m.bal = bal
                      /\ m.ins = r
  /\ \E MS \in Majority :    
        LET mset == {m \in msgs : /\ m.type = "phase1b"
                                  /\ m.ins  = r
                                  /\ m.mbal = bal 
                                  /\ m.acc  \in MS}
            maxbal == Maximum({m.bal : m \in mset})
            val == IF maxbal = -1 
                     THEN "aborted"
                     ELSE (CHOOSE m \in mset : m.bal = maxbal).val
        IN  /\ \A ac \in MS : \E m \in mset : m.acc = ac
            /\ Send([type |-> "phase2a", ins |-> r, bal |-> bal, val |-> val])
  /\ UNCHANGED <<rmState, aState>>

-----------------------------------------------------------------------------
(***************************************************************************)
(*                             ACCEPTOR ACTIONS                            *)
(***************************************************************************)
Phase1b(acc) ==  
  \E m \in msgs : 
    /\ m.type = "phase1a"
    /\ aState[m.ins][acc].mbal < m.bal
    /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal]
    /\ Send([type |-> "phase1b", 
             ins  |-> m.ins, 
             mbal |-> m.bal, 
             bal  |-> aState[m.ins][acc].bal, 
             val  |-> aState[m.ins][acc].val,
             acc  |-> acc])
    /\ UNCHANGED rmState

Phase2b(acc) == 
  /\ \E m \in msgs : 
       /\ m.type = "phase2a"
       /\ aState[m.ins][acc].mbal \leq m.bal
       /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal,
                                   ![m.ins][acc].bal  = m.bal,
                                   ![m.ins][acc].val  = m.val]
       /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal, 
                  val |-> m.val, acc |-> acc])
  /\ UNCHANGED rmState
-----------------------------------------------------------------------------
PCNext ==  \* The next-state action
  \/ \E r \in RM : \/ RMPrepare(r) 
                   \/ RMChooseToAbort(r) 
                   \/ RMInferDecision(r)
  \/ \E bal \in Ballot \ {0}, r \in RM : Phase1a(bal, r) \/ Phase2a(bal, r)
  \/ \E acc \in Acceptor : Phase1b(acc) \/ Phase2b(acc)
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following part of the spec is not covered in Lecture 7.  It will be *)
(* explained in Lecture 8.                                                 *)
(***************************************************************************)
PCSpec == /\ PCInit
          /\ [][PCNext]_vars
          /\ \A bal \in Ballot \ {0}, r \in RM : /\ WF_vars(Phase1a(bal, r))
                                                 /\ WF_vars(Phase2a(bal, r))
          /\ \E MS \in Majority : \A ac \in MS :
                WF_vars(Phase1b(ac)) /\ WF_vars(Phase2b(ac))
          /\ \A r \in RM: WF_vars(RMInferDecision(r))
  (*************************************************************************)
  (* The complete spec of the Paxos Commit protocol.                       *)
  (*************************************************************************)

THEOREM PCSpec => []PCTypeOK
=============================================================================
\* Modification History
\* Last modified Fri Nov 23 22:38:11 EST 2018 by steve
\* Created Fri Nov 02 17:50:32 EDT 2018 by steve
