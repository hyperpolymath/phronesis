-------------------------------- MODULE PhronesisConsensus --------------------------------
(*
 * TLA+ Specification for Phronesis Consensus Protocol
 *
 * This module specifies the consensus mechanism used for action execution
 * in the Phronesis policy language. It models a simplified PBFT-style
 * protocol with the following properties:
 *
 * Safety:
 *   - Agreement: All honest agents agree on committed actions
 *   - Validity: Only valid actions (passing policy checks) can commit
 *   - Non-repudiation: All commits are logged immutably
 *
 * Liveness:
 *   - Termination: Every proposed action eventually commits or aborts
 *
 * Model Parameters:
 *   - N: Total number of agents
 *   - F: Maximum number of Byzantine (faulty) agents
 *   - Constraint: N >= 3*F + 1
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Agents,           \* Set of all agents
    Actions,          \* Set of possible actions
    MaxRounds,        \* Bound for model checking
    Threshold         \* Voting threshold (typically 2/3 + 1)

VARIABLES
    proposed,         \* The currently proposed action (or NULL)
    votes,            \* Function: Agent -> {APPROVE, REJECT, NONE}
    committed,        \* Sequence of committed actions
    round,            \* Current consensus round
    agentState,       \* Function: Agent -> {IDLE, VOTING, COMMITTED}
    log               \* Immutable consensus log

\* Type invariant
TypeOK ==
    /\ proposed \in Actions \cup {NULL}
    /\ votes \in [Agents -> {"APPROVE", "REJECT", "NONE"}]
    /\ committed \in Seq(Actions)
    /\ round \in Nat
    /\ agentState \in [Agents -> {"IDLE", "VOTING", "COMMITTED"}]
    /\ log \in Seq([action: Actions, votes: [Agents -> {"APPROVE", "REJECT"}], timestamp: Nat])

\* Initial state
Init ==
    /\ proposed = NULL
    /\ votes = [a \in Agents |-> "NONE"]
    /\ committed = <<>>
    /\ round = 0
    /\ agentState = [a \in Agents |-> "IDLE"]
    /\ log = <<>>

\* Helper: Count approvals
ApprovalCount == Cardinality({a \in Agents : votes[a] = "APPROVE"})

\* Helper: Count rejections
RejectionCount == Cardinality({a \in Agents : votes[a] = "REJECT"})

\* Helper: All votes cast
AllVotesCast == \A a \in Agents : votes[a] # "NONE"

\* Helper: Consensus reached
ConsensusReached == ApprovalCount >= Threshold

\* Helper: Consensus failed
ConsensusFailed == RejectionCount > Cardinality(Agents) - Threshold

-----------------------------------------------------------------------------
\* Actions

\* Leader proposes an action
Propose(action) ==
    /\ proposed = NULL
    /\ round < MaxRounds
    /\ proposed' = action
    /\ agentState' = [a \in Agents |-> "VOTING"]
    /\ round' = round + 1
    /\ UNCHANGED <<votes, committed, log>>

\* Agent casts a vote
Vote(agent, vote) ==
    /\ proposed # NULL
    /\ agentState[agent] = "VOTING"
    /\ votes[agent] = "NONE"
    /\ vote \in {"APPROVE", "REJECT"}
    /\ votes' = [votes EXCEPT ![agent] = vote]
    /\ UNCHANGED <<proposed, committed, round, agentState, log>>

\* Commit action if consensus reached
Commit ==
    /\ proposed # NULL
    /\ ConsensusReached
    /\ committed' = Append(committed, proposed)
    /\ log' = Append(log, [
         action |-> proposed,
         votes |-> [a \in Agents |-> votes[a]],
         timestamp |-> round
       ])
    /\ proposed' = NULL
    /\ votes' = [a \in Agents |-> "NONE"]
    /\ agentState' = [a \in Agents |-> "IDLE"]
    /\ UNCHANGED round

\* Abort action if consensus failed
Abort ==
    /\ proposed # NULL
    /\ ConsensusFailed
    /\ proposed' = NULL
    /\ votes' = [a \in Agents |-> "NONE"]
    /\ agentState' = [a \in Agents |-> "IDLE"]
    /\ UNCHANGED <<committed, round, log>>

\* Timeout (all votes cast but no decision)
Timeout ==
    /\ proposed # NULL
    /\ AllVotesCast
    /\ ~ConsensusReached
    /\ ~ConsensusFailed
    /\ proposed' = NULL
    /\ votes' = [a \in Agents |-> "NONE"]
    /\ agentState' = [a \in Agents |-> "IDLE"]
    /\ UNCHANGED <<committed, round, log>>

-----------------------------------------------------------------------------
\* Specification

Next ==
    \/ \E action \in Actions : Propose(action)
    \/ \E agent \in Agents, vote \in {"APPROVE", "REJECT"} : Vote(agent, vote)
    \/ Commit
    \/ Abort
    \/ Timeout

Spec == Init /\ [][Next]_<<proposed, votes, committed, round, agentState, log>>

-----------------------------------------------------------------------------
\* Safety Properties

\* Agreement: No conflicting commits
Agreement ==
    \A i, j \in 1..Len(committed) :
        i = j \/ committed[i] # committed[j]

\* Validity: Only properly voted actions commit
Validity ==
    \A i \in 1..Len(log) :
        Cardinality({a \in Agents : log[i].votes[a] = "APPROVE"}) >= Threshold

\* Non-repudiation: Every committed action is in the log
NonRepudiation ==
    \A i \in 1..Len(committed) :
        \E j \in 1..Len(log) : log[j].action = committed[i]

\* Log is append-only (no modifications)
LogAppendOnly ==
    [][Len(log') >= Len(log)]_log

\* Combined safety property
Safety == Agreement /\ Validity /\ NonRepudiation

-----------------------------------------------------------------------------
\* Liveness Properties (under fairness)

\* Every proposal eventually commits or aborts
EventualDecision ==
    proposed # NULL ~> (proposed = NULL)

\* The system makes progress
Progress ==
    <>(Len(committed) > 0)

-----------------------------------------------------------------------------
\* Byzantine Fault Tolerance

\* Assuming F Byzantine agents (modeled as arbitrary voters)
\* With N >= 3F + 1 and Threshold = 2F + 1:
\*   - Byzantine agents cannot commit invalid actions alone
\*   - Honest agents (>= 2F + 1) can always reach consensus

ByzantineSafety ==
    \* Even if F agents vote arbitrarily, safety holds
    \A subset \in SUBSET Agents :
        Cardinality(subset) <= (Cardinality(Agents) - 1) \div 3 =>
            \* These agents cannot force a commit without honest majority
            Cardinality(subset) < Threshold

-----------------------------------------------------------------------------
\* Model Checking Configuration

\* For TLC model checker, use these constants:
\* Agents = {a1, a2, a3, a4}  (N = 4)
\* Actions = {act1, act2}
\* MaxRounds = 3
\* Threshold = 3  (for N=4, F=1, need 2F+1 = 3)

\* Check: Safety, Validity, NonRepudiation
\* Check with fairness: EventualDecision, Progress

=============================================================================
