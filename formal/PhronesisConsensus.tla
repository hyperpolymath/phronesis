-------------------------------- MODULE PhronesisConsensus --------------------------------
(*
 * SPDX-License-Identifier: MPL-2.0
 * Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
 *
 * TLA+ specification of the Phronesis action-commit consensus, modelled as a
 * single-round Byzantine quorum protocol (PBFT-style core).
 *
 * KEY MODELLING CHOICES (design decision 2026-06-14):
 *   - Agents have INDIVIDUAL commit views (committed[agent][round]), so
 *     "Agreement" is the genuine BFT property: no two HONEST agents commit
 *     different values for the same round.
 *   - The adversary is strong: a subset `Byzantine` may EQUIVOCATE (vote for
 *     several conflicting values), AND honest agents may receive different
 *     values for the same round (modelling a faulty/equivocating PROPOSER) —
 *     each honest agent still votes at most ONCE per round.
 *
 * Safety then rests on QUORUM INTERSECTION (not on a trusted proposer): with
 * N = |Agents|, F = |Byzantine|, N >= 3F+1 and Threshold = 2F+1, any two
 * Threshold-quorums share >= F+1 agents, hence >= 1 honest agent; since an
 * honest agent votes at most once per round, two conflicting values cannot
 * both reach a quorum. The threshold is LOAD-BEARING: lowering it below 2F+1
 * makes TLC report an Agreement violation (see the negative test in CI).
 *
 * Run:  tlc PhronesisConsensus.tla -config PhronesisConsensus.cfg
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Agents,       \* set of all agents (N = Cardinality(Agents))
    Actions,      \* set of proposable actions
    MaxRounds,    \* number of consensus rounds modelled (rounds are independent)
    Threshold,    \* quorum size (intended 2F+1)
    Byzantine,    \* subset of Agents that may equivocate (|Byzantine| <= F)
    NULL          \* "no value" marker

ASSUME ByzantineSubsetOfAgents == Byzantine \subseteq Agents

Honest == Agents \ Byzantine
Rounds == 1..MaxRounds

VARIABLES
    msgs,       \* [Rounds -> SUBSET (Agents \X Actions)] : vote messages cast
    committed   \* [Agents -> [Rounds -> Actions \cup {NULL}]] : per-agent commit view

vars == <<msgs, committed>>

\* Distinct senders who voted for action v in round r.
Senders(r, v) == { a \in Agents : <<a, v>> \in msgs[r] }

\* Has honest agent a already voted in round r?
HonestVoted(a, r) == \E v \in Actions : <<a, v>> \in msgs[r]

------------------------------------------------------------------------------
TypeOK ==
    /\ msgs \in [Rounds -> SUBSET (Agents \X Actions)]
    /\ committed \in [Agents -> [Rounds -> Actions \cup {NULL}]]

Init ==
    /\ msgs = [r \in Rounds |-> {}]
    /\ committed = [a \in Agents |-> [r \in Rounds |-> NULL]]

------------------------------------------------------------------------------
\* Actions

\* An HONEST agent votes ONCE per round, for the value it was delivered. The
\* delivered value is chosen over all Actions to model a faulty/equivocating
\* proposer that may split the vote across honest agents.
HonestVote(a, r, v) ==
    /\ a \in Honest
    /\ v \in Actions
    /\ ~HonestVoted(a, r)
    /\ msgs' = [msgs EXCEPT ![r] = @ \cup {<<a, v>>}]
    /\ UNCHANGED committed

\* A BYZANTINE agent may vote for ANY action (equivocation: possibly several).
ByzVote(a, r, v) ==
    /\ a \in Byzantine
    /\ v \in Actions
    /\ msgs' = [msgs EXCEPT ![r] = @ \cup {<<a, v>>}]
    /\ UNCHANGED committed

\* An honest agent commits v for round r once it observes a Threshold-quorum.
Commit(a, r, v) ==
    /\ a \in Honest
    /\ committed[a][r] = NULL
    /\ Cardinality(Senders(r, v)) >= Threshold
    /\ committed' = [committed EXCEPT ![a][r] = v]
    /\ UNCHANGED msgs

Next ==
    \/ \E a \in Agents, r \in Rounds, v \in Actions : HonestVote(a, r, v)
    \/ \E a \in Agents, r \in Rounds, v \in Actions : ByzVote(a, r, v)
    \/ \E a \in Agents, r \in Rounds, v \in Actions : Commit(a, r, v)

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------------
\* Safety properties

\* AGREEMENT (the genuine BFT property): no two honest agents commit different
\* values for the same round. Holds by quorum intersection iff Threshold >= 2F+1.
Agreement ==
    \A a, b \in Honest, r \in Rounds :
        (committed[a][r] # NULL /\ committed[b][r] # NULL)
            => committed[a][r] = committed[b][r]

\* VALIDITY: an honest agent only commits a value backed by a Threshold-quorum.
Validity ==
    \A a \in Honest, r \in Rounds :
        committed[a][r] # NULL =>
            Cardinality(Senders(r, committed[a][r])) >= Threshold

\* BYZANTINE SAFETY (state-level): a committed value cannot be forged by the
\* Byzantine minority alone. Every honest commit is backed by at least
\* (Threshold - |Byzantine|) HONEST senders, provided Threshold > |Byzantine|.
ByzantineSafety ==
    /\ Threshold > Cardinality(Byzantine)
    /\ \A a \in Honest, r \in Rounds :
         committed[a][r] # NULL =>
             Cardinality(Senders(r, committed[a][r]) \cap Honest)
                 >= Threshold - Cardinality(Byzantine)

\* Combined safety.
Safety == TypeOK /\ Agreement /\ Validity /\ ByzantineSafety

=============================================================================
