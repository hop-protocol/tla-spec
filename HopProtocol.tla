----------------------- MODULE HopProtocol ------------------------------------
EXTENDS Integers, Naturals, TLC, Sequences, FiniteSets

VARIABLES
  l1Chain,
  l2Chain,
  chains,
  pendingTransfers,
  commitThreshold,
  bondedWithdrawals,
  roots


\*-----------------------

SumSeq(S) ==
  LET seq == S
      Sum[ i \in 1..Len(seq) ] == IF i = 1 THEN seq[i] ELSE seq[i] + Sum[i-1]
  IN IF seq = <<>> THEN 0 ELSE Sum[Len(seq)]

RECURSIVE SeqFromSet(_)
SeqFromSet(S) ==
  IF S = {} THEN << >>
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  << x >> \o SeqFromSet(S \ {x})

Range(s) == {s[x] : x \in DOMAIN s}

Hash(v) == CHOOSE n \in 1..5: TRUE

ASSUME(Hash(<<1>>) = Hash(<<1>>))
ASSUME(Hash(<<{1,2,3}>>) = Hash(<<{2,1,3,1}>>))

\*-----------------------

Init ==
  /\ l1Chain = 1
  /\ l2Chain = 2..3
  /\ chains = 1..3
  /\ pendingTransfers = [c \in l2Chain |-> <<>>]
  /\ commitThreshold = 1
  /\ roots = [c \in chains |-> <<>>]
  /\ bondedWithdrawals = [c \in chains |-> {}]

SendTransfer(c) ==
  /\ c # 1
  /\ Len(pendingTransfers[c]) < 5
  /\ pendingTransfers' = [pendingTransfers EXCEPT ![c] = pendingTransfers[c] \o <<[
      target |-> chains, amount |-> 1, id |-> Hash(1..2)
     ]>>]
  /\ Print(<<"send", Len(pendingTransfers[c])>>, TRUE)
  /\ UNCHANGED <<l1Chain, l2Chain, chains, roots, commitThreshold, bondedWithdrawals>>

CommitTransfers(c) ==
  /\ c # 1
  /\ Len(roots[c]) < 20
  /\ SumSeq([x \in DOMAIN pendingTransfers[c] |-> pendingTransfers[c][x].amount]) > commitThreshold
  /\ Print(<<"commit">>, TRUE)
  /\ pendingTransfers' = [pendingTransfers EXCEPT ![c] = <<>>]
  /\ roots' = [k \in chains |-> roots[k] \o <<Hash(pendingTransfers[c])>>]
  /\ UNCHANGED <<l1Chain, l2Chain, chains, commitThreshold, bondedWithdrawals>>

BondWithdrawal(dest) ==
  /\ \E source \in l2Chain:
    /\ Len(pendingTransfers[source]) > 0
    /\ \E x \in DOMAIN pendingTransfers[source] :
      /\ pendingTransfers[source][x].id \notin bondedWithdrawals[dest]
      /\ bondedWithdrawals' = [bondedWithdrawals EXCEPT ![dest] = bondedWithdrawals[dest] \cup {pendingTransfers[source][x].id}]
      /\ Print(<<"bondWithdrawal", bondedWithdrawals'>>, TRUE)
    /\ UNCHANGED <<l1Chain, l2Chain, chains, commitThreshold, pendingTransfers, roots>>

Next ==
  /\ \E c \in chains :
      /\ \/ SendTransfer(c)
         \/ CommitTransfers(c)
         \/ BondWithdrawal(c)

AllHaveTransferRoots == /\ \A c \in chains :
                            /\ Len(roots[c]) > 0
                            /\ \A k \in chains: Range(roots[c]) \cap Range(roots[k]) # {}

AllHaveBondedWithdrawals == /\ \A c \in chains :
                                /\ Len(SeqFromSet(bondedWithdrawals[c])) > 0

EventuallyAllHaveTransferRoots == <>[]AllHaveTransferRoots
EventuallyAllHaveBondedWithdrawals == <>[]AllHaveBondedWithdrawals

vars == <<l1Chain, l2Chain, chains, pendingTransfers, commitThreshold, roots, bondedWithdrawals>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Live == EventuallyAllHaveTransferRoots /\ EventuallyAllHaveBondedWithdrawals
===============================================================================
