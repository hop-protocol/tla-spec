----------------------- MODULE HopProtocol ------------------------------------
EXTENDS Integers, Naturals, TLC, Sequences, FiniteSets

CONSTANT
  B,      \* block
  CT      \* commit threshold

VARIABLES
  C      \* chain

Pick(S) == CHOOSE s \in S : TRUE

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) ==
  IF S = {} THEN value
  ELSE LET s == Pick(S)
       IN IF Op(s, value) = Op(value, s)
       THEN SetReduce(Op, S \ {s}, Op(s, value))
       ELSE Assert(FALSE, "Err")

SumSeq(S) ==
  LET seq == S
      Sum[ i \in 1..Len(seq) ] == IF i = 1 THEN seq[i] ELSE seq[i] + Sum[i-1]
  IN IF seq = <<>> THEN 0 ELSE Sum[Len(seq)]

RECURSIVE SeqFromSet(_)
SeqFromSet(S) ==
  IF S = {} THEN << >>
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  << x >> \o SeqFromSet(S \ {x})


Hash(v) == CHOOSE n \in {Int}: TRUE

ASSUME(Hash(<<1>>) = Hash(<<1>>))
ASSUME(Hash(<<{1,2,3}>>) = Hash(<<{2,1,3,1}>>))

TypeOK ==
  /\ B \subseteq 1..5
  /\ \E c \in 1..2 : C[c].h \in 1..5

Init ==
  /\ C = [c \in 1..2 |-> [
      id  |-> c,                 \* chain id
      h   |-> 1,                 \* block height
      pt  |-> <<>>,              \* pending transfers
      pts |-> 0,                 \* pending transfers sum
      tr  |-> 0                  \* transfer root
    ]]

Add(c) ==
  LET s == <<(RandomElement(1..2))>> \o C[c].pt IN s

Send(c) ==
  /\ Print(<<C>>, TRUE)
  /\ C[c].pts < 3
  /\ C' = [C EXCEPT ![c] = [
      id  |-> C[c].id,
      h   |-> C[c].h,
      pt  |-> Add(c),
      pts |-> SumSeq(Add(c)),
      tr  |-> C[c].tr
    ]]

Commit(c) ==
  /\ C[c].pts > CT
  /\ C' = [C EXCEPT ![c] = [
      id  |-> C[c].id,
      h   |-> C[c].h,
      pt  |-> <<>>,
      pts |-> 0,
      tr  |-> C[c].pts
    ]]

Next == /\ \E bn \in B:
          \/ /\ \E c \in DOMAIN C:
                /\ \/ Send(C[c].id)
                   \/ Commit(C[c].id)
          \/ /\ C' = [c \in DOMAIN C|-> [
                  id  |-> C[c].id,
                  h   |-> bn,
                  pt  |-> C[c].pt,
                  pts |-> C[c].pts,
                  tr  |-> C[c].tr
                ]]

Spec == Init /\ [][Next]_<<C>>
===============================================================================