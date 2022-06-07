---------------------------- MODULE UtilDeno ----------------------------

EXTENDS Integers, NaturalsInduction, Util

CONSTANTS DefI(_,_), States, Error

DefInternalI(I,n) == [state \in States |-> IF n = 0 THEN Error ELSE DefI(I[n-1], state)]
InternalI[n \in Nat] == DefInternalI(InternalI, n)
I(state) == ChooseIfExists({InternalI[n][state] : n \in Nat}, LAMBDA x : x # Error, Error)
  
THEOREM IExists == InternalI = [n \in Nat |-> DefInternalI(InternalI, n)]
  <1> DEFINE f0 == [state \in States |-> Error]
             fn(p,n) == [state \in States |-> DefI(p,state)]
             Def(f,n) == IF n = 0 THEN f0 ELSE fn(f[n-1],n)
  <1>same \A f,n : DefInternalI(f,n) = Def(f,n) BY DEF DefInternalI
  <1> SUFFICES ASSUME InternalI = CHOOSE f : f = [n \in Nat |-> Def(f,n)]
               PROVE  InternalI = [n \in Nat |-> Def(InternalI,n)]
    BY <1>same DEF InternalI
  <1> HIDE DEF f0, fn
  <1> QED BY NatInductiveDef DEF NatInductiveDefHypothesis, NatInductiveDefConclusion
  
=============================================================================