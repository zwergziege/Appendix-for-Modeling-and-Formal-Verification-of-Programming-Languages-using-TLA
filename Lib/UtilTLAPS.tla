----------------------------- MODULE UtilTLAPS -----------------------------

EXTENDS Integers, TLAPS, NaturalsInduction, Sequences, 
        WellFoundedInduction, FiniteSetTheorems, SequenceTheorems,
        Util
        

SetEq(A,B) == A \subseteq B /\ B \subseteq A

ContinuityPrerequisite(f) ==
  /\ f = [n \in Nat |-> f[n]]
  /\ \A n \in Nat : f[n] \subseteq f[n+1]

ContinuityResult(f,Op(_)) ==
  UNION {Op(f[n]) : n \in Nat} = Op(UNION {f[n] : n \in Nat})
  
IsContinuous(Op(_)) == 
  \A f : ContinuityPrerequisite(f) => ContinuityResult(f, Op)
  
USE DEF ContinuityPrerequisite, ContinuityResult

THEOREM ContinuousXYZ ==
  ASSUME NEW Op1(_), NEW Op2(_),
         IsContinuous(Op1),
         IsContinuous(Op2)
  PROVE  IsContinuous(LAMBDA p : Op1(p) \cup Op2(p))
  <1> QED BY DEF IsContinuous
  
THEOREM ContinuousConst == 
  ASSUME NEW x
  PROVE  IsContinuous(LAMBDA p : x) 
  BY DEF IsContinuous


(***************************************)

THEOREM FunctionEquality ==
  ASSUME NEW f, NEW g, IsFunction(f), IsFunction(g),
         DOMAIN f = DOMAIN g, \A arg \in DOMAIN f : f[arg] = g[arg]
  PROVE  f = g BY DEF IsFunction

THEOREM SeqInduction ==
  ASSUME NEW S, NEW P(_), P(<<>>),
         ASSUME NEW s \in S, NEW ss \in Seq(S), P(ss)
         PROVE  P(<<s>> \o ss)
  PROVE  \A seq \in Seq(S) : P(seq)
  <1> DEFINE SeqB(n) == {seq \in Seq(S) : Len(seq) = n}
             P2(n) == \A seq \in SeqB(n) : P(seq)
  <1> SUFFICES \A n \in Nat : P2(n) OBVIOUS
  <1> SUFFICES ASSUME NEW n \in Nat, P2(n) PROVE P2(n+1) BY P2(0), NatInduction
  <1> TAKE seq \in SeqB(n+1)
  <1> QED BY Tail(seq) \in SeqB(n), Head(seq) \in S, seq = <<Head(seq)>> \o Tail(seq)  

IfNatExistsUniversalNatExistsAssumption(S,P(_,_)) == 
  /\ \A s \in S, n \in Nat : P(s,n) => \A m \in Nat : P(s,n+m)
  /\ \A s \in S : \E n \in Nat : P(s,n)

IfNatExistsUniversalNatExistsConclusion(S,P(_,_)) == 
  \E n \in Nat : \A s \in S : P(s,n)
  
THEOREM IfNatExistsUniversalNatExists == 
  ASSUME NEW S, IsFiniteSet(S), NEW P(_,_), 
         IfNatExistsUniversalNatExistsAssumption(S,P)
  PROVE  IfNatExistsUniversalNatExistsConclusion(S,P)
  <1> PP(T) == IfNatExistsUniversalNatExistsConclusion(T,P)
  <1>0 PP({}) BY DEF IfNatExistsUniversalNatExistsConclusion      
  <1> SUFFICES PP(S) OBVIOUS
  <1> HIDE DEF PP
  <1> SUFFICES 
         ASSUME NEW T \in SUBSET S,
                \A U \in (SUBSET T) \ {T} : PP(U)
         PROVE  PP(T)
      BY FS_WFInduction
  <1> USE DEF PP
  <1> SUFFICES ASSUME T # {} PROVE PP(T)
      BY PP({}) DEF IfNatExistsUniversalNatExistsConclusion
  <1> DEFINE U(x) == T \ {x}
  <1> SUFFICES ASSUME NEW x \in T, PP(U(x)) PROVE PP(U(x) \cup {x}) OBVIOUS
  <1> U(x) \subseteq S OBVIOUS
  <1> HIDE DEF U
  <1> QED BY DEF IfNatExistsUniversalNatExistsAssumption, IfNatExistsUniversalNatExistsConclusion

(***************************************)
(* Inductive Definitions               *)
(***************************************)

RecFProperty(f, s0, next(_,_)) == 
  NatInductiveDefConclusion(f, s0, next) /\
  \A n \in Nat : 
    /\ f[n] = IF n = 0 THEN s0 ELSE next(f[n-1],n)
    /\ f[n+1] = next(f[n],n+1)
    /\ f[n] \subseteq RecDef(s0, next)
  
RecDefDepth(s0, next(_,_), s) ==
  LET f == RecF(s0,next)
     \* r[n \in Nat] == IF \E m \in 0..n : s \in f[m] THEN n ELSE r[n+1]
  IN  CHOOSE n \in Nat : s \in f[n] /\ \A m \in Nat : (s \in f[m] => (n <= m))
      \*IF s \in S THEN r[0] ELSE -1
  
RecDefOrdering(s0, next(_,_)) ==
  LET S == RecDef(s0,next)
      r(s) == RecDefDepth(s0, next, s)
  IN  { ss \in S \X S : r(ss[1]) < r(ss[2]) }       

THEOREM RecDefExists ==
  ASSUME NEW s0, NEW next(_,_), 
         NEW f, f = RecF(s0, next)
  PROVE  RecFProperty(f, s0, next)
    <1>I1 NatInductiveDefHypothesis(f, s0, next)
          BY DEF NatInductiveDefHypothesis, RecDef, RecF
    <1>I2 NatInductiveDefConclusion(f, s0, next)
          BY <1>I1, NatInductiveDef
    <1>a \A n \in Nat : f[n] = IF n = 0 THEN s0 ELSE next(f[n-1],n) BY <1>I2 DEF NatInductiveDefConclusion, RecFProperty
    <1>b \A n \in Nat : f[n+1] = next(f[n],n+1) BY ONLY <1>a
    <1>c \A n \in Nat : f[n] \subseteq RecDef(s0,next) BY <1>a DEF RecDef
    <1> QED BY <1>a, <1>b, <1>c, <1>I2 DEF RecFProperty

THEOREM RecDefContainsS0 == 
  ASSUME NEW s0, NEW next(_,_) PROVE s0 \subseteq RecDef(s0,next)
  <1> DEFINE f == RecF(s0,next)
  <1> RecFProperty(f,s0,next) BY RecDefExists
  <1> s0 = f[0] BY DEF RecFProperty
  <1> QED BY DEF RecDef

\* TODO: low usability
RecDefApproximationAssumption(S, s0, next_int(_)) ==
  /\ S = RecDef(s0, LAMBDA p,n: p \cup UNION {next_int(ps) : ps \in Seq(p)})

THEOREM RecDefApproximation ==
  ASSUME NEW S, NEW s0, NEW next_int(_),
  RecDefApproximationAssumption(S, s0, next_int) 
  PROVE  S = s0 \cup UNION {next_int(ps) : ps \in Seq(S)} 
  <1> DEFINE create(p) == UNION {next_int(ps) : ps \in Seq(p)}
             all(p)    == p \cup create(p)
             target(p) == s0 \cup create(p)
             Next(p,n) == all(p)
             f == RecF(s0, Next)
  <1> SUFFICES S = s0 \cup create(S) OBVIOUS
  <1>f f = [n \in Nat |-> IF n = 0 THEN s0 ELSE all(f[n-1])] 
    <2> HIDE DEF Next
    <2> NatInductiveDefConclusion(f, s0, Next) BY RecDefExists DEF RecFProperty
    <2> QED BY DEF NatInductiveDefConclusion, RecDefApproximationAssumption, Next
  <1>S S = UNION {f[n] : n \in Nat} BY DEF RecDef, RecDefApproximationAssumption
  <1> HIDE DEF f, all
  <1>a \A s \in S : s \in target(S)
    <2> DEFINE P(n) == \A s \in f[n] : s \in target(S)
    <2> SUFFICES \A n \in Nat : P(n) BY <1>S
    <2> SUFFICES ASSUME NEW n \in Nat, P(n) PROVE P(n+1) BY <1>f, P(0), NatInduction DEF all
    <2> SUFFICES ASSUME NEW s \in all(f[n]) PROVE s \in target(S) BY <1>f
    <2> QED BY <1>S DEF all
    \*<1> SUFFICES \A n \in Nat : \A s \in f[n] : s \in s0 \cup UNION {next_int(ps) : ps \in Seq(S)}
  <1>b \A s \in target(S) : s \in S
    <2> SUFFICES \A s \in create(S) : s \in S BY <1>S, <1>f, \A s \in s0 : s \in S
    <2> SUFFICES \A s \in create(S) : s \in UNION {all(f[n]) : n \in Nat} BY <1>f, <1>S DEF all
    <2> SUFFICES \A s \in create(S) : \E n \in Nat : s \in create(f[n]) BY DEF all
    <2>subset \A n,m \in Nat : f[n] \subseteq f[n+m]
      <3> TAKE n \in Nat
      <3> DEFINE P(m) == f[n] \subseteq f[n+m]
      <3> SUFFICES ASSUME NEW m \in Nat, P(m) PROVE P(m+1) BY NatInduction, P(0)
      <3> f[n+m+1] = all(f[n+m]) BY ONLY <1>f
      <3> QED BY DEF all  
    <2> \A seq \in Seq(S) : \E n \in Nat : seq \in Seq(f[n])
      <3> DEFINE P(seq) == \E n \in Nat : seq \in Seq(f[n])
      <3> SUFFICES ASSUME NEW s \in S, NEW seq \in Seq(S), P(seq) PROVE P(<<s>> \o seq) BY SeqInduction, P(<<>>)
      <3> DEFINE sseq == <<s>> \o seq
                 n1 == CHOOSE n \in Nat : s \in f[n]
                 n2 == CHOOSE n \in Nat : seq \in Seq(f[n])
                 ff == f[n1+n2]
      <3>n1 n1 \in Nat /\ s \in f[n1] BY <1>S
      <3>n2 n2 \in Nat /\ seq \in Seq(f[n2]) OBVIOUS
      <3> HIDE DEF n1, n2
      <3>n s \in ff /\ seq \in Seq(ff) BY <2>subset, <3>n1, <3>n2
      <3> SUFFICES sseq \in Seq(ff) BY <3>n1, <3>n2
      <3> HIDE DEF ff
      <3> QED BY ONLY <3>n
    <2> QED OBVIOUS
  <1> QED BY <1>a, <1>b DEF RecDefApproximationAssumption

THEOREM FixedPointAsRecDef == 
  ASSUME NEW s0, NEW next(_), 
         next({}) = {}, \* could be removed by setting defining s0_ == s0 \cup next({}) and next_(p) == next(p) \ next({})
         \A a,b : next(a) \cup next(b) \subseteq next(a \cup b)
  PROVE  FixedPoint(LAMBDA p : s0 \cup next(p)) = RecDef(s0, LAMBDA p,n : p \cup next(p))
  <1> DEFINE f1 == RecF({}, LAMBDA p,n : s0 \cup next(p))
             f2 == RecF(s0, LAMBDA p,n : p \cup next(p))
  <1>f1 f1 = [n \in Nat |-> IF n = 0 THEN {} ELSE s0 \cup next(f1[n-1])] 
    <2> RecFProperty(f1, {}, LAMBDA p,n : s0 \cup next(p)) BY RecDefExists
    <2> QED BY DEF RecFProperty, NatInductiveDefConclusion
  <1>f2 f2 = [n \in Nat |-> IF n = 0 THEN s0 ELSE f2[n-1] \cup next(f2[n-1])] 
    <2> RecFProperty(f2, s0, LAMBDA p,n :  p \cup next(p)) BY RecDefExists 
    <2> QED BY DEF RecFProperty, NatInductiveDefConclusion
  <1> SUFFICES UNION {f1[n] : n \in Nat} = UNION {f2[n] : n \in Nat} BY DEF FixedPoint, RecDef
  <1> HIDE DEF f1, f2
  <1>0 f1[0] = {} BY <1>f1
  <1>h \A n \in Nat : f1[n] \subseteq f1[n+1]
    <2> DEFINE P(n) == f1[n] \subseteq f1[n+1]
    <2>0 P(0) BY <1>f1
    <2> SUFFICES ASSUME NEW n \in Nat, P(n) PROVE P(n+1) BY NatInduction, <2>0
    <2> f1[n+1] = s0 \cup next(f1[n]) BY <1>f1
    <2> f1[n+2] = s0 \cup next(f1[n+1]) BY <1>f1
    <2> QED OBVIOUS
  <1> DEFINE P(n) == f1[n+1] = f2[n]
  <1> SUFFICES \A n \in Nat : P(n) BY <1>0
  <1>P0 P(0)
    <2> f1[1] = s0 \cup next(f1[0]) BY <1>f1
    <2> QED BY <1>f2, <1>0, f1[1] = s0
  <1> SUFFICES ASSUME NEW n \in Nat, P(n) PROVE P(n+1) BY NatInduction, <1>P0
  <1> f2[n+1] = f2[n] \cup next(f2[n]) BY <1>f2
  <1> f1[n+1+1] = s0 \cup next(f1[n+1]) BY <1>f1
  <1> f1[n+1] = s0 \cup next(f1[n]) BY <1>f1
  <1> QED BY <1>h
  
FixedPointNext(s0, p, next_int(_)) == s0 \cup UNION {next_int(ps) : ps \in Seq(p)}
  
FixedPointAssumption(S, s0, next_int(_)) ==
  /\ S = FixedPoint(LAMBDA p : FixedPointNext(s0, p, next_int))
 
THEOREM IsFixedPoint == 
  ASSUME NEW S, NEW s0, NEW next_int(_),
         FixedPointAssumption(S, s0, next_int)
  PROVE  S = FixedPointNext(s0, S, next_int)
  <1> USE DEF FixedPointNext
  <1> DEFINE Op(p) == FixedPointNext(s0, p, next_int)
             s0_ == s0 \cup next_int(<<>>)
             next_int_(p) == next_int(p) \ next_int(<<>>)
             Op_(p) == FixedPointNext(s0_, p, next_int_)
  <1>op \A p : Op_(p) = Op(p)
    <2> TAKE p
    <2>a Op_(p) \subseteq Op(p) BY <<>> \in Seq(p) DEF FixedPointNext
    <2>b Op(p) \subseteq Op_(p) BY DEF FixedPointNext
    <2> QED BY <2>a, <2>b
  <1> FixedPointAssumption(S, s0_, next_int_) BY <1>op DEF FixedPointAssumption
  <1> SUFFICES S = FixedPointNext(s0_, S, next_int_) BY <1>op
  <1> HIDE DEF s0_, next_int_
  <1> DEFINE next(p) == UNION {next_int_(ps) : ps \in Seq(p)}
             Next(p) == p \cup next(p)
  <1> S = RecDef(s0_, LAMBDA p,n : Next(p))
    <2> next({}) = {} BY Seq({}) = {<<>>} DEF next_int_
    <2> \A a,b : next(a) \cup next(b) \subseteq next(a \cup b) 
      <3> SUFFICES ASSUME NEW a, NEW b PROVE next(a) \subseteq next(a \cup b) OBVIOUS
      <3> QED BY Seq(a) \subseteq Seq(a \cup b) DEF FixedPointAssumption
    <2> QED BY FixedPointAsRecDef DEF FixedPointAssumption
  <1> RecDefApproximationAssumption(S,s0_,next_int_) 
      BY FixedPointAsRecDef DEF FixedPointAssumption, RecDefApproximationAssumption
  <1> QED BY RecDefApproximation DEF FixedPointAssumption

THEOREM IsFixedPoint2 ==
  ASSUME NEW next_int(_), NEW s0
  PROVE  HasFixedPoint(LAMBDA p : FixedPointNext(s0, p, next_int))
  <1> DEFINE Op(p) == FixedPointNext(s0, p, next_int)
  <1> FixedPointAssumption(FixedPoint(Op), s0, next_int) BY DEF FixedPointAssumption
  <1> QED BY IsFixedPoint DEF HasFixedPoint, IsFixedPointOfOp

THEOREM SeqIsContinuous == IsContinuous(Seq) 
  <1> SUFFICES ASSUME NEW f, f = [n \in Nat |-> f[n]], \A n \in Nat : f[n] \subseteq f[n + 1]
               PROVE  UNION {Seq(f[n]) : n \in Nat} = Seq(UNION {f[n] : n \in Nat})
      BY DEF IsContinuous
  <1> DEFINE OpUnion(Op(_)) == Op(UNION {f[n] : n \in Nat})
             UnionOp(Op(_)) == UNION {Op(f[n]) : n \in Nat}
             Target(Op(_))  == OpUnion(Op) = UnionOp(Op)
  <1> SUFFICES Target(Seq) OBVIOUS
  <1> SUFFICES OpUnion(Seq) \subseteq UnionOp(Seq) OBVIOUS
  <1> SUFFICES ASSUME NEW s \in OpUnion(Seq) PROVE \E n \in Nat : s \in Seq(f[n]) OBVIOUS
  <1> DEFINE P(m,n) == s[m] \in f[n]
  <1> \E n \in Nat : \A m \in DOMAIN s : P(m,n)
    <2> IsFiniteSet(DOMAIN s) BY DEF IsFiniteSet
    <2> SUFFICES IfNatExistsUniversalNatExistsAssumption(DOMAIN s, P) BY IfNatExistsUniversalNatExists DEF IfNatExistsUniversalNatExistsConclusion
    <2> \A m \in DOMAIN s : \E n \in Nat : P(m,n) OBVIOUS
    <2> \A m \in DOMAIN s, n \in Nat : P(m,n) => \A k \in Nat : P(m,n+k)
      <3> TAKE m \in DOMAIN s, n \in Nat
      <3> HAVE P(m,n)
      <3> DEFINE PP(k) == P(m,n+k)
      <3> SUFFICES ASSUME NEW k \in Nat, PP(k) PROVE PP(k+1) BY PP(0), NatInduction
      <3> QED OBVIOUS
    <2> QED BY DEF IfNatExistsUniversalNatExistsAssumption 
  <1> QED OBVIOUS
  
THEOREM ASSUME NEW next(_) PROVE IsContinuous(LAMBDA p : UNION {next(ps) : ps \in Seq(p)}) 
  <1> DEFINE Next(p) == UNION {next(ps) : ps \in Seq(p)}
  <1> SUFFICES IsContinuous(Next) OBVIOUS
  <1> HIDE DEF Next
  <1> SUFFICES ASSUME NEW f, f = [n \in Nat |-> f[n]], \A n \in Nat : f[n] \subseteq f[n + 1]
               PROVE  UNION {Next(f[n]) : n \in Nat} = Next(UNION {f[n] : n \in Nat})
      BY DEF IsContinuous
  <1> DEFINE Target(Op(_))  == UNION {Op(f[n]) : n \in Nat} = Op(UNION {f[n] : n \in Nat})
  <1> SUFFICES Target(Seq)
    <2> SUFFICES 
       UNION {next(ps) : ps \in UNION {Seq(f[n]) : n \in Nat}}
       = UNION {UNION {next(ps) : ps \in Seq(f[n])} : n \in Nat}
       BY DEF Next
    <2> QED OBVIOUS
  <1> QED BY SeqIsContinuous DEF IsContinuous
         
THEOREM ContinuityEntailsLinearCup ==
  ASSUME NEW Op(_), IsContinuous(Op) 
  PROVE \A a,b : Op(a) \cup Op(b) \subseteq Op(a \cup b)
  <1> SUFFICES \A a,b : Op(a) \subseteq Op(a \cup b) OBVIOUS
  <1> TAKE a,b
  <1> DEFINE f == [n \in Nat |-> IF n = 0 THEN a ELSE a \cup b ]
  <1> UNION {Op(f[n]) : n \in Nat} = Op(UNION {f[n] : n \in Nat}) 
    <2> f = [n \in Nat |-> f[n]] OBVIOUS
    <2> \A n \in Nat : f[n] \subseteq f[n+1] OBVIOUS
    <2> HIDE DEF f
    <2> QED BY DEF IsContinuous
  <1> QED OBVIOUS
  
THEOREM ContinuityResultOfFixedPointRecF ==
  ASSUME NEW Op(_), IsContinuous(Op)
  PROVE  ContinuityPrerequisite(RecF({}, LAMBDA p,n : Op(p)))
  <1> DEFINE f == RecF({}, LAMBDA p,n : Op(p))
             P(n) == f[n] \subseteq f[n+1] 
  <1>f f = [n \in Nat |-> IF n = 0 THEN {} ELSE Op(f[n-1])] 
    <2> NatInductiveDefConclusion(f, {}, LAMBDA p,n : Op(p)) BY RecDefExists DEF RecFProperty
    <2> QED BY RecDefExists DEF NatInductiveDefConclusion
  <1> SUFFICES \A n \in Nat : P(n)
    <2> IsContinuous(Op)!(f) BY DEF IsContinuous
    <2> QED BY <1>f
  <1> HIDE DEF f
  <1>fn \A n \in Nat : f[n+1] = Op(f[n]) BY <1>f
  <1>0 P(0) BY <1>f
  <1> SUFFICES ASSUME NEW n \in Nat, P(n) PROVE P(n+1) BY NatInduction, <1>0
  <1> f[n+1] = Op(f[n]) BY ONLY <1>fn
  <1> f[n+2] = Op(f[n+1]) BY ONLY <1>fn
  <1> \A a, b : Op(a) \cup Op(b) \subseteq Op(a \cup b) BY ContinuityEntailsLinearCup
  <1> QED OBVIOUS
  
IFP3A(S,s0,next(_)) == 
  /\ S = RecDef({}, LAMBDA p,n : s0 \cup next(p))
  /\ IsContinuous(next)
  
THEOREM IsFixedPoint3 ==
  ASSUME NEW next(_), NEW s0, NEW S, IFP3A(S,s0,next)
  PROVE  S = s0 \cup next(S)
  <1> DEFINE Next(p,n) == s0 \cup next(p)
             f == RecF({},Next)
  <1>f f = [n \in Nat |-> IF n = 0 THEN {} ELSE Next(f[n-1],n)] 
    <2> HIDE DEF Next 
    <2> NatInductiveDefConclusion(f, {}, Next) BY RecDefExists DEF RecFProperty
    <2> QED BY RecDefExists DEF NatInductiveDefConclusion, Next
  <1> HIDE DEF f
  <1>fn \A n \in Nat : f[n+1] = s0 \cup next(f[n])
    <2> DEFINE Def(n) == IF n = 0 THEN {} ELSE s0 \cup next(f[n-1])
    <2>b f = [n \in Nat |-> Def(n)] BY <1>f \* wat?? why is this needed
    <2> HIDE DEF Def
    <2> TAKE n \in Nat
    <2> f[n+1] = Def(n+1) BY ONLY <2>b
    <2> QED BY DEF Def
  <1>S1 S = UNION {f[n] : n \in Nat} BY DEF IFP3A, RecDef, f
  <1>S2 S = s0 \cup UNION {next(f[n]) : n \in Nat} 
    <2> S = UNION {f[n+1] : n \in Nat} BY <1>f, <1>S1
    <2> SUFFICES \A n \in Nat : f[n+1] = s0 \cup next(f[n])
      <3> S = UNION {s0 \cup next(f[n]) : n \in Nat} OBVIOUS
      <3> QED OBVIOUS
    <2> QED BY <1>fn
  <1> SUFFICES UNION {next(f[n]) : n \in Nat} = next(UNION {f[n] : n \in Nat}) BY <1>S1, <1>S2
  <1> DEFINE P(n) == f[n] \subseteq f[n+1] 
  <1> SUFFICES \A n \in Nat : P(n)
    <2> IsContinuous(next)!(f) BY DEF IFP3A, IsContinuous
    <2> QED BY <1>f
  <1>0 P(0) BY <1>f
  <1> SUFFICES ASSUME NEW n \in Nat, P(n) PROVE P(n+1) BY NatInduction, <1>0
  <1> f[n+1] = s0 \cup next(f[n]) BY ONLY <1>fn
  <1> f[n+2] = s0 \cup next(f[n+1]) BY ONLY <1>fn
  <1> \A a, b : next(a) \cup next(b) \subseteq next(a \cup b) BY ContinuityEntailsLinearCup DEF IFP3A
  <1> QED OBVIOUS
  
IFP4A(S,s0,next(_)) == 
  /\ S = RecDef(s0, LAMBDA p,n : p \cup next(p))
  /\ IsContinuous(next)
  
THEOREM IsFixedPoint4 ==
  ASSUME NEW next(_), NEW s0, NEW S, IFP4A(S,s0,next)
  PROVE  S = s0 \cup next(S)
  <1> DEFINE Next(p,n) == p \cup next(p)
             f == RecF(s0,Next)
  <1>f f = [n \in Nat |-> IF n = 0 THEN s0 ELSE Next(f[n-1], n)] 
    <2> HIDE DEF Next 
    <2> NatInductiveDefConclusion(f, s0, Next) BY RecDefExists DEF RecFProperty
    <2> QED BY RecDefExists DEF NatInductiveDefConclusion, Next
  <1> HIDE DEF f
  <1>fn \A n \in Nat : f[n+1] = f[n] \cup next(f[n])
    <2> DEFINE Def(n) == IF n = 0 THEN s0 ELSE f[n-1] \cup next(f[n-1])
    <2>b f = [n \in Nat |-> Def(n)] BY <1>f \* wat?? why is this needed
    <2> HIDE DEF Def
    <2> TAKE n \in Nat
    <2> f[n+1] = Def(n+1) BY ONLY <2>b
    <2> QED BY DEF Def
  <1>S1 S = UNION {f[n] : n \in Nat} BY DEF IFP4A, RecDef, f
  <1>S2 S = s0 \cup UNION {next(f[n]) : n \in Nat}
    <2>S S = s0 \cup UNION {f[n+1] : n \in Nat} BY <1>f, <1>S1
    <2> SUFFICES S \subseteq s0 \cup UNION {next(f[n]) : n \in Nat} 
      <3> SUFFICES s0 \cup UNION {next(f[n]) : n \in Nat} \subseteq S OBVIOUS
      <3> QED BY <1>fn, <2>S
    <2> DEFINE target == s0 \cup UNION {next(f[n]) : n \in Nat}
               P(n) == \A s \in f[n] : s \in target
    <2> SUFFICES \A s \in UNION {f[n] : n \in Nat} : s \in target BY <1>S1
    <2> SUFFICES \A n \in Nat : P(n) OBVIOUS
    <2>0 P(0) BY <1>f
    <2> SUFFICES ASSUME NEW n \in Nat, P(n) PROVE P(n+1) BY <2>0, NatInduction
    <2> QED BY <1>fn
  <1> UNION {next(f[n]) : n \in Nat} = next(UNION {f[n] : n \in Nat})
    <2> \A n \in Nat : f[n] \subseteq f[n+1] BY <1>fn
    <2> SUFFICES IsContinuous(next)!(f) BY <1>f
    <2> QED BY DEF IFP4A, IsContinuous
  <1> QED BY <1>f, <1>S1, <1>S2
  
IFP5A(S,Op(_)) == 
  /\ S = FixedPoint(Op)
  /\ IsContinuous(Op)
  
THEOREM IsFixedPoint5 ==
  ASSUME NEW Op(_), NEW S, IFP5A(S,Op)
  PROVE  S = Op(S)
  <1> DEFINE s0 == {}
  <1>a IFP3A(S,s0,Op) BY DEF IFP5A, IFP3A, FixedPoint
  <1> HIDE DEF s0
  <1> S = s0 \cup Op(S) BY ONLY IsFixedPoint3, <1>a
  <1> QED BY DEF s0
  
THEOREM IsLeastFP ==
  ASSUME NEW Op(_), IsContinuous(Op)
  PROVE  IsLeastFixedPointOfOp(FixedPoint(Op), Op)
  <1> DEFINE LFP == FixedPoint(Op) 
             f == RecF({}, LAMBDA p,n : Op(p))
  <1> SUFFICES ASSUME NEW FP, FP = Op(FP)
               PROVE  LFP \subseteq FP
      BY IsFixedPoint5 DEF IFP5A, IsLeastFixedPointOfOp, IsFixedPointOfOp
  <1> SUFFICES \A n \in Nat : f[n] \subseteq FP
      BY LFP = UNION {f[n] : n \in Nat} DEF FixedPoint, RecDef
  <1> NatInductiveDefConclusion(f, {}, LAMBDA p,n : Op(p)) BY RecDefExists DEF RecFProperty
  <1> IsContinuous(Op) BY DEF IFP5A
  <1> HIDE DEF f
  <1> DEFINE P(n) == f[n] \subseteq FP
  <1> P(0) BY DEF NatInductiveDefConclusion
  <1> SUFFICES ASSUME NEW n \in Nat, f[n] \subseteq FP
               PROVE  P(n+1)
      BY NatInduction
  <1> SUFFICES Op(f[n]) \subseteq FP BY f[n+1] = Op(f[n]) DEF NatInductiveDefConclusion
  <1> \A a,b : Op(a) \cup Op(b) \subseteq Op(a \cup b) BY ContinuityEntailsLinearCup
  <1> QED BY FP = Op(f[n] \cup FP)
    
THEOREM HierarchicInduction == 
  ASSUME NEW s0, NEW next(_,_), NEW P(_), 
         \A m \in s0 : P(m),
         \A n \in Nat : (\A m \in RecF(s0,next)[n] : P(m)) => (\A m \in next(RecF(s0,next)[n],n+1) : P(m)) 
  PROVE  \A m \in RecDef(s0,next) : P(m)
    <1> DEFINE f == RecF(s0,next)
    <1>E RecFProperty(f,s0,next) BY RecDefExists 
    <1>a \A m \in f[0] : P(m) BY <1>E DEF RecFProperty
    <1>b \A n \in Nat : (\A m \in RecF(s0,next)[n] : P(m)) => (\A m \in RecF(s0,next)[n+1] : P(m)) BY <1>E DEF RecFProperty
    <1> SUFFICES \A n \in Nat : \A m \in f[n] : P(m) BY DEF RecDef
    <1> QED BY NatInduction, <1>a, <1>b DEF RecDef
    
RecDefDepthProperty(s0, next(_,_), s) ==
  LET d == RecDefDepth(s0, next, s)
  IN  /\ d \in Nat 
      /\ s \in RecF(s0,next)[d] 
      /\ \A m \in Nat : (s \in RecF(s0,next)[m] => (d <= m))
      /\ \A m \in Nat : m < d => s \notin RecF(s0,next)[m]

THEOREM RecDefDepthExists == 
  ASSUME NEW s0, NEW next(_,_), NEW s \in RecDef(s0, next)
  PROVE  RecDefDepthProperty(s0,next,s)
  <1> USE DEF RecDefDepthProperty
  <1> DEFINE f    == RecF(s0,next)
             p(n) == s \in f[n]
             P(n) == s \in f[n] /\ \A m \in Nat : (s \in f[m] => (n <= m))
             depth == RecDefDepth(s0,next,s)
  <1> SUFFICES \E n \in Nat : P(n) BY DEF depth, RecDefDepth, f
  <1>a \E n \in Nat : p(n) BY DEF f, RecDef
  <1> SUFFICES ASSUME NEW N \in Nat, p(N) PROVE \E n \in Nat : p(n) /\ \A m \in 0..n-1 : ~p(m) BY <1>a
  <1> HIDE DEF p
  <1> QED BY SmallestNatural
        
THEOREM RecursiveDefinedOrderingIsWellFounded ==
  ASSUME NEW s0, NEW next(_,_)
  PROVE IsWellFoundedOn(RecDefOrdering(s0, next), RecDef(s0, next))
  <1> DEFINE R == RecDefOrdering(s0, next)
             S == RecDef(s0, next)
             depth(s) == RecDefDepth(s0,next,s)
             f == RecF(s0, next)
  <1> HIDE DEF depth, f, S, R
  <1> USE DEF RecDefDepthProperty 
  <1> SUFFICES ASSUME NEW g \in [Nat -> S], \A n \in Nat : <<g[n+1], g[n]>> \in R
               PROVE FALSE BY DEF IsWellFoundedOn, R, S    
  <1> DEFINE h == [n \in Nat |-> depth(g[n])]
  <1>a \A n \in Nat : h[n+1] < h[n] BY DEF R, RecDefOrdering, depth
  <1>bh ASSUME NEW s \in S, NEW d, d=depth(s)
        PROVE s \in f[d] /\ (\A m \in Nat : s \in f[m] => d =< m) BY RecDefDepthExists, <1>bh DEF S, f, depth
  <1>b h \in [Nat -> Nat] BY RecDefDepthExists, <1>bh DEF depth, RecDefDepth
  <1> HIDE DEF h
  <1>nwf ~IsWellFoundedOn(OpToRel(<,Nat), Nat) BY <1>a, <1>b DEF IsWellFoundedOn, OpToRel
  <1> QED BY NatLessThanWellFounded, <1>nwf
  
  
THEOREM WFDefOnSuffices == 
  ASSUME NEW s0, NEW next(_,_), NEW Def(_,_), NEW fun, 
         fun = CHOOSE f : f = [s \in RecDef(s0, next) |-> Def(f,s)],
         ASSUME NEW g, NEW h, NEW n \in Nat, NEW s \in RecF(s0, next)[n],
                n = RecDefDepth(s0,next,s),
                \A y \in UNION {RecF(s0, next)[m] : m \in 0..n-1} : g[y] = h[y]
         PROVE  Def(g,s) = Def(h,s)
  PROVE  fun = [ss \in RecDef(s0,next) |-> Def(fun, ss)]
  <1> DEFINE S          == RecDef(s0, next)
             R          == RecDefOrdering(s0, next)
             f          == RecF(s0, next)
             depth(s)   == RecDefDepth(s0,next,s)
  <1> HIDE DEF S
  <1> SUFFICES fun = [s \in S |-> Def(fun,s)] BY DEF S
  <1> SUFFICES WFDefOn(R,S,Def) 
    <2>a OpDefinesFcn(fun, S, Def) BY DEF OpDefinesFcn, S
    <2>b IsWellFoundedOn(R,S) BY RecursiveDefinedOrderingIsWellFounded DEF S
    <2> QED BY WFInductiveDef, <2>a, <2>b DEF WFInductiveDefines
  <1>e SUFFICES ASSUME NEW g, NEW h, NEW s \in S, \A y \in SetLessThan(s, R, S) : g[y] = h[y],
                       NEW n, n = depth(s)
                PROVE Def(g,s) = Def(h,s) BY DEF WFDefOn 
  <1>Ed n \in Nat /\ s \in f[n] /\ (\A m \in Nat : s \in f[m] => n =< m) 
        BY RecDefDepthExists, <1>e DEF S, f, depth, RecDefDepthProperty
  <1>Ef RecFProperty(f, s0, next) BY RecDefExists 
  <1>subset ASSUME NEW m \in Nat PROVE f[m] \subseteq S BY <1>Ef DEF S, RecDef, RecFProperty
  <1>sn s \in f[n] BY <1>Ed, <1>e DEF S
  <1>sp \A y \in UNION {f[m] : m \in 0..n-1} : g[y] = h[y]
    <2>0 CASE n = 0 BY <2>0
    <2> SUFFICES ASSUME NEW m \in 0..(n-1), n # 0 PROVE f[m] \subseteq SetLessThan(s, R, S) BY <1>e, <2>0
    <2> HIDE DEF f, R
    <2> SUFFICES \A y \in f[m] : <<y,s>> \in R 
      <3> SUFFICES \A y \in f[m] : y \in {yy \in S : <<yy, s>> \in R} BY DEF SetLessThan
      <3> SUFFICES f[m] \subseteq S OBVIOUS
      <3> QED BY <1>subset
    <2>mNat m \in Nat OBVIOUS
    <2>mSmall m < n BY <2>mNat, <1>Ed
    <2>fSubS f[m] \subseteq S BY <1>Ef, <2>mNat DEF S, f, RecDef, RecFProperty
    <2> SUFFICES \A y \in f[m] : depth(y) < depth(s) BY <2>fSubS DEF R, RecDefOrdering, S
    <2> HIDE DEF depth
    <2> SUFFICES ASSUME NEW y \in f[m], NEW k, k = depth(y) PROVE k < n BY <1>e
    <2>Ed k \in Nat /\ y \in f[k] /\ (\A l \in Nat : y \in f[l] => k =< l) 
          BY RecDefDepthExists, <2>fSubS DEF S, f, depth, RecDefDepthProperty
    <2> SUFFICES k <= m BY <2>mSmall, <2>Ed, <1>Ed
    <2> QED BY <2>Ed
  <1> QED BY <1>sp, <1>Ed, <1>e

\* TODO: Beautification: FunOverRecDefExists this and WFDefOnSuffices
RecFSmaller(s0,next(_,_),n) == UNION {RecF(s0, next)[m] : m \in 0..n-1}
RecFExistsAssumption(s0, next(_,_), Def(_,_)) ==
  \A n \in Nat : \A s \in RecF(s0,next)[n] : 
    n = RecDefDepth(s0,next,s) =>
    \A f : Def(f,s) = Def(Restrict(f, RecFSmaller(s0,next,n)),s)

THEOREM FunOverRecDefExists == 
  ASSUME NEW s0, NEW next(_,_), NEW Def(_,_), NEW fun, 
         fun = CHOOSE f : f = [s \in RecDef(s0, next) |-> Def(f,s)],
         RecFExistsAssumption(s0, next, Def)
  PROVE  fun = [ss \in RecDef(s0,next) |-> Def(fun, ss)]
  <1> SUFFICES ASSUME NEW g, NEW h, NEW n \in Nat, NEW s \in RecF(s0, next)[n],
                      n = RecDefDepth(s0,next,s),
                      \A y \in UNION {RecF(s0, next)[m] : m \in 0..n-1} : g[y] = h[y]
               PROVE  Def(g,s) = Def(h,s) BY WFDefOnSuffices
  <1> DEFINE Res(f) == Restrict(f, RecFSmaller(s0,next,n))
  <1> SUFFICES Def(Res(g),s) = Def(Res(h),s) BY DEF RecFExistsAssumption
  <1> QED BY DEF Restrict, RecFSmaller

Composite(DefS(_),T) == UNION {DefS(t) : t \in T}
RecWrapN(DefS(_),s0,next(_,_),n) == Composite(DefS, RecF(s0,next)[n])
RecursiveWrap(DefS(_),s0,next(_,_)) == 
  LET rwn(n) == RecWrapN(DefS,s0,next,n)
  IN  RecDef(rwn(0), LAMBDA p,n: rwn(n))

RecCompAssumption(DefS(_),inv(_)) ==
  \A T : \A t \in T : \A s \in DefS(t) : inv(s) = t
  
THEOREM RecursiveComposition ==
  ASSUME NEW DefS(_), NEW s0, NEW next(_,_)
  PROVE  Composite(DefS, RecDef(s0, next)) = RecursiveWrap(DefS,s0,next)
  <1> USE DEF Composite, RecWrapN
  <1> DEFINE C(T) == Composite(DefS,T)
             S0        == C(RecF(s0,next)[0])
             Next(p,n) == C(RecF(s0,next)[n])
             F == RecF(S0,Next)  
             f == RecF(s0,next)
  <1>E RecFProperty(F,S0,Next) BY RecDefExists
  <1> HIDE DEF F, f
  <1>F F = [ n \in Nat |-> C(f[n]) ] BY <1>E DEF RecFProperty, NatInductiveDefConclusion, f
  <1>R RecDef(S0, Next) = UNION {C(f[n]) : n \in Nat} BY <1>F DEF F, f, RecDef
  <1> SUFFICES C(UNION {f[n] : n \in Nat}) = UNION {C(f[n]) : n \in Nat} BY <1>R DEF RecDef, RecursiveWrap, f
  <1> QED OBVIOUS

RecCompDepthProperty(DefS(_), s0, next(_,_), inv(_)) ==
  \A s \in RecursiveWrap(DefS,s0,next) : 
     RecDefDepth(RecWrapN(DefS,s0,next,0), LAMBDA p,n: RecWrapN(DefS,s0,next,n), s) =
     RecDefDepth(s0,next,inv(s))
  
THEOREM RecursiveCompositionDepth ==
  ASSUME NEW DefS(_), NEW s0, NEW next(_,_), NEW inv(_), RecCompAssumption(DefS,inv)
  PROVE RecCompDepthProperty(DefS,s0,next,inv)
  <1> USE DEF RecCompDepthProperty, Composite, RecWrapN
  <1> TAKE s \in RecursiveWrap(DefS,s0,next)
  <1> DEFINE C(T) == Composite(DefS, T)
             S0        == RecWrapN(DefS,s0,next,0)
             Next(p,n) == RecWrapN(DefS,s0,next,n)
             t == inv(s)
             tD == RecDefDepth(s0,next,t)
             sD == RecDefDepth(S0,Next,s)
             f == RecF(s0,next)
             F == RecF(S0,Next)
  <1>rw s \in C(RecDef(s0,next)) BY RecursiveComposition
  <1>t t \in RecDef(s0,next) /\ s \in DefS(t) BY <1>rw DEF RecCompAssumption
  <1>sD RecDefDepthProperty(S0, Next, s) BY RecDefDepthExists DEF RecursiveWrap
  <1>tD RecDefDepthProperty(s0, next, t) BY RecDefDepthExists, <1>t
  <1> SUFFICES sD = tD OBVIOUS
  <1>Fe RecFProperty(F, S0, Next) BY RecDefExists
  <1>F F = [n \in Nat |-> C(f[n])] BY <1>Fe DEF RecFProperty, NatInductiveDefConclusion
  <1> HIDE DEF t, S0, Next
  <1> SUFFICES t \in f[sD] /\ s \in C(f[tD]) BY <1>sD, <1>tD, <1>F DEF RecDefDepthProperty
  <1>a s \in C(f[tD]) BY <1>tD, <1>t DEF RecDefDepthProperty
  <1>b t \in f[sD] 
    <2> s \in C(f[sD]) BY <1>sD, <1>F DEF RecDefDepthProperty
    <2> QED BY <1>t DEF RecCompAssumption
  <1> QED BY <1>a, <1>b
  
BaseNat      == {0}
NextNat(p,n) == {n}

THEOREM NatProp == 
  /\ Nat = RecDef(BaseNat, NextNat) 
  /\ RecF(BaseNat, NextNat) = [n \in Nat |-> {n}]
  /\ \A n \in Nat : n = RecDefDepth(BaseNat, NextNat, n)
  <1> DEFINE f == RecF(BaseNat, NextNat) 
  <1> RecFProperty(f, BaseNat, NextNat) BY RecDefExists
  <1> f = [n \in Nat |-> {n}] BY RecDefExists DEF RecFProperty, BaseNat, NextNat, NatInductiveDefConclusion
  <1>a Nat = RecDef(BaseNat, NextNat)
    <2> QED BY DEF RecDef
  <1>b \A n \in Nat : n = RecDefDepth(BaseNat, NextNat, n)
    <2> TAKE n \in Nat
    <2> RecDefDepthProperty(BaseNat, NextNat, n) BY RecDefDepthExists, <1>a
    <2> QED BY DEF RecDefDepthProperty
  <1> QED BY <1>a, <1>b

(***********************************************************************************)
(* Stuff                                                                           *)
(***********************************************************************************)

IsReflexive(S,R(_,_)) == \A a \in S : R(a,a)
IsSymmetric(S,R(_,_)) == \A a,b \in S : R(a,b) <=> R(b,a)
IsTransitive(S,R(_,_)) == \A a,b,c \in S : (R(a,b) /\ R(b,c)) => R(a,c) 
IsEquivalence(S,R(_,_)) == IsSymmetric(S,R) /\ IsReflexive(S,R) /\ IsTransitive(S,R)

IsCompatible(S,R(_,_),Fs) ==
  \A f \in Fs, n \in Nat : \A arg1, arg2 \in SeqN(S,n) :
    arg1 \in DOMAIN f => 
    /\ arg2 \in DOMAIN f 
    /\ (\A idx \in DOMAIN arg1 : R(arg1[idx],arg2[idx])) => R(f[arg1],f[arg2])
IsCongruence(S,R(_,_),Fs) == IsEquivalence(S,R) /\ IsCompatible(S,R,Fs)

THEOREM SeqInduction2Silly == 
  ASSUME NEW S, NEW P(_,_), 
         \A x \in Seq(S) : P(x, <<>>) /\ P(<<>>, x),
         \A x, y \in S, xs, ys \in Seq(S) : 
           /\ P(<<x>> \o xs, ys) 
           /\ P(xs,ys) 
           /\ P(xs, <<y>> \o ys)
           => P(<<x>> \o xs, <<y>> \o ys)
  PROVE  \A xs,ys \in Seq(S) : P(xs,ys)
  <1> PP(xs) == \A ys \in Seq(S) : P(xs,ys)
  <1> SUFFICES \A xs \in Seq(S) : PP(xs) OBVIOUS
  <1> SUFFICES ASSUME NEW x \in S, NEW xs \in Seq(S), PP(xs)
               PROVE PP(<<x>> \o xs) BY SeqInduction, PP(<<>>)
  <1> SUFFICES ASSUME NEW y \in S, NEW ys \in Seq(S), P(<<x>> \o xs,ys)
               PROVE P(<<x>> \o xs, <<y>> \o ys) BY <<x>> \o xs \in Seq(S), P(<<x>> \o xs, <<>>), SeqInduction
  <1> QED BY <<y>> \o ys \in Seq(S)
  
THEOREM 
  ASSUME NEW S, NEW P(_),
         P(<<>>), \A s \in S : P(<<s>>),
         \A x1, x2 \in S, xs \in Seq(S) : P(xs) <=> P(<<x1,x2>> \o xs)
  PROVE  \A xs \in Seq(S) : P(xs)
  <1> DEFINE PP(xs) == \A x \in S : P(<<x>> \o xs)
             PPP(xs) == P(xs) => PP(xs)
  <1> SUFFICES \A xs \in Seq(S), x \in S : P(xs) => P(<<x>> \o xs) 
    <2> SUFFICES ASSUME NEW x \in S, NEW xs \in Seq(S), P(xs)
                 PROVE  P(<<x>> \o xs) 
        BY SeqInduction
    <2> QED OBVIOUS
  <1> SUFFICES \A xs \in Seq(S) : PPP(xs) OBVIOUS  
  \*<1> SUFFICES \A xs \in Seq(S) : PP(xs) OBVIOUS  
  <1>0 PP(<<>>) BY \A y : <<y>> \o <<>> = <<y>>
  <1> SUFFICES ASSUME NEW x \in S, NEW xs \in Seq(S), PPP(xs)
               PROVE PPP(<<x>> \o xs)
      BY SeqInduction, <1>0
  <1> HAVE P(<<x>> \o xs)
  <1> TAKE x2 \in S
  <1> SUFFICES P(<<x2,x>> \o xs) OBVIOUS
  <1> QED OBVIOUS
  
THEOREM SeqInduction2 == 
  ASSUME NEW S, NEW P(_),
         P(<<>>), \A s \in S : P(<<s>>),
         \A x1, x2 \in S, xs \in Seq(S) : P(xs) => P(<<x1,x2>> \o xs)
  PROVE  \A xs \in Seq(S) : P(xs)
  <1> DEFINE Base == {<<>>} \cup {<<s>> : s \in S}
             Next(p,n) == {<<v[1],v[2]>> \o v[3] : v \in S \X S \X p}
             f == RecF(Base,Next)
             SeqS == RecDef(Base,Next)
  <1> HIDE DEF Base, Next, f, SeqS
  <1>S SeqS = UNION {f[n] : n \in Nat} BY DEF SeqS, f, RecDef
  <1>SS SeqS = Seq(S)
    <2> DEFINE SeqSN(n) == {s \in Seq(S) : Len(s) = n}
    <2>h \A n \in Nat : f[n] = SeqSN(2*n) \cup SeqSN(2*n+1)
      <3>f f = [n \in Nat |-> IF n = 0 THEN Base ELSE Next(f[n-1],n)] BY RecDefExists DEF f, RecFProperty, NatInductiveDefConclusion
      <3> DEFINE target(n) == SeqSN(2*n) \cup SeqSN(2*n+1)
                 PP(n) == f[n] = target(n)
      <3>0 PP(0) 
        <4> SUFFICES Base = SeqSN(0) \cup SeqSN(1) BY <3>f
        <4> SeqSN(0) = {<<>>} OBVIOUS
        <4> SeqSN(1) = {<<s>> : s \in S}
          <5> SeqSN(1) \subseteq {<<s>> : s \in S} OBVIOUS
          <5> {<<s>> : s \in S} \subseteq SeqSN(1) OBVIOUS
          <5> QED OBVIOUS
        <4> QED BY DEF Base
      <3>n SUFFICES ASSUME NEW n \in Nat, PP(n) PROVE PP(n+1) BY NatInduction, <3>0
      <3> f[n + 1] = Next(f[n], n+1) BY <3>f
      <3>a f[n+1] \subseteq target(n+1)
        <4> DEFINE PPP(s) == s \in target(n+1)
        <4> SUFFICES \A s \in f[n+1] : PPP(s) OBVIOUS
        <4> HIDE DEF PPP
        <4> SUFFICES ASSUME NEW s1 \in S, NEW s2 \in S, NEW ss \in f[n] PROVE PPP(<<s1,s2>> \o ss) BY DEF Next
        <4> QED BY <3>n DEF PPP
      <3>b target(n+1) \subseteq f[n+1]
        <4> SUFFICES ASSUME NEW s \in Seq(S), Len(s) = 2*n + 2 \/ Len(s) = 2*n + 2 + 1 PROVE s \in Next(f[n], n+1) OBVIOUS
        <4> DEFINE PPP(s1,s2,ss) == s = <<s1,s2>> \o ss
        <4> SUFFICES \E v \in S \X S \X f[n] : PPP(v[1],v[2],v[3]) BY DEF Next
        <4> SUFFICES \E s1 \in S, s2 \in S, ss \in f[n] : PPP(s1,s2,ss) OMITTED
        <4> DEFINE st == Tail(Tail(s))
        <4>con <<s[1], s[2]>> \o st = s
          <5> <<s[1]>> \o Tail(s) = s OBVIOUS
          <5> <<s[1]>> \o (<<s[2]>> \o st) = s BY Head(Tail(s)) = s[2], Tail(s) = <<s[2]>> \o st
          <5> QED BY ConcatAssociative
        <4>len Len(st) = Len(s) - 2 
          <5> Len(Tail(s)) = Len(s) - 1 OBVIOUS
          <5> QED BY Len(st) = Len(Tail(s)) - 1
        <4>st st \in Seq(S)
          <5> DEFINE t == Tail(s)
          <5> t \in Seq(S) OBVIOUS
          <5> Len(t) > 0 OBVIOUS
          <5> st = Tail(t) OBVIOUS
          <5> HIDE DEF t, st
          <5> QED OBVIOUS
        <4> s[1] \in S /\ s[2] \in S OBVIOUS
        <4> HIDE DEF st
        <4> st \in f[n] BY <4>con, <4>len, <4>st, <3>n 
        <4> QED BY <4>con
      <3> QED BY <3>a, <3>b
    <2> Seq(S) = UNION {SeqSN(n) : n \in Nat} OBVIOUS
    <2> HIDE DEF SeqSN
    <2> SeqS = UNION {SeqSN(2*n) \cup SeqSN(2*n+1) : n \in Nat} BY <1>S, <2>h
    <2> SUFFICES Seq(S) \subseteq SeqS OBVIOUS
    <2> SUFFICES \A n \in Nat : SeqSN(n) \subseteq SeqS OBVIOUS
    <2> SUFFICES \A n \in Nat : \E m \in Nat : n = 2*m \/ n = 2*m+1 OBVIOUS
    <2> QED BY \A n \in Nat : (n = 2 * (n \div 2) \/ n = 2 * (n \div 2) + 1) /\ n \div 2 \in Nat
  <1> SUFFICES \A ss \in SeqS : P(ss) BY <1>SS 
  <1>0 \A ss \in Base : P(ss) BY DEF Base
  <1>n \A n \in Nat : (\A ss \in f[n] : P(ss)) => \A ss \in Next(f[n],n+1) : P(ss) 
    <2> SUFFICES ASSUME NEW n \in Nat, \A ss \in f[n] : P(ss) PROVE \A ns \in Next(f[n],n+1) : P(ns) OBVIOUS
    <2> SUFFICES ASSUME NEW s1 \in S, NEW s2 \in S, NEW ss \in f[n] PROVE P(<<s1,s2>> \o ss) BY DEF Next
    <2> QED BY <1>SS, <1>S
  <1> QED BY <1>0, <1>n, HierarchicInduction DEF SeqS, f

(***********************************************************************************)
(* Util Theorems                                                                   *)
(***********************************************************************************)

THEOREM MapMapFRange == 
  ASSUME NEW L, NEW R, DOMAIN L = DOMAIN R
  PROVE MapMapF(L,R) \in [Range(L) -> Range(R)]
  <1> \A arg \in DOMAIN R : R[arg] \in Range(R) BY DEF Range
  <1> SUFFICES ASSUME NEW l \in Range(L) PROVE \E o \in DOMAIN L : L[o] = l BY DEF MapMapF
  <1> QED BY DEF Range

THEOREM MapMapFBijective == 
  ASSUME NEW L, NEW R, DOMAIN L = DOMAIN R, IsBijective(L)
  PROVE \A arg \in DOMAIN L : MapMapF(L,R)[L[arg]] = R[arg]
  <1> TAKE arg \in DOMAIN L
  <1> SUFFICES {o \in DOMAIN L : L[o] = L[arg]} = {arg} BY DEF MapMapF, Range
  <1> QED BY DEF IsBijective

THEOREM ASSUME NEW S, NEW L(_), NEW R(_)
        PROVE  MapMapF([s \in S |-> L(s)], [s \in S |-> R(s)]) = MapMap(S,L,R)
        BY DEF MapMapF, MapMap, Range

IfLowestExistsConclusion(P(_),f,_ \prec _) ==
  \E arg \in DOMAIN f : P(f[arg]) /\ \A arg2 \in DOMAIN f : (P(f[arg2]) => \neg (arg2 \prec arg))

THEOREM IfExistsLowestExists ==
  ASSUME NEW P(_), NEW f,  NEW _ \prec _, \E arg \in DOMAIN f : P(f[arg]), 
         IsWellFoundedOn(OpToRel(\prec, DOMAIN f), DOMAIN f)
  PROVE  IfLowestExistsConclusion(P, f, \prec)
  <1> USE DEF IfLowestExistsConclusion
  <1> DEFINE subset == {arg \in DOMAIN f : P(f[arg])}
  <1> subset # {} /\ subset \subseteq DOMAIN f OBVIOUS
  <1> SUFFICES \E arg \in subset : \A arg2 \in subset : <<arg2, arg>> \notin OpToRel(\prec, DOMAIN f) BY DEF OpToRel
  <1> HIDE DEF subset
  <1> QED BY WFMin
  
THEOREM IfExistsLowestIdxExists == 
  ASSUME NEW P(_), NEW f, DOMAIN f \in SUBSET Nat, \E arg \in DOMAIN f : P(f[arg])
  PROVE  IfLowestExistsConclusion(P, f, <)
  <1> USE DEF IfLowestExistsConclusion
  <1> DEFINE a \prec b == a < b
  <1> IsWellFoundedOn(OpToRel(\prec, DOMAIN f), DOMAIN f) 
    <2> IsWellFoundedOn(OpToRel(<, Nat), DOMAIN f) BY NatLessThanWellFounded, IsWellFoundedOnSubset
    <2> SUFFICES OpToRel(<, DOMAIN f) \cap Nat \X Nat \subseteq OpToRel(<, Nat) BY IsWellFoundedOnSubrelation
    <2> QED BY DEF OpToRel
  <1> HIDE DEF \prec
  <1> \E arg \in DOMAIN f : P(f[arg]) /\ \A arg2 \in DOMAIN f : (P(f[arg2]) => \neg (arg2 \prec arg))
      BY IfExistsLowestExists
  <1> QED BY DEF \prec
  
UniqueChooseIfExistsAssumption(S, I, Iint(_,_), error) ==
  /\ I = [s \in S |-> ChooseIfExists({Iint(s,n) : n \in Nat}, LAMBDA res : res # error, error)]
  /\ \A s \in S, n \in Nat : Iint(s,n) # error => Iint(s,n) = Iint(s,n+1)
UniqueChooseIfExistsConclusion(S, I, Iint(_,_), error) ==
  \A s \in S, n \in Nat : 
    /\ Iint(s,n) \in {I[s], error}
    /\ Iint(s,n) = I[s] => \A m \in Nat : n<m => Iint(s,m) = I[s]

THEOREM UniqueChooseIfExists == 
  ASSUME NEW S, NEW I, NEW Iint(_,_), NEW error,
         UniqueChooseIfExistsAssumption(S, I, Iint, error) 
  PROVE  UniqueChooseIfExistsConclusion(S, I, Iint, error)
  <1> USE DEF UniqueChooseIfExistsAssumption, UniqueChooseIfExistsConclusion
  <1> \A s \in S, n \in Nat :
        Iint(s,n) # error => \A m \in Nat : n<m => Iint(s,m) = Iint(s,n)
    <2> DEFINE P2(s,n,m) == n<m => Iint(s,m) = Iint(s,n)
               P1(s,n) == Iint(s,n) # error => \A m \in Nat : P2(s,n,m)
               P(n) == \A s \in S : P1(s,n)
    <2> TAKE s \in S, n \in Nat
    <2> HAVE Iint(s,n) # error
    <2>m0 P2(s,n,0) OBVIOUS
    <2> SUFFICES ASSUME NEW m \in Nat, P2(s,n,m) PROVE P2(s,n,m+1) BY NatInduction, <2>m0
    <2> HAVE n<m+1
    <2> Iint(s,m) = Iint(s,n) BY n = m \/ n < m
    <2> QED OBVIOUS
  <1> \A s \in S, n \in Nat : Iint(s,n) \in {I[s], error}
    <2> TAKE s \in S
    <2> DEFINE fun == [n \in Nat |-> Iint(s,n)]
               Perr(x)   == x # error
               Psmall(n) == Perr(fun[n]) /\ \A m \in Nat : Perr(fun[m]) => \neg (m < n)
               smallN    == CHOOSE n \in Nat : Psmall(n)
    <2> SUFFICES ASSUME \E n \in Nat : Perr(fun[n]) PROVE \A n \in Nat : fun[n] \in {I[s],error} OBVIOUS
    <2> Psmall(smallN) /\ smallN \in Nat
      <3> IfLowestExistsConclusion(Perr,fun,<) BY IfExistsLowestIdxExists
      <3> QED BY DEF IfLowestExistsConclusion
    <2> HIDE DEF smallN
    <2>a \A n \in Nat : n < smallN  => fun[n] = error OBVIOUS
    <2>b \A n \in Nat : smallN <= n => fun[n] = fun[smallN]
      <3> TAKE n \in Nat 
      <3> HAVE smallN <= n
      <3> QED BY fun[smallN] # error, n = smallN \/ smallN < n
    <2> \A n \in Nat : Iint(s,n) \in {error, Iint(s,smallN)}
      <3> TAKE n \in Nat
      <3> n < smallN \/ smallN <= n BY ONLY smallN \in Nat
      <3> QED BY <2>a, <2>b
    <2> Iint(s,smallN) = I[s] BY DEF Range, ChooseIfExists
    <2> QED OBVIOUS
  <1> QED OBVIOUS

=============================================================================