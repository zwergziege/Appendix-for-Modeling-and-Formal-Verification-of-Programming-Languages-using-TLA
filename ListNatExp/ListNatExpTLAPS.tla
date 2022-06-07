-------------------------- MODULE ListNatExpTLAPS --------------------------
EXTENDS FiniteSets, Sequences, ListNatExp, UtilTLAPS, Util, TLAPS, WellFoundedInduction, NaturalsInduction

Aux == INSTANCE ListNatExpAux

USE DEF PrintMTAST, PrintTAST, PrintMAST, PrintAST, PrintT
USE DEF Tags, Types, PartialFunctions
USE DEF W_funEnv

\* ugly to use. 
\* - with external definition additional steps are required (see SI <1>b -> <2>f)
\* - with additional parameter for depth, depth has to be defined at all times
\* - with depth internal, depth is always expanded -> harder for PS + contains LAMBDAs which smt can't handle...
ASTDepth(ast) == RecDefDepth(BaseAST, NextAST, ast)
ASTRec == RecF(BaseAST, NextAST)

THEOREM ListProp == \A l \in Lists : "op" \in DOMAIN l /\ l.op = "List"
  <1> DEFINE f  == RecF(BaseList, NextList)
             P(l) == "op" \in DOMAIN l /\ l.op = "List"
  <1> SUFFICES \A l \in Lists : P(l) OBVIOUS
  <1>base ASSUME NEW l \in BaseList PROVE P(l) BY DEF BaseList, List, Value
  <1> HIDE DEF f, P
  <1>next ASSUME NEW n \in Nat, \A l \in f[n] : P(l), NEW l \in NextList(f[n],n+1) PROVE P(l) BY <1>next DEF NextList, List, Value, P
  <1> QED BY <1>base, <1>next, HierarchicInduction DEF Lists, f

ASTProperty(ast) == 
    LET depth == ASTDepth(ast)
        p == ASTRec[depth-1]
    IN  /\ "op" \in DOMAIN ast
        /\ ast.op = "Nat"       => (depth = 0 /\ ast \in Naturals)
        /\ ast.op = "List"      => (depth = 0 /\ ast \in Lists)
        /\ ast.op = "Bool"      => (depth = 0 /\ ast \in Bools)
        /\ ast.op = "Var"       => (depth = 0 /\ ast \in Vars)
        /\ ast.op = "Error"     => (depth = 0 /\ ast = Error)
        /\ ast.op = "Cond"      => (depth # 0 /\ ast \in Conds(p))
        /\ ast.op = "FunCall"   => (depth # 0 /\ ast \in FunCalls(p)) 
        /\ ast.op = "BuiltIn"   => (depth # 0 /\ ast \in BuiltIns(p))
        /\ ast.op = "ListCtor"  => (depth # 0 /\ ast \in ListCtors(p))
        /\ ast.op \in Tags
        /\ depth # 0 => p \subseteq ASTs

THEOREM ASTProp == 
  ASSUME NEW ast \in ASTs
  PROVE  ASTProperty(ast)
  <1> DEFINE s0 == BaseAST
             f == RecF(s0,NextAST)
             depth == ASTDepth(ast)
  <1>ast ast \in RecDef(s0, NextAST) BY DEF ASTs 
  <1> ASTRec = f BY DEF ASTRec
  <1> HIDE DEF f
  <1>Ef RecFProperty(f, s0, NextAST) BY RecDefExists DEF f
  <1>Ed RecDefDepthProperty(s0, NextAST, ast) BY RecDefDepthExists, <1>ast
  <1> SUFFICES ASSUME NEW n \in Nat, n = depth PROVE ASTProperty(ast) BY <1>Ed DEF f, RecDefDepthProperty, ASTDepth, ASTRec
  <1>astD ast \in f[n] BY <1>Ed DEF RecDefDepthProperty, f, ASTDepth, ASTRec
  <1>n0 ASSUME NEW m \in Nat, m # 0 PROVE f[m] = NextAST(f[m-1],m) BY <1>n0, <1>Ef DEF RecFProperty 
  <1>a CASE n = 0
    <2>s0 ast \in s0 
      <3> SUFFICES ast \in f[0] BY <1>Ef DEF RecFProperty
      <3> QED BY <1>a, <1>Ed DEF s0, ASTDepth, ASTRec, RecDefDepthProperty, f
    <2>dom "op" \in DOMAIN ast /\ ast.op \in {"Nat","Var","Bool","List", "Error"} 
           BY ONLY <2>s0, ListProp DEF s0, BaseAST, Naturals, Vars, Bools, Error, Bool, Natural, Value
    <2> /\ \A l \in Lists : l.op = "List"
        /\ \A v \in Vars : v.op = "Var"
        /\ \A b \in Bools : b.op = "Bool"
        /\ \A m \in Naturals : m.op = "Nat"
        /\ Error.op = "Error"
        BY ListProp DEF Naturals, Vars, Bools, Bool, Natural, Value, Error
    <2> QED BY <1>a, <2>s0, <2>dom DEF ASTProperty, BaseAST
  \*  <2> QED BY ONLY <1>a, <2>s0, <2>dom, <2>e, ListProp DEF ASTProperty, Tags, BaseAST, Naturals, Vars, Bools, Bool, Natural, Value
  <1>b CASE n # 0
    <2>next ast \in NextAST(f[n-1],n)!2
      <3> SUFFICES ast \in NextAST(f[n-1],n) /\ ast \notin f[n-1] BY DEF NextAST, ASTDepth, ASTRec
      <3>a ast \in NextAST(f[n-1],n) BY <1>n0, <1>b, <1>astD
      <3>b ast \notin f[n-1] BY <1>Ed, <1>b DEF RecDefDepthProperty, f, depth, ASTDepth, ASTRec
      <3> QED BY <3>a, <3>b
    <2>d0 ast.op \in {"Cond","FunCall","BuiltIn", "ListCtor"} BY <2>next DEF Conds, FunCalls, BuiltIns, ListCtors
    <2>n n-1 \in Nat BY ONLY <1>b
    <2>p RecF(s0,NextAST)[n-1] \subseteq ASTs BY <1>Ef, <2>n DEF f, RecFProperty, ASTs, s0
    <2> SUFFICES 
          /\ "op" \in DOMAIN ast
          /\ ast.op = "Cond"      => ast \in Conds(f[n-1])
          /\ ast.op = "FunCall"  => ast \in FunCalls(f[n-1])
          /\ ast.op = "BuiltIn"   => ast \in BuiltIns(f[n-1])
          /\ ast.op = "ListCtor" => ast \in ListCtors(f[n-1])
        BY <2>d0, <1>b, <2>p DEF ASTProperty, f, s0, Tags
    <2> QED BY <2>next, <1>b DEF Conds, FunCalls, BuiltIns, ListCtors
  <1> QED BY <1>a, <1>b

OrderedSubASTs(ast) ==
  CASE ast.op \in {"FunCall", "BuiltIn", "ListCtor"} -> ast.args
  []   ast.op = "Cond" -> [arg \in {"cond","then","else"} |-> ast[arg]]
  []   OTHER -> <<>>

StripSubASTs(ast) ==
  CASE ast.op \in {"FunCall", "BuiltIn", "ListCtor"} -> RestrictBy(ast,{"args"})
  []   ast.op = "Cond" -> RestrictBy(ast,{"cond","then","else"})
  []   OTHER -> ast

SIAssumption(P(_)) == 
  LET RecAST == Conds(ASTs) \cup FunCalls(ASTs) \cup BuiltIns(ASTs) \cup ListCtors(ASTs)
  IN /\ \A ast \in BaseAST : P(ast)
     /\ \A ast \in RecAST : (\A sub \in Range(OrderedSubASTs(ast)) : P(sub)) => P(ast)

THEOREM StructuralInduction == 
  ASSUME NEW P(_), SIAssumption(P) 
  PROVE \A ast \in ASTs : P(ast)
  <1> DEFINE s0         == BaseAST
             f          == RecF(s0, NextAST)
             depth(s)   == RecDefDepth(s0,NextAST,s)
  <1> SUFFICES /\ \A s \in s0 : P(s)
               /\ \A n \in Nat : (\A s \in f[n] : P(s)) => (\A s \in NextAST(f[n],n+1) : P(s))
      BY HierarchicInduction DEF ASTs
  <1> HIDE DEF f
  <1> USE  DEF OrderedSubASTs
  <1>a ASSUME NEW s \in s0 PROVE P(s) BY ListProp DEF SIAssumption, BaseAST, Bools, Naturals, Vars
  <1>b ASSUME NEW n \in Nat, \A s \in f[n] : P(s), NEW s \in NextAST(f[n],n+1) PROVE P(s)
    <2> SUFFICES ASSUME s \in NextAST(f[n],n+1)!2 PROVE P(s) BY <1>b DEF NextAST
    <2>fAST f[n] \subseteq ASTs BY RecDefExists DEF ASTs, f, RecFProperty
    <2>si SIAssumption(P)!1!2!(s) 
      <3> SUFFICES Seq(f[n]) \subseteq Seq(ASTs) BY <2>fAST DEF SIAssumption, Conds, FunCalls, BuiltIns, ListCtors
      <3> QED BY <2>fAST DEF Seq
    <2> SUFFICES \A sub \in Range(OrderedSubASTs(s)) : sub \in f[n] BY <2>si, <1>b
    <2>a CASE s.op \in {"FunCall", "BuiltIn", "ListCtor"} 
      <3> SUFFICES \A seq \in Seq(f[n]) : \A idx \in DOMAIN seq : seq[idx] \in f[n] BY <1>b, <2>a DEF Conds, FunCalls, BuiltIns, ListCtors, Range
      <3> QED OBVIOUS
    <2>b CASE s.op = "Cond" 
      <3> SUFFICES ASSUME s \in Conds(f[n]) PROVE \A seq \in Range([arg \in {"cond", "then", "else"} |-> s[arg]]) : seq \in f[n] BY <2>b, <1>b DEF Conds, FunCalls, BuiltIns, ListCtors
      <3> QED BY <2>b, <1>b DEF Conds, Range
    <2> QED BY <2>a, <2>b DEF Conds, FunCalls, BuiltIns, ListCtors, Range
  <1> QED BY <1>a, <1>b
  
SIAssumptionII(P(_)) == 
  /\ \A ast \in Bools \cup Naturals \cup Lists \cup Vars \cup {Error} : P(ast)
  /\ \A ast \in FunCalls(ASTs) \cup BuiltIns(ASTs) \cup ListCtors(ASTs) : 
        (\A sub \in Range(ast.args) : P(sub)) => P(ast)
  /\ \A ast \in Conds(ASTs) : 
        (\A sub \in {ast.cond, ast.then, ast.else} : P(sub)) => P(ast)

THEOREM StructuralInductionII == 
  ASSUME NEW P(_), SIAssumptionII(P) 
  PROVE \A ast \in ASTs : P(ast)
  <1> DEFINE s0         == BaseAST
             f          == RecF(s0, NextAST)
             depth(s)   == RecDefDepth(s0,NextAST,s)
  <1> SUFFICES /\ \A s \in s0 : P(s)
               /\ \A n \in Nat : (\A s \in f[n] : P(s)) => (\A s \in NextAST(f[n],n+1) : P(s))
      BY HierarchicInduction DEF ASTs
  <1> HIDE DEF f
  <1> USE  DEF OrderedSubASTs
  <1>a ASSUME NEW s \in s0 PROVE P(s) BY ListProp DEF SIAssumptionII, BaseAST, Bools, Naturals, Vars
  <1>b ASSUME NEW n \in Nat, \A s \in f[n] : P(s), NEW s \in NextAST(f[n],n+1) PROVE P(s)
    <2>sn SUFFICES ASSUME s \in NextAST(f[n],n+1)!2 PROVE P(s) BY <1>b, <2>sn DEF NextAST
    <2>fAST f[n] \subseteq ASTs BY RecDefExists DEF ASTs, f, RecFProperty
    <2>sub /\ FunCalls(f[n]) \subseteq FunCalls(ASTs) /\ BuiltIns(f[n]) \subseteq BuiltIns(ASTs)
           /\ ListCtors(f[n]) \subseteq ListCtors(ASTs) /\ Conds(f[n]) \subseteq Conds(ASTs)
           BY <2>fAST, Seq(f[n]) \subseteq Seq(ASTs) DEF FunCalls, BuiltIns, Conds, ListCtors
    <2>a CASE s.op \in {"FunCall", "BuiltIn", "ListCtor"} 
      <3> s \in FunCalls(f[n]) \cup BuiltIns(f[n]) \cup ListCtors(f[n]) BY <2>sn, <2>a DEF Conds, FunCalls, BuiltIns, ListCtors
      <3> (\A sub \in Range(s.args) : P(sub)) => P(s) BY <2>sub DEF SIAssumptionII, FunCalls, BuiltIns, ListCtors, Conds
      <3> s.args \in Seq(f[n]) BY DEF FunCalls, BuiltIns, ListCtors
      <3> QED BY <1>b DEF SIAssumptionII, Range
    <2>b CASE s.op = "Cond" 
      <3> s \in Conds(f[n]) BY <2>sn, <2>b DEF Conds, FunCalls, BuiltIns, ListCtors
      <3> (\A sub \in {s.cond, s.then, s.else} : P(sub)) => P(s) BY <2>sub DEF SIAssumptionII, Conds
      <3> QED BY <1>b DEF Conds
    <2> QED BY <2>a, <2>b, <1>b DEF NextAST, Conds, FunCalls, BuiltIns, ListCtors, Range
  <1> QED BY <1>a, <1>b

DefState(ast)  == [ funEnv : FunctionMaps, varEnv : VariableMaps, ast : {ast} ]
BaseState      == RecWrapN(DefState,BaseAST,NextAST,0)
NextState(p,n) == RecWrapN(DefState,BaseAST,NextAST,n)
    
THEOREM StatesProp == 
  /\ RecCompAssumption(DefState, LAMBDA s : s.ast)
  /\ States = RecDef(BaseState,NextState)
  /\ \A s \in States : RecDefDepth(BaseState,NextState,s) = RecDefDepth(BaseAST,NextAST,s.ast)
  <1> DEFINE f == RecF(BaseAST,NextAST)
             F == RecF(BaseState,NextState)
             inv(s) == s.ast
  <1>0 RecCompAssumption(DefState, inv) BY DEF DefState, RecCompAssumption, State
  <1>a States = RecDef(BaseState,NextState)
    <2> States = Composite(DefState, ASTs) 
        BY SetEq(States, Composite(DefState, ASTs)) DEF States, DefState, Composite, SetEq
    <2> QED BY <1>0, RecursiveComposition DEF BaseState, NextState, States, ASTs, RecursiveWrap
  <1>b \A s \in States : RecDefDepth(BaseState,NextState,s) = RecDefDepth(BaseAST,NextAST,inv(s))
    <2>rcd RecCompDepthProperty(DefState, BaseAST, NextAST, inv) BY <1>0, RecursiveCompositionDepth DEF BaseState, NextState
    <2> QED BY <1>a, <2>rcd DEF BaseState, NextState, RecursiveWrap, RecCompDepthProperty
  <1> QED BY <1>0, <1>a, <1>b
  
THEOREM SOSExists == SOS = [s \in States |->  DefSOS(SOS,s)]
  <1> DEFINE F          == RecF(BaseState, NextState)
             f          == RecF(BaseAST, NextAST)
             depth(s)   == RecDefDepth(BaseState,NextState,s)
  <1> USE  DEF ASTDepth, ASTRec, Tags
  <1> SUFFICES RecFExistsAssumption(BaseState, NextState, DefSOS) BY FunOverRecDefExists, StatesProp DEF SOS
  <1> SUFFICES ASSUME NEW fun, NEW n \in Nat, NEW s \in F[n],
               n = RecDefDepth(BaseState,NextState,s)
               PROVE  DefSOS(fun,s) = DefSOS(Restrict(fun, RecFSmaller(BaseState,NextState,n)),s)
      BY DEF   RecFExistsAssumption
  <1>Ef RecFProperty(F,BaseState,NextState) BY RecDefExists
  <1>sinS s \in States BY <1>Ef, StatesProp DEF RecFProperty
  <1>ainA s.ast \in ASTs BY <1>sinS DEF States
  <1>East ASTProperty(s.ast) BY ASTProp, <1>ainA DEF ASTs 
  <1> DEFINE ast == s.ast
             c1      == DefSOS(0,s)!1!2!1!1
             e1(g)   == DefSOS(g,s)!1!2!1!2
             c2      == DefSOS(0,s)!1!2!2!1
             e2(g)   == DefSOS(g,s)!1!2!2!2
             e3      == DefSOS(0,s)!1!2!3!2
             sdef(g) == CASE c1 -> e1(g) [] c2 -> e2(g) [] OTHER -> e3
             sfun    == Restrict(fun, RecFSmaller(BaseState,NextState,n))
  <1> SUFFICES sdef(fun) = sdef(sfun) BY DEF DefSOS 
  <1> HIDE DEF F, c1, c2, e1, e2, e3
  <1>c1o2 SUFFICES ASSUME c1 \/ c2 PROVE sdef(fun) = sdef(sfun) BY <1>c1o2 DEF e1, e2
  <1>op s.ast.op \in {"BuiltIn", "FunCall", "ListCtor", "Cond"} BY <1>c1o2 DEF c1, c2
  <1> n \in Nat \ {0} BY <1>op, StatesProp, <1>sinS, ASTProp, <1>ainA DEF ASTProperty
  <1>Fe RecFProperty(F, BaseState, NextState) BY RecDefExists DEF F
  <1>F  F = [m \in Nat |-> Composite(DefState,f[m])] BY <1>Fe DEF RecFProperty, NatInductiveDefConclusion, BaseState, NextState, RecWrapN
  <1>a CASE c1
    <2> SUFFICES e1(fun) = e1(sfun) BY <1>a
    <2> DEFINE NeedEval(sub) == DefSOS(SOS,s)!:!NeedEval(sub)
               subAst == (s.ast.args)[LowestIdx(s.ast.args, NeedEval)]
               arg    == [s EXCEPT !.ast = subAst]
    <2> SUFFICES arg \in RecFSmaller(BaseState, NextState, n) BY DEF e1, Restrict
    <2> SUFFICES arg \in F[n-1] BY n-1 \in 0..n-1 DEF RecFSmaller, F
    <2>op s.ast.op \in {"BuiltIn", "FunCall", "ListCtor"} BY <1>a DEF c1
    <2> subAst \in f[n-1]
      <3> s.ast.args \in Seq(f[n-1]) BY <1>East, <1>sinS, StatesProp, <2>op DEF ASTProperty, BuiltIns, ListCtors, FunCalls
      <3> LowestIdx(s.ast.args, NeedEval) \in DOMAIN s.ast.args 
        <4> SUFFICES LowestIdx(s.ast.args, NeedEval) \in DOMAIN s.ast.args OBVIOUS
        <4> \E idx \in DOMAIN s.ast.args : NeedEval(s.ast.args[idx]) BY <1>a DEF c1
        <4> HIDE DEF NeedEval
        <4> DOMAIN s.ast.args \in SUBSET Nat BY DEF Seq
        <4> \E idx \in DOMAIN s.ast.args : 
              /\ NeedEval(s.ast.args[idx])  
              /\ \A idx2 \in DOMAIN s.ast.args : NeedEval(s.ast.args[idx2]) => ~idx2 < idx 
            BY IfExistsLowestIdxExists DEF IfLowestExistsConclusion
        <4> QED BY DEF LowestIdx, Lowest
      <3> QED OBVIOUS
    <2> QED BY <1>F, n-1 \in Nat DEF DefState, Composite
  <1>b CASE c2
    <2> SUFFICES e2(fun) = e2(sfun) BY <1>b
    <2> DEFINE arg == [s EXCEPT !.ast = s.ast.cond]
    <2> SUFFICES arg \in RecFSmaller(BaseState, NextState, n) BY DEF e2, Restrict    
    <2> SUFFICES arg \in F[n-1] BY n-1 \in 0..n-1 DEF RecFSmaller, F
    <2> SUFFICES s.ast.cond \in f[n-1] BY <1>F, n-1 \in Nat DEF DefState, F, Composite
    <2> QED BY <1>East, <1>sinS, StatesProp, <1>b DEF ASTProperty, Conds, c2
  <1> QED BY <1>a, <1>b DEF e1, e2 

THEOREM WExists == 
  ASSUME NEW funEnv, NEW IDSet PROVE W_ast(funEnv, IDSet) = [ast \in ASTs |-> DefW(funEnv, IDSet, ast, W_ast(funEnv, IDSet))]
  <1> DEFINE Def(f, x)  == DefW(funEnv, IDSet, x, f)
             s0         == BaseAST 
             f          == RecF(s0, NextAST)
  <1>w1 SUFFICES ASSUME NEW w, w = W_ast(funEnv, IDSet) PROVE w = [ast \in RecDef(s0,NextAST) |-> Def(w,ast)] BY DEF ASTs
  <1>w w = CHOOSE fun : fun = [s \in RecDef(s0,NextAST) |-> Def(fun,s)] BY <1>w1 DEF W_ast, ASTs
  <1> HIDE DEF Def
  <1> USE DEF ASTDepth, ASTRec
  <1> SUFFICES ASSUME NEW g, NEW h, NEW n \in Nat, NEW s \in f[n], 
                      n = ASTDepth(s), \A y \in UNION {f[m] : m \in 0..n-1} : g[y] = h[y]
               PROVE  Def(g,s) = Def(h,s) BY <1>w
  <1> SUFFICES Wsub(g,s) = Wsub(h,s) BY DEF Def, DefW
  <1>Ef RecFProperty(f,s0,NextAST) BY RecDefExists
  <1>Efn f[n] = IF n = 0 THEN s0 ELSE NextAST(f[n-1],n) BY <1>Ef DEF RecFProperty
  <1>sinS s \in RecDef(s0,NextAST) BY DEF RecDef 
  <1>Ed RecDefDepthProperty(s0,NextAST,s) BY RecDefDepthExists, <1>sinS
  <1>East ASTProperty(s) BY ASTProp, <1>sinS DEF ASTs 
  <1> HIDE DEF f
  <1>op SUFFICES ASSUME s.op \in {"FunCall","BuiltIn","ListCtor","Cond"} PROVE Wsub(g,s) = Wsub(h,s) BY DEF Wsub
  <1> n # 0 BY <1>East, <1>op, IsaM("best") DEF ASTDepth, ASTProperty, Tags
  <1>fun CASE s.op \in {"FunCall","BuiltIn","ListCtor"}
    <2> SUFFICES Wsub(g,s)!1!2 = Wsub(h,s)!1!2 BY <1>fun DEF Wsub
    <2> SUFFICES \A arg \in Range(s.args) : arg \in f[n-1] BY DEF Range
\*    <2> s \in FunCalls(f[n-1]) \cup BuiltIns(f[n-1]) \cup ListCtors(f[n-1]) BY <1>East, <1>fun DEF f, ASTProperty, ASTRec
\*    <2> s.args \in Seq(f[n-1]) BY DEF FunCalls, BuiltIns, ListCtors
    <2> s.args \in Seq(f[n-1]) BY <1>East, <1>fun DEF f, ASTProperty, FunCalls, BuiltIns, ListCtors
    <2> QED BY DEF Range
  <1>cond CASE s.op = "Cond"
    <2> SUFFICES \A sub \in {s.cond, s.then, s.else} : sub \in f[n-1] BY <1>cond DEF Wsub, Tags
    <2> s \in Conds(f[n-1]) BY <1>East, <1>cond DEF f, ASTProperty, Conds
    <2> QED BY DEF Conds
  <1> QED BY <1>cond, <1>fun, <1>op

THEOREM IExists == 
  I_internal = [ n \in Nat |-> [state \in States |-> IF n = 0 THEN Error ELSE DefI(I_internal[n-1], state)]] 
  <1> DEFINE fBody(f,n) == [state \in States |-> IF n = 0 THEN Error ELSE DefI(f[n-1], state)]
             f0 == [state \in States |-> Error]
             Def(p,n) == [state \in States |-> DefI(p,state)]
             fBody2(p,n) == IF n = 0 THEN f0 ELSE Def(p,n)
  <1> SUFFICES ASSUME I_internal = CHOOSE f : f = [n \in Nat |-> fBody2(f[n-1],n)]
               PROVE  I_internal = [n \in Nat |-> fBody2(I_internal[n-1],n)]
    <2> I_internal = CHOOSE f : f = [n \in Nat |-> fBody(f,n)] BY DEF I_internal
    <2> QED BY \A f,n : fBody(f,n) = fBody2(f[n-1],n)
  <1> HIDE DEF Def
  <1> QED BY NatInductiveDef DEF NatInductiveDefHypothesis, NatInductiveDefConclusion

THEOREM ASTsConverge == ASTs = BaseAST \cup NextAST(ASTs,0)!2
  <1> DEFINE cs(ps) == IF Len(ps) = 3 THEN {[ op |-> "Cond", cond |-> ps[1], then |-> ps[2], else |-> ps[3] ]} ELSE {}
             fcs(ps) == [ op : {"FunCall"}, name : IDs, args : {ps} ]
             bis(ps) == [ op : {"BuiltIn"}, name : BuiltInNames, args : {ps} ]
             lcs(ps) == [ op : {"ListCtor"}, args : {ps} ]
             union(p, op(_)) == UNION {op(ps) : ps \in Seq(p)}
             next_int(ps) == cs(ps) \cup fcs(ps) \cup bis(ps) \cup lcs(ps)
             next(p) == p \cup union(p, next_int)
             InnerNextAST(p) == NextAST(p,0)!2
  <1> USE DEF SetEq
  <1> HIDE DEF cs, fcs, bis, lcs
  <1> \A p,n : NextAST(p,n) = p \cup InnerNextAST(p) BY DEF NextAST, InnerNextAST
  <1> \A p : InnerNextAST(p) = union(p,next_int) 
    <2> TAKE p
    <2> Conds(p)     = union(p, cs)  
      <3> SUFFICES ASSUME NEW s \in Conds(p) 
                   PROVE  s \in union(p, cs) 
          BY union(p, cs) \subseteq Conds(p) DEF Conds, cs
      <3> SUFFICES \A x,y,z \in p : Cond(x,y,z) \in union(p,cs) BY \E x,y,z \in p : s = Cond(x,y,z) DEF Cond, cs, Conds
      <3> TAKE x,y,z \in p
      <3> Cond(x,y,z) \in cs(<<x,y,z>>) BY DEF Cond, cs
      <3> QED BY <<x,y,z>> \in Seq(p)
    <2> FunCalls(p)  = union(p, fcs) BY SetEq(FunCalls(p), union(p,fcs)) DEF FunCalls, fcs
    <2> BuiltIns(p)  = union(p, bis) BY SetEq(BuiltIns(p), union(p,bis)) DEF BuiltIns, bis
    <2> ListCtors(p) = union(p, lcs) BY SetEq(ListCtors(p), union(p,lcs)) DEF ListCtors, lcs
    <2> QED BY DEF InnerNextAST
  <1> HIDE DEF next_int, next
  <1> ASTs = RecDef(BaseAST, LAMBDA p,n : NextAST(p,n)) BY DEF ASTs, RecDef, RecF
  <1> RecDefApproximationAssumption(ASTs, BaseAST, next_int) 
      BY DEF RecDefApproximationAssumption, next
  <1> QED BY RecDefApproximation
  
USE DEF ContinuityPrerequisite, ContinuityResult
  
THEOREM ListsConverge == Lists = {List(seq) : seq \in Seq(Values)}
  <1> DEFINE next(p) == {List(seq) : seq \in Seq(p \cup Naturals \cup Bools)}
  <1>a Lists = RecDef(BaseList, LAMBDA p,n: p \cup next(p)) BY DEF RecDef, Lists, RecF, NextList
  <1>b IsContinuous(next)
    <2> SUFFICES ASSUME NEW f, ContinuityPrerequisite(f) PROVE ContinuityResult(f, next) BY DEF IsContinuous
    <2> ContinuityResult(f, Seq) BY SeqIsContinuous DEF IsContinuous
    <2> QED BY SeqIsContinuous DEF IsContinuous
  <1> HIDE DEF next
  <1> Lists = BaseList \cup next(Lists) BY <1>a, <1>b, IsFixedPoint4 DEF IFP4A
  <1> QED BY \A x : <<>> \in Seq(x) DEF Values, next, BaseList
  
THEOREM InductionOverLists == 
  ASSUME NEW P(_), P(List(<<>>)),
         ASSUME NEW x \in Values, NEW xs \in Seq(Values), P(List(xs))
         PROVE  P(List(<<x>> \o xs))
  PROVE  \A l \in Lists : P(l)
  <1> SUFFICES \A seq \in Seq(Values) : P(List(seq)) BY ListsConverge
  <1> QED BY SeqInduction

ValueProperty(val) == 
  /\ val \in ASTs
  /\ val.op \in Types
  /\ val.op = "Nat"  <=> (val \in Naturals /\ val.val \in Nat)
  /\ val.op = "Bool" <=> (val \in Bools /\ val.val \in BOOLEAN)
  /\ val.op = "List" <=> (val \in Lists /\ val.val \in Seq(Values))
  
THEOREM ValueProp == \A val \in Values : ValueProperty(val)
  BY ListsConverge, ASTsConverge DEF BaseAST, Values, Naturals, Natural, Value, Values, Bool, Bools, List, ValueProperty

THEOREM ICodomain == \A state \in States : I(state) \in Values \cup {Error}
  <1> DEFINE IsValidResult(result) == result \in Values \cup {Error}
             Pn(n) == \A state \in States : IsValidResult(I_internal[n][state])
  <1> SUFFICES \A n \in Nat : Pn(n)
      BY DEF I, ChooseIfExists
  <1>n SUFFICES ASSUME NEW n \in Nat, Pn(n) PROVE Pn(n+1) BY NatInduction, IExists, Pn(0)
  <1> SUFFICES ASSUME NEW funEnv \in FunctionMaps, NEW varEnv \in VariableMaps
               PROVE  \A ast \in ASTs : IsValidResult(I_internal[n+1][State(funEnv, varEnv, ast)])
      BY DEF States, State
  <1> DEFINE state(ast) == State(funEnv, varEnv, ast)
             II == I_internal[n]
             IIast(ast) == II[state(ast)]
             nAST(ast) == ISub(II,state(ast))
             NoDynErr(ast) == ~DynamicError(nAST(ast))
             Case(ast) == 
               CASE ast.op = "FunCall"  -> II[State(funEnv, MapMapF(funEnv[ast.name].args, nAST(ast).args), funEnv[ast.name].ast)]
               []   ast.op = "BuiltIn"  -> BuiltInStep(nAST(ast))
               []   ast.op = "ListCtor" -> List(nAST(ast).args)
               []   ast.op = "Cond"     -> IF nAST(ast).cond.val THEN IIast(ast.then) ELSE IIast(ast.else)
               []   ast.op = "Var"      -> varEnv[ast.id]
               []   ast.op \in Types \cup {"Error"} -> ast
             StateProp(ast) == 
               /\ state(ast).ast = ast
               /\ state(ast).varEnv = varEnv
               /\ state(ast).funEnv = funEnv
             w == W_ast(funEnv,DOMAIN varEnv)
             dw(ast) == DefW(funEnv, DOMAIN varEnv, ast, w)
  <1>asts \A ast \in ASTs : State(funEnv, varEnv, ast) \in States BY DEF State, States
  <1>state \A ast \in ASTs : StateProp(ast) BY DEF State
  <1> SUFFICES ASSUME NEW ast \in ASTs, W(state(ast)), NoDynErr(ast) PROVE IsValidResult(Case(ast))
   <2> SUFFICES ASSUME NEW ast \in ASTs
                PROVE  IsValidResult(DefI(II,state(ast)))
        BY IExists, <1>asts
    <2> DefI(II, state(ast))!1!3 = Case(ast) BY <1>state, StateProp(ast)
    <2> QED BY DEF DefI
  <1> HIDE DEF Case
  <1>w dw(ast) BY <1>state, StateProp(ast), WExists DEF W
  <1>0 CASE ast \in BaseAST
    <2>a CASE ast \in Values BY <2>a, ListProp DEF Case, Values, Naturals, Bools, Natural, Bool, Value
    <2>b CASE ast \in Vars BY <2>b, <1>w DEF Vars, VariableMaps, Case, DefW
    <2>c CASE ast = Error BY <2>c DEF Case, Error
    <2> QED BY <1>0, <2>a, <2>b, <2>c DEF BaseAST, Values
  <1>cond CASE ast \in Conds(ASTs)
    <2> ast.op = "Cond" /\ ast.then \in ASTs /\ ast.else \in ASTs BY <1>cond DEF Conds
    <2> QED BY <1>n, <1>asts DEF Case
  <1> SUFFICES ASSUME ast \in FunCalls(ASTs) \cup BuiltIns(ASTs) \cup ListCtors(ASTs)
              PROVE  IsValidResult(Case(ast))
      BY ASTsConverge, <1>0, <1>cond
  <1> DEFINE AST == nAST(ast)
  <1>nast AST = [ast EXCEPT !.args = Map(ast.args, IIast)] 
    <2> ast.op \in {"BuiltIn", "ListCtor", "FunCall"} BY DEF FunCalls, BuiltIns, ListCtors
    <2> SUFFICES Map(ast.args, IIast) = 
                 Map(ast.args, LAMBDA sub : II[[state(ast) EXCEPT !.ast = sub]])
        BY <1>state DEF ISub
    <2> SUFFICES \A sub : IIast(sub) = II[[state(ast) EXCEPT !.ast = sub]] BY <1>state
    <2> QED BY DEF State
  <1> HIDE DEF nAST
  <1>args AST.args \in Seq(Values)
    <2> Error \notin Range(AST.args) BY <1>nast
        DEF FunCalls, BuiltIns, ListCtors, DynamicError
    <2> ast.args \in Seq(ASTs) BY DEF FunCalls, BuiltIns, ListCtors
    <2> \A idx \in DOMAIN ast.args : IsValidResult(IIast(ast.args[idx])) 
        BY <1>n, <1>asts
    <2> AST.args \in Seq(Values \cup {Error}) BY <1>nast DEF Map
    <2> QED BY DEF Range
  <1>call CASE ast \in FunCalls(ASTs)
    <2> DEFINE fun == funEnv[ast.name]
               newEnv == MapMapF(fun.args, AST.args)
    <2> /\ ast.name \in DOMAIN funEnv 
        /\ Len(fun.args) = Len(ast.args)
        BY <1>w, <1>call DEF DefW, FunCalls
    <2>a newEnv \in VariableMaps 
      <3> fun.args \in Seq(IDs) BY DEF FunctionMaps, Functions
      <3> SUFFICES newEnv \in [Range(fun.args) -> Range(AST.args)]
          BY <1>args DEF Range, VariableMaps
      <3> IsBijective(fun.args) BY <1>state, fun \in Range(state(ast).funEnv) DEF W, Range
      <3> DOMAIN fun.args = DOMAIN AST.args 
        <4> DOMAIN ast.args = 1..Len(ast.args) /\ DOMAIN fun.args = 1..Len(fun.args)
            BY <1>args, LenProperties
        <4> QED BY <1>nast DEF Map
      <3> QED BY MapMapFRange
    <2>b funEnv[ast.name].ast \in ASTs BY DEF FunctionMaps, Functions
    <2> \A v \in VariableMaps, a \in ASTs : State(funEnv, v, a) \in States BY DEF State, States
    <2> QED BY <2>a, <2>b, <1>n, <1>asts, <1>call DEF FunCalls, Case
  <1>builtin CASE ast \in BuiltIns(ASTs)
    <2> ast.op = "BuiltIn" BY <1>builtin DEF BuiltIns
    <2> SUFFICES IsValidResult(BuiltInStep(AST)) BY DEF Case
    <2> ~BuiltInError(AST) BY <1>nast, AST.op = "BuiltIn" DEF DynamicError
    <2> DEFINE arg1 == AST.args[1]
               arg2 == AST.args[2]
    <2> HIDE DEF AST
    <2> Len(AST.args) = Len(BuiltInSig(AST.name))
      <3> Len(ast.args) = Len(BuiltInSig(ast.name)) BY <1>w DEF DefW 
      <3> QED BY <1>nast DEF Map
    <2> \A idx \in DOMAIN AST.args : ValueProperty(AST.args[idx]) BY ValueProp, <1>args
    <2> \A idx \in DOMAIN AST.args : AST.args[idx].op \in BuiltInSig(AST.name)[idx] BY DEF BuiltInError
    <2>add CASE AST.name = "+" 
      <3> arg1 \in Naturals /\ arg2 \in Naturals BY <2>add DEF ValueProperty, BuiltInSig
      <3> QED BY <2>add DEF BuiltInStep, Values, Natural, Naturals, Value    
    <2>mult CASE AST.name = "*" 
      <3> arg1 \in Naturals /\ arg2 \in Naturals BY <2>mult DEF ValueProperty, BuiltInSig
      <3> arg1.val \in Nat /\ arg2.val \in Nat BY DEF Value, Natural, Naturals
      <3> arg1.val * arg2.val \in Nat OBVIOUS
      <3> QED BY <2>mult DEF BuiltInStep, Values, Natural, Naturals, Value
    <2>sub CASE AST.name = "-" 
      <3> arg1 \in Naturals /\ arg2 \in Naturals BY <2>sub DEF ValueProperty, BuiltInSig
      <3> arg1.val - arg2.val \in Nat BY <2>sub DEF Value, Natural, Naturals, BuiltInError
      <3> QED BY <2>sub DEF BuiltInStep, Values, Natural, Naturals, Value
    <2>bool CASE AST.name \in {">","=","~"} 
       BY <2>bool, (arg1.val > arg2.val) \in BOOLEAN, (arg1.op = arg2.op /\ arg1.val = arg2.val) \in BOOLEAN, (~arg1.val) \in BOOLEAN 
       DEF BuiltInStep, Values, Value, Bool, Bools
    <2>build CASE AST.name = "build"
      <3> arg1 \in Values /\ arg2 \in Lists BY <2>build, <1>args DEF ValueProperty, BuiltInSig
      <3> (<<arg1>> \o arg2.val) \in Seq(Values) BY ListsConverge DEF List, Value, Values
      <3> QED BY <2>build, ListsConverge DEF BuiltInStep, Values
    <2>list CASE AST.name \in {"head","tail"}
      <3> arg1 \in Lists BY <2>list DEF ValueProperty, BuiltInSig
      <3> CASE arg1.val # <<>>
        <4> List(Tail(arg1.val)) \in Values
          BY ListsConverge, HeadTailProperties, Tail(arg1.val) \in Seq(Values), ListsConverge DEF List, Value, Values
        <4> Head(arg1.val) \in Values BY ListsConverge, HeadTailProperties DEF List, Value
        <4> QED BY <2>list DEF BuiltInStep, Values
      <3> CASE arg1.val = <<>> BY <2>list DEF BuiltInStep, Values
      <3> QED OBVIOUS
    <2> AST.name \in {"+","-","*",">","=","~","build","head","tail"} 
        BY <1>nast, <1>builtin DEF BuiltIns, BuiltInNames
    <2> QED BY <2>add, <2>mult, <2>sub, <2>bool, <2>build, <2>list
  <1>lcs CASE ast \in ListCtors(ASTs) 
    <2> SUFFICES List(AST.args) \in Lists BY <1>lcs DEF ListCtors, Case, Values
    <2> QED BY ListsConverge, <1>args
  <1> QED BY <1>call, <1>builtin, <1>lcs

THEOREM HasResultIsWellformed ==
  ASSUME NEW state \in States, I(state) # Error
  PROVE  W(state)
  <1> DEFINE n == CHOOSE n \in Nat : I_internal[n][state] # Error
  <1> n \in Nat /\ I_internal[n][state] # Error 
      BY \E m \in Nat : I_internal[m][state] # Error DEF I, ChooseIfExists
  <1> HIDE DEF n
  <1> DefI(I_internal[n-1],state) # Error BY IExists
  <1> QED BY DEF DefI

THEOREM UniqueI == 
  \A state \in States, n \in Nat : 
     /\ I_internal[n][state] \in {I(state), Error}  
     /\ I_internal[n][state] = I(state) => \A m \in Nat : n<m => I_internal[m][state] = I(state)
  <1> DEFINE Iint(state,n) == I_internal[n][state]
             II == [state \in States |-> I(state)]
  <1> SUFFICES \A n \in Nat, state \in States : Iint(state,n) # Error => Iint(state,n) = Iint(state,n+1)
    <2> UniqueChooseIfExistsAssumption(States, II, Iint, Error) BY DEF UniqueChooseIfExistsAssumption, I
    <2> UniqueChooseIfExistsConclusion(States, II, Iint, Error) BY UniqueChooseIfExists
    <2> QED BY DEF UniqueChooseIfExistsConclusion
  <1> DEFINE P(n) == \A state \in States : Iint(state,n) # Error => Iint(state,n) = Iint(state,n+1)
  <1>0 P(0) BY IExists
  <1> SUFFICES ASSUME NEW n \in Nat PROVE P(n) => P(n+1) BY <1>0, NatInduction
  <1> SUFFICES ASSUME P(n), NEW state \in States, Iint(state,n+1) # Error
               PROVE  Iint(state,n+1) = Iint(state,n+2) OBVIOUS
  <1> SUFFICES DefI(I_internal[n],state) = DefI(I_internal[n+1],state) BY IExists
  <1> ASTProperty(state.ast) BY ASTProp DEF States
  <1>opSub \A f : \A s \in States : ISub(f,s).op = s.ast.op
    <2> TAKE f
    <2> TAKE s \in States
    <2> ASTProperty(s.ast) BY ASTProp DEF States
    <2> "op" \in DOMAIN s.ast BY DEF ASTProperty
    <2> QED BY DEF ISub
  <1> DEFINE funEnv == state.funEnv
             ast == state.ast
             isub(m) == ISub(I_internal[m],state)
             IISub(m,sub) == I_internal[m][[state EXCEPT !.ast = sub]]
             isubArgs(m) == Map(ast.args, LAMBDA sub : IISub(m,sub))
             isubCond(m) == IISub(m,ast.cond)
             FunExp(m)  == I_internal[m][State(funEnv, MapMapF(funEnv[ast.name].args, isub(m).args), funEnv[ast.name].ast)]
             CondExp(m) == IF isub(m).cond.val THEN IISub(m,ast.then) ELSE IISub(m,ast.else)
             CaseExp(m) == DefI(I_internal[m],state)!1!3
  <1>isub isub(n) = isub(n+1)
    <2>dyn ~DynamicError(isub(n)) 
      <3> DefI(I_internal[n],state) # Error BY IExists
      <3> QED BY DEF DefI
    <2>dynResult 
        /\ isub(n).op \in {"BuiltIn", "ListCtor", "FunCall"} => Error \notin Range(isub(n).args) 
        /\ isub(n).op = "Cond" => isub(n).cond # Error
        BY <2>dyn DEF DynamicError
    <2>a CASE state.ast.op \in {"FunCall", "BuiltIn", "ListCtor"}
      <3> isub(n).args = isubArgs(n) 
        <4> isub(n) = [state.ast EXCEPT !.args = isubArgs(n)] BY <2>a DEF ISub
        <4> QED OBVIOUS
      <3> Error \notin Range(isubArgs(n)) BY <2>dynResult, <1>opSub, <2>a
      <3> SUFFICES isubArgs(n) = isubArgs(n+1) BY <2>a DEF ISub
      <3> SUFFICES \A idx \in DOMAIN state.ast.args : 
                     [state EXCEPT !.ast = state.ast.args[idx]] \in States BY DEF Map, Range
      <3> TAKE idx \in DOMAIN state.ast.args
      <3> SUFFICES state.ast.args[idx] \in ASTs BY DEF States
      <3> /\ state.ast.args \in Seq(ASTRec[ASTDepth(state.ast) - 1]) 
          /\ ASTRec[ASTDepth(state.ast) - 1] \subseteq ASTs
          BY <2>a DEF ASTProperty, BuiltIns, FunCalls, ListCtors
      <3> QED OBVIOUS
    <2>b CASE state.ast.op = "Cond"
      <3> isub(n).cond = isubCond(n) 
        <4> isub(n) = [state.ast EXCEPT !.cond = isubCond(n)] BY <2>b DEF ISub
        <4> QED OBVIOUS
      <3> isubCond(n) # Error BY <2>b, <1>opSub, <2>dynResult
      <3> SUFFICES isubCond(n) = isubCond(n+1) BY <2>b DEF ISub
      <3> SUFFICES state.ast.cond \in ASTs BY DEF Map, Range, States
      <3> QED BY <2>b DEF ASTProperty, Conds
    <2> QED BY <2>a, <2>b DEF ISub
  <1> HIDE DEF CaseExp
  <1>noErr SUFFICES ASSUME W(state), ~DynamicError(isub(n)), CaseExp(n) # Error
               PROVE CaseExp(n) = CaseExp(n+1)\*DefI(I_internal[n],state) = DefI(I_internal[n+1],state)
    <2> \A m : DefI(I_internal[m],state) = 
      IF ~W(state) \/ DynamicError(isub(m)) THEN Error ELSE CaseExp(m)
      BY <1>noErr, IsaM("best") DEF DefI, CaseExp
    <2> I_internal[n + 1][state] = DefI(I_internal[n],state) BY ONLY IExists
    <2> QED BY <1>isub
  <1>a CASE state.ast.op = "FunCall" 
    <2>noErr SUFFICES ASSUME FunExp(n) # Error PROVE FunExp(n) = FunExp(n+1) 
             BY <1>isub, <1>a, <2>noErr, <1>noErr DEF CaseExp
    <2> ast \in ASTs /\ funEnv \in FunctionMaps BY DEF States
    <2>w /\ ast.name \in DOMAIN funEnv                
         /\ Len(funEnv[ast.name].args) = Len(ast.args)
      <3> DEFINE w == W_ast(state.funEnv, DOMAIN state.varEnv)
      <3>w DefW(state.funEnv, DOMAIN state.varEnv, ast, w) BY <1>noErr, WExists DEF W
      <3> QED BY <1>a, <3>w DEF DefW
    <2>dyn ~\E arg \in Range(isub(n).args) : arg \notin ASTs \/ arg.op \notin Types
           BY <1>a, <1>opSub, <1>noErr DEF DynamicError
    <2>a MapMapF(funEnv[ast.name].args, isub(n).args) \in VariableMaps
      <3> DEFINE fun == funEnv[ast.name]
                 fargs == fun.args
                 aargs == isub(n).args
                 newVarEnv == MapMapF(fargs,aargs)
      <3> aargs = isubArgs(n)
        <4> isub(n) = [ast EXCEPT !.args = isubArgs(n)] BY <1>a DEF ISub
        <4> QED OBVIOUS
      <3> SUFFICES newVarEnv \in VariableMaps OBVIOUS
      <3> fun \in Functions BY <2>w DEF FunctionMaps
      <3> fargs \in Seq(IDs) BY DEF Functions
      <3> Range(fargs) \in SUBSET IDs BY ONLY fun \in Functions DEF Range, Functions
      <3> DOMAIN newVarEnv \in SUBSET IDs BY DEF MapMapF
      <3> Len(fargs) = Len(aargs) BY <2>w DEF Map
      <3> aargs \in Seq(Values)
        <4>a ASSUME NEW val \in Range(aargs) PROVE val \in Values 
             BY <2>dyn, ASTProp, val \in ASTs \/ val.op \in Types, ASTProperty(val) DEF ASTProperty, Values
        <4>b \A idx \in DOMAIN aargs : aargs[idx] \in Values BY <4>a DEF Range
        <4>c aargs = [idx \in DOMAIN aargs |-> aargs[idx]] BY DEF Map
        <4> QED BY ONLY <4>b, <4>c, fargs \in Seq(IDs), Len(fargs) = Len(aargs)        
      <3> HIDE DEF fargs, aargs
      <3> \A idx \in DOMAIN newVarEnv : newVarEnv[idx] \in Values 
          BY ONLY fargs \in Seq(IDs), Len(fargs) = Len(aargs), aargs \in Seq(Values) DEF MapMapF, Range
      <3> newVarEnv \in [DOMAIN newVarEnv -> Values] BY DEF Range, MapMapF
      <3> QED BY DEF VariableMaps, Range
    <2>b funEnv[ast.name].ast \in ASTs BY <2>w DEF FunctionMaps, Functions
    <2> QED BY <1>isub, <2>a, <2>b, <2>noErr DEF States, State
  <1>b CASE state.ast.op = "Cond" 
    <2> USE <1>isub
    <2> SUFFICES ASSUME CondExp(n) # Error PROVE CondExp(n) = CondExp(n+1) BY <1>b, <1>noErr DEF CaseExp
    <2> SUFFICES ast.then \in ASTs /\ ast.else \in ASTs BY DEF States
    <2> QED BY <1>b DEF ASTProperty, Conds
  <1>c CASE state.ast.op \notin {"FunCall", "Cond"} BY <1>isub, <1>c DEF CaseExp
  <1> QED BY <1>a, <1>b, <1>c

ISubSplit(fEnv, vEnv, ast) ==
  LET II(sub) == I(State(fEnv, vEnv, sub))
  IN  CASE ast.op \in {"FunCall", "BuiltIn", "ListCtor"} -> [ast EXCEPT !.args = Map(ast.args, II)]
      []   ast.op = "Cond"                               -> Cond(II(ast.cond), II(ast.then), II(ast.else))
      []   OTHER -> ast

CongruentASTsAssumption(funEnv, varEnv, a, b) == 
  LET trans(x) == ISubSplit(funEnv, varEnv, x)
      w(x) == W(State(funEnv,varEnv,x))
  IN  trans(a) = trans(b) /\ w(a) /\ w(b)

CongruentASTsConclusion(funEnv, varEnv, a, b) == 
  LET trans(x) == I(State(funEnv, varEnv, x))
  IN  trans(a) = trans(b)

THEOREM Congruence == 
  \A funEnv \in FunctionMaps, varEnv \in VariableMaps, a \in ASTs, b \in ASTs : 
    CongruentASTsAssumption(funEnv, varEnv, a, b) =>
    CongruentASTsConclusion(funEnv, varEnv, a, b)
  OMITTED

\* example for conditionals
THEOREM \A funEnv \in FunctionMaps, varEnv \in VariableMaps, a,b \in Conds(ASTs) :
          CongruentASTsAssumption(funEnv,varEnv,a,b)
          =>  CongruentASTsConclusion(funEnv,varEnv,a,b)
  <1> USE DEF CongruentASTsConclusion, PrintTAST, ChooseIfExists
  <1> TAKE funEnv \in FunctionMaps, varEnv \in VariableMaps, a,b \in Conds(ASTs)
  <1> HAVE CongruentASTsAssumption(funEnv,varEnv,a,b)
  <1> DEFINE s(c) == State(funEnv,varEnv,c)
  <1> \A arg \in {"cond","then","else"} : CongruentASTsConclusion(funEnv,varEnv,a[arg],b[arg])
      BY DEF CongruentASTsAssumption, ISubSplit, Cond, Conds
  <1>w W(s(a)) /\ W(s(b)) BY DEF CongruentASTsAssumption
  <1> HIDE DEF CongruentASTsConclusion
  <1> \A x : /\ \A y : s(x) = [s(y) EXCEPT !.ast = x]
             /\ s(x).funEnv = funEnv /\ s(x).varEnv = varEnv /\ s(x).ast = x
             /\ x \in ASTs => s(x) \in States 
             /\ x \in Conds(ASTs) =>
                /\ x \in ASTs
                /\ x.cond \in ASTs /\ x.then \in ASTs /\ x.else \in ASTs 
            BY ASTsConverge DEF State, States, Conds
  <1> SUFFICES I(s(a)) = I(s(b)) BY DEF CongruentASTsConclusion
  <1> DEFINE nAST(c,n) == ISub(I_internal[n],s(c))
             Iint(x,m) == I_internal[m][s(x)]
             nASTEq(c,n) == Cond(Iint(c.cond, n),c.then,c.else)
  <1>nAST \A c \in Conds(ASTs), n \in Nat : nAST(c,n) = nASTEq(c,n)
      <2> TAKE c \in Conds(ASTs), n \in Nat
      <2> nAST(c,n) = ISub(I_internal[n],s(c))!1!2!2
          BY DEF ISub, Conds
      <2> QED BY DEF Cond, Conds, State
  <1>DynErr \A c \in Conds(ASTs), n \in Nat : 
            DynamicError(nAST(c,n)) <=> Iint(c.cond, n) = Error \/ Iint(c.cond, n).op # "Bool"
    <2> TAKE c \in Conds(ASTs), n \in Nat
    <2> nAST(c,n) = nASTEq(c,n) BY <1>nAST
    <2> SUFFICES DynamicError(nAST(c,n)) <=> nAST(c, n).cond = Error \/ nAST(c, n).cond.op # "Bool"
        BY DEF Cond
    <2> QED BY DEF DynamicError, Conds, Cond
  <1>a CASE I(s(a.cond)) = Error 
    <2> SUFFICES ASSUME NEW c \in Conds(ASTs), I(s(c.cond)) = Error PROVE I(s(c)) = Error BY <1>a, <1>w DEF CongruentASTsConclusion
    <2> SUFFICES \A n \in Nat : Iint(c,n) = Error BY DEF I, Range 
    <2> TAKE n \in Nat
    <2> SUFFICES ASSUME n # 0 PROVE DefI(I_internal[n-1], s(c)) = Error BY IExists
    <2> SUFFICES DynamicError(nAST(c,n-1)) BY DEF DefI
    <2> HIDE DEF nAST
    <2> SUFFICES nAST(c,n-1) = Cond(Error,c.then,c.else)
        BY nAST(c,n-1).op = "Cond" /\ nAST(c,n-1).cond = Error 
        DEF DynamicError, Cond, PrintTAST
    <2> Iint(c.cond,n-1) = Error BY n-1 \in Nat DEF I, Range
    <2> QED BY <1>nAST DEF Conds, Cond
  <1>b CASE I(s(a.cond)) # Error
    <2> DEFINE t1(c) == IF I(s(c.cond)).val THEN I(s(c.then)) ELSE I(s(c.else))
               t2(c) == \/ I(s(c.cond)).op # "Bool" /\ I(s(c)) = Error 
                        \/ I(s(c.cond)).op = "Bool" /\ I(s(c)) = t1(c)
               iiint(c,n) == IF Iint(c.cond,n-1).val THEN Iint(c.then,n-1) ELSE Iint(c.else,n-1)
               iint(c,n) ==  IF n = 0 \/ Iint(c.cond, n-1) = Error \/ Iint(c.cond,n-1).op # "Bool" THEN Error ELSE iiint(c,n)
    <2> SUFFICES ASSUME NEW c \in Conds(ASTs), I(s(c.cond)) # Error, W(s(c)) PROVE t2(c)
        BY <1>b, <1>w DEF CongruentASTsConclusion
    <2>iint ASSUME NEW n \in Nat
            PROVE Iint(c,n) = iint(c,n)
      <3> SUFFICES ASSUME n # 0 PROVE DefI(I_internal[n-1],s(c)) = iint(c,n) BY IExists
      <3>a Iint(c,n) = DefI(I_internal[n-1],s(c)) BY IExists
      <3>err CASE Iint(c.cond, n-1) = Error \/ Iint(c.cond,n-1).op # "Bool"
        <4> DynamicError(nAST(c,n-1)) BY <3>err, <1>DynErr
        <4> QED BY <3>err, <3>a, <1>DynErr DEF DefI
      <3> HIDE DEF s, Iint
      <3> SUFFICES ASSUME Iint(c.cond, n-1) # Error, Iint(c.cond,n-1).op = "Bool"
                   PROVE  DefI(I_internal[n-1],s(c)) = iiint(c,n)
          BY <3>err
      <3> SUFFICES DefI(I_internal[n-1], s(c))!1!3!4!2 = iiint(c,n)
        <4>DynErr ~DynamicError(nAST(c,n-1)) BY <1>DynErr, <1>b
        <4> W(s(c)) /\ ~DynamicError(nAST(c,n-1)) BY <4>DynErr
        <4> s(c).ast.op = "Cond" BY DEF Conds
        <4> SUFFICES DefI(I_internal[n-1], s(c)) = DefI(I_internal[n-1], s(c))!1!3!4!2 BY <3>a 
        <4> QED BY DEF DefI
      <3> nAST(c,n-1) = Cond(Iint(c.cond,n-1),c.then,c.else) BY ONLY <1>nAST, n-1 \in Nat DEF Cond
      <3> nAST(c,n-1).cond = Iint(c.cond,n-1) BY DEF State, Cond
      <3> QED BY DEF Iint, State, Cond      
    <2>Err CASE \/  I(s(c.cond)).op # "Bool"
                \/  I(s(c.cond)).val /\ I(s(c.then)) = Error
                \/ ~I(s(c.cond)).val /\ I(s(c.else)) = Error
      <3> SUFFICES I(s(c)) = Error BY <2>Err 
      <3> SUFFICES ASSUME NEW n \in Nat PROVE Iint(c,n) = Error BY DEF I, Range
      <3> SUFFICES ASSUME n # 0 PROVE Error = iint(c,n) BY <2>iint
      <3> SUFFICES ASSUME Iint(c.cond,n-1) = I(s(c.cond)), I(s(c.cond)) # Error
                   PROVE  Error = iint(c,n)
          BY UniqueI, n-1 \in Nat DEF State, States
      <3>a CASE I(s(c.cond)).op # "Bool" BY <3>a
      <3> SUFFICES ASSUME 
                \/  I(s(c.cond)).val /\ I(s(c.then)) = Error
                \/ ~I(s(c.cond)).val /\ I(s(c.else)) = Error
                PROVE Error = iiint(c,n) BY <3>a, <2>Err   
      <3> QED BY UniqueI, n-1 \in Nat
    <2> SUFFICES ASSUME  I(s(c.cond)).op = "Bool",
                         I(s(c.cond)).val => I(s(c.then)) # Error,
                        ~I(s(c.cond)).val => I(s(c.else)) # Error 
                 PROVE I(s(c)) = t1(c) BY <2>Err
    <2> SUFFICES ASSUME NEW n \in Nat, \A arg \in {"cond", "then", "else"} : Iint(c[arg],n) = I(s(c[arg]))
                 PROVE I(s(c)) = t1(c)
      <3> \A arg \in {"cond", "then", "else"} : s(c[arg]) \in States BY DEF States, State, Conds
      <3> \A arg \in {"cond", "then", "else"} : \E n \in Nat : Iint(c[arg],n) = I(s(c[arg])) 
          BY UniqueI DEF I, Range
      <3> DEFINE args == {"cond", "then", "else"}
                 argP(m) == \A arg \in args : Iint(c[arg],m) = I(s(c[arg]))
                 m == CHOOSE m \in Nat : argP(m)
      <3> m \in Nat /\ argP(m) BY UniqueI, \E k \in Nat : argP(k)
      <3> HIDE DEF m
      <3> \A arg \in args : Iint(c[arg],m) = I(s(c[arg])) BY UniqueI
      <3> QED OBVIOUS
    <2> Iint(c,n+1) # Error BY <2>iint
    <2> SUFFICES Iint(c,n+1) = I(s(c)) BY <2>iint
    <2> QED BY UniqueI, s(c) \in States
  <1> QED BY <1>a, <1>b
  
THEOREM AdditionResolution ==
  ASSUME NEW funEnv \in FunctionMaps, NEW varEnv \in VariableMaps, NEW a \in ASTs, NEW b \in ASTs
  PROVE  LET II(ast) == I(State(funEnv,varEnv,ast))
             addition == BuiltIn("+",<<a,b>>)
         IN  IF II(a) \in Naturals /\ II(b) \in Naturals
             THEN II(addition) = Natural(II(a).val + II(b).val)
             ELSE II(addition) = Error
  <1> DEFINE addition == BuiltIn("+",<<a,b>>)
             dState(ast) == State(funEnv,varEnv,ast)
             WW(ast) == W(dState(ast))
             WW_AST  == W_ast(funEnv, DOMAIN varEnv)
             II(ast) == I(dState(ast))
             II_internal(ast,n) == I_internal[n][dState(ast)]
             isub(n) == ISub(I_internal[n], dState(addition))
             dynErr(n) == \E arg \in { II_internal(x,n) : x \in {a,b} } : 
               arg = Error \/ arg \notin ASTs \/ arg.op # "Nat"
             P == II(a) \in Naturals /\ II(b) \in Naturals
  <1> \A ast \in ASTs : dState(ast) \in States BY DEF States, State
  <1> /\ addition = BuiltIn("+",<<a,b>>)
      /\ addition.args[1] = a /\ addition.args[2] = b 
      /\ addition.op = "BuiltIn" /\ addition.name = "+" BY DEF BuiltIn
  <1> addition \in ASTs
    <3> SUFFICES addition \in BuiltIns(ASTs) BY ASTsConverge
    <3> QED BY DEF BuiltIns, BuiltIn, BuiltInNames
  <1>w WW_AST = [ast \in ASTs |-> DefW(funEnv, DOMAIN varEnv, ast, WW_AST)] BY ONLY WExists
  <1>ww WW(a) /\ WW(b) <=> WW(addition) 
    <2>w1 WW(a) /\ WW(b) => WW(addition) 
      <3> HAVE WW(a) /\ WW(b)
      <3> WW_AST[a] /\ WW_AST[b] BY DEF W, State
      <3> SUFFICES WW_AST[addition] 
        <4> SUFFICES dState(addition) \in States BY DEF W, State
        <4> SUFFICES addition \in ASTs BY DEF States, State
        <4> QED OBVIOUS
      <3> SUFFICES Wsub(WW_AST, addition) /\ Len(BuiltInSig(addition.name)) = Len(addition.args) 
          BY <1>w DEF BuiltIn, DefW
      <3> Wsub(WW_AST, addition) BY DEF Wsub, BuiltIn, Range
      <3> Len(BuiltInSig(addition.name)) = Len(addition.args) BY DEF BuiltInSig, BuiltIn
      <3> QED OBVIOUS
    <2>w2 WW(addition) => WW(a) /\ WW(b)
      <3> HAVE WW(addition)
      <3> SUFFICES WW_AST[a] /\ WW_AST[b] BY DEF State, W, States
      <3> Wsub(WW_AST, addition) BY <1>w DEF W, State, DefW
      <3> QED BY DEF Wsub, BuiltIn, Range
    <2> QED BY <2>w1, <2>w2
  <1>isub \A n \in Nat : isub(n) = BuiltIn("+",<<II_internal(a,n), II_internal(b,n)>>)
    <2> TAKE n \in Nat
    <2> dState(addition).ast = addition BY DEF State
    <2> isub(n) = ISub(I_internal[n],dState(addition))!1!1!2 BY DEF ISub
    <2> \A s1, s2 : [dState(s1) EXCEPT !.ast = s2] = dState(s2) BY DEF State
    <2> isub(n) = [addition EXCEPT !.args = Map(@, LAMBDA sub : II_internal(sub,n))] OBVIOUS
    <2> QED BY DEF BuiltIn, Map \*BY DEF ISub, Range, Map
  <1>dyn \A n \in Nat : DynamicError(isub(n)) <=> dynErr(n)
    <2> TAKE n \in Nat
    <2> HIDE DEF isub
    <2> isub(n) = BuiltIn("+",<<II_internal(a,n), II_internal(b,n)>>) BY <1>isub
    <2> isub(n).op = "BuiltIn" BY DEF BuiltIn
    <2> SUFFICES dynErr(n) <=> DynamicError(isub(n))!1!1!2 \/ DynamicError(isub(n))!1!2!2
      <3> SUFFICES DynamicError(isub(n)) <=> DynamicError(isub(n))!1!1!2 \/ DynamicError(isub(n))!1!2!2 OBVIOUS
      <3> QED BY ONLY isub(n).op = "BuiltIn" DEF BuiltIn, DynamicError
    <2> Range(isub(n).args) = {II_internal(x,n) : x \in {a,b}} BY DEF Range, BuiltIn
    <2> BuiltInError(isub(n)) <=> \E arg \in Range(isub(n).args) : arg.op # "Nat" 
        BY DEF BuiltIn, Range, BuiltInError, BuiltInSig
    <2> QED OBVIOUS
  <1>iint \A n \in Nat, ast \in ASTs : II_internal(ast,n) = IF n = 0 THEN Error ELSE DefI(I_internal[n-1], dState(ast)) BY IExists
  <1>a ASSUME  P PROVE II(addition) = Natural(II(a).val + II(b).val)
    <2> Error \notin Naturals BY DEF Error, Naturals, Natural, Value
    <2> DEFINE result == Natural(II(a).val + II(b).val)
               n == CHOOSE n \in Nat : \A x \in {a,b} : II(x) = II_internal(x,n)
    <2> SUFFICES II(addition) = result OBVIOUS
    <2>n n \in Nat /\ \A x \in {a,b} : II(x) = II_internal(x,n)
      <3> ASSUME NEW x \in {a,b} PROVE \E m \in Nat : II(x) = II_internal(x,m) 
        <4> II(x) \in Naturals BY <1>a
        <4> QED BY DEF I, ChooseIfExists
      <3> QED BY UniqueI, \E m \in Nat : \A x \in {a,b} : II(x) = II_internal(x,m)
    <2> result \in Naturals BY <1>a DEF Natural, Naturals, Value
    <2> n \in Nat BY <2>n
    <2> HIDE DEF n, result
    <2>h II_internal(addition,n+1) \in {Error, II(addition)} BY UniqueI
    <2> SUFFICES II_internal(addition,n+1) = result 
        BY <2>h DEF I, ChooseIfExists
    <2> SUFFICES result = DefI(I_internal[n],dState(addition)) BY IExists
    <2> HIDE DEF isub
    <2> SUFFICES BuiltInStep(isub(n)) = DefI(I_internal[n],dState(addition))
      <3> SUFFICES result = BuiltInStep(isub(n)) OBVIOUS
      <3> BuiltInStep(isub(n)) = Natural((isub(n).args)[1].val + (isub(n).args)[2].val)
          BY ONLY <1>isub, isub(n).name = "+" DEF BuiltIn, BuiltInStep
      <3> QED BY <2>n, <1>isub DEF result, BuiltIn
    <2> \A x,y \in ASTs : dState(x) = [dState(y) EXCEPT !.ast = x] BY DEF State
    <2> SUFFICES W(dState(addition)) /\ ~DynamicError(isub(n)) BY DEF DefI, isub, State
    <2>dyn ~DynamicError(isub(n)) 
      <3> SUFFICES Naturals \subseteq ASTs BY <1>a, <2>n, <1>dyn DEF Naturals, Natural, Value
      <3> QED BY ASTsConverge DEF BaseAST
    <2> QED BY <2>dyn, <1>a, <1>ww, HasResultIsWellformed
  <1>b ASSUME ~P PROVE II(addition) = Error
    <2> SUFFICES ASSUME NEW n \in Nat
                 PROVE  II_internal(addition,n) = Error
        BY DEF I, ChooseIfExists
    <2> SUFFICES ASSUME n # 0 PROVE DefI(I_internal[n-1], dState(addition)) = Error BY <1>iint
    <2> SUFFICES DynamicError(isub(n-1)) BY DEF DefI
    <2> SUFFICES dynErr(n-1) BY <1>dyn
    <2> \E arg \in {II_internal(x,n-1) : x \in {a,b}} : arg \notin Naturals 
      <3> SUFFICES ASSUME NEW x \in ASTs, I(dState(x)) \notin Naturals
                   PROVE  \A m \in Nat : II_internal(x,m) \notin Naturals
          BY <1>b
      <3> TAKE m \in Nat
      <3> II_internal(x,m) \in {Error,II(x)} BY UniqueI
      <3> Error \notin Naturals BY DEF Error, Naturals, Natural, Value
      <3> QED OBVIOUS
    <2> SUFFICES ASSUME NEW arg, arg \notin Naturals, arg \in ASTs
                 PROVE  arg.op # "Nat"
        OBVIOUS
    <2> ASTProperty(arg) BY ASTProp
    <2> QED BY DEF ASTProperty
  <1> QED BY <1>a, <1>b

ForAllStatesTemplate(set, op(_,_,_)) == 
  \A funEnv \in FunctionMaps, varEnv \in VariableMaps, ast \in set: 
    op(funEnv, varEnv, ast)
    
ResolutionTemplate(set, op(_)) == 
  LET real_op(fEnv, vEnv, ast) == 
        I(State(fEnv, vEnv, ast)) = I(State(fEnv, vEnv, op(ast)))
  IN  ForAllStatesTemplate(set, real_op)

ForAllValidStates(set, op(_,_,_)) == 
  ForAllStatesTemplate(set, LAMBDA fEnv, vEnv, ast : W(State(fEnv,vEnv,ast)) => op(fEnv,vEnv,ast))

USE DEF ForAllStatesTemplate, ForAllValidStates, ResolutionTemplate

THEOREM ValueWellFormed ==
  LET op(funEnv, varEnv, val) == W_ast(funEnv, DOMAIN varEnv)[val]
  IN  ForAllStatesTemplate(Values, op)
  <1> SUFFICES ASSUME NEW funEnv \in FunctionMaps, NEW varEnv \in VariableMaps, NEW value \in Values
               PROVE  W_ast(funEnv, DOMAIN varEnv)[value]
      OBVIOUS
  <1> DEFINE w == W_ast(funEnv, DOMAIN varEnv)
  <1> SUFFICES DefW(funEnv, DOMAIN varEnv, value, w) BY WExists, ASTsConverge DEF Values, BaseAST
  <1> value.op \in Types BY ValueProp DEF ValueProperty
  <1> QED BY DEF DefW, Wsub

THEOREM ValueResolution ==
  LET op(funEnv, varEnv, ast) == W_funEnv(funEnv) => I(State(funEnv,varEnv,ast)) = ast
  IN  ForAllStatesTemplate(Values, op)
  <1> SUFFICES ASSUME NEW funEnv \in FunctionMaps, NEW varEnv \in VariableMaps, NEW value \in Values,
                      W_funEnv(funEnv)
               PROVE  I(State(funEnv,varEnv,value)) = value
      OBVIOUS
  <1> DEFINE state == State(funEnv,varEnv,value)
  <1> /\ state.funEnv = funEnv
      /\ state.varEnv = varEnv
      /\ state.ast = value
      BY DEF State
  <1> value.op \in Types BY ValueProp DEF ValueProperty
  <1>state state \in States BY ASTsConverge DEF States, BaseAST, State, Values 
  <1> W(State(funEnv,varEnv,value)) 
    <2> DEFINE w == W_ast(funEnv, DOMAIN varEnv)
    <2> SUFFICES w[value] BY <1>state DEF W
    <2> SUFFICES DefW(funEnv, DOMAIN varEnv, value, w) BY WExists, ASTsConverge DEF BaseAST, Values
    <2> QED BY DEF DefW, Wsub
  <1>error value # Error BY ValueProp DEF Error, ValueProperty
  <1> SUFFICES I_internal[1][state] = value BY UniqueI, <1>state, <1>error
  <1> SUFFICES DefI(I_internal[0], state) = value BY IExists, <1>state
  <1> ~DynamicError(ISub(I_internal[0],state)) BY DEF DynamicError, ISub
  <1> QED BY DEF DefI

THEOREM VarResolution ==
  LET op(funEnv,varEnv,var) == 
        var.id \in DOMAIN varEnv => 
        CongruentASTsConclusion(funEnv, varEnv, var, varEnv[var.id])
  IN  ForAllStatesTemplate(Vars, op)

THEOREM ResolveAddition ==
  LET op(addition) == Natural(addition.args[1].val + addition.args[2].val)
  IN  ResolutionTemplate({BuiltIn("+",<<a,b>>) : a,b \in Naturals}, op)
  
THEOREM ResolveEquality == 
  LET op(eq) == BuiltInStep(eq)!1!4!2
  IN  ResolutionTemplate({BuiltIn("=",<<a,b>>) : a,b \in Values}, op)

THEOREM ResolveHead ==
  LET op(fEnv, vEnv, list) ==
        LET II(ast) == I(State(fEnv, vEnv, ast)) 
        IN  \/ list = List(<<>>) /\ II(Aux!first(list)) = II(list)
            \/ II(Aux!first(list)) = II(Head(list.val))
  IN  ForAllStatesTemplate(Lists, op)
  
THEOREM ResolveTail ==
  LET op(fEnv, vEnv, list) ==
        LET II(ast) == I(State(fEnv, vEnv, ast)) 
        IN  \/ list = List(<<>>) /\ II(Aux!rest(list)) = list
            \/ II(Aux!rest(list)) = II(List(Tail(list.val)))
  IN  ForAllStatesTemplate(Lists, op)
  
THEOREM ResolveBuild ==
  \A fEnv \in FunctionMaps, vEnv \in VariableMaps, x \in Values, l \in Lists :
    CongruentASTsConclusion(fEnv, vEnv, Aux!build(x,l), List(<<x>> \o l.val))

THEOREM ResolveCond ==
  LET op(funEnv, varEnv, ast) == 
        LET state(sub) == State(funEnv, varEnv, sub)
            II(sub) == I(state(sub))
        IN  II(ast) = IF II(ast.cond).val THEN II(ast.then) ELSE II(ast.else)
  IN  ForAllValidStates({Cond(cond,then,else) : cond \in Bools, then, else \in ASTs}, op)
  
THEOREM ResolveFunCall == 
  \A funEnv \in FunctionMaps, varEnv \in VariableMaps : 
    \A name \in DOMAIN funEnv : \A args \in [1..Len(funEnv[name].args) -> Values] : 
      I(State(funEnv, varEnv, FunCall(name, args))) = 
      I(State(funEnv, MapMapF(funEnv[name].args, args), funEnv[name].ast))
  <1> TAKE funEnv \in FunctionMaps, varEnv \in VariableMaps
  <1> TAKE name \in DOMAIN funEnv
  <1> TAKE args \in [1..Len(funEnv[name].args) -> Values]
  <1> DEFINE fun == funEnv[name]
             nVarEnv == MapMapF(fun.args, args)
             state1 == State(funEnv, varEnv, FunCall(name, args))
             state2 == State(funEnv, nVarEnv, fun.ast)
  <1>state1 state1 \in States
    <2> SUFFICES FunCall(name, args) \in FunCalls(ASTs) BY ASTsConverge DEF State, States
    <2> QED BY ASTsConverge DEF FunCall, FunCalls, BaseAST, Values, FunctionMaps
  <1>state2 state2 \in States
    <2> SUFFICES MapMapF(fun.args, args) \in VariableMaps BY DEF State, States, FunctionMaps, Functions
    <2> [Range(fun.args) -> Range(args)] \subseteq VariableMaps
      <3> Range(fun.args) \in SUBSET IDs BY DEF Range, FunctionMaps, Functions
      <3> Range(args) \in SUBSET Values BY DEF Range
      <3> QED BY DEF VariableMaps
    <2> QED BY MapMapFRange
  <1> SUFFICES {I_internal[n][state1] : n \in Nat} = {I_internal[n][state2] : n \in Nat} BY DEF I
  <1>An SUFFICES \A n \in Nat : I_internal[n+1][state1] = I_internal[n][state2]
    <2> {n+1 : n \in Nat} = Nat \ {0} BY ONLY TRUE
    <2> I_internal[0][state1] = I_internal[0][state2] BY <1>state1, <1>state2, IExists
    <2> SUFFICES {I_internal[n][state1] : n \in {n+1 : n \in Nat}} = {I_internal[n][state2] : n \in Nat} OBVIOUS
    <2> QED BY ONLY <1>An
  <1> TAKE n \in Nat
  <1> DEFINE II == I_internal[n]
             isub == ISub(II, state1)
             funCallState == State(funEnv, MapMapF(fun.args, isub.args), fun.ast)
             defI == IF ~W(state1) \/ DynamicError(isub) THEN Error ELSE II[funCallState]
             w == W_ast(funEnv, DOMAIN varEnv)
  <1>w w = [ast \in ASTs |-> DefW(funEnv, DOMAIN varEnv, ast, w)] BY ONLY WExists
  <1>state1subs state1.ast = FunCall(name, args) /\ state1.varEnv = varEnv /\ state1.funEnv = funEnv BY DEF State
  <1>state2subs state2.ast = fun.ast /\ state2.varEnv = nVarEnv /\ state2.funEnv = funEnv BY DEF State
  <1>isubSubs isub.op = "FunCall" /\ isub.args = [ arg \in DOMAIN args |-> II[State(funEnv,varEnv,args[arg])] ]
    <2> DEFINE lhs == Map(args, LAMBDA arg : II[[state1 EXCEPT !.ast = arg]])
    <2>a isub = [FunCall(name,args) EXCEPT !.args = lhs] BY <1>state1subs DEF ISub, FunCall
    <2> SUFFICES <1>isubSubs!2!2 = lhs BY <2>a DEF FunCall
    <2> QED BY DEF FunCall, Map, Range, State
  <1>value \A value \in Values : value \in ASTs /\ value.op \in Types BY ValueProp DEF ValueProperty
  <1> HIDE DEF state1, state2
  <1> SUFFICES DefI(II,state1) = II[state2] BY <1>state1, IExists
  <1> SUFFICES defI = II[state2] BY <1>state1subs DEF DefI, FunCall
  <1>noW CASE ~W_funEnv(funEnv)
    <2> HIDE DEF defI
    <2> SUFFICES defI = Error /\ DefI(I_internal[n-1],state2) = Error BY <1>state2, IExists
    <2> SUFFICES ~W(state1) /\ ~W(state2) BY DEF DefI, defI
    <2> QED BY <1>noW, <1>state1subs, <1>state2subs DEF W
  <1> SUFFICES ASSUME W_funEnv(funEnv) PROVE defI = II[state2] BY <1>noW
  <1>0 CASE n = 0
    <2> SUFFICES defI = Error BY <1>0, <1>state2, IExists
    <2>noArgs CASE DOMAIN args = {}
      <3> SUFFICES funCallState \in States BY <1>0, IExists
      <3> QED BY <1>state2, <1>isubSubs, <2>noArgs DEF States, state2, State
    <2> CASE DOMAIN args # {} 
      <3> SUFFICES ASSUME NEW value \in Values PROVE II[State(funEnv,varEnv,value)] = Error 
          BY <1>isubSubs DEF Range, DynamicError
      <3> SUFFICES State(funEnv, varEnv, value) \in States BY IExists, <1>0
      <3> QED BY ASTsConverge DEF State, States, BaseAST, Values
    <2> QED BY <2>noArgs
  <1> SUFFICES ASSUME n # 0 PROVE defI = II[state2] BY <1>0
  <1> isub.op = "FunCall" /\ isub.args = args
    <2> SUFFICES ASSUME NEW value \in Values PROVE II[State(funEnv,varEnv,value)] = value BY <1>isubSubs
    <2> DEFINE state == State(funEnv,varEnv,value)
    <2> state \in States BY ASTsConverge DEF State, States, BaseAST, Values
    <2> state.funEnv = funEnv /\ state.varEnv = varEnv /\ state.ast = value BY DEF State
    <2> SUFFICES DefI(I_internal[n-1], state) = value BY IExists
    <2> HIDE DEF state
    <2> W(state) BY <1>w, <1>value DEF W, DefW, Wsub, States
    <2> ~DynamicError(ISub(I_internal[n-1], state)) BY <1>value DEF DynamicError, ISub
    <2> QED BY <1>value DEF DefI
  <1> W(state1)
    <2> SUFFICES w[FunCall(name, args)] BY <1>state1, <1>state1subs DEF W
    <2> SUFFICES DefW(funEnv, DOMAIN varEnv, FunCall(name,args), w) 
        BY <1>w, <1>state1, FunCall(name, args) \in ASTs DEF state1, States, State
    <2> SUFFICES ASSUME NEW value \in Values PROVE w[value] BY DEF FunCall, Wsub, DefW, Range
    <2> QED BY <1>w, <1>value DEF DefW, Wsub
  <1> ~DynamicError(isub) BY <1>value DEF DynamicError, Range, Error
  <1> QED BY DEF state2

ASSUME IDsFixed == Aux!ids = IDs
ASSUME AuxFunEnvIsWF == Aux!funEnv \in FunctionMaps /\ W_funEnv(Aux!funEnv)

THEOREM ListEmptyOrNot ==
  ASSUME NEW list \in Lists
  PROVE  \/ list = List(<<>>)
         \/ \E x \in Values, xs \in Seq(Values) : list = List(<<x>> \o xs)

AppendElse == Aux!build(Aux!first(Var("l1")),Aux!append(Aux!rest(Var("l1")),Var("l2")))
  
THEOREM ResolveAppend ==
  ASSUME NEW l1 \in Lists, NEW l2 \in Lists,
         NEW varEnv \in VariableMaps
  PROVE  LET II(vEnv, ast) == I(State(Aux!funEnv, vEnv, ast))
             nEnv == [l1 |-> l1, l2 |-> l2]
         IN  II(varEnv,FunCall("append",<<l1,l2>>)) =
             IF l1 = List(<<>>) THEN II(nEnv, l2)
             ELSE II(nEnv, AppendElse)
  <1> DEFINE nEnv == [l1 |-> l1, l2 |-> l2]
             funEnv == Aux!funEnv
             state(ast) == State(funEnv, nEnv, ast)
             fun == funEnv["append"]
             w == W_ast(funEnv, {"l1","l2"})
             nil == List(<<>>)
             cond == Aux!equal(Var("l1"),nil)
             body == Aux!appendBody
             II(ast) == I(state(ast))
  <1>envs /\ funEnv \in FunctionMaps /\ W_funEnv(funEnv)
          /\ nEnv \in VariableMaps 
     BY AuxFunEnvIsWF, IDsFixed DEF Values, VariableMaps, Aux!ids, nEnv
  <1> HIDE DEF W_funEnv, nEnv, funEnv\*, state
  <1> USE DEF Aux!funEnv
  <1>w w = [ast \in ASTs |-> DefW(funEnv, {"l1","l2"}, ast, w)] BY WExists
  <1>fun fun.args = <<"l1","l2">> /\ fun.ast = Aux!appendBody BY DEF funEnv, Aux!Function
  <1> SUFFICES II(body) = IF l1 = List(<<>>) THEN II(l2) ELSE II(AppendElse)
    <2> USE <1>fun DEF nEnv
    <2> "append" \in DOMAIN funEnv BY DEF funEnv
    <2> <<l1,l2>> \in [1..Len(fun.args) -> Values] BY DEF Values
    <2> nEnv = MapMapF(fun.args, <<l1,l2>>)
      <3> DEFINE nEnv2 == MapMapF(fun.args, <<l1,l2>>)
      <3> \A arg \in Range(fun.args) : nEnv[arg] = nEnv2[arg] 
        <4> SUFFICES \A arg \in DOMAIN fun.args : nEnv2[fun.args[arg]] = <<l1,l2>>[arg] BY DEF Range
        <4> DOMAIN fun.args = DOMAIN <<l1,l2>> OBVIOUS
        <4> IsBijective(fun.args) BY DEF IsBijective 
        <4> QED BY MapMapFBijective
      <3> DOMAIN nEnv = DOMAIN nEnv2 BY DEF MapMapF, Range
      <3> Range(fun.args) = DOMAIN nEnv BY DEF Range
      <3> QED BY DEF MapMapF
    <2> HIDE DEF Aux!funEnv
    <2> QED BY ResolveFunCall, <1>envs DEF funEnv
  <1> \A ast : 
        /\ state(ast).funEnv = funEnv /\ state(ast).varEnv = nEnv /\ state(ast).ast = ast 
        /\ \A sub : [state(ast) EXCEPT !.ast = sub] = state(sub)
      BY DEF State
  <1>state state(body) \in States OMITTED
  <1>W W(state(body))
    <2> SUFFICES w[body] BY <1>state, <1>envs, DOMAIN state(body).varEnv = {"l1","l2"} DEF W, nEnv
    <2> fun \in Range(funEnv) BY DEF Range, funEnv
    <2> W_ast(funEnv, Range(fun.args))[fun.ast] BY <1>envs DEF W_funEnv
    <2> QED BY <1>fun DEF Range
  <1>vars II(Var("l1")) = II(l1) /\ II(Var("l2")) = II(l2)
        BY <1>envs, VarResolution, IDsFixed 
        DEF state, States, Var, Vars, Aux!ids, CongruentASTsConclusion, nEnv
  <1>cond II(cond) = II(Bool(l1 = nil))
    <2> DEFINE ast2 == Aux!equal(l1,nil)
    <2> cond \in ASTs /\ ast2 \in ASTs OMITTED
    <2> \A ast \in {cond, ast2} : 
          /\ DOMAIN ast = {"op", "name", "args"}
          /\ ast.op = "BuiltIn" /\ ast.name = "=" 
        BY DEF Aux!equal, Aux!BuiltIn
    <2> SUFFICES II(ast2) = II(Bool(l1 = nil))
      <3> SUFFICES CongruentASTsAssumption(funEnv, nEnv, cond, ast2)
          BY Congruence, <1>envs DEF CongruentASTsConclusion, state
      <3> W(state(ast2)) /\ W(state(cond)) OMITTED
      <3> SUFFICES Map(cond.args, II) = Map(ast2.args, II)
          BY DEF ISubSplit, Aux!equal, Aux!BuiltIn, CongruentASTsAssumption, state
      <3> SUFFICES II(Var("l1")) = II(l1) BY DEF Map, Aux!equal, Aux!BuiltIn
      <3> QED BY <1>vars
    <2> l1 \in Values /\ nil \in Values BY ListsConverge, <<>> \in Seq(Values) DEF Values
    <2> ast2 = BuiltIn("=",<<l1,nil>>) /\ ast2.args = <<l1,nil>> BY DEF Aux!equal, Aux!BuiltIn, BuiltIn
    <2> HIDE DEF ast2
    <2> (l1.op = nil.op /\ l1.val = nil.val) <=> (l1 = nil)
        BY ListsConverge DEF List, Value
    <2> QED BY ResolveEquality, <1>envs DEF state
  <1> DEFINE ast == Cond(Bool(l1 = nil), l2, AppendElse)
  <1>ast ast \in ASTs OMITTED
  <1>ast2 ast \in {Cond(c,t,e) : c \in Bools, t,e \in ASTs}
    <2> ASTProperty(ast) BY <1>ast, ASTProp
    <2> ast \in Conds(ASTs) BY DEF ASTProperty, Cond, Conds
    <2> SUFFICES Bool(l1 = nil) \in Bools BY DEF Conds, Cond
    <2> QED BY DEF Bool, Bools, Value
  <1>Wast W(state(ast))
    <2> SUFFICES w[ast] BY <1>envs, <1>ast DEF W, State, States, nEnv
    <2> ast.op = "Cond" BY DEF Cond
    <2> SUFFICES Wsub(w,ast) BY <1>w, <1>ast DEF DefW
    <2> w[Bool(l1 = nil)] OMITTED
    <2> w[l2]             OMITTED
    <2> w[AppendElse]     OMITTED
    <2> QED BY DEF Wsub, Cond
  <1>cond2 II(body) = II(ast)
    <2> DEFINE ast2 == Cond(cond, Var("l2"), AppendElse)
    <2> Aux!appendBody = ast2 OMITTED
    <2> ast2 \in ASTs BY <1>state DEF State, States
    <2> SUFFICES CongruentASTsAssumption(funEnv, nEnv, ast, ast2)
        BY Congruence, <1>envs, <1>ast DEF CongruentASTsConclusion
    <2> W(state(ast2)) OMITTED
    <2> QED BY <1>cond, <1>vars, <1>Wast DEF CongruentASTsAssumption, ISubSplit, Cond
  <1> HIDE DEF ast
  <1>cond3 ResolveCond!:!op(funEnv, nEnv, ast) BY <1>ast2, <1>Wast, ResolveCond, <1>envs
  <1>bool l1 = nil <=> II(Bool(l1 = nil)).val 
    <2> Bool(l1 = nil) \in Values BY DEF Bool, Bools, Value, Values
    <2> SUFFICES Bool(l1 = nil).val <=> l1 = nil BY ValueResolution, <1>envs
    <2> QED BY DEF Bool, Value
  <1> QED BY <1>cond3, <1>bool, <1>cond2 DEF ast, Cond

THEOREM ResolveAppend2 ==
  \A l1, l2 \in Lists, varEnv \in VariableMaps :
    I(State(Aux!funEnv, varEnv, FunCall("append",<<l1,l2>>))) = List(l1.val \o l2.val)
  <1> SUFFICES ASSUME NEW l2 \in Lists PROVE 
      \A l1 \in Lists, varEnv \in VariableMaps :
        I(State(Aux!funEnv, varEnv, FunCall("append",<<l1,l2>>))) = List(l1.val \o l2.val)
      OBVIOUS
  <1> DEFINE P1(l1) == \A varEnv \in VariableMaps : 
                 I(State(Aux!funEnv, varEnv, FunCall("append",<<l1,l2>>))) = List(l1.val \o l2.val)
             fEnv == Aux!funEnv
             vEnv(l1) == [l1 |-> l1, l2 |-> l2]
             state(l1,ast) == State(fEnv,vEnv(l1),ast)
             II(l1,ast) == I(state(l1,ast))
             P(l1) == List(l1.val \o l2.val) = IF l1 = List(<<>>) THEN II(l1,l2) ELSE II(l1,AppendElse)
  <1>0 P1(List(<<>>))
    <2> TAKE varEnv \in VariableMaps
    <2> SUFFICES P(List(<<>>)) BY ResolveAppend, ListsConverge, List(<<>>) \in Lists
    <2> SUFFICES l2 = II(List(<<>>),l2) BY ListsConverge, l2 = List(l2.val) DEF List, Value
    <2> List(<<>>) \in Values /\ l2 \in Values BY ListsConverge, <<>> \in Seq(Values) DEF Values
    <2> vEnv(List(<<>>)) \in VariableMaps BY IDsFixed DEF VariableMaps, Aux!ids
    <2> QED BY AuxFunEnvIsWF, ValueResolution
  <1> SUFFICES ASSUME NEW x \in Values, NEW xs \in Seq(Values), P1(List(xs))
               PROVE  P1(List(<<x>> \o xs))
      BY <1>0, InductionOverLists
  <1> TAKE varEnv \in VariableMaps
  <1> DEFINE l1 == List(<<x>> \o xs)
             targetSeq == <<x>> \o xs \o l2.val
             III(ast) == II(l1, ast)
             w(a) == W(state(l1,a))
             assume(a,b) == CongruentASTsAssumption(fEnv, vEnv(l1), a, b)
             conclude(a,b) == CongruentASTsConclusion(fEnv, vEnv(l1), a, b)
             vSeq == Seq(Values)
  <1> /\ l2.val \in vSeq /\ <<x>> \in vSeq
      /\ <<x>> \o xs \in vSeq /\ xs \o l2.val \in vSeq
      /\ targetSeq \in vSeq
     BY ListsConverge DEF List, Value
  <1> \A seq \in vSeq : List(seq) \in Lists /\ List(seq).val = seq BY ListsConverge DEF List, Value
  <1> l1 = List(<<x>> \o xs) /\ l1 \in Lists BY ListsConverge, <<x>> \o xs \in Seq(Values)
  <1> SUFFICES P(l1) BY ResolveAppend
  <1> SUFFICES List(targetSeq) = III(AppendElse) BY DEF List, Value
  <1>envs /\ vEnv(l1) \in VariableMaps
          /\ fEnv \in FunctionMaps /\ W_funEnv(fEnv)
    <2> vEnv(l1) \in [{"l1","l2"} -> Values] BY DEF Values
    <2> vEnv(l1) \in VariableMaps BY IDsFixed DEF VariableMaps, Aux!ids
    <2> QED BY AuxFunEnvIsWF, ValueResolution
  <1> HIDE DEF vEnv, fEnv, l1, P1, W_funEnv
  <1>con \A a, b \in ASTs : assume(a,b) => III(a) = III(b) BY Congruence, <1>envs DEF CongruentASTsConclusion
  <1>vars /\ III(Var("l1")) = III(l1) /\ III(Var("l2")) = III(l2)
          /\ Var("l1") \in ASTs /\ Var("l2") \in ASTs
          BY <1>envs, VarResolution, IDsFixed, ASTsConverge
          DEF CongruentASTsConclusion, Aux!ids, Var, Vars, vEnv, BaseAST
  <1>prev III(FunCall("append", <<List(xs),l2>>)) = III(List(xs \o l2.val))
    <2> List(xs) \in Values /\ List(xs).val = xs BY ListsConverge DEF Values, Value, List
    <2> List(xs \o l2.val) \in Values BY ListsConverge, xs \o l2.val \in Seq(Values) DEF Values
    <2> III(List(xs \o l2.val)) = List(xs \o l2.val) BY <1>envs, ValueResolution
    <2> QED BY <1>envs, ValueResolution DEF P1, fEnv
  <1> \A z : w(z) => z \in ASTs BY DEF W, State, States
  <1>head III(Aux!first(Var("l1"))) = III(x)
    <2> SUFFICES III(Aux!first(l1)) = III(x)
      <3> w(Aux!first(l1)) /\ w(Aux!first(Var("l1"))) OMITTED
      <3> assume(Aux!first(l1), Aux!first(Var("l1"))) 
          BY <1>vars DEF Map, CongruentASTsAssumption, ISubSplit, Aux!first, Aux!BuiltIn
      <3> QED BY <1>con
    <2> QED BY ResolveHead, <1>envs DEF List, Value
  <1>tail III(Aux!rest(Var("l1"))) = III(List(xs))    
    <2> SUFFICES III(Aux!rest(l1)) = III(List(xs))
      <3> w(Aux!rest(l1)) /\ w(Aux!rest(Var("l1"))) OMITTED
      <3> assume(Aux!rest(l1), Aux!rest(Var("l1"))) 
          BY <1>vars DEF Map, CongruentASTsAssumption, ISubSplit, Aux!rest, Aux!BuiltIn
      <3> QED BY <1>con
    <2> QED BY ResolveTail, <1>envs DEF List, Value
  <1>append III(Aux!append(Aux!rest(Var("l1")), Var("l2"))) = III(List(xs \o l2.val))
    <2> w(Aux!append(Aux!rest(Var("l1")), Var("l2"))) /\ w(FunCall("append", <<List(xs),l2>>)) OMITTED
    <2> assume(Aux!append(Aux!rest(Var("l1")), Var("l2")), FunCall("append", <<List(xs),l2>>))
        BY <1>vars, <1>tail DEF Map, CongruentASTsAssumption, ISubSplit, Aux!append, Aux!FunCall, FunCall
    <2> QED BY <1>con, <1>prev
  <1> SUFFICES III(Aux!build(x, List(xs \o l2.val))) = List(targetSeq)
    <2> w(AppendElse) /\ w(Aux!build(x, List(xs \o l2.val))) OMITTED
    <2> assume(AppendElse, Aux!build(x, List(xs \o l2.val)))
        BY <1>append, <1>head DEF AppendElse, Aux!build, Aux!BuiltIn, ISubSplit, CongruentASTsAssumption, Map
    <2> QED BY <1>con
  <1> SUFFICES III(List(targetSeq)) = List(targetSeq)
    <2> SUFFICES III(List(targetSeq)) = III(List(<<x>> \o List(xs \o l2.val).val))
        BY ResolveBuild, <1>envs DEF CongruentASTsConclusion
    <2> QED BY ConcatAssociative
  <1> QED BY ValueResolution, <1>envs DEF Values

=============================================================================