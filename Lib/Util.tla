-------------------------------- MODULE Util --------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets,  SequenceOps, Functions, FiniteSetsExt

(******************************************************************************)
(* general utils                                                              *)
(******************************************************************************)

SetByPred(P(_)) == CHOOSE S : \A s : (s \in S) = P(s)
SetByPredTLC(P(_)) == {s \in Any : P(s)}

ChooseIfExists(S, P(_), fb) == 
  IF \E s \in S : P(s) 
  THEN CHOOSE s \in S : P(s)
  ELSE fb

Arbitrary(set) == CHOOSE s \in set : TRUE

ConditionalOp(cond, val, op(_)) == IF cond THEN op(val) ELSE val

(* functions & sequences *)

IsBijective(fun) == \A i1, i2 \in DOMAIN fun : i1 = i2 <=> fun[i1] = fun[i2]
Invert(f, img) == CHOOSE arg \in DOMAIN f : f[arg] = img
\*Inverse(f) == [img \in Range(f) |-> Invert(f, img)]

MinPrec(S, _ \prec _) == CHOOSE x \in S : \A y \in S : \neg (y \prec x)
MinInClass(P(_), _ \prec _) == CHOOSE x : P(x) /\ \A y : P(y) => \neg (y \prec x)
\* should be called min arg
Lowest(f, P(_), _ \prec _) == CHOOSE arg \in DOMAIN f : P(f[arg]) /\ \A arg2 \in DOMAIN f : (P(f[arg2]) => \neg arg2 \prec arg)
LowestIdx(seq, P(_)) == Lowest(seq, P, <)

Map(f, R(_)) == [arg \in DOMAIN f |-> R(f[arg])]
MapF(f, g) == Map(f, LAMBDA arg : g[arg])

MapMap(S,L(_),R(_)) ==
  LET LS == {L(s) : s \in S}
  IN  [l \in LS |-> R(CHOOSE s \in S : L(s) = l)]
MapMapF(L,R) == [l \in Range(L) |-> R[CHOOSE o \in DOMAIN R : L[o] = l]]

PartialFunctions(domain, codomain) == UNION { [subset -> codomain] : subset \in SUBSET domain }
SingleFunction(arg,val) == [a \in {arg} |-> val]

IsFunction(f) == f = [arg \in DOMAIN f |-> f[arg]]
IsFunctionOf(f,domain) == IsFunction(f) /\ DOMAIN f = domain
IsSeq(f) == IsFunction(f) /\ DOMAIN f \in {1..n : n \in Nat}

ExtendBy(f,g) == [arg \in DOMAIN f \cup DOMAIN g |-> IF arg \in DOMAIN f THEN f[arg] ELSE g[arg]]
RestrictTo(f,args) == [arg \in args \cap DOMAIN f |-> f[arg]]
RestrictBy(f,args) == [arg \in DOMAIN f \ args |-> f[arg]]

EqualExcept(f,g,args) == RestrictBy(f,args) = RestrictBy(g,args)

PartialMap(fun, domain, op(_)) == 
  ExtendBy([arg \in domain |-> op(fun[arg])], fun)
PartialMapF(fun, domain, f) == PartialMap(fun, domain, LAMBDA x : f[x])

\* TODO : replace reduce with it's equivalent from the community modules

Reduce(seq,op(_,_),init) ==
  LET f[idx \in Nat] == IF Len(seq) < idx THEN init ELSE op(seq[idx],f[idx+1])
  IN  f[1]

ReduceLeft(seq,op(_,_),init) ==
  LET f[idx \in Nat] == IF 0 = idx THEN init ELSE op(f[idx-1],seq[idx])
  IN  f[Len(seq)]

SweepInit(seq, op(_,_), init) == 
  LET full_op(l,r) == l \o <<op(Last(l),r)>>
  IN  ReduceLeft(seq, full_op, <<init>>)

Sweep(seq, op(_,_)) == 
  IF seq = <<>> THEN <<>> 
  ELSE SweepInit(Tail(seq), op, Head(seq))

Flatten(seq) == Reduce(seq, LAMBDA l,r : l \o r, <<>>)

SeqN(S,n) == [1..n -> S]

CartProd(sets) == 
  LET op(set,prod) == {<<a>> \o b : a \in set, b \in prod}
  IN  Reduce(sets, op, {<<>>})

At(obj, path) == 
  LET op(l,r) == l[r] 
  IN  ReduceLeft(path, op, obj)

(*
Except(obj, path, sub) == 
  LET f[n \in Nat] == 
         LET val == IF n = Len(path) THEN sub ELSE f[n+1] 
         IN  [At(obj, RestrictTo(path,1..(n-1))) EXCEPT ![path[n]] = val]
  IN  IF path = <<>> THEN obj ELSE f[1]
*)

Except(obj, path, sub) == 
  LET vals == SweepInit(Front(path), LAMBDA l,r : l[r], obj)
      VPs == [idx \in DOMAIN path |-> [val |-> vals[idx], path |-> path[idx]]]
      op(l,r) == [l.val EXCEPT ![l.path] = r]
  IN  Reduce(VPs, op, sub)

EmptyFunction == <<>>
OverridableFunction(domain, def(_,_))  == LET f[arg \in domain] == def(f,arg) IN f
OverridableFunction_(domain, def(_,_)) == LET f[arg \in Any]    == def(f,arg) IN f

(******************************************************************************)
(* Recursive definitions and helpers                                          *)
(******************************************************************************)

\* consider renaming / simplification of the following operators before suggesting them as part of community modules
RecF(s0, next(_,_))   == LET f[n \in Nat] == IF n = 0 THEN s0 ELSE next(f[n-1],n) IN  f
RecDef(s0, next(_,_)) == UNION {RecF(s0, next)[n] : n \in Nat}

\* should be called LeastFixedPointOfContinuousOperator fixed point or smth similar.
FixedPoint(Op(_)) == RecDef({}, LAMBDA p,n : Op(p))

IsFixedPointOfOp(X,Op(_)) == X = Op(X)
HasFixedPoint(Op(_)) == \E X : IsFixedPointOfOp(X, Op)
IsLeastFixedPointOfOp(LFP, Op(_)) == 
  /\ IsFixedPointOfOp(LFP, Op)
  /\ \A FP : IsFixedPointOfOp(FP, Op) => LFP \subseteq FP

SeekFixedPoint(Op(_), start) == 
  LET f == RecF(start, LAMBDA p, n: Op(p))
      IsFP(n) == f[n] = f[n+1]
      P(n) == IsFP(n) /\ \A m \in Nat : m < n => ~IsFP(m)
      n == CHOOSE n \in Nat : P(n)
  IN  f[n]

SubNodes(node, infos) == 
  LET subList(info) == 
        IF info.isList THEN node[info.name] ELSE <<node[info.name]>>
  IN  Flatten(Map(infos, subList))

SubNodesBefore(node, infos, cond(_)) ==
  LET subs == SubNodes(node, infos)
  IN  IF \E idx \in DOMAIN subs : cond(subs[idx])
      THEN RestrictTo(subs, 1..LowestIdx(subs,cond)-1)
      ELSE subs
      
MapSubNodes(node,o_infos,op(_)) == 
  LET infos == Range(o_infos)
      NonListNames == {info.name : info \in {info \in infos : ~info.isList}}
      MapNonList == PartialMap(node, NonListNames, op)
      ListNames == {info.name : info \in {info \in infos : info.isList}}
      MapList == PartialMap(MapNonList, ListNames, LAMBDA list : Map(list,op))
  IN  MapList

SimpleTransformFirstSubNode(node, infos, cond(_), op(_)) ==
  LET full_op(info, next) == 
        LET selected == node[info.name]
            idx == LowestIdx(selected, cond)
        IN  CASE info.isList /\ \E i \in DOMAIN selected : cond(selected[i])
                 -> op(selected[idx])
            []   ~info.isList /\ cond(selected)
                 -> op(selected)
            []   OTHER -> next
  IN  Reduce(infos, full_op, node)

TransformFirstSubNode(node, infos, cond(_), op(_,_), domain) ==
  LET full_op(info, next) == 
        LET selected == node[info.name]
            idx == LowestIdx(selected, cond)
        IN  CASE info.isList /\ \E i \in DOMAIN selected : cond(selected[i])
                 -> op(selected[idx], [sub \in domain |-> [node EXCEPT ![info.name][idx] = sub]])
            []   ~info.isList /\ cond(selected)
                 -> op(selected, [sub \in domain |-> [node EXCEPT ![info.name] = sub]])
            []   OTHER -> next
  IN  Reduce(infos, full_op, node)
  
(******************************************************************************)
(* function / community module stuff                                          *)
(******************************************************************************)

\* TODO add a community module for typing that provides smth similar to the following
\* IsNat(x) == x \in Nat
IsFun(x) == x = [arg \in DOMAIN x |-> x[arg]]
\* IsStdSet(x)
\* ...
\* TypedCompare(x,y)

ConstructFromSetIf(set, P(_), C(_)) == {C(e) : e \in {e \in set : P(e)}}

\* Very impractical due to comparability restrictions
TransitiveRange(fun) == 
  LET Op(set) == {fun} \cup UNION ConstructFromSetIf(set, IsFun, Range)
  IN  SeekFixedPoint(Op,{})

\* Transitive Domain without intermediate paths
LeafDomain(fun) ==
  LET td[sub \in TransitiveRange(fun)] == 
        IF IsFun(sub) /\ DOMAIN sub # {}
        THEN UNION {{<<arg>> \o val : val \in td[sub[arg]]} : arg \in DOMAIN sub}
        ELSE {<<>>}
  IN  td[fun]

TransitiveDomain(fun) ==
  LET tuple(path, val) == <<path, val>>
      isfun(t) == IsFun(t[2])
      construct(t) == {tuple(t[1] \o <<arg>>, t[2][arg]) : arg \in DOMAIN t[2]}
      Op(tuples) == {tuple(<<>>,fun)} \cup UNION ConstructFromSetIf(tuples, isfun, construct)
  IN  {t[1] : t \in SeekFixedPoint(Op, {})}
  (*  LET td[sub \in TransitiveRange(fun)] == \* this is bad bc it depends on TransitiveRange
        IF Print(sub, TRUE) /\ IsFun(sub)
        THEN {<<>>} \cup UNION {{<<arg>> \o val : val \in td[sub[arg]]} : arg \in DOMAIN sub}
        ELSE {<<>>}
  IN  td[fun]
  *)
  
TransitiveFun(fun) ==
  [arg \in TransitiveDomain(fun) |-> At(fun, arg)]

DeepFind(fun, P(_)) == 
  (*LET def(sub, find) == \* warining: this does not register P(fun)
        LET set_a(arg) == IF P(sub[arg]) THEN {<<>>} ELSE {}
            set_b(arg) == IF ~IsFun(sub[arg]) THEN {} ELSE find[sub[arg]]
            set(arg) == {<<arg>> \o path : path \in set_a(arg) \cup set_b(arg)}
        IN  UNION { set(arg) : arg \in DOMAIN fun}
      find[sub \in TransitiveRange(fun)] == def(sub,find)
  IN  find[fun]*)
  {path \in TransitiveDomain(fun) : P(At(fun, path))}
  
Find(fun, P(_)) ==
  (* LET def(sub, find) == \* depends on TransitiveRange => bad
        LET set ==
              UNION { {<<arg>> \o path : path \in find[sub[arg]]} : arg \in DOMAIN sub}
        IN  IF P(sub) THEN {<<>>} 
            ELSE IF IsFun(sub) THEN set
            ELSE {} 
      find[sub \in TransitiveRange(fun)] == def(sub,find)
  IN  find[fun]  *)
  LET def(path, find) == 
        LET sub == At(fun, path)
            set ==
              UNION { find[path \o <<arg>>] : arg \in DOMAIN sub}
        IN  IF P(sub) THEN {path} 
            ELSE IF IsFun(sub) THEN set
            ELSE {} 
      find[path \in TransitiveDomain(fun)] == def(path,find)
  IN  find[<<>>]

FindWithPathPredicate(fun, P(_,_)) ==
  LET def(path, find) == 
        LET sub == At(fun, path)
            set ==
              UNION { find[path \o <<arg>>] : arg \in DOMAIN sub}
        IN  IF P(path, sub) THEN {path} 
            ELSE IF IsFun(sub) THEN set
            ELSE {} 
      find[path \in TransitiveDomain(fun)] == def(path,find)
  IN  find[<<>>]

Replace(fun, P(_), R(_)) ==
  LET op(x,prev) == Except(prev, x, R(At(fun,x)))
  IN  FoldSet(op, fun, Find(fun, P))

ModelValue(x) == CHOOSE X : TRUE \* TODO implement in community module
  
Match(in, variables, pattern) ==
  (* property
  LET P(subst) == 
        LET P(sub) == sub \in variables
            R(sub) == subst[sub]
        IN  DOMAIN subst = variables /\ in = Replace(pattern, P, R)
      result(valid, subst) == [ valid |-> valid, substitution |-> subst]
  IN  IF \E s : P(s) THEN result(TRUE, CHOOSE s : P(s)) ELSE result(FALSE, <<>>) *)
  LET Perror(path, sub) == 
        LET psub == At(pattern, path)
        IN  /\ psub \notin variables
            /\ \/ IsFun(sub) # IsFun(psub)
               \/ ~IsFun(sub) /\ psub # sub
               \/ IsFun(sub) /\ DOMAIN psub # DOMAIN sub
      Pvar(var, path, sub) == var # sub /\ At(pattern, path) = var
      error_paths == FindWithPathPredicate(in, Perror)
      var_paths(var) == FindWithPathPredicate(in, LAMBDA path, sub : Pvar(var, path, sub))
      var_sets == [var \in variables |-> {At(in, path) : path \in var_paths(var)}]
  IN  IF error_paths = {} /\ \A var \in variables : Cardinality(var_sets[var]) = 1 
      THEN [valid |->  TRUE, substitution |-> Map(var_sets, Arbitrary)]
      ELSE [valid |-> FALSE, substitution |-> <<>>]

\* TODO Operator to check membership of a (possibly infinite) recursive definition
\* IsMemberOfAssociatedRecDef(Op(_), value) == value \in FixedPoint(Op)

\* TODO Operator (with java override) that checks whether an operator is guaranteed continuous
\* usful for warning :D
\* which operators preserve continuity?
\* GuaranteesContinuity(Op(_)) == IF IsContinuous(Op) THEN Arbitrary(BOOLEAN) ELSE FALSE

\* TODO it would be lovely to have the possibility to add TLC module overrides to instances
\* This way we could have a module for inductive definitions

(*
---- module InductiveDefinition ----

CONSTANT Op(_)

S == FixedPoint(Op)

f == RecF({}, LAMBDA p,n : Op(p))

IsMember(val) == value \in S

HasFiniteIterations == \E n \in Nat : f[n] = f[n+1]

====
*)

(******************************************************************************)
(* specifics                                                                  *)
(******************************************************************************)

ValidEncoding(e) ==
  \A op \in e.Operators : 
    \A seq \in CartProd(Map(op.arity, LAMBDA arg : DOMAIN e.Encodings[arg])) :
      e.Encodings[op.ret][op.operator[seq]] = 
      op.eoperator[[ arg \in DOMAIN seq |-> e.Encodings[op.arity[arg]][seq[arg]]]]

\* if all members of the input type are comparable, the definition simplifies a lot
ValidEncodingComp(e) ==
  \A op \in e.Operators : \A args \in DOMAIN op.op :
    e.Encoding[op.op[args]] = op.eop[Map(args, LAMBDA arg : e.Encoding[arg])]

=============================================================================