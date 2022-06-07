----------------------------- MODULE AExp -----------------------------
EXTENDS Integers, FiniteSets, Sequences, Util, UtilTLAPS, UtilDebug

CONSTANT IDs

\* should be in ASTs for SOS...
Error               == [ op |-> "error" ]
ASTString(ast)      == "override me"
PrintMTAST(msg,ast) == TRUE

(******************************************************************************)
(* list of types                                                              *)
(******************************************************************************)

IntType            == [ op |-> "type", type |-> "int" ]
BoolType           == [ op |-> "type", type |-> "bool" ]

FunType(args, ret) == [ op |-> "type", type |-> "fun", args |-> args, ret |-> ret ]
ListType(type)     == [ op |-> "type", type |-> "list", template |-> type ]
TupleType(types)   == [ op |-> "type", type |-> "tuple", types |-> types]

FunTypes(p)        == [ op : {"type"}, type : {"fun"}, args : Seq(p), ret : p ]
ListTypes(p)       == [ op : {"type"}, type : {"list"}, template : p ]
TupleTypes(p)      == [ op : {"type"}, type : {"tuple"}, types : Seq(p) ]

BaseTypes          == {IntType, BoolType}
NextTypes(p,n)     == p \cup FunTypes(p) \cup ListTypes(p) \cup TupleTypes(p)
Types              == RecDef(BaseTypes, NextTypes)

TypeIDPair(type,id) == [id |-> id, type |-> type]
TypeIDPairs         == [id : IDs, type : Types]
TILs                == Seq(TypeIDPairs)
TILids(til)         == [idx \in DOMAIN til |-> til[idx].id]
TILtypes(til)       == [idx \in DOMAIN til |-> til[idx].type]
MapFromTIL(til)     == MapMapF(TILids(til), TILtypes(til))

(******************************************************************************)
(* list of values                                                             *)
(******************************************************************************)

Value(type, val)  == [ op |-> "val", type |-> type, val |-> val ]
Integer(i)        == Value(      IntType, i)
Bool(b)           == Value(     BoolType, b)
List(t,l)         == Value(  ListType(t), l)
Tuple(ts,l)       == Value(TupleType(ts), l)
Fun(til, rt, ast) == Value(FunType(TILtypes(til),rt), [fargs |-> TILids(til), ast |-> ast])

SelectTags(objs,tags) == {sub \in objs : sub.op \in tags}
SelectTag(objs,tag)   == {sub \in objs : sub.op = tag}

Bools        == [ op : {"val"}, type : {BoolType}, val : BOOLEAN ]
Integers     == [ op : {"val"}, type : {IntType}, val : Int ]
Lists(p)     == [ op : {"val"}, type : ListTypes(Types), val : Seq(SelectTag(p,"val")) ]
Tuples(p)    == [ op : {"val"}, type : TupleTypes(Types), val : Seq(SelectTag(p,"val")) ]
Funs(p)      == [ op : {"val"}, type : FunTypes(Types), val : [fargs : Seq(IDs), ast : p] ]
Values(p)    == Bools \cup Integers \cup Lists(p) \cup Funs(p) \cup Tuples(p)

(******************************************************************************)
(* list of language constructs                                                *)
(******************************************************************************)

Tags         == {"var", "global var", "val", "cond", "fun call", "builtin", "tuple access",
                 "list ctor", "tuple ctor", "fun ctor"}
BuiltInNames == {"+","-","*",">","=","build","tail","head","neg"}

Var(id)                  == [ op |-> "var" , id |-> id ]
GVar(id)                 == [ op |-> "global var", id |-> id ]
Cond(cond, then, else)   == [ op |-> "cond", cond |-> cond, then |-> then, else |-> else ]
FunCall(fun, args)       == [ op |-> "fun call" , fun |-> fun, args |-> args ]
BuiltIn(name, args)      == [ op |-> "builtin" , name |-> name, args |-> args ]
ListCtor(type, args)     == [ op |-> "list ctor", type |-> type, args |-> args ]
TupleCtor(args)          == [ op |-> "tuple ctor", args |-> args ]
FunCtor(til, ret, ast)   == [ op |-> "fun ctor", fargs |-> til, ret |-> ret, ast |-> ast ]
TupleAccess(ast, idx)    == [ op |-> "tuple access", tuple |-> ast, idx |-> idx ]

Vars             == [ op : {"var"}, id : IDs ]
GVars            == [ op : {"global var"}, id : IDs ]
Conds(p)         == [ op : {"cond"}, cond : p, then : p, else : p ]
FunCalls(p)      == [ op : {"fun call"}, fun : p, args : Seq(p) ]
BuiltIns(p)      == [ op : {"builtin"}, name : BuiltInNames, args : Seq(p) ]
ListCtors(p)     == [ op : {"list ctor"}, type : Types, args : Seq(p) ]
TupleCtors(p)    == [ op : {"tuple ctor"}, args : Seq(p) ]
FunCtors(p)      == [ op : {"fun ctor"}, fargs : TILs, ret : Types, ast : p ]
TupleAccesses(p) == [ op : {"tuple access"}, tuple : p, idx : Nat ]

GetInfoAST(ast) == 
  LET op == ast.op
      Info(name, isList, isLazy) == [ name |-> name, isList |-> isList, isLazy |-> isLazy ] 
      IList(name) == Info(name,TRUE,FALSE)
      ILazy(name) == Info(name,FALSE,TRUE)
      I(name)     == Info(name,FALSE,FALSE)
  IN  CASE op = "val"           -> <<>>
      []   op = "var"           -> <<>>
      []   op = "global var"    -> <<>>
      []   op = "cond"          -> <<I("cond"),ILazy("then"),ILazy("else")>>
      []   op = "fun call"      -> <<I("fun"),IList("args")>>
      []   op = "builtin"       -> <<IList("args")>>
      []   op = "list ctor"     -> <<IList("args")>>
      []   op = "tuple ctor"    -> <<IList("args")>>
      []   op = "fun ctor"      -> <<ILazy("ast")>>
      []   op = "tuple access"  -> <<I("tuple")>>
      
FilterAttributes(node, filter(_)) == SelectSeq(GetInfoAST(node), filter)
FilterNonLazyAttributes(node) == FilterAttributes(node, LAMBDA info : ~info.isLazy)

(* ASTs & states *)

BaseAST      == Bools \cup Integers \cup Vars \cup GVars \cup {Error}
NextAST(p,n) == 
  p \cup 
  (Lists(p) \cup Tuples(p) \cup Funs(p)) \cup
  (Conds(p) \cup FunCalls(p) \cup BuiltIns(p)) \cup 
  (ListCtors(p) \cup TupleCtors(p) \cup FunCtors(p) \cup TupleAccesses(p))
ASTs == RecDef(BaseAST, NextAST)

Universe == {v \in ASTs : v.op = "value"}

Environments == PartialFunctions(IDs, Universe)
SEnvironments == PartialFunctions(IDs, Types)

State(genv, env, ast) == [genv |-> genv, env |-> env, ast |-> ast]
States == [ genv : Environments, env : Environments, ast : ASTs ]
SStates == [ genv : SEnvironments, env : SEnvironments, ast : ASTs ]
StateToStatic(state) == PartialMap(state, {"genv", "env"}, LAMBDA env : Map(env, LAMBDA val : val.type))

(* Built Ins*)
           
BuiltInList[name \in BuiltInNames] == 
  LET BI(sigFun, valFun, errFun) == [sigFun |-> sigFun, valFun |-> valFun, errFun |-> errFun]
      single(in, out) == [t \in {in} |-> out]
      multi(len, P(_)) == {tl \in Seq(Types) : Len(tl) = len /\ P(tl)}
      NoError == [v \in Seq(ASTs) |-> TRUE]
  IN
  CASE name = "+" -> BI(single(<<IntType,IntType>>, IntType), [v \in Seq(ASTs) |-> Integer(v[1].val + v[2].val)], NoError)
  []   name = "-" -> BI(single(<<IntType,IntType>>, IntType), [v \in Seq(ASTs) |-> Integer(v[1].val - v[2].val)], NoError)
  []   name = "*" -> BI(single(<<IntType,IntType>>, IntType), [v \in Seq(ASTs) |-> Integer(v[1].val * v[2].val)], NoError)
  []   name = ">" -> BI(single(<<IntType,IntType>>, BoolType), [v \in Seq(ASTs) |-> Bool(v[1].val > v[2].val)], NoError)  
  []   name = "=" -> BI([v \in multi(2,LAMBDA tl : TRUE) |-> BoolType], [v \in Seq(ASTs) |-> Bool(v[1].type = v[2].type /\ v[1] = v[2])], NoError)
  []   name = "neg" -> BI(single(<<BoolType>>, BoolType), [v \in Seq(ASTs) |-> Bool(\neg v[1].val)], NoError)
  []   name = "build" -> BI([v \in multi(2, LAMBDA tl : tl[2] = ListType(tl[1])) |-> v[2]],      [v \in Seq(ASTs) |-> List(v[1].type, <<v[1]>> \o v[2].val)], NoError)
  []   name = "head"  -> BI([v \in multi(1, LAMBDA tl : tl[1].type = "list") |-> v[1].template], [v \in Seq(ASTs) |-> v[1].val[1]], [v \in Seq(ASTs) |-> v[1].val # <<>>])
  []   name = "tail"  -> BI([v \in multi(1, LAMBDA tl : tl[1].type = "list") |-> v[1]],          [v \in Seq(ASTs) |-> List(v[1].type.template, Tail(v[1].val))], [v \in Seq(ASTs) |-> v[1].val # <<>>])

(******************************************************************************)
(* Static Semantics / Well Formedness                                         *)
(* Structure, Variables, Types                                                *)
(******************************************************************************)

FV[ast \in ASTs] == 
  LET op   == ast.op
  IN  CASE op = "val"          -> {}
      []   op = "var"          -> {ast.id}
      []   op = "global var"   -> {ast.id}
      []   op = "cond"         -> FV[ast.cond] \cup FV[ast.then] \cup FV[ast.else]
      []   op = "tuple access" -> FV[ast.tuple]
      []   op = "fun call"     -> FV[ast.fun] \cup UNION {FV[sub] : sub \in ast.args}
      []   op = "builtin"      -> UNION {FV[sub] : sub \in ast.args}
      []   op = "list ctor"    -> UNION {FV[sub] : sub \in ast.args}
      []   op = "tuple ctor"   -> UNION {FV[sub] : sub \in ast.args}
      []   op = "fun ctor"     -> FV[ast.ast] \ TILids(ast.fargs)

Type[state \in SStates] == 
  LET ast  == state.ast
      op   == ast.op
      recType(sub_ast) == Type[State(state.genv, state.env, sub_ast)]
  IN  CASE op = "val"        -> ast.type
      []   op = "var"        -> state.env[ast.id]
      []   op = "global var" -> state.genv[ast.id]
      []   op = "cond"       -> recType(ast.then)
      []   op = "fun call"   -> recType(ast.fun).ret
      []   op = "builtin"    -> BuiltInList[ast.name].sigFun[Map(ast.args, recType)]
      []   op = "list ctor"  -> ListType(ast.type)
      []   op = "fun ctor"   -> FunType(TILtypes(ast.fargs), ast.ret)
      []   op = "tuple ctor" -> TupleType(Map(ast.args, recType))
      []   op = "tuple access" -> recType(ast.tuple).types[ast.idx]

W_val(genv, ast, W) == 
  LET val  == ast.val
      type == ast.type
      op   == type.type
      W_sub(sub) == W[State(genv,<<>>,sub)]
      funState == State(genv, MapMapF(val.fargs, type.args), val.ast)
      err(msg) == ~PrintMTAST(msg,ast)
  IN CASE op \in {"int","bool"} -> TRUE
     []   op = "list"  -> 
            \/ \A elem \in Range(val) : W_sub(elem) /\ elem.type = type.template
            \/ err("invalid sub type in list") 
     []   op = "tuple" -> 
            \/ \A idx \in DOMAIN val : W_sub(val[idx]) /\ val[idx].type = type.types[idx]
            \/ err("invalid sub type in tuple")
     []   op = "fun"   -> 
            /\ \/ DOMAIN type.args = DOMAIN val.fargs /\ IsBijective(val.fargs)
               \/ err("function arg error")
            /\ \/ W[funState] /\ type.ret = Type[funState]
               \/ err("function return type mismatch")

W_ast[state \in SStates] ==
  LET ast  == state.ast
      genv == state.genv
      env  == state.env
      op   == ast.op
      TsubEnv(senv,sub) == Type[State(genv,senv,sub)]
      Tsub(sub)         == TsubEnv(env,sub)
      WsubEnv(senv,sub) == W_ast[State(genv,senv,sub)]
      Wsub(sub)         == WsubEnv(env,sub)
      err(msg) == ~PrintMTAST(msg,ast)
      Wsubs(subs)       == \A sub \in subs : Wsub(sub) \/ err("error in sub ast")
      fun_ctor_env == ExtendBy(env, MapFromTIL(ast.fargs))
  IN  CASE op = "val"         -> W_val(genv, ast, W_ast)
      []   op = "var"         -> ast.id \in DOMAIN env  \/ err("missing var")
      []   op = "global var"  -> ast.id \in DOMAIN genv \/ err("missing global var")
      []   op = "cond" -> 
             /\ Wsubs({ast.cond, ast.then, ast.else})
             /\ Tsub(ast.cond).type = "bool"    \/ err("cond not boolean")
             /\ Tsub(ast.then) = Tsub(ast.else) \/ err("branches disagree on type")
      []   op = "fun call"   -> 
             /\ Wsub(ast.fun) /\ Wsubs(Range(ast.args)) 
             /\ Tsub(ast.fun).type = "fun"               \/ err("try to call non-fun")
             /\ Tsub(ast.fun).args = Map(ast.args, Tsub) \/ err("fun signature mismatch")
      []   op = "builtin"    -> 
             /\ Wsubs(Range(ast.args))
             /\ Map(ast.args, Tsub) \in DOMAIN BuiltInList[ast.name].sigFun \/ err("builtin signature mismatch")
      []   op = "list ctor"  -> 
             /\ \/ \A arg \in Range(ast.args) : Wsub(arg) /\ Tsub(arg) = ast.type  
                \/ err("element does not match list template")
      []   op = "fun ctor"   -> 
             /\ \/ IsBijective(TILids(ast.fargs)) /\ Range(TILids(ast.fargs)) \cap DOMAIN env = {} 
                \/ err("variable name already taken")
             /\ WsubEnv(fun_ctor_env, ast.ast) 
             /\ ast.ret = TsubEnv(fun_ctor_env, ast.ast) \/ err("fun ctor ret type mismatch")
      []   op = "tuple ctor" -> Wsubs(Range(ast.args))
      []   op = "tuple access" -> 
             /\ Wsub(ast.tuple) 
             /\ Tsub(ast.tuple).type = "tuple"           \/ err("tried to access non-tuple")
             /\ ast.idx \in DOMAIN Tsub(ast.tuple).types \/ err("tuple access out of bounds")
      []   OTHER -> err("unknown ast")
      
W(state) == 
  LET w(env, val) == W_ast[StateToStatic(State(state.genv, env, val))] IN
  /\ \A val \in Range(state.env)  : w(<<>>, val)
  /\ \A val \in Range(state.genv) : w(<<>>, val)
  /\ w(state.env, state.ast)

StatesFromStatic(sstate) == 
  { s \in States : StateToStatic(s) = sstate /\ W(StateToStatic(s)) }

StatesFromSEnv(genv, senv, ast) == 
  LET EnvEq(env) == Map(env, LAMBDA var : var.type) = senv
  IN  { s \in States : s.genv = genv /\ s.ast = ast /\ EnvEq(s.env) /\ W(StateToStatic(s)) }
      
(******************************************************************************)
(* semantics                                                                  *)
(******************************************************************************)

SubstituteVars[env \in Environments, ast \in ASTs] ==
  CASE ast.op = "var"      -> IF ast.id \in DOMAIN env THEN env[ast.id] ELSE ast
  []   ast.op = "fun ctor" -> 
         [ ast EXCEPT !.ast = SubstituteVars[RestrictBy(env, TILids(ast.fargs)), @] ] \* facilitates shadowing if needed
  []   OTHER -> MapSubNodes(ast, GetInfoAST(ast), LAMBDA sub : SubstituteVars[env, sub])

DynamicError(ast) == 
  /\ ast.op = "builtin" /\ ~BuiltInList[ast.name].errFun[ast.args] 
  /\ PrintMTAST("invalid built in", ast)
  
DefSOS(SOS,state) ==
LET env  == state.env
    genv == state.genv
    ast  == state.ast
    except(sub) == [state EXCEPT !.ast = sub]
    SOSr(sub) == SOS[except(sub)].ast
    AdvanceCond(sub) == sub.op # "val"
    AdvanceOp(sub, newAST) ==
      IF sub = Error /\ PrintMTAST("trace", ast) THEN Error
      ELSE newAST[SOSr(sub)]
    Advance == TransformFirstSubNode(ast, FilterNonLazyAttributes(ast), AdvanceCond, AdvanceOp, ASTs)
IN  IF Advance # ast THEN except(Advance)
    ELSE IF DynamicError(ast) THEN except(Error) 
    ELSE 
      CASE ast.op = "val"          -> except(ast)
      []   ast.op = "var"          -> except(env[ast.id])
      []   ast.op = "global var"   -> except(genv[ast.id])
      []   ast.op = "cond"         -> except(IF ast.cond.val THEN ast.then ELSE ast.else)
      []   ast.op = "fun call"     -> except(SubstituteVars[MapMapF(ast.fun.val.fargs, ast.args), ast.fun.val.ast])
      []   ast.op = "builtin"      -> except(BuiltInList[ast.name].valFun[ast.args]) 
      []   ast.op = "list ctor"    -> except(List(ast.type,ast.args)) 
      []   ast.op = "tuple ctor"   -> except(Tuple(Map(ast.args, LAMBDA arg : arg.type),ast.args))
      []   ast.op = "fun ctor"     -> except(Fun(ast.fargs, ast.ret, SubstituteVars[env, ast.ast]))
      []   ast.op = "tuple access" -> except(ast.tuple.val[ast.idx])
      []   ast.op = "error"        -> except(ast)
SOS[state \in States] == DefSOS(SOS,state)

=============================================================================
