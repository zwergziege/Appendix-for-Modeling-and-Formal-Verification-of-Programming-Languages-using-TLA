----------------------------- MODULE ListNatExp -----------------------------
EXTENDS Integers, FiniteSets, Sequences, Util

CONSTANT IDs

PrintMTAST(msg,ast) == TRUE
PrintMAST(msg,ast) == IF PrintMTAST(msg,ast) THEN ast ELSE ast
PrintTAST(ast) == PrintMTAST("",ast)
PrintAST(ast) == PrintMAST("",ast)

(******************************************************************************)
(* list of types                                                              *)
(******************************************************************************)

Types == {"Nat", "List", "Bool"}

\* Value is a hack. 
\* should be [ arg \in {"op",type} |-> IF arg = type THEN val ELSE type ]
\* access: val[val.type]
Value(type, val)  == [ op |-> type, val |-> val ] \*[ arg \in {"op","val",type} |-> IF arg = "val" THEN val ELSE type ]
Natural(n)        == Value("Nat",n)
List(l)           == Value("List",l)
Bool(b)           == Value("Bool",b)

(* definition *)

Naturals    == { Natural(n) : n \in Nat }
Bools       == { Bool(b) : b \in BOOLEAN }

BaseList      == { List(<<>>) }
NextList(p,n) == p \cup { List(v) : v \in Seq(p \cup Naturals \cup Bools) }
Lists         == RecDef(BaseList, NextList)

Values    == Naturals \cup Lists \cup Bools

(******************************************************************************)
(* list of language constructs                                                *)
(******************************************************************************)

Tags == {"Cond", "FunCall", "BuiltIn", "ListCtor", "Var", "Error"} \cup Types
  
BuiltInNames == { "+", "-", "*", ">", "~", "=", "build", "head", "tail" }

Var(id)                == [ op |-> "Var" , id |-> id ]
Cond(cond, then, else) == [ op |-> "Cond", cond |-> cond, then |-> then, else |-> else ]
FunCall(name, args)    == [ op |-> "FunCall" , name |-> name, args |-> args ]
BuiltIn(name, args)    == [ op |-> "BuiltIn" , name |-> name, args |-> args ]
ListCtor(args)         == [ op |-> "ListCtor", args |-> args ]

Error                  == [ op |-> "Error" ]

And(a, b) == Cond(a, b, Bool(FALSE))
Or(a, b)  == Cond(a, Bool(TRUE), b)

Vars         == [ op : {"Var"}, id : IDs ]
Conds(p)     == [ op : {"Cond"}, cond : p, then : p, else : p ]
FunCalls(p)  == [ op : {"FunCall"}, name : IDs, args : Seq(p) ]
BuiltIns(p)  == [ op : {"BuiltIn"}, name : BuiltInNames, args : Seq(p) ]
ListCtors(p) == [ op : {"ListCtor"}, args : Seq(p) ]

GetInfoAST(ast) == 
  LET op == ast.op
      Info(name, isList, isLazy) == [ name |-> name, isList |-> isList, isLazy |-> isLazy ] 
      IList(name) == Info(name,TRUE,FALSE)
      ILazy(name) == Info(name,FALSE,TRUE)
      I(name)     == Info(name,FALSE,FALSE)
  IN  CASE op = "Var"      -> <<>>
      []   op \in Types    -> <<>>
      []   op = "Cond"     -> <<I("cond"),ILazy("then"),ILazy("else")>>
      []   op = "FunCall"  -> <<IList("args")>>
      []   op = "BuiltIn"  -> <<IList("args")>>
      []   op = "ListCtor" -> <<IList("args")>>

(* ASTs & states *)

BaseAST      == Bools \cup Naturals \cup Lists \cup Vars \cup {Error}
NextAST(p,n) == p \cup (Conds(p) \cup FunCalls(p) \cup BuiltIns(p) \cup ListCtors(p))
ASTs == RecDef(BaseAST, NextAST)

Function(args, ast) == [ args |-> args, ast |-> ast ]
Functions           == [ args : Seq(IDs), ast : ASTs ]

FunctionMaps == PartialFunctions(IDs, Functions)
VariableMaps == PartialFunctions(IDs, Values)

State(funs,vars,ast) == [funEnv |-> funs, varEnv |-> vars, ast |-> ast]
States == [ funEnv : FunctionMaps, varEnv : VariableMaps, ast : ASTs ]

(******************************************************************************)
(* definitions of builtins                                                    *)
(******************************************************************************)

BuiltInSig(name) == 
  CASE name = "+"     -> <<{"Nat"},{"Nat"}>>
  []   name = "-"     -> <<{"Nat"},{"Nat"}>>
  []   name = "*"     -> <<{"Nat"},{"Nat"}>>
  []   name = ">"     -> <<{"Nat"},{"Nat"}>>
  []   name = "~"     -> <<{"Bool"}>>
  []   name = "="     -> <<Types,Types>>
  []   name = "build" -> <<Types,{"List"}>>
  []   name = "head"  -> <<{"List"}>>
  []   name = "tail"  -> <<{"List"}>>

BuiltInError(ast) == 
  LET name == ast.name 
      args == ast.args
  IN  \/ /\ \E idx \in DOMAIN args : args[idx].op \notin BuiltInSig(name)[idx]
         /\ PrintMTAST("invalid builtin argument types", ast)
      \/ /\ name = "-" /\ args[1].val - args[2].val < 0 
         /\ PrintMTAST("invalid subtraction", ast)
  
BuiltInStep(ast) == 
  LET name == ast.name
      args == ast.args
  IN CASE name = "+" -> Natural(args[1].val + args[2].val)
     []   name = "-" -> Natural(args[1].val - args[2].val)
     []   name = "*" -> Natural(args[1].val * args[2].val)
     []   name = "=" -> Bool(args[1].op = args[2].op /\ args[1].val = args[2].val)
     []   name = ">" -> Bool(args[1].val > args[2].val)
     []   name = "~" -> Bool(~args[1].val)
     []   name = "build" -> List(<<args[1]>> \o args[2].val)
     []   name = "head" -> IF args[1].val = <<>> THEN args[1] ELSE      Head(args[1].val)
     []   name = "tail" -> IF args[1].val = <<>> THEN args[1] ELSE List(Tail(args[1].val))

(******************************************************************************)
(* static semantics                                                           *)
(******************************************************************************)

\* not much except for checking number of args and existence of identifiers
\* static typing is impossible (untyped lists are evil)

\* check all relevant sub asts
Wsub(w, ast) == 
  CASE ast.op \in {"FunCall", "BuiltIn", "ListCtor"} -> \A arg \in Range(ast.args) : w[arg]
  []   ast.op = "Cond" -> \A sub_ast \in {ast.cond, ast.then, ast.else} : w[sub_ast]
  []   OTHER -> TRUE
  
DefW(funs, vars, ast, w) ==
  LET err(msg) == ~PrintMTAST(msg,ast)
  IN  Wsub(w, ast) /\
      \/ /\ ast.op = "FunCall"  
         /\ ast.name \in DOMAIN funs                 \/ err("unknown function")
         /\ Len(funs[ast.name].args) = Len(ast.args) \/ err("invalid arity")
      \/ /\ ast.op = "BuiltIn"   
         /\ Len(BuiltInSig(ast.name)) = Len(ast.args) \/ err("builtin arity mismatch")
      \/ ast.op = "ListCtor" 
      \/ ast.op = "Cond"      
      \/ /\ ast.op = "Var"       
         /\ ast.id \in vars \/ err("unknown argument")
      \/ ast.op \in Types

W_ast(funs, vars) == LET w[ast \in ASTs] == DefW(funs,vars,ast,w) IN  w

W_funEnv(funEnv) == 
  \A fun \in Range(funEnv) : 
     /\ W_ast(funEnv, Range(fun.args))[fun.ast]
     /\ IsBijective(fun.args) \/ ~PrintMTAST("fun with duplicate arguments: " \o ToString(fun.args), fun.ast)

W(state) == 
  /\ state \in States
  /\ W_funEnv(state.funEnv)
  /\ W_ast(state.funEnv, DOMAIN state.varEnv)[state.ast]
  
(******************************************************************************)
(* semantics                                                                  *)
(******************************************************************************)

SubstituteVars(vars, AST) == 
  LET sub[ast \in ASTs] == 
        CASE ast.op \in {"BuiltIn","FunCall","ListCtor"} -> [ast EXCEPT !.args = [i \in DOMAIN @ |-> sub[@[i]]]]
        []   ast.op = "Cond"    -> [ast EXCEPT !.cond = sub[@], !.then = sub[@], !.else = sub[@]]
        []   ast.op = "Var"     -> vars[ast.id]
        []   OTHER -> ast
  IN sub[AST]
  
DynamicError(ast) == 
  LET pError(msg) == PrintMTAST(msg, ast)
  IN  \/ /\ ast.op \in {"BuiltIn", "ListCtor", "FunCall"} 
         /\ \/ Error \in Range(ast.args) /\ pError("trace")
            \/ \E arg \in Range(ast.args) : arg \notin ASTs \/ arg.op \notin Types
      \/ ast.op = "BuiltIn" /\ BuiltInError(ast) 
      \/ ast.op = "Cond" /\ \/ ast.cond = Error     /\ pError("trace")
                            \/ ast.cond.op # "Bool" /\ pError("condition is not boolean")
      
DefSOS(SOS,state) == 
LET ast == state.ast
    SOSr(sub) == SOS[[state EXCEPT !.ast = sub]].ast
    NeedEval(sub) == sub.op \notin (Types \cup {"Error"})
    FunStep(fun) == SubstituteVars(MapMapF(fun.args, ast.args), fun.ast) 
    a !! b == [a EXCEPT !.ast = b]
IN  state !!
    CASE /\ ast.op \in {"BuiltIn","FunCall","ListCtor"}
         /\ \E idx \in DOMAIN ast.args : NeedEval(ast.args[idx])
         -> [ast EXCEPT !.args[LowestIdx(ast.args, NeedEval)] = SOSr(@)]
    []   /\ ast.op = "Cond" /\ NeedEval(ast.cond) 
         -> [ast EXCEPT !.cond = SOSr(@)]
    []   OTHER -> 
    IF DynamicError(state.ast) THEN Error ELSE
    CASE ast.op = "BuiltIn"   -> BuiltInStep(ast)
    []   ast.op = "FunCall"  -> FunStep(state.funEnv[ast.name])
    []   ast.op = "ListCtor" -> List(ast.args)
    []   ast.op = "Cond"      -> IF ast.cond.val THEN ast.then ELSE ast.else
    []   ast.op = "Var"       -> state.varEnv[ast.id]
    []   ast.op \in Types \cup {"Error"} -> ast
SOS[state \in States] == DefSOS(SOS,state)

\* evaluates all relevant sub asts using the given interpretation function I

ISub(I, state) ==
  LET ast == state.ast
      I_ast(sub) == I[[state EXCEPT !.ast = sub]]
  IN  CASE ast.op \in {"FunCall", "BuiltIn", "ListCtor"} -> [ast EXCEPT !.args = Map(ast.args, I_ast)]
      []   ast.op = "Cond"                               -> [ast EXCEPT !.cond = I_ast(ast.cond)]
      []   OTHER -> ast
      
DefI(I, state) == 
  LET funs == state.funEnv
      vars == state.varEnv
      ast  == state.ast
      I_ast(sub) == I[[state EXCEPT !.ast = sub]]
      nAST  == ISub(I, state)
  IN  IF \/ \neg W(state) /\ PrintMTAST("malformed", state.ast)
         \/ DynamicError(nAST)
      THEN Error ELSE
      CASE ast.op = "FunCall"   -> I[State(funs, MapMapF(funs[ast.name].args, nAST.args), funs[ast.name].ast)]
      []   ast.op = "BuiltIn"   -> BuiltInStep(nAST)
      []   ast.op = "ListCtor"  -> List(nAST.args)
      []   ast.op = "Cond"      -> IF nAST.cond.val THEN I_ast(ast.then) ELSE I_ast(ast.else)
      []   ast.op = "Var"       -> vars[ast.id]
      []   ast.op \in Types \cup {"Error"} -> ast
      
Denotational == INSTANCE UtilDeno
      
I_internal[n \in Nat] == 
  [state \in States |-> IF n = 0 THEN Error ELSE DefI(I_internal[n-1], state)]

I(in) == 
  ChooseIfExists({I_internal[n][in] : n \in Nat}, LAMBDA res : res # Error, Error)
  
=============================================================================
