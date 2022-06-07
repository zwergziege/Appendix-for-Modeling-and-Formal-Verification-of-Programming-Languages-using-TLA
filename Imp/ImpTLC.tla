----------------------------- MODULE ImpTLC -----------------------------
EXTENDS Imp

(******************************************************************************)
(* TLC                                                                        *)
(******************************************************************************)

RECURSIVE TypeString(_)
TypeString(type) == 
  LET s(a) == TypeString(a)
      sl(a,sep) == TemplateSL(s,a,sep)
  IN  CASE type.type \in {"int", "bool", "void"} -> type.type
      []   type.type = "ref" -> "§" \o s(type.template)
      []   type.type = "struct" -> type.name
      []   type.type = "vector" -> "vec" \o square(s(type.template))
      []   OTHER -> ToString(type)
  
RECURSIVE ValueString(_)
ValueString(val) == 
  LET s(a) == ValueString(a)
      sl(a,sep) == TemplateSL(s,a,sep)
      type == val.type.type
  IN  CASE type \in {"int", "bool"} -> ToString(val.val)
      []   type = "ref" -> "§" \o ToString(val.val) 
      []   type = "struct" -> val.type.name \o brac(sl(val.val,", "))
      []   type = "vector" -> square(sl(val.val,", "))
      []   type = "void" -> "void"
      []   OTHER -> ToString(val)

RECURSIVE ASTString(_)
ASTString(ast) == 
  LET s(a) == ASTString(a)
      sl(a,sep) == TemplateSL(s,a,sep)
  IN  CASE ast.op = "val" -> ValueString(ast)
      []   ast.op = "cond" -> "if " \o s(ast.cond) \o " then " \o s(ast.then) \o " else " \o s(ast.else)
      []   ast.op \in {"builtin", "fun call"} -> ast.name \o brac(sl(ast.args,", "))
      []   ast.op = "vector ctor"   -> square(sl(ast.args,", "))
      []   ast.op = "struct ctor"   -> ast.name \o brac(sl(ast.args,", "))
      []   ast.op = "var ctor" -> brac("var " \o ast.id \o " := " \o s(ast.val))
      []   ast.op = "var access" -> ast.id
      []   ast.op = "struct access" -> s(ast.struct) \o "." \o ast.field
      []   ast.op = "vector access" -> s(ast.vec) \o square(s(ast.idx))
      []   ast.op = "vector insert" -> s(ast.vec) \o ".insert" \o brac(s(ast.idx) \o ", " \o s(ast.val))
      []   ast.op = "vector delete" -> s(ast.vec) \o ".delete" \o brac(s(ast.idx))
      []   ast.op = "assign"        -> brac(s(ast.ref) \o " <- " \o s(ast.val))
      []   ast.op = "struct assign" -> s(ast.struct) \o "." \o ast.field \o " := " \o s(ast.val)
      []   ast.op = "vector assign" -> s(ast.vec) \o "[" \o s(ast.idx) \o "] := " \o s(ast.val)
      []   ast.op = "var assign"    -> ast.id \o " := " \o s(ast.val)
      []   ast.op = "while" -> "while " \o s(ast.cond) \o " do " \o s(ast.body)
      []   ast.op = "block" -> sl(ast.args,"; ")
      []   ast.op = "scope" -> curly(s(ast.val))
      []   ast.op = "return" -> "return" \o square(ToString(ast.target)) \o " " \o s(ast.val)
      []   ast.op = "error" -> "ERROR"
      []   OTHER -> ToString(ast)

TypeIDPairString(tidp) == tidp.id \o " : " \o TypeString(tidp.type)
TILString(til) == TemplateSL(TypeIDPairString, til, ", ")

PrintTFunEnv(env) == 
  /\ PrintTI("functions:") /\ IncIndent
  /\ \A name \in DOMAIN env : PrintTI(name \o brac(TILString(env[name].args)) \o " : " \o TypeString(env[name].ret) \o " = " \o ASTString(env[name].body))
  /\ DecIndent

PrintTStructTable(env) == 
  /\ PrintTI("structs:") /\ IncIndent
  /\ \A name \in DOMAIN env : PrintTI(name \o square(TILString(env[name])))
  /\ DecIndent
  
PrintTStore(env) ==
  /\ PrintTI("storage:") /\ IncIndent
  /\ \A idx \in DOMAIN env : PrintTI("§" \o ToString(idx) \o " #" \o ToString(env[idx].cnt) \o " : " \o ValueString(env[idx].val))
  /\ DecIndent
  
PrintTStack(stack) == 
  /\ PrintTI("stack: ") /\ IncIndent
  /\ \A idx \in DOMAIN stack :
    /\ PrintTI(ToString(idx) \o " (" \o stack[idx].scopeType \o ") :") /\ IncIndent
    /\ \A id \in DOMAIN stack[idx].env : PrintTI(id \o " : " \o ValueString(stack[idx].env[id]))
    /\ DecIndent
  /\ DecIndent
  
PrintTState(state) == 
  /\ PrintTI("state:") /\ IncIndent
  /\ PrintTI("ast: " \o ASTString(state.ast))
  /\ PrintTStore(state.store)
  /\ PrintTStack(state.stack)
  /\ PrintTStructTable(state.structTable)
  /\ PrintTFunEnv(state.funTable)
  /\ DecIndent
  
PrintTStaticStack(stack) == 
  /\ PrintTI("static stack:") /\ IncIndent
  /\ \A idx \in DOMAIN stack : 
     /\ PrintTI(ToString(idx) \o " (" \o stack[idx].scopeType \o ") : " \o TypeString(stack[idx].targetType)) /\ IncIndent
     /\ \A id \in DOMAIN stack[idx].env : PrintTI(id \o " : " \o TypeString(stack[idx].env[id]))
     /\ DecIndent
  /\ DecIndent

PrintTStaticState(state) == 
  /\ PrintTI("static state:") /\ IncIndent
  /\ PrintTI("ast: " \o ASTString(state.ast))
  /\ PrintTStaticStack(state.stack)
  /\ PrintTStructTable(state.structTable)
  /\ PrintTFunEnv(state.funTable)
  /\ DecIndent
  
PrintStaticError_(msg, state) == PrintTI(msg) /\ PrintTStaticState(state)
PrintDynamicError_(msg, state) == PrintTI(msg) /\ PrintTState(state)

ids == Any \*STRING

RECURSIVE EvalSOS(_)
EvalSOS(state) == 
  IF PrintDynamicError_("current eval:", state) 
  THEN IF SOS[state] = state THEN state ELSE EvalSOS(SOS[state]) 
  ELSE FALSE

asts == 
LET f == [args \in Any |-> FunCall(Head(args),Tail(args))] 
    b == [args \in Any |-> BuiltIn(Head(args),Tail(args))]
    v == [name \in Any |-> VarAccess(name) ]
    vec    == [args \in Any |-> VectorCtor(Head(args),Tail(args))]
    struct == [args \in Any |-> StructCtor(Head(args),Tail(args))]
    i == [arg \in Any |-> Integer(arg)]
    sl == [args \in Any |-> Block(args)]
    
    x123 == VarCtor("x",vec[IntType, i[1], i[2], i[3]])
    p34  == VarCtor("p", struct["point",i[3],i[4]])
    
    cond  ^+ == IfThen(b["~",cond], Return(Bool(FALSE),1))
    tests ^# == NewScope(BoolType, sl[tests \o <<Bool(TRUE)>>])
    
IN
[
  a |-> i[10],
  b |-> NewScope(IntType, f["sum", VarCtor("x",i[3])]),
  sum |-> Cond(b["=", b["#", v["n"]], i[1]], i[1], b["+", v["n"], f["sum", b["-", v["n"], i[1]]]]),
  StorageTest |-> NewScope(VectorType(IntType), VarCtor("x", vec[IntType, i[1], VarCtor("y", i[2]), v["y"], b["@",v["y"]]])),
  AssignRefTest |-> NewScope(IntType, sl[
    x123, 
    VarCtor("a", VectorAccess(v["x"],i[2])), 
    VarCtor("y", vec[IntType, v["a"]]),
    Assign(VectorAccess(v["y"], i[1]), b["+", VectorAccess(v["y"], i[1]), i[2]]),
    Assign(v["x"],v["y"]),
    VectorAccess(v["y"], i[1])
  ]),
  WhileTest |-> NewScope(NoType, sl[x123, While(b["~", b["=", i[0], b["length", v["x"]]]], VectorDelete(v["x"], i[1])), i[3]]),
  fun |-> sl[f[<<"fun">>], sl[<<>>]],
  dotprod |-> b["+", b["*", StructAccess(v["a"], "x"), StructAccess(v["b"], "x")], b["*", StructAccess(v["a"], "y"), StructAccess(v["b"], "y")]],
  StructTest |-> NewScope(StructType("point"), sl[p34, Assign(StructAccess(v["p"],"x"), i[1]), v["P"]]),
  dotp |-> NewScope(IntType, sl[p34, f["dotprod", v["p"], v["p"]]]),
  modify |-> Assign(v["a"],b["+",v["a"],i[1]]),
  modifyTest |-> <<
    x123,
    f["modify", VectorAccess(v["x"],i[1])],
    b["=", b["#",v["x"]], vec[IntType, i[2], i[2], i[3]]] ^+
  >> ^#,
  AssignCompoundTest |-> <<
    x123,p34,
    \*b["=", AssignStruct(b["@",v["p"]], "y", i[5]), struct["point",StructAccess(v["p"],"x"),i[5]]] ^+,
    b["=", b["@",StructAccess(v["p"],"y")], i[4]] ^+,
    AssignStruct(v["p"], "y", i[5]),
    b["~", b["=", StructAccess(v["p"], "y"), i[5]]] ^+,
    b["=", b["@", StructAccess(v["p"], "y")], i[5]] ^+,
    AssignVec(v["x"], VarCtor("idx", StructAccess(v["p"], "x")), v["idx"]),
    b["=", VectorAccess(v["x"], v["idx"]), v["idx"]] ^+,
    b["=", VarCtor("y", vec[IntType,i[10]]), AssignVar("x",v["y"])] ^+,
    AssignVar("y", vec[IntType,i[20]]),
    b["=", b["#",v["y"]], vec[IntType,i[20]]] ^+,
    b["~", b["=", VarCtor("z", vec[IntType,i[10]]), AssignVar("z",v["y"])]] ^+    \* this creates dangling refs -.-
  >> ^#,
  BugTest |-> <<
    VarCtor("x", vec[IntType, i[0]]),
    b["=", b["+", VectorAccess(v["x"],i[1]), VectorAccess(Assign(v["x"], vec[IntType, i[1]]), i[1])], i[1]] ^+
  >> ^#,
  ScopeTest |-> <<
    VarCtor("x", i[1]),
    VarCtor("y", i[2]),
    NewScope(NoType, AssignVar("x",v["y"])),
    b["=",v["x"],v["y"]] ^+,
    b["=",i[1],NewScope(IntType, NewScope(IntType, Return(Cond(Bool(FALSE), Return(i[2],2), i[1]), 1)))] ^+,
    b["=",i[2],NewScope(IntType, NewScope(IntType, Return(Cond(Bool(TRUE), Return(i[2],2), i[1]), 1)))] ^+,
    b["=",b["#", NewScope(IntType, VarCtor("z",i[3]))],i[3]] ^+
  >> ^#,
  ErrorTest |-> NewScope(NoType, Block(<<x123,VectorAccess(v["x"],i[4])>>))
]

FunctionTable == 
LET formal(type,id) == TypeIDPair(type,id) IN 
[
  modify |-> Function(<<formal(IntType,"a")>>, NoType, asts.modify),
  fun |-> Function(<<>>, NoType, asts.a),
  sum |-> Function(<<formal(IntType, "n")>>, IntType, asts.sum),
  dotprod |-> Function(<<formal(StructType("point"), "a"),formal(StructType("point"),"b")>>, IntType, asts.dotprod)
]

StructTable == 
LET formal(type,id) == TypeIDPair(type,id) IN
[
  empty |-> <<>>,
  point |-> <<formal(IntType,"x"), formal(IntType,"y")>>
]

EvalASTwithSOS(ast) == 
  IF /\ StaticCheck(StructTable, FunctionTable, ast) 
     /\ PrintT("------------------------------------------------")
  THEN EvalSOS(InitialState(StructTable, FunctionTable, ast)) 
  ELSE Error

ast == asts.ErrorTest

VARIABLE state
Init == /\ PrintT("---") 
        /\ state \in IF StaticCheck(StructTable, FunctionTable, ast) THEN {InitialState(StructTable, FunctionTable, ast)} ELSE {}
Next == state' = SOS[state] /\ PrintDynamicError("current eval: ", state') /\ state # state'

=============================================================================