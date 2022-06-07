----------------------------- MODULE ListNatExpTLC -----------------------------
EXTENDS ListNatExp, ListNatExpAux, UtilDebug

(******************************************************************************)
(* TLC                                                                        *)
(******************************************************************************)

\* Tip: comment out all constants you don't need.

RECURSIVE ASTString(_)
ASTString(ast) == 
  LET s(a) == ASTString(a)
      csl(a) == TemplateSL(s,a,", ")
  IN  CASE ast.op = "Cond" -> "if " \o s(ast.cond) \o " then " \o s(ast.then) \o " else " \o s(ast.else)
      []   ast.op \in {"BuiltIn", "FunCall"} -> ast.name \o "(" \o csl(ast.args) \o ")"
      []   ast.op \in {"List", "ListCtor"}   -> "[" \o csl(ast[IF ast.op = "List" THEN "val" ELSE "args"]) \o "]"
      []   ast.op = "Nat" -> ToString(ast.val)
      []   ast.op = "Bool" -> ToString(ast.val)
      []   ast.op = "Var" -> ast.id
      []   ast.op = "Error" -> "ERROR"
      []   OTHER -> ToString(ast)
      
RECURSIVE EvalSOS(_)
EvalSOS(state) == 
  IF SOS[state] = state THEN state ELSE EvalSOS(SOS[state])
      
I_(in) == I_internal[1000000][in]
      
PrintMTAST_(msg,in) == 
  LET ast == IF "op" \in DOMAIN in THEN in ELSE in.ast 
      message == IF msg = "" THEN "" ELSE msg \o ": "
  IN  PrintT(message \o ASTString(ast)) 

PrintS(msg,val) == IF PrintT(msg) THEN val ELSE val

Seq_(S) == UNION { SeqN(S,n) : n \in 0..3 }
RecDef_(s0,next(_,_)) == UNION { RecF(s0,next)[n] : n \in 0..2 }
Bools_     == {Bool(b) : b \in {}}
Naturals_  == {Natural(n) : n \in 0..0}
NextList_(p,n) == p \cup { List(v) : v \in Seq_(p \cup {Natural(m) : m \in 0..0}) }
Lists_ == RecDef_(BaseList,NextList_)

NatsO_ == {Natural(n) : n \in 0..30}

\*Tautology == \A state \in states : I(state) = Bool(TRUE)


VARIABLES conf
Init == conf = State(funEnv, varEnvs[2], asts.a7)
Next == conf # SOS[conf] /\ conf' = SOS[conf] /\ PrintTAST(conf.ast)

\*Equality == conf # SOS[conf] \/ PrintS("I:   ", PrintAST(I(initConf))) = PrintS("SOS: ", PrintAST(conf.ast))
\*Truthy   == conf \notin Bools \/ PrintAST(conf.ast) = Bool(TRUE)
=============================================================================