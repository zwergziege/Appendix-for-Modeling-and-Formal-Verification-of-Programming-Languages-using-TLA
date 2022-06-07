----------------------------- MODULE AExpTLC -----------------------------
EXTENDS AExp

(******************************************************************************)
(* TLC                                                                        *)
(******************************************************************************)

RECURSIVE TypeString(_)
TypeString(type) == 
  LET ts(a)  == TypeString(a)
      csl(a) == TemplateSL(ts,a,", ") 
      t      == type.type
  IN CASE t \in {"int", "bool"} -> t
     []   t = "fun" -> ts(type.ret) \o "(" \o csl(type.args) \o ")"
     []   t = "list" -> "List[" \o ts(type.template) \o "]"
     []   t = "tuple" -> "Tuple[" \o csl(type.args) \o "]"

RECURSIVE ASTString_(_)
ASTString_(ast) == 
  LET s(a) == ASTString_(a)
      csl(a) == TemplateSL(s,a,", ")
  IN  CASE ast.op = "cond" -> "if " \o s(ast.cond) \o " then " \o s(ast.then) \o " else " \o s(ast.else)
      []   ast.op = "builtin" -> ast.name \o "(" \o csl(ast.args) \o ")"
      []   ast.op = "fun call" -> s(ast.fun) \o "(" \o csl(ast.args) \o ")"
      []   ast.op = "list ctor" -> "[" \o csl(ast.args) \o "]"
      []   ast.op = "fun ctor" -> "(" \o TemplateSL(LAMBDA farg : farg.id \o " : " \o TypeString(farg.type), ast.fargs, ", ") \o ")"
                    \o " -> " \o TypeString(ast.ret) \o " : " \o s(ast.ast)
      []   ast.op = "tuple ctor" -> "(" \o csl(ast.args) \o ")"
      []   ast.op = "tuple access" -> s(ast.tuple) \o "[" \o ToString(ast.idx) \o "]"
      []   ast.op = "global var" -> "@" \o ast.id
      []   ast.op = "var" -> ast.id
      []   ast.op = "val" ->
           CASE ast.type.type = "int"   -> ToString(ast.val)
           []   ast.type.type = "bool"  -> ToString(ast.val)
           []   ast.type.type = "fun"   -> "(" \o TemplateSL(LAMBDA farg : farg, ast.val.fargs, ", ") \o ") -> " \o s(ast.val.ast)
           []   ast.type.type = "tuple" -> "(" \o csl(ast.val) \o ")"
           []   ast.type.type = "list"  -> "[" \o csl(ast.val) \o "]"
           []   OTHER -> "Error: invalid value"
      []   ast.op = "error" -> "Error"
      []   OTHER -> "ast with unknown op: " \o ToString(ast)

PrintAST(in) == LET ast == IF "op" \in DOMAIN in THEN in ELSE in.ast IN
  IF PrintT(ASTString(ast)) THEN in ELSE FALSE
PrintMTAST_(msg, ast) == PrintTI(msg \o ": " \o ASTString(ast))
PrintS(msg,val) == IF PrintT(msg) THEN val ELSE val

ids == {"a","b","c","d","l","cumsum"}

EvalSOS[s \in Any] == IF s = SOS[s] THEN s ELSE EvalSOS[SOS[s]]

asts ==  
  LET plus(a,b)  == BuiltIn("+",<<a,b>>)
      minus(a,b) == BuiltIn("-",<<a,b>>)
      mult(a,b)  == BuiltIn("*",<<a,b>>)
      equal(a,b) == BuiltIn("=",<<a,b>>)
      great(a,b) == BuiltIn(">",<<a,b>>)
      build(a,b) == BuiltIn("build",<<a,b>>)
      head(a)   == BuiltIn("head",<<a>>)
      tail(a)    == BuiltIn("tail",<<a>>)
      
      tip(type,id) == TypeIDPair(type, id)
      
      lhs && rhs == Cond(~lhs, Bool(FALSE), rhs)
      lhs || rhs == Cond( lhs, Bool( TRUE), rhs)
      
      b  == [ b \in BOOLEAN |-> Bool(b) ]
      n  == [ n \in Int |-> Integer(n) ]
      
      v  == [ id \in ids |-> Var(id) ]
      g  == [ id \in ids |-> GVar(id) ]
      fc(til, ret, ast) == FunCtor(til,ret,ast)
      lc(type)          == [ args \in Any |-> ListCtor(type,args) ]
      tc                == [ args \in Any |-> TupleCtor(args) ]
      fa(ast)     == [ args \in Any |-> FunCall(ast, args) ]
      ta(ast,idx) == TupleAccess(ast,idx)
  IN  
  [
    cumsum |-> 
      Cond(equal(tail(v.l), lc(IntType)[<<>>]),
        v.l,
        build(head(v.l), fa(g.cumsum)[<<build(plus(head(v.l),head(tail(v.l))), tail(tail(v.l)))>>])
      ),
    cumsum_call |-> fa(g.cumsum)[<<g.l>>],
    a |-> build(head(v.l),v.l),
    b |-> fa(ta(tc[fc(<<tip(IntType,"a")>>,IntType,v.a),Integer(5)],1))[<<Integer(2)>>]
  ] 
environments == <<
   [ 
     l |-> List(IntType, [i \in {1,2,3} |-> Integer(i)]), 
     cumsum |-> Fun(<<TypeIDPair(ListType(IntType),"l")>>, ListType(IntType), asts.cumsum)
   ]
>>
state == State(environments[1], environments[1], asts.b)

VARIABLE conf
WellFormed == W(conf)
Init == conf = state
Next == conf # SOS[conf] /\ conf' = PrintAST(SOS[conf])
=============================================================================