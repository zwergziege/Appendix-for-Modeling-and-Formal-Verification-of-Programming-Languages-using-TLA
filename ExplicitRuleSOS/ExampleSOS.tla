-------------------------- MODULE ExampleSOS --------------------------

EXTENDS TLC, Sequences, Integers, Functions, Util

Configurations == Any
C == Configurations

Integer(i)    == [ op |-> "int", val |-> i ]
Bool(b)       == [ op |-> "bool", val |-> b ]
BinOp(op,a,b) == [ op |-> "op", name |-> op, a |-> a, b |-> b ]
Cond(i,t,e)   == [ op |-> "cond", cond |-> i, then |-> t, else |-> e ]
Env(e, ast)   == [ op |-> "env", env |-> e, ast |-> ast ]
Var(name)     == [ op |-> "var", name |-> name ]
FunCall(name, args) == [ op |-> "fun", name |-> name, args |-> args ]

State(funs,vars,ast) == [funs |-> funs, vars |-> vars, ast |-> ast]
Fun(args,body) == [args |-> args, body |-> body]

Rule(in, pts, p, out) == [InPattern |-> in, PremiseTransforms |-> pts, Premise |-> p, OutTransform |-> out]

Rules == 
LET CMap(map(_)) == [c \in C |-> map(c)]
    CMapExceptAST(map(_)) == CMap(LAMBDA c : [c EXCEPT !.ast = map(c)])
    CMapSub(name) == CMapExceptAST(LAMBDA c : c.ast[name])
    PT(vec) == CMap(LAMBDA c : Map(vec, LAMBDA elem : [c EXCEPT !.ast = elem])) 
    PTfromNames(names) == CMap(LAMBDA c : Map(names, LAMBDA name : [c EXCEPT !.ast = c.ast[name]])) 
    PremMap(map(_,_)) == [ c \in C, cc \in Seq(C) |-> map(c,cc)]
    PremMapTrue == PremMap(LAMBDA c,cc: TRUE)
    PremMapExceptAST(map(_,_)) == PremMap(LAMBDA c, cc : [c EXCEPT !.ast = map(c,cc)])
    PremMapSub(name) == PremMap(LAMBDA c, prem: [c EXCEPT !.ast[name] = prem[1].ast])
    BinOpR(c,prem) == 
      CASE c.ast.name = "+" -> Integer(c.ast.a.val + c.ast.b.val)
      []   c.ast.name = "*" -> Integer(c.ast.a.val * c.ast.b.val)
      []   c.ast.name = "-" -> Integer(c.ast.a.val - c.ast.b.val)
      []   c.ast.name = "=" -> Bool(c.ast.a.val = c.ast.b.val)
    CondR(c,prem) == IF c.ast.cond.val THEN c.ast.then ELSE c.ast.else
    
    LowestArg(c) == LowestIdx(c.ast.args, LAMBDA arg : arg.op # "int")
    FunCond(c) == c.ast.name \in DOMAIN c.funs /\ Len(c.funs[c.ast.name].args) = Len(c.ast.args)
    FunR(c,prem) == Env(MapMapF(c.funs[c.ast.name].args, c.ast.args), c.funs[c.ast.name].body)
    
    IsInt(ast) == ast.op = "int"
    
IN  <<
      Rule([c \in C |-> c.ast.op = "op" /\ ~IsInt(c.ast.a)],
           PTfromNames(<<"a">>), PremMapTrue, PremMapSub("a")),
      Rule([c \in C |-> c.ast.op = "op" /\ IsInt(c.ast.a) /\ ~IsInt(c.ast.b)],
           PTfromNames(<<"b">>), PremMapTrue, PremMapSub("b")),
      Rule([c \in C |-> c.ast.op = "op" /\ IsInt(c.ast.a) /\ IsInt(c.ast.b)],
           PT(<<>>), PremMapTrue, PremMapExceptAST(BinOpR)),
      Rule([c \in C |-> c.ast.op = "cond" /\ c.ast.cond.op # "bool"],
           PTfromNames(<<"cond">>), PremMapTrue, PremMapSub("cond")),
      Rule([c \in C |-> c.ast.op = "cond" /\ c.ast.cond.op = "bool"],
           PT(<<>>), PremMapTrue, PremMapExceptAST(CondR)),
      Rule([c \in C |-> c.ast.op = "var" /\ c.ast.name \in DOMAIN c.vars],
           PT(<<>>), PremMapTrue, PremMapExceptAST(LAMBDA c, prem : c.vars[c.ast.name])),
      Rule([c \in C |-> c.ast.op = "env" /\ ~IsInt(c.ast.ast)],
           CMap(LAMBDA c : <<State(c.funs, c.ast.env, c.ast.ast)>>),
           PremMapTrue, PremMapSub("ast")),
      Rule([c \in C |-> c.ast.op = "env" /\ IsInt(c.ast.ast)],
           PT(<<>>), PremMapTrue, PremMapExceptAST(LAMBDA c, prem : c.ast.ast)),
      Rule([c \in C |-> c.ast.op = "fun" /\ \E arg \in Range(c.ast.args) : arg.op # "int"],
           CMap(LAMBDA c : <<[c EXCEPT !.ast = @.args[LowestArg(c)]]>>),
           PremMapTrue, PremMapExceptAST(LAMBDA c, prem : [c.ast EXCEPT !.args[LowestArg(c)] = prem[1].ast])),
      Rule([c \in C |-> c.ast.op = "fun" /\ \A arg \in Range(c.ast.args) : arg.op = "int" /\ FunCond(c)],
           PT(<<>>), PremMapTrue, PremMapExceptAST(FunR))
    >>

Funs == [fact |-> Fun(<<"n">>, Cond(BinOp("=",Var("n"),Integer(0)), Integer(1), BinOp("*",Var("n"),FunCall("fact",<<BinOp("-",Var("n"),Integer(1))>>))))]
Vars == [m |-> Integer(4)]
\*AST == BinOp("+",Integer(1),BinOp("+",Integer(2),Var("n")))
AST == FunCall("fact",<<Var("m")>>)

INSTANCE SOS

VARIABLE config
Init == config = State(Funs,Vars,AST)
Next == config' \in NextConfigs[config]

=============================================================================