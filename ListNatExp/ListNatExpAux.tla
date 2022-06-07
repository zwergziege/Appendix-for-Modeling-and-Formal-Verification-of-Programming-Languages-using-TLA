--------------------------- MODULE ListNatExpAux ---------------------------

EXTENDS ListNatExp

(***************************************************************************)
(* Additional stuff                                                        *)
(***************************************************************************)
ids == \*{"l","x","reverse","append","l1","l2"}
       {"a","b","c","d","l",
        "append","reverse","sum","cumsum",
        "l1","l2","x","a1","a2","a3","b1","b2","b3","c1","c2","c3","pi_gt","pi_add"}


\* essentials
plus(a,b)  == BuiltIn("+",<<a,b>>)
minus(a,b) == BuiltIn("-",<<a,b>>)
mult(a,b)  == BuiltIn("*",<<a,b>>)
equal(a,b) == BuiltIn("=",<<a,b>>)
great(a,b) == BuiltIn(">",<<a,b>>)
build(a,b) == BuiltIn("build",<<a,b>>)
first(a)   == BuiltIn("head",<<a>>)
rest(a)    == BuiltIn("tail",<<a>>)
V == [ id \in ids |-> Var(id) ]
F == [ name \in ids |-> [args \in Any |-> FunCall(name, args)] ]
L == [ args \in Any |-> ListCtor(args) ]
N == [ n \in Nat |-> Natural(n) ]
True == Bool(TRUE)
False == Bool(FALSE)
nil == List(<<>>)
\* function short cuts
append(x,y) == FunCall("append", <<x,y>>)
appendBody  == Cond(equal(V.l1,nil), V.l2, build(first(V.l1),append(rest(V.l1),V.l2)))
reverse(x)  == FunCall("reverse", <<x>>)
reverseBody == Cond(equal(V.l,nil), nil, append(reverse(rest(V.l)),build(first(V.l),nil)))
cumsum(x)   == FunCall("cumsum", <<x>>)

expression1(ll, xx) == reverse(append(ll, build(xx,nil)))
expression2(ll, xx) == build(xx,reverse(ll))

asts == 
LET \* general short cuts
    a1 == reverse(append(V.l, build(V.x,nil)))
    a2 == build(V.x,reverse(V.l))
IN  
[   
  a1      |-> a1,
  a2      |-> a2,
  a3      |-> equal(a1,a2),
  cumsum  |-> Cond(equal(rest(V.l), nil),
                V.l,
                build(first(V.l), cumsum(build(plus(first(V.l),first(rest(V.l))), rest(rest(V.l)))))
               ),
  a4      |-> cumsum(V.l),
  a5      |-> plus(V.x,V.x),
  a6      |-> reverse(reverse(V.l)),
  a7      |-> append(V.l, L[<<V.x>>]),
  pi_gt   |-> Cond(equal(V.l1,nil), False, Cond(equal(V.l2,nil), True, F.pi_gt[rest(V.l1),rest(V.l2)])), 
  pi_add  |-> Cond(equal(V.l1,nil), V.l2, build(nil, F.pi_add[rest(V.l1),V.l2]))
]


      
varEnvs == 
<<
   [ l |-> List([i \in {1,2} |-> Natural(i)]),
     x |-> Natural(3) ],
   [ l |-> List([i \in {1} |-> Natural(i)]),
     x |-> Natural(2) ]
>>

funEnv == 
[ 
  cumsum  |-> Function(<<"l">>, asts.cumsum),
  append  |-> Function(<<"l1","l2">>, appendBody),
  reverse |-> Function(<<"l">>, reverseBody),
  pi_gt   |-> Function(<<"l1","l2">>, asts.pi_gt),
  pi_add  |-> Function(<<"l1","l2">>, asts.pi_add)
]

ComposeState(varEnvIdx, astName) == State(funEnv, varEnvs[varEnvIdx], asts[astName])

TestEqualityProperty(ast1, ast2, os) ==
  \A varEnv \in os : 
    LET i(ast) == I(State(funEnv,varEnv,ast)) 
    IN  i(ast1) = i(ast2)

TestPropertyAppendReverse == TestEqualityProperty(asts.a1, asts.a2, [ l : Lists, x : Naturals ])
(*TestPropertyReverseReverse == TestEqualityProperty(asts.a6, Var("l"), [ l : Lists ])        
    
EvalState == I(State(funEnv, varEnvs[1], asts.a2))

EvalFunction(d,fun) == 
  LET domain == [DOMAIN d[fun].args -> Values]
      f[args \in domain] == I(State(d, EmptyFunction, FunCall(fun,args))) 
  IN  f

EncodingNat ==
  LET eNat[n \in Nat] == List([m \in 1..n |-> List(<<>>)])
      eBool == [b \in BOOLEAN |-> Bool(b)]
      op(arity,ret,o,eo) == [ arity |-> arity, ret |-> ret, operator |-> o, eoperator |-> eo]
      gt[a \in Nat, b \in Nat]  == a>b
      add[a \in Nat, b \in Nat] == a+b
  IN  
  [ Encodings |-> [ nat |-> eNat, bool |-> eBool ],
    Operators |-> {
        op(<<"nat","nat">>,"bool",gt,EvalFunction(funEnv,"pi_gt")),
        op(<<"nat","nat">>,"nat",add,EvalFunction(funEnv,"pi_add"))
      }
  ]

NatsO == Naturals

EncodingNatComp == 
  LET e[in \in Naturals \cup Bools] == 
        CASE in \in Naturals -> List([n \in 1..in.val |-> List(<<>>)])
        []   in \in Bools -> in
      op(o,eo) == [op |-> o, eop |-> eo]
      gt[x \in NatsO, y \in NatsO]  == Bool(x.val>y.val)
      add[x \in NatsO, y \in NatsO] == Natural(x.val+y.val)
  IN [ Encoding  |-> e, 
       Operators |-> {
           op(gt,EvalFunction(funEnv,"pi_gt")),
           op(add,EvalFunction(funEnv,"pi_add"))
         }
     ]
*)
=============================================================================