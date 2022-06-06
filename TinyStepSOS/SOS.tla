---------------------------- MODULE SOS ----------------------------

EXTENDS Integers, Sequences, Util, TLC

Tags == {"var", "int", "op"}

Integer(val)   == [ op |-> "int", val |-> val ]
Var(id)        == [ op |-> "var" , id |-> id ]
Op(arg1, arg2) == [ op |-> "op" , arg1 |-> arg1, arg2 |-> arg2 ]

State(variables, ast) == [
  vars |-> variables,
  ast |-> ast
]

(******************************************************************************)
(* static semantics                                                           *)
(******************************************************************************)

WellFormed[state \in Any] == 
  LET ast == state.ast
      w(sub) == WellFormed[[state EXCEPT !.ast = sub]] 
  IN  CASE ast.op = "var" -> ast.id \in DOMAIN state.vars
      []   ast.op = "op"  -> w(ast.arg1) /\ w(ast.arg2)
      []   ast.op = "int" -> ast.val \in Int
      []   OTHER -> FALSE
  
(******************************************************************************)
(* semantics                                                                  *)
(******************************************************************************)

CONSTANT initial_state
VARIABLES state, path

current == At(state, path)

Advance == /\ current.op = "op" 
           /\ \/ /\ current.arg1.op # "int" 
                 /\ path' = path \o <<"arg1">>
              \/ /\ current.arg2.op # "int"
                 /\ path' = path \o <<"arg2">>
           /\ UNCHANGED state

ResolveTo(ast) == 
  /\ state' = Except(state, path, ast)
  /\ path' = <<"ast">>
  
ResolveOp == 
  /\ current.op = "op"
  /\ current.arg1.op = "int"
  /\ current.arg2.op = "int"
  /\ ResolveTo(Integer(current.arg1.val + current.arg2.val))
  
ResolveVar == 
  /\ current.op = "var"
  /\ ResolveTo(Integer(state.vars[current.id]))

Resolve ==
  \/ ResolveOp
  \/ ResolveVar 

PathOkay == 0 < Len(path) /\ path[1] = "ast" 

Init == path = <<"ast">> /\ state = initial_state
Next == Resolve \/ Advance

Spec == Init /\ [][Next]_<<state,path>>

=============================================================================