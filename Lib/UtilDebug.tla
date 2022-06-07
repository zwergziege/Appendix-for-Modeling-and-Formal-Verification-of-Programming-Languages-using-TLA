-------------------------------- MODULE UtilDebug --------------------------------
EXTENDS Util, Integers, Sequences, TLC, FiniteSets,  SequenceOps

Die(reason) == Assert(FALSE,reason)
TODO == Die("not implemented")

square(a) == "[" \o a \o "]"
curly(a)  == "{" \o a \o "}"
brac(a)   == "(" \o a \o ")"

\* evaluates l before and r after val
Sandwich(l,val,r) == <<l,val,r>>[2]

IndentTLCGet == 1
ASSUME TLCSet(IndentTLCGet,0)
GetIndentCount == TLCGet(IndentTLCGet)
IncIndent      == TLCSet(IndentTLCGet, GetIndentCount + 1)
DecIndent      == TLCSet(IndentTLCGet, GetIndentCount - 1)
Indent         == 
  LET f[n \in Nat] == IF n = 0 THEN "" ELSE "  " \o f[n-1]
  IN  f[GetIndentCount]
IndentNewLine  == "\n" \o Indent
Indented(val)  == Sandwich(IncIndent, val, DecIndent)

PrintC(cond, msg) == IF cond THEN PrintT(msg) ELSE FALSE
PrintTI(msg)      == PrintT(Indent \o msg)
PrintEnter(str, val) == 
  Sandwich(PrintTI("enter: " \o str), Indented(val), PrintTI("exit: " \o str))

IdentityOp(arg) == arg

NormalizeSet(set) == 
  LET f[sub \in SUBSET set] ==
        IF Cardinality(sub) = 0 THEN <<>>
        ELSE LET a == Arbitrary(sub) IN <<a>> \o f[sub \ {a}]
  IN  f[set]

NormalizeFun(fun) == 
  Map(NormalizeSet(DOMAIN fun), LAMBDA arg : <<arg,fun[arg]>>)

TemplateSL(toS(_),l,sep) == 
  LET f[n \in Nat] == 
        CASE n = 0 -> ""
        []   n = 1 -> toS(l[n])
        []   OTHER -> f[n-1] \o sep \o toS(l[n])
  IN  f[Len(l)]
  \* Reduce(PartialMap(Map(l,toS), 1..(Len(l)-1), LAMBDA e : e \o sep), LAMBDA lhs,rhs : lhs \o rhs)

FunToStr(fun, argStr(_), imgStr(_), sep1, sep2) == 
  LET PairStr(pair) == argStr(pair[1]) \o sep1 \o imgStr(pair[2])
  IN  TemplateSL(PairStr, NormalizeFun(fun), sep2)


=============================================================================