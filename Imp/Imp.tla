----------------------------- MODULE Imp -----------------------------
EXTENDS Integers, FiniteSets, Sequences, Util, UtilDebug

CONSTANT IDs

Error                == [ op |-> "error" ]

(******************************************************************************)
(* list of types                                                              *)
(******************************************************************************)

IntType            == [ type |-> "int" ]
BoolType           == [ type |-> "bool" ]

VectorType(type)   == [ type |-> "vector", template |-> type ]
RefType(type)      == [ type |-> "ref", template |-> type ]
StructType(name)   == [ type |-> "struct", name |-> name ]

StructTypes        == [ type : {"struct"}, name : IDs ]
VectorTypes(p)     == [ type : {"vector"}, template : p ]
RefTypes(p)        == [ type : {"ref"}, template : p ]

BaseTypes          == {IntType, BoolType} \cup StructTypes
NextTypes(p,n)     == p \cup VectorTypes(p)
Types              == RecDef(BaseTypes, NextTypes)
TypesAndRefsOf(p)  == p \cup RefTypes(p)
TypesAndRefs       == TypesAndRefsOf(Types)

NoType             == [ type |-> "void" ]
TypesAndNoType     == Types \cup {NoType}

\* maybe extend structs to classes (without inheritance)?
\* maybe add first class functions again?

(******************************************************************************)
(* set of values                                                              *)
(******************************************************************************)

Value(type, val)       == [ op |-> "val", type |-> type, val |-> val ]
Integer(i)             == Value(      IntType,   i)
Bool(b)                == Value(     BoolType,   b)
Vector(t,v)            == Value(VectorType(t),   v)
Struct(n,v)            == Value(StructType(n),   v)
Ref(t,loc_idx)         == Value(RefType(t),loc_idx)

NoValue                == [ op |-> "val", type |-> NoType ]

ValueSet(types, values) == [ op : {"val"}, type : types, val : values]  
Bools        == ValueSet({BoolType}, BOOLEAN)
Integers     == ValueSet({IntType}, Int)
Refs         == ValueSet(RefTypes(Types), Nat)
Vectors(p)   == ValueSet(VectorTypes(Types), Seq(p))
Structs(p)   == ValueSet(StructTypes, Seq(p))

BasePackedValue       == Bools \cup Integers
NextPackedValue(p,n)  == p \cup Vectors(p) \cup Structs(p)
PackedValues          == RecDef(BasePackedValue,NextPackedValue)

UnpackedValues     == Bools \cup Integers \cup Vectors(Refs) \cup Structs(Refs)

BaseValue      == BasePackedValue \cup Refs
NextValue(p,n) == NextPackedValue(p,n)
Values         == RecDef(BaseValue, NextValue)

AllValues == Values \cup {NoValue}

(******************************************************************************)
(* list of language constructs                                                *)
(******************************************************************************)

Tags         == {"val", "cond", "fun call", "builtin",
                 "var ctor", "vector ctor", "struct ctor", 
                 "var access", "vector access", "struct access",
                 "vector insert", "vector remove", 
                 "assign", "vector assign", "struct assign", "var assign",
                 "while", "block", "scope", "return"}
BuiltInNames == {"+","-","*",">","=","~","#","@","length"}

Cond(cond, then, else)    == [ op |-> "cond", cond |-> cond, then |-> then, else |-> else ]
FunCall(name, args)       == [ op |-> "fun call", name |-> name, args |-> args ]
BuiltIn(name, args)       == [ op |-> "builtin", name |-> name, args |-> args ]
VectorCtor(type, args)    == [ op |-> "vector ctor", type |-> type, args |-> args ]
StructCtor(name, args)    == [ op |-> "struct ctor", name |-> name, args |-> args ]
VarCtor(id, val)          == [ op |-> "var ctor", id |-> id, val |-> val]
VarAccess(id)             == [ op |-> "var access" , id |-> id ]
StructAccess(ast, name)   == [ op |-> "struct access", struct |-> ast, field |-> name ]
VectorAccess(vec,idx)     == [ op |-> "vector access", vec |-> vec, idx |-> idx ]
VectorInsert(vec,idx,val) == [ op |-> "vector insert", vec |-> vec, idx |-> idx, val |-> val ]
VectorDelete(vec,idx)     == [ op |-> "vector delete", vec |-> vec, idx |-> idx ]
Assign(ref, val)          == [ op |-> "assign", ref |-> ref, val |-> val ]
AssignVec(vec, idx, val)  == [ op |-> "vector assign", vec |-> vec, idx |-> idx, val |-> val]
AssignStruct(s, f, val)   == [ op |-> "struct assign", struct |-> s, field |-> f, val |-> val]
AssignVar(id, val)        == [ op |-> "var assign", id |-> id, val |-> val]
While(cond, body)         == [ op |-> "while", cond |-> cond, body |-> body ]
Block(args)               == [ op |-> "block", args |-> args ]
Scope(sType, val, rType)  == [ op |-> "scope", sType |-> sType, val |-> val, rType |-> rType ]
Return(value, target)     == [ op |-> "return", val |-> value, target |-> target ]

\* Special ASTs

NewScope(rType, val) == Scope("public", val, rType)

Or(a1,a2)  == Cond(a1, Bool(TRUE), a2)
And(a1,a2) == Cond(a1, a2, Bool(FALSE)) 

IfThen(cond,then) == Cond(cond, then, NoValue)

(* definition of ASTs and context / static context *)

ScopeTypes == {"private", "public", "final"}

VarAccesses       == [ op : {"var access"} , id : IDs ]
Conds(p)          == [ op : {"cond"}, cond : p, then : p, else : p ]
FunCalls(p)       == [ op : {"fun call"}, name : IDs, args : Seq(p) ]
BuiltIns(p)       == [ op : {"builtin"}, name : BuiltInNames, args : Seq(p) ]
VectorCtors(p)    == [ op : {"vector ctor"}, type : Types, args : Seq(p) ]
StructCtors(p)    == [ op : {"struct ctor"}, name : IDs, args : Seq(p) ]
VarCtors(p)       == [ op : {"var ctor"}, id : IDs, val : p]
StructAccesses(p) == [ op : {"struct access"}, struct : p, field : IDs ]
VectorAccesses(p) == [ op : {"vector access"}, vec : p, idx : p ]
VectorInserts(p)  == [ op : {"vector insert"}, vec : p, idx : p, val : p ]
VectorDeletes(p)  == [ op : {"vector delete"}, vec : p, idx : p ]
Assigns(p)        == [ op : {"assign"}, ref : p, val : p ]
AssignVecs(p)     == [ op : {"vector assign"}, vec : p, idx : p, val : p]
AssignStructs(p)  == [ op : {"struct assign"}, struct : p, field : IDs, val : p]
AssignVars(p)     == [ op : {"var assign"}, id : IDs, val : p]
Whiles(p)         == [ op : {"while"}, cond : p, body : p ]
Blocks(p)         == [ op : {"block"}, args : Seq(p) ]
Scopes(p)         == [ op : {"scope"}, sType : ScopeTypes, val : p, rType : TypesAndNoType ]
Returns(p)        == [ op : {"return"}, val : p, target : Nat ]

BaseAST      == VarAccesses \cup AllValues \cup {Error}
NextAST(p,n) == UNION {
  Conds(p), FunCalls(p), BuiltIns(p), VarCtors(p), 
  VectorCtors(p), VectorAccesses(p), VectorInserts(p), VectorDeletes(p), 
  StructCtors(p), StructAccesses(p), 
  Assigns(p), AssignVecs(p), AssignStructs(p), AssignVars(p), 
  Whiles(p), Blocks(p), Scopes(p), Returns(p)
}
ASTs == RecDef(BaseAST,NextAST)

TypeIDPair(type, id) == [id |-> id, type |-> type]
TypeIDPairs          == [id : IDs, type : Types]
TIL(ids,types)       == [ idx \in DOMAIN ids |-> TypeIDPair(types[idx], ids[idx])]
TILs                 == Seq(TypeIDPairs)
TILids(til)          == [idx \in DOMAIN til |-> til[idx].id]
TILtypes(til)        == [idx \in DOMAIN til |-> til[idx].type]

TILokay(til)       == Cardinality(Range(TILids(til))) = Cardinality(DOMAIN til)
TILidx(til, id)    == CHOOSE idx \in DOMAIN til : til[idx].id = id
TILaccess(til, id) == til[TILidx(til,id)].type
TILmap(til)        == MapMapF(TILids(til), TILtypes(til))

Function(args, ret, body) == [args |-> args, ret |-> ret, body |-> body]
Functions == [ args : TILs, ret : TypesAndNoType, body : ASTs ]

MapIDsTo(target)   == PartialFunctions(IDs, target)
StructTableEntries == TILs
StructTables       == MapIDsTo(StructTableEntries)
FunEnvironments    == MapIDsTo(Functions) 
StackFrame(e,st)   == [ scopeType |-> st, env |-> e ]
StackFrames        == [ scopeType : ScopeTypes, env : MapIDsTo(Refs) ]
LocEntry(val, cnt) == [ val |-> val, cnt |-> cnt ]
LocEntries         == [ val : UnpackedValues, cnt : Nat]
Stores             == PartialFunctions(Nat, LocEntries)

States == [ structTable : StructTables, funTable : FunEnvironments, store : Stores,
            stack : Seq(StackFrames), ast : ASTs 
          ]
          
InitialState(st, ft, ast) == [ structTable |-> st, funTable |-> ft, store |-> <<>>, stack |-> <<>>, ast |-> ast]
InitialStates             == { state \in States : state.store = <<>> /\ state.stack = <<>> }

StaticVarEnvironments    == MapIDsTo(RefTypes(Types))
StaticStackFrame(e,t,st) == [ env |-> e, targetType |-> t, scopeType |-> st ]
StaticStackFrames        == [ scopeType : ScopeTypes, env : StaticVarEnvironments, targetType : Types ] 

StaticState(st,ft,s,ast) == [ structTable |-> st, funTable |-> ft, stack |-> s, ast |-> ast ]
StaticStates == [ structTable : StructTables, funTable : FunEnvironments, 
                  stack : Seq(StaticStackFrames), ast : ASTs ]
    
(******************************************************************************)
(* node info & tools                                                          *)
(******************************************************************************)
            
GetInfoAST(ast) == 
  LET op == ast.op
      Info(name, isList, isLazy) == [ name |-> name, isList |-> isList, isLazy |-> isLazy ] 
      IList(name) == Info(name,TRUE,FALSE)
      ILazy(name) == Info(name,FALSE,TRUE)
      I(name)     == Info(name,FALSE,FALSE)
  IN  CASE op = "val"           -> <<>>
      []   op = "cond"          -> <<I("cond"), ILazy("then"), ILazy("else")>>
      []   op = "fun call"      -> <<IList("args")>>
      []   op = "builtin"       -> <<IList("args")>>
      []   op = "vector ctor"   -> <<IList("args")>>
      []   op = "struct ctor"   -> <<IList("args")>>
      []   op = "var ctor"      -> <<I("val")>>
      []   op = "var access"    -> <<>>
      []   op = "struct access" -> <<I("struct")>>
      []   op = "vector access" -> <<I("vec"), I("idx")>>
      []   op = "vector insert" -> <<I("vec"), I("idx"), I("val")>>
      []   op = "vector delete" -> <<I("vec"), I("idx")>>
      []   op = "assign"        -> <<I("ref"), I("val")>>
      []   op = "struct assign" -> <<I("struct"), I("val")>>
      []   op = "vector assign" -> <<I("vec"), I("idx"), I("val")>>
      []   op = "var assign"    -> <<I("val")>>
      []   op = "while"         -> <<ILazy("cond"), ILazy("body")>>  
      []   op = "block"         -> <<IList("args")>>
      []   op = "scope"         -> <<I("val")>>
      []   op = "return"        -> <<I("val")>>
      []   op = "error"         -> Die("Called GetInfoAST with error")

FilterAttributesAST(node, filter(_)) == SelectSeq(GetInfoAST(node), filter)
FilterNonLazyAttributes(node) == FilterAttributesAST(node, LAMBDA info : ~info.isLazy)

FindStackFrame[stack \in Seq(StackFrames) \cup Seq(StaticStackFrames), name \in IDs] ==
  IF      stack = <<>>                          THEN 0
  ELSE IF name \in DOMAIN Head(stack).env       THEN 1
  ELSE IF Head(stack).scopeType = "private"     THEN 0
  ELSE IF FindStackFrame[Tail(stack), name] = 0 THEN 0
  ELSE    FindStackFrame[Tail(stack), name] + 1

(******************************************************************************)
(* static semantics                                                           *)
(******************************************************************************)
  
ResolveRefType(t) == IF t.type = "ref" THEN t.template ELSE t
MakeRefType(t)    == IF t.type = "ref" THEN t ELSE RefType(t)

PrintStaticError(msg, state) == TRUE

StaticCheckAST[state \in StaticStates] == 
  LET ast == state.ast
      op  == ast.op
      Result(ctx, type)     == [ ctx EXCEPT !.ast = type ]
      CheckSubAST(ctx, sub) == StaticCheckAST[[ctx EXCEPT !.ast = sub]]
      err_cond ?? resolution == IF err_cond THEN Error ELSE resolution
      PSE(msg) == PrintStaticError(op \o ": " \o msg, state)
      RRT(type)       == ResolveRefType(type)
      RRTs(type_list) == Map(type_list, RRT)
      
      stack_idx(s) == FindStackFrame[s.stack, ast.id]
      
      ChainCheckOp(ctx, c_ast) == 
        IF ctx = Error THEN Error ELSE CheckSubAST(ctx, c_ast)
      ArgCtxs             == Tail(SweepInit(ast.args, ChainCheckOp, state))
      ArgCtxsError        == Error \in Range(ArgCtxs)
      ArgCtxsResult(type) == Result(Last(<<state>> \o ArgCtxs), type)
      ArgCtxsTypes        == Map(ArgCtxs, LAMBDA arg : arg.ast)
  IN  CASE op = "val" -> 
             LET type == ast.type.type
                 eSub(desired(_)) == 
                   \E idx \in DOMAIN ast.val : CheckSubAST(state, ast.val[idx]).ast # desired(idx)
                 struct_descriptor == state.structTable[ast.type.name]
                 fail_cond == 
                   CASE type = "struct" -> 
                          \/ ast.type.name \notin DOMAIN state.structTable /\ PSE("unknown struct name")
                          \/ DOMAIN ast.val # DOMAIN struct_descriptor /\ PSE("struct element count mismatch")
                          \/ eSub(LAMBDA idx : struct_descriptor[idx].type) /\ PSE("struct type mismatch")
                   []   type = "vector" -> eSub(LAMBDA idx : ast.type.template) /\ PSE("vector type mismatch")
                   []   type = "ref" -> TRUE /\ PSE("ref in initial AST is illegal")
                   []   type \in {"int", "bool", "void"} -> FALSE
             IN  fail_cond ?? Result(state, ast.type)
      []   op = "cond" -> 
             LET cond_ctx == CheckSubAST(state, ast.cond)
                 then_ctx == CheckSubAST(cond_ctx, ast.then)
                 else_ctx == CheckSubAST(cond_ctx, ast.else)
                 result_type ==
                   CASE NoType \in {then_ctx.ast, else_ctx.ast} -> NoType
                   []   then_ctx.ast = else_ctx.ast -> then_ctx.ast
                   []   OTHER -> Error
             IN  \/ cond_ctx = Error \/ then_ctx = Error \/ else_ctx = Error
                 \/ RRT(cond_ctx.ast).type # "bool" /\ PSE("cond condition not bool")
                 \/ then_ctx.stack # else_ctx.stack /\ PSE("branch stacks disagree on declared vars")
                 \/ result_type = Error             /\ PSE("branch return types mismatch")
                 ?? Result(cond_ctx, result_type)
      []   op = "fun call" ->
             LET fun  == state.funTable[ast.name]
             IN  \/ ast.name \notin DOMAIN state.funTable /\ PSE("missing function")
                 \/ DOMAIN fun.args # DOMAIN ast.args /\ PSE("arity mismatch")
                 \/ ArgCtxsError
                 \/ RRTs(ArgCtxsTypes) # TILtypes(fun.args) /\ PSE("formal and actual types mismatch")
                 ?? ArgCtxsResult(fun.ret)
      []   op = "builtin" ->
             LET name == ast.name
                 SC(okay, type) == [okay |-> okay, type |-> type]
                 types == RRTs(ArgCtxsTypes)
                 SignatureInfo == 
                   CASE name = "+" -> SC(types = <<IntType,IntType>>, IntType)
                   []   name = "-" -> SC(types = <<IntType,IntType>>, IntType)
                   []   name = "*" -> SC(types = <<IntType,IntType>>, IntType)
                   []   name = ">" -> SC(types = <<IntType,IntType>>, BoolType)
                   []   name = "~" -> SC(types = <<BoolType>>, BoolType)
                   []   name = "=" -> SC(Len(types) = 2, BoolType)
                   []   name = "#" -> SC(Len(types) = 1, types[1])
                   []   name = "@" -> SC(Len(types) = 1, types[1])
                   []   name = "length" -> SC(Len(types) = 1 /\ types[1].type = "vector", IntType)
             IN  \/ name \notin BuiltInNames /\ PSE("invalid builtin")
                 \/ ArgCtxsError
                 \/ ~SignatureInfo.okay /\ PSE("type or arity mismatch")
                 ?? ArgCtxsResult(SignatureInfo.type)
      []   op = "vector ctor" ->
             \/ ArgCtxsError
             \/ \E type \in Range(RRTs(ArgCtxsTypes)) : type # ast.type /\ PSE("type mismatch")
             ?? ArgCtxsResult(VectorType(ast.type))
      []   op = "struct ctor" ->
             \/ ast.name \notin DOMAIN state.structTable /\ PSE("unknown struct name")
             \/ DOMAIN ast.args # DOMAIN state.structTable[ast.name] /\ PSE("invalid arg count")
             \/ ArgCtxsError
             \/ RRTs(ArgCtxsTypes) # TILtypes(state.structTable[ast.name]) /\ PSE("type mismatch")
             ?? ArgCtxsResult(StructType(ast.name))
      []   op = "var ctor" ->
             LET addVar(ctx, type) == [ctx EXCEPT !.stack[1].env = ExtendBy(@,SingleFunction(ast.id, type))]
                 value_ctx == CheckSubAST(state, ast.val)
                 value_ref == MakeRefType(value_ctx.ast)
             IN  \/ state.stack = <<>>       /\ PSE("missing stack")
                 \/ value_ctx = Error 
                 \/ stack_idx(value_ctx) # 0 /\ PSE("variable already present")
                 \/ value_ctx.ast = NoType   /\ PSE("rhs is not a value")
                 ?? Result(addVar(value_ctx, value_ref), value_ref)
      []   op = "var access" -> 
             \/ stack_idx(state) = 0 /\ PSE("missing var")
             ?? Result(state, state.stack[stack_idx(state)].env[ast.id])
      []   op = "vector insert" ->
             LET vec_ctx == CheckSubAST(state, ast.vec)
                 idx_ctx == CheckSubAST(vec_ctx, ast.idx)
                 val_ctx == CheckSubAST(idx_ctx, ast.val)
                 vec_template == RRT(vec_ctx.ast).template
             IN  \/ vec_ctx = Error \/ idx_ctx = Error \/ val_ctx = Error
                 \/ RRT(vec_ctx.ast).type # "vector" /\ PSE("insert into non-vector")
                 \/ RRT(idx_ctx.ast).type # "int"    /\ PSE("insert into vector at non-int index")
                 \/ RRT(val_ctx.ast) # vec_template  /\ PSE("vector type and insert type mismatch")
                 ?? Result(val_ctx, vec_ctx.ast)
      []   op = "vector delete" ->
             LET vec_ctx == CheckSubAST(state, ast.vec)
                 idx_ctx == CheckSubAST(vec_ctx, ast.idx)
             IN  \/ vec_ctx = Error \/ idx_ctx = Error
                 \/ RRT(vec_ctx.ast).type # "vector" /\ PSE("vector delete from non-vector")
                 \/ RRT(idx_ctx.ast).type # "int"    /\ PSE("vector delete from vector at non-int index")
                 ?? Result(idx_ctx, vec_ctx.ast)
      []   op = "vector access" ->
             LET vec_ctx == CheckSubAST(state, ast.vec)
                 idx_ctx == CheckSubAST(vec_ctx, ast.idx)
                 vec_template == RRT(vec_ctx.ast).template
                 \* returns ref if vec is in storage, else branch not always accurate (e.g. Vec[x][1]) (same for struct access)
                 ret_type == ConditionalOp(vec_ctx.ast.type = "ref", vec_template, RefType)        
             IN  \/ vec_ctx = Error \/ idx_ctx = Error
                 \/ RRT(vec_ctx.ast).type # "vector" /\ PSE("vector access non-vector")
                 \/ RRT(idx_ctx.ast).type # "int"    /\ PSE("vector access at non-int index")
                 ?? Result(idx_ctx, ret_type) 
      []   op = "struct access" -> 
             LET struct_ctx  == CheckSubAST(state, ast.struct)
                 struct_name == RRT(struct_ctx.ast).name
                 field_type  == TILaccess(state.structTable[struct_name], ast.field)
                 rec_type    == IF struct_ctx.ast.type = "ref" THEN RefType(field_type) ELSE field_type
             IN  \/ struct_ctx = Error
                 \/ RRT(struct_ctx.ast).type # "struct"         /\ PSE("struct access non-struct") 
                 \/ struct_name \notin DOMAIN state.structTable /\ PSE("unknown struct name")
                 \/ ast.field \notin Range(TILids(state.structTable[struct_name])) /\ PSE("unknown field name")
                 ?? Result(struct_ctx, rec_type)
      []   op = "assign" ->
             LET ref_ctx == CheckSubAST(state, ast.ref)
                 val_ctx == CheckSubAST(ref_ctx, ast.val)
             IN  \/ ref_ctx = Error \/ val_ctx = Error
                 \/ ref_ctx.ast.type # "ref" /\ PSE("tried to assign to non ref")
                 \/ ref_ctx.ast.template # RRT(val_ctx.ast) /\ PSE("mismatching type on assign")
                 ?? Result(val_ctx, ref_ctx.ast)
      []   op = "struct assign" -> 
             LET struct_ctx  == CheckSubAST(state, ast.struct)
                 val_ctx     == CheckSubAST(struct_ctx, ast.val)
                 struct_name == RRT(struct_ctx.ast).name
                 field_type  == TILaccess(state.structTable[struct_name], ast.field)
             IN  \/ struct_ctx = Error \/ val_ctx = Error
                 \/ struct_ctx.ast.type      # "ref"            /\ PSE("struct assign non-ref")
                 \/ RRT(struct_ctx.ast).type # "struct"         /\ PSE("struct assign non-struct") 
                 \/ struct_name \notin DOMAIN state.structTable /\ PSE("unknown struct name")
                 \/ ast.field \notin Range(TILids(state.structTable[struct_name])) /\ PSE("unknown field name")
                 \/ field_type # RRT(val_ctx.ast) /\ PSE("struct assign type mismatch")
                 ?? Result(val_ctx, struct_ctx.ast)
      []   op = "vector assign" -> 
             LET vec_ctx == CheckSubAST(state, ast.vec)
                 idx_ctx == CheckSubAST(vec_ctx, ast.idx)
                 val_ctx == CheckSubAST(idx_ctx, ast.val)
             IN  \/ vec_ctx = Error \/ idx_ctx = Error \/ val_ctx = Error
                 \/ vec_ctx.ast.type      # "ref"    /\ PSE("vector assign non-ref")
                 \/ RRT(vec_ctx.ast).type # "vector" /\ PSE("vector assign non-vector")
                 \/ RRT(idx_ctx.ast).type # "int"    /\ PSE("vector assign vector at non-int index")
                 \/ RRT(vec_ctx.ast).template # RRT(val_ctx.ast) /\ PSE("vector assign type mismatch")
                 ?? Result(val_ctx, vec_ctx.ast)
      []   op = "var assign" -> 
             LET val_ctx == CheckSubAST(state, ast.val)
                 ref_type == state.stack[stack_idx(state)].env[ast.id]
             IN  \/ val_ctx = Error
                 \/ stack_idx(state) = 0   /\ PSE("missing var")
                 \/ RRT(ref_type) # RRT(val_ctx.ast) /\ PSE("var assign type mismatch")  
                 ?? Result(val_ctx, ref_type)
      []   op = "while" ->
             LET cond_ctx  == CheckSubAST(state, ast.cond)
                 while_ctx == CheckSubAST(cond_ctx, ast.body)
             IN  \/ cond_ctx = Error \/ while_ctx = Error
                 \/ state.stack # cond_ctx.stack    /\ PSE("var decl in while cond")
                 \/ RRT(cond_ctx.ast).type # "bool" /\ PSE("while condition not bool")
                 \/ state.stack # while_ctx.stack   /\ PSE("var decl in while body")
                 ?? Result(while_ctx, NoType)
      []   op = "block" ->
             \/ ArgCtxsError
             ?? Last(<<Result(state, NoValue)>> \o ArgCtxs)
      []   op = "scope" -> 
             LET new_frame == StaticStackFrame(<<>>, ast.rType, ast.sType)
                 new_ctx   == [state EXCEPT !.stack = <<new_frame>> \o @ ]
                 ret  == CheckSubAST(new_ctx, ast.val)
             IN  \/ ast.sType = "final"
                 \/ ret = Error
                 \/ ast.rType \notin {NoType, RRT(ret.ast)} /\ PSE("scope return type mismatch")
                 ?? Result(state, ast.rType)
      []   op = "return" ->
             LET ret_ctx == CheckSubAST(state, ast.val)
                 target_type == state.stack[ast.target].targetType
             IN  \/ Len(state.stack) < ast.target /\ PSE("not enough stack frames to pop")
                 \/ target_type # RRT(ret_ctx.ast) /\ PSE("ret type does not match target")
                 ?? Result(ret_ctx, target_type)

StaticCheck(st, ft, ast) == 
  LET SC(stack, sast) == StaticCheckAST[StaticState(st, ft, stack, sast)]
      PSE(msg) == PrintStaticError(msg, StaticState(st, ft, <<>>, ast)) /\ FALSE
  IN  /\ st \in StructTables /\ ft \in FunEnvironments /\ ast \in ASTs
      /\ \A fn \in DOMAIN ft : 
           LET f == ft[fn]
               arg_map == Map(TILmap(f.args), LAMBDA type : RefType(type))
               fun_ctx == SC(<<StaticStackFrame(arg_map, f.ret,"private")>>, f.body)
           IN  /\ TILokay(f.args) \/ PSE("repeating arg names in " \o fn)
               /\ fun_ctx # Error 
               /\ f.ret \in {ResolveRefType(fun_ctx.ast), NoType} \/ PSE("function ret type mismatch in " \o fn)
      /\ \A sn \in DOMAIN st : TILokay(st[sn]) \/ PSE("repeating field names in " \o sn)
      /\ SC(<<>>, ast) # Error

(******************************************************************************)
(* semantics                                                                  *)
(******************************************************************************)

(* Operators *)

PrintDynamicError(msg, state) == TRUE
DynamicError(msg, state) == IF PrintDynamicError(msg, state) THEN [state EXCEPT !.ast = Error ] ELSE FALSE

ResolveRef(state, val) == 
  IF val.type.type = "ref" THEN state.store[val.val].val ELSE val
  
RefInc[state \in States, ast \in Values] == 
  LET recurse == ReduceLeft(ast.val, LAMBDA s,a : RefInc[s,a], state)
  IN CASE ast.type.type = "ref" -> [state EXCEPT !.store[ast.val].cnt = @+1]
     []   ast.type.type \in {"struct", "vector"} -> recurse
     []   OTHER -> state

RefIncSelf(state) == RefInc[state, state.ast]
  
RefDec[state \in States, ast \in Values] == 
  LET val == ResolveRef(state, ast)
      recurse == ReduceLeft(val.val, LAMBDA s,a : RefDec[s,a], state)
      rec_ctx == IF val.type.type \in {"struct", "vector"} THEN recurse ELSE state
  IN  IF ast.type.type = "ref"
      THEN IF state.store[ast.val].cnt = 1 
           THEN [rec_ctx EXCEPT !.store = RestrictBy(@, {ast.val})]
           ELSE [state EXCEPT !.store[ast.val].cnt = @-1]
      ELSE rec_ctx
      
DecRefs[state \in States, seq \in Seq(Values)] == 
  ReduceLeft(seq, LAMBDA s,a : RefDec[s,a], state)
  
PopStackFrame[state \in States] == 
  LET env == state.stack[1].env
      var_name  == CHOOSE var_name \in DOMAIN env : TRUE
      new_frame == [state EXCEPT !.stack[1].env = RestrictBy(@, {var_name})]
  IN  IF env = <<>> 
      THEN [state EXCEPT !.stack = Tail(@)]
      ELSE PopStackFrame[RefDec[new_frame, env[var_name]]]
  
AddLoc(state) == 
  LET used_idx == DOMAIN state.store
      idx == IF used_idx = {} THEN 1 ELSE Min(1..(1+Max(used_idx)) \ used_idx)
      unpacked == state.ast
      ref == Ref(unpacked.type, idx)     
  IN  [state EXCEPT !.ast = ref, !.store = ExtendBy(@, SingleFunction(idx, LocEntry(unpacked, 1)))]
  
Pack[state \in States] == 
  LET val == state.ast
      type == val.type.type 
      PackSub(ast) == Pack[[state EXCEPT !.ast = ast]]
  IN  CASE type = "ref" -> PackSub(ResolveRef(state, val))
      []   type \in {"struct", "vector"} -> [val EXCEPT !.val = Map(val.val, PackSub)]
      []   type \in {"int", "bool", "void"} -> val

UnPack[state \in States, first_lvl \in BOOLEAN] == 
  LET type == state.ast.type.type
      UPallOp(ctx,val) == 
        LET new_ctx == UnPack[[ctx EXCEPT !.ast = val], FALSE]
            new_val == [ctx.ast EXCEPT !.val = @ \o <<new_ctx.ast>> ]
        IN  [new_ctx EXCEPT !.ast = new_val ]
      UPallInit == [state EXCEPT !.ast.val = <<>>]
      UPall == ReduceLeft(state.ast.val, UPallOp, UPallInit)
      first ?? other == IF first_lvl THEN first ELSE other
  IN  CASE type = "ref"                  -> state ?? RefInc[state, state.ast]
      []   type \in {"int", "bool"}      -> state ?? AddLoc(state)
      []   type \in {"struct", "vector"} -> UPall ?? AddLoc(UPall)

BuiltInCall(state) == 
  LET name  == state.ast.name
      args  == state.ast.args
      vals  == Map(args, LAMBDA arg : ResolveRef(state,arg).val)
  IN 
  CASE name = "+" -> Integer(vals[1] + vals[2])
  []   name = "-" -> Integer(vals[1] - vals[2])
  []   name = "*" -> Integer(vals[1] * vals[2])
  []   name = ">" -> Bool(vals[1] > vals[2])
  []   name = "~" -> Bool(~vals[1])  
  []   name = "=" -> Bool(args[1].type = args[2].type /\ args[1] = args[2])
  []   name = "#" -> Pack[[state EXCEPT !.ast = args[1]]]
  []   name = "@" -> ResolveRef(state, args[1])
  []   name = "length" -> Integer(Len(vals[1]))

(* SOS *)

SOS[state \in States] == 
  LET PDE(msg) == PrintDynamicError(state.ast.op \o ": " \o msg, state)
      ReplaceAST(s, ast) == [s EXCEPT !.ast = ast]
      RetAST(ast) == ReplaceAST(state, ast)
      ast == state.ast
      op  == ast.op
      EarlyReturn(sub) == sub.op = "error" \/ (sub.op = "return" /\ sub.val.op = "val")
      AdvanceCond(sub) == sub.op # "val"
      AdvanceOp(sub, newAST) ==
        IF EarlyReturn(sub)
        THEN DecRefs[RetAST(sub), SubNodesBefore(ast, FilterNonLazyAttributes(ast), EarlyReturn)]
        ELSE [ SOS[RetAST(sub)] EXCEPT !.ast = newAST[@] ]
      Advance == TransformFirstSubNode(ast, FilterNonLazyAttributes(ast), AdvanceCond, AdvanceOp, ASTs)
  IN 
  CASE op = "error" -> state
  []   op = "scope" /\ ast.sType # "final" ->  
         LET newAST == [ast EXCEPT !.sType = "final"]
         IN  [ state EXCEPT !.ast = newAST, !.stack = <<StackFrame(<<>>,ast.sType)>> \o @]
  []   op = "scope" /\ ast.sType = "final" /\ ast.val.op = "return" /\ ast.val.val.op = "val" ->
         IF ast.val.target # 1 
         THEN PopStackFrame[RetAST([ast.val EXCEPT !.target = @ - 1])]
         ELSE RetAST([ast EXCEPT !.val = @.val])
  []   op = "scope" /\ ast.sType = "final" /\ ast.val.op = "error" ->
         PopStackFrame[RetAST(ast.val)]
  []   OTHER ->
  IF Advance # ast THEN Advance ELSE 
  LET fail ?? success == IF fail THEN RetAST(Error) ELSE success
      sub_vals \propto new_ctx == DecRefs[new_ctx, sub_vals]
      RR(sub) == ResolveRef(state,sub)
      struct == RR(ast.struct)
      struct_idx == TILidx(state.structTable[struct.type.name], ast.field)
      vec == RR(ast.vec)
      idx == RR(ast.idx).val
      stack_idx == FindStackFrame[state.stack, ast.id]
  IN
  CASE op = "val" -> <<ast>> \propto 
         RetAST(Pack[state])
  []   op = "cond" -> <<ast.cond>> \propto 
         IF RR(ast.cond).val THEN RetAST(ast.then) ELSE RetAST(ast.else)
  []   op = "fun call" -> 
         LET fun == state.funTable[ast.name]
             VarDecls == [i \in DOMAIN ast.args |-> VarCtor(fun.args[i].id, ast.args[i])]
             ScopeBody == Block(VarDecls \o <<fun.body>>)
         IN  RetAST(Scope("private", ScopeBody, fun.ret))
  []   op = "builtin" -> ast.args \propto
         RefIncSelf(RetAST(BuiltInCall(state)))
  []   op = "vector ctor" -> RetAST(Vector(ast.type, ast.args))
  []   op = "struct ctor" -> RetAST(Struct(ast.name, ast.args))
  []   op = "var ctor"    -> <<ast.val>> \propto
         LET ref_ctx == RefIncSelf(UnPack[RetAST(ast.val), FALSE])
         IN  [ ref_ctx EXCEPT !.stack[1].env = ExtendBy(@, SingleFunction(ast.id, ref_ctx.ast)) ]
  []   op = "var access" -> RefIncSelf(RetAST(state.stack[stack_idx].env[ast.id]))
  []   op = "struct access" -> <<ast.struct>> \propto
         LET new_ast == struct.val[struct_idx]
         IN  RefIncSelf(RetAST(new_ast))
  []   op = "vector access" -> <<ast.vec, ast.idx>> \propto
         \/ idx \notin DOMAIN vec.val /\ PDE("index out of bounds") 
         ?? RefIncSelf(RetAST(vec.val[idx]))
  []   op = "vector insert" -> <<ast.vec, ast.idx, ast.val>> \propto
         \/ idx \notin DOMAIN vec.val /\ idx # Len(vec.val)+1 /\ PDE("index out of bounds") 
         ?? LET a !! b == IF ast.vec.type.type = "ref" THEN a ELSE b
                val_ctx == UnPack[RetAST(ast.val), FALSE] !! RetAST(ast.val)
                new_vec == [ vec EXCEPT !.val = InsertAt(@, idx, val_ctx.ast) ]
                ref_ctx == [ val_ctx EXCEPT !.store[ast.vec.val].val = new_vec ]
            IN  RefIncSelf(ReplaceAST(ref_ctx !! state, ast.vec !! new_vec))
  []   op = "vector delete" -> <<ast.idx>> \propto
         \/ idx \notin DOMAIN vec.val /\ PDE("index out of bounds") 
         ?? LET a !! b == IF ast.vec.type.type = "ref" THEN a ELSE b
                new_vec == [ vec EXCEPT !.val = RemoveAt(@, idx) ]
                del_ctx == RefDec[state, vec.val[idx]]
                ref_ctx == [ del_ctx EXCEPT !.store[ast.vec.val].val = new_vec ]
            IN  ReplaceAST(ref_ctx !! del_ctx, ast.vec !! new_vec)
  []   op = "assign" -> <<ast.val>> \propto
         LET val_ctx == UnPack[RetAST(RR(ast.val)), TRUE]
             deref_ctx == RefDec[val_ctx, ResolveRef(state,ast.ref)]
             loc_ctx == [deref_ctx EXCEPT !.store[ast.ref.val].val = ResolveRef(val_ctx,val_ctx.ast)]
         IN  ReplaceAST(loc_ctx, ast.ref)
  []   op = "struct assign" ->
         LET unpack_val_ctx == UnPack[RetAST(ast.val), FALSE]
             ref_dec_ctx == RefDec[unpack_val_ctx, struct.val[struct_idx]]
             new_struct == [ struct EXCEPT !.val[struct_idx] = unpack_val_ctx.ast ]
             new_ctx == [ ref_dec_ctx EXCEPT !.store[ast.struct.val].val = new_struct ]
         IN  <<ast.struct, ast.val>> \propto
             RefIncSelf(ReplaceAST(new_ctx, ast.struct))
  []   op = "vector assign" -> <<ast.vec, ast.idx, ast.val>> \propto 
         \/ idx \notin DOMAIN vec.val /\ PDE("index out of bounds") 
         ?? LET unpack_val_ctx == UnPack[RetAST(ast.val), FALSE]
                ref_dec_ctx == RefDec[unpack_val_ctx, vec.val[idx]]
                new_vec == [ vec EXCEPT !.val[idx] = unpack_val_ctx.ast ]
                new_ctx == [ ref_dec_ctx EXCEPT !.store[ast.vec.val].val = new_vec ]
            IN  RefIncSelf(ReplaceAST(new_ctx, ast.vec))
  []   op = "var assign" ->
         LET unpack_val_ctx == UnPack[RetAST(ast.val), FALSE]
             ref_dec_ctx == RefDec[unpack_val_ctx, state.stack[stack_idx].env[ast.id]]
             new_ctx == [ ref_dec_ctx EXCEPT !.stack[stack_idx].env[ast.id] = unpack_val_ctx.ast ]
         IN  <<ast.val>> \propto
             RefIncSelf(new_ctx)
  []   op = "block" -> ast.args \propto
         RefIncSelf(RetAST(Last(<<NoValue>> \o ast.args)))
  []   op = "while" -> RetAST(IfThen(ast.cond,Block(<<ast.body,ast>>)))
  []   op = "scope" -> 
         LET new_ctx == 
           IF ast.rType.type = "void" 
           THEN RefDec[RetAST(NoValue), ast.val]
           ELSE RetAST(ast.val)
         IN  PopStackFrame[new_ctx]
  []   op = "return" -> PDE("return should never be evaluated") ?? [state EXCEPT !.ast = Error]

=============================================================================