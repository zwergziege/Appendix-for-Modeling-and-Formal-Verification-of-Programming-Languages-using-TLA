-------------------------------- MODULE SOS --------------------------------

EXTENDS Util

CONSTANT Rules, Configurations

\* the only purpose of a rule is to check it against configs (or transitions)
\* thus everything is a function in terms of configs
\* works for the following kind of rules
\*
\* p_1 -> p_1', ..., p_n -> p_n' additional_constraints
\* ----------------------------------------------------
\*                    in -> out
\* where
\* - <in> may introduce variables used in all other values
\* - <p_i> is defined in terms of <in>
\* - <p_i'> may introduce variables used in the additional constraints and <out>
\* - the additional constraints do not contain the transition predicate ->
\*
\* InPattern         : pattern that the <in> has to match
\* PremiseTransforms : transform that maps <in> to a sequence <p> of <p_i> that is used as part of the premises
\* Premise           : premise in terms of <in> and a sequence of premise candidates <p_i'>
\* OutTransform      : the resulting configuration in terms of -//-
\* 
\* If a given configuration does not match the input pattern of a rule, this rule is not applicable.
\* A single configuration may have several viable successors. Thus the sequence <p_i'> (<p'>) can be any sequence in the carthesian product of the sets of successors for <p_i>.
\* Conditions on <p_i'> as well as the additional constraints can be expressed in the Premise field. Any candidate <p'> that does not fulfill those needs to be rejected.
\* For each valid <p'>, <in> has a successor state <out> determined by OutTransform.
\*
\* consequences: 
\* <p_i'> can not occur in <p_j>. This makes (finite) big-step semantics of languages with function calls impossible unless a substitution operator is available
\*
\* Big-step SOS for function calls in functional languages using lookahead (call by value)
\* 
\* \A i : state(vars, a_i) -> a_i', state(MapMap(fargs, a'), f.body) -> val ...
\* -----------------------------------------------------------------------------
\*               state(vars, f(a_i)) -> val
\*
\* Big-step SOS for function calls in functional languages using substitution (call by text/name)
\*
\* state(vars, SubstituteVars(f.body, MapMap(fargs, a))) -> val ...
\* -------------------------------------------------------------------
\*               state(vars, f(a_i)) -> val
\*
\* alternative approaches
\* - add a pattern to match for all premise transforms (speed up for large sets of possible rhs in premise)
\* - extract configuration from descriptor. a rule would then be a function from config to descriptor (pure sugar)
\* - revert to PremiseTransforms being a sequence of transforms instead
\* - make vars in <p_i'> available in <p_j> where i<j (i.e. let PremiseTransforms access previously generated <p_i'>)
\*   would enable non-cyclic look-ahead (source-dependent). 
\* - add derivable predicates (how?)
\* - add labled transition relations (how?)

AllRules == [
  InPattern         : [Configurations -> BOOLEAN], 
  PremiseTransforms : [Configurations -> Seq(Configurations)],
  Premise           : [Configurations \X Seq(Configurations) -> BOOLEAN],
  OutTransform      : [Configurations \X Seq(Configurations) -> Configurations]
]

ASSUME \A idx \in DOMAIN Rules: Rules[idx] \in AllRules

NextConfigs[config \in Configurations] == 
  LET NextConfigsRule(rule) == 
        LET PremiseResults == CartProd(MapF(rule.PremiseTransforms[config], NextConfigs))
            ValidPremiseResults == {result \in PremiseResults : rule.Premise[config, result]}
            Results == {rule.OutTransform[config,result] : result \in ValidPremiseResults}
        IN  IF ~rule.InPattern[config] THEN {} ELSE Results
  IN  UNION {NextConfigsRule(Rules[idx]) : idx \in DOMAIN Rules}
  
\* todo: sweet proof that 
\* ASSUME NEW s0, NEW next(_), Configs = RecDef(s0,next),
\*        \A n \in Nat : \A cfg \in RecF(s0,next)[n] : \A rule \in Rules : 
\*          rule.InPattern(cfg) => 
\*          Range(rule.PremiseTransforms[cfg]) \subseteq RecF(s0,next)[n-1]
\* PROVE  Exists(NextConfigsDomain, NextConfigsDef)

=============================================================================
