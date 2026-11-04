theory HlrDecomposition
  imports
    (* Gen  *) specification.Specification composition.Composition
               instance.SpecificationInstance 
    (* Hwl  *)

begin




lemma pred_0:
  assumes "Specification.wholePredicate ()  (InputMap.connector\<cdot>(natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1)) (OutputMap.connector\<cdot>(natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1))"
      and "wellformed (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)"
      and "Specification.assumption_0 () (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"
      and "natOutChannel_pattern = natOutChannel_pattern_instantiated_1"
      and "bOutChannel_pattern = bOutChannel_pattern_instantiated_1"
      and "sOutChannel_pattern = sOutChannel_pattern_instantiated_1"
      and "natInChannel_pattern_instantiated_1 = natInChannel_pattern"
      and "bInChannel_pattern_instantiated_1 = bInChannel_pattern"
      and "sInChannel_pattern_instantiated_1 = sInChannel_pattern"
    shows "Specification.predicate_0 () (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"
  apply(insert assms(1-3), simp add: assms(4-9))
  apply(simp add: Specification.wholePredicate_def Specification.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: InputMap.connector.rep_eq OutputMap.connector.rep_eq)?
  apply(simp add: Specification.assumption_0_def Specification.predicate_0_def Specification.predicate_1_def Specification.causality_def)?
  apply(simp add: Specification.assumption_0_def Specification.predicate_0_def Specification.predicate_1_def Specification.causality_def)?
  apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)?
  apply(simp add: len_stream_def[symmetric])?
  (* autosledgi *) sorry

lemma pred_1:
  assumes "Specification.wholePredicate ()  (InputMap.connector\<cdot>(natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1)) (OutputMap.connector\<cdot>(natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1))"
      and "wellformed (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)"
      and "Specification.assumption_0 () (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"
      and "natOutChannel_pattern = natOutChannel_pattern_instantiated_1"
      and "bOutChannel_pattern = bOutChannel_pattern_instantiated_1"
      and "sOutChannel_pattern = sOutChannel_pattern_instantiated_1"
      and "natInChannel_pattern_instantiated_1 = natInChannel_pattern"
      and "bInChannel_pattern_instantiated_1 = bInChannel_pattern"
      and "sInChannel_pattern_instantiated_1 = sInChannel_pattern"
    shows "Specification.predicate_1 () (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"
  apply(insert assms(1-3), simp add: assms(4-9))
  apply(simp add: Specification.wholePredicate_def Specification.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: InputMap.connector.rep_eq OutputMap.connector.rep_eq)?
  apply(simp add: Specification.assumption_0_def Specification.predicate_0_def Specification.predicate_1_def Specification.causality_def)?
  apply(simp add: Specification.assumption_0_def Specification.predicate_0_def Specification.predicate_1_def Specification.causality_def)?
  apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)?
  apply(simp add: len_stream_def[symmetric])?
  (* autosledgi *) sorry

lemma causality:
  assumes "Specification.wholePredicate ()  (InputMap.connector\<cdot>(natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1)) (OutputMap.connector\<cdot>(natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1))"
      and "natOutChannel_pattern = natOutChannel_pattern_instantiated_1"
      and "bOutChannel_pattern = bOutChannel_pattern_instantiated_1"
      and "sOutChannel_pattern = sOutChannel_pattern_instantiated_1"
      and "natInChannel_pattern_instantiated_1 = natInChannel_pattern"
      and "bInChannel_pattern_instantiated_1 = bInChannel_pattern"
      and "sInChannel_pattern_instantiated_1 = sInChannel_pattern"
    shows "Specification.causality (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"
  apply(insert assms)
  apply(simp add: Specification.wholePredicate_def Specification.causality_def
                  Specification.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: InputMap.connector.rep_eq OutputMap.connector.rep_eq)?
  apply(simp add: Specification.causality_def strongpred_def weakpred_def tlen_prod_def)?
  apply(rule conjI)?
  (* autosledgi *) sorry

lemma pred_whole:
  assumes "Specification.wholePredicate () (InputMap.connector\<cdot>(natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1))  (OutputMap.connector\<cdot>(natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1))"
      and "natOutChannel_pattern = natOutChannel_pattern_instantiated_1"
      and "bOutChannel_pattern = bOutChannel_pattern_instantiated_1"
      and "sOutChannel_pattern = sOutChannel_pattern_instantiated_1"
      and "natInChannel_pattern_instantiated_1 = natInChannel_pattern"
      and "bInChannel_pattern_instantiated_1 = bInChannel_pattern"
      and "sInChannel_pattern_instantiated_1 = sInChannel_pattern"
    shows "Specification.wholePredicate () (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"
  apply(simp add: Specification.wholePredicate_def)
  using assms causality pred_0 pred_1 by force

lemma pred_whole2:
  assumes "Specification.wholePredicate () (InputMap.connector\<cdot>(Composition_rawinput2SpecificationInstance input))(OutputMap.connector\<cdot>(Composition_rawoutput2SpecificationInstance output))"
  assumes "Connectors.connector\<cdot>(Composition_rawinput2Connectors input) = Composition_rawoutput2Connectors output"
  assumes "rawinput2composition_feedback input = rawoutput2composition_feedback output"
    shows "Specification.wholePredicate () (rawinput2composition input) (rawoutput2composition output)"
  apply(rule rawinput2composition.cases[of "input"],
        rule rawoutput2composition.cases[of "output"], simp)
  apply(rule pred_whole)
  using assms apply (auto simp add: Connectors.connector.rep_eq)
  done

lemma raw_input_eq:
  assumes "spf\<in>(Composition.rawSps ())"
    shows "((sb)\<star>::Input.channels\<^sup>\<Omega>)
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(Connector1Input.channels
                           \<union>Instance1Input.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)

lemma raw_pred_whole:
  assumes "spf\<in>(Composition.rawSps ())"
    shows "Specification.wholePredicate ()
             (Input.SB.getter\<cdot>(sb\<star>))
             (Output.SB.getter\<cdot>((spf\<cdot>(sb))\<star>))"
  apply(subst raw_input_eq[OF assms(1)])
  apply(simp add: Input.sbgetter_def Output.sbgetter_def
                  Composition_input_Sub.getter_sub_eq Composition_output_Sub.getter_sub_eq)
  apply(rule pred_whole2)
  apply(simp only: SpecificationInstance_input_Sub.getter_sub_eq[symmetric] SpecificationInstance_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: InputMap.connector.rep_eq OutputMap.connector.rep_eq)
  apply(subst Instance1Input.getter_fold,
        subst Instance1Output.getter_fold,
        subst sb_star21, simp)
  apply(rule SpecificationInstance_pred_general[OF assms(1)])
  apply(simp add: Specification.Sps_def)
  apply(simp only: Connectors_input_Sub.getter_sub_eq[symmetric]
                   Connectors_output_Sub.getter_sub_eq[symmetric])
  apply(subst Connector1Input.getter_fold,
        subst Connector1Output.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst connector_apply_eq, simp, simp)
  apply(simp only: feedback_input_sub.getter_sub_eq[symmetric]
                   feedback_output_sub.getter_sub_eq[symmetric])
  apply(subst Feedback.getter_fold,
        subst Feedback.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst feedback_getter_eq, simp, simp)
  done

lemma comp_pred_whole:
  assumes "spf\<in>(Composition.Sps ())"
    shows "Specification.wholePredicate ()
             (Input.SB.getter\<cdot>sb)
             (Output.SB.getter\<cdot>(spf\<cdot>(sb)))"
  apply(rule spsconvert_predicate)
  using assms apply(simp add: Composition.Sps_def)
  using raw_pred_whole apply blast
  by auto

lemma refinement[simp]: "Composition.Sps () \<subseteq> Specification.Sps ()"
  by(simp add: subsetI Specification.Sps_def comp_pred_whole)


end
