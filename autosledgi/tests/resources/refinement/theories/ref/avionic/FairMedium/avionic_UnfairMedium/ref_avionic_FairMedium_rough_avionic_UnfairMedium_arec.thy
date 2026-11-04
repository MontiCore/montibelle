theory ref_avionic_FairMedium_rough_avionic_UnfairMedium_arec
  imports (* Core *) automaton.AREC
           (* Gen *) sps_avionic_UnfairMedium.def_avionic_UnfairMedium sps_avionic_FairMedium.def_avionic_FairMedium ref_avionic_FairMedium_rough_avionic_UnfairMedium_StateMapping
           (* Hwl *) 

begin


fun paramMap:: "unit \<Rightarrow> unit" where
"paramMap () = ()"

ML_val \<open>checkStateRefinement @{context}
  @{term "(\<lambda> p state sbe. def_avionic_UnfairMedium.transitionH_00 p state sbe \<union> def_avionic_UnfairMedium.transitionH_01 p state sbe)"}
  @{term "paramMap"}
  @{term "stateMap"}
  def_avionic_FairMedium.channel_avionic_Booleans_val_i_val_transitionList \<close>


end
