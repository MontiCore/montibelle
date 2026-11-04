theory ref_avionic_PerfectMedium_rough_avionic_FairMedium_arec
  imports (* Core *) automaton.AREC
           (* Gen *) sps_avionic_FairMedium.def_avionic_FairMedium sps_avionic_PerfectMedium.def_avionic_PerfectMedium ref_avionic_PerfectMedium_rough_avionic_FairMedium_StateMapping
           (* Hwl *) 

begin


fun paramMap:: "unit \<Rightarrow> unit" where
"paramMap () = ()"

ML_val \<open>checkStateRefinement @{context}
  @{term "(\<lambda> p state sbe. def_avionic_FairMedium.transitionH_00 p state sbe \<union> def_avionic_FairMedium.transitionH_01 p state sbe)"}
  @{term "paramMap"}
  @{term "stateMap"}
  def_avionic_PerfectMedium.channel_avionic_Booleans_val_i_val_transitionList \<close>


end
