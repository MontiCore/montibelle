theory ref_avionic_PerfectMedium_rough_avionic_FairMedium_StateMapping
  imports sps_avionic_FairMedium.def_avionic_FairMedium_States sps_avionic_PerfectMedium.def_avionic_PerfectMedium_States

begin


fun stateMap :: "def_avionic_PerfectMedium_States.State \<Rightarrow> def_avionic_FairMedium_States.State" where
"stateMap (def_avionic_PerfectMedium_States.StateConstr s ) =
  undefined"


end
