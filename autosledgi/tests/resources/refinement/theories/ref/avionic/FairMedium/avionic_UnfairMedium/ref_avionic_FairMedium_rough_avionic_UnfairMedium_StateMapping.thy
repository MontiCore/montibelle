theory ref_avionic_FairMedium_rough_avionic_UnfairMedium_StateMapping
  imports sps_avionic_UnfairMedium.def_avionic_UnfairMedium_States sps_avionic_FairMedium.def_avionic_FairMedium_States

begin


fun stateMap :: "def_avionic_FairMedium_States.State \<Rightarrow> def_avionic_UnfairMedium_States.State" where
"stateMap (def_avionic_FairMedium_States.StateConstr s _) =
  (def_avionic_UnfairMedium_States.StateConstr def_avionic_UnfairMedium_States.Substate.state__State )"


end
