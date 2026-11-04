theory aut_1_pressed_input

imports bundle_button bundle_colors
  eventcomponent.EventAutomaton
  bundle.MsgWithChan

begin

definition aut_1i::"(nat, cs1 msgWithChan event, bundle_colors.cs sb) iAutomaton" where
"aut_1i = \<lparr>iautTransition=undefined, iautInitConfig=undefined \<rparr>"


definition aut_1::"(nat, cs1 msgWithChan event, bundle_colors.cs sb) automaton" where
"aut_1 = gi2gc aut_1i"


end