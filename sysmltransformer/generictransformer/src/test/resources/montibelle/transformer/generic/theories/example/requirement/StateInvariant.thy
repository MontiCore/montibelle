theory StateInvariant
  imports
    (* Gen *) EventAutomatonInvariant.EventAutomatonInvariant
    (* Hwl  *)

begin


fun StateInvariantFun::"State \<Rightarrow> bool" where
"StateInvariantFun (StateConstr s iTest) = ((iTest < 10))"


end
