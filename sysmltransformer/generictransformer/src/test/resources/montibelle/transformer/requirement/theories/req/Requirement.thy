theory Requirement
  imports
    (* Gen  *) Requirement
               Requirement
    (* Hwl  *)
begin

lemma Requirement:
  assumes "input = <[EventMsg a, Tick]>"
  assumes "output = < [EventMsg ( \<not> a), Tick]>"
    shows "def_Inverter_LLR1_Output.sbgetter \<cdot>
       (execsem ((), (x, y), z, s)
       (def_Inverter_LLR1_Input.sbsetter \<cdot> input)) = output"
  (* autosledgi *) oops

end
