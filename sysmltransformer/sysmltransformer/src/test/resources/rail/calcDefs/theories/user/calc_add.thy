theory calc_add
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Gen  *)
    (* Hwl  *)

begin

fun add:: "nat => nat => nat" where
"add a b = (a + b)"

end
