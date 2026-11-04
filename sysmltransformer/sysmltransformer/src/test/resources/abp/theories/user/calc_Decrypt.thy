theory calc_Decrypt
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Gen  *)
    (* Hwl  *)

begin

fun Decrypt:: "nat => nat" where
"Decrypt x = (x - 10)"

end
