theory calc_Encrypt
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Gen  *)
    (* Hwl  *)

begin

fun Encrypt:: "nat => nat" where
"Encrypt x = (x + 10)"

end
