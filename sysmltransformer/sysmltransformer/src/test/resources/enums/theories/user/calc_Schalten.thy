theory calc_Schalten
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Gen  *)Ampelfarben
    (* Hwl  *)

begin

fun Schalten:: "Ampelfarben => Ampelfarben" where
"Schalten aktuell = (if (aktuell = Rot) then Gruen else Rot)"

end
