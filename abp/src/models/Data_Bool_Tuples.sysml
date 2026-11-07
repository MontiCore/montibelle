private import ScalarValues::Natural;
private import ScalarValues::Boolean;

port def Data_Bool_Tuples {
  out attribute val: Tuple { redefines fst: Natural; redefines snd: Boolean; }
}
