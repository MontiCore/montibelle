private import ScalarValues::Natural;
private import ScalarValues::Boolean;

port def Nat_Bool_Tuples {
  out attribute val: Tuple {
    redefines fst: Natural;
    redefines snd: Boolean;
  }
}
