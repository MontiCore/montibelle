private import ScalarValues::Boolean;

port def Tuples {
  out attribute val: Tuple {
    redefines fst: Boolean;
    redefines snd: Boolean;
  }
}
