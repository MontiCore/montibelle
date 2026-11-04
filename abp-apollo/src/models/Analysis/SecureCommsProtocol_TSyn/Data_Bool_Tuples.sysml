private import ScalarValues::**;
private import VerificationLibrary::**;

port def Data_Bool_Tuples {
  out attribute val: Tuple { redefines fst: Natural; redefines snd: Boolean; }
}
