private import ScalarValues::Natural;
private import ScalarValues::Boolean;

part def SecureProtocol_HLR2 specializes SecureProtocol_HLR1 {
  port input: ~Data;
  port output: Data;

  part alice: Alice_HLR;
  part bob: Bob_HLR;
  part eve1: Eve_HLR { 
    redefines input.val: Tuple { 
      redefines fst: Natural; 
      redefines snd: Boolean; 
    }
    redefines output.val: Tuple { 
      redefines fst: Natural; 
      redefines snd: Boolean; 
    }
  }
  part eve2: Eve_HLR { 
    redefines input.val: Boolean;
    redefines output.val: Boolean;
  }
  part encrypt1: Encrypt1_HLR;
  part encrypt2: Encrypt2_HLR;
  part decrypt1: Decrypt1_HLR;
  part decrypt2: Decrypt2_HLR;

  connect input to alice.input;
  connect alice.output to encrypt1.input;
  connect encrypt1.output to eve1.input;
  connect eve1.output to decrypt1.input;
  connect decrypt1.output to bob.input;
  connect bob.output to output;
  connect bob.control to encrypt2.input;
  connect encrypt2.output to eve2.input;
  connect eve2.output to decrypt2.input;
  connect decrypt2.output to alice.control;
}