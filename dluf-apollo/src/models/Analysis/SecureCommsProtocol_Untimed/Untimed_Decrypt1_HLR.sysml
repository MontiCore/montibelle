private import VerificationLibrary::untimed;
private import VerificationLibrary::Tuple;
private import Streams::UntimedStream::**;
private import ScalarValues::**;

#untimed part def Untimed_Decrypt1_HLR {
  port input: ~Data_Bool_Tuples;
  port output: Data_Bool_Tuples;

  satisfy requirement MsgProcessing {
    attribute input_history: UntimedStream { 
      redefines E: Tuple { 
        redefines fst: Natural; 
        redefines snd: Boolean; 
      }
    }
    attribute output_history: UntimedStream { 
      redefines E: Tuple { 
        redefines fst: Natural; 
        redefines snd: Boolean; 
      }
    }
    connect input_history to input;
    connect output_history to output;

    assert constraint {
      uProjFst(output_history) 
      == uProjFst(input_history)->uMap({in x: Natural; x - 10})
      &
      uProjSnd(output_history) 
      == uProjSnd(input_history)->uMap({in x: Boolean; not x})
    }
  }
}