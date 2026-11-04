private import Streams::SyncStream::**;
private import ScalarValues::**;
private import VerificationLibrary::**;

#tsyn part def Encrypt1_HLR {
  port input: ~Data_Bool_Tuples;
  port output: Data_Bool_Tuples;

  satisfy requirement MsgProcessing {
    attribute input_history: SyncStream { 
      redefines E: Tuple { 
        redefines fst: Natural; 
        redefines snd: Boolean; 
      }
    }
    attribute output_history: SyncStream { 
      redefines E: Tuple { 
        redefines fst: Natural; 
        redefines snd: Boolean; 
      }
    }
    connect input_history to input;
    connect output_history to output;

    assert constraint {
      syncProjFst(output_history) 
      == syncProjFst(input_history)->syncMap({in x: Natural; x + 10})
      &
      syncProjSnd(output_history) 
      == syncProjSnd(input_history)->syncMap({in x: Boolean; not x})
    }
  }
}
