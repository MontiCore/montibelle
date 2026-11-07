private import Streams::**;
private import ScalarValues::Natural;
private import ScalarValues::Boolean;

part def Encrypt1_HLR {
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
      syncProjFst(output_history) == smap (tsyn_map (+10)) input_history
      &
      syncProjSnd(output_history) == smap (tsyn_map (Not)) input_history
    }
  }
}
