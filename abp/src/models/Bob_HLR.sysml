private import Streams::SyncStream::**;
private import ScalarValues::Natural;
private import ScalarValues::Boolean;

part def Bob_HLR {
  port input: ~Data_Bool_Tuples;
  port control: Booleans;
  port output: Data;

  satisfy requirement MsgProcessing {
    attribute input_history: SyncStream { 
      redefines E: Tuple { 
        redefines fst: Natural; 
        redefines snd: Boolean; 
      }
    }
    attribute output_history: SyncStream { 
      redefines E: Natural;
    }
    attribute control_history: SyncStream { 
      redefines E: Boolean;
    }
    connect input_history to input;
    connect output_history to output;
    connect control_history to control;

    assert constraint {
      output_history == syncProjFst(input_history.rcDups())
    }
    assert constraint {
      control_history == syncProjSnd(input_history)
    }
  }
}
