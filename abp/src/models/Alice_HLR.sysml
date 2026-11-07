private import Streams::**;
private import ScalarValues::Natural;
private import ScalarValues::Boolean;
private import ScalarFunctions::min;

part def Alice_HLR {
  port input: ~Data;
  port control: ~Booleans;
  port output: Data_Bool_Tuples;

  satisfy requirement MsgProcessing {
    attribute input_history: SyncStream { 
      redefines E: Natural;
    }
    attribute control_history: SyncStream { 
      redefines E: Boolean;
    }
    attribute output_history: SyncStream { 
      redefines E: Tuple { 
        redefines fst: Natural; 
        redefines snd: Boolean; 
      }
    }
    connect input_history to input;
    connect control_history to control;
    connect output_history to output;

    assume constraint {
      input_history.len() == Infinity & control_history.len() == Infinity
    }
    assert constraint {
      uProjFst(output_history.untimed().rcDups()) ⊑ input_history
      &
      uProjSnd(output_history.untimed().rcDups()).rcDups()
        == uProjSnd(output_history.untimed().rcDups())
      &
      control_history.rcDups().len() < input_history.len() 
        implies output_history.len() == Infinity
      &
      syncProjFst(output_history.rcDups()).len() 
        == min(input_history.len(), 1 + control_history.rcDups().len())
    }
  }
}
