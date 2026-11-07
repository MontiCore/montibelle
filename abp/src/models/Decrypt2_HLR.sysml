private import Streams::**;
private import ScalarValues::Natural;
private import ScalarValues::Boolean;

part def Decrypt2_HLR {
  port input: ~Booleans;
  port output: Booleans;

  satisfy requirement MsgProcessing {
    attribute input_history: SyncStream { 
      redefines E: Boolean;
    }
    attribute output_history: SyncStream { 
      redefines E: Boolean;
    }
    connect input_history to input;
    connect output_history to output;

    assert constraint {
      output_history == smap (tsyn_map (Not)) input_history
    }
  }
}