private import Streams::**;
private import ScalarValues::Natural;
private import ScalarValues::Boolean;
private import VerificationLibrary::tsyn;

#tsyn part def Decrypt2_HLR {
  port input: ~Confirmations;
  port output: Confirmations;

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
      output_history == input_history->syncMap{ in x: Boolean; not x } 
    }
  }
}