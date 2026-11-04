private import Streams::SyncStream::**;
private import ScalarValues::**;
private import VerificationLibrary::**;

#tsyn part def Encrypt2_HLR {
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