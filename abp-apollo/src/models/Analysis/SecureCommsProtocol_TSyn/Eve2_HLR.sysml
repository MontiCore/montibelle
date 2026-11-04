private import Streams::SyncStream::**;
private import Streams::'∞';
private import Streams::UntimedStream;
private import ScalarValues::**;
private import VerificationLibrary::**;
private import ControlFunctions::**;

#tsyn part def Eve2_HLR {
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

    attribute def UntimedBooleanStream :> UntimedStream {
      redefines E: Boolean; 
    }

    assert constraint output {
      (all UntimedBooleanStream)->exists {
        in ora: UntimedBooleanStream;
        output_history == input_history->syncBoolFilter(ora)
          & ora->uSetFilter({true})->len() == '∞'
      }
    }
  }
}