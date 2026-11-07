private import VerificationLibrary::**;
private import Streams::'∞';
private import Streams::UntimedStream::**;
private import ScalarValues::**;
private import ControlFunctions::**;

#untimed part def Untimed_Eve2_HLR {
  port input: ~Confirmations;
  port output: Confirmations;

  satisfy requirement MsgProcessing {
    attribute input_history: UntimedStream { 
      redefines E: Boolean;
    }
    attribute output_history: UntimedStream { 
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
        output_history == input_history->uBoolFilter(ora)
          & ora->uSetFilter({true})->len() == '∞'
      }
    }
  }
}