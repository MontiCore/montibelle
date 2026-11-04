private import VerificationLibrary::untimed;
private import VerificationLibrary::Tuple;
private import Streams::UntimedStream::**;
private import Streams::'∞';
private import ScalarValues::**;
private import ControlFunctions::**;

#untimed part def Untimed_Eve1_HLR {
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