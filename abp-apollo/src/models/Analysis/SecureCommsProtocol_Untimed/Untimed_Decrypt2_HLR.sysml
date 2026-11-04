private import VerificationLibrary::untimed;
private import Streams::UntimedStream::**;
private import ScalarValues::Natural;
private import ScalarValues::Boolean;

#untimed part def Untimed_Decrypt2_HLR {
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

    assert constraint {
      output_history == input_history->uMap{ in x: Boolean; not x } 
    }
  }
}