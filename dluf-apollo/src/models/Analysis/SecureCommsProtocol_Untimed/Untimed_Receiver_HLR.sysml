private import VerificationLibrary::Tuple;
private import VerificationLibrary::untimed;
private import Streams::UntimedStream::**;
private import ScalarValues::Natural;
private import ScalarValues::Boolean;

#untimed part def Untimed_Receiver_HLR {
  port input: ~Data_Bool_Tuples;
  port control: Confirmations;
  port output: ApolloMissionData;

  satisfy requirement MsgProcessing {
    attribute input_history: UntimedStream { 
      redefines E: Tuple { 
        redefines fst: Natural; 
        redefines snd: Boolean; 
      }
    }
    attribute output_history: UntimedStream { 
      redefines E: Natural;
    }
    attribute control_history: UntimedStream { 
      redefines E: Boolean;
    }
    connect input_history to input;
    connect output_history to output;
    connect control_history to control;

    assert constraint {
      output_history == uProjFst(input_history->uRcDups())
    }
    assert constraint {
      control_history == uProjSnd(input_history)
    }
  }
}
