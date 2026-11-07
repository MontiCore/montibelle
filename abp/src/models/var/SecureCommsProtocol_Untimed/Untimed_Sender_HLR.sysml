private import Streams::UntimedStream::**;
private import Streams::Infinity;
private import ScalarValues::Natural;
private import ScalarValues::Boolean;
private import ScalarFunctions::min;
private import VerificationLibrary::Tuple;
private import VerificationLibrary::untimed;

#untimed part def Untimed_Sender_HLR {
  port input: ~ApolloMissionData;
  port control: ~Confirmations;
  port output: Data_Bool_Tuples;

  satisfy requirement MsgProcessing {
    attribute input_history: UntimedStream { 
      redefines E: Natural;
    }
    attribute control_history: UntimedStream { 
      redefines E: Boolean;
    }
    attribute output_history: UntimedStream { 
      redefines E: Tuple { 
        redefines fst: Natural; 
        redefines snd: Boolean; 
      }
    }
    connect input_history to input;
    connect control_history to control;
    connect output_history to output;

    assume constraint {
      input_history->len() == Infinity & control_history->len() == Infinity
    }
    assert constraint {
      uProjFst(
        output_history->uRcDups())->'⊑'(input_history)
      &
      uProjSnd(output_history->uRcDups())->uRcDups()
        == uProjSnd(output_history->uRcDups())
      &
      control_history->uRcDups()->len() < input_history->len() 
        implies output_history->len() == Infinity
      &
      uProjFst(output_history->uRcDups())->len() 
        == min(input_history->len(), 1 + control_history->uRcDups()->len())
    }
  }
}
