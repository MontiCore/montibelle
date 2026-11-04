private import Streams::SyncStream::**;
private import Streams::UntimedStream;
private import Streams::Infinity;
private import ScalarValues::Natural;
private import ScalarValues::Boolean;
private import ScalarFunctions::min;
private import VerificationLibrary::Tuple;
private import VerificationLibrary::tsyn;

#tsyn part def Sender_HLR {
  port input: ~ApolloMissionData;
  port control: ~Confirmations;
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
      input_history->len() == Infinity & control_history->len() == Infinity
    }
    assert constraint {
      uProjFst(
        output_history->syncUntimed()->uRcDups())->'⊑'(input_history)
      &
      uProjSnd(output_history->syncUntimed()->uRcDups())->uRcDups()
        == uProjSnd(output_history->syncUntimed()->uRcDups())
      &
      control_history->syncRcDups()->len() < input_history->len() 
        implies output_history->len() == Infinity
      &
      syncProjFst(output_history->syncRcDups())->len() 
        == min(input_history->len(), 1 + control_history->syncRcDups()->len())
    }
  }
}
