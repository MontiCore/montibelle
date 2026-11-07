private import VerificationLibrary::untimed;
private import Streams::UntimedStream::**;
private import Streams::Infinity;
private import ScalarValues::Natural;

#untimed part def Untimed_SecureProtocol_HLR1 {
  port input: ~ApolloMissionData;
  port output: ApolloMissionData;

  satisfy requirement {
    attribute input_history: UntimedStream { 
      redefines E: Natural;
    }
    attribute output_history: UntimedStream { 
      redefines E: Natural;
    }

    connect input_history to input;
    connect output_history to output;

    assume constraint {
      input_history->len() == Infinity
    }
    assert constraint {
      output_history == input_history
    }
  }
}