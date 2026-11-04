private import Streams::SyncStream::**;
private import Streams::Infinity;
private import ScalarValues::Natural;
private import VerificationLibrary::tsyn;

#tsyn part def SecureProtocol_HLR1 {
  port input: ~ApolloMissionData;
  port output: ApolloMissionData;

  satisfy requirement {
    attribute input_history: SyncStream { 
      redefines E: Natural;
    }
    attribute output_history: SyncStream { 
      redefines E: Natural;
    }

    connect input_history to input;
    connect output_history to output;

    assume constraint {
      input_history->len() == Infinity
    }
    assert constraint {
      output_history->syncUntimed() == input_history->syncUntimed()
    }
  }
}