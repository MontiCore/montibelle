private import Streams::**;
private import ScalarValues::Natural;

part def SecureProtocol_HLR1 {
  port input: ~Data;
  port output: Data;

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
      input_history.len() == Infinity
    }
    assert constraint {
      output_history.untimed() == input_history.untimed()
    }
  }
}