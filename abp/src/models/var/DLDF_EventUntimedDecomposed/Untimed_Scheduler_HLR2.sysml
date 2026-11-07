private import VerificationLibrary::untimed;
private import Streams::UntimedStream::**;
private import Streams::'∞';
private import ScalarValues::*;
private import ControlFunctions::*;
private import CollectionFunctions::*;

#untimed part def Untimed_Scheduler_HLR2 {
  port input: ~Packets;
  port output: Packets;

  attribute capacity: Natural;

  satisfy requirement NonStarvation {
    attribute input_history: UntimedStream { :>> E: Packet; }
    attribute output_history: UntimedStream { :>> E: Packet; }

    connect input_history to input;
    connect output_history to output;

    assume constraint InfLongTimeframe {
      input_history->len() == '∞'
    }
    assume constraint SizeBelowMaxCap {
      input_history->values()->forAll {
        in v: Packet;
        v.size < capacity
      }        
    }
    require constraint InfManyOutputMessages {
      output_history->len() == '∞'
    }
  }
}