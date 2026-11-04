private import VerificationLibrary::tsyn;
private import Streams::SyncStream::**;
private import Streams::'∞';
private import Streams::Eps;
private import ScalarValues::*;
private import ControlFunctions::*;
private import CollectionFunctions::*;

#tsyn part def TSyn_Scheduler_HLR2 {
  port input: ~Packets;
  port output: Packets;

  attribute capacity: Natural;

  satisfy requirement NonStarvation {
    attribute input_history: SyncStream { :>> E: Packet; }
    attribute output_history: SyncStream { :>> E: Packet; }

    connect input_history to input;
    connect output_history to output;

    assume constraint InfLongTimeframe {
      input_history->len() == '∞'
    }
    assume constraint MessageInEachInterval {
      (all Natural)->forAll {
        in t: Natural;
        input_history->syncNth(t) != Eps
      }
    }
    assume constraint SizeBelowMaxCap {
      input_history->values()->forAll {
        in v: Packet;
        v.size < capacity
      }        
    }
    require constraint InfManyOutputMessages {
      output_history->syncUntimed()->len() == '∞'
    }
  }
}