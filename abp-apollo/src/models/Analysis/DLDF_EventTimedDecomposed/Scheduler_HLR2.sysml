private import Streams::EventStream::**;
private import Streams::'∞';
private import ScalarValues::*;
private import ControlFunctions::*;
private import CollectionFunctions::*;

part def Scheduler_HLR2 {
  port input: ~Packets;
  port output: Packets;

  attribute capacity: Natural;

  satisfy requirement NonStarvation {
    attribute input_history: EventStream { :>> E: Packet; }
    attribute output_history: EventStream { :>> E: Packet; }

    connect input_history to input;
    connect output_history to output;

    assume constraint InfLongTimeframe {
      input_history->len() == '∞'
    }
    assume constraint MessageInEachInterval {
      (all Natural)->forAll {
        in t: Natural;
        input_history->eNth(t)->len() > 0
      }
    }
    assume constraint SizeBelowMaxCap {
      input_history->values()->forAll {
        in v: Packet;
        v.size < capacity
      }        
    }
    require constraint InfManyOutputMessages {
      output_history->eUntimed()->len() == '∞'
    }
  }
}