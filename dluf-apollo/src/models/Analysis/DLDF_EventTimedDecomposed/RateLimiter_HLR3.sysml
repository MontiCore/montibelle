private import Streams::EventStream::**;
private import Streams::'∞';
private import ScalarValues::*;
private import ControlFunctions::*;
private import CollectionFunctions::*;

part def RateLimiter_HLR3 {
  port input: ~Packets;
  port output: Packets;
  port control: Ctrl;

  attribute cap: Natural;

  satisfy requirement NonStarvation {
    attribute input_history: EventStream { 
      redefines E: Packet;
    }
    attribute control_history: EventStream { 
      redefines E: CtrlEnum;
    }
    attribute output_history: EventStream { 
      redefines E: Packet;
    }
    connect input_history to input;
    connect control_history to control;
    connect output_history to output;

    assume constraint InfLongTimeframe {
      input_history->len() == '∞'
    }
    assume constraint SizeBelowMaxCap {
      input_history->values()->forAll {
        in v: Packet;
        v.size < cap
      }
    }
    assume constraint ControlMessageSemantics {
      (all Natural)->forAll {
        in t: Natural;
        (
          control_history->eNth(t+1)->len() 
          == input_history->eNth(t)->len()
        ) | (
          control_history->eNth(t+1)->values()
          ->contains(CtrlEnum::NAK)
        )
        implies
        (all Natural)->forAll {
          in t : Natural;
          input_history->eNth(t)->len() > 0
        }
      }
    }
    require constraint InfManyOutputMessages {
      output_history->eUntimed()->len() == '∞'
    }
  }
}