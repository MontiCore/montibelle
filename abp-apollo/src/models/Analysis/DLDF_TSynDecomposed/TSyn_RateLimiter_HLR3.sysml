private import VerificationLibrary::tsyn;
private import Streams::SyncStream::**;
private import Streams::'∞';
private import Streams::Eps;
private import ScalarValues::*;
private import ControlFunctions::*;
private import CollectionFunctions::*;

#tsyn part def TSyn_RateLimiter_HLR3 {
  port input: ~Packets;
  port output: Packets;
  port control: Ctrl;

  attribute cap: Natural;

  satisfy requirement NonStarvation {
    attribute input_history: SyncStream { 
      redefines E: Packet;
    }
    attribute control_history: SyncStream { 
      redefines E: CtrlEnum;
    }
    attribute output_history: SyncStream { 
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
          control_history->syncNth(t+1) != Eps 
          implies input_history->syncNth(t) != Eps
        ) | (
          control_history->syncNth(t+1) == CtrlEnum::NAK
        )
        implies
        (all Natural)->forAll {
          in t : Natural;
          input_history->syncNth(t) != Eps
        }
      }
    }
    require constraint InfManyOutputMessages {
      output_history->syncUntimed()->len() == '∞'
    }
  }
}