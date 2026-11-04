private import VerificationLibrary::untimed;
private import Streams::UntimedStream::**;
private import Streams::'∞';
private import ScalarValues::*;
private import ControlFunctions::*;
private import CollectionFunctions::*;

#untimed part def Untimed_RateLimiter_HLR3 {
  port input: ~Packets;
  port output: Packets;
  port control: Ctrl;

  attribute cap: Natural;

  satisfy requirement NonStarvation {
    attribute input_history: UntimedStream { 
      redefines E: Packet;
    }
    attribute control_history: UntimedStream { 
      redefines E: CtrlEnum;
    }
    attribute output_history: UntimedStream { 
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
    require constraint InfManyOutputMessages {
      output_history->len() == '∞'
    }
  }
}