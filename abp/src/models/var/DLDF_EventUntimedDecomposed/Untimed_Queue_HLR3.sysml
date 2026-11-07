private import VerificationLibrary::untimed;
private import Streams::UntimedStream::**;
private import Streams::'∞';
private import ScalarValues::*;
private import ControlFunctions::*;
private import CollectionFunctions::*;

#untimed part def Untimed_Queue_HLR3 {  
  port input: ~Packets;
  port control: ~Ctrl;
  port output: Packets;

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
      input_history->len() == '∞' & control_history->len() == '∞'
    }
    require constraint OutputSubsetInput {
      input_history->values()->containsAll(output_history->values())
    }
  }

}
