private import VerificationLibrary::*;
private import Streams::**;
private import ScalarValues::*;
private import ControlFunctions::*;
private import CollectionFunctions::*;

part def Queue_HLR3 {  
  port input: ~Packets;
  port control: ~Ctrl;
  port output: Packets;

  #delayed satisfy requirement NonStarvation {
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
      input_history->len() == '∞' & control_history->len() == '∞'
    }
    assume constraint MessageInEachInterval {
      (all Natural)->forAll {
        in attribute t : Natural;
        input_history->eNth(t)->len() > 0
      }
    }
    require constraint AlwaysTransmit {
      (all Natural)->forAll {
        in attribute t : Natural;

        ((
          control_history->eNth(t+1)->len() 
          == output_history->eNth(t)->len()
        ) | (
          control_history->eNth(t+1)->values()
          ->contains(CtrlEnum::NAK)
        ))
        implies
          (all Natural)->forAll {
            in attribute t : Natural;
            output_history->eNth(t)->len() > 0
          }
      }
    }
    require constraint OutputSubsetInput {
      input_history->values()->containsAll(output_history->values())
    }
  }

}
