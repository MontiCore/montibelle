private import VerificationLibrary::*;
private import Streams::SyncStream::**;
private import Streams::'∞';
private import Streams::Eps;
private import ScalarValues::*;
private import ControlFunctions::*;
private import CollectionFunctions::*;

#tsyn part def TSyn_Queue_HLR3 {  
  port input: ~Packets;
  port control: ~Ctrl;
  port output: Packets;

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
      input_history->len() == '∞' & control_history->len() == '∞'
    }
    assume constraint MessageInEachInterval {
      (all Natural)->forAll {
        in attribute t : Natural;
        input_history->syncNth(t) != Eps
      }
    }
    require constraint AlwaysTransmit {
      (all Natural)->forAll {
        in attribute t : Natural;

        ((
          control_history->syncNth(t+1) != Eps 
          implies output_history->syncNth(t) != Eps
        ) | (
          control_history->syncNth(t+1) == CtrlEnum::NAK
        ))
        implies
          (all Natural)->forAll {
            in attribute t : Natural;
            output_history->syncNth(t) != Eps
          }
      }
    }
    require constraint OutputSubsetInput {
      input_history->values()->containsAll(output_history->values())
    }
  }

}
