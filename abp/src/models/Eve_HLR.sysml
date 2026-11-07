private import Streams::**;
private import ScalarValues::Boolean;
private import ControlFunctions::exists;

part def Eve_HLR {
  attribute def I;
  attribute def O;

  port input: ~GenericPortDef { in val redefines val: I; }
  port output: GenericPortDef { out val redefines val: O; }

  satisfy requirement {
    attribute input_history: SyncStream;
    attribute output_history: SyncStream;

    connect input_history to input;
    connect output_history to output;

    attribute def UntimedBooleanStream :> UntimedStream {
      redefines E: Boolean; 
    }

    assert constraint {
      (all UntimedBooleanStream)->exists { 
        in ora: UntimedStream;
        output_history == input_history.syncBoolFilter(ora)
          & ora.setFilter({true}).len() == Infinity
      }
    }
  }

}