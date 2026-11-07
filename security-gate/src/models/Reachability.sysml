private import SequenceFunctions::intersection;
private import SequenceFunctions::includes;

requirement req_SecurityOfGate {
  subject c : SecurityGate_LLR;
  attribute input: EventStream;

  assume constraint gate_is_secure {
    input.values()->intersection((ActionEnum::Alice_plus_Eve_request_Camera_accepts,
       ActionEnum::Bob_plus_Eve_request_Camera_accepts)) == {}
  }

  require constraint {
    ReachableStates(c.behavior, input)->excludes(c.behavior.Bob_Alice_Eve)
  }
}
