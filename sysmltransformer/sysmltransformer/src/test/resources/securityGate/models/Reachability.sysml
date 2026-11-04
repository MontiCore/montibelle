private import SequenceFunctions::intersection;
private import SequenceFunctions::excludes;
private import VerificationLibrary::ReachableStates;

requirement req_SecurityOfGate {
  subject c : SecurityGate_LLR;
  attribute input: EventStream;


  assume constraint gate_is_secure {
    input.values()->intersection((ActionEnum::Alice_plus_Eve_request_Camera_accepts,
       ActionEnum::Bob_plus_Eve_request_Camera_accepts)) == {}
  }

  assert constraint {
    ReachableStates(c.behavior, input.values())->excludes(SecurityGate_LLR.behavior.Bob_Alice_Eve)
  }
}
