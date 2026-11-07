package VerificationLibrary {
  attribute def EventStream {
    calc values;
  }

  attribute def Tick;

  abstract occurrence def Behavior;
  abstract occurrence behaviors : Behavior[*] nonunique;

  metadata def delayed :> Metaobjects::SemanticMetadata {
    :>> baseType = behaviors meta SysML::Usage;
  }

  calc def ReachableStates {
    in stateUsage;
    in input;
  }
}
