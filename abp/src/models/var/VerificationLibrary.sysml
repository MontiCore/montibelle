library package VerificationLibrary {

  metadata def <delayed> 'Strict Causalality' {
    :>> annotatedElement : BehaviorSpecification;
  }

  metadata def <instant> 'Non-strict Causality' {
    :>> annotatedElement : BehaviorSpecification;
  }

  metadata def <timed> 'Timed' {
    :>> annotatedElement : SysML::PartDefinition;
  }

  metadata def <untimed> 'Untimed' {
    :>> annotatedElement : SysML::PartDefinition;
  }

  metadata def <tsyn> 'Time-Syncronous' :> 'Timed' {
    :>> annotatedElement : SysML::PartDefinition;
  }

  attribute def Tuple {
    attribute def F;
    attribute def S;

    attribute fst: F;
    attribute snd: S;
  }

}