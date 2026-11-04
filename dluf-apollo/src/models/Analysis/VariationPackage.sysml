package VariationPackage {

  variation part def Executablility {
    variant part untimed : 'Untimed Protocol';
    variant part timed: 'Time-Syncronous Protocol';
  }

  variation part def <'Adequacy'> 'Model Quality' {
    variant part eventTimed : 'Event-driven Timed DLDF';
    variant part eventUntimed : 'Event-driven Untimed DLDF';
    variant part timeSync : 'Time-Syncronous DLDF';
  }

  variation part def 'Event-driven Timed DLDF' {
    variant part atomic : 'Atomic DLDF';
    variant part decomposed : 'Decomposed DLDF';
  }

}