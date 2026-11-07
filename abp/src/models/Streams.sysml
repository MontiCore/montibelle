package Streams {
  private import ScalarValues::*;
  private import Collections::Set;

  attribute Infinity;

  attribute def Generic {
    attribute typeParameter : KerML::Core::Type;
  }

  attribute def Stream :> Generic {
    attribute E redefines typeParameter : KerML::Core::Type;

    calc def len {
      in : Stream;
      return : Natural;
    }
    calc def hasInfiniteLen {
      in : Stream;
      return : Boolean;
    }
    calc def isEmpty {
      in : Stream;
      return : Boolean;
    }

    calc def repeat {
      in elem: Generic;
      in n: Natural;
      return : Stream { :>> E = elem.typeParameter; }
    }

    calc def 'iterate' {
      in generator: SysML::CalculationDefinition { 
        :>> parameter : Generic[1];
        :>> result : Generic { 
          :>> typeParameter = parameter.typeParameter;
        }
      }
      in starter: Generic { 
        :>> typeParameter = generator.parameter.typeParameter; 
      }
      return : Stream { :>> E = starter.typeParameter; }
    }

    calc def values {
      in : Stream;
      return : Collections::Set {
        redefines elements subsets E[*];
      }
    }

    calc def smap {
      in : Stream;
      in generator: SysML::CalculationDefinition { 
        :>> parameter : Generic[1];
        :>> result : Generic[1];
      }
      return : Stream { :>> E = result.typeParameter; }
    }

    calc def '⊑' {
      in : Stream; 
      in : Stream; 
      return : Boolean;
    }
  }

  attribute def UntimedStream :> Stream {
    calc def 'first' {
      in : UntimedStream;
      return subsets E;
    }

    calc def nth {
      in : UntimedStream;
      in n: Natural;
      return subsets E;
    }

    calc def rcDups {
      in : UntimedStream;
      return : UntimedStream;
    }

    calc def 'filter' {
      in : UntimedStream;
      in f;
      return : UntimedStream;
    }

    calc def setFilter {
      in : UntimedStream;
      in set: Collections::Set;
      return : UntimedStream;
    }

    calc def uProjFst {
      in s: Streams::UntimedStream { redefines E: Tuple; }
      return : Streams::UntimedStream { :>> E = s::E.F; }
    }

    calc def uProjSnd {
      in s: Streams::UntimedStream { redefines E: Tuple; }
      return : Streams::UntimedStream { :>> E = s::E.S; }
    }
  }

  attribute def EventStream :> Stream {
    calc def 'first' {
      in : EventStream;
      return : UntimedStream { :>> E = E; }
    }

    calc def nth {
      in : EventStream;
      in n: Natural;
      return : UntimedStream { :>> E = E; }
    }
  }

  attribute def SyncStream :> Stream {
    calc def 'first' {
      in : SyncStream;
      return subsets E;
    }

    calc def nth {
      in : SyncStream;
      in n: Natural;
      return subsets E;
    }

    calc def rcDups {
      in : SyncStream;
      return : SyncStream;
    }

    calc def untimed {
      in : SyncStream;
      return : Streams::UntimedStream { :>> E = E; }
    }

    calc def syncBoolFilter {
      in : SyncStream;
      in f: UntimedStream { redefines E: Boolean; }
      return : SyncStream;
    }

    calc def syncProjFst {
      in s: Streams::SyncStream { redefines E: Tuple; }
      return : Streams::SyncStream { :>> E = s::E.F; }
    }

    calc def syncProjSnd {
      in s: Streams::SyncStream { redefines E: Tuple; }
      return : Streams::SyncStream { :>> E = s::E.S; }
    }
  }
}