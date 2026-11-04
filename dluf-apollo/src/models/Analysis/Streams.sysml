package Streams {
  private import ScalarValues::*;
  private import Collections::Set;
  private import VerificationLibrary::Tuple;

  attribute def Tick;
  attribute Eps;

  attribute Infinity;
  alias '∞' for Infinity; 

  attribute def Generic {
    attribute typeParameter;
  }

  attribute def Stream :> Generic {
    attribute E redefines typeParameter;

    calc def len { 
      in : Stream;
      return : Natural; 
    }
    calc def hasInfiniteLen {
      in s: Stream;
      return : Boolean;
    }
    calc def isEmpty {
      in s: Stream;
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
      in s : Stream;
      return : Collections::Set {
        redefines elements subsets s.E[*];
      }
    }

    calc def map {
      in s: Stream;
      in f: SysML::CalculationDefinition { 
        :>> parameter : Generic[1] { :>> parameter.typeParameter = s.E; }
        :>> result : Generic[1];
      }
      return : Stream { :>> E = f.result.typeParameter; }
    }

    calc def '⊑' {
      in : Stream; 
      in : Stream; 
      return : Boolean;
    }
  }

  attribute def UntimedStream :> Stream {
    calc def 'first' {
      in s: UntimedStream;
      return subsets s.E;
    }

    calc def uNth {
      in s: UntimedStream;
      in n: Natural;
      return subsets s.E;
    }
    
    calc def uMap :> map {
      in s: UntimedStream;
      in :>> f: SysML::CalculationDefinition { 
        :>> parameter : Generic[1] { :>> parameter.typeParameter = s.E; }
        :>> result : Generic[1];
      }
      return : UntimedStream { :>> result.E = f.result.typeParameter; }
    }

    calc def 'filter' {
      in s: UntimedStream;
      in f;
      return : UntimedStream;
    }

    calc def uSetFilter {
      in s: UntimedStream;
      in set: Collections::Set;
      return : UntimedStream { redefines E = s.E; }
    }

    calc def uRcDups {
      in s: UntimedStream;
      return : UntimedStream { redefines E = s.E; }
    }

    calc def uBoolFilter {
      in s: UntimedStream;
      in f: UntimedStream { redefines E: Boolean; }
      return : UntimedStream { redefines E = s.E; }
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
      in s: EventStream;
      return : UntimedStream { :>> E = s.E; }
    }

    calc def eNth {
      in s: EventStream;
      in n: Natural;
      return : UntimedStream { :>> E = s.E; }
    }

    calc def eUntimed {
      in s: EventStream;
      return : Streams::UntimedStream { :>> E = s.E; }
    }
  }

  attribute def SyncStream :> Stream {
    calc def syncFirst {
      in s: SyncStream;
      return subsets s.E;
    }

    calc def syncNth {
      in s: SyncStream;
      in n: Natural;
      return subsets s.E;
    }

    calc def syncMap :> map {
      in s: SyncStream;
      in :>> f: SysML::CalculationDefinition { 
        :>> parameter : Generic[1] { :>> parameter.typeParameter = s.E; }
        :>> result : Generic[1];
      }
      return : SyncStream { :>> result.E = f.result.typeParameter; }
    }

    calc def syncRcDups {
      in s: SyncStream;
      return : SyncStream;
    }

    calc def syncUntimed {
      in s: SyncStream;
      return : Streams::UntimedStream { :>> E = s.E; }
    }

    calc def syncBoolFilter {
      in s: SyncStream;
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