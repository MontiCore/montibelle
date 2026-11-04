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

    calc def projFst {
      in s: Stream { redefines E: Tuple; }
      return : Stream { :>> E = s::E.F; }
    }

    calc def projSnd {
      in s: Stream { redefines E: Tuple; }
      return : Stream { :>> E = s::E.S; }
    }

    calc def dropFirst {
      in s: Stream;
      return : Stream { :>> E = s.E; }
    }

    calc def take {
      in s: Stream;
      in n: Natural;
      return : Stream { :>> E = s.E; }
    }

    calc def dropMultiple {
      in s: Stream;
      in n: Natural;
      return : Stream { :>> E = s.E; }
    }

    calc def times {
      in s: Stream;
      in n: Natural;
      return : Stream { :>> E = s.E; }
    }

    calc def infTimes {
      in s: Stream;
      return : Stream { :>> E = s.E; }
    }

    calc def 'filter' {
      in s: Stream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : Stream { :>> E = s.E; }
    }

    calc def takeWhile {
      in s: Stream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : Stream { :>> E = s.E; }
    }

    calc def dropWhile {
      in s: Stream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : Stream { :>> E = s.E; }
    }

    calc def rcDups {
      in s: Stream;
      return : Stream { :>> E = s.E; }
    }

    calc def zip {
      in s: Stream;
      in second: Stream;
      return : Stream {
        :>> E: Tuple {
          :>> fst subsets s.E;
          :>> snd subsets second.E;
        }
      }
    }

    calc def scanl {
      in s: Stream;
      in f: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = acc.typeParameter; }
        :>> result : SysML::CalculationDefinition {
          :>> parameter : Generic[1] { :>> typeParameter = s.E; }
          :>> result : Generic[1] { :>> typeParameter = acc.typeParameter; }
        }
      }
      in acc: Generic;
      return : Stream { :>> E = acc.typeParameter; }
    }

    calc def '⊑' {
      in : Stream;
      in : Stream;
      return : Boolean;
    }
  }

  attribute def UntimedStream :> Stream {
    calc def uFirst {
      in s: UntimedStream;
      return subsets s.E;
    }

    calc def uNth {
      in s: UntimedStream;
      in n: Natural;
      return subsets s.E;
    }

    calc def uRepeat {
      in elem: Generic;
      in n: Natural;
      return : UntimedStream { :>> E = elem.typeParameter; }
    }

    calc def uIterate {
      in generator: SysML::CalculationDefinition {
        :>> parameter : Generic[1];
        :>> result : Generic {
          :>> typeParameter = parameter.typeParameter;
        }
      }
      in starter: Generic {
        :>> typeParameter = generator.parameter.typeParameter;
      }
      return : UntimedStream { :>> E = starter.typeParameter; }
    }

    calc def uDropFirst {
      in s: UntimedStream;
      return : UntimedStream { :>> E = s.E; }
    }

    calc def uTake {
      in s: UntimedStream;
      in n: Natural;
      return : UntimedStream { :>> E = s.E; }
    }

    calc def uDropMultiple {
      in s: UntimedStream;
      in n: Natural;
      return : UntimedStream { :>> E = s.E; }
    }

    calc def uTimes {
      in s: UntimedStream;
      in n: Natural;
      return : UntimedStream { :>> E = s.E; }
    }

    calc def uInfTimes {
      in s: UntimedStream;
      return : UntimedStream { :>> E = s.E; }
    }

    calc def uMap {
      in s: UntimedStream;
      in f: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Generic[1];
      }
      return : UntimedStream { :>> E = f.result.typeParameter; }
    }

    calc def uFilter {
      in s: UntimedStream;
      in f: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : UntimedStream { :>> E = s.E; }
    }

    calc def uTakeWhile {
      in s: UntimedStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : UntimedStream { :>> E = s.E; }
    }

    calc def uDropWhile {
      in s: UntimedStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : UntimedStream { :>> E = s.E; }
    }

    calc def uZip {
      in s: UntimedStream;
      in second: UntimedStream;
      return : UntimedStream {
        :>> E: Tuple {
          :>> fst subsets s.E;
          :>> snd subsets second.E;
        }
      }
    }

    calc def uScanl {
      in s: UntimedStream;
      in f: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = acc.typeParameter; }
        :>> result : SysML::CalculationDefinition {
          :>> parameter : Generic[1] { :>> typeParameter = s.E; }
          :>> result : Generic[1] { :>> typeParameter = acc.typeParameter; }
        }
      }
      in acc: Generic;
      return : UntimedStream { :>> E = acc.typeParameter; }
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

    calc def eRepeat {
      in elem: Generic;
      in n: Natural;
      return : EventStream { :>> E = elem.typeParameter; }
    }

    calc def eIterate {
      in generator: SysML::CalculationDefinition {
        :>> parameter : Generic[1];
        :>> result : Generic {
          :>> typeParameter = parameter.typeParameter;
        }
      }
      in starter: Generic {
        :>> typeParameter = generator.parameter.typeParameter;
      }
      return : EventStream { :>> E = starter.typeParameter; }
    }

    calc def eProjFst {
      in s: Streams::EventStream { redefines E: Tuple; }
      return : Streams::EventStream { :>> E = s::E.F; }
    }

    calc def eProjSnd {
      in s: Streams::EventStream { redefines E: Tuple; }
      return : Streams::EventStream { :>> E = s::E.S; }
    }

    calc def eDropFirst {
      in s: EventStream;
      return : EventStream { :>> E = s.E; }
    }

    calc def eTake {
      in s: EventStream;
      in n: Natural;
      return : EventStream { :>> E = s.E; }
    }

    calc def eDropMultiple {
      in s: EventStream;
      in n: Natural;
      return : EventStream { :>> E = s.E; }
    }

    calc def eTimes {
      in s: EventStream;
      in n: Natural;
      return : EventStream { :>> E = s.E; }
    }

    calc def eInfTimes {
      in s: EventStream;
      return : EventStream { :>> E = s.E; }
    }

    calc def eMap {
      in s: EventStream;
      in f: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Generic[1];
      }
      return : EventStream { :>> E = f.result.typeParameter; }
    }

    calc def eFilter {
      in s: EventStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : EventStream { :>> E = s.E; }
    }

    calc def eTakeWhile {
      in s: EventStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : EventStream { :>> E = s.E; }
    }

    calc def eDropWhile {
      in s: EventStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : EventStream { :>> E = s.E; }
    }

    calc def eRcDups {
      in s: EventStream;
      return : EventStream { :>> E = s.E; }
    }

    calc def eZip {
      in s: EventStream;
      in second: EventStream;
      return : EventStream {
        :>> E: Tuple {
          :>> fst subsets s.E;
          :>> snd subsets second.E;
        }
      }
    }

    calc def eScanl {
      in s: EventStream;
      in f: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = acc.typeParameter; }
        :>> result : SysML::CalculationDefinition {
          :>> parameter : Generic[1] { :>> typeParameter = s.E; }
          :>> result : Generic[1] { :>> typeParameter = acc.typeParameter; }
        }
      }
      in acc: Generic;
      return : EventStream { :>> E = acc.typeParameter; }
    }

    calc def eDelay {
      in s: EventStream;
      in n: Natural;
      return : EventStream { :>> E = s.E; }
    }

    calc def eMapSlice {
      in s: EventStream;
      in f: SysML::CalculationDefinition {
        :>> parameter : UntimedStream[1] { :>> E = s.E; }
        :>> result : UntimedStream[1];
      }
      return : EventStream { :>> E = f.result.E; }
    }

    calc def eRougherTime {
      in s: EventStream;
      in slices: Natural;
      return : EventStream { :>> E = s.E; }
    }

    calc def eFinerTime {
      in s: EventStream;
      in slices: Natural;
      return : Collections::Set {
        redefines elements : EventStream[*] { :>> E = s.E; }
      }
    }

    calc def eUntimed {
      in s: EventStream;
      return : Streams::UntimedStream { :>> E = s.E; }
    }

    calc def eSync {
      in s: EventStream;
      return : SyncStream { :>> E = s.E; }
    }

    calc def eTopt {
      in s: EventStream;
      return : ToptStream { :>> E = s.E; }
    }
  }

  attribute def ToptStream :> Stream {
    calc def toptFirst {
      in s: ToptStream;
      return subsets s.E[0..1];
    }

    calc def toptNth {
      in s: ToptStream;
      in n: Natural;
      return subsets s.E[0..1];
    }

    calc def toptRepeat {
      in elem: Generic;
      in n: Natural;
      return : ToptStream { :>> E = elem.typeParameter; }
    }

    calc def toptIterate {
      in generator: SysML::CalculationDefinition {
        :>> parameter : Generic[1];
        :>> result : Generic {
          :>> typeParameter = parameter.typeParameter;
        }
      }
      in starter: Generic {
        :>> typeParameter = generator.parameter.typeParameter;
      }
      return : ToptStream { :>> E = starter.typeParameter; }
    }

    calc def toptProjFst {
      in s: ToptStream { redefines E: Tuple; }
      return : ToptStream { :>> E = s::E.F; }
    }

    calc def toptProjSnd {
      in s: ToptStream { redefines E: Tuple; }
      return : ToptStream { :>> E = s::E.S; }
    }

    calc def toptDropFirst {
      in s: ToptStream;
      return : ToptStream { :>> E = s.E; }
    }

    calc def toptTake {
      in s: ToptStream;
      in n: Natural;
      return : ToptStream { :>> E = s.E; }
    }

    calc def toptDropMultiple {
      in s: ToptStream;
      in n: Natural;
      return : ToptStream { :>> E = s.E; }
    }

    calc def toptTimes {
      in s: ToptStream;
      in n: Natural;
      return : ToptStream { :>> E = s.E; }
    }

    calc def toptInfTimes {
      in s: ToptStream;
      return : ToptStream { :>> E = s.E; }
    }

    calc def toptMap {
      in s: ToptStream;
      in f: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Generic[1];
      }
      return : ToptStream { :>> E = f.result.typeParameter; }
    }

    calc def toptFilter {
      in s: ToptStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : ToptStream { :>> E = s.E; }
    }

    calc def toptTakeWhile {
      in s: ToptStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : ToptStream { :>> E = s.E; }
    }

    calc def toptDropWhile {
      in s: ToptStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : ToptStream { :>> E = s.E; }
    }

    calc def toptRcDups {
      in s: ToptStream;
      return : ToptStream { :>> E = s.E; }
    }

    calc def toptZip {
      in s: ToptStream;
      in second: ToptStream;
      return : ToptStream {
        :>> E: Tuple {
          :>> fst subsets s.E;
          :>> snd subsets second.E;
        }
      }
    }

    calc def toptScanl {
      in s: ToptStream;
      in f: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = acc.typeParameter; }
        :>> result : SysML::CalculationDefinition {
          :>> parameter : Generic[1] { :>> typeParameter = s.E; }
          :>> result : Generic[1] { :>> typeParameter = acc.typeParameter; }
        }
      }
      in acc: Generic;
      return : ToptStream { :>> E = acc.typeParameter; }
    }

    calc def toptDelay {
      in s: ToptStream;
      in n: Natural;
      return : ToptStream { :>> E = s.E; }
    }

    calc def toptSizeEmptyTimeslices {
      in s: ToptStream;
      return : Natural;
    }

    calc def toptUntimed {
      in s: ToptStream;
      return : UntimedStream { :>> E = s.E; }
    }

    calc def toptSync {
      in s: ToptStream;
      return : SyncStream { :>> E = s.E; }
    }

    calc def toptEvent {
      in s: ToptStream;
      return : EventStream { :>> E = s.E; }
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

    calc def syncRepeat {
      in elem: Generic;
      in n: Natural;
      return : SyncStream { :>> E = elem.typeParameter; }
    }

    calc def syncIterate {
      in generator: SysML::CalculationDefinition {
        :>> parameter : Generic[1];
        :>> result : Generic {
          :>> typeParameter = parameter.typeParameter;
        }
      }
      in starter: Generic {
        :>> typeParameter = generator.parameter.typeParameter;
      }
      return : SyncStream { :>> E = starter.typeParameter; }
    }

    calc def syncDropFirst {
      in s: SyncStream;
      return : SyncStream { :>> E = s.E; }
    }

    calc def syncTake {
      in s: SyncStream;
      in n: Natural;
      return : SyncStream { :>> E = s.E; }
    }

    calc def syncDropMultiple {
      in s: SyncStream;
      in n: Natural;
      return : SyncStream { :>> E = s.E; }
    }

    calc def syncTimes {
      in s: SyncStream;
      in n: Natural;
      return : SyncStream { :>> E = s.E; }
    }

    calc def syncInfTimes {
      in s: SyncStream;
      return : SyncStream { :>> E = s.E; }
    }

    calc def syncMap {
      in s: SyncStream;
      in f: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Generic[1];
      }
      return : SyncStream { :>> E = f.result.typeParameter; }
    }

    calc def syncFilter {
      in s: SyncStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : SyncStream { :>> E = s.E; }
    }

    calc def syncTakeWhile {
      in s: SyncStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : SyncStream { :>> E = s.E; }
    }

    calc def syncDropWhile {
      in s: SyncStream;
      in predicate: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = s.E; }
        :>> result : Boolean[1];
      }
      return : SyncStream { :>> E = s.E; }
    }

    calc def syncRcDups {
      in s: SyncStream;
      return : SyncStream { :>> E = s.E; }
    }

    calc def syncZip {
      in s: SyncStream;
      in second: SyncStream;
      return : SyncStream {
        :>> E: Tuple {
          :>> fst subsets s.E;
          :>> snd subsets second.E;
        }
      }
    }

    calc def syncScanl {
      in s: SyncStream;
      in f: SysML::CalculationDefinition {
        :>> parameter : Generic[1] { :>> typeParameter = acc.typeParameter; }
        :>> result : SysML::CalculationDefinition {
          :>> parameter : Generic[1] { :>> typeParameter = s.E; }
          :>> result : Generic[1] { :>> typeParameter = acc.typeParameter; }
        }
      }
      in acc: Generic;
      return : SyncStream { :>> E = acc.typeParameter; }
    }

    calc def syncDelay {
      in s: SyncStream;
      in n: Natural;
      return : SyncStream { :>> E = s.E; }
    }

    calc def syncUntimed {
      in s: SyncStream;
      return : Streams::UntimedStream { :>> E = s.E; }
    }

    calc def syncTopt {
      in s: SyncStream;
      return : ToptStream { :>> E = s.E; }
    }

    calc def syncEvent {
      in s: SyncStream;
      return : EventStream { :>> E = s.E; }
    }

    calc def syncBoolFilter {
      in s: SyncStream;
      in f: UntimedStream { redefines E: Boolean; }
      return : SyncStream { :>> E = s.E; }
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
