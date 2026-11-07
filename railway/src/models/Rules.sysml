package Rules {
  private import ControlFunctions::exists;
  private import ScalarValues::Boolean;
  private import Railway::*;
  private import Signals::*;
  private import ControlFunctions::forAll;

  calc def Close {
    in a: Access_Point;
    in b: Access_Point;
    in railway: Railway_Network;
    return : Boolean;

    a.sect == b.sect
    | (railway.access_points)->exists { 
        in c: Access_Point; 
        a.sect == (c.co).sect & c.sect == b.sect 
    }
  }

  calc def Possible_Switch {
    in a: Access_Point;
    in b: Access_Point;
    return : Boolean;  

    a.sect == b.sect 
        & (a,b) != (a42,a43)
        & (a,b) != (a43,a42)
        & (a,b) != (a72,a71)
        & (a,b) != (a71,a72)
  }

  private import Collections::Map;
  private import ScalarValues::String;
  private import ControlFunctions::forAll;

  calc def SafeLight {
    in railway: Railway_Network;
    in a: Access_Point;
    return : Boolean;  

    a.isOpen & a.co.isOpen & 
      (railway.access_points)->forAll {
        in b: Access_Point;
        (Close(a, b, railway) & b.isGreen) 
          implies (
            a == b | (a.sect == b.co.sect & a.co.sect == b.sect) 
          )
      }
  }

  calc def IsFree {
    in t: Train[*];
    in a: Access_Point;
    return : Boolean;

    t->forAll { 
      in t: Train;
      t.position.sect != a.sect
    }
  }

  calc def SafeGreen {
    in railway: Railway_Network;
    in a: Access_Point;
    return : Boolean;  

    SafeLight(railway, a) 
    & (railway.access_points)->forAll {
      in b: Access_Point;
      Close(a, b, railway) & a.co.sect != b.sect implies IsFree(railway.trains, b)
    }
  }

  calc def Protected {
    in railway: Railway_Network;
    in s: Section;
    return : Boolean;  

    (railway.access_points)->forAll {
      in a: Access_Point;
      a.sect == s implies not a.isGreen & not a.co.isGreen
    }
  }

  calc def Phys_Trans_Enter {
    in railway: Railway_Network;
    in signal: Enters;
    return : Railway_Network;

    attribute t0: Train = signal.train;
    attribute a: Access_Point = signal.access;

    attribute untouched: Train[*] = railway.trains->select {
      in t: Train;
      t != t0
    };

    if a.co.sect == t0.position.sect ? 
      new Railway_Network(
        access_points = railway.access_points, 
        trains = untouched + new Train(a)
      )
    else
      railway
  }

  calc def Phys_Trans_Open {
    in railway: Railway_Network;
    in signal: OpenUp;
    return : Railway_Network;

    attribute c: Access_Point = signal.a;
    attribute b: Access_Point = signal.b;

    attribute c_after: Access_Point = new Access_Point(
      c.sect,
      c.co,
      true,
      c.isGreen
    );

    attribute b_after: Access_Point = new Access_Point(
      b.sect,
      b.co,
      true,
      b.isGreen
    );

    attribute co_c_after: Access_Point = new Access_Point(
      c.co.sect,
      c_after,
      false,
      c.co.isGreen
    );

    attribute co_b_after: Access_Point = new Access_Point(
      b.co.sect,
      b_after,
      false,
      b.co.isGreen
    );

    attribute untouched: Access_Point[*] = railway.access_points->select {
      in a: Access_Point;
      a != c & a != b & a != c.co & a != b.co
    };

    attribute openedRailway: Railway_Network = new Railway_Network(
      access_points = untouched + (c_after, b_after, co_c_after, co_b_after),
      trains = railway.trains
    );

    if Possible_Switch(c, b) ? openedRailway else railway
  }

  private import ControlFunctions::'select';

  calc def Phys_Trans_Color {
    in railway: Railway_Network;
    in signal: SetColor;
    return : Railway_Network;

    attribute access_after: Access_Point = new Access_Point(
      signal.access.sect,
      signal.access.co,
      signal.access.isOpen,
      signal.b
    );
    attribute coAccess_after: Access_Point = new Access_Point(
      signal.access.co.sect,
      access_after,
      signal.access.co.isOpen,
      signal.access.co.isGreen
    );
    attribute untouched: Access_Point[*] = railway.access_points->select {
      in a: Access_Point;
      a != signal.access & a != signal.access.co
    };

    new Railway_Network(
      access_points = untouched + (access_after, coAccess_after), 
      trains = railway.trains
    )
  }

  calc def SecureState {
    in railway: Railway_Network;
    return : Boolean;

    railway.trains->forAll {
      in t1: Train;
      railway.trains->forAll {
        in t2: Train;
        Close(t1.position, t2.position, railway) implies (t1 == t2)
      }
    }
  }

  calc def ReachableStates {
    in c: Controller;
    in input: Signal[*];
  }
}