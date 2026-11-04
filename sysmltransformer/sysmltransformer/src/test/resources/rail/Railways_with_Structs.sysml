package Structs {

  enum def Section {
    s1; s2; s3; s4; s5; s6; s7;
  }

  attribute def Access {
    enum co: Access;
    enum sect: Section;
    attribute isOpen: Boolean;
    attribute isGreen: Boolean;
  }

  attribute def Train {
    attribute position: Access;
  }

  attribute def Schienennetz {
    attribute stuecke: Access[*];
    attribute trains: Train[*];
  }

  attribute t1: Train {
    ::> position = a11;
  }

  attribute t2: Train {
    ::> position = a43;
  }

  attribute a11 : Access {
    ::> co = a73;
    ::> sect = Section::s1;
    ::> isOpen = false;
    ::> isGreen = true;
  }

  attribute a73 : Access { 
    ::> co = a11;
    ::> sect = Section::s1;
    ::> isOpen = false;
    ::> isGreen = true;
  }

  attribute a12 : Access;
  attribute a21 : Access;
  attribute a22 : Access;
  attribute a31 : Access;
  attribute a32 : Access;
  attribute a41 : Access;
  attribute a42 : Access;
  attribute a43 : Access;
  attribute a51 : Access;
  attribute a52 : Access;
  attribute a61 : Access;
  attribute a62 : Access;
  attribute a71 : Access;
  attribute a72 : Access;


  private import ControlFunctions::exists;
  private import ScalarValues::Boolean;

  calc def Close {
    in a: Access;
    in b: Access;
    in schienen: Schienennetz;
    return : Boolean;

    a.sect == b.sect
    | (schienen.stuecke)->exists { 
        in c: Access; 
        a.sect == (c.co).sect & c.sect == b.sect 
    }
  }

  calc def Possible_Switch {
    in a: Access;
    in b: Access;
    return : Boolean;  

    a.sect == b.sect 
        & (a,b) != (a42,a43)
        & (a,b) != (a43,a42)
        & (a,b) != (a72,a71)
        & (a,b) != (a71,a72)
  }

  attribute def Enters {
    attribute train: Train;
    attribute access: Access;
  }

  attribute def OpenUp {
    attribute a: Access;
    attribute b: Access;
  }

  attribute def SetColor {
    attribute access: Access;
    attribute b: Boolean;
  }

  private import Collections::Map;
  private import ScalarValues::String;
  private import ControlFunctions::forAll;

  calc def SafeLight {
    in schienen: Schienennetz;
    in a: Access;
    return : Boolean;  

    a.isOpen & a.co.isOpen & 
      (schienen.stuecke)->forAll {
        in b: Access;
        (Close(a, b) & b.isGreen) 
          implies (
            a == b | (a.sect == b.co.sect & a.co.sect == b.sect) 
          )
      }
  }

  calc def IsFree {
    in t: Train[*];
    in a: Access;
    return : Boolean;

    t->forAll { 
      in t: Train;
      t.position.sect != a.sect
    }
  }

  calc def SafeGreen {
    in schienen: Schienennetz;
    in a: Access;
    return : Boolean;  

    SafeLight(schienen, a) 
    & (schienen.stuecke)->forAll {
      in b: Access;
      Close(a, b) & a.co.sect != b.sect implies IsFree(schienen.trains, b)
    }
  }

  calc def Protected {
    in schienen: Schienennetz;
    in s: Section;
    return : Boolean;  

    (schienen.stuecke)->forAll {
      in a: Access;
      a.sect == s implies not a.isGreen & not a.co.isGreen
    }
  }

  enum def Reject {
    Reject;
  }

  calc def Phys_Trans_Enter {
    in schienen: Schienennetz;
    in signal: Enters;
    return : Schienennetz;

    attribute t0: Train = signal.train;
    attribute a: Access = signal.access;

    attribute untouched: Train[*] = schienen.trains->select {
      in t: Train;
      t != t0
    };

    if a.co.sect == t0.position.sect ? 
      new Schienennetz(
        stuecke = schienen.stuecke, 
        trains = untouched + new Train(a)
      )
    else
      schienen
  }

  calc def Phys_Trans_Open {
    in schienen: Schienennetz;
    in signal: OpenUp;
    return : Schienennetz;


  }

  private import ControlFunctions::'select';

  calc def Phys_Trans_Color {
    in schienen: Schienennetz;
    in signal: SetColor;
    return : Schienennetz;

    attribute betroffen: Access = new Access(
      signal.access.co, 
      signal.access.sect,
      signal.access.isOpen,
      signal.b
    );
    attribute coAccess: Access = new Access(
      betroffen,
      signal.access.co.sect,
      signal.access.co.isOpen,
      signal.access.co.isGreen
    );
    attribute untouched: Access[*] = schienen.stuecke->select {
      in a: Access;
      a != signal.access & a != signal.access.co
    };

    new Schienennetz(
      stuecke = untouched + (betroffen, coAccess), 
      trains = schienen.trains
    )
  }

  port i: Signal;
  port o: Reject;

  state def Control_Railway {

    attribute schienen: Schienennetz {
      ::> stuecke = (a11, a12, a21, a22, a31, a32, a41, a42, a43, a51, a52, a61,
                    a62, a71, a72, a73);
      ::> trains = (t1, t2);
    }

    state S;

    transition
      first S
      accept openUp : OpenUp via i
      if IsFree(schienen.trains, openUp.a) & Protected(schienen, openUp.a.sect)
      do action { assign schienen := Phys_Trans_Open(schienen, openUp); }
      then S;

  }
}