package Functional {

  enum def Section {
    s1; s2; s3; s4; s5; s6; s7;
  }

  enum def Access {
    a11;
    a12;
    a21;
    a22;
    a31;
    a32;
    a41;
    a42;
    a43;
    a51;
    a52;
    a61;
    a62;
    a71;
    a72;
    a73;
  }

  calc def Sect {
    in a : Access;
    return : Section;

    if(a == Access::a11) ?
      Section::s1
    else if(a == Access::a12) ?
      Section::s1
    else if(a == Access::a21) ?
      Section::s2
    else 
      Section::s3
  }

  calc def Co {
    in a : Access;
    return : Access;

    if(a == Access::a11) ?
      Access::a73
    else if(a == Access::a12) ?
      Access::a21
    else if(a == Access::a21) ?
      Access::a12
    else
      Access::a31
  }

  private import ControlFunctions::exists;
  private import ScalarValues::Boolean;

  calc def Close {
    in a: Access;
    in b: Access;
    return : Boolean;

    Sect(a) == Sect(b) 
        | (all Access)->exists { 
            in c: Access; 
            Sect(a) == Sect(Co(c)) & Sect(c) == Sect(b) 
        }
  }

  calc def Possible_Switch {
    in a: Access;
    in b: Access;
    return : Boolean;  

    Sect(a) == Sect(b) 
        & (a,b) != (Access::a42,Access::a43)
        & (a,b) != (Access::a43,Access::a42)
        & (a,b) != (Access::a72,Access::a71)
        & (a,b) != (Access::a71,Access::a72)
  }

  enum def Train {
    T1;
    T2;
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
    in s_green: Map;
    in s_pos: Map;
    in s_open: Map;
    in a: Access;
    return : Boolean;  

  }

  calc def SafeGreen {
    in s_green: Map;
    in s_pos: Map;
    in s_open: Map;
    in a: Access;
    return : Boolean;  

  }

  enum def Reject {
    Reject;
  }

  port i: Signal;
  port o: Reject;

  state def Control_Railway {




    state S;

  }
}