private import Signals::*;
private import Railway::*;
private import Rules::*;

part def Controller {
  port i: Signal;
  port o: Reject;

  state def Control_Railway {

    attribute railway: Railway_Network {
      ::> access_points = (a11, a12, a21, a22, a31, a32, a41, a42, a43, a51, 
                           a52, a61, a62, a71, a72, a73);
      ::> trains = (t1, t2);
    }

    state S;

    transition
      first S
      accept openUp : OpenUp via i
      if IsFree(railway.trains, openUp.a) & Protected(railway, openUp.a.sect)
      do action { assign railway := Phys_Trans_Open(railway, openUp); }
      then S;

    transition
      first S
      accept openUp : OpenUp via i
      if not (IsFree(railway.trains, openUp.a) & Protected(railway, openUp.a.sect))
      do action { send Reject :: Reject via o; }
      then S;

    transition
      first S
      accept setColor : SetColor via i
      if setColor.b & SafeGreen(railway, setColor.access)
      do action { assign railway := Phys_Trans_Color(railway, setColor); }
      then S;

    transition
      first S
      accept setColor : SetColor via i
      if setColor.b & not SafeGreen(railway, setColor.access)
      do action { send Reject :: Reject via o; }
      then S;

    transition
      first S
      accept setColor : SetColor via i
      if not setColor.b
      do action { assign railway := Phys_Trans_Color(railway, setColor); }
      then S;

    transition
      first S
      accept enters : Enters via i
      if enters.access.isGreen
      do action { assign railway := Phys_Trans_Enter(railway, enters); }
      then S;

    transition
      first S
      accept enters : Enters via i
      if not enters.access.isGreen
      do action { send Reject :: Reject via o; }
      then S;
  }
}