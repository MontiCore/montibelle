private import Railway::*;
private import Rules::*;
private import ControlFunctions::forAll;

requirement Controller_Security {
    subject c: Controller; 
    attribute input: Signal[*];

    require constraint {
      ReachableStates(c, input)->forAll {
        in st: Railway_Network;
        SecureState(st)
      }
    }
}