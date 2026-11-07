private import ScalarValues::Boolean;
private import ScalarValues::Natural;
private import ControlFunctions::forAll;
private import ControlFunctions::'implies';

part def LightControl_HLR1 {
  port switchstatus: Booleans;
  port alarmstatus: Booleans;
  port onOffCmd: ~Booleans;

  assert constraint {
    (all Natural)->forAll{ 
      in t: Natural; 
      t+1 < alarmstatus.val.len() & t+1 < switchstatus.val.len()
      'implies' 
      alarmstatus.val.nth(t+1) & alarmstatus.val.nth(t) 
      'implies'
      onOffCmd.val.nth(t+1) != onOffCmd.val.nth(t)
    }
  }

}