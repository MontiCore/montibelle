private import ScalarValues::Boolean;
private import ScalarValues::Natural;
private import ControlFunctions::forAll;
private import ControlFunctions::'implies';

part def Flasher_HLR {
  port input: Booleans;
  port output: ~Booleans;

  assert constraint {
    (all Natural)->forall {
      in t: Natural;
      
      t+1 < input.val.len()
      'implies'
      output.val.nth(t+1) != output.val.nth(t)
        & output.val.first() == input.val.first()
        & output.val.len() == input.val.len()
    }
  }

}