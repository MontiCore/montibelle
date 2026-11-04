part def Bob_LLR specializes Bob_HLR {
  timing delayed;

  port input:   ~Data_Bool_Tuples;
  port control:  Booleans;
  port output:   Data;

  attribute init_ctrl: boolean;

  #tsyn exhibit state BobAutomaton {
    entry action {
      assign ctrl := init_ctrl;
    }
    attribute ctrl: boolean;
    state S;

    then S;

    transition
      first S
      if input.val == Eps
      do action {
        send Eps to control.val;
        send Eps to output.val;
        assign ctrl := ctrl;
      }
      then S;

    transition
      first S
      if input.val[1] == ctrl
      do action {
        send input.val[1] to control.val;
        send input.val[0] to output.val;
        assign ctrl := not input.val[1];
      }
      then S;

    transition
      first S
      if input.val[1] != ctrl
      do action{
        send input.val[1] to control.val;
        send Eps to output.val;
        assign ctrl := ctrl;
      }
      then S;
  }
}
