part def SecurityGate_LLR {
  port input: Action;

  #delayed exhibit state behavior {
    entry;
    then Bob_Alice;

    state Bob_Alice;
    state Bob;
    state Alice;
    state Bob_Alice_Eve;
    state Alarm_Eve_detected;

    transition
      first Bob_Alice
      accept data : ActionEnum via input
      if input.data == ActionEnum::Bob_wants_to_exit_cockpit
      then Alice;

    transition
      first Bob_Alice
      accept data : ActionEnum via input
      if input.data == ActionEnum::Alice_wants_to_exit_cockpit
      then Bob;

    transition
      first Bob_Alice
      accept data : ActionEnum via input
      if input.data != ActionEnum::Bob_wants_to_exit_cockpit & input.data != ActionEnum::Alice_wants_to_exit_cockpit
      then Bob_Alice;

    transition
      first Bob
      accept data : ActionEnum via input
      if input.data == ActionEnum::Alice_plus_Eve_request_Camera_accepts
      then Bob_Alice_Eve;

    transition
      first Bob
      accept data : ActionEnum via input
      if input.data == ActionEnum::Alice_without_Eve_request_Camera_accepts
      then Bob_Alice;

    transition
      first Bob
      accept data : ActionEnum via input
      if input.data == ActionEnum::Alice_plus_Eve_request_Camera_denies
      then Alarm_Eve_detected;

    transition
      first Bob
      accept data : ActionEnum via input
      if input.data != ActionEnum::Alice_plus_Eve_request_Camera_accepts | input.data != ActionEnum::Alice_without_Eve_request_Camera_accepts | input.data != ActionEnum::Alice_without_Eve_request_Camera_denies
      then Bob;

    transition
      first Alice
      accept data : ActionEnum via input
      if input.data == ActionEnum::Bob_plus_Eve_request_Camera_accepts
      then Bob_Alice_Eve;

    transition
      first Alice
      accept data : ActionEnum via input
      if input.data == ActionEnum::Bob_without_Eve_request_Camera_accepts
      then Bob_Alice;

    transition
      first Alice
      accept data : ActionEnum via input
      if input.data == ActionEnum::Bob_plus_Eve_request_Camera_denies
      then Alarm_Eve_detected;

    transition
      first Alice
      accept data : ActionEnum via input
      if input.data != ActionEnum::Bob_plus_Eve_request_Camera_accepts | input.data != ActionEnum::Bob_without_Eve_request_Camera_accepts | input.data != ActionEnum::Bob_without_Eve_request_Camera_denies
      then Alice;

    transition
      first Bob_Alice_Eve
      accept data : ActionEnum via input
      then Bob_Alice_Eve;

    transition
      first Alarm_Eve_detected
      accept data : ActionEnum via input
      then Alarm_Eve_detected;

    transition
      first Bob_Alice
      accept Tick
      then Bob_Alice;

    transition
      first Bob
      accept Tick
      then Bob;

    transition
      first Alice
      accept Tick
      then Alice;

    transition
      first Bob_Alice_Eve
      accept Tick
      then Bob_Alice_Eve;

    transition
      first Alarm_Eve_detected
      accept Tick
      then Alarm_Eve_detected;
  }
}
