theory ActionEnum
  imports "HOL-Library.Countable_Set"

begin

datatype ActionEnum = Bob_plus_Eve_request_Camera_accepts | Alice_plus_Eve_request_Camera_accepts | Bob_plus_Eve_request_Camera_denies | Alice_plus_Eve_request_Camera_denies | Bob_without_Eve_request_Camera_accepts | Alice_without_Eve_request_Camera_accepts | Bob_without_Eve_request_Camera_denies | Alice_without_Eve_request_Camera_denies | Bob_wants_to_exit_cockpit | Alice_wants_to_exit_cockpit

instance ActionEnum::countable
  apply(intro_classes)
  by(countable_datatype)

end
