theory CtrlEnum
  imports "HOL-Library.Countable_Set"

begin

datatype CtrlEnum = ACK | NAK

instance CtrlEnum::countable
  apply(intro_classes)
  by(countable_datatype)

end
