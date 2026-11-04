theory Reject
  imports "HOL-Library.Countable_Set"

begin

datatype Reject = Reject

instance Reject::countable
  apply(intro_classes)
  by(countable_datatype)

end
