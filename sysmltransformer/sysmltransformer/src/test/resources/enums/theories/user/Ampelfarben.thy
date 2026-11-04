theory Ampelfarben
  imports "HOL-Library.Countable_Set"

begin

datatype Ampelfarben = Rot | Gruen | Gelb

instance Ampelfarben::countable
  apply(intro_classes)
  by(countable_datatype)

end
