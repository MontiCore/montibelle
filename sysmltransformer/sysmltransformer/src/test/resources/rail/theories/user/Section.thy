theory Section
  imports "HOL-Library.Countable_Set"

begin

datatype Section = sec1 | sec2 | sec3 | sec4 | sec5 | sec6 | sec7

instance Section::countable
  apply(intro_classes)
  by(countable_datatype)

end
