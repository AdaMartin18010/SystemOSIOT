theory TestDef
  imports Main
begin

definition mytest :: "nat => nat => bool" where
  "mytest x y = !a. a = a"

end
