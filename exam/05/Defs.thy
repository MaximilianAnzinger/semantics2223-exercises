theory Defs
  imports Main
begin

datatype bits = B nat | Any
datatype entry = Unchanged ("'_'_'_'_'_'_'_'_'_") | None | Some bits

end
