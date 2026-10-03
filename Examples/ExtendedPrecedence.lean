import LeanPoo.C4.Linearize

namespace LeanPoo.Examples.ExtendedPrecedence
open C4 Precedence

private def ordinary := mergePrefix [["X", "S", "T"], ["Y"]] [["X"], ["Y"]] []
private def exempt := mergePrefix [["X", "S", "T"], ["Y"]] [["X"], ["Y"]] ["X", "S", "T"]
#guard ordinary.toOption.map (·.output) == some ["X", "S", "T", "Y"]
#guard exempt.toOption.map (fun result => result.output ++ ["X", "S", "T"]) == some ["Y", "X", "S", "T"]
#eval ordinary.map (·.output)
#eval exempt.map (fun result => result.output ++ ["X", "S", "T"])
end LeanPoo.Examples.ExtendedPrecedence
