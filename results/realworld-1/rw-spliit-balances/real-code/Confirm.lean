import Allocation.Spec
open Allocation

-- 1.21.0 case 0, REQ-CONSERVATION: shares add up to 99, amount is 100
example : ¬ ConservesOn 100 [33, 33, 33] := by decide

-- 1.21.0 case 2, REQ-CONSERVATION: shares add up to 739928270, amount is 739928271
example : ¬ ConservesOn 739928271 [45235789, 105011654, 29080150, 59775865, 29080150, 156709699, 21002331, 129245113, 53313609, 111473910] := by decide

