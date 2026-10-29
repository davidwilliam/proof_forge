import EqualSplit.Spec
open EqualSplit

-- v1.0.3 case 0, REQ-VALID-SUCCEEDS: splitting among 4 parties failed
example : 0 < 4 := by decide

-- v1.0.3 case 1, REQ-VALID-SUCCEEDS: splitting among 3 parties failed
example : 0 < 3 := by decide

-- v1.0.3 case 5, REQ-VALID-SUCCEEDS: splitting among 9 parties failed
example : 0 < 9 := by decide

-- v1.0.5 case 1, REQ-CONSERVATION: shares add up to 2, amount is -2
example : ¬ ConservesOn (-2) [1, 1, 0] := by decide

-- v1.0.5 case 1, REQ-WITHIN-ONE-UNIT: share 1 is a unit or more away from -2/3
example : ¬ WithinOneUnitOn (-2) 3 [1, 1, 0] := by decide

-- v1.0.5 case 1, REQ-SIGN: share 1 has the wrong sign for amount -2
example : ¬ SignOn (-2) [1, 1, 0] := by decide

-- v1.0.5 case 48, REQ-CONSERVATION: shares add up to 9, amount is -9
example : ¬ ConservesOn (-9) [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0] := by decide

-- v1.0.5 case 48, REQ-WITHIN-ONE-UNIT: share 1 is a unit or more away from -9/11
example : ¬ WithinOneUnitOn (-9) 11 [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0] := by decide

-- v1.0.5 case 48, REQ-SIGN: share 1 has the wrong sign for amount -9
example : ¬ SignOn (-9) [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0] := by decide

