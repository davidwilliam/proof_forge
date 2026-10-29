import Allocation.Spec
open Allocation

-- v3.0.9 case 0, REQ-WITHIN-ONE-UNIT: share 0 is 1, exact share is 0/10
example : ¬ WithinOneUnitOn 5 [0, 7, 3] [1, 3, 1] := by decide

-- v3.0.9 case 0, REQ-ZERO-RATIO: share 0 has ratio 0 and receives 1
example : ¬ ZeroRatioOn [0, 7, 3] [1, 3, 1] := by decide

-- v3.0.9 case 0, REQ-LARGEST-REMAINDER: share 0 was rounded up and share 1 rounded down, but share 1 has the larger remainder
example : ¬ LargestRemainderOn 5 [0, 7, 3] [1, 3, 1] := by decide

-- v3.0.9 case 2, REQ-LARGEST-REMAINDER: share 0 was rounded up and share 1 rounded down, but share 1 has the larger remainder
example : ¬ LargestRemainderOn 9999 [75, 25] [7500, 2499] := by decide

-- v3.0.9 case 3, REQ-LARGEST-REMAINDER: share 0 was rounded up and share 3 rounded down, but share 3 has the larger remainder
example : ¬ LargestRemainderOn (-231094825) [6890, 663, 4242, 8376, 7961, 6634, 4969] [(-40071557), (-3855942), (-24671051), (-48713987), (-46300388), (-38582688), (-28899212)] := by decide

-- v3.0.9 case 32, REQ-WITHIN-ONE-UNIT: share 3 is 1, exact share is 0/35
example : ¬ WithinOneUnitOn (-82) [10, 1, 2, 0, 6, 10, 6] [(-23), (-2), (-4), 1, (-15), (-24), (-15)] := by decide

-- v3.0.9 case 32, REQ-ZERO-RATIO: share 3 has ratio 0 and receives 1
example : ¬ ZeroRatioOn [10, 1, 2, 0, 6, 10, 6] [(-23), (-2), (-4), 1, (-15), (-24), (-15)] := by decide

-- v3.0.9 case 32, REQ-SIGN: share 1 has the wrong sign for amount -82
example : ¬ SignOn (-82) [(-23), (-2), (-4), 1, (-15), (-24), (-15)] := by decide

-- v3.1.0 case 1, REQ-VALID-SUCCEEDS: valid input was refused
example : Valid 1 [1, 1] := by decide

-- v3.1.0 case 2, REQ-LARGEST-REMAINDER: share 0 was rounded up and share 1 rounded down, but share 1 has the larger remainder
example : ¬ LargestRemainderOn 9999 [75, 25] [7500, 2499] := by decide

-- v3.1.0 case 3, REQ-LARGEST-REMAINDER: share 0 was rounded up and share 3 rounded down, but share 3 has the larger remainder
example : ¬ LargestRemainderOn (-231094825) [6890, 663, 4242, 8376, 7961, 6634, 4969] [(-40071557), (-3855942), (-24671051), (-48713987), (-46300388), (-38582688), (-28899212)] := by decide

-- v3.1.0 case 47, REQ-WITHIN-ONE-UNIT: share 1 is -33, exact share is -1088/32
example : ¬ WithinOneUnitOn (-272) [3, 4, 9, 2, 6, 3, 5] [(-25), (-33), (-77), (-17), (-51), (-26), (-43)] := by decide

-- v3.1.0 case 97, REQ-VALID-SUCCEEDS: valid input was refused
example : Valid 4 [3059, 5957, 933, 2840] := by decide

-- v3.2.0 case 2, REQ-LARGEST-REMAINDER: share 0 was rounded up and share 1 rounded down, but share 1 has the larger remainder
example : ¬ LargestRemainderOn 9999 [75, 25] [7500, 2499] := by decide

-- v3.2.0 case 3, REQ-LARGEST-REMAINDER: share 0 was rounded up and share 3 rounded down, but share 3 has the larger remainder
example : ¬ LargestRemainderOn (-231094825) [6890, 663, 4242, 8376, 7961, 6634, 4969] [(-40071557), (-3855942), (-24671051), (-48713987), (-46300388), (-38582688), (-28899212)] := by decide

-- v3.2.0 case 47, REQ-WITHIN-ONE-UNIT: share 1 is -33, exact share is -1088/32
example : ¬ WithinOneUnitOn (-272) [3, 4, 9, 2, 6, 3, 5] [(-25), (-33), (-77), (-17), (-51), (-26), (-43)] := by decide

