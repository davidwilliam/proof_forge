import Allocation.Spec
open Allocation

-- v6.18.0 case 0, REQ-CONSERVATION: shares add up to 700272, amount is 700273
example : ¬ ConservesOn 700273 [61565, 61565, 61565, 61565, 61565, 61565, 61565, 60953, 52091, 52091, 52091, 52091] := by decide

-- v6.18.0 case 1, REQ-WITHIN-ONE-UNIT: share 2 is -17, exact share is -5160001/325244
example : ¬ WithinOneUnitOn (-77) [5306, 33936, 67013, 63691, 53075, 39755, 62468] [(-2), (-8), (-17), (-15), (-12), (-9), (-14)] := by decide

-- v6.18.0 case 1, REQ-LARGEST-REMAINDER: share 1 was rounded up and share 2 rounded down, but share 2 has the larger remainder
example : ¬ LargestRemainderOn (-77) [5306, 33936, 67013, 63691, 53075, 39755, 62468] [(-2), (-8), (-17), (-15), (-12), (-9), (-14)] := by decide

-- v6.18.0 case 15, REQ-CONSERVATION: shares add up to 908440, amount is 908441
example : ¬ ConservesOn 908441 [47379, 861061] := by decide

-- v6.19.0 case 0, REQ-WITHIN-ONE-UNIT: share 0 is 61566, exact share is 827623467376091945300/13443134288012976
example : ¬ WithinOneUnitOn 700273 [1181858314366100, 1181858314366100, 1181858314366100, 1181858314366100, 1181858314366100, 1181858314366100, 1181858314366100, 1170126087450276, 1000000000000000, 1000000000000000, 1000000000000000, 1000000000000000] [61566, 61565, 61565, 61565, 61565, 61565, 61565, 60953, 52091, 52091, 52091, 52091] := by decide

-- v6.19.0 case 0, REQ-LARGEST-REMAINDER: share 0 was rounded up and share 7 rounded down, but share 7 has the larger remainder
example : ¬ LargestRemainderOn 700273 [1181858314366100, 1181858314366100, 1181858314366100, 1181858314366100, 1181858314366100, 1181858314366100, 1181858314366100, 1170126087450276, 1000000000000000, 1000000000000000, 1000000000000000, 1000000000000000] [61566, 61565, 61565, 61565, 61565, 61565, 61565, 60953, 52091, 52091, 52091, 52091] := by decide

-- v6.19.0 case 1, REQ-WITHIN-ONE-UNIT: share 2 is -17, exact share is -5160001/325244
example : ¬ WithinOneUnitOn (-77) [5306, 33936, 67013, 63691, 53075, 39755, 62468] [(-2), (-8), (-17), (-15), (-12), (-9), (-14)] := by decide

-- v6.19.0 case 1, REQ-LARGEST-REMAINDER: share 1 was rounded up and share 2 rounded down, but share 2 has the larger remainder
example : ¬ LargestRemainderOn (-77) [5306, 33936, 67013, 63691, 53075, 39755, 62468] [(-2), (-8), (-17), (-15), (-12), (-9), (-14)] := by decide

