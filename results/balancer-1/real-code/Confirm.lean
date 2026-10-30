import BalancerSwap.StableMath
open BalancerSwap

def pool2 (w o : Nat) : Pool where
  n := 2
  balance k := if k = 0 then w else if k = 1 then o else 0
  rate k := if k = 1 then 1058132408689971699 else 1000000000000000000
  fee := 100000000000000

-- case 0: D 137893 -> 2445
example : value (stableMath 200000 2) (pool2 889 1472) < value (stableMath 200000 2) (pool2 67000 67000) := by decide

-- case 7: D 137893 -> 3852
example : value (stableMath 200000 2) (pool2 5472 4) < value (stableMath 200000 2) (pool2 67000 67000) := by decide

-- case 10: D 137893 -> 13851
example : value (stableMath 200000 2) (pool2 19485 15) < value (stableMath 200000 2) (pool2 67000 67000) := by decide

-- case 18: D 137893 -> 34172
example : value (stableMath 200000 2) (pool2 49363 32) < value (stableMath 200000 2) (pool2 67000 67000) := by decide

-- case 33: D 137893 -> 3156
example : value (stableMath 200000 2) (pool2 3165 68) < value (stableMath 200000 2) (pool2 67000 67000) := by decide

-- case 47: D 137893 -> 125233
example : value (stableMath 200000 2) (pool2 437009 9) < value (stableMath 200000 2) (pool2 67000 67000) := by decide

