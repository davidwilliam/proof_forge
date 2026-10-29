import EulerLending.Spec
open EulerLending

-- b1ee326 case 0 step 5: account 1 owes 390000000000000000000000000 against 320000000000000000000000000
example : ¬ Healthy ⟨320000000000000000000000000, 390000000000000000000000000⟩ := by decide

-- b1ee326 case 12 step 5: account 0 owes 17 against 16
example : ¬ Healthy ⟨16, 17⟩ := by decide

