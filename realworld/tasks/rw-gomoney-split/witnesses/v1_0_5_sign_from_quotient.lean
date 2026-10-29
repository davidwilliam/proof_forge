import Solution
/-!
Kernel-checked refutation of the go-money 1.0.5 port (`attacks/v1_0_5_sign_from_quotient.lean`)
on the input of issue #106: -2 cents split three ways.
-/
open EqualSplit

theorem port_output : split (-2) 3 = some [1, 1, 0] := by decide

theorem port_refuted_conservation : ¬ Conserves split :=
  fun h => absurd (h (-2) 3 [1, 1, 0] port_output) (by decide)

theorem port_refuted_sign : ¬ Sign split :=
  fun h => absurd (h (-2) 3 [1, 1, 0] port_output) (by decide)
