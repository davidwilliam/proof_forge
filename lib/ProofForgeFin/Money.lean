import ProofForgeFin.Money.Round
import ProofForgeFin.Money.Allocation
import ProofForgeFin.Money.Hamilton
import ProofForgeFin.Money.Split
import ProofForgeFin.Money.Currency
/-!
# ProofForgeFin.Money

Money in minor units: rounding modes, allocation and splits, currencies with different
exponents, interest, currency conversion and fees.

* `ProofForgeFin.Money.Round`: the rounding modes of money libraries on integer fractions,
  their exact bounds and the relations between them.
* `ProofForgeFin.Money.Allocation`: requirements of an allocation by ratios, the implications
  between them, the symmetric convention for negative amounts, and the remainder-to-the-first
  methods.
* `ProofForgeFin.Money.Hamilton`: allocation by the largest-remainder method.
* `ProofForgeFin.Money.Split`: equal splits of signed amounts.
* `ProofForgeFin.Money.Currency`: currencies, minor units, and rescaling between exponents.
-/
