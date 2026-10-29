import ClmmMath.Spec
open ClmmMath

-- original case 0, REQ-DELTA-A-COVERS
example : ∀ shlw : Shlw, getDeltaA shlw 60257519765924248467716150 60863087478126617965993239 10365647984364446732462244378333008 true = some 1 → ¬ DeltaACovers shlw := by
  intro shlw h hc; exact absurd (hc _ _ _ _ h) (by decide)

-- original case 2, REQ-SHLW-EXACT
example : ∀ shlw : Shlw, shlw 6277101735386680763835789423207666908085499738337898853712 = (9075487151368008912317032979326758767558656, false) → ¬ ShlwExact shlw := by
  intro shlw h hex; have e := hex 6277101735386680763835789423207666908085499738337898853712 (by rw [h]); rw [h] at e; exact absurd e (by decide)

-- original case 3, REQ-SHLW-EXACT
example : ∀ shlw : Shlw, shlw 6277101735386680763835789423207666416102355444464034512896 = (0, false) → ¬ ShlwExact shlw := by
  intro shlw h hex; have e := hex 6277101735386680763835789423207666416102355444464034512896 (by rw [h]); rw [h] at e; exact absurd e (by decide)

-- original case 5, REQ-DELTA-A-COVERS
example : ∀ shlw : Shlw, getDeltaA shlw 60257519765924248467716150 60861982675731563055069238 10384593717069655257060992658440192 true = some 0 → ¬ DeltaACovers shlw := by
  intro shlw h hc; exact absurd (hc _ _ _ _ h) (by decide)

-- original case 10, REQ-SHLW-EXACT
example : ∀ shlw : Shlw, shlw 6277101735386683105903941386108044688699448269690241981769 = (43203531802445514110796897935841104923241742605814819106848768, false) → ¬ ShlwExact shlw := by
  intro shlw h hex; have e := hex 6277101735386683105903941386108044688699448269690241981769 (by rw [h]); rw [h] at e; exact absurd e (by decide)

-- original case 43, REQ-DELTA-A-COVERS
example : ∀ shlw : Shlw, getDeltaA shlw 60257519765924248467716150 60863087478126617965993239 10365647984364446732462244378333008 true = some 1 → ¬ DeltaACovers shlw := by
  intro shlw h hc; exact absurd (hc _ _ _ _ h) (by decide)

-- pr6 case 3, REQ-SHLW-EXACT
example : ∀ shlw : Shlw, shlw 6277101735386680763835789423207666416102355444464034512896 = (0, false) → ¬ ShlwExact shlw := by
  intro shlw h hex; have e := hex 6277101735386680763835789423207666416102355444464034512896 (by rw [h]); rw [h] at e; exact absurd e (by decide)

-- pr6 case 5, REQ-DELTA-A-COVERS
example : ∀ shlw : Shlw, getDeltaA shlw 60257519765924248467716150 60861982675731563055069238 10384593717069655257060992658440192 true = some 0 → ¬ DeltaACovers shlw := by
  intro shlw h hc; exact absurd (hc _ _ _ _ h) (by decide)

-- pr6 case 22, REQ-SHLW-EXACT
example : ∀ shlw : Shlw, shlw 6277101735386680763835789423207666416102355444464034512896 = (0, false) → ¬ ShlwExact shlw := by
  intro shlw h hex; have e := hex 6277101735386680763835789423207666416102355444464034512896 (by rw [h]); rw [h] at e; exact absurd e (by decide)

