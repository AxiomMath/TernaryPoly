module

public import TernaryPeriodPolynomials.ModularForm.ThreeTerm.Map
public import TernaryPeriodPolynomials.ModularForm.Hecke.Consumer

@[expose] public section


noncomputable section
open MvPolynomial

namespace TernaryPoly.BinaryCuspPeriod

/-- The unrestricted actual map detects every normalized actual simultaneous prime eigenform. -/
theorem extreme_periodMap_normalized_ne_zero {d : ℕ} (hd : Even d) (hgt : 4 < d)
    (f : Forms d) (ev : Nat.Primes → ℂ) (hf : BinaryCuspHecke.IsPrimeEigenform f ev)
    (h1 : coefficients f 1 = 1) : BinaryComplexPeriod.extreme ℂ d (periodMap d hd f) ≠ 0 := by
  rw [extreme_periodMap]
  exact BinaryCuspHecke.normalized_eigen_extreme_ne_zero hgt f ev hf h1

/-- Scalar normalization removes the normalization hypothesis for the actual map's extreme
coordinate. No eigenform existence or spanning theorem is assumed or asserted. -/
theorem extreme_periodMap_eigen_ne_zero {d : ℕ} (hd : Even d) (hgt : 4 < d)
    (f : Forms d) (ev : Nat.Primes → ℂ) (hf : BinaryCuspHecke.IsPrimeEigenform f ev)
    (hne : f ≠ 0) : BinaryComplexPeriod.extreme ℂ d (periodMap d hd f) ≠ 0 := by
  have h := (BinaryCuspHecke.actual_normalization_and_extreme hgt f ev hf hne).2.2
  rw [extreme_periodMap]
  intro hz
  apply h
  rw [oddPeriod_smul, coeff_smul, hz, smul_zero]

/-- A nonzero actual simultaneous prime eigenform has nonzero image in the actual period space. -/
theorem periodMap_eigen_ne_zero {d : ℕ} (hd : Even d) (hgt : 4 < d)
    (f : Forms d) (ev : Nat.Primes → ℂ) (hf : BinaryCuspHecke.IsPrimeEigenform f ev)
    (hne : f ≠ 0) : periodMap d hd f ≠ 0 := by
  intro hz
  apply extreme_periodMap_eigen_ne_zero hd hgt f ev hf hne
  rw [hz, map_zero]

end TernaryPoly.BinaryCuspPeriod
