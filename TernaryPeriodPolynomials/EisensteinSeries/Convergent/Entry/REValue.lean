module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REMain
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBadMain
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.ClassLevel

@[expose] public section


/-!
# R-e: The scalars: formula, nonvanishing, comparison with the printed constant

`rFull_eq_lseries_ratio` (`r_full = L(h,n+1)/L(h,n+2)`), `rFull_ne_zero`, `rFull_eq_nine_mul` (`r_full = 9·c₃·r_print`), `printedScalar_ne_zero_of_frozen` (from the `global_entry_ne_zero`) and `entryScalar_rPrint` (the sign: `entryScalar n r_print = -(printed scalar)`).

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The classical local polynomial at `3`. -/
def poly3 (a s : ℂ) (k : ℂ) : ℂ := 1 - a * (3 : ℂ) ^ (-s) + (3 : ℂ) ^ (k - 1 - 2 * s)

theorem primesEquiv_placeThree : Rat.HeightOneSpectrum.primesEquiv placeThree = primeThree :=
  Equiv.apply_symm_apply _ _

namespace SphericalEntryData

variable {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)

include S

theorem weight_k : (-2 * S.halfWeight : ℤ) = (n : ℤ) + 3 := by
  have := S.weight
  omega

theorem weight_gt : 6 < (-2 * S.halfWeight : ℤ) := by
  have := S.large
  have := S.weight
  omega

theorem normalizedEigenform : IsNormalizedEigenform S.form := ⟨S.normalized, S.eigenvalues, S.relations⟩

/-- `r` has the Euler product formula: the ratio of the `L`-values with the factor at `3` omitted, times the
local factor at `3`. -/
theorem value_eq : S.value = globalEntryRatio S.form := by
  unfold SphericalEntryData.value
  exact removeEulerThree_ratio_eq S.weight_gt S.form S.normalizedEigenform

/-- The Fourier coefficient at `3` is the Hecke eigenvalue at `3`. -/
theorem coeff_three : fourierCoeff S.form 3 = S.eigenvalues primeThree := by
  have initial' : (UpperHalfPlane.qExpansion 1 S.form).coeff 1 = 1 := by
    have heq := fourierCoeff_eq S.form
    exact (congrFun heq 1).symm.trans S.normalized
  have period : (1 : ℝ) ∈ levelOne.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using levelOne.strictWidthInfty_mem_strictPeriods
  have first := cuspForm_hecke_prime_coefficient S.form period primeThree (S.eigenvalues primeThree)
    (S.relations primeThree) initial'
  exact (congrFun (fourierCoeff_eq S.form) 3).trans first

theorem euler3_eq : S.euler3 =
    poly3 (S.eigenvalues primeThree) ((n : ℂ) + 2) ((n : ℂ) + 3) /
      poly3 (S.eigenvalues primeThree) ((n : ℂ) + 1) ((n : ℂ) + 3) := by
  unfold SphericalEntryData.euler3 SphericalEntryData.localEigenvalue
  rw [← entryExponent_eq n]
  rw [cuspLocalPadicEulerFactor_cohomological D.cusp S.sphericalCusp D.cohomological placeThree S.halfWeight
    S.weight (S.eigenvalues (Rat.HeightOneSpectrum.primesEquiv placeThree))]
  rw [primesEquiv_placeThree]
  have h3 : (primeThree : ℕ) = 3 := rfl
  rw [h3, classicalPrimeEulerPolynomial_eq 3 (by norm_num), classicalPrimeEulerPolynomial_eq 3 (by norm_num)]
  unfold poly3
  push_cast
  rfl

theorem weight_cast : (((-2 * S.halfWeight : ℤ) : ℂ)) = (n : ℂ) + 3 := by
  rw [S.weight_k]
  push_cast
  ring

/-- The `L`-series of the form (coefficients `a_h(m)`). -/
def lseries (s : ℂ) : ℂ := LSeries (fun m => fourierCoeff S.form m) s

theorem globalEntryRatio_formula : globalEntryRatio S.form =
    (S.lseries ((n : ℂ) + 1) * poly3 (S.eigenvalues primeThree) ((n : ℂ) + 1) ((n : ℂ) + 3)) /
      (S.lseries ((n : ℂ) + 2) * poly3 (S.eigenvalues primeThree) ((n : ℂ) + 2) ((n : ℂ) + 3)) := by
  unfold globalEntryRatio poly3 SphericalEntryData.lseries
  rw [S.weight_cast, S.coeff_three]
  have e1 : (n : ℂ) + 3 - 2 = (n : ℂ) + 1 := by ring
  have e2 : (n : ℂ) + 3 - 1 = (n : ℂ) + 2 := by ring
  rw [e1, e2]

theorem lseries_ne_zero_and_poly (s : ℂ) (hs : s = (n : ℂ) + 1 ∨ s = (n : ℂ) + 2) :
    S.lseries s ≠ 0 ∧ poly3 (S.eigenvalues primeThree) s ((n : ℂ) + 3) ≠ 0 := by
  have hs' : s = (((-2 * S.halfWeight : ℤ) : ℂ)) - 2 ∨ s = (((-2 * S.halfWeight : ℤ) : ℂ)) - 1 := by
    rw [S.weight_cast]
    rcases hs with h | h
    · left; rw [h]; ring
    · right; rw [h]; ring
  have nonzero := lemma_2_5' S.weight_gt S.form S.normalizedEigenform {primeThree} s hs'
  simp only [Finset.prod_singleton, show (primeThree : ℕ) = 3 from rfl, Nat.cast_ofNat] at nonzero
  obtain ⟨first, second⟩ := mul_ne_zero_iff.mp nonzero
  refine ⟨first, ?_⟩
  unfold poly3
  rw [← S.coeff_three, ← S.weight_cast]
  exact second

/-- **The scalar `r` is the ratio of the full `L`-values**: the product of all local Euler factors,
including the one at `3`, is `L(h, k-2) / L(h, k-1)` with `k = n + 3`. -/
theorem rFull_eq_lseries_ratio : S.rFull = S.lseries ((n : ℂ) + 1) / S.lseries ((n : ℂ) + 2) := by
  unfold SphericalEntryData.rFull
  rw [S.value_eq, S.euler3_eq, S.globalEntryRatio_formula]
  obtain ⟨l1, p1⟩ := S.lseries_ne_zero_and_poly ((n : ℂ) + 1) (Or.inl rfl)
  obtain ⟨l2, p2⟩ := S.lseries_ne_zero_and_poly ((n : ℂ) + 2) (Or.inr rfl)
  field_simp

theorem rFull_ne_zero : S.rFull ≠ 0 := by
  rw [S.rFull_eq_lseries_ratio]
  exact div_ne_zero (S.lseries_ne_zero_and_poly ((n : ℂ) + 1) (Or.inl rfl)).1
    (S.lseries_ne_zero_and_poly ((n : ℂ) + 2) (Or.inr rfl)).1

theorem euler3_ne_zero : S.euler3 ≠ 0 := by
  rw [S.euler3_eq]
  exact div_ne_zero (S.lseries_ne_zero_and_poly ((n : ℂ) + 2) (Or.inr rfl)).2
    (S.lseries_ne_zero_and_poly ((n : ℂ) + 1) (Or.inl rfl)).2

/-- **The paper's finite scalar** (without the archimedean factor): `(1/9) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)`. -/
def rPrint : ℂ := (1 / 9 : ℂ) * globalEntryRatio S.form

theorem rBad_eq_rPrint : S.rBad = S.rPrint := by
  unfold SphericalEntryData.rBad SphericalEntryData.rPrint
  rw [S.value_eq]
  ring

theorem rPrint_ne_zero : S.rPrint ≠ 0 := by
  unfold SphericalEntryData.rPrint
  exact mul_ne_zero (by norm_num) (globalEntryRatio_ne_zero S.weight_gt S.form S.normalizedEigenform)

/-- **Comparison of the spherical and bad-plane scalars**: `r_full = 9 · c₃ · r_print`, with `c₃` the local Euler
factor at the place `3`. -/
theorem rFull_eq_nine_mul : S.rFull = 9 * S.euler3 * S.rPrint := by
  unfold SphericalEntryData.rFull SphericalEntryData.rPrint
  rw [S.value_eq]
  ring

/-- The paper's printed scalar `-2πi/(9(n+1)) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` (equation `ar:eq:globalentry`). -/
def printedScalar : ℂ :=
  -2 * Real.pi * Complex.I / (9 * ((n : ℂ) + 1)) * globalEntryRatio S.form

theorem printedScalar_eq : S.printedScalar = (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) * S.rPrint := by
  unfold SphericalEntryData.printedScalar SphericalEntryData.rPrint
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

theorem printedScalar_ne_zero : S.printedScalar ≠ 0 := by
  rw [S.printedScalar_eq]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  refine mul_ne_zero (div_ne_zero ?_ hn) S.rPrint_ne_zero
  simp [hpi, Complex.I_ne_zero]

/-- **The sign.**  The scalar of the class-level comparison, `entryScalar n r = (-r)(-2πi/(n+1))`, evaluated at the
bare finite scalar `r = r_print` of the bad plane, is MINUS the paper's printed scalar.  (The minus sign is not
produced by the finite part: it comes from the archimedean ledger of the cochain computation, `h_plane = (-1)ⁿ(n+1)F`
against `h_line = (-1)^{n+1}(n+1)F`; it is a normalization item between the source-class seeds and the printed
constant.) -/
theorem entryScalar_rPrint : entryScalar n S.rPrint = -S.printedScalar := by
  rw [S.printedScalar_eq]
  unfold entryScalar
  ring

theorem printedScalar_frozen : S.printedScalar =
    -2 * Real.pi * Complex.I / (9 * ((n : ℂ) + 1)) *
      ((LSeries (fun m => fourierCoeff S.form m) ((n : ℂ) + 1) *
          (1 - fourierCoeff S.form 3 * (3 : ℂ) ^ (-((n : ℂ) + 1)) + (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 1)))) /
        (LSeries (fun m => fourierCoeff S.form m) ((n : ℂ) + 2) *
          (1 - fourierCoeff S.form 3 * (3 : ℂ) ^ (-((n : ℂ) + 2)) + (3 : ℂ) ^ ((n : ℂ) + 2 - 2 * ((n : ℂ) + 2))))) := by
  unfold SphericalEntryData.printedScalar
  rw [S.globalEntryRatio_formula, ← S.coeff_three]
  unfold poly3 SphericalEntryData.lseries
  have e1 : (n : ℂ) + 3 - 1 - 2 * ((n : ℂ) + 1) = (n : ℂ) + 2 - 2 * ((n : ℂ) + 1) := by ring
  have e2 : (n : ℂ) + 3 - 1 - 2 * ((n : ℂ) + 2) = (n : ℂ) + 2 - 2 * ((n : ℂ) + 2) := by ring
  rw [e1, e2]

end SphericalEntryData

theorem fourierCoeff_cast {k k' : ℤ} (e : k = k') (f : CuspForm levelOne k) (m : ℕ) :
    fourierCoeff (e ▸ f) m = fourierCoeff f m := by
  subst e
  rfl

theorem isNormalizedEigenform_cast {k k' : ℤ} (e : k = k') (f : CuspForm levelOne k)
    (h : IsNormalizedEigenform f) : IsNormalizedEigenform (e ▸ f) := by
  subst e
  exact h

namespace SphericalEntryData

variable {n : ℕ} {D : InducingData n} (S : SphericalEntryData D)

include S

/-- **Nonvanishing of the printed scalar from the target `global_entry_ne_zero`.** -/
theorem printedScalar_ne_zero_of_frozen : S.printedScalar ≠ 0 := by
  have e := S.weight_k
  have frozen := global_entry_ne_zero n S.large (e ▸ S.form) (isNormalizedEigenform_cast e S.form S.normalizedEigenform)
  simp only [fourierCoeff_cast e S.form] at frozen
  rw [S.printedScalar_frozen]
  exact frozen

end SphericalEntryData




end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
