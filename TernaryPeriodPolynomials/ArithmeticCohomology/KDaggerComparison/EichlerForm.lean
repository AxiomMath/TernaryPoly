module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.HeckeFaithfulness
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Multiplicativity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarNonvanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Equivariance

@[expose] public section


/-!
# CMP-8: the classical form of the Eichler vector is a nonzero multiple of the normalized eigenform `S.form`

The spherical datum `S` of the entry carries the normalized level-one eigenform `S.form` (first coefficient `1`, prime Hecke
relations with `S.eigenvalues`) and a nonzero spherical vector which is a Hecke eigenvector for the corresponding eigenvalues
(`S.eigen`).  The scalar function of the vector is a level-one cusp form `f` (`CuspidalSpan.EichlerInput.exists_classicalForm`).
This file proves that `f` has the prime Hecke relations with the eigenvalues of `S.form`, is nonzero, and equals
`fourierCoeff f 1 • S.form`; this is the multiplicity-one statement for level one, obtained from the existing
`cuspForm_hecke_first_coefficient_ne_zero` (a nonzero form with the Hecke relations has `a₁ ≠ 0`) applied to `f - a₁(f) • S.form`.
It is a statement about the cusp forms themselves (equality of the underlying functions), not only of q-expansions.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

theorem hasPrimeHeckeRelations_sub {weight : ℤ} {f g : UpperHalfPlane → ℂ} {ev : Nat.Primes → ℂ}
    (hf : HasPrimeHeckeRelations weight f ev) (hg : HasPrimeHeckeRelations weight g ev) :
    HasPrimeHeckeRelations weight (f - g) ev := by
  intro prime point
  have h1 := hf prime point
  have h2 := hg prime point
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  linear_combination h1 - h2

/-- **The scalar function of the Eichler vector has the prime Hecke relations with the eigenvalues of `S.form`.** -/
theorem scalar_hasPrimeHeckeRelations {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) (I : EichlerInput D.cusp n)
    (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) :
    HasPrimeHeckeRelations (-2 * S.halfWeight) (cuspScalarWeightedLinear D.cusp S.halfWeight 1 S.vector)
      S.eigenvalues := by
  have rot : ∀ angle : Circle, D.cusp.π (atInfinity (binaryRotations angle)) S.vector.val =
      (angle : ℂ) ^ (2 * S.halfWeight) • S.vector.val := by
    rw [← hv, ← hw]; exact I.rotation
  have eig : ∀ prime, scalarPrimeHecke S.halfWeight prime (cuspScalarWeightedLinear D.cusp S.halfWeight 1 S.vector) =
      ((prime.val : ℂ) ^ (S.halfWeight + 1) * S.eigenvalues prime) •
        cuspScalarWeightedLinear D.cusp S.halfWeight 1 S.vector := by
    intro prime
    rw [← cuspPrimeHeckeSum_scalar_intertwines D.cusp I.central_positive S.halfWeight prime S.vector rot,
      S.eigen prime, map_smul]
  have := scalarPrimeHecke_eigen_relations S.halfWeight _ _ eig
  have hcancel : ∀ prime : Nat.Primes, (prime.val : ℂ) ^ (-S.halfWeight - 1) *
      ((prime.val : ℂ) ^ (S.halfWeight + 1) * S.eigenvalues prime) = S.eigenvalues prime := by
    intro prime
    rw [← mul_assoc, ← zpow_add₀ (Nat.cast_ne_zero.mpr prime.property.ne_zero)]
    have : -S.halfWeight - 1 + (S.halfWeight + 1) = 0 := by ring
    rw [this, zpow_zero, one_mul]
  have hfun : (fun prime : Nat.Primes => (prime.val : ℂ) ^ (-S.halfWeight - 1) *
      ((prime.val : ℂ) ^ (S.halfWeight + 1) * S.eigenvalues prime)) = S.eigenvalues := funext hcancel
  rw [hfun] at this
  exact this

theorem levelOne_period : (1 : ℝ) ∈ levelOne.strictPeriods := by
  simpa only [Subgroup.strictWidthInfty_SL2Z] using levelOne.strictWidthInfty_mem_strictPeriods

theorem fourierCoeff_eq_qExpansion {k : ℤ} (f : CuspForm levelOne k) (m : ℕ) :
    fourierCoeff f m = (UpperHalfPlane.qExpansion 1 f).coeff m := by
  unfold fourierCoeff
  rw [Subgroup.strictWidthInfty_SL2Z]

/-- **Multiplicity one at level one for the entry datum.**  If `f` is the classical level-one cusp form of the Eichler vector
(its function is the scalar function of `S.vector`), then `f` is nonzero, `a₁(f) ≠ 0` and `f = a₁(f) • S.form`.  The equality is
one of cusp forms (of the underlying functions), obtained from the Hecke relations of the vector and of `S.form`. -/
theorem eichlerForm_eq_smul_form {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) (I : EichlerInput D.cusp n)
    (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) (f : CuspForm levelOne (-2 * S.halfWeight))
    (hf : (f : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear D.cusp S.halfWeight 1 S.vector) :
    f ≠ 0 ∧ fourierCoeff f 1 ≠ 0 ∧ f = fourierCoeff f 1 • S.form := by
  have rot : ∀ angle : Circle, D.cusp.π (atInfinity (binaryRotations angle)) S.vector.val =
      (angle : ℂ) ^ (2 * S.halfWeight) • S.vector.val := by
    rw [← hv, ← hw]; exact I.rotation
  have hrel : HasPrimeHeckeRelations (-2 * S.halfWeight) (f : UpperHalfPlane → ℂ) S.eigenvalues := by
    rw [hf]; exact scalar_hasPrimeHeckeRelations S I hw hv
  have hne : f ≠ 0 := by
    obtain ⟨point, hp⟩ := cuspScalarWeightedRealization_identity_nonzero D.cusp I.central_positive S.halfWeight
      S.vector S.spherical rot S.nonzero
    intro h0
    apply hp
    have := congrFun hf point
    rw [h0] at this
    exact this.symm
  have h1 : fourierCoeff f 1 ≠ 0 := by
    rw [fourierCoeff_eq_qExpansion]
    exact cuspForm_hecke_first_coefficient_ne_zero f levelOne_period hne S.eigenvalues hrel
  refine ⟨hne, h1, ?_⟩
  by_contra hd
  have hdne : f - fourierCoeff f 1 • S.form ≠ 0 := sub_ne_zero.mpr hd
  have hdrel : HasPrimeHeckeRelations (-2 * S.halfWeight)
      ((f - fourierCoeff f 1 • S.form : CuspForm levelOne (-2 * S.halfWeight)) : UpperHalfPlane → ℂ)
      S.eigenvalues :=
    hasPrimeHeckeRelations_sub hrel (S.relations.smul (fourierCoeff f 1))
  apply cuspForm_hecke_first_coefficient_ne_zero _ levelOne_period hdne S.eigenvalues hdrel
  have e : ((f - fourierCoeff f 1 • S.form : CuspForm levelOne (-2 * S.halfWeight)) : UpperHalfPlane → ℂ) =
      (f : UpperHalfPlane → ℂ) - ((fourierCoeff f 1 • S.form : CuspForm levelOne (-2 * S.halfWeight)) : UpperHalfPlane → ℂ) := rfl
  have e2 : ((fourierCoeff f 1 • S.form : CuspForm levelOne (-2 * S.halfWeight)) : UpperHalfPlane → ℂ) =
      fourierCoeff f 1 • (S.form : UpperHalfPlane → ℂ) := rfl
  rw [e, ModularForm.qExpansion_sub (by norm_num : (0 : ℝ) < 1) levelOne_period f (fourierCoeff f 1 • S.form), e2,
    ModularForm.qExpansion_smul (by norm_num : (0 : ℝ) < 1) levelOne_period _ S.form]
  simp only [map_sub, PowerSeries.coeff_smul, smul_eq_mul]
  have hnorm : (UpperHalfPlane.qExpansion 1 S.form).coeff 1 = 1 := by
    rw [← fourierCoeff_eq_qExpansion]; exact S.normalized
  rw [hnorm, ← fourierCoeff_eq_qExpansion, mul_one, sub_self]

end TernaryPeriodPolynomials.Argument.KDaggerComparison
