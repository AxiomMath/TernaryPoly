module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Injective
public import TernaryPeriodPolynomials.Polynomial.Integral
public import Mathlib.Algebra.MvPolynomial.Division

@[expose] public section

open MvPolynomial

noncomputable section
namespace TernaryPoly

/-- Todd in the first coordinate is injective. -/
theorem ternaryTodd_injective (u : MvPolynomial (Fin 2) ℚ) :
    Function.Injective (ternaryTodd u) := by
  intro p q h
  apply (finSuccEquiv ℚ 2).injective
  apply todd_injective u
  exact (finSuccEquiv ℚ 2).symm.injective h

/-- Every ternary rational polynomial has an antiderivative in the first coordinate. -/
theorem exists_pderiv_zero_eq (h : TernaryPolynomial) :
    ∃ e : TernaryPolynomial, pderiv 0 e = h := by
  refine ⟨(finSuccEquiv ℚ 2).symm (polyIntegral (finSuccEquiv ℚ 2 h)), ?_⟩
  apply (finSuccEquiv ℚ 2).injective
  rw [finSuccEquiv_pderiv_zero, AlgEquiv.apply_symm_apply, derivative_polyIntegral]

/-- The first radical difference has Todd output `-Y ∂₀e`. -/
theorem ternaryTodd_shift_one_sub (e : TernaryPolynomial) :
    ternaryTodd (X (0 : Fin 2)) (alternatingShift (X 1) e - e) =
      -(X 1) * pderiv 0 e := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [ternaryTodd, AlgEquiv.apply_symm_apply, map_sub, alternatingShift,
    finSuccEquiv_shift_Y, map_mul, map_neg, finSuccEquiv_ternary_X_one,
    finSuccEquiv_pderiv_zero]
  simpa only [map_sub, Polynomial.smul_eq_C_mul, map_neg] using
    todd_difference (X (0 : Fin 2)) (finSuccEquiv ℚ 2 e)

/-- The second radical difference has Todd output `-Z ∂₀e`. -/
theorem ternaryTodd_shift_two_sub (e : TernaryPolynomial) :
    ternaryTodd (X (1 : Fin 2)) (alternatingShift (X 2) e - e) =
      -(X 2) * pderiv 0 e := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [ternaryTodd, AlgEquiv.apply_symm_apply, map_sub, alternatingShift,
    finSuccEquiv_shift_Z, map_mul, map_neg, finSuccEquiv_ternary_X_two,
    finSuccEquiv_pderiv_zero]
  simpa only [map_sub, Polynomial.smul_eq_C_mul, map_neg] using
    todd_difference (X (1 : Fin 2)) (finSuccEquiv ℚ 2 e)

/-- The two independent coordinate variables force a common factor. -/
theorem radical_common_factor (α β : TernaryPolynomial)
    (h : X 2 * α - X 1 * β = 0) :
    ∃ k : TernaryPolynomial, α = X 1 * k ∧ β = X 2 * k := by
  have heq : X 2 * α = X 1 * β := sub_eq_zero.mp h
  have hd : (X 1 : TernaryPolynomial) ∣ X 2 * α := ⟨β, heq⟩
  have hn : ¬ (X 1 : TernaryPolynomial) ∣ X 2 := by
    rw [X_dvd_X]
    decide
  obtain ⟨k, hk⟩ := (X_dvd_mul_iff.mp hd).resolve_left hn
  refine ⟨k, hk, ?_⟩
  apply mul_left_cancel₀ (X_ne_zero (1 : Fin 3))
  calc
    X 1 * β = X 2 * α := heq.symm
    _ = X 1 * (X 2 * k) := by rw [hk]; ring

/-- Every pair with zero Todd contraction is a pair of differences of one polynomial. -/
theorem radical_todd_kernel_exact (g₁ g₂ : TernaryPolynomial)
    (h : X 2 * ternaryTodd (X (0 : Fin 2)) g₁ -
      X 1 * ternaryTodd (X (1 : Fin 2)) g₂ = 0) :
    ∃ e : TernaryPolynomial,
      g₁ = alternatingShift (X 1) e - e ∧
      g₂ = alternatingShift (X 2) e - e := by
  obtain ⟨k, h₁, h₂⟩ := radical_common_factor _ _ h
  obtain ⟨e, he⟩ := exists_pderiv_zero_eq (-k)
  refine ⟨e, ?_, ?_⟩
  · apply ternaryTodd_injective (X (0 : Fin 2))
    rw [h₁, ternaryTodd_shift_one_sub, he, neg_mul_neg]
  · apply ternaryTodd_injective (X (1 : Fin 2))
    rw [h₂, ternaryTodd_shift_two_sub, he, neg_mul_neg]

/-- Differences of a common polynomial have zero Todd contraction. -/
theorem radical_todd_differences_zero (e : TernaryPolynomial) :
    X 2 * ternaryTodd (X (0 : Fin 2)) (alternatingShift (X 1) e - e) -
      X 1 * ternaryTodd (X (1 : Fin 2)) (alternatingShift (X 2) e - e) = 0 := by
  rw [ternaryTodd_shift_one_sub, ternaryTodd_shift_two_sub]
  ring

/-- Exactness of the polynomial radical Todd contraction. -/
theorem radical_todd_kernel_iff (g₁ g₂ : TernaryPolynomial) :
    (X 2 * ternaryTodd (X (0 : Fin 2)) g₁ -
      X 1 * ternaryTodd (X (1 : Fin 2)) g₂ = 0) ↔
    ∃ e : TernaryPolynomial,
      g₁ = alternatingShift (X 1) e - e ∧
      g₂ = alternatingShift (X 2) e - e := by
  constructor
  · exact radical_todd_kernel_exact g₁ g₂
  · rintro ⟨e, rfl, rfl⟩
    exact radical_todd_differences_zero e

/-- The literal alternating frames lie in this kernel exactly when they are common differences. -/
theorem alternatingTodd_eq_zero_iff_exact_frames (f : TernaryPolynomial) :
    alternatingTodd f = 0 ↔
    ∃ e : TernaryPolynomial,
      alternatingFrame1 f = alternatingShift (X 1) e - e ∧
      alternatingFrame2 f = alternatingShift (X 2) e - e :=
  radical_todd_kernel_iff (alternatingFrame1 f) (alternatingFrame2 f)

end TernaryPoly
