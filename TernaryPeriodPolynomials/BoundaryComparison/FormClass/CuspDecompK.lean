module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.RowOrbits

@[expose] public section


/-!
# Every cusp: decompositions of `w₀⁻¹u(σ) · ι(k)⁻¹`

Formalized by Claude Sonnet 5.5.

For `k ∈ SL₃(ℤ)` let `kInvFin k = ι(k⁻¹) ∈ GL₃(𝔸_f)`. The classical series at the cusp `k⁻¹Pk` is the Eisenstein series of the
induced section evaluated at `(1, ι(k⁻¹))`; its unfolding sees the points `w₀⁻¹u(r) ι(k⁻¹) ∈ P(ℚ) K(N)`, `r = slRowPt (k a)`, `a ∈ Γ(N)`.
* `decompK_gFin`, `adelicSection_gFin_rational_K`: the section there is the classical section at `k a · qMat(shiftV r w)`.
* `adelicSection_gFin_add_latK`: constant on `σ + (NẐ)²` (normality of `K(N)`).
* `exists_elt_of_decompK`: the cover.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

/-- The finite adele `ι(k⁻¹)`. -/
def kInvFin (k : SL(3, ℤ)) : FiniteGL := rationalFinite (Matrix.SpecialLinearGroup.mapGL ℚ k⁻¹)

theorem kInvFin_eq (k : SL(3, ℤ)) :
    kInvFin k = GeneralLinearGroup.map integralEmbedding (Matrix.SpecialLinearGroup.mapGL IntegralAdeles k⁻¹) := by
  unfold kInvFin
  rw [rationalFinite_mapGL]

variable (N : ℕ) [NeZero N]

theorem kInvFin_conj (k : SL(3, ℤ)) {κ : GL3 IntegralAdeles} (hκ : κ ∈ levelKernel N 3) :
    ∃ κ' ∈ levelKernel N 3, GeneralLinearGroup.map integralEmbedding κ * kInvFin k =
      kInvFin k * GeneralLinearGroup.map integralEmbedding κ' := by
  refine ⟨Matrix.SpecialLinearGroup.mapGL IntegralAdeles k * κ * (Matrix.SpecialLinearGroup.mapGL IntegralAdeles k)⁻¹,
    ?_, ?_⟩
  · exact (levelKernel_normal N 3).conj_mem κ hκ _
  · have h : Matrix.SpecialLinearGroup.mapGL IntegralAdeles k⁻¹ = (Matrix.SpecialLinearGroup.mapGL IntegralAdeles k)⁻¹ :=
      map_inv _ _
    rw [kInvFin_eq, h]
    simp only [map_mul, map_inv]
    group

theorem adelicSection_gFin_add_latK (hN : 3 ≤ N) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (k : SL(3, ℤ)) (w : Fin 2 → ℝ) (σ ν : FiniteAdeles × FiniteAdeles) (h1 : ν.1 ∈ latSet N) (h2 : ν.2 ∈ latSet N)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5) :
    adelicSection N n (hfun f) (gReal w) (gFin (σ + ν) * kInvFin k) y a b =
      adelicSection N n (hfun f) (gReal w) (gFin σ * kInvFin k) y a b := by
  obtain ⟨κ, hκ, e⟩ := gFin_add_lat N σ ν h1 h2
  obtain ⟨κ', hκ', e'⟩ := kInvFin_conj N k hκ
  rw [e, mul_assoc, e', ← mul_assoc]
  exact adelicSection_mul_ker N hN n f (gReal_det w) _ hκ' hy a b

theorem decompK_gFin (k A : SL(3, ℤ)) (hA : A * k⁻¹ ∈ gammaN N) (h0 : (A : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0) :
    IsDecomp N (gFin (algebraMap ℚ FiniteAdeles (slRowPt A).1, algebraMap ℚ FiniteAdeles (slRowPt A).2) * kInvFin k)
      (piOf (slRowPt A) A) (Matrix.SpecialLinearGroup.mapGL IntegralAdeles (A * k⁻¹)) := by
  have := decomp_rational N (piOf_planeDet A h0) hA
  convert this using 1
  rw [gFin_rational (slRowPt A), kInvFin, ← map_mul]
  congr 1
  rw [← piOf_mul (slRowPt A) A, mul_assoc, ← map_mul]

end TernaryPeriodPolynomials.Argument.FormClassK
