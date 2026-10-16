module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageFace
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REMain

@[expose] public section


/-!
# CMP-8 (3): the finite scalar `c_F` is `1` at an integral face

For an inducing datum whose character is trivial on the integral units, `cF D (faceArg h) = 1` for every `h ∈ SL₃(ℤ)`: `faceArg h` is the diagonal image of an integral
matrix, whose parabolic factor is integral (`finitePlaneFactor_integral`).  So the scalar `K_h = (-1)^n (n+1)/2 · c_F(g_h)` of `phiPlaneAt_bad_face_forms` is the constant
`(-1)^n (n+1)/2`, the same at every face.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.FormSeedBridge
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section
namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

/-- **`c_F` is `1` on integral finite adeles** (character trivial on integral units). -/
theorem cFin_integral {n : ℕ} (D : InducingData n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1) {f : FiniteGL}
    (hf : ∃ k₀ : Matrix.GeneralLinearGroup (Fin 3) IntegralAdeles, f = Matrix.GeneralLinearGroup.map integralEmbedding k₀) :
    cFin D f = 1 := by
  obtain ⟨k₀, hk₀⟩ := hf
  obtain ⟨k, hk⟩ := finitePlaneParabolic_spec f
  have hpmem := finitePlaneParabolic_mem f
  have hpk : finitePlaneParabolic f = Matrix.GeneralLinearGroup.map integralEmbedding (k₀ * k⁻¹) := by
    have h1 : finitePlaneParabolic f = finitePlaneParabolic f * Matrix.GeneralLinearGroup.map integralEmbedding k *
        Matrix.GeneralLinearGroup.map integralEmbedding k⁻¹ := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [h1, ← hk, hk₀, ← map_mul]
  have hmem : Matrix.GeneralLinearGroup.map integralEmbedding (k₀ * k⁻¹) ∈ planeParabolic FiniteAdeles := hpk ▸ hpmem
  have hkk : k₀ * k⁻¹ ∈ planeParabolic IntegralAdeles := integral_mem_planeParabolic hmem
  have key : ∀ (q : FiniteGL) (hq : q ∈ planeParabolic FiniteAdeles),
      q = Matrix.GeneralLinearGroup.map integralEmbedding (k₀ * k⁻¹) →
        finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) q hq = 1 := by
    intro q hq hqe
    subst hqe
    exact finitePlaneFactor_integral D.chi _ _ hχ hkk hq
  exact key _ hpmem hpk

/-- **`c_F` at the face argument.** -/
theorem cF_faceArg {n : ℕ} (D : InducingData n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1) (h : SL(3, ℤ)) :
    cF D (faceArg h) = 1 := by
  unfold cF
  rw [faceArg_eq, finiteGroup_rational]
  exact cFin_integral D hχ (integralFinite_integral _)

end TernaryPeriodPolynomials.Argument.KDaggerComparison
