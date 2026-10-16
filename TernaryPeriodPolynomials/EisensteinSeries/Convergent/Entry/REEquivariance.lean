module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REJacobian
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REMatrix
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REVector

@[expose] public section


/-!
# R-e: Equivariance of the entry integral under the line parabolic

`entryPlaneIntegral_lineParabolic`: for a left-`planeParabolic`-invariant weight `w` and `q = u(a,a') lineLevi(d,B)` with `B` lower triangular, the entry integral at `q f` is the plane factor of `planeLevi(B,d)` times the Jacobian constant times the entry integral at `f` evaluated at `y · B`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The finite entry integral at the finite matrix `f`, against the weight `w`, evaluated at `y`. -/
def entryPlaneIntegral (σ : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (w : FiniteGL → ℂ) (vec : σ.H)
    (f : FiniteGL) (y : BinaryAdelicGL) : ℂ :=
  ∫ v : FiniteAdeles × FiniteAdeles, w (weyl⁻¹ * lineUnipotent v.1 v.2 * f) *
    entryRz σ (finitePlaneVector σ χ 0 b (weyl⁻¹ * lineUnipotent v.1 v.2 * f) vec) y
    ∂(finiteMeasure.prod finiteMeasure)

/-- **Equivariance of the entry integral under the line parabolic** (lower triangular Levi block). -/
theorem entryPlaneIntegral_lineParabolic (σ : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (w : FiniteGL → ℂ) (hw : ∀ p ∈ planeParabolic FiniteAdeles, ∀ f, w (p * f) = w f)
    {vec : σ.H} (hvec : vec ∈ σ.smooth) (hsph : vec ∈ sphericalSubspace σ)
    (a a' : FiniteAdeles) (d : FiniteAdelesˣ) (B : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (h01 : B.val 0 1 = 0) (α₁ α₃ : FiniteAdelesˣ) (h₁ : α₁.val = (d⁻¹).val * B.val 0 0)
    (h₃ : α₃.val = (d⁻¹).val * B.val 1 1) (f : FiniteGL) (y : BinaryAdelicGL) :
    entryPlaneIntegral σ χ b w vec (lineUnipotent a a' * lineLevi d B * f) y =
      (scaleConstant α₁ * scaleConstant α₃).toReal •
        (finitePlaneFactor χ 0 b (planeLevi B d) (planeLevi_mem B d) *
          entryPlaneIntegral σ χ b w vec f (y * atFinite B)) := by
  let G : FiniteAdeles × FiniteAdeles → ℂ := fun u =>
    w (weyl⁻¹ * lineUnipotent u.1 u.2 * f) *
      entryRz σ (finitePlaneVector σ χ 0 b (weyl⁻¹ * lineUnipotent u.1 u.2 * f) vec) (y * atFinite B)
  have pointwise : ∀ v : FiniteAdeles × FiniteAdeles,
      w (weyl⁻¹ * lineUnipotent v.1 v.2 * (lineUnipotent a a' * lineLevi d B * f)) *
        entryRz σ (finitePlaneVector σ χ 0 b
          (weyl⁻¹ * lineUnipotent v.1 v.2 * (lineUnipotent a a' * lineLevi d B * f)) vec) y =
      finitePlaneFactor χ 0 b (planeLevi B d) (planeLevi_mem B d) *
        G (α₁.val * v.1 + (d⁻¹).val * B.val 1 0 * v.2 + (d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0),
          α₃.val * v.2 + (d⁻¹).val * (a' * B.val 1 1)) := by
    intro v
    have matrix : weyl⁻¹ * lineUnipotent v.1 v.2 * (lineUnipotent a a' * lineLevi d B * f) =
        planeLevi B d * (weyl⁻¹ * lineUnipotent
          (α₁.val * v.1 + (d⁻¹).val * B.val 1 0 * v.2 + (d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0))
          (α₃.val * v.2 + (d⁻¹).val * (a' * B.val 1 1)) * f) := by
      have step := weyl_inv_lineUnipotent_mul_lineLevi (v.1 + a) (v.2 + a') d B
      rw [h01] at step
      have first : (d⁻¹).val * ((v.1 + a) * B.val 0 0 + (v.2 + a') * B.val 1 0) =
          α₁.val * v.1 + (d⁻¹).val * B.val 1 0 * v.2 + (d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0) := by
        rw [h₁]; ring
      have second : (d⁻¹).val * ((v.1 + a) * 0 + (v.2 + a') * B.val 1 1) =
          α₃.val * v.2 + (d⁻¹).val * (a' * B.val 1 1) := by
        rw [h₃]; ring
      rw [first, second] at step
      calc weyl⁻¹ * lineUnipotent v.1 v.2 * (lineUnipotent a a' * lineLevi d B * f)
          = weyl⁻¹ * (lineUnipotent v.1 v.2 * lineUnipotent a a') * lineLevi d B * f := by
            simp only [mul_assoc]
        _ = weyl⁻¹ * lineUnipotent (v.1 + a) (v.2 + a') * lineLevi d B * f := by
            rw [← lineUnipotent_add]
        _ = _ := by rw [step]; simp only [mul_assoc]
    rw [matrix, hw _ (planeLevi_mem B d)]
    have vec_smooth := finitePlaneVector_smooth (σ := σ) χ 0 b
      (weyl⁻¹ * lineUnipotent
        (α₁.val * v.1 + (d⁻¹).val * B.val 1 0 * v.2 + (d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0))
        (α₃.val * v.2 + (d⁻¹).val * (a' * B.val 1 1)) * f) hvec
    rw [finitePlaneVector_mul χ 0 b hχ hsph (planeLevi_mem B d), planeBlockGL_planeLevi'',
      entryRz_smul (σ.smooth_stable _ _ vec_smooth), entryRz_pi vec_smooth]
    simp only [G]
    ring
  simp_rw [entryPlaneIntegral, pointwise]
  rw [integral_const_mul, integral_finiteAffine α₁ α₃ ((d⁻¹).val * B.val 1 0)
    ((d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0)) ((d⁻¹).val * (a' * B.val 1 1)) G]
  simp only [Complex.real_smul, G]
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
