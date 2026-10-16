module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBase
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REEquivariance
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REDecomp
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REScalar

@[expose] public section


/-!
# R-e: The entry integral at an arbitrary finite matrix

`entryPlaneIntegral_general`: `∫ rz(φ(w⁻¹u(v)f))(y) dv = r · rz(finiteLineVector f)(y)` for every `f ∈ GL₃(𝔸_f)` and `y`, with `r = (∏_{p≠3} c_p)·c₃`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem lineCornerUnit_unip_levi (a a' : FiniteAdeles) (d : FiniteAdelesˣ)
    (B : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hp : lineUnipotent a a' * lineLevi d B ∈ lineParabolic FiniteAdeles) :
    lineCornerUnit (lineUnipotent a a' * lineLevi d B) hp = d := by
  apply Units.ext
  change (lineUnipotent a a' * lineLevi d B).val 0 0 = d.val
  rw [Units.val_mul, lineLevi_val]
  simp [lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem lineBlockGL_unip_levi (a a' : FiniteAdeles) (d : FiniteAdelesˣ)
    (B : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hp : lineUnipotent a a' * lineLevi d B ∈ lineParabolic FiniteAdeles) :
    lineBlockGL (lineUnipotent a a' * lineLevi d B) hp = B := by
  apply Units.ext
  change !![(lineUnipotent a a' * lineLevi d B).val 1 1, (lineUnipotent a a' * lineLevi d B).val 1 2;
    (lineUnipotent a a' * lineLevi d B).val 2 1, (lineUnipotent a a' * lineLevi d B).val 2 2] = B.val
  rw [Units.val_mul, lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem lineUnip_levi_mem (a a' : FiniteAdeles) (d : FiniteAdelesˣ)
    (B : GeneralLinearGroup (Fin 2) FiniteAdeles) :
    lineUnipotent a a' * lineLevi d B ∈ lineParabolic FiniteAdeles :=
  (lineParabolic FiniteAdeles).mul_mem ⟨rfl, rfl⟩ (lineLevi_mem d B)

theorem unit_of_lower_triangular (B : GeneralLinearGroup (Fin 2) FiniteAdeles) (h01 : B.val 0 1 = 0) :
    ∃ u₀ u₁ : FiniteAdelesˣ, u₀.val = B.val 0 0 ∧ u₁.val = B.val 1 1 ∧
      GeneralLinearGroup.det B = u₀ * u₁ := by
  have hdet : (GeneralLinearGroup.det B).val = B.val 0 0 * B.val 1 1 := by
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h01]; ring
  have unit : IsUnit (B.val 0 0 * B.val 1 1) := hdet ▸ (GeneralLinearGroup.det B).isUnit
  obtain ⟨u₀, h₀⟩ := (isUnit_of_mul_isUnit_left unit)
  obtain ⟨u₁, h₁⟩ := (isUnit_of_mul_isUnit_right unit)
  exact ⟨u₀, u₁, h₀, h₁, Units.ext (by rw [hdet, Units.val_mul, h₀, h₁])⟩

/-- **The entry integral at an arbitrary finite matrix**, evaluated at an arbitrary point. -/
theorem entryPlaneIntegral_general (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (vec : cusp.smooth) (nonzero : vec ≠ 0) (spherical : vec.val ∈ sphericalSubspace cusp)
    (convergent : 3 < b.re) (eigenvalues : FinitePlace → ℂ)
    (eigen : ∀ place, cuspLocalPadicSphereOperator cusp place 1 vec = eigenvalues place • vec)
    (value : ℂ) (product : HasProd (fun place : {place : FinitePlace // place ≠ placeThree} =>
      cuspLocalPadicEulerFactor cusp place.val (eigenvalues place.val) b) value)
    (f : FiniteGL) (y : BinaryAdelicGL) :
    entryPlaneIntegral cusp χ b (fun _ => 1) vec.val f y =
      value * cuspLocalPadicEulerFactor cusp placeThree (eigenvalues placeThree) b *
        entryRz cusp (finiteLineVector cusp χ 2 (b - 1) f vec.val) y := by
  obtain ⟨a, a', d, B, κ, h01, hf⟩ := finite_line_decomposition f
  obtain ⟨u₀, u₁, h₀, h₁, hdet⟩ := unit_of_lower_triangular B h01
  subst hf
  have plane := entryPlaneIntegral_lineParabolic cusp χ b hχ (fun _ => 1) (fun _ _ _ => rfl) vec.property spherical a a' d B
    h01 (d⁻¹ * u₀) (d⁻¹ * u₁) (by rw [Units.val_mul, h₀]) (by rw [Units.val_mul, h₁])
    (GeneralLinearGroup.map integralEmbedding κ) y
  have base : ∀ y' : BinaryAdelicGL,
      entryPlaneIntegral cusp χ b (fun _ => 1) vec.val (GeneralLinearGroup.map integralEmbedding κ) y' =
        value * cuspLocalPadicEulerFactor cusp placeThree (eigenvalues placeThree) b * cusp.realize vec y' := by
    intro y'
    unfold entryPlaneIntegral
    simp_rw [one_mul, finitePlaneVector_entry cusp χ b hχ spherical _ κ]
    exact integral_planeOpposite cusp χ b hχ vec nonzero spherical convergent eigenvalues eigen value product y'
  have hp := lineUnip_levi_mem a a' d B
  have line : entryRz cusp (finiteLineVector cusp χ 2 (b - 1)
      (lineUnipotent a a' * lineLevi d B * GeneralLinearGroup.map integralEmbedding κ) vec.val) y =
      finiteLineFactor χ 2 (b - 1) (lineUnipotent a a' * lineLevi d B) hp *
        cusp.realize vec (y * atFinite B) := by
    rw [finiteLineVector_eq χ 2 (b - 1) hχ spherical hp κ rfl,
      entryRz_smul (cusp.smooth_stable _ _ vec.property), entryRz_pi vec.property,
      entryRz_of_mem vec.property, lineBlockGL_unip_levi]
  rw [plane, base, line]
  have factorL : finiteLineFactor χ 2 (b - 1) (lineUnipotent a a' * lineLevi d B) hp =
      χ.toMonoidHom (Norm.finiteAdeleUnit d) * normPower (Norm.finiteAdeleUnit d) 2 *
        normPower (Norm.finiteAdeleUnit (u₀ * u₁)) (b - 1) := by
    unfold finiteLineFactor
    rw [lineCornerUnit_unip_levi, lineBlockGL_unip_levi, hdet]
  have factorP : finitePlaneFactor χ 0 b (planeLevi B d) (planeLevi_mem B d) =
      χ.toMonoidHom (Norm.finiteAdeleUnit d) * normPower (Norm.finiteAdeleUnit d) 0 *
        normPower (Norm.finiteAdeleUnit (u₀ * u₁)) b := by
    rw [finitePlaneFactor_planeLevi', hdet]
  rw [factorL, factorP, Complex.real_smul]
  have scalar := scalar_identity χ b d u₀ u₁
  linear_combination (value * cuspLocalPadicEulerFactor cusp placeThree (eigenvalues placeThree) b *
    cusp.realize vec (y * atFinite B)) * scalar

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
