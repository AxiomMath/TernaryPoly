module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REMeasurable

@[expose] public section


/-!
# R-e: The local integrable majorant

`planeCoeff_majorant`: for a compact `Z` in the upper half plane the plane coefficient function along the radical is dominated by an integrable function of `v` uniformly in `z ∈ Z`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The matrix identity of the equivariance, as a standalone statement. -/
theorem radical_levi_identity (v : FiniteAdeles × FiniteAdeles) (a a' : FiniteAdeles) (d : FiniteAdelesˣ)
    (B : GeneralLinearGroup (Fin 2) FiniteAdeles) (h01 : B.val 0 1 = 0) (α₁ α₃ : FiniteAdelesˣ)
    (h₁ : α₁.val = (d⁻¹).val * B.val 0 0) (h₃ : α₃.val = (d⁻¹).val * B.val 1 1) (f : FiniteGL) :
    weyl⁻¹ * lineUnipotent v.1 v.2 * (lineUnipotent a a' * lineLevi d B * f) =
      planeLevi B d * (weyl⁻¹ * lineUnipotent
        (finiteAffine α₁ α₃ ((d⁻¹).val * B.val 1 0) ((d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0))
          ((d⁻¹).val * (a' * B.val 1 1)) v).1
        (finiteAffine α₁ α₃ ((d⁻¹).val * B.val 1 0) ((d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0))
          ((d⁻¹).val * (a' * B.val 1 1)) v).2 * f) := by
  have step := weyl_inv_lineUnipotent_mul_lineLevi (v.1 + a) (v.2 + a') d B
  rw [h01] at step
  rw [finiteAffine_apply]
  dsimp only
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

theorem planeCoeff_decomp (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (vec : cusp.smooth) (spherical : vec.val ∈ sphericalSubspace cusp)
    (a a' : FiniteAdeles) (d : FiniteAdelesˣ) (B : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (h01 : B.val 0 1 = 0) (α₁ α₃ : FiniteAdelesˣ) (h₁ : α₁.val = (d⁻¹).val * B.val 0 0)
    (h₃ : α₃.val = (d⁻¹).val * B.val 1 1) (κ : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (x : BinaryAdelicGL) (v : FiniteAdeles × FiniteAdeles) (z : ℂ) :
    planeCoeff cusp χ b hw vec x
        (weyl⁻¹ * lineUnipotent v.1 v.2 * (lineUnipotent a a' * lineLevi d B *
          GeneralLinearGroup.map integralEmbedding κ)) z =
      (z.im ^ hw : ℝ) * (finitePlaneFactor χ 0 b (planeLevi B d) (planeLevi_mem B d) *
        (normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det
            (entryBlock (finiteAffine α₁ α₃ ((d⁻¹).val * B.val 1 0)
              ((d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0)) ((d⁻¹).val * (a' * B.val 1 1)) v)))) b *
          entryRz cusp vec.val (x * atInfinity (sectionMatrix z) * atFinite B *
            atFinite (entryBlock (finiteAffine α₁ α₃ ((d⁻¹).val * B.val 1 0)
              ((d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0)) ((d⁻¹).val * (a' * B.val 1 1)) v))))) := by
  set pt := finiteAffine α₁ α₃ ((d⁻¹).val * B.val 1 0) ((d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0))
    ((d⁻¹).val * (a' * B.val 1 1)) v with hpt
  rw [planeCoeff_eq, radical_levi_identity v a a' d B h01 α₁ α₃ h₁ h₃ (GeneralLinearGroup.map integralEmbedding κ)]
  have vec_smooth := finitePlaneVector_smooth (σ := cusp) χ 0 b
    (weyl⁻¹ * lineUnipotent pt.1 pt.2 * GeneralLinearGroup.map integralEmbedding κ) vec.property
  rw [finitePlaneVector_mul χ 0 b hχ spherical (planeLevi_mem B d), planeBlockGL_planeLevi'',
    entryRz_smul (cusp.smooth_stable _ _ vec_smooth), entryRz_pi vec_smooth,
    finitePlaneVector_entry cusp χ b hχ spherical pt κ,
    entryRz_planeOpposite cusp χ b hχ vec.property spherical pt]

theorem unit_from_mul_isUnit_aux (B : GeneralLinearGroup (Fin 2) FiniteAdeles) (h01 : B.val 0 1 = 0) :
    ∃ u₀ u₁ : FiniteAdelesˣ, u₀.val = B.val 0 0 ∧ u₁.val = B.val 1 1 ∧
      GeneralLinearGroup.det B = u₀ * u₁ := by
  have hdet : (GeneralLinearGroup.det B).val = B.val 0 0 * B.val 1 1 := by
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h01]; ring
  have unit : IsUnit (B.val 0 0 * B.val 1 1) := hdet ▸ (GeneralLinearGroup.det B).isUnit
  obtain ⟨u₀, h₀⟩ := (isUnit_of_mul_isUnit_left unit)
  obtain ⟨u₁, h₁⟩ := (isUnit_of_mul_isUnit_right unit)
  exact ⟨u₀, u₁, h₀, h₁, Units.ext (by rw [hdet, Units.val_mul, h₀, h₁])⟩

/-- **The local (in `z`) integrable majorant** of the plane coefficient function along the radical. -/
theorem planeCoeff_majorant (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (vec : cusp.smooth) (spherical : vec.val ∈ sphericalSubspace cusp) (convergent : 3 < b.re)
    (x : BinaryAdelicGL) (f : FiniteGL) (Z : Set ℂ) (hZ : IsCompact Z) (hZ' : Z ⊆ {z : ℂ | 0 < z.im}) :
    ∃ φ : FiniteAdeles × FiniteAdeles → ℝ, Integrable φ (finiteMeasure.prod finiteMeasure) ∧
      ∀ v : FiniteAdeles × FiniteAdeles, ∀ z ∈ Z,
        ‖planeCoeff cusp χ b hw vec x (weyl⁻¹ * lineUnipotent v.1 v.2 * f) z‖ ≤ φ v := by
  obtain ⟨a, a', d, B, κ, h01, hf⟩ := finite_line_decomposition f
  obtain ⟨u₀, u₁, h₀, h₁, hdet⟩ := unit_from_mul_isUnit_aux B h01
  subst hf
  obtain ⟨C, bounded⟩ := cusp.bounded vec
  have continuousOn : ContinuousOn (fun z : ℂ => z.im ^ hw) Z := by
    intro z hz
    have positive : z.im ≠ 0 := (hZ' hz).ne'
    exact ((Complex.continuous_im.continuousAt).zpow₀ hw (Or.inl positive)).continuousWithinAt
  obtain ⟨M, hM⟩ := hZ.exists_bound_of_continuousOn continuousOn
  let α₁ : FiniteAdelesˣ := d⁻¹ * u₀
  let α₃ : FiniteAdelesˣ := d⁻¹ * u₁
  have e₁ : α₁.val = (d⁻¹).val * B.val 0 0 := by simp only [α₁, Units.val_mul, h₀]
  have e₃ : α₃.val = (d⁻¹).val * B.val 1 1 := by simp only [α₃, Units.val_mul, h₁]
  let T := finiteAffine α₁ α₃ ((d⁻¹).val * B.val 1 0) ((d⁻¹).val * (a * B.val 0 0 + a' * B.val 1 0))
    ((d⁻¹).val * (a' * B.val 1 1))
  refine ⟨fun v => M * (‖finitePlaneFactor χ 0 b (planeLevi B d) (planeLevi_mem B d)‖ * C) *
    entryWeight b (T v), ?_, ?_⟩
  · have base := entryWeight_integrable b convergent
    have mapped : Integrable (entryWeight b) (Measure.map T (finiteMeasure.prod finiteMeasure)) := by
      rw [finiteAffine_map]
      exact base.smul_measure (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
    exact ((integrable_map_equiv T (entryWeight b)).mp mapped).const_mul _
  · intro v z hz
    rw [planeCoeff_decomp cusp χ b hw hχ vec spherical a a' d B h01 α₁ α₃ e₁ e₃ κ x v z, norm_mul, norm_mul,
      norm_mul]
    have hMz : ‖(z.im ^ hw : ℝ)‖ ≤ M := hM z hz
    have real_norm : ‖((z.im ^ hw : ℝ) : ℂ)‖ = ‖(z.im ^ hw : ℝ)‖ := Complex.norm_real _
    rw [real_norm]
    have remainder : ‖entryRz cusp vec.val (x * atInfinity (sectionMatrix z) * atFinite B *
        atFinite (entryBlock (T v)))‖ ≤ C := by
      rw [entryRz_of_mem vec.property]
      exact bounded _
    have weight : ‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det (entryBlock (T v)))) b‖ =
        entryWeight b (T v) := by
      unfold entryWeight
      rw [binary_det_atFinite]
      rfl
    rw [weight]
    have n₁ : 0 ≤ ‖finitePlaneFactor χ 0 b (planeLevi B d) (planeLevi_mem B d)‖ := norm_nonneg _
    have n₂ : 0 ≤ entryWeight b (T v) := norm_nonneg _
    calc ‖(z.im ^ hw : ℝ)‖ * (‖finitePlaneFactor χ 0 b (planeLevi B d) (planeLevi_mem B d)‖ *
          (entryWeight b (T v) * ‖entryRz cusp vec.val (x * atInfinity (sectionMatrix z) * atFinite B *
            atFinite (entryBlock (T v)))‖))
        ≤ M * (‖finitePlaneFactor χ 0 b (planeLevi B d) (planeLevi_mem B d)‖ *
          (entryWeight b (T v) * C)) := by
          apply mul_le_mul hMz _ (by positivity) ((norm_nonneg _).trans hMz)
          apply mul_le_mul_of_nonneg_left _ n₁
          exact mul_le_mul_of_nonneg_left remainder n₂
      _ = _ := by ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
