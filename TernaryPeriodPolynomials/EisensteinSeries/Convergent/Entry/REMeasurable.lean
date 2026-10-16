module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REPointwise

@[expose] public section


/-!
# R-e: Joint measurability of the plane coefficient function along the radical

`planeCoeff_measurable`: `(v,z) ↦ c_F(w⁻¹u(v)f) F(x b_F(w⁻¹u(v)f))(z)` is measurable (continuous in `z`, locally constant in `v`).

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem planeCoeff_right (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (vec : cusp.smooth) (spherical : vec.val ∈ sphericalSubspace cusp) (x : BinaryAdelicGL) (f : FiniteGL)
    (κ : GeneralLinearGroup (Fin 3) IntegralAdeles) (z : ℂ) :
    planeCoeff cusp χ b hw vec x (f * GeneralLinearGroup.map integralEmbedding κ) z =
      planeCoeff cusp χ b hw vec x f z := by
  rw [planeCoeff_eq, planeCoeff_eq, finitePlaneVector_mul_integral χ 0 b hχ spherical]

theorem planeCoeff_continuous_matrix (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (vec : cusp.smooth) (spherical : vec.val ∈ sphericalSubspace cusp) (x : BinaryAdelicGL) (z : ℂ) :
    Continuous (fun h : FiniteGL => planeCoeff cusp χ b hw vec x h z) := by
  apply continuous_iff_continuousAt.mpr
  intro matrix
  apply Filter.EventuallyEq.continuousAt
  have near : ∀ᶠ other in nhds matrix, matrix⁻¹ * other ∈ finiteIntegralGLLevel 3 :=
    (continuous_const.mul continuous_id).continuousAt.eventually
      ((finiteIntegralGLLevel_isOpen 3).mem_nhds (by
        change matrix⁻¹ * matrix ∈ finiteIntegralGLLevel 3
        rw [inv_mul_cancel]
        exact (finiteIntegralGLLevel 3).one_mem))
  filter_upwards [near] with other member
  obtain ⟨compact, equality⟩ := member
  have factors : other = matrix * GeneralLinearGroup.map integralEmbedding compact := by
    rw [equality, mul_inv_cancel_left]
  rw [factors, planeCoeff_right cusp χ b hw hχ vec spherical]

theorem planeCoeff_continuous_point (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ)
    (vec : cusp.smooth) (x : BinaryAdelicGL) (h : FiniteGL) :
    Continuous (fun z : {z : ℂ // 0 < z.im} => planeCoeff cusp χ b hw vec x h z.1) := by
  unfold planeCoeff
  refine continuous_const.mul ?_
  have analytic := cuspScalarWeightedRealization_analytic cusp hw vec
    (x * atFinite (planeBlockGL (finitePlaneParabolic h) (finitePlaneParabolic_mem h)))
  exact analytic.continuousOn.comp_continuous continuous_subtype_val (fun z => z.2)

theorem radical_translate_continuous (f : FiniteGL) :
    Continuous (fun v : FiniteAdeles × FiniteAdeles => weyl⁻¹ * lineUnipotent v.1 v.2 * f) := by
  have equality : (fun v : FiniteAdeles × FiniteAdeles => weyl⁻¹ * lineUnipotent v.1 v.2 * f) =
      fun v => planeOppositeStandardMatrix v.1 v.2 * (permMatrix FiniteAdeles * f) := by
    funext v
    rw [← weyl_inv_lineUnipotent_perm]
    simp only [mul_assoc]
    rw [← mul_assoc (permMatrix FiniteAdeles) (permMatrix FiniteAdeles) f, permMatrix_mul_self, one_mul]
  rw [equality]
  exact planeOppositeStandardMatrix_continuous.mul continuous_const

theorem planeCoeff_measurable (cusp : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ) (hw : ℤ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    (vec : cusp.smooth) (spherical : vec.val ∈ sphericalSubspace cusp) (x : BinaryAdelicGL) (f : FiniteGL) :
    Measurable (fun w : (FiniteAdeles × FiniteAdeles) × {z : ℂ // 0 < z.im} =>
      planeCoeff cusp χ b hw vec x (weyl⁻¹ * lineUnipotent w.1.1 w.1.2 * f) w.2.1) := by
  let u : {z : ℂ // 0 < z.im} → FiniteAdeles × FiniteAdeles → ℂ := fun z v =>
    planeCoeff cusp χ b hw vec x (weyl⁻¹ * lineUnipotent v.1 v.2 * f) z.1
  have cont : ∀ v : FiniteAdeles × FiniteAdeles, Continuous fun z : {z : ℂ // 0 < z.im} => u z v :=
    fun v => planeCoeff_continuous_point cusp χ b hw vec x _
  have meas : ∀ z : {z : ℂ // 0 < z.im}, Measurable (u z) := fun z =>
    ((planeCoeff_continuous_matrix cusp χ b hw hχ vec spherical x z.1).comp
      (radical_translate_continuous f)).measurable
  have joint : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable (ι := {z : ℂ // 0 < z.im})
      (α := FiniteAdeles × FiniteAdeles) (β := ℂ) (u := u) cont meas
  have swapped : Measurable (Function.uncurry u ∘ Prod.swap :
      (FiniteAdeles × FiniteAdeles) × {z : ℂ // 0 < z.im} → ℂ) :=
    joint.comp (measurable_swap (α := FiniteAdeles × FiniteAdeles) (β := {z : ℂ // 0 < z.im}))
  exact swapped

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
