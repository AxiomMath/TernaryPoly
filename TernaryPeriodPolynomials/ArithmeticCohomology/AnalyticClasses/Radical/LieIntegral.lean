module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.LieMeanValue

@[expose] public section


/-!
# The Lie condition for the transfer of the Eichler normal form

For a scalar form `F` with Eichler data and `n ≥ 2`, the coinvariant part of the antisymmetrised
mixed radical derivative of the real good-line transfer of the Eichler normal form is integrable
over the good-line coordinate and integrates to zero. Integrability comes from the bound
`|S_{F_h}(u)| ≤ C · TS(u)`, obtained by transporting the scalar form back to the moved point
`h B(u)` where it is evaluated at the fixed point `i`; the vanishing is the mean value identity
for the obstruction shape, together with the reflection `(s, t) ↦ (s, -t)` for its
antiholomorphic part.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

variable {n : ℕ}

namespace RadicalLie

open EdgeExplicit

/-! ### The decay of the obstruction shape -/

/-- The decay `TS(u) = (√R)^{-(n+3)} = (1 + s² + t²)^{-(n+3)/4}` as a real power. -/
theorem sqrt_gsRadius_pow_inv (u : ℝ × ℝ) :
    (Real.sqrt (gsRadius u) ^ (n + 3))⁻¹ =
      (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) := by
  have hx : 0 ≤ 1 + u.1 ^ 2 + u.2 ^ 2 := by positivity
  rw [Real.rpow_neg hx, gsRadius, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx,
    ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 2
  push_cast
  ring

theorem integrable_transferDecay (hn : 2 ≤ n) :
    Integrable fun u : ℝ × ℝ => (Real.sqrt (gsRadius u) ^ (n + 3))⁻¹ := by
  have hmass := (integral_one_add_sq_rpow_neg (a := ((n : ℝ) + 3) / 4) (by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)).1
  exact hmass.congr (Filter.Eventually.of_forall fun u => (sqrt_gsRadius_pow_inv u).symm)

section Eichler

variable {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
include hF

/-- **The obstruction shape at the moved point**: `S_{F_h}(u) = TS(u) ζ^{n+3} F_{h B(u)}(i)`. -/
theorem obstructionShape_eq_moved (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    obstructionShape n (F h) u =
      transferScale n u * radialUnit u ^ (n + 3) * F (movedPoint u h) Complex.I := by
  rw [eichlerData_movedPoint hF, obstructionShape, ← transferScale_mul_scale (n := n) u]
  ring

theorem continuous_obstructionShape (h : BinaryAdelicGL) :
    Continuous (obstructionShape n (F h)) := by
  have hα : Continuous fun u : ℝ × ℝ => ((gsAlpha u : ℂ) ^ (n + 3))⁻¹ :=
    ((Complex.continuous_ofReal.comp continuous_gsAlpha).pow _).inv₀
      fun u => pow_ne_zero _ (gsAlpha_complex_ne_zero u)
  have hf : Continuous fun u => F h (goodPoint u) :=
    (hF.holomorphic h).continuousOn.comp_continuous continuous_goodPoint goodPoint_im_pos
  exact (hα.mul (continuous_radialUnit.pow _)).mul hf

theorem exists_bound_obstructionShape :
    ∃ C, ∀ h u, ‖obstructionShape n (F h) u‖ ≤ C * (Real.sqrt (gsRadius u) ^ (n + 3))⁻¹ := by
  obtain ⟨C, hC⟩ := hF.bounded {Complex.I} (by simp) isCompact_singleton
  refine ⟨C, fun h u => ?_⟩
  have hq := Real.sqrt_pos.mpr (gsRadius_pos u)
  have scale : ‖transferScale n u‖ = (Real.sqrt (gsRadius u) ^ (n + 3))⁻¹ := by
    rw [transferScale_eq, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hq.le]
  rw [obstructionShape_eq_moved hF, norm_mul, norm_mul, scale, norm_pow]
  have unit : ‖radialUnit u‖ ^ (n + 3) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_radialUnit_le u)
  have value := hC (movedPoint u h) Complex.I (Set.mem_singleton _)
  have decay : 0 ≤ (Real.sqrt (gsRadius u) ^ (n + 3))⁻¹ := by positivity
  calc (Real.sqrt (gsRadius u) ^ (n + 3))⁻¹ * ‖radialUnit u‖ ^ (n + 3) *
        ‖F (movedPoint u h) Complex.I‖
      ≤ (Real.sqrt (gsRadius u) ^ (n + 3))⁻¹ * 1 * C := by gcongr
    _ = C * (Real.sqrt (gsRadius u) ^ (n + 3))⁻¹ := by ring

theorem integrable_obstructionShape (hn : 2 ≤ n) (h : BinaryAdelicGL) :
    Integrable (obstructionShape n (F h)) := by
  obtain ⟨C, hC⟩ := exists_bound_obstructionShape hF
  exact ((integrable_transferDecay hn).const_mul C).mono'
    (continuous_obstructionShape hF h).aestronglyMeasurable
    (Filter.Eventually.of_forall (hC h))

/-! ### The reflection `(s, t) ↦ (s, -t)` -/

omit hF in
theorem measurePreserving_reflectCoordinate :
    MeasurePreserving reflectCoordinate (volume : Measure (ℝ × ℝ)) volume :=
  (MeasurePreserving.id _).prod (Measure.measurePreserving_neg _)

omit hF in
theorem measurableEmbedding_reflectCoordinate : MeasurableEmbedding reflectCoordinate :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)).measurableEmbedding

theorem integrable_obstructionShape_reflect (hn : 2 ≤ n) (h : BinaryAdelicGL) :
    Integrable fun u => obstructionShape n (F h) (reflectCoordinate u) :=
  (measurePreserving_reflectCoordinate.integrable_comp_emb
    measurableEmbedding_reflectCoordinate).mpr (integrable_obstructionShape hF hn h)

/-! ### The Lie condition -/

theorem radicalObstruction_eichlerNormal_fun (h : BinaryAdelicGL) :
    (fun u => radicalObstruction (eichlerNormal n F) u h) = fun u =>
      2⁻¹ * ((n : ℂ) + 1) * ((-1) ^ (n + 1) * obstructionShape n (F h) u +
        obstructionShape n (F (h * atInfinity UpperHalfPlane.J)) (reflectCoordinate u)) :=
  funext fun u => radicalObstruction_eichlerNormal F hF u h

/-- **Integrability of the Lie obstruction density.** -/
theorem integrable_radicalObstruction (hn : 2 ≤ n) (h : BinaryAdelicGL) :
    Integrable (fun u => radicalObstruction (eichlerNormal n F) u h)
      ((volume : Measure ℝ).prod volume) := by
  rw [← Measure.volume_eq_prod, radicalObstruction_eichlerNormal_fun hF]
  exact (((integrable_obstructionShape hF hn h).const_mul _).add
    (integrable_obstructionShape_reflect hF hn _)).const_mul _

/-- **The Lie condition**: the coinvariant part of the antisymmetrised mixed radical derivative of
the real good-line transfer of the Eichler normal form integrates to zero. -/
theorem integral_radicalObstruction (hn : 2 ≤ n) (h : BinaryAdelicGL) :
    ∫ u, radicalObstruction (eichlerNormal n F) u h ∂((volume : Measure ℝ).prod volume) = 0 := by
  rw [← Measure.volume_eq_prod, radicalObstruction_eichlerNormal_fun hF, integral_const_mul,
    integral_add ((integrable_obstructionShape hF hn h).const_mul _)
      (integrable_obstructionShape_reflect hF hn _), integral_const_mul,
    measurePreserving_reflectCoordinate.integral_comp measurableEmbedding_reflectCoordinate,
    integral_obstructionShape (hF.holomorphic h) (integrable_obstructionShape hF hn h),
    integral_obstructionShape (hF.holomorphic _) (integrable_obstructionShape hF hn _)]
  ring

end Eichler

end RadicalLie

end TernaryPeriodPolynomials.AnalyticClasses
