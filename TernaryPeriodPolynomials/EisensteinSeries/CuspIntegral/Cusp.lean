module

public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Lift
public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Scaling
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ArithmeticModularity

@[expose] public section


/-!
# The unipotent integral of the adelic lift

For `g = γ r κ` and `γ = b σ` (`b` upper triangular, `σ ∈ SL₂(ℤ)`), the function
`u ↦ φ_f (n(u) g)` equals `Ψ (c u)` with `Ψ v = φ_f (n(v) σ r κ)` periodic under `ℚ`.
By rational scaling the integral over `[0,1) × Ẑ` equals that of `u ↦ Ψ (3 u)`, which is the
classical function `F (3 x)`, `F y = liftReal f (σ⁻¹ n(y) σ r)`, whose integral over a period
vanishes (`integral_liftReal_unipotent`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.CuspIntegral

theorem infGL_finGL_mul (a c : BinaryRealGL) (b d : BinaryFiniteGL) :
    infGL a * finGL b * (infGL c * finGL d) = infGL (a * c) * finGL (b * d) := by
  calc infGL a * finGL b * (infGL c * finGL d) = infGL a * (finGL b * infGL c) * finGL d := by
        simp only [mul_assoc]
    _ = infGL a * (infGL c * finGL b) * finGL d := by rw [infGL_finGL_comm c b]
    _ = infGL (a * c) * finGL (b * d) := by
        rw [map_mul, map_mul]
        simp only [mul_assoc]

theorem binaryUnipotent_adele (a : ℝ) (b : FiniteAdeles) :
    binaryUnipotent ((a, b) : Adeles) = infGL (binaryUnipotent a) * finGL (binaryUnipotent b) := by
  change _ = atInfinity _ * atFinite _
  rw [← PlaneEisensteinContinuation.Norm.combineGL_eq_mul]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [binaryUnipotent, combineGL, pairMatrix, Prod.ext_iff]

theorem redGL_unipotent_zero {w : IntegralAdeles} (hw : integralReduction w = 0) :
    redGL (binaryUnipotent w) = 1 := by
  have : redGL (binaryUnipotent w) = binaryUnipotent (integralReduction w) :=
    PlaneEisensteinContinuation.BinaryStrongApproximation.unipotent_map integralReduction w
  rw [this, hw]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binaryUnipotent]

theorem isDecomp_unipotent (σ : SpecialLinearGroup (Fin 2) ℤ) (x : ℝ) (w : IntegralAdeles)
    (hw : integralReduction w = 0) (r : BinaryRealGL)
    (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) (κ : BinaryFiniteGL) (hκ : κ ∈ levelGroup) :
    IsDecomp (binaryUnipotent ((x, integralEmbedding w) : Adeles) *
        (ratGL (SpecialLinearGroup.mapGL ℚ σ) * (infGL r * finGL κ)))
      (SpecialLinearGroup.mapGL ℚ σ)
      (SpecialLinearGroup.mapGL ℝ σ⁻¹ * binaryUnipotent x * (SpecialLinearGroup.mapGL ℝ σ * r))
      (intGL ((SpecialLinearGroup.mapGL IntegralAdeles σ)⁻¹ * binaryUnipotent w *
        SpecialLinearGroup.mapGL IntegralAdeles σ) * κ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [det_mapGL_unipotent_mul, map_mul, det_mapGL, one_mul]
    exact hr
  · refine Subgroup.mul_mem _ ?_ hκ
    rw [mem_levelGroup_iff]
    refine ⟨_, rfl, ?_⟩
    rw [map_mul, map_mul, map_inv, redGL_unipotent_zero hw]
    simp
  · have hrat : ratGL (SpecialLinearGroup.mapGL ℚ σ) =
        infGL (SpecialLinearGroup.mapGL ℝ σ) *
          finGL (intGL (SpecialLinearGroup.mapGL IntegralAdeles σ)) :=
      PlaneEisensteinContinuation.ArithmeticModularity.rational_decomposition σ
    have hn : binaryUnipotent ((x, integralEmbedding w) : Adeles) =
        infGL (binaryUnipotent x) * finGL (intGL (binaryUnipotent w)) := by
      rw [binaryUnipotent_adele]
      congr 2
      exact (PlaneEisensteinContinuation.BinaryStrongApproximation.unipotent_map
        integralEmbedding w).symm
    have hmapσ : SpecialLinearGroup.mapGL ℝ σ⁻¹ = (SpecialLinearGroup.mapGL ℝ σ)⁻¹ :=
      map_inv _ _
    rw [hrat, hn, hmapσ]
    rw [infGL_finGL_mul (SpecialLinearGroup.mapGL ℝ σ) r
        (intGL (SpecialLinearGroup.mapGL IntegralAdeles σ)) κ,
      infGL_finGL_mul (binaryUnipotent x) (SpecialLinearGroup.mapGL ℝ σ * r) _ _,
      infGL_finGL_mul (SpecialLinearGroup.mapGL ℝ σ)
        ((SpecialLinearGroup.mapGL ℝ σ)⁻¹ * binaryUnipotent x *
          (SpecialLinearGroup.mapGL ℝ σ * r)) _ _]
    congr 2
    · group
    · simp only [map_mul, map_inv]
      group

theorem measurableSet_additiveDomain : MeasurableSet additiveDomain :=
  measurableSet_Ico.prod integralLattice_isCompact.measurableSet

/-- The cuspidal integral of the adelic lift: integrability and vanishing. -/
theorem adelicLift_cuspidal {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (g : BinaryAdelicGL) :
    IntegrableOn (fun u => adelicLift f (binaryUnipotent u * g)) additiveDomain adeleMeasure ∧
      (∫ u in additiveDomain, adelicLift f (binaryUnipotent u * g) ∂adeleMeasure) = 0 := by
  obtain ⟨γ, r, κ, hg⟩ := exists_isDecomp g
  obtain ⟨b, c, σ, hγ, hb⟩ := exists_upper_triangular_mul γ
  have hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val := hg.1
  have hκ : κ ∈ levelGroup := hg.2.1
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : BinaryAdelicGL,
      g₀ = ratGL (SpecialLinearGroup.mapGL ℚ σ) * (infGL r * finGL κ) := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Adeles → ℂ,
      ∀ v, Ψ v = adelicLift f (binaryUnipotent v * g₀) := ⟨_, fun _ => rfl⟩
  have hgeq : g = ratGL b * g₀ := by
    rw [hg₀, hg.2.2, hγ, map_mul, mul_assoc]
  have hrew : ∀ u, adelicLift f (binaryUnipotent u * g) = Ψ (rationalAdele c.val * u) := by
    intro u
    rw [hΨ, hgeq, ← mul_assoc, hb u, mul_assoc]
    exact adelicLift_ratGL_mul f b _
  have hper : ∀ q : ℚ, ∀ v, Ψ (rationalAdele q + v) = Ψ v := by
    intro q v
    have hq : binaryUnipotent (rationalAdele q) = ratGL (binaryUnipotent q) :=
      (PlaneEisensteinContinuation.BinaryStrongApproximation.unipotent_map rationalAdele q).symm
    rw [hΨ, hΨ, PlaneEisensteinContinuation.BinaryStrongApproximation.unipotent_add,
      mul_assoc, hq]
    exact adelicLift_ratGL_mul f _ _
  -- the classical function along the unipotent line
  have hr' : 0 < (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ σ * r) : ℝˣ).val := by
    rw [map_mul, det_mapGL, one_mul]
    exact hr
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℂ, ∀ y, F y = liftReal f (SpecialLinearGroup.mapGL ℝ σ⁻¹ *
      binaryUnipotent y * (SpecialLinearGroup.mapGL ℝ σ * r)) := ⟨_, fun _ => rfl⟩
  have hFcont : Continuous F := by
    rw [funext hF]
    exact continuous_liftReal_unipotent f σ⁻¹ (SpecialLinearGroup.mapGL ℝ σ * r) hr'
  obtain ⟨C, hC⟩ := liftReal_bounded f
  have hFbd : ∀ y, ‖F y‖ ≤ C := fun y => by
    rw [hF]
    exact hC _ (by rw [det_mapGL_unipotent_mul]; exact hr')
  have hFint : ∫ y in (0 : ℝ)..3, F y = 0 := by
    rw [funext hF]
    exact integral_liftReal_unipotent f σ⁻¹ (SpecialLinearGroup.mapGL ℝ σ * r) hr'
  have hΨ3 : ∀ u ∈ additiveDomain, Ψ (rationalAdele (3 : ℚ) * u) = F (3 * u.1) := by
    intro u hu
    obtain ⟨w₀, hw₀⟩ := hu.2
    have hu3 : rationalAdele (3 : ℚ) * u =
        ((3 : ℝ) * u.1, integralEmbedding ((3 : IntegralAdeles) * w₀)) := by
      refine Prod.ext ?_ ?_
      · change ((3 : ℚ) : ℝ) * u.1 = (3 : ℝ) * u.1
        norm_num
      · change algebraMap ℚ FiniteAdeles 3 * u.2 = integralEmbedding (3 * w₀)
        rw [map_mul, ← hw₀, map_ofNat (algebraMap ℚ FiniteAdeles) 3, map_ofNat integralEmbedding 3]
    have hred : integralReduction ((3 : IntegralAdeles) * w₀) = 0 := by
      have h3 : integralReduction (3 : IntegralAdeles) = 0 := by
        rw [map_ofNat]
        decide
      rw [map_mul, h3, zero_mul]
    rw [hΨ, hu3, hF, hg₀]
    exact adelicLift_eq_of_isDecomp f (isDecomp_unipotent σ (3 * u.1) _ hred r hr κ hκ)
  have hGint : IntegrableOn (fun u : Adeles => F (3 * u.1)) additiveDomain adeleMeasure := by
    refine Measure.integrableOn_of_bounded (M := C) ?_ ?_ ?_
    · rw [adeleMeasure_additiveDomain]
      exact ENNReal.one_ne_top
    · exact (hFcont.comp (continuous_const.mul continuous_fst)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun u => hFbd _)
  have hGintegral : ∫ u in additiveDomain, F (3 * u.1) ∂adeleMeasure = 0 := by
    have hrestrict : adeleMeasure.restrict additiveDomain =
        (volume.restrict (Set.Ico (0 : ℝ) 1)).prod
          (finiteMeasure.restrict (Set.range integralEmbedding)) :=
      (Measure.prod_restrict _ _).symm
    have hν : (finiteMeasure.restrict (Set.range integralEmbedding)).real Set.univ = 1 := by
      simp [Measure.real, finiteMeasure_integralLattice]
    rw [hrestrict, integral_fun_fst (fun x : ℝ => F (3 * x)), hν, one_smul,
      integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_mul_left F (by norm_num : (3 : ℝ) ≠ 0)]
    simp [hFint]
  obtain ⟨c3, hc3⟩ : ∃ c3 : ℚˣ, c3.val = 3 := ⟨Units.mk0 3 (by norm_num), rfl⟩
  have hint3 : IntegrableOn (fun u => Ψ (rationalAdele c3.val * u)) additiveDomain
      adeleMeasure := by
    rw [hc3]
    exact hGint.congr_fun (fun u hu => (hΨ3 u hu).symm) measurableSet_additiveDomain
  have hfun : (fun u => adelicLift f (binaryUnipotent u * g)) =
      fun u => Ψ (rationalAdele c.val * u) := funext hrew
  rw [hfun]
  refine ⟨(rational_periodic_integrableOn_scaling Ψ hper c).mpr
    ((rational_periodic_integrableOn_scaling Ψ hper c3).mp hint3), ?_⟩
  calc ∫ u in additiveDomain, Ψ (rationalAdele c.val * u) ∂adeleMeasure
      = ∫ u in additiveDomain, Ψ u ∂adeleMeasure := rational_periodic_integral_scaling Ψ hper c
    _ = ∫ u in additiveDomain, Ψ (rationalAdele c3.val * u) ∂adeleMeasure :=
        (rational_periodic_integral_scaling Ψ hper c3).symm
    _ = ∫ u in additiveDomain, F (3 * u.1) ∂adeleMeasure := by
        rw [hc3]
        exact setIntegral_congr_fun measurableSet_additiveDomain (fun u hu => hΨ3 u hu)
    _ = 0 := hGintegral

end TernaryPeriodPolynomials.CuspIntegral
