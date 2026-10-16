module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Realize
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.L1

@[expose] public section


/-!
# Scalar properties of the realization

For a Bergman vector `F` whose values are fixed by an open compact subgroup `U` and whose
weighted `L¹` integral is finite, the realization `realizeU M hU F` is given by an absolutely
convergent integral, because the evaluation functionals of `U`-fixed vectors are uniformly
bounded (`exists_bound_evalU`). Each of the four scalar properties of
`CuspIntegral.IsCuspidalLike` then holds pointwise in the integrand: left
`GL₂(ℚ)`-invariance, the central character and boundedness directly, and cuspidality after
exchanging the unipotent integral with the realization integral (Fubini). The realization is
linear on such vectors.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
open TernaryPeriodPolynomials.CuspIntegral

namespace TernaryPeriodPolynomials.Regularity

/-! ### Continuity of the matrices involved -/

/-- A map into a group of units is continuous on a set if its values and their inverses are. -/
theorem continuousOn_units {X R : Type*} [TopologicalSpace X] [Monoid R] [TopologicalSpace R]
    {f : X → Rˣ} {s : Set X} (h₁ : ContinuousOn (fun x => ((f x : Rˣ) : R)) s)
    (h₂ : ContinuousOn (fun x => (((f x)⁻¹ : Rˣ) : R)) s) : ContinuousOn f s :=
  Units.isEmbedding_embedProduct.isInducing.continuousOn_iff.mpr
    (h₁.prodMk (MulOpposite.continuous_op.comp_continuousOn h₂))

theorem gBar_inv_val {w : ℂ} (hw : w.im ≠ 0) :
    (((gBar w)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-(w.im)⁻¹, w.re / w.im; 0, 1] := by
  rw [Matrix.coe_units_inv, gBar_val hw]
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  ring

theorem continuousOn_gBar : ContinuousOn gBar offReal := by
  refine continuousOn_units ?_ ?_
  · have h : Continuous fun w : ℂ => !![-w.im, w.re; 0, (1 : ℝ)] := by
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    exact h.continuousOn.congr fun w hw => gBar_val hw
  · have h : ContinuousOn (fun w : ℂ => !![-(w.im)⁻¹, w.re / w.im; 0, (1 : ℝ)]) offReal := by
      refine continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => ?_
      have him : ContinuousOn (fun w : ℂ => (w.im)⁻¹) offReal :=
        Complex.continuous_im.continuousOn.inv₀ fun w hw => hw
      have hre : ContinuousOn (fun w : ℂ => w.re / w.im) offReal :=
        Complex.continuous_re.continuousOn.div Complex.continuous_im.continuousOn fun w hw => hw
      fin_cases i <;> fin_cases j
      · exact him.neg
      · exact hre
      · exact continuousOn_const
      · exact continuousOn_const
    exact h.congr fun w hw => gBar_inv_val hw

theorem continuous_atInfinity_binary :
    Continuous (atInfinity : GL (Fin 2) ℝ → BinaryAdelicGL) := by
  have value : Continuous (fun g : GL (Fin 2) ℝ => g.val) := Units.continuous_val
  have inverse : Continuous (fun g : GL (Fin 2) ℝ => (g⁻¹).val) :=
    Units.continuous_val.comp continuous_inv
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous (fun g : GL (Fin 2) ℝ =>
      (g.val i j, (1 : Matrix (Fin 2) (Fin 2) FiniteAdeles) i j))
    exact ((continuous_apply j).comp ((continuous_apply i).comp value)).prodMk continuous_const
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous (fun g : GL (Fin 2) ℝ =>
      ((g⁻¹).val i j, (1 : Matrix (Fin 2) (Fin 2) FiniteAdeles) i j))
    exact ((continuous_apply j).comp ((continuous_apply i).comp inverse)).prodMk continuous_const

theorem continuous_binaryUnipotent_adeles :
    Continuous (fun u : Adeles => (binaryUnipotent u : BinaryAdelicGL)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;> simp only [binaryUnipotent] <;> fun_prop
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;> simp only [binaryUnipotent] <;> fun_prop

theorem atInfinity_mul_binary (g h : GL (Fin 2) ℝ) :
    (atInfinity (g * h) : BinaryAdelicGL) = atInfinity g * atInfinity h := by
  rw [atInfinity, atInfinity, atInfinity, combineGL_mul, mul_one]

theorem atInfinity_mul_atFinite_comm (g : GL (Fin 2) ℝ) (f : BinaryFiniteGL) :
    (atInfinity g : BinaryAdelicGL) * atFinite f = atFinite f * atInfinity g := by
  rw [atInfinity, atFinite, combineGL_mul, combineGL_mul]
  simp only [mul_one, one_mul]

variable {k : ℕ} (M : FiniteModel k)

/-! ### Bounds and continuity of the evaluation functionals -/

/-- The evaluation functionals on `U`-fixed vectors are uniformly bounded. -/
theorem exists_bound_evalFixedL {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : BinaryAdelicGL) (v : fixedSubmodule M.σ U),
      ‖evalFixedL M hU y v‖ ≤ C * ‖v‖ := by
  have := M.finiteDimensional U hU
  have hb : ∀ v : fixedSubmodule M.σ U, ∃ C : ℝ, ∀ y,
      ‖M.ε (Submodule.inclusion (fixed_le_finiteSmooth M hU) v) y‖ ≤ C :=
    fun v => (M.like _).bounded
  let Φ : fixedSubmodule M.σ U →ₗ[ℂ] BoundedContinuousFunction BinaryAdelicGL ℂ :=
    { toFun := fun v => BoundedContinuousFunction.ofNormedAddCommGroup
        (M.ε (Submodule.inclusion (fixed_le_finiteSmooth M hU) v)) (M.continuous_ε _)
        (hb v).choose (hb v).choose_spec
      map_add' := fun v w => by
        ext y
        simp [map_add]
      map_smul' := fun c v => by
        ext y
        simp [map_smul] }
  let Φc := LinearMap.toContinuousLinearMap Φ
  refine ⟨‖Φc‖, ContinuousLinearMap.opNorm_nonneg _, fun y v => ?_⟩
  calc ‖evalFixedL M hU y v‖ = ‖Φc v y‖ := rfl
    _ ≤ ‖Φc v‖ := BoundedContinuousFunction.norm_coe_le_norm _ y
    _ ≤ ‖Φc‖ * ‖v‖ := Φc.le_opNorm v

/-- The functionals `evalU` are uniformly bounded. -/
theorem exists_bound_evalU {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : BinaryAdelicGL) (e : M.E), ‖evalU M hU y e‖ ≤ C * ‖e‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_evalFixedL M hU
  refine ⟨C, hC0, fun y e => ?_⟩
  rw [evalU_apply]
  calc ‖evalFixedL M hU y (projU M hU e)‖ ≤ C * ‖projU M hU e‖ := hC y _
    _ ≤ C * ‖e‖ := mul_le_mul_of_nonneg_left (norm_projU_le M hU e) hC0

theorem continuous_evalFixedL {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) :
    Continuous (evalFixedL M hU) := by
  have := M.finiteDimensional U hU
  exact continuous_clm_apply.mpr fun v =>
    M.continuous_ε (Submodule.inclusion (fixed_le_finiteSmooth M hU) v)

/-- Continuity of the realization integrand on `ℂ ∖ ℝ`. -/
theorem continuousOn_evalU_comp {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    {X : Type*} [TopologicalSpace X] {s : Set X} {Y : X → BinaryAdelicGL} (hY : ContinuousOn Y s)
    {G : X → M.E}
    (hG : ContinuousOn G s) : ContinuousOn (fun w => evalU M hU (Y w) (G w)) s :=
  ((continuous_evalFixedL M hU).comp_continuousOn hY).clm_apply
    ((projU M hU).continuous.comp_continuousOn hG)

theorem continuousOn_realizeIntegrand {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    (F : BergmanSpace k M.E) (x : BinaryAdelicGL) :
    ContinuousOn (fun w => evalU M hU (x * atInfinity (gBar w)) (F w) *
      ((|w.im| ^ ((k : ℝ) / 2) : ℝ) : ℂ)) offReal := by
  refine (continuousOn_evalU_comp M hU ?_ (BergmanSpace.continuousOn F)).mul ?_
  · exact continuousOn_const.mul (continuous_atInfinity_binary.comp_continuousOn continuousOn_gBar)
  · exact (Complex.continuous_ofReal.comp
      (Complex.continuous_im.abs.rpow_const fun _ => Or.inr (by positivity))).continuousOn

/-- The realization integrand is bounded by the weighted norm of `F`. -/
theorem norm_realizeIntegrand_le {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) {C : ℝ}
    (hC : ∀ (y : BinaryAdelicGL) (e : M.E), ‖evalU M hU y e‖ ≤ C * ‖e‖)
    (F : BergmanSpace k M.E) (x : BinaryAdelicGL) (w : ℂ) :
    ‖evalU M hU (x * atInfinity (gBar w)) (F w) * ((|w.im| ^ ((k : ℝ) / 2) : ℝ) : ℂ)‖ ≤
      C * (‖F w‖ * |w.im| ^ ((k : ℝ) / 2)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC _ _) (by positivity)

theorem integrable_realizeIntegrand {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    {F : BergmanSpace k M.E} (hF : L1Finite F) (x : BinaryAdelicGL) :
    Integrable (fun w => evalU M hU (x * atInfinity (gBar w)) (F w) *
      ((|w.im| ^ ((k : ℝ) / 2) : ℝ) : ℂ)) hypMeasure := by
  obtain ⟨C, -, hC⟩ := exists_bound_evalU M hU
  refine Integrable.mono' (hF.integrable.const_mul C)
    (BergmanAux.aesm (continuousOn_realizeIntegrand M hU F x))
    (Filter.Eventually.of_forall fun w => norm_realizeIntegrand_le M hU hC F x w)

/-- The realization is bounded by the weighted `L¹` integral. -/
theorem norm_realizeU_le {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) {C : ℝ}
    (hC : ∀ (y : BinaryAdelicGL) (e : M.E), ‖evalU M hU y e‖ ≤ C * ‖e‖)
    {F : BergmanSpace k M.E} (hF : L1Finite F) (x : BinaryAdelicGL) :
    ‖realizeU M hU F x‖ ≤ C * ∫ w, ‖F w‖ * |w.im| ^ ((k : ℝ) / 2) ∂hypMeasure := by
  rw [realizeU, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hF.integrable.const_mul C)
    (Filter.Eventually.of_forall fun w => norm_realizeIntegrand_le M hU hC F x w)

/-! ### Linearity -/

theorem realizeU_add {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    {F G : BergmanSpace k M.E} (hF : L1Finite F) (hG : L1Finite G) :
    realizeU M hU (F + G) = realizeU M hU F + realizeU M hU G := by
  funext x
  rw [Pi.add_apply, realizeU, realizeU, realizeU, ← integral_add
    (integrable_realizeIntegrand M hU hF x) (integrable_realizeIntegrand M hU hG x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [BergmanSpace.add_apply, map_add, add_mul]

theorem realizeU_smul {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) (c : ℂ)
    (F : BergmanSpace k M.E) : realizeU M hU (c • F) = c • realizeU M hU F := by
  funext x
  rw [Pi.smul_apply, realizeU, realizeU, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [BergmanSpace.smul_apply, map_smul, smul_eq_mul, mul_assoc]

/-! ### The scalar cuspidal properties -/

section Like

variable {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) {F : BergmanSpace k M.E}
  (hFU : ∀ w, F w ∈ fixedSubmodule M.σ U)

include hFU in
theorem realizeU_leftRational (γ : BinaryRationalGL) (x : BinaryAdelicGL) :
    realizeU M hU F (GeneralLinearGroup.map rationalAdele γ * x) = realizeU M hU F x := by
  unfold realizeU
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [evalU_of_mem M hU _ (hFU w)]
  rw [mul_assoc, (M.like _).leftRational]

include hFU in
theorem realizeU_central (t : Adelesˣ) (x : BinaryAdelicGL) :
    realizeU M hU F (GeneralLinearGroup.scalar (Fin 2) t * x) = M.χ t * realizeU M hU F x := by
  rw [realizeU, realizeU, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [evalU_of_mem M hU _ (hFU w)]
  rw [mul_assoc, (M.like _).central, mul_assoc]

theorem realizeU_bounded (hF : L1Finite F) : ∃ C : ℝ, ∀ x, ‖realizeU M hU F x‖ ≤ C := by
  obtain ⟨C, -, hC⟩ := exists_bound_evalU M hU
  exact ⟨_, fun x => norm_realizeU_le M hU hC hF x⟩

instance : SFinite hypMeasure := by
  unfold hypMeasure
  infer_instance

/-- The additive fundamental domain has measure one. -/
theorem adeleMeasure_additiveDomain_eq : adeleMeasure additiveDomain = 1 := by
  rw [adeleMeasure, additiveDomain, Measure.prod_prod, finiteMeasure_integralLattice,
    Real.volume_Ico]
  norm_num

instance : IsFiniteMeasure (adeleMeasure.restrict additiveDomain) :=
  ⟨by rw [Measure.restrict_apply_univ, adeleMeasure_additiveDomain_eq]; exact ENNReal.one_lt_top⟩

include hFU in
theorem realizeU_cuspidal (hF : L1Finite F) (g : BinaryAdelicGL) :
    IntegrableOn (fun u => realizeU M hU F (binaryUnipotent u * g)) additiveDomain
        adeleMeasure ∧
      (∫ u in additiveDomain, realizeU M hU F (binaryUnipotent u * g) ∂adeleMeasure) = 0 := by
  obtain ⟨C, -, hC⟩ := exists_bound_evalU M hU
  set Φ : Adeles → ℂ → ℂ := fun u w =>
    evalU M hU (binaryUnipotent u * g * atInfinity (gBar w)) (F w) *
      ((|w.im| ^ ((k : ℝ) / 2) : ℝ) : ℂ) with hΦ
  have hcont : ContinuousOn (Function.uncurry Φ) (Set.univ ×ˢ offReal) := by
    refine (continuousOn_evalU_comp M hU (Y := fun p : Adeles × ℂ =>
      binaryUnipotent p.1 * g * atInfinity (gBar p.2)) (G := fun p : Adeles × ℂ => F p.2)
      ?_ ?_).mul ?_
    · refine ((continuous_binaryUnipotent_adeles.comp continuous_fst).continuousOn.mul
        continuousOn_const).mul ?_
      exact continuous_atInfinity_binary.comp_continuousOn
        (continuousOn_gBar.comp continuous_snd.continuousOn fun p hp => hp.2)
    · exact (BergmanSpace.continuousOn F).comp continuous_snd.continuousOn fun p hp => hp.2
    · exact (Complex.continuous_ofReal.comp ((Complex.continuous_im.comp
        continuous_snd).abs.rpow_const fun _ => Or.inr (by positivity))).continuousOn
  have hmeas : AEStronglyMeasurable (Function.uncurry Φ)
      ((adeleMeasure.restrict additiveDomain).prod hypMeasure) := by
    have h1 : AEStronglyMeasurable (Function.uncurry Φ)
        (((adeleMeasure.restrict additiveDomain).prod volume).restrict (Set.univ ×ˢ offReal)) :=
      hcont.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_offReal)
    refine h1.mono_ac ?_
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    exact Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl BergmanAux.hyp_ac
  have hint : Integrable (Function.uncurry Φ)
      ((adeleMeasure.restrict additiveDomain).prod hypMeasure) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod
      (hF.integrable.const_mul C)) hmeas (Filter.Eventually.of_forall fun p => ?_)
    simp only [one_mul]
    exact norm_realizeIntegrand_le M hU hC F _ p.2
  have hinner : ∀ u, realizeU M hU F (binaryUnipotent u * g) = ∫ w, Φ u w ∂hypMeasure :=
    fun u => rfl
  refine ⟨?_, ?_⟩
  · exact hint.integral_prod_left
  · simp only [hinner]
    rw [integral_integral_swap hint]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hΦ, evalU_of_mem M hU _ (hFU w), Pi.zero_apply]
    rw [integral_mul_const]
    have hz := ((M.like ⟨F w, fixed_le_finiteSmooth M hU (hFU w)⟩).cuspidal
      (g * atInfinity (gBar w))).2
    simp only [← mul_assoc] at hz
    rw [hz, zero_mul]

include hFU in
/-- The realization of an `L¹` vector with `U`-fixed values has the four scalar properties. -/
theorem realizeU_isCuspidalLike (hF : L1Finite F) : IsCuspidalLike M.χ (realizeU M hU F) where
  leftRational := realizeU_leftRational M hU hFU
  central := realizeU_central M hU hFU
  bounded := realizeU_bounded M hU hF
  cuspidal := realizeU_cuspidal M hU hFU hF

end Like

end TernaryPeriodPolynomials.Regularity

end
