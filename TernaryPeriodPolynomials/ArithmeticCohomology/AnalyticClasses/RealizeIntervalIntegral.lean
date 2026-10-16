module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.AnalyticFamilies
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineUniformDecay

@[expose] public section



/-!
# The realization commutes with path integrals of real translates

`CuspidalRepresentation.realize` is not assumed continuous. For a smooth (here: analytic)
vector fixed by the finite congruence level, the orbit `M ↦ π(M) v` lifts locally into an
analytic stage, a Banach space on which the sup-norm realization is continuous
(`PlaneEisensteinContinuation`: admissibility and the closed-graph theorem). Hence, along a
continuous path of real matrices, the realization of the Hilbert-space interval integral of
`φ(t) π(γ(t)) v` is the scalar interval integral of the realized translates.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Set Filter Topology
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.AnalyticClasses

/-- The upper-left `2 × 2` block of a `3 × 3` real matrix. -/
def topLeft (M : PlaneMatrix) : BinaryMatrix := !![M 0 0, M 0 1; M 1 0, M 1 1]

/-- The block map as a continuous linear map. -/
def topLeftCLM : PlaneMatrix →L[ℝ] BinaryMatrix :=
  LinearMap.toContinuousLinearMap
    { toFun := topLeft
      map_add' := fun M N => by
        ext i j; fin_cases i <;> fin_cases j <;> simp [topLeft]
      map_smul' := fun c M => by
        ext i j; fin_cases i <;> fin_cases j <;> simp [topLeft] }

theorem topLeftCLM_apply (M : PlaneMatrix) : topLeftCLM M = topLeft M := rfl

theorem topLeft_planeBlock (N : BinaryMatrix) (d : ℝ) : topLeft (planeBlock N d) = N := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [topLeft, planeBlock]

theorem topLeft_add (M N : PlaneMatrix) : topLeft (M + N) = topLeft M + topLeft N :=
  map_add topLeftCLM M N

/-- The orbit family parameterized by `3 × 3` matrices through their upper-left block. -/
def orbitFamily (data : CuspidalRepresentation) (vector : data.H) (M : PlaneMatrix) : data.H :=
  realOrbit data vector (topLeft M)

theorem realOrbit_realOrbit (data : CuspidalRepresentation) (vector : data.H) (x N : BinaryMatrix)
    (hx : x.det ≠ 0) (hN : N.det ≠ 0) :
    realOrbit data (realOrbit data vector N) x = realOrbit data vector (x * N) := by
  unfold realOrbit
  have hx' : (invertibleMatrix x).val = x := invertibleMatrix_val x hx
  have hprod := invertibleMatrix_left_mul (invertibleMatrix x) N hN
  rw [hx'] at hprod
  rw [hprod, Height.atInfinity_mul, map_mul, Module.End.mul_apply]

theorem familyOrbit_analyticAt (data : CuspidalRepresentation) (vector : data.smooth)
    (M₀ : BinaryMatrix) (hM₀ : M₀.det ≠ 0) :
    AnalyticAt ℝ (familyOrbit data (orbitFamily data vector.val)) (1, planeBlock M₀ 0) := by
  have identityRegularity : AnalyticAt ℝ (realOrbit data vector.val) 1 :=
    (SobolevSeminorms.smooth_orbit_contDiffAt_one data vector).analyticAt
  have atPoint : AnalyticAt ℝ (realOrbit data vector.val) M₀ := by
    have h := AnalyticOrbit.realOrbit_analyticAt_of_one data vector.val identityRegularity
      (invertibleMatrix M₀)
    rwa [invertibleMatrix_val M₀ hM₀] at h
  let B : BinaryMatrix →L[ℝ] BinaryMatrix →L[ℝ] BinaryMatrix :=
    LinearMap.toContinuousLinearMap leftMultiplicationLinear
  have hmul : AnalyticAt ℝ (fun p : JointMatrix => p.1 * topLeft p.2) (1, planeBlock M₀ 0) := by
    have hB := B.analyticAt_bilinear ((1 : BinaryMatrix), topLeft (planeBlock M₀ 0))
    have hpair : AnalyticAt ℝ (fun p : JointMatrix => (p.1, topLeftCLM p.2)) (1, planeBlock M₀ 0) :=
      ((ContinuousLinearMap.fst ℝ BinaryMatrix PlaneMatrix).analyticAt _).prod
        ((topLeftCLM.comp (ContinuousLinearMap.snd ℝ BinaryMatrix PlaneMatrix)).analyticAt _)
    exact AnalyticAt.comp (g := fun q : BinaryMatrix × BinaryMatrix => B q.1 q.2)
      (f := fun p : JointMatrix => (p.1, topLeftCLM p.2)) hB hpair
  have hvalue : (1 : BinaryMatrix) * topLeft (planeBlock M₀ 0) = M₀ := by
    rw [one_mul, topLeft_planeBlock]
  have composite : AnalyticAt ℝ (fun p : JointMatrix => realOrbit data vector.val (p.1 * topLeft p.2))
      (1, planeBlock M₀ 0) := by
    have atPoint' : AnalyticAt ℝ (realOrbit data vector.val)
        ((fun p : JointMatrix => p.1 * topLeft p.2) (1, planeBlock M₀ 0)) := by
      simpa only [hvalue] using atPoint
    exact AnalyticAt.comp (g := realOrbit data vector.val)
      (f := fun p : JointMatrix => p.1 * topLeft p.2) atPoint' hmul
  apply composite.congr
  have hopen : IsOpen {p : JointMatrix | p.1.det ≠ 0 ∧ (topLeft p.2).det ≠ 0} := by
    apply IsOpen.inter
    · exact isOpen_ne.preimage (continuous_fst.matrix_det)
    · exact isOpen_ne.preimage ((topLeftCLM.continuous.comp continuous_snd).matrix_det)
  have hmem : ((1 : BinaryMatrix), planeBlock M₀ 0) ∈
      {p : JointMatrix | p.1.det ≠ 0 ∧ (topLeft p.2).det ≠ 0} := by
    refine ⟨by simp, ?_⟩
    rw [topLeft_planeBlock]; exact hM₀
  filter_upwards [hopen.mem_nhds hmem] with p hp
  exact (realOrbit_realOrbit data vector.val p.1 (topLeft p.2) hp.1 hp.2).symm

/-- The block embedding of `2 × 2` matrices, as a continuous linear map. -/
def planeBlockCLM : BinaryMatrix →L[ℝ] PlaneMatrix :=
  LinearMap.toContinuousLinearMap
    { toFun := fun N => planeBlock N 0
      map_add' := fun M N => by
        ext i j; fin_cases i <;> fin_cases j <;> simp [planeBlock]
      map_smul' := fun c M => by
        ext i j; fin_cases i <;> fin_cases j <;> simp [planeBlock] }

theorem planeBlockCLM_apply (N : BinaryMatrix) : planeBlockCLM N = planeBlock N 0 := rfl

theorem nnnorm_planeBlock_le (N : BinaryMatrix) : ‖planeBlock N 0‖₊ ≤ ‖N‖₊ := by
  rw [Matrix.nnnorm_le_iff]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBlock, Matrix.nnnorm_entry_le_entrywise_sup_nnnorm]

/-- Real translates of a finite-level fixed vector are finite-level fixed. -/
theorem realOrbit_fixed (data : CuspidalRepresentation) (vector : data.H)
    (fixed : vector ∈ BinaryLevel.fixedSubspace data BinaryLevel.finiteCongruence) (M : BinaryMatrix) :
    realOrbit data vector M ∈ BinaryLevel.fixedSubspace data BinaryLevel.finiteCongruence := by
  intro element
  unfold realOrbit
  rw [← Module.End.mul_apply, ← map_mul, FiniteLevel.atFinite_atInfinity_commute, map_mul,
    Module.End.mul_apply, fixed element]

/-- **Local commutation.** Near an invertible matrix, the realization commutes with interval
integrals of continuous scalar multiples of real translates. -/
theorem realize_intervalIntegral_local (data : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages data) (vector : data.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace data BinaryLevel.finiteCongruence)
    (M₀ : BinaryMatrix) (hM₀ : M₀.det ≠ 0) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ (γ : ℝ → BinaryMatrix) (φ : ℝ → ℂ) (a b : ℝ), a ≤ b →
      ContinuousOn γ (Icc a b) → ContinuousOn φ (Icc a b) → (∀ t ∈ Icc a b, ‖γ t - M₀‖₊ ≤ r) →
      ∃ w : data.smooth, w.val = (∫ t in a..b, φ t • realOrbit data vector.val (γ t)) ∧
        ∀ h, data.realize w h =
          ∫ t in a..b, φ t * data.realize vector (h * atInfinity (invertibleMatrix (γ t))) := by
  obtain ⟨series, R, expansion⟩ := familyOrbit_analyticAt data vector M₀ hM₀
  obtain ⟨radius, positiveRadius, radiusBound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp expansion.r_pos
  have radiusPositive : (0 : ℝ≥0) < radius := by exact_mod_cast positiveRadius
  have halfPositive : (0 : ℝ≥0) < radius / 2 := div_pos radiusPositive (by norm_num)
  have halfBound : ((radius / 2 : ℝ≥0) : ENNReal) + ((radius / 2 : ℝ≥0) : ENNReal) < R := by
    rw [← ENNReal.coe_add, add_halves]
    exact radiusBound
  let center : PlaneMatrix := planeBlock M₀ 0
  have fixedFamily (offset : ParameterBall (radius / 2)) :
      orbitFamily data vector.val (center + offset.val) ∈
        BinaryLevel.fixedSubspace data BinaryLevel.finiteCongruence :=
    realOrbit_fixed data vector.val fixed _
  let lift := localStageFamily data BinaryLevel.finiteCongruence (orbitFamily data vector.val) center
    series R expansion (radius / 2) (radius / 2) halfPositive halfBound fixedFamily
  have liftContinuous : Continuous lift :=
    localStageFamily_continuous data BinaryLevel.finiteCongruence (orbitFamily data vector.val) center
      series R expansion (radius / 2) (radius / 2) halfPositive halfBound fixedFamily
  refine ⟨radius / 2, halfPositive, ?_⟩
  intro γ φ a b hab hγ hφ hbound
  let γ' : ℝ → BinaryMatrix := fun t => γ (projIcc a b hab t)
  let φ' : ℝ → ℂ := fun t => φ (projIcc a b hab t)
  have hγ' : Continuous γ' := hγ.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc a b hab t).property)
  have hφ' : Continuous φ' := hφ.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc a b hab t).property)
  let off : ℝ → ParameterBall (radius / 2) := fun t =>
    ⟨planeBlock (γ' t - M₀) 0, (nnnorm_planeBlock_le _).trans (hbound _ (projIcc a b hab t).property)⟩
  have hoff : Continuous off :=
    ((planeBlockCLM.continuous.comp (hγ'.sub continuous_const))).subtype_mk _
  have hvalue (t : ℝ) : orbitFamily data vector.val (center + (off t).val) = realOrbit data vector.val (γ' t) := by
    unfold orbitFamily
    congr 1
    change topLeft (planeBlock M₀ 0 + planeBlock (γ' t - M₀) 0) = γ' t
    rw [topLeft_add, topLeft_planeBlock, topLeft_planeBlock, add_sub_cancel]
  have hlift (t : ℝ) : stageHilbertMap data BinaryLevel.finiteCongruence (radius / 2) halfPositive
      (lift (off t)) = realOrbit data vector.val (γ' t) := hvalue t
  let stageFamily : ℝ → analyticStage data BinaryLevel.finiteCongruence (radius / 2) halfPositive :=
    fun t => φ' t • lift (off t)
  have hstage : Continuous stageFamily := hφ'.smul (liftContinuous.comp hoff)
  have hint : IntervalIntegrable stageFamily volume a b := hstage.intervalIntegrable a b
  let element := ∫ t in a..b, stageFamily t
  let realization : analyticStage data BinaryLevel.finiteCongruence (radius / 2) halfPositive →L[ℂ]
      lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
    ⟨AnalyticRealization.stageRealization data BinaryLevel.finiteCongruence
      BinaryLevel.finiteCongruence_isOpen BinaryLevel.finiteCongruence_isCompact (radius / 2) halfPositive,
      stages (radius / 2) halfPositive⟩
  have eqOnγ : EqOn γ' γ (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    simp [γ', projIcc_of_mem hab ht]
  have eqOnφ : EqOn φ' φ (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    simp [φ', projIcc_of_mem hab ht]
  refine ⟨(stageSmoothMap data BinaryLevel.finiteCongruence BinaryLevel.finiteCongruence_isOpen
    BinaryLevel.finiteCongruence_isCompact (radius / 2) halfPositive element).val, ?_, ?_⟩
  · change stageHilbertMap data BinaryLevel.finiteCongruence (radius / 2) halfPositive element = _
    have hcomm : ∫ x in a..b, stageHilbertMap data BinaryLevel.finiteCongruence (radius / 2)
          halfPositive (stageFamily x) =
        stageHilbertMap data BinaryLevel.finiteCongruence (radius / 2) halfPositive
          (∫ x in a..b, stageFamily x) :=
      (stageHilbertMap data BinaryLevel.finiteCongruence (radius / 2) halfPositive).intervalIntegral_comp_comm hint
    rw [← hcomm]
    apply intervalIntegral.integral_congr
    intro t ht
    change stageHilbertMap data BinaryLevel.finiteCongruence (radius / 2) halfPositive
      (φ' t • lift (off t)) = _
    rw [map_smul, hlift, eqOnγ ht, eqOnφ ht]
  · intro h
    change realization element h = _
    have hcomm : ∫ x in a..b, realization (stageFamily x) =
        realization (∫ x in a..b, stageFamily x) := realization.intervalIntegral_comp_comm hint
    rw [← hcomm]
    have key := (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ h).intervalIntegral_comp_comm
      (f := fun x => realization (stageFamily x)) (μ := volume) (a := a) (b := b)
      ((realization.continuous.comp hstage).intervalIntegrable a b)
    change (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ h)
      (∫ x in a..b, realization (stageFamily x)) = _
    rw [← key]
    apply intervalIntegral.integral_congr
    intro t ht
    change (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ h) (realization (φ' t • lift (off t))) = _
    rw [map_smul, map_smul, smul_eq_mul]
    change φ' t * (realization (lift (off t))) h = _
    change φ' t * AnalyticRealization.stageRealization data BinaryLevel.finiteCongruence
      BinaryLevel.finiteCongruence_isOpen BinaryLevel.finiteCongruence_isCompact (radius / 2) halfPositive
        (lift (off t)) h = _
    rw [AnalyticRealization.stageRealization_apply]
    have hsmooth : (stageSmoothMap data BinaryLevel.finiteCongruence BinaryLevel.finiteCongruence_isOpen
        BinaryLevel.finiteCongruence_isCompact (radius / 2) halfPositive (lift (off t))).val =
        ⟨data.π (atInfinity (invertibleMatrix (γ' t))) vector.val,
          data.smooth_stable _ _ vector.property⟩ := by
      apply Subtype.ext
      change stageHilbertMap data BinaryLevel.finiteCongruence (radius / 2) halfPositive (lift (off t)) = _
      rw [hlift]
      rfl
    rw [hsmooth, data.equivariant, eqOnγ ht, eqOnφ ht]

/-- The commutation property on one interval. -/
def CommutesOn (data : CuspidalRepresentation) (vector : data.smooth) (γ : ℝ → BinaryMatrix)
    (φ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∃ w : data.smooth, w.val = (∫ t in a..b, φ t • realOrbit data vector.val (γ t)) ∧
    ∀ h, data.realize w h =
      ∫ t in a..b, φ t * data.realize vector (h * atInfinity (invertibleMatrix (γ t)))

theorem CommutesOn.trans {data : CuspidalRepresentation} {vector : data.smooth} {γ : ℝ → BinaryMatrix}
    {φ : ℝ → ℂ} {a b c : ℝ} (hγ : Continuous γ) (hφ : Continuous φ)
    (hdet : ∀ t, (γ t).det ≠ 0)
    (first : CommutesOn data vector γ φ a b) (second : CommutesOn data vector γ φ b c) :
    CommutesOn data vector γ φ a c := by
  obtain ⟨w₁, hw₁, hr₁⟩ := first
  obtain ⟨w₂, hw₂, hr₂⟩ := second
  have hH : Continuous (fun t => φ t • realOrbit data vector.val (γ t)) := by
    refine hφ.smul ?_
    have hcont : ContinuousOn (realOrbit data vector.val) SobolevSeminorms.binaryDomain :=
      (SobolevSeminorms.smooth_orbit_contDiffOn data vector).continuousOn
    have composite := hcont.comp_continuous hγ hdet
    exact composite
  have hS (h : BinaryAdelicGL) : Continuous (fun t =>
      φ t * data.realize vector (h * atInfinity (invertibleMatrix (γ t)))) := by
    refine hφ.mul ?_
    have hsmooth := data.scalarSmooth vector h
    have hcont : ContinuousOn (fun A : Fin 1 → BinaryMatrix =>
        data.realize vector (h * atInfinity (invertibleMatrix (A 0))))
        {A | ∀ i, (A i).det ≠ 0} := hsmooth.continuousOn
    have composite := hcont.comp_continuous (f := fun t : ℝ => fun _ : Fin 1 => γ t)
      (continuous_pi fun _ => hγ) (fun t i => hdet t)
    exact composite
  refine ⟨w₁ + w₂, ?_, ?_⟩
  · rw [Submodule.coe_add, hw₁, hw₂, intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable a b) (hH.intervalIntegrable b c)]
  · intro h
    rw [map_add, Pi.add_apply, hr₁, hr₂, intervalIntegral.integral_add_adjacent_intervals
      ((hS h).intervalIntegrable a b) ((hS h).intervalIntegrable b c)]

/-- **Global commutation.** Along a continuous path of invertible real matrices, the realization
of the Hilbert-space interval integral of `φ(t) π(γ(t)) v` is the scalar interval integral. -/
theorem commutesOn_of_continuous (data : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages data) (vector : data.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace data BinaryLevel.finiteCongruence)
    (γ : ℝ → BinaryMatrix) (φ : ℝ → ℂ) (hγ : Continuous γ) (hφ : Continuous φ)
    (hdet : ∀ t, (γ t).det ≠ 0) (a b : ℝ) (hab : a ≤ b) :
    CommutesOn data vector γ φ a b := by
  have local_radius (M : BinaryMatrix) (hM : M.det ≠ 0) :=
    realize_intervalIntegral_local data stages vector fixed M hM
  choose r hr hcomm using local_radius
  let cover : ℝ → Set ℝ := fun t => γ ⁻¹' Metric.ball (γ t) (r (γ t) (hdet t))
  have hopen (t : ℝ) : IsOpen (cover t) := Metric.isOpen_ball.preimage hγ
  have hcover : Icc a b ⊆ ⋃ t, cover t := by
    intro s _
    exact Set.mem_iUnion.mpr ⟨s, Metric.mem_ball_self (by exact_mod_cast hr _ _)⟩
  obtain ⟨δ, δpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hopen hcover
  -- every short interval inside `[a, b]` satisfies the property
  have piece (x y : ℝ) (hxy : x ≤ y) (hx : x ∈ Icc a b) (hshort : y - x < δ) :
      CommutesOn data vector γ φ x y := by
    obtain ⟨i, hi⟩ := hδ x hx
    obtain ⟨w, hw, hrw⟩ := hcomm (γ i) (hdet i) γ φ x y hxy hγ.continuousOn hφ.continuousOn (by
      intro t ht
      have hmem : t ∈ Metric.ball x δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      have hball := hi hmem
      change γ t ∈ Metric.ball (γ i) (r (γ i) (hdet i)) at hball
      rw [Metric.mem_ball, dist_eq_norm] at hball
      exact (NNReal.coe_le_coe.mp (le_of_lt (by simpa using hball))))
    exact ⟨w, hw, hrw⟩
  -- subdivide
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  let step : ℝ := (b - a) / (N + 1)
  have hstep0 : 0 ≤ step := div_nonneg (by linarith) hNpos.le
  have hstepδ : step < δ := by
    have : (b - a) / δ < N + 1 := by linarith
    rw [div_lt_iff₀ δpos] at this
    rw [div_lt_iff₀ hNpos]
    linarith
  have induction (k : ℕ) (hk : k ≤ N + 1) : CommutesOn data vector γ φ a (a + k * step) := by
    induction k with
    | zero =>
      refine ⟨0, ?_, ?_⟩
      · simp
      · intro h; simp
    | succ k ih =>
      have hk' : k ≤ N + 1 := by omega
      have hlow : a + k * step ∈ Icc a b := by
        constructor
        · nlinarith
        · have hkle : (k : ℝ) ≤ N + 1 := by exact_mod_cast hk'
          have : (k : ℝ) * step ≤ (N + 1) * step := mul_le_mul_of_nonneg_right hkle hstep0
          have hfull : ((N : ℝ) + 1) * step = b - a := by
            simp only [step]; field_simp
          linarith
      have hnext := piece (a + k * step) (a + (k + 1 : ℕ) * step) (by push_cast; nlinarith) hlow
        (by push_cast; linarith)
      exact (ih hk').trans hγ hφ hdet hnext
  have hfinal := induction (N + 1) le_rfl
  have hend : a + ((N + 1 : ℕ) : ℝ) * step = b := by
    simp only [step]; push_cast; field_simp; ring
  rwa [hend] at hfinal

end TernaryPeriodPolynomials.AnalyticClasses
