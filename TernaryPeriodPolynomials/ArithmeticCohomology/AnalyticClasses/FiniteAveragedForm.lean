module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeInterface
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FinAvgLeviInvariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CanonicalTransferGlueAverage
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.AnalyticParameterIntegral

@[expose] public section


/-!
# The finite good-line average of a scalar form

For a function `X` on `GL₂(𝔸)` the finite good-line average at the cohomological point is
`⟨X⟩(h) = ∫ w(f) X(b(f) h) df`, where `b(f)` is the block of the standard finite plane
coordinates of the finite radical pair `f` away from `3` and `w(f)` the finite cusp weight. It
commutes with right translations. If `X` is left invariant under `GL₂(ℚ)` and right invariant
under `GL₂(Ẑ)`, then `⟨X⟩` is invariant under left translation by real integral matrices at
real points: the real matrix `γ` is the rational one times the finite one `γ_f⁻¹`, and the left
finite translate by `γ_f⁻¹` is absorbed by the measure preserving change of variables `f ↦ f γ⁻¹`
of the finite radical coordinates.

For a scalar form `F h z` with the Eichler data, the average `⟨F(·, z)⟩` taken at the real
component of the adelic point inherits the Eichler data, provided the averaged integrands are
measurable at real points.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### The average -/

/-- The finite good-line average of a function on `GL₂(𝔸)` at the cohomological point, translating
its argument on the left by the block of the standard finite plane coordinates. -/
def finiteAverageLeft (n : ℕ) (X : BinaryAdelicGL → ℂ) (h : BinaryAdelicGL) : ℂ :=
  ∫ finite, standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
      X (atFinite (standardGoodLineFiniteCoordinates finite).block * h)
    ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)

/-- **The finite good-line average of a scalar form** `F h z`, in the adelic variable `h`. -/
def averagedForm (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (z : ℂ) : ℂ :=
  finiteAverageLeft n (fun point => F point z) h

theorem averagedForm_def (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (z : ℂ) :
    averagedForm n F h z = ∫ finite, standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
      F (atFinite (standardGoodLineFiniteCoordinates finite).block * h) z
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := rfl

/-- Right translations commute with the finite average. -/
theorem averagedForm_mul (F : BinaryAdelicGL → ℂ → ℂ) (h k : BinaryAdelicGL) (z : ℂ) :
    averagedForm n F (h * k) z = averagedForm n (fun point => F (point * k)) h z := by
  simp only [averagedForm_def, mul_assoc]

/-- The real component of an adelic point. -/
def binaryRealPart : BinaryAdelicGL →* BinaryRealGL :=
  GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles)

theorem binaryRealPart_atInfinity (g : BinaryRealGL) : binaryRealPart (atInfinity g) = g := by
  apply Units.ext
  rfl

theorem binaryRealPart_mul_atInfinity (h : BinaryAdelicGL) (g : BinaryRealGL) :
    binaryRealPart (h * atInfinity g) = binaryRealPart h * g := by
  rw [map_mul, binaryRealPart_atInfinity]

/-- **The averaged scalar form at the real component** of the adelic point. On real points it is
the finite average `averagedForm`. -/
def averagedRealForm (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (z : ℂ) : ℂ :=
  averagedForm n F (atInfinity (binaryRealPart h)) z

theorem averagedRealForm_atInfinity (F : BinaryAdelicGL → ℂ → ℂ) (g : BinaryRealGL) (z : ℂ) :
    averagedRealForm n F (atInfinity g) z = averagedForm n F (atInfinity g) z := by
  rw [averagedRealForm, binaryRealPart_atInfinity]

theorem averagedRealForm_mul_atInfinity (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL)
    (g : BinaryRealGL) (z : ℂ) :
    averagedRealForm n F (h * atInfinity g) z =
      averagedForm n F (atInfinity (binaryRealPart h) * atInfinity g) z := by
  rw [averagedRealForm, binaryRealPart_mul_atInfinity, atInfinity_mul]

/-! ### The weight -/

/-- The finite cusp weight is the determinant weight of the `p`-adic plane coordinates. -/
theorem standardGoodLineFiniteCuspWeight_eq_padic (finite : FiniteAwayThree × FiniteAwayThree) :
    standardGoodLineFiniteCuspWeight n cohomologicalPoint finite =
      normPower (GeneralLinearGroup.det
        (atFinite (standardGoodLineFinitePadicCoordinates finite).block))
        ((n : ℂ) / 2 + 3 + cohomologicalPoint) := by
  rw [standardGoodLineFiniteCuspWeight_det, binary_det_atFinite]
  exact finitePlaneInductionBlocks_normPower _
    (finitePlaneLevelInductionCoordinates _ (standardGoodLineFiniteCoordinates finite))
    (standardGoodLineFinitePadicCoordinates finite) _

theorem norm_standardGoodLineFiniteCuspWeight (finite : FiniteAwayThree × FiniteAwayThree) :
    ‖standardGoodLineFiniteCuspWeight n cohomologicalPoint finite‖ =
      goodLinePositiveWeight ((n : ℂ) / 2 + 3 + cohomologicalPoint) finite := by
  rw [standardGoodLineFiniteCuspWeight_eq_padic]
  rfl

theorem norm_standardGoodLineFiniteCuspWeight_integrable (large : 3 < n) :
    Integrable (fun finite => ‖standardGoodLineFiniteCuspWeight n cohomologicalPoint finite‖)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  simp only [norm_standardGoodLineFiniteCuspWeight]
  exact goodLinePositiveWeight_integrable _ (cohomologicalExponent_re large)

/-- **A uniform bound for the finite average.** -/
theorem norm_finiteAverageLeft_le (large : 3 < n) (X : BinaryAdelicGL → ℂ) (h : BinaryAdelicGL)
    {C : ℝ} (bound : ∀ finite : FiniteAwayThree × FiniteAwayThree,
      ‖X (atFinite (standardGoodLineFiniteCoordinates finite).block * h)‖ ≤ C) :
    ‖finiteAverageLeft n X h‖ ≤
      (∫ finite, ‖standardGoodLineFiniteCuspWeight n cohomologicalPoint finite‖
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) * C := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le
    ((norm_standardGoodLineFiniteCuspWeight_integrable large).mul_const C)
    (Filter.Eventually.of_forall fun finite => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (bound finite) (norm_nonneg _)

/-! ### Invariance under real integral Levi translations -/

section Levi

variable (X : BinaryAdelicGL → ℂ)
  (left : ∀ (γ : BinaryRationalGL) (h : BinaryAdelicGL),
    X (GeneralLinearGroup.map rationalAdele γ * h) = X h)
  (right : ∀ (h : BinaryAdelicGL) (compact : GeneralLinearGroup (Fin 2) IntegralAdeles),
    X (h * atFinite (GeneralLinearGroup.map integralEmbedding compact)) = X h)

/-- The weighted value of `X` at a finite plane coordinate system, translated by a real point. -/
def finitePlaneValue (g : BinaryRealGL) {finite : FiniteGL}
    (coords : FinitePlaneInductionCoordinates finite) : ℂ :=
  normPower (finiteAdeleUnit (GeneralLinearGroup.det coords.block))
      ((n : ℂ) / 2 + 3 + cohomologicalPoint) *
    X (atFinite coords.block * atInfinity g)

include right in
/-- The weighted value does not depend on the finite plane coordinate system. -/
theorem finitePlaneValue_independent (g : BinaryRealGL) {finite : FiniteGL}
    (first second : FinitePlaneInductionCoordinates finite) :
    finitePlaneValue (n := n) X g first = finitePlaneValue (n := n) X g second := by
  obtain ⟨integral, equality⟩ := finitePlaneInductionBlocks_exists_integral finite first second
  unfold finitePlaneValue
  rw [finitePlaneInductionBlocks_normPower finite first second, equality, atFinite_mul,
    mul_assoc (atFinite first.block),
    ← (atInfinity_commute_atFinite g (GeneralLinearGroup.map integralEmbedding integral)).eq,
    ← mul_assoc, right]

include left in
/-- The real integral matrix `γ` is absorbed as the finite translate `γ_f⁻¹` on the left. -/
theorem apply_atFinite_mul_realLevi (γ : GeneralLinearGroup (Fin 2) ℤ) (block : BinaryFiniteGL)
    (point : BinaryAdelicGL) :
    X (atFinite block * (atInfinity (realLeviMatrix γ) * point)) =
      X (atFinite (finiteLeviMatrix γ⁻¹ * block) * point) := by
  have product : atFinite block * (atInfinity (realLeviMatrix γ) * point) =
      GeneralLinearGroup.map rationalAdele (GeneralLinearGroup.map (Int.castRingHom ℚ) γ) *
        (atFinite (finiteLeviMatrix γ⁻¹ * block) * point) := by
    have inverse : finiteLeviMatrix γ⁻¹ = (finiteLeviMatrix γ)⁻¹ := map_inv _ _
    calc atFinite block * (atInfinity (realLeviMatrix γ) * point) =
        atInfinity (realLeviMatrix γ) * atFinite block * point := by
          rw [← mul_assoc, (atInfinity_commute_atFinite (realLeviMatrix γ) block).eq]
      _ = (atInfinity (realLeviMatrix γ) * atFinite (finiteLeviMatrix γ)) *
          ((atFinite (finiteLeviMatrix γ))⁻¹ * atFinite block * point) := by
          simp only [mul_assoc, mul_inv_cancel_left]
      _ = _ := by rw [← rationalAdele_intMatrix, inverse, atFinite_mul, atFinite_inv]
  rw [product, left]

include left right in
/-- **Invariance of the finite average under real integral Levi translations** at real points,
for a function that is left `GL₂(ℚ)`-invariant and right `GL₂(Ẑ)`-invariant. -/
theorem finiteAverageLeft_realLevi (γ : GeneralLinearGroup (Fin 2) ℤ) (g : BinaryRealGL) :
    finiteAverageLeft n X (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) *
        atInfinity g) = finiteAverageLeft n X (atInfinity g) := by
  set φ : FiniteAwayThree × FiniteAwayThree → ℂ := fun finite =>
    standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
      X (atFinite (finiteLeviMatrix γ⁻¹ * (standardGoodLineFiniteCoordinates finite).block) *
        atInfinity g)
  have pointwise (finite : FiniteAwayThree × FiniteAwayThree) :
      φ (leviRowAction γ⁻¹ finite) = standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        X (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g) := by
    have transported := finitePlaneValue_independent (n := n) X right g
      (transportCoordinates γ⁻¹ finite (finitePlaneLevelInductionCoordinates _
        (standardGoodLineFiniteCoordinates (leviRowAction γ⁻¹ finite))))
      (finitePlaneLevelInductionCoordinates _ (standardGoodLineFiniteCoordinates finite))
    unfold finitePlaneValue at transported
    change normPower (finiteAdeleUnit (GeneralLinearGroup.det (finiteLeviMatrix γ⁻¹ *
        (standardGoodLineFiniteCoordinates (leviRowAction γ⁻¹ finite)).block))) _ *
      X (atFinite (finiteLeviMatrix γ⁻¹ *
        (standardGoodLineFiniteCoordinates (leviRowAction γ⁻¹ finite)).block) * atInfinity g) =
      normPower (finiteAdeleUnit (GeneralLinearGroup.det
        (standardGoodLineFiniteCoordinates finite).block)) _ *
      X (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g) at transported
    rw [map_mul, finiteAdeleUnit_mul, normPower_mul, normPower_finiteLeviMatrix_det, one_mul,
      ← standardGoodLineFiniteCuspWeight_det, ← standardGoodLineFiniteCuspWeight_det] at transported
    exact transported
  have change_variables := (leviRowAction_measurePreserving γ⁻¹).integral_comp
    (leviRowEquiv γ⁻¹).toHomeomorph.measurableEmbedding φ
  simp only [pointwise] at change_variables
  unfold finiteAverageLeft
  rw [change_variables]
  apply integral_congr_ae
  filter_upwards [] with finite
  exact congrArg _ (apply_atFinite_mul_realLevi X left γ _ _)

end Levi

/-! ### The Eichler data of the averaged form -/

/-- A closed ball around a point of the upper half plane inside the upper half plane. -/
theorem closedBall_subset_upper {z : ℂ} (positive : 0 < z.im) :
    Metric.closedBall z (z.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
  intro w member
  have distance : ‖w - z‖ ≤ z.im / 2 := by rwa [Metric.mem_closedBall, dist_eq_norm] at member
  have imaginary : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at imaginary
  change 0 < w.im
  linarith [neg_abs_le (w.im - z.im)]

/-- Holomorphy of a finite average of holomorphic functions with integrable bounds on compacts. -/
theorem differentiableOn_finiteAverage (large : 3 < n)
    (G : ℂ → FiniteAwayThree × FiniteAwayThree → ℂ)
    (measurable : ∀ z : ℂ, 0 < z.im →
      AEStronglyMeasurable (G z) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))
    (holomorphic : ∀ finite, DifferentiableOn ℂ (fun z => G z finite) {z : ℂ | 0 < z.im})
    (bounded : ∀ K ⊆ {z : ℂ | 0 < z.im}, IsCompact K → ∃ C : ℝ, ∀ finite, ∀ z ∈ K,
      ‖G z finite‖ ≤ ‖standardGoodLineFiniteCuspWeight n cohomologicalPoint finite‖ * C) :
    DifferentiableOn ℂ (fun z => ∫ finite, G z finite
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) {z : ℂ | 0 < z.im} := by
  classical
  intro center positive
  have radius : 0 < center.im / 2 := half_pos positive
  have ball_upper : Metric.ball center (center.im / 2) ⊆ {z : ℂ | 0 < z.im} :=
    Metric.ball_subset_closedBall.trans (closedBall_subset_upper positive)
  obtain ⟨C, hC⟩ := bounded _ (closedBall_subset_upper positive) (isCompact_closedBall _ _)
  set H : ℂ → FiniteAwayThree × FiniteAwayThree → ℂ := fun z finite =>
    if 0 < z.im then G z finite else 0
  have local_eq : ∀ z ∈ Metric.ball center (center.im / 2),
      (fun z => ∫ finite, H z finite ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) z =
        ∫ finite, G z finite ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
    intro z member
    have upper : 0 < z.im := ball_upper member
    simp only [H, ite_eq_left upper]
  have averaged :=
    EisensteinGraph.StandardConstruction.AnalyticParameterIntegral.integral_differentiableOn
    (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) H
    (fun z => by
      by_cases upper : 0 < z.im
      · simp only [H, ite_eq_left upper]
        exact measurable z upper
      · simp only [H, ite_eq_right upper]
        exact aestronglyMeasurable_const)
    (Metric.ball center (center.im / 2)) Metric.isOpen_ball
    (fun finite => ((holomorphic finite).mono ball_upper).congr fun z member => by
      simp only [H, ite_eq_left (show 0 < z.im from ball_upper member)])
    (fun finite => ‖standardGoodLineFiniteCuspWeight n cohomologicalPoint finite‖ * C)
    ((norm_standardGoodLineFiniteCuspWeight_integrable large).mul_const C)
    (fun finite z member => by
      simp only [H, ite_eq_left (show 0 < z.im from ball_upper member)]
      exact hC finite z (Metric.ball_subset_closedBall member))
  have congruent := averaged.congr (fun z member => (local_eq z member).symm)
  exact (congruent.differentiableAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self radius))).differentiableWithinAt

/-- **The averaged form at the real component inherits the Eichler data**, provided the averaged
integrands are measurable at real points of the upper half plane. -/
theorem EichlerData.averagedReal (large : 3 < n) {F : BinaryAdelicGL → ℂ → ℂ}
    (hF : EichlerData n F)
    (measurable : ∀ (g : BinaryRealGL) (z : ℂ), 0 < z.im → AEStronglyMeasurable (fun finite =>
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        F (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g) z)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    EichlerData n (averagedRealForm n F) where
  holomorphic h := by
    refine differentiableOn_finiteAverage large (fun z finite =>
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        F (atFinite (standardGoodLineFiniteCoordinates finite).block *
          atInfinity (binaryRealPart h)) z)
      (fun z positive => measurable _ z positive)
      (fun finite => (hF.holomorphic _).const_mul _) (fun K subset compact => ?_)
    obtain ⟨C, hC⟩ := hF.bounded K subset compact
    exact ⟨C, fun finite z member => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _ z member) (norm_nonneg _)⟩
  modular A hA h z := by
    rw [averagedRealForm_mul_atInfinity, averagedRealForm, averagedForm_def, averagedForm_def,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with finite
    rw [← mul_assoc, hF.modular A hA, mul_left_comm]
  central c positive h z := by
    rw [averagedRealForm_mul_atInfinity, averagedRealForm, averagedForm_def, averagedForm_def]
    apply integral_congr_ae
    filter_upwards [] with finite
    rw [← mul_assoc, hF.central c positive]
  bounded K subset compact := by
    obtain ⟨C, hC⟩ := hF.bounded K subset compact
    exact ⟨(∫ finite, ‖standardGoodLineFiniteCuspWeight n cohomologicalPoint finite‖
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) * C, fun h w member =>
      norm_finiteAverageLeft_le large (fun point => F point w)
        (atInfinity (binaryRealPart h)) fun finite => hC _ w member⟩

end TernaryPeriodPolynomials.AnalyticClasses
