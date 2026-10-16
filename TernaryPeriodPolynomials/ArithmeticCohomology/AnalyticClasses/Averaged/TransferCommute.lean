module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.TransferPeriod
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.TransferLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeAnalyticBounds

@[expose] public section


/-!
# The finite average commutes with the real good-line transfer

A scalar test of the transferred integrand of a binary family `N` at `(1, a, c)` is a linear
functional, depending only on the good-line coordinate `u`, of `N(A_u)(h B_u)`. Let `F = F_v` be
the scalar weighted realization of a spherical smooth vector with the Eichler data and `F_avg` its
finite average at the real component. Then at a real point `g` the finite average of the
inhomogeneous real transfer of the pointwise Eichler normal form of `F` is the real transfer of the
pointwise Eichler normal form of `F_avg` (Fubini over the good-line coordinate and the finite
pair: the integrand is continuous in `u`, continuous in the finite pair, and dominated by the
transfer bound in `u` times the integrable finite weight). In particular the finite average of
scalar tests of the transfer is the transfer of `F_avg` at the identity.

Since `F_avg` is invariant under left translation by real integral matrices, so is the real
transfer of its pointwise Eichler normal form, and hence so is the finite average of the real
transfer of `F` at real points.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### Scalar tests of the transferred integrand -/

/-- The linear functional of the binary values computing a scalar test of the transferred
integrand at `(1, a, c)` and the good-line coordinate `u`. -/
def relativeTest (u : ℝ × ℝ) (a c : LineGroup) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ :=
  transferScale n u • (functional ∘ₗ realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹ ∘ₗ
    (realUpperRadicalRep n).ρ (relativeVertex u a).left ∘ₗ realUpperBinaryValue n
      (realPlaneRadicalAction (relativeVertex u a).right
        ((relativeVertex u a)⁻¹ * relativeVertex u c).left))

/-- **A scalar test of the transferred integrand is a linear functional of the binary values.** -/
theorem functional_relativeIntegrand_eq_relativeTest
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (u : ℝ × ℝ)
    (a c : LineGroup) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    functional (relativeIntegrand N u a c h) =
      relativeTest u a c functional (N (relativeVertex u a).right (movedAdelic h u)) := by
  unfold relativeIntegrand pointCanonical relativeTest movedAdelic
  rw [map_smul, smul_eq_mul, LinearMap.smul_apply, smul_eq_mul]
  rfl

/-! ### The average of the transfer -/

section Spherical

variable (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
  (spherical : vector.val ∈ cuspSphericalValues cusp)

include spherical in
/-- **The finite average commutes with the real transfer of the pointwise Eichler normal form**
at real points (`n ≥ 5`). -/
theorem averagedLine_lineTransferCochain_eichlerNormal (large : 5 ≤ n)
    (hF : EichlerData n (cuspScalarWeightedRealization cusp halfWeight vector)) (x y : LineGroup)
    (g : BinaryRealGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    averagedLine (lineTransferCochain
        (eichlerNormal n (cuspScalarWeightedRealization cusp halfWeight vector)) x y)
        (atInfinity g, functional) =
      lineTransferCochain (eichlerNormal n
        (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector))) x y
        (atInfinity g, functional) := by
  set F := cuspScalarWeightedRealization cusp halfWeight vector
  set B : ℝ × ℝ → BinaryRealGL := fun u => (gsPlaneVertex (standardGoodLineRealArgument u)).right
  set H : ℝ × ℝ → FiniteAwayThree × FiniteAwayThree → ℂ := fun u finite =>
    standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
      functional (relativeIntegrand (eichlerNormal n F) u x (x * y)
        (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g))
  have rewritten (u : ℝ × ℝ) : H u = fun finite =>
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        relativeTest u x (x * y) functional (eichlerNormal n F (relativeVertex u x).right
          (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity (g * B u))) := by
    funext finite
    simp only [H, functional_relativeIntegrand_eq_relativeTest, movedAdelic,
      atFinite_mul_atInfinity_mul, B]
  have key (u : ℝ × ℝ) := weighted_functional_eichlerNormal cusp halfWeight vector spherical
    (by omega) (relativeVertex u x).right (g * B u) (relativeTest u x (x * y) functional)
  have inner (u : ℝ × ℝ) : ∫ finite, H u finite
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      functional (relativeIntegrand (eichlerNormal n (averagedRealForm n F)) u x (x * y)
        (atInfinity g)) := by
    rw [rewritten, (key u).2.2, functional_relativeIntegrand_eq_relativeTest, movedAdelic,
      atInfinity_mul]
  have measurable : StronglyMeasurable (Function.uncurry H) := by
    refine stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun finite => continuous_const.mul
        (continuous_functional_relativeIntegrand hF x (x * y) _ functional)) (fun u => ?_)
    rw [rewritten]
    exact (key u).1.stronglyMeasurable
  obtain ⟨bound, bound_integrable, bounded⟩ :=
    lineTransferIntegrand_dominated large hF.pointCocycle ![1, x, x * y] functional
  have dominating : Integrable (fun point : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      bound point.1 * ‖standardGoodLineFiniteCuspWeight n cohomologicalPoint point.2‖)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :=
    bound_integrable.mul_prod (norm_standardGoodLineFiniteCuspWeight_integrable (by omega))
  have joint : Integrable (Function.uncurry H)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) := by
    refine dominating.mono' measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun point => ?_)
    change ‖H point.1 point.2‖ ≤ _
    have pointBound := bounded point.1
      (atFinite (standardGoodLineFiniteCoordinates point.2).block * atInfinity g)
    rw [lineTransferIntegrand_eq_relative] at pointBound
    simp only [H, norm_mul, mul_comm (bound point.1)]
    exact mul_le_mul_of_nonneg_left pointBound (norm_nonneg _)
  rw [averagedLine_apply, lineTransferCochain_apply]
  simp only [lineTransferCochain_apply, ← integral_const_mul]
  rw [← integral_integral_swap joint]
  exact integral_congr_ae (Filter.Eventually.of_forall inner)

include spherical in
/-- **The finite average of scalar tests of the real transfer of `F_v` is the real transfer of
`F_avg` at the identity** (`n ≥ 5`). -/
theorem finiteAverageLine_lineTransferCochain_eichlerNormal (large : 5 ≤ n)
    (hF : EichlerData n (cuspScalarWeightedRealization cusp halfWeight vector)) (x y : LineGroup)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    finiteAverageLine (lineTransferCochain
        (eichlerNormal n (cuspScalarWeightedRealization cusp halfWeight vector)) x y) functional =
      lineTransferCochain (eichlerNormal n
        (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector))) x y
        (1, functional) := by
  rw [finiteAverageLine_eq_averagedLine, ← atInfinity_one,
    averagedLine_lineTransferCochain_eichlerNormal cusp halfWeight vector spherical large hF]

/-! ### Levi invariance -/

include spherical in
/-- **The averaged form at the real component is invariant under left translation by real
integral matrices.** -/
theorem averagedRealForm_cuspScalar_left_realLevi (γ : GeneralLinearGroup (Fin 2) ℤ)
    (h : BinaryAdelicGL) (z : ℂ) :
    averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector)
        (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * h) z =
      averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector) h z := by
  rw [averagedRealForm, averagedRealForm, map_mul, binaryRealPart_atInfinity, atInfinity_mul,
    averagedForm_cuspScalar_realLevi cusp halfWeight vector spherical]

theorem binaryAmbientRepresentation_eq_smul (A : BinaryRealGL)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (h : BinaryAdelicGL) :
    binaryAmbientRepresentation n A values h =
      normPower (GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) •
        binaryCoefficient n A (values (h * atInfinity A)) := rfl

/-- The pointwise Eichler normal form inherits left invariance from the scalar form. -/
theorem eichlerNormal_left_invariant {F : BinaryAdelicGL → ℂ → ℂ} {s : BinaryAdelicGL}
    (invariant : ∀ h z, F (s * h) z = F h z) (A : BinaryRealGL) (h : BinaryAdelicGL) :
    eichlerNormal n F A (s * h) = eichlerNormal n F A h := by
  have period (z : ℂ) (h : BinaryAdelicGL) : eichlerPeriod n F z (s * h) = eichlerPeriod n F z h :=
    by simp only [eichlerPeriod, eichlerIntegrand, invariant]
  rw [eichlerNormal_def, eichlerNormal_def, period, binaryAmbientRepresentation_eq_smul,
    binaryAmbientRepresentation_eq_smul, mul_assoc, period]

include spherical in
/-- **The real transfer of the pointwise Eichler normal form of `F_avg` is invariant under left
translation by real integral matrices.** -/
theorem lineTransferCochain_averaged_realLevi (γ : GeneralLinearGroup (Fin 2) ℤ)
    (a b : LineGroup) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    lineTransferCochain (eichlerNormal n
        (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector))) a b
        (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * h, functional) =
      lineTransferCochain (eichlerNormal n
        (averagedRealForm n (cuspScalarWeightedRealization cusp halfWeight vector))) a b
        (h, functional) :=
  lineTransferCochain_left_invariant
    (S := {atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)})
    (fun s member A h => by
      rw [Set.mem_singleton_iff.mp member]
      exact eichlerNormal_left_invariant
        (averagedRealForm_cuspScalar_left_realLevi cusp halfWeight vector spherical γ) A h)
    a b rfl h functional

include spherical in
/-- **The finite average of the real transfer of `F_v` is invariant under left translation by
real integral matrices** at real points (`n ≥ 5`). -/
theorem averagedLine_lineTransferCochain_eichlerNormal_realLevi (large : 5 ≤ n)
    (hF : EichlerData n (cuspScalarWeightedRealization cusp halfWeight vector)) (x y : LineGroup)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (g : BinaryRealGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    averagedLine (lineTransferCochain
        (eichlerNormal n (cuspScalarWeightedRealization cusp halfWeight vector)) x y)
        (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * atInfinity g, functional) =
      averagedLine (lineTransferCochain
        (eichlerNormal n (cuspScalarWeightedRealization cusp halfWeight vector)) x y)
        (atInfinity g, functional) := by
  rw [← atInfinity_mul,
    averagedLine_lineTransferCochain_eichlerNormal cusp halfWeight vector spherical large hF,
    averagedLine_lineTransferCochain_eichlerNormal cusp halfWeight vector spherical large hF,
    atInfinity_mul, lineTransferCochain_averaged_realLevi cusp halfWeight vector spherical]

end Spherical

end TernaryPeriodPolynomials.AnalyticClasses
