module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.TransferCommute
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.TransferRegular

@[expose] public section


/-!
# Integrability of the finite averages of the real transfers

The finite good-line average of a scalar test `X(h, λ) = ∫ ψ(u, h, λ) du` is absolutely
convergent at every real point `g`, provided `ψ` is continuous in `u`, its weighted values are
measurable in the finite pair, and it is dominated by an integrable function of `u` uniformly in
the adelic point (Fubini on `ℝ² × (𝔸_f^{(3)})²`). This applies to the inhomogeneous real transfer
of the pointwise Eichler normal form of the scalar weighted realization of a spherical smooth
vector, and to the real transfer of `θκ` for the lift `κ` of a smooth spherical tuple: the
weighted values of `κ` are finite sums of `p`-adic good-line integrands of spherical vectors,
which are continuous in the finite pair.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.ArchimedeanConstant
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ}

/-- **Integrability of the finite average of a `u`-integral.** -/
theorem integrable_weighted_integral (large : 3 < n)
    {ψ : ℝ × ℝ → FiniteAwayThree × FiniteAwayThree → ℂ}
    (continuous : ∀ finite, Continuous fun u => ψ u finite)
    (measurable : ∀ u, StronglyMeasurable fun finite =>
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite * ψ u finite)
    {bound : ℝ × ℝ → ℝ} (integrable : Integrable bound ((volume : Measure ℝ).prod volume))
    (bounded : ∀ u finite, ‖ψ u finite‖ ≤ bound u) :
    Integrable (fun finite => standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        ∫ u, ψ u finite ∂((volume : Measure ℝ).prod volume))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  set H : ℝ × ℝ → FiniteAwayThree × FiniteAwayThree → ℂ := fun u finite =>
    standardGoodLineFiniteCuspWeight n cohomologicalPoint finite * ψ u finite
  have joint_measurable : StronglyMeasurable (Function.uncurry H) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun finite => continuous_const.mul (continuous finite)) measurable
  have dominating : Integrable (fun point : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      bound point.1 * ‖standardGoodLineFiniteCuspWeight n cohomologicalPoint point.2‖)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :=
    integrable.mul_prod (norm_standardGoodLineFiniteCuspWeight_integrable large)
  have joint : Integrable (Function.uncurry H)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) := by
    refine dominating.mono' joint_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun point => ?_)
    change ‖H point.1 point.2‖ ≤ _
    simp only [H, norm_mul, mul_comm (bound point.1)]
    exact mul_le_mul_of_nonneg_left (bounded _ _) (norm_nonneg _)
  refine joint.integral_prod_right.congr (Filter.Eventually.of_forall fun finite => ?_)
  exact integral_const_mul (standardGoodLineFiniteCuspWeight n cohomologicalPoint finite)
    (fun u => ψ u finite)

section Spherical

variable (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
  (spherical : vector.val ∈ cuspSphericalValues cusp)

include spherical in
/-- **The finite average of the real transfer of the pointwise Eichler normal form is absolutely
convergent** at real points (`n ≥ 5`). -/
theorem lineAverage_integrable_eichlerNormal (large : 5 ≤ n)
    (hF : EichlerData n (cuspScalarWeightedRealization cusp halfWeight vector)) (x y : LineGroup)
    (g : BinaryRealGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun finite => standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        lineTransferCochain (eichlerNormal n (cuspScalarWeightedRealization cusp halfWeight vector))
          x y (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g,
            functional))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  set F := cuspScalarWeightedRealization cusp halfWeight vector
  set B : ℝ × ℝ → BinaryRealGL := fun u => (gsPlaneVertex (standardGoodLineRealArgument u)).right
  obtain ⟨bound, bound_integrable, bounded⟩ :=
    lineTransferIntegrand_dominated large hF.pointCocycle ![1, x, x * y] functional
  simp only [lineTransferCochain_apply]
  refine integrable_weighted_integral (by omega)
    (ψ := fun u finite => functional (relativeIntegrand (eichlerNormal n F) u x (x * y)
      (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)))
    (fun finite => continuous_functional_relativeIntegrand hF x (x * y) _ functional)
    (fun u => ?_) bound_integrable (fun u finite => ?_)
  · have key := weighted_functional_eichlerNormal cusp halfWeight vector spherical
      (by omega) (relativeVertex u x).right (g * B u) (relativeTest u x (x * y) functional)
    have rewritten : (fun finite => standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        functional (relativeIntegrand (eichlerNormal n F) u x (x * y)
          (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g))) =
        fun finite => standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          relativeTest u x (x * y) functional (eichlerNormal n F (relativeVertex u x).right
            (atFinite (standardGoodLineFiniteCoordinates finite).block *
              atInfinity (g * B u))) := by
      funext finite
      simp only [functional_relativeIntegrand_eq_relativeTest, movedAdelic,
        atFinite_mul_atInfinity_mul, B]
    rw [rewritten]
    exact key.1.stronglyMeasurable
  · have pointBound := bounded u
      (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)
    rwa [lineTransferIntegrand_eq_relative] at pointBound

end Spherical

/-! ### The real transfer of `θκ` -/

/-- **Weighted scalar tests of the lift of a smooth spherical tuple are continuous in the finite
pair.** -/
theorem weighted_hilbertLift_continuous (cusp : CuspidalRepresentation)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth)
    (spherical : ∀ position, vectors position ∈ cuspSphericalValues cusp) (k : BinaryRealGL)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Continuous (fun finite : FiniteAwayThree × FiniteAwayThree =>
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        functional (hilbertLift cusp n vectors
          (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity k))) := by
  have term (position : Fin (n + 2)) (finite : FiniteAwayThree × FiniteAwayThree) :
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          smoothRealize cusp (vectors position)
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity k) =
        goodLineFinitePadicIntegrand cusp
          (cuspSmoothAction cusp (atInfinity k) ⟨vectors position, smooth position⟩)
          ((n : ℂ) / 2 + 3 + cohomologicalPoint) finite := by
    rw [← goodLineFinitePadicIntegrand_eq n cusp cohomologicalPoint _
      (cuspSmoothAction_real_spherical cusp _ (spherical position) k) finite,
      cuspSmoothAction_realize, smoothRealize_of_mem cusp ⟨vectors position, smooth position⟩]
  have expansion (finite : FiniteAwayThree × FiniteAwayThree) :
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          functional (hilbertLift cusp n vectors
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity k)) =
        ∑ position, goodLineFinitePadicIntegrand cusp
          (cuspSmoothAction cusp (atInfinity k) ⟨vectors position, smooth position⟩)
          ((n : ℂ) / 2 + 3 + cohomologicalPoint) finite *
            functional (binaryWeightBasis (n + 1) position) := by
    rw [functional_eq_sum_coord functional, Finset.mul_sum]
    refine Finset.sum_congr rfl fun position _ => ?_
    rw [coord_hilbertLift, ← mul_assoc, term]
  simp only [expansion]
  exact continuous_finsetSum _ fun position _ =>
    (goodLineFinitePadicIntegrand_continuous cusp _
      (cuspSmoothAction_real_spherical cusp _ (spherical position) k) _).mul continuous_const

/-- **The finite average of the real transfer of `θκ` is absolutely convergent** at real points,
for the lift `κ` of a smooth spherical tuple (`n ≥ 5`). -/
theorem lineAverage_integrable_bridgeTransfer (large : 5 ≤ n) (cusp : CuspidalRepresentation)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth)
    (spherical : ∀ position, vectors position ∈ cuspSphericalValues cusp) (a : LineGroup)
    (g : BinaryRealGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun finite => standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        bridgeTransfer (hilbertLift cusp n vectors) a
          (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g, functional))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  set κ := hilbertLift cusp n vectors
  set B : ℝ × ℝ → BinaryRealGL := fun u => (gsPlaneVertex (standardGoodLineRealArgument u)).right
  have bounded := hilbertLift_bounded cusp vectors smooth
  have continuous := hilbertLift_ambient_continuous cusp vectors smooth
  have compactBound : ∀ (K : Set BinaryRealGL), IsCompact K →
      ∀ test : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
        ∃ C : ℝ, ∀ A ∈ K, ∀ h', ‖test ((fun _ => κ) A h')‖ ≤ C := fun _ _ test => by
    obtain ⟨C, hC⟩ := bounded test
    exact ⟨C, fun _ _ h' => hC h'⟩
  obtain ⟨C, -, hC⟩ := lineTransferIntegrand_bound_of compactBound ![1, 1, a] functional
  rw [bridgeTransfer_eq_lineTransfer]
  refine integrable_weighted_integral (by omega)
    (ψ := fun u finite => functional (lineTransferIntegrand (fun _ => κ) ![1, 1, a] u
      (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g)))
    (fun finite => lineTransferIntegrand_degenerate_continuous continuous 1 a _ functional)
    (fun u => ?_)
    (((lineInput_measurePreserving 1).integrable_comp_of_integrable
      (kernelBase_decay_integrable large)).const_mul C) (fun u finite => ?_)
  · have rewritten : (fun finite => standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        functional (lineTransferIntegrand (fun _ => κ) ![1, 1, a] u
          (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g))) =
        fun finite => standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          (transferScale n u • (functional ∘ₗ
            realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹ ∘ₗ
              realUpperBinaryValue n (relativeVertex u a).left))
            (κ (atFinite (standardGoodLineFiniteCoordinates finite).block *
              atInfinity (g * B u))) := by
      funext finite
      rw [lineTransferIntegrand_degenerate_one, map_smul, smul_eq_mul, LinearMap.smul_apply,
        smul_eq_mul, atFinite_mul_atInfinity_mul]
      rfl
    rw [rewritten]
    exact (weighted_hilbertLift_continuous cusp vectors smooth spherical _ _).stronglyMeasurable
  · refine (hC u _).trans (le_of_eq ?_)
    change (cornerScale (gsVertex (standardGoodLineRealArgument u * lineMatrix 1)) : ℝ) ^
      (((n : ℝ) + 3) / 2) * C = _
    rw [cornerScale_gsVertex (goodLineForm_lineMatrix u 1), gsVertex_lineMatrix_corner,
      ← abs_of_pos (inv_pos.mpr (gsRadius_pos _)), gsRadius_inv_rpow, mul_comm]
    congr 2
    ring

end TernaryPeriodPolynomials.AnalyticClasses
