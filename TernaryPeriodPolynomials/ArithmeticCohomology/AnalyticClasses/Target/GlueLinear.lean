module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Target.GlueSplit
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeAnalyticRegular

@[expose] public section


/-!
# Linearity of the averaged transfer in the test at the identity

A scalar test `F(h, λ)` is linear in the test at a point `h` if `F(h, λ) = λ(v_F(h))` for the
coefficient vector `v_F(h)` read off from the dual basis. This is stable under sums, differences
and, at `h`, under the action of the real good-line stabilizer if it holds at the moved point.
The finite average of the transfer of `θκ`, for the lift `κ` of a smooth spherical tuple, is
linear in the test at real points, since the averaged scalar tests are absolutely convergent
there. Hence the averaged transfer `T` and its mixed radical edges are linear in the test at the
identity.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ}

/-- Scalar tests that are linear in the test at one adelic point. -/
def LinearAt (F : LineValues n) (h : BinaryAdelicGL) : Prop :=
  ∀ functional : HomogeneousPoly n →ₗ[ℂ] ℂ, F (h, functional) = functional (lineVector F h)

theorem LinearTests.linearAt {F : LineValues n} (linear : LinearTests F) (h : BinaryAdelicGL) :
    LinearAt F h :=
  linear h

theorem LinearAt.add {F G : LineValues n} {h : BinaryAdelicGL} (first : LinearAt F h)
    (second : LinearAt G h) : LinearAt (F + G) h := by
  intro functional
  change F (h, functional) + G (h, functional) = _
  rw [lineVector_add, map_add, first, second]

theorem LinearAt.sub {F G : LineValues n} {h : BinaryAdelicGL} (first : LinearAt F h)
    (second : LinearAt G h) : LinearAt (F - G) h := by
  intro functional
  change F (h, functional) - G (h, functional) = _
  rw [lineVector_sub, map_sub, first, second]

theorem LinearAt.smul {F : LineValues n} {q : LineGroup} {h : BinaryAdelicGL}
    (linear : LinearAt F (h * atInfinity (pivotConjugate (q.right : BinaryRealGL)))) :
    LinearAt (q • F) h := by
  intro functional
  have vector : lineVector (q • F) h = realCoefficientComponent n trivialCharacter (lineMatrix q)
      (lineVector F (h * atInfinity (pivotConjugate (q.right : BinaryRealGL)))) := by
    unfold lineVector
    simp only [lineValues_smul_apply]
    simp_rw [linear (((homogeneousBasis n).coord _).comp _), LinearMap.comp_apply,
      Module.Basis.coord_apply]
    exact (homogeneousBasis n).sum_repr _
  rw [vector, lineValues_smul_apply, linear, LinearMap.comp_apply]

/-- **The finite average of the transfer of `θκ` is linear in the test at real points**, for the
lift `κ` of a smooth spherical tuple (`n ≥ 5`). -/
theorem linearAt_averagedLine_bridgeTransfer (large : 5 ≤ n) (cusp : CuspidalRepresentation)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth)
    (spherical : ∀ position, vectors position ∈ cuspSphericalValues cusp) (a : LineGroup)
    (g : BinaryRealGL) :
    LinearAt (averagedLine (bridgeTransfer (hilbertLift cusp n vectors) a)) (atInfinity g) := by
  intro functional
  have linear := linearTests_bridgeTransfer large (hilbertLift_bounded cusp vectors smooth)
    (hilbertLift_ambient_continuous cusp vectors smooth) a
  have integrable (j : Fin (Module.finrank ℂ (HomogeneousPoly n))) :=
    (lineAverage_integrable_bridgeTransfer large cusp vectors smooth spherical a g
      ((homogeneousBasis n).coord j)).mul_const (functional (homogeneousBasis n j))
  have pointwise (finite : FiniteAwayThree × FiniteAwayThree) :
      standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          bridgeTransfer (hilbertLift cusp n vectors) a
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g,
              functional) =
        ∑ j, standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
          bridgeTransfer (hilbertLift cusp n vectors) a
            (atFinite (standardGoodLineFiniteCoordinates finite).block * atInfinity g,
              (homogeneousBasis n).coord j) * functional (homogeneousBasis n j) := by
    rw [linear, functional_lineVector, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [functional_lineVector]
  simp only [averagedLine_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall pointwise),
    integral_finsetSum _ fun j _ => integrable j]
  exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _

section Averaged

variable (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
  (spherical : vector.val ∈ cuspSphericalValues cusp)
  (hF : EichlerData n (cuspScalarWeightedRealization cusp halfWeight vector))
  (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth)
  (vectors_spherical : ∀ position, vectors position ∈ cuspSphericalValues cusp)

include spherical hF smooth vectors_spherical in
/-- **The averaged transfer is linear in the test at the identity** (`n ≥ 5`). -/
theorem linearAt_averagedTransfer (large : 5 ≤ n) (a b : LineGroup) :
    LinearAt (averagedTransfer n (cuspScalarWeightedRealization cusp halfWeight vector)
      (hilbertLift cusp n vectors) a b) 1 := by
  have averaged := hF.averagedReal_cuspScalar cusp halfWeight vector spherical (by omega)
  have bridge (q : LineGroup) (g : BinaryRealGL) :=
    linearAt_averagedLine_bridgeTransfer large cusp vectors smooth vectors_spherical q g
  refine ((lineTransferCochain_linear large averaged a b).linearAt 1).add
    ((LinearAt.smul ?_).sub ?_ |>.add ?_)
  · rw [one_mul]
    exact bridge b _
  · rw [← atInfinity_one]
    exact bridge (a * b) 1
  · rw [← atInfinity_one]
    exact bridge a 1

include spherical hF smooth vectors_spherical in
/-- **The mixed radical edges of the averaged transfer are linear in the test at the identity**
(`n ≥ 5`). -/
theorem linearAt_radicalEdge_averagedTransfer (large : 5 ≤ n) (m : unimodularLevi)
    (Y : Fin 2 → ℝ) :
    LinearAt (radicalEdge (averagedTransfer n (cuspScalarWeightedRealization cusp halfWeight
      vector) (hilbertLift cusp n vectors)) m Y) 1 := by
  rw [radicalEdge_eq]
  exact (linearAt_averagedTransfer cusp halfWeight vector spherical hF vectors smooth
    vectors_spherical large _ _).sub
    (linearAt_averagedTransfer cusp halfWeight vector spherical hF vectors smooth
      vectors_spherical large _ _)

end Averaged

end TernaryPeriodPolynomials.AnalyticClasses
