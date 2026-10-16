module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Target.GlueIntegrable

@[expose] public section


/-!
# The finite average of the real transfer of the reconstructed binary cocycle

Let `B` be a binary cocycle reconstructed from the classical endpoint `v` and a finite-level
correction `κ`, so that pointwise `B = N_{F_v} + δκ` with `F_v` the scalar weighted realization
of `v`. Its real good-line transfer is `t_{N_{F_v}} + δ(θκ)`. Every piece is absolutely
convergent along the finite good-line average at real points, so the finite average of the
transfer of `B` at `(a, b)` is `T (a, b)` at the identity, where
`T = t_{N_{F_avg}} + δH`, `F_avg` is the finite average of `F_v`, and `H q` is the finite average
of the transfer of `θκ` at `q`. The same holds for the mixed radical edges of the transfer.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

variable {n : ℕ}

/-- **The averaged real transfer** `T = t_{N_{F_avg}} + δH` of the reconstructed binary cocycle:
`F_avg` is the finite average of `F`, and `H q` the finite average of the transfer of `θκ`. -/
def averagedTransfer (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ)
    (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (a b : LineGroup) : LineValues n :=
  lineTransferCochain (eichlerNormal n (averagedRealForm n F)) a b +
    (a • averagedLine (bridgeTransfer κ b) - averagedLine (bridgeTransfer κ (a * b)) +
      averagedLine (bridgeTransfer κ a))

theorem averagedTransfer_apply (F : BinaryAdelicGL → ℂ → ℂ)
    (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (a b : LineGroup)
    (p : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ)) :
    averagedTransfer n F κ a b p =
      lineTransferCochain (eichlerNormal n (averagedRealForm n F)) a b p +
        ((a • averagedLine (bridgeTransfer κ b)) p - averagedLine (bridgeTransfer κ (a * b)) p +
          averagedLine (bridgeTransfer κ a) p) := rfl

section Reconstructed

variable (cusp : CuspidalRepresentation) (stages : AnalyticScalar.ContinuousStages cusp)
  (halfWeight : ℤ) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
  (hF : EichlerData n (cuspScalarWeightedRealization cusp halfWeight vector))
  (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp n))
  (correction : Fin (n + 2) → cusp.H)
  (correction_smooth : ∀ position, correction position ∈ cusp.smooth)
  (correction_spherical : ∀ position, correction position ∈ cuspSphericalValues cusp)
  (reconstruction : ∀ A : BinaryRealGL,
    binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) (original A) =
      (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp n halfWeight vector.val
        ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
        binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
          (binaryEndpointPeriod cusp n halfWeight vector.val
            (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
      (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A correction - correction))

include stages spherical hF correction_smooth correction_spherical reconstruction in
/-- **The finite average of the transfer of the reconstructed binary cocycle is the averaged
transfer at the identity** (`n ≥ 5`), and it is absolutely convergent. -/
theorem finiteAverageLine_original (large : 5 ≤ n) (a b : LineGroup)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun finite => standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        lineTransferCochain (fun A => (original A).val) a b
          (atFinite (standardGoodLineFiniteCoordinates finite).block, functional))
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      finiteAverageLine (lineTransferCochain (fun A => (original A).val) a b) functional =
        averagedTransfer n (cuspScalarWeightedRealization cusp halfWeight vector)
          (hilbertLift cusp n correction) a b (1, functional) := by
  set F := cuspScalarWeightedRealization cusp halfWeight vector
  set κ := hilbertLift cusp n correction
  set w := standardGoodLineFiniteCuspWeight n cohomologicalPoint
  set block := fun finite : FiniteAwayThree × FiniteAwayThree =>
    atFinite (standardGoodLineFiniteCoordinates finite).block
  set pivot := pivotConjugate (a.right : BinaryRealGL)
  set shifted := functional ∘ₗ realCoefficientComponent n trivialCharacter (lineMatrix a)
  have decomposition := lineTransferCochain_original_eq large cusp stages halfWeight vector
    (spherical_mem_fixedSubspace cusp _ spherical) original correction correction_smooth
    reconstruction a b
  have i₀ := lineAverage_integrable_eichlerNormal cusp halfWeight vector spherical large hF a b 1
    functional
  have i₁ := lineAverage_integrable_bridgeTransfer large cusp correction correction_smooth
    correction_spherical b pivot shifted
  have i₂ := lineAverage_integrable_bridgeTransfer large cusp correction correction_smooth
    correction_spherical (a * b) 1 functional
  have i₃ := lineAverage_integrable_bridgeTransfer large cusp correction correction_smooth
    correction_spherical a 1 functional
  simp only [atInfinity_one, mul_one] at i₀ i₂ i₃
  have pointwise (finite : FiniteAwayThree × FiniteAwayThree) :
      w finite * lineTransferCochain (fun A => (original A).val) a b (block finite, functional) =
        w finite * lineTransferCochain (eichlerNormal n F) a b (block finite, functional) +
          (w finite * bridgeTransfer κ b (block finite * atInfinity pivot, shifted) -
            w finite * bridgeTransfer κ (a * b) (block finite, functional) +
            w finite * bridgeTransfer κ a (block finite, functional)) := by
    rw [decomposition]
    change w finite * (lineTransferCochain (eichlerNormal n F) a b (block finite, functional) +
      ((a • bridgeTransfer κ b) (block finite, functional) -
        bridgeTransfer κ (a * b) (block finite, functional) +
        bridgeTransfer κ a (block finite, functional))) = _
    rw [lineValues_smul_apply]
    ring
  have total : Integrable (fun finite => w finite * lineTransferCochain (eichlerNormal n F) a b
      (block finite, functional) +
        (w finite * bridgeTransfer κ b (block finite * atInfinity pivot, shifted) -
          w finite * bridgeTransfer κ (a * b) (block finite, functional) +
          w finite * bridgeTransfer κ a (block finite, functional)))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := i₀.add ((i₁.sub i₂).add i₃)
  refine ⟨total.congr (Filter.Eventually.of_forall fun finite => (pointwise finite).symm), ?_⟩
  have e₀ : ∫ finite, w finite * lineTransferCochain (eichlerNormal n F) a b
      (block finite, functional) ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      lineTransferCochain (eichlerNormal n (averagedRealForm n F)) a b (1, functional) :=
    finiteAverageLine_lineTransferCochain_eichlerNormal cusp halfWeight vector spherical large hF
      a b functional
  have e₁ : ∫ finite, w finite * bridgeTransfer κ b (block finite * atInfinity pivot, shifted)
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      (a • averagedLine (bridgeTransfer κ b)) (1, functional) := by
    rw [lineValues_smul_apply, averagedLine_apply, one_mul]
  have e₂ : ∫ finite, w finite * bridgeTransfer κ (a * b) (block finite, functional)
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      averagedLine (bridgeTransfer κ (a * b)) (1, functional) := by
    rw [averagedLine_apply]
    simp only [mul_one, block, w]
  have e₃ : ∫ finite, w finite * bridgeTransfer κ a (block finite, functional)
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
      averagedLine (bridgeTransfer κ a) (1, functional) := by
    rw [averagedLine_apply]
    simp only [mul_one, block, w]
  change ∫ finite, w finite * lineTransferCochain (fun A => (original A).val) a b
      (block finite, functional) ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) = _
  have h₁ := integral_add i₀ ((i₁.sub i₂).add i₃)
  have h₂ := integral_add (i₁.sub i₂) i₃
  have h₃ := integral_sub i₁ i₂
  simp only [Pi.add_apply, Pi.sub_apply] at h₁ h₂ h₃
  rw [integral_congr_ae (Filter.Eventually.of_forall pointwise), h₁, h₂, h₃, e₀, e₁, e₂, e₃,
    averagedTransfer_apply]

include stages spherical hF correction_smooth correction_spherical reconstruction in
/-- **The finite average of a mixed radical edge of the transfer of the reconstructed binary
cocycle is the mixed radical edge of the averaged transfer at the identity** (`n ≥ 5`). -/
theorem finiteAverageLine_radicalEdge_original (large : 5 ≤ n) (m : unimodularLevi)
    (Y : Fin 2 → ℝ) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    finiteAverageLine (radicalEdge (lineTransferCochain (fun A => (original A).val)) m Y)
        functional =
      radicalEdge (averagedTransfer n (cuspScalarWeightedRealization cusp halfWeight vector)
        (hilbertLift cusp n correction)) m Y (1, functional) := by
  have first := finiteAverageLine_original cusp stages halfWeight vector spherical hF original
    correction correction_smooth correction_spherical reconstruction large (lineLeviElement m)
    (lineRadicalElement (Matrix.vecMul Y (m : BinaryRealGL).val)) functional
  have second := finiteAverageLine_original cusp stages halfWeight vector spherical hF original
    correction correction_smooth correction_spherical reconstruction large (lineRadicalElement Y)
    (lineLeviElement m) functional
  rw [radicalEdge_eq, radicalEdge_eq]
  change ∫ finite, standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
      (lineTransferCochain (fun A => (original A).val) (lineLeviElement m)
          (lineRadicalElement (Matrix.vecMul Y (m : BinaryRealGL).val))
          (atFinite (standardGoodLineFiniteCoordinates finite).block, functional) -
        lineTransferCochain (fun A => (original A).val) (lineRadicalElement Y) (lineLeviElement m)
          (atFinite (standardGoodLineFiniteCoordinates finite).block, functional))
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) = _
  simp only [mul_sub]
  rw [integral_sub first.1 second.1]
  exact congrArg₂ (· - ·) first.2 second.2

end Reconstructed

end TernaryPeriodPolynomials.AnalyticClasses
