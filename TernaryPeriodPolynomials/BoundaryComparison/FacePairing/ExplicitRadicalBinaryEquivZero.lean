module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RadicalCrossedH1ZeroEquiv
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BinaryWedgeZeroEquiv
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BinaryEmbeddingZeroEquiv
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ExplicitRadical

@[expose] public section


/-!
# The degree-`0` radical-to-binary identification

The degree-0 analogue of `explicitRadicalBinaryEquiv`: a `LinearEquiv` from the bad-line crossed
`H¹` at degree `0` directly to `Binary.HomogeneousPoly 1`, built from the same two-step template
(`crossedH1RepresentationEqEquiv` transporting along the literal radical-restriction equality,
then the radical-to-pair identification) but with the degree-0 replacements
(`radicalCrossedH1ZeroEquiv`, `binaryHomogeneousEmbeddingZeroEquiv`, `binaryPairWedgeZeroEquiv`)
standing in for the positive-degree Koszul/exponential machinery.
-/

noncomputable section

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **The degree-`0` analogue of `explicitRadicalBinaryEquiv`.** -/
def explicitRadicalBinaryEquivZero :
    CrossedH1 ((standardBadLineRepresentation 0).comp SemidirectProduct.inl) ≃ₗ[ℂ]
      Binary.HomogeneousPoly 1 :=
  (crossedH1RepresentationEqEquiv _ _ (standardBadLineRepresentation_radical 0)).trans
    (radicalCrossedH1ZeroEquiv.trans
      ((LinearEquiv.prodCongr binaryHomogeneousEmbeddingZeroEquiv.symm
          binaryHomogeneousEmbeddingZeroEquiv.symm).trans
        binaryPairWedgeZeroEquiv))

/-- The evaluation of a binary-pair radical cocycle at the two generators, bundled as the pair
`radicalCrossedEvaluation` extracts. -/
theorem radicalCrossedEvaluation_binaryPairRadicalCocycle
    (pair : Binary.HomogeneousPoly 0 × Binary.HomogeneousPoly 0) :
    (radicalCrossedEvaluation 0 (binaryPairRadicalCocycle 0 pair)).val =
      (binaryHomogeneousEmbedding 0 pair.1, binaryHomogeneousEmbedding 0 pair.2) := by
  show ((binaryPairRadicalCocycle 0 pair).val (integralRadicalGenerator 0),
    (binaryPairRadicalCocycle 0 pair).val (integralRadicalGenerator 1)) = _
  simp [binaryPairRadicalCocycle_generator]

/-- The degree-`0` radical crossed `H¹` equivalence sends the class of a binary-pair radical
cocycle to the pair's binary embedding. -/
theorem radicalCrossedH1ZeroEquiv_binaryPairRadicalCocycle
    (pair : Binary.HomogeneousPoly 0 × Binary.HomogeneousPoly 0) :
    radicalCrossedH1ZeroEquiv ((radicalCrossedBoundaries 0).mkQ (binaryPairRadicalCocycle 0 pair)) =
      (binaryHomogeneousEmbedding 0 pair.1, binaryHomogeneousEmbedding 0 pair.2) := by
  simp only [radicalCrossedH1ZeroEquiv, radicalCrossedH1ZeroEquivCocycles,
    radicalCrossedEvaluationEquiv, LinearEquiv.trans_apply,
    LinearEquiv.ofEq, Submodule.topEquiv_apply]
  exact radicalCrossedEvaluation_binaryPairRadicalCocycle pair

/-- `binaryHomogeneousEmbeddingZeroEquiv.symm` undoes `binaryHomogeneousEmbedding 0`. -/
theorem binaryHomogeneousEmbeddingZeroEquiv_symm_apply (f : Binary.HomogeneousPoly 0) :
    binaryHomogeneousEmbeddingZeroEquiv.symm (binaryHomogeneousEmbedding 0 f) = f := by
  apply binaryHomogeneousEmbeddingZeroEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- **Degree-`0` coordinate fact**: `explicitRadicalBinaryEquivZero` sends the class of
`explicitBinaryPairCocycle 0 pair` to `binaryPairWedge 0 pair`, exactly mirroring
`explicitBinaryPairCocycle_coordinate` at positive degree. -/
theorem explicitBinaryPairCocycle_coordinate_zero
    (pair : Binary.HomogeneousPoly 0 × Binary.HomogeneousPoly 0) :
    explicitRadicalBinaryEquivZero
      ((crossedBoundaries ((standardBadLineRepresentation 0).comp SemidirectProduct.inl)).mkQ
        (explicitBinaryPairCocycle 0 pair)) = binaryPairWedge 0 pair := by
  change (radicalCrossedH1ZeroEquiv.trans
      ((LinearEquiv.prodCongr binaryHomogeneousEmbeddingZeroEquiv.symm
          binaryHomogeneousEmbeddingZeroEquiv.symm).trans binaryPairWedgeZeroEquiv))
    ((radicalCrossedBoundaries 0).mkQ
      ((standardRadicalCocycleEquiv 0)
        ((standardRadicalCocycleEquiv 0).symm (binaryPairRadicalCocycle 0 pair)))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    radicalCrossedH1ZeroEquiv_binaryPairRadicalCocycle, LinearEquiv.prodCongr_apply,
    binaryHomogeneousEmbeddingZeroEquiv_symm_apply, binaryHomogeneousEmbeddingZeroEquiv_symm_apply]
  simp only [binaryPairWedgeZeroEquiv, LinearEquiv.ofBijective_apply, binaryPairWedgeZeroLinear,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- **Degree-`0` binary-pair representative fact**: every class in the degree-`0` bad-line
crossed `H¹` is represented by some `explicitBinaryPairCocycle 0 pair`, exactly mirroring
`standardRadicalH1_binaryPair_representative` at positive degree. -/
theorem standardRadicalH1_binaryPair_representative_zero
    (coordinate : CrossedH1 ((standardBadLineRepresentation 0).comp SemidirectProduct.inl)) :
    ∃ pair : Binary.HomogeneousPoly 0 × Binary.HomogeneousPoly 0,
      (crossedBoundaries ((standardBadLineRepresentation 0).comp SemidirectProduct.inl)).mkQ
        (explicitBinaryPairCocycle 0 pair) = coordinate := by
  refine ⟨binaryEulerPair 0 (explicitRadicalBinaryEquivZero coordinate), ?_⟩
  apply explicitRadicalBinaryEquivZero.injective
  rw [explicitBinaryPairCocycle_coordinate_zero, binaryPairWedge_euler]

end TernaryPeriodPolynomials.Argument.FacePairing
