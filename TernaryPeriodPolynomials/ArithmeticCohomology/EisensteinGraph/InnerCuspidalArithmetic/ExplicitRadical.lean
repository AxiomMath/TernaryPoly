module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Binary.WedgeAction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def crossedRepresentationEqEquiv {GroupType Value : Type} [Group GroupType]
    [AddCommGroup Value] [Module ℂ Value]
    (first second : Representation ℂ GroupType Value) (same : first = second) :
    crossedCocycles first ≃ₗ[ℂ] crossedCocycles second where
  toFun cochain := ⟨cochain.val, by
    rw [← same]
    exact cochain.property⟩
  invFun cochain := ⟨cochain.val, by
    rw [same]
    exact cochain.property⟩
  left_inv cochain := Subtype.ext rfl
  right_inv cochain := Subtype.ext rfl
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

theorem crossedRepresentationEqEquiv_boundary {GroupType Value : Type} [Group GroupType]
    [AddCommGroup Value] [Module ℂ Value]
    (first second : Representation ℂ GroupType Value) (same : first = second) (value : Value) :
    crossedRepresentationEqEquiv first second same (crossedBoundary first value) =
      crossedBoundary second value := by
  apply Subtype.ext
  funext element
  change first element value - value = second element value - value
  rw [same]

theorem crossedRepresentationEqEquiv_boundaries {GroupType Value : Type} [Group GroupType]
    [AddCommGroup Value] [Module ℂ Value]
    (first second : Representation ℂ GroupType Value) (same : first = second) :
    (crossedBoundaries first).map (crossedRepresentationEqEquiv first second same).toLinearMap =
      crossedBoundaries second := by
  apply le_antisymm
  · rintro cochain ⟨previous, ⟨value, rfl⟩, rfl⟩
    exact ⟨value, (crossedRepresentationEqEquiv_boundary first second same value).symm⟩
  · rintro cochain ⟨value, rfl⟩
    exact ⟨crossedBoundary first value, ⟨value, rfl⟩,
      crossedRepresentationEqEquiv_boundary first second same value⟩

def crossedH1RepresentationEqEquiv {GroupType Value : Type} [Group GroupType]
    [AddCommGroup Value] [Module ℂ Value]
    (first second : Representation ℂ GroupType Value) (same : first = second) :
    CrossedH1 first ≃ₗ[ℂ] CrossedH1 second :=
  Submodule.Quotient.equiv _ _ (crossedRepresentationEqEquiv first second same)
    (crossedRepresentationEqEquiv_boundaries first second same)

def standardRadicalCocycleEquiv (degree : ℕ) :
    crossedCocycles ((standardBadLineRepresentation degree).comp SemidirectProduct.inl) ≃ₗ[ℂ]
      crossedCocycles (radicalRepresentation degree) :=
  crossedRepresentationEqEquiv _ _ (standardBadLineRepresentation_radical degree)

def explicitRadicalBinaryEquiv (degree : ℕ) (positive : 0 < degree) :
    CrossedH1 ((standardBadLineRepresentation degree).comp SemidirectProduct.inl) ≃ₗ[ℂ]
      Binary.HomogeneousPoly (degree + 1) :=
  (crossedH1RepresentationEqEquiv _ _ (standardBadLineRepresentation_radical degree)).trans
    (radicalCrossedBinaryEquiv degree positive)

def explicitBinaryPairCocycle (degree : ℕ)
    (pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree) :
    crossedCocycles ((standardBadLineRepresentation degree).comp SemidirectProduct.inl) :=
  (standardRadicalCocycleEquiv degree).symm (binaryPairRadicalCocycle degree pair)

theorem explicitBinaryPairCocycle_coordinate (degree : ℕ) (positive : 0 < degree)
    (pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree) :
    explicitRadicalBinaryEquiv degree positive
      ((crossedBoundaries ((standardBadLineRepresentation degree).comp SemidirectProduct.inl)).mkQ
        (explicitBinaryPairCocycle degree pair)) = binaryPairWedge degree pair := by
  change radicalCrossedBinaryEquiv degree positive
    ((radicalCrossedBoundaries degree).mkQ
      ((standardRadicalCocycleEquiv degree)
        ((standardRadicalCocycleEquiv degree).symm (binaryPairRadicalCocycle degree pair)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact binaryPairRadicalCocycle_coordinate degree positive pair

theorem explicitBinaryPairCocycle_apply (degree : ℕ)
    (pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree)
    (radical : Multiplicative (ℤ × ℤ)) :
    (explicitBinaryPairCocycle degree pair).val radical =
      (radical.toAdd.1 : ℂ) • binaryHomogeneousEmbedding degree pair.1 +
        (radical.toAdd.2 : ℂ) • binaryHomogeneousEmbedding degree pair.2 := rfl

theorem standardRadicalH1_binaryPair_representative (degree : ℕ) (positive : 0 < degree)
    (coordinate : CrossedH1 ((standardBadLineRepresentation degree).comp SemidirectProduct.inl)) :
    ∃ pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree,
      (crossedBoundaries ((standardBadLineRepresentation degree).comp SemidirectProduct.inl)).mkQ
        (explicitBinaryPairCocycle degree pair) = coordinate := by
  refine ⟨binaryEulerPair degree (explicitRadicalBinaryEquiv degree positive coordinate), ?_⟩
  apply (explicitRadicalBinaryEquiv degree positive).injective
  rw [explicitBinaryPairCocycle_coordinate, binaryPairWedge_euler]

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
