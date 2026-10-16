module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Levi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.EdgeExactness
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.InvariantCoordinates

@[expose] public section


/-!
# The identity-plane stabilizer with sign-twisted coefficients

For a rank-one character `χ` with `χ(-1_∞) = -1` the coefficient representation
`rationalCoefficientComponent n χ` restricted to the identity-plane stabilizer `Λ₀ = U ⋊ GL₂(ℤ)`
differs from the trivial-character one by the sign of the Levi determinant.  The restriction to the
radical `U` is unchanged, while the Levi element `diag(m, 1)` acts by `det m • arithmeticLeviCoefficient`.
Consequently the Hochschild–Serre edge of `Λ₀` takes values in `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁰)` and the
radical invariants form the trivial `GL₂(ℤ)`-module.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

/-- The coefficient representation of the identity-plane stabilizer for the character `χ`. -/
def identityPlaneCoefficientRepT (n : ℕ) (χ : RankOneCharacter) :
    Rep ℂ (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :=
  Rep.of ((rationalCoefficientComponent n χ).comp
    (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))).subtype)

/-- The Levi section acts by the integral determinant times the untwisted Levi action. -/
theorem identityPlaneCoefficientRepT_section (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    (identityPlaneCoefficientRepT n χ).ρ (identityPlaneLeviSection matrix) =
      (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) • arithmeticLeviCoefficient n matrix :=
  rho_arithmeticLevi_odd n hχ matrix

/-- The twisted representation restricted to the radical acts as the untwisted one. -/
theorem identityPlaneCoefficientRepT_radical_rho (n : ℕ) (χ : RankOneCharacter)
    (element : RadicalLattice) :
    (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)).ρ element =
      (upperRadicalLatticeRep n).ρ element :=
  rho_upperRadicalLattice n χ element

/-- The restriction of the twisted stabilizer representation to the radical is the upper radical
lattice representation. -/
theorem identityPlaneCoefficientRepT_radical (n : ℕ) (χ : RankOneCharacter) :
    Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) =
      upperRadicalLatticeRep n := by
  have equality : ((rationalCoefficientComponent n χ).comp
      (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))).subtype).comp
        identityPlaneRadicalInclusion =
      (rationalCoefficientComponent n trivialCharacter).comp upperRadicalLattice :=
    MonoidHom.ext (rho_upperRadicalLattice n χ)
  exact congrArg Rep.of equality

/-! ### Transport between the restricted representation and the upper radical representation -/

/-- The identity map from the restricted twisted representation to the upper radical lattice
representation. -/
def radicalComparisonT (n : ℕ) (χ : RankOneCharacter) :
    Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) →ₗ[ℂ]
      upperRadicalLatticeRep n :=
  LinearMap.id

/-- The identity map from the upper radical lattice representation to the restricted twisted
representation. -/
def radicalComparisonInvT (n : ℕ) (χ : RankOneCharacter) :
    upperRadicalLatticeRep n →ₗ[ℂ]
      Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) :=
  LinearMap.id

theorem radicalComparisonT_intertwines (n : ℕ) (χ : RankOneCharacter) (element : RadicalLattice) :
    ((upperRadicalLatticeRep n).ρ element).comp (radicalComparisonT n χ) =
      (radicalComparisonT n χ).comp
        ((Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)).ρ
          ((MonoidHom.id RadicalLattice) element)) := by
  apply LinearMap.ext
  intro vector
  exact LinearMap.congr_fun (identityPlaneCoefficientRepT_radical_rho n χ element).symm vector

theorem radicalComparisonInvT_intertwines (n : ℕ) (χ : RankOneCharacter)
    (element : RadicalLattice) :
    ((Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)).ρ element).comp
        (radicalComparisonInvT n χ) =
      (radicalComparisonInvT n χ).comp
        ((upperRadicalLatticeRep n).ρ ((MonoidHom.id RadicalLattice) element)) := by
  apply LinearMap.ext
  intro vector
  exact LinearMap.congr_fun (identityPlaneCoefficientRepT_radical_rho n χ element) vector

/-- One-cocycles of the restricted twisted representation are one-cocycles of the upper radical
representation (same underlying function). -/
def cocycleToUpperT (n : ℕ) (χ : RankOneCharacter) :
    groupCohomology.cocycles₁ (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) →ₗ[ℂ]
      groupCohomology.cocycles₁ (upperRadicalLatticeRep n) :=
  oneCocyclePullback _ _ (MonoidHom.id RadicalLattice) (radicalComparisonT n χ)
    (radicalComparisonT_intertwines n χ)

/-- The inverse of `cocycleToUpperT`. -/
def cocycleFromUpperT (n : ℕ) (χ : RankOneCharacter) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep n) →ₗ[ℂ]
      groupCohomology.cocycles₁ (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) :=
  oneCocyclePullback _ _ (MonoidHom.id RadicalLattice) (radicalComparisonInvT n χ)
    (radicalComparisonInvT_intertwines n χ)

theorem cocycleToUpperT_apply (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₁
      (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)))
    (element : RadicalLattice) :
    cocycleToUpperT n χ cycle element = cycle element := rfl

theorem cocycleToUpperT_fromUpper (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) :
    cocycleToUpperT n χ (cocycleFromUpperT n χ cycle) = cycle := by
  apply groupCohomology.cocycles₁_ext
  intro element
  rfl

theorem cocycleFromUpperT_toUpper (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₁
      (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))) :
    cocycleFromUpperT n χ (cocycleToUpperT n χ cycle) = cycle := by
  apply groupCohomology.cocycles₁_ext
  intro element
  rfl

/-- The identification of the first cohomology of the restricted twisted representation with that of
the upper radical lattice representation. -/
def radicalH1EquivT (n : ℕ) (χ : RankOneCharacter) :
    groupCohomology.H1 (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) ≃ₗ[ℂ]
      groupCohomology.H1 (upperRadicalLatticeRep n) :=
  LinearEquiv.ofLinearMap
    (f := oneCocyclePullbackH1 _ _ (MonoidHom.id RadicalLattice) (radicalComparisonT n χ)
      (radicalComparisonT_intertwines n χ))
    (g := oneCocyclePullbackH1 _ _ (MonoidHom.id RadicalLattice) (radicalComparisonInvT n χ)
      (radicalComparisonInvT_intertwines n χ))
    (by
      apply LinearMap.ext
      intro cohomology
      obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (upperRadicalLatticeRep n) cohomology
      rw [LinearMap.comp_apply, oneCocyclePullbackH1_apply, oneCocyclePullbackH1_apply]
      exact congrArg (groupCohomology.H1π (upperRadicalLatticeRep n))
        (cocycleToUpperT_fromUpper n χ cycle))
    (by
      apply LinearMap.ext
      intro cohomology
      obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective
        (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) cohomology
      rw [LinearMap.comp_apply, oneCocyclePullbackH1_apply, oneCocyclePullbackH1_apply]
      exact congrArg
        (groupCohomology.H1π (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)))
        (cocycleFromUpperT_toUpper n χ cycle))

/-- Binary coordinates on the first cohomology of the restricted twisted representation. -/
def identityPlaneRadicalH1CoordinateT (n : ℕ) (χ : RankOneCharacter) :
    groupCohomology.H1 (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) ≃ₗ[ℂ]
      Binary.HomogeneousPoly (n + 1) :=
  (radicalH1EquivT n χ).trans (upperRadicalH1Coordinate n)

theorem identityPlaneRadicalH1CoordinateT_apply (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₁
      (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))) :
    identityPlaneRadicalH1CoordinateT n χ
        (groupCohomology.H1π (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) cycle) =
      upperRadicalCocycleCoordinate n (cocycleToUpperT n χ cycle) :=
  (congrArg (fun cohomology => upperRadicalH1Coordinate n cohomology)
    (oneCocyclePullbackH1_apply _ _ (MonoidHom.id RadicalLattice) (radicalComparisonT n χ)
      (radicalComparisonT_intertwines n χ) cycle)).trans (upperRadicalH1Coordinate_apply _)

/-! ### The Levi action on the radical cohomology -/

theorem det_map_intCast (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    (((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) : ℂˣ)) : ℂ) =
      (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) := by
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
  exact ((Int.castRingHom ℂ).map_det matrix.val).symm

/-- The twist-zero binary action is the determinant times the twist `-1` action. -/
theorem homogeneousAction_zero_twist_apply (d : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (polynomial : Binary.HomogeneousPoly d) :
    Binary.homogeneousAction d 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) polynomial =
      (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) •
        Binary.homogeneousAction d (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
          polynomial := by
  have twist := LinearMap.congr_fun
    (homogeneousAction_succ_twist d (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)) polynomial
  rw [LinearMap.smul_apply, det_map_intCast] at twist
  have zero : (-1 : ℤ) + 1 = 0 := by norm_num
  rw [zero] at twist
  exact twist

theorem splitRadicalH1Action_applyT (n : ℕ) (χ : RankOneCharacter)
    (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁
      (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))) :
    splitRadicalH1Action identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix
        (groupCohomology.H1π (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) cycle) =
      groupCohomology.H1π (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))
        (splitRadicalCocycleAction identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix cycle) :=
  splitRadicalH1Action_apply identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix cycle

theorem cocycleToUpperT_splitAction (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁
      (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))) :
    cocycleToUpperT n χ
        (splitRadicalCocycleAction identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix cycle) =
      (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) •
        upperRadicalCocycleLevi n matrix (cocycleToUpperT n χ cycle) := by
  apply groupCohomology.cocycles₁_ext
  intro element
  have inverse : identityPlaneSplitting.conjAct matrix⁻¹ element = upperLeviLatticeInput matrix element :=
    identityPlaneSplitting_inverse_action matrix element
  change (identityPlaneCoefficientRepT n χ).ρ (identityPlaneLeviSection matrix)
      (cycle (identityPlaneSplitting.conjAct matrix⁻¹ element)) =
    (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) •
      arithmeticLeviCoefficient n matrix (cycle (upperLeviLatticeInput matrix element))
  rw [identityPlaneCoefficientRepT_section n χ hχ matrix, inverse]
  rfl

/-- The binary coordinate is equivariant for the twisted Levi action, with determinant twist `0`. -/
theorem identityPlaneRadicalH1CoordinateT_equivariant (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cohomology : groupCohomology.H1
      (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))) :
    identityPlaneRadicalH1CoordinateT n χ
        (splitRadicalH1Action identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix cohomology) =
      Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (identityPlaneRadicalH1CoordinateT n χ cohomology) := by
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective
    (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) cohomology
  have left := identityPlaneRadicalH1CoordinateT_apply n χ
    (splitRadicalCocycleAction identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix cycle)
  have right := identityPlaneRadicalH1CoordinateT_apply n χ cycle
  rw [splitRadicalH1Action_applyT, left, right, cocycleToUpperT_splitAction n χ hχ matrix cycle,
    map_smul (upperRadicalCocycleCoordinate n), upperRadicalCocycleCoordinate_equivariant,
    homogeneousAction_zero_twist_apply]

/-- **The twisted Levi coordinate isomorphism.**  The first cohomology of the radical, as a
`GL₂(ℤ)`-module, is `Sym^{n+1} ⊗ det⁰`. -/
def identityPlaneRadicalCoordinateIsoT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRepT n χ) ≅
      arithmeticBinaryRep (n + 1) 0 :=
  Rep.mkIso (Representation.Equiv.mk (identityPlaneRadicalH1CoordinateT n χ) (by
    intro matrix
    apply LinearMap.ext
    intro cohomology
    change groupCohomology.H1
      (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) at cohomology
    change identityPlaneRadicalH1CoordinateT n χ
        (splitRadicalH1Action identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix cohomology) =
      Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (identityPlaneRadicalH1CoordinateT n χ cohomology)
    exact identityPlaneRadicalH1CoordinateT_equivariant n χ hχ matrix cohomology))

/-- The isomorphism on first `GL₂(ℤ)`-cohomology induced by the coordinate isomorphism. -/
def identityPlaneLeviCohomologyIsoT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    groupCohomology.H1
        (splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRepT n χ)) ≅
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0) :=
  (groupCohomology.functor ℂ (GeneralLinearGroup (Fin 2) ℤ) 1).mapIso
    (identityPlaneRadicalCoordinateIsoT n χ hχ)

/-- **The source stabilizer edge** with the twisted coefficients: its target is the first cohomology
of `Sym^{n+1} ⊗ det⁰`. -/
def identityPlaneBinaryEdgeT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    (twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)).ker →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0) :=
  (identityPlaneLeviCohomologyIsoT n χ hχ).hom.hom.comp
    (splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRepT n χ))

theorem identityPlaneBinaryEdgeT_apply (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) :
    identityPlaneBinaryEdgeT n χ hχ
        (relativeTwoCocycleClass identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) cycle) =
      (identityPlaneLeviCohomologyIsoT n χ hχ).hom
        (groupCohomology.H1π
          (splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRepT n χ))
          (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRepT n χ) cycle)) := by
  exact congrArg (fun cohomology => (identityPlaneLeviCohomologyIsoT n χ hχ).hom cohomology)
    (splitCohomologyEdge_apply identityPlaneSplitting (identityPlaneCoefficientRepT n χ) cycle)

/-! ### The radical invariants form the trivial representation -/

/-- The trivial one-dimensional representation of `GL₂(ℤ)`. -/
def arithmeticTrivialRep : Rep ℂ (GeneralLinearGroup (Fin 2) ℤ) :=
  Rep.of (Representation.trivial ℂ (GeneralLinearGroup (Fin 2) ℤ) ℂ)

theorem identityPlaneCoefficientRepT_invariants (n : ℕ) (χ : RankOneCharacter) :
    (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)).ρ.invariants =
      (upperRadicalLatticeRep n).ρ.invariants := by
  refine Submodule.ext (fun (vector : HomogeneousPoly n) => ?_)
  change vector ∈ Representation.invariants
      ((rationalCoefficientComponent n χ).comp upperRadicalLattice : Representation ℂ RadicalLattice
        (HomogeneousPoly n)) ↔
    vector ∈ Representation.invariants
      ((rationalCoefficientComponent n trivialCharacter).comp upperRadicalLattice :
        Representation ℂ RadicalLattice (HomogeneousPoly n))
  rw [Representation.mem_invariants, Representation.mem_invariants]
  apply forall_congr'
  intro element
  change rationalCoefficientComponent n χ (upperRadicalLattice element) vector = vector ↔
    rationalCoefficientComponent n trivialCharacter (upperRadicalLattice element) vector = vector
  rw [rho_upperRadicalLattice n χ element]

/-- The radical invariants are the line spanned by `X₂ⁿ`. -/
def identityPlaneInvariantEquivT (n : ℕ) (χ : RankOneCharacter) :
    ℂ ≃ₗ[ℂ] (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)).ρ.invariants :=
  (upperRadicalInvariantEquiv n).trans
    (LinearEquiv.ofEq _ _ (identityPlaneCoefficientRepT_invariants n χ).symm)

theorem identityPlaneInvariantEquivT_apply (n : ℕ) (χ : RankOneCharacter) (scalar : ℂ) :
    (identityPlaneInvariantEquivT n χ scalar).val = upperRadicalInvariantEmbedding n scalar := rfl

/-- The twisted Levi action fixes the radical-invariant line pointwise. -/
theorem identityPlaneCoefficientRepT_section_embedding (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (scalar : ℂ) :
    (identityPlaneCoefficientRepT n χ).ρ (identityPlaneLeviSection matrix)
        (upperRadicalInvariantEmbedding n scalar) = upperRadicalInvariantEmbedding n scalar := by
  have nonzero : (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) ≠ 0 :=
    Int.cast_ne_zero.mpr (Units.ne_zero _)
  have character : (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) * arithmeticDeterminantCharacter matrix = 1 := by
    change (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) *
      (((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) : ℂˣ)) : ℂ) ^ (-1 : ℤ) = 1
    rw [det_map_intCast, zpow_neg_one, mul_inv_cancel₀ nonzero]
  have action : (identityPlaneCoefficientRepT n χ).ρ (identityPlaneLeviSection matrix)
      (upperRadicalInvariantEmbedding n scalar) =
      (((GeneralLinearGroup.det matrix : ℤˣ) : ℤ) : ℂ) •
        arithmeticLeviCoefficient n matrix (upperRadicalInvariantEmbedding n scalar) :=
    LinearMap.congr_fun (identityPlaneCoefficientRepT_section n χ hχ matrix)
      (upperRadicalInvariantEmbedding n scalar)
  rw [action, arithmeticLevi_upperInvariant, ← map_smul (upperRadicalInvariantEmbedding n),
    smul_eq_mul, ← mul_assoc, character, one_mul]

/-- **The twisted invariant isomorphism.**  The radical invariants of the twisted representation form
the trivial `GL₂(ℤ)`-module. -/
def identityPlaneInvariantIsoT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    arithmeticTrivialRep ≅
      splitInvariantRepresentation identityPlaneSplitting (identityPlaneCoefficientRepT n χ) :=
  Rep.mkIso (Representation.Equiv.mk (identityPlaneInvariantEquivT n χ) (by
    intro matrix
    apply LinearMap.ext
    intro scalar
    apply Subtype.ext
    exact (identityPlaneCoefficientRepT_section_embedding n χ hχ matrix scalar).symm))

/-- The induced isomorphism on second `GL₂(ℤ)`-cohomology. -/
def identityPlaneInvariantH2IsoT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    groupCohomology.H2 arithmeticTrivialRep ≅
      groupCohomology.H2
        (splitInvariantRepresentation identityPlaneSplitting (identityPlaneCoefficientRepT n χ)) :=
  (groupCohomology.functor ℂ (GeneralLinearGroup (Fin 2) ℤ) 2).mapIso
    (identityPlaneInvariantIsoT n χ hχ)

end TernaryPeriodPolynomials.Twisted
