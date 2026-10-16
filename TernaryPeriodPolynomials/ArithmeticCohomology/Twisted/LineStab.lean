module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Levi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LowerRadicalEdgeFormula

@[expose] public section


/-!
# The good-line stabilizer with sign-twisted coefficients

For a rank-one character `χ` with `χ(-1_∞) = -1`, the coefficient representation of the good-line
stabilizer `Λ₁ ⋊ GL₂(ℤ)` (lower radical `Λ₁`, Levi `diag(m, 1)`) is
`goodLineCoefficientRepT n χ`.  Its restriction to the lower radical is the untwisted lattice
representation `lowerRadicalLatticeRep n` (identity map, `lowerRadicalIsoT`), while the Levi section
acts by `det m • arithmeticLeviCoefficient n m`.  Consequently the Levi action on the radical
cohomology `H¹(Λ₁, V)` is `det m` times the untwisted one, the binary coordinate of the radical
cohomology intertwines it with `Sym^{n+1} ⊗ det⁻¹` (`goodLineRadicalCoordinateIsoT`), and the split
Hochschild-Serre edge of the good-line stabilizer lands in `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det)`
(`goodLineBinaryEdgeT`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

/-- The integral determinant of an arithmetic Levi matrix, seen over `ℂ`, is the determinant of its
complex image. -/
theorem goodLineDetMapT (m : GeneralLinearGroup (Fin 2) ℤ) :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) m) : ℂˣ) : ℂ) =
      (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) := by
  rw [GeneralLinearGroup.map_det]
  rfl

/-- Lowering the determinant twist divides by the determinant. -/
theorem goodLineHomogeneousAction_zeroT (d : ℕ) (A : Binary.GL2) :
    Binary.homogeneousAction d 0 A =
      (((GeneralLinearGroup.det A : ℂˣ) : ℂ))⁻¹ • Binary.homogeneousAction d 1 A := by
  have twist := homogeneousAction_succ_twist d 0 A
  rw [zero_add] at twist
  rw [twist, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]

/-- The coefficient representation of the good-line stabilizer for the character `χ`. -/
def goodLineCoefficientRepT (n : ℕ) (χ : RankOneCharacter) :
    Rep ℂ (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) :=
  Rep.of ((rationalCoefficientComponent n χ).comp
    (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)).subtype)

/-- The twisted coefficients restricted to the lower radical. -/
def lowerRadicalRepT (n : ℕ) (χ : RankOneCharacter) : Rep ℂ RadicalLattice :=
  Rep.of ((rationalCoefficientComponent n χ).comp lowerRadicalLattice)

/-- The restriction of `goodLineCoefficientRepT` to the lower radical. -/
abbrev goodLineRadicalRepT (n : ℕ) (χ : RankOneCharacter) : Rep ℂ RadicalLattice :=
  Rep.res goodLineRadicalInclusion (goodLineCoefficientRepT n χ)

theorem goodLineRadicalRepT_def (n : ℕ) (χ : RankOneCharacter) :
    goodLineRadicalRepT n χ = lowerRadicalRepT n χ := rfl

/-- The twisted and untwisted lattice representations of the lower radical are identified by the
identity map, since the radical has positive determinant. -/
def lowerRadicalIsoT (n : ℕ) (χ : RankOneCharacter) : lowerRadicalRepT n χ ≅ lowerRadicalLatticeRep n :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ (HomogeneousPoly n)) (by
    intro element
    apply LinearMap.ext
    intro vector
    change rationalCoefficientComponent n χ (lowerRadicalLattice element) vector =
      rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice element) vector
    rw [rho_lowerRadicalLattice n χ element]))

theorem lowerRadicalRepT_eq (n : ℕ) (χ : RankOneCharacter) :
    lowerRadicalRepT n χ = lowerRadicalLatticeRep n := by
  have equality : (rationalCoefficientComponent n χ).comp lowerRadicalLattice =
      (rationalCoefficientComponent n trivialCharacter).comp lowerRadicalLattice :=
    MonoidHom.ext fun element => rho_lowerRadicalLattice n χ element
  exact congrArg Rep.of equality

/-- **The restriction of the twisted stabilizer representation to the lower radical is the untwisted
lattice representation.** -/
theorem goodLineCoefficientRepT_radical (n : ℕ) (χ : RankOneCharacter) :
    Rep.res goodLineRadicalInclusion (goodLineCoefficientRepT n χ) = lowerRadicalLatticeRep n :=
  (goodLineRadicalRepT_def n χ).trans (lowerRadicalRepT_eq n χ)

/-- The twisted representation on the Levi section. -/
theorem goodLineCoefficientRepT_section (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (m : GeneralLinearGroup (Fin 2) ℤ) :
    (goodLineCoefficientRepT n χ).ρ (goodLineLeviSection m) =
      (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) • arithmeticLeviCoefficient n m :=
  rho_arithmeticLevi_odd n hχ m

/-! ### Transport of radical cocycles to the untwisted lattice representation -/

/-- The identity morphism from the twisted to the untwisted lower-radical representation. -/
def lowerRadicalHomT (n : ℕ) (χ : RankOneCharacter) :
    Rep.res (MonoidHom.id RadicalLattice) (lowerRadicalRepT n χ) ⟶ lowerRadicalLatticeRep n :=
  (lowerRadicalIsoT n χ).hom

/-- Transport of one-cocycles of the twisted radical representation to the untwisted one. -/
def goodLineCocycleCastT (n : ℕ) (χ : RankOneCharacter) :
    groupCohomology.cocycles₁ (goodLineRadicalRepT n χ) →ₗ[ℂ]
      groupCohomology.cocycles₁ (lowerRadicalLatticeRep n) :=
  (groupCohomology.mapCocycles₁ (MonoidHom.id RadicalLattice) (lowerRadicalHomT n χ)).hom

theorem goodLineCocycleCastT_apply (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₁ (goodLineRadicalRepT n χ)) (element : RadicalLattice) :
    goodLineCocycleCastT n χ cycle element = cycle element := by
  have equality := groupCohomology.mapCocycles₁_comp_i_apply (MonoidHom.id RadicalLattice)
    (lowerRadicalHomT n χ) cycle
  exact congrFun equality element

/-- Transport of the radical cohomology. -/
def goodLineH1CastIsoT (n : ℕ) (χ : RankOneCharacter) :
    groupCohomology.H1 (goodLineRadicalRepT n χ) ≅ groupCohomology.H1 (lowerRadicalLatticeRep n) :=
  (groupCohomology.functor ℂ RadicalLattice 1).mapIso (lowerRadicalIsoT n χ)

theorem goodLineH1CastIsoT_apply (n : ℕ) (χ : RankOneCharacter)
    (cycle : groupCohomology.cocycles₁ (goodLineRadicalRepT n χ)) :
    (goodLineH1CastIsoT n χ).hom (groupCohomology.H1π (goodLineRadicalRepT n χ) cycle) =
      groupCohomology.H1π (lowerRadicalLatticeRep n) (goodLineCocycleCastT n χ cycle) :=
  groupCohomology.H1π_comp_map_apply (A := lowerRadicalRepT n χ) (B := lowerRadicalLatticeRep n)
    (MonoidHom.id RadicalLattice) (lowerRadicalHomT n χ) cycle

/-! ### The twisted Levi action on the radical cohomology -/

/-- The Levi action on `H¹(Λ₁, V)` induced by the twisted coefficients: `det m` times the untwisted
action `lowerRadicalH1Levi`. -/
def lowerRadicalH1LeviT (n : ℕ) (m : GeneralLinearGroup (Fin 2) ℤ) :
    Module.End ℂ (groupCohomology.H1 (lowerRadicalLatticeRep n)) :=
  (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) • lowerRadicalH1Levi n m

theorem lowerRadicalH1LeviT_apply (n : ℕ) (m : GeneralLinearGroup (Fin 2) ℤ)
    (cohomology : groupCohomology.H1 (lowerRadicalLatticeRep n)) :
    lowerRadicalH1LeviT n m cohomology =
      (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) • lowerRadicalH1Levi n m cohomology := rfl

/-- The determinant of an arithmetic Levi matrix squares to one. -/
theorem goodLineDetSqT (m : GeneralLinearGroup (Fin 2) ℤ) :
    (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) * (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (GeneralLinearGroup.det m) with determinant | determinant
  · rw [determinant]
    simp
  · rw [determinant]
    simp

/-- The binary coordinate of the radical cohomology intertwines the twisted Levi action with
`Sym^{n+1} ⊗ det^{-1}`, which on `GL₂(ℤ)` is the same module as `Sym^{n+1} ⊗ det`. -/
theorem lowerRadicalH1Coordinate_equivariantT {n : ℕ} (positive : 0 < n)
    (m : GeneralLinearGroup (Fin 2) ℤ) (cohomology : groupCohomology.H1 (lowerRadicalLatticeRep n)) :
    lowerRadicalH1Coordinate n positive (lowerRadicalH1LeviT n m cohomology) =
      Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) m)
        (lowerRadicalH1Coordinate n positive cohomology) := by
  have twist := homogeneousAction_succ_twist (n + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) m)
  rw [neg_add_cancel, goodLineDetMapT] at twist
  rw [lowerRadicalH1LeviT_apply, map_smul, lowerRadicalH1Coordinate_equivariant positive, twist,
    LinearMap.smul_apply, smul_smul, goodLineDetSqT, one_smul]

theorem goodLineCocycleCastT_splitAction (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (m : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (goodLineRadicalRepT n χ)) :
    goodLineCocycleCastT n χ
        (splitRadicalCocycleAction goodLineSplitting (goodLineCoefficientRepT n χ) m cycle) =
      (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) •
        lowerRadicalCocycleLevi n m (goodLineCocycleCastT n χ cycle) := by
  apply groupCohomology.cocycles₁_ext
  intro element
  have input : splitRadicalInput goodLineSplitting m element = lowerLeviLatticeInput m element :=
    goodLineSplitting_inverse_action m element
  have action : splitRadicalCocycleAction goodLineSplitting (goodLineCoefficientRepT n χ) m cycle element =
      (goodLineCoefficientRepT n χ).ρ (goodLineLeviSection m) (cycle (lowerLeviLatticeInput m element)) :=
    (splitRadicalCocycleAction_apply goodLineSplitting (goodLineCoefficientRepT n χ) m cycle element).trans
      (congrArg (fun radical : RadicalLattice =>
        (goodLineCoefficientRepT n χ).ρ (goodLineLeviSection m) (cycle radical)) input)
  have first : goodLineCocycleCastT n χ
        (splitRadicalCocycleAction goodLineSplitting (goodLineCoefficientRepT n χ) m cycle) element =
      (goodLineCoefficientRepT n χ).ρ (goodLineLeviSection m) (cycle (lowerLeviLatticeInput m element)) :=
    (goodLineCocycleCastT_apply n χ _ element).trans action
  have second : lowerRadicalCocycleLevi n m (goodLineCocycleCastT n χ cycle) element =
      arithmeticLeviCoefficient n m (cycle (lowerLeviLatticeInput m element)) :=
    (lowerRadicalCocycleLevi_apply n m (goodLineCocycleCastT n χ cycle) element).trans
      (congrArg (fun vector => arithmeticLeviCoefficient n m vector)
        (goodLineCocycleCastT_apply n χ cycle (lowerLeviLatticeInput m element)))
  change goodLineCocycleCastT n χ
      (splitRadicalCocycleAction goodLineSplitting (goodLineCoefficientRepT n χ) m cycle) element =
    (((GeneralLinearGroup.det m : ℤˣ) : ℤ) : ℂ) •
      (lowerRadicalCocycleLevi n m (goodLineCocycleCastT n χ cycle) element)
  rw [first, second]
  exact LinearMap.congr_fun (goodLineCoefficientRepT_section n χ hχ m) (cycle (lowerLeviLatticeInput m element))

theorem goodLineSplitH1ActionT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (m : GeneralLinearGroup (Fin 2) ℤ)
    (cohomology : groupCohomology.H1 (goodLineRadicalRepT n χ)) :
    (goodLineH1CastIsoT n χ).hom
        (splitRadicalH1Action goodLineSplitting (goodLineCoefficientRepT n χ) m cohomology) =
      lowerRadicalH1LeviT n m ((goodLineH1CastIsoT n χ).hom cohomology) := by
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (goodLineRadicalRepT n χ) cohomology
  have action : splitRadicalH1Action goodLineSplitting (goodLineCoefficientRepT n χ) m
        (groupCohomology.H1π (goodLineRadicalRepT n χ) cycle) =
      groupCohomology.H1π (goodLineRadicalRepT n χ)
        (splitRadicalCocycleAction goodLineSplitting (goodLineCoefficientRepT n χ) m cycle) :=
    splitRadicalH1Action_apply goodLineSplitting (goodLineCoefficientRepT n χ) m cycle
  have transport : (goodLineH1CastIsoT n χ).hom
        (groupCohomology.H1π (goodLineRadicalRepT n χ)
          (splitRadicalCocycleAction goodLineSplitting (goodLineCoefficientRepT n χ) m cycle)) =
      groupCohomology.H1π (lowerRadicalLatticeRep n)
        (goodLineCocycleCastT n χ
          (splitRadicalCocycleAction goodLineSplitting (goodLineCoefficientRepT n χ) m cycle)) :=
    goodLineH1CastIsoT_apply n χ _
  rw [action, transport, goodLineH1CastIsoT_apply, lowerRadicalH1LeviT_apply,
    lowerRadicalH1Levi_apply, goodLineCocycleCastT_splitAction n χ hχ, map_smul]

/-! ### The binary coordinate of the radical cohomology -/

/-- Binary coordinates on the radical cohomology of the twisted stabilizer. -/
def goodLineRadicalEquivT (n : ℕ) (χ : RankOneCharacter) (positive : 0 < n) :
    groupCohomology.H1 (goodLineRadicalRepT n χ) ≃ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (LinearEquiv.ofBijective (goodLineH1CastIsoT n χ).hom.hom
    (ConcreteCategory.bijective_of_isIso (goodLineH1CastIsoT n χ).hom)).trans
    (lowerRadicalH1Coordinate n positive)

theorem goodLineRadicalEquivT_apply (n : ℕ) (χ : RankOneCharacter) (positive : 0 < n)
    (cohomology : groupCohomology.H1 (goodLineRadicalRepT n χ)) :
    goodLineRadicalEquivT n χ positive cohomology =
      lowerRadicalH1Coordinate n positive ((goodLineH1CastIsoT n χ).hom cohomology) := rfl

/-- The radical cohomology of the twisted good-line stabilizer is `Sym^{n+1} ⊗ det⁻¹` as a
representation of the Levi quotient `GL₂(ℤ)` (the same module as `Sym^{n+1} ⊗ det`). -/
def goodLineRadicalCoordinateIsoT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) :
    splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRepT n χ) ≅
      arithmeticBinaryRep (n + 1) (-1) :=
  Rep.mkIso (Representation.Equiv.mk (goodLineRadicalEquivT n χ positive) (by
    intro matrix
    apply LinearMap.ext
    intro cohomology
    change groupCohomology.H1 (goodLineRadicalRepT n χ) at cohomology
    change goodLineRadicalEquivT n χ positive
        (splitRadicalH1Action goodLineSplitting (goodLineCoefficientRepT n χ) matrix cohomology) =
      Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (goodLineRadicalEquivT n χ positive cohomology)
    have transport : goodLineRadicalEquivT n χ positive
          (splitRadicalH1Action goodLineSplitting (goodLineCoefficientRepT n χ) matrix cohomology) =
        lowerRadicalH1Coordinate n positive ((goodLineH1CastIsoT n χ).hom
          (splitRadicalH1Action goodLineSplitting (goodLineCoefficientRepT n χ) matrix cohomology)) :=
      goodLineRadicalEquivT_apply n χ positive _
    rw [transport, goodLineRadicalEquivT_apply, goodLineSplitH1ActionT n χ hχ,
      lowerRadicalH1Coordinate_equivariantT positive]))

def goodLineLeviCohomologyIsoT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) :
    groupCohomology.H1 (splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRepT n χ)) ≅
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) :=
  (groupCohomology.functor ℂ (GeneralLinearGroup (Fin 2) ℤ) 1).mapIso
    (goodLineRadicalCoordinateIsoT n χ hχ positive)

/-- The target stabilizer edge for the sign-twisted coefficients, with binary target
`Sym^{n+1} ⊗ det⁻¹`. -/
def goodLineBinaryEdgeT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) :
    (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRepT n χ)).ker →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) :=
  (goodLineLeviCohomologyIsoT n χ hχ positive).hom.hom.comp
    (splitCohomologyEdge goodLineSplitting (goodLineCoefficientRepT n χ))

theorem goodLineBinaryEdge_applyT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ)) :
    goodLineBinaryEdgeT n χ hχ positive
        (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRepT n χ) cycle) =
      (goodLineLeviCohomologyIsoT n χ hχ positive).hom
        (groupCohomology.H1π (splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRepT n χ))
          (splitCocycleEdge goodLineSplitting (goodLineCoefficientRepT n χ) cycle)) := by
  exact congrArg (fun cohomology => (goodLineLeviCohomologyIsoT n χ hχ positive).hom cohomology)
    (splitCohomologyEdge_apply goodLineSplitting (goodLineCoefficientRepT n χ) cycle)

end TernaryPeriodPolynomials.Twisted
