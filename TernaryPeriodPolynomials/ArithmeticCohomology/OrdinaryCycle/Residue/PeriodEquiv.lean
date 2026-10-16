module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.PeriodSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.PeriodCanonical
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.LiftableResidueObstruction

@[expose] public section


open scoped DirectSum
noncomputable section
namespace TernaryPoly.OrdinaryResiduePeriod
open SinglePole SinglePoleCoordinate SinglePoleSupport OrdinaryFullCoefficient
open OrdinaryResidueSupport OrdinaryResidueGeneral

/-- The canonical principal parts depend linearly on their common literal binary numerator. -/
def canonicalMap (n : ℕ) : BinaryV (n+1) →ₗ[ℚ] Residues n :=
  ∑ i : Fin 3, (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) (axis i)).comp
    (((numeratorRelations n (axis i)).mkQ).comp (axisScale i • homogeneousLift (n+1) i))

@[simp] theorem canonicalMap_apply (n : ℕ) (q : BinaryV (n+1)) :
    canonicalMap n q = residue n (canonicalRepresentative n q) := by
  simp only [canonicalMap,Fin.sum_univ_three,LinearMap.add_apply,LinearMap.comp_apply,
    LinearMap.smul_apply,canonicalRepresentative,map_add,coordinatePole,residue_simplePole]

theorem symmetric_of_relations (n : ℕ) (r : Residues n)
    (hr : Relations (residueAction n (-1)) r) : SymmetricResidue n (-1) r :=
  symmetry_of_relations _ r hr

theorem odd_of_relations (n : ℕ) (r : Residues n)
    (hr : Relations (residueAction n (-1)) r) : SeparatelyOddResidue n (-1) r :=
  (separatelyOddResidue_neg_one_iff n r).mpr (sign_invariant_of_relations _ r hr)

/-- Full apartment equations force actual canonical coordinate reconstruction. -/
theorem canonical_recovery (n : ℕ) (r : Residues n)
    (hr : Relations (residueAction n (-1)) r) :
    canonicalMap n (coordinateTuple n r 0) = r := by
  rw [canonicalMap_apply,←reconstruct_eq_canonical n (-1) r (symmetric_of_relations n r hr)]
  exact residue_reconstruct_of_norm n (-1) r
    (symmetric_of_relations n r hr) (odd_of_relations n r hr) hr.norm

/-- The common literal numerator inherits all three symmetry equations from actual full residue relations. -/
theorem coordinate_symmetricOdd (n : ℕ) (r : Residues n)
    (hr : Relations (residueAction n (-1)) r) :
    OrdinaryResidueGeneral.SymmetricOdd (coordinateTuple n r 0).val := by
  constructor
  · exact congrArg Subtype.val (coordinateTuple_swap n (-1) r (symmetric_of_relations n r hr))
  · exact congrArg Subtype.val (coordinateTuple_odd_first n (-1) r (odd_of_relations n r hr))
  · exact congrArg Subtype.val (coordinateTuple_odd_second n (-1) r (odd_of_relations n r hr))

/-- The full binary period relation follows from actual residue norm zero, independently of liftability. -/
theorem coordinate_period (n : ℕ) (r : Residues n)
    (hr : Relations (residueAction n (-1)) r) :
    SymmetricBinaryPeriodRelations (coordinateTuple n r 0).val := by
  apply (canonical_residue_norm_iff n _ (coordinate_symmetricOdd n r hr)).mp
  rw [residue_norm,←canonicalMap_apply,canonical_recovery n r hr]
  exact hr.norm

/-- The existing literal reference-coordinate map lands in the homogeneous binary period subspace. -/
theorem coordinatePeriod_mem (n : ℕ) (F : ResidueHom n (-1)) :
    coordinatePeriod n 0 F ∈ periodSpace (n+1) :=
  coordinate_period n (reference (residueAction n (-1)) F) (hom_relations _ F)

/-- The actual coordinate map, with its proved period-space codomain. -/
def coordinateMap (n : ℕ) : ResidueHom n (-1) →ₗ[ℚ] periodSpace (n+1) :=
  (coordinatePeriod n 0).codRestrict _ (coordinatePeriod_mem n)

/-- A binary period gives a genuine full-level residue functional through its canonical actual residue. -/
def inverseFun (n : ℕ) (q : periodSpace (n+1)) : ResidueHom n (-1) := by
  have hr : Relations (residueAction n (-1)) (canonicalMap n q.val) := by
    rw [canonicalMap_apply]
    exact canonical_relations n q.val q.property
  exact ⟨functional _ (canonicalMap n q.val) hr,functional_equivariant _ _ hr⟩

@[simp] theorem inverseFun_reference (n : ℕ) (q : periodSpace (n+1)) :
    reference (residueAction n (-1)) (inverseFun n q) = canonicalMap n q.val :=
  functional_reference _ _ _

/-- Linearity of the inverse follows from actual reference injectivity, not a chosen presentation. -/
def inverseMap (n : ℕ) : periodSpace (n+1) →ₗ[ℚ] ResidueHom n (-1) where
  toFun := inverseFun n
  map_add' p q := by
    apply reference_injective (residueAction n (-1))
    change reference (residueAction n (-1)) (inverseFun n (p+q)) =
      reference (residueAction n (-1)) (inverseFun n p + inverseFun n q)
    rw [map_add,inverseFun_reference,inverseFun_reference,inverseFun_reference]
    exact (canonicalMap n).map_add p.val q.val
  map_smul' c q := by
    apply reference_injective (residueAction n (-1))
    change reference (residueAction n (-1)) (inverseFun n (c • q)) =
      reference (residueAction n (-1)) (c • inverseFun n q)
    rw [map_smul,inverseFun_reference,inverseFun_reference]
    exact (canonicalMap n).map_smul c q.val

@[simp] theorem coordinate_inverse (n : ℕ) (q : periodSpace (n+1)) :
    coordinateMap n (inverseMap n q) = q := by
  apply Subtype.ext
  change SinglePoleCoordinate.literalFiberMap n 0
    ((reference (residueAction n (-1)) (inverseFun n q)) (axis 0)) = q.val
  rw [inverseFun_reference,canonicalMap_apply]
  exact canonical_coordinateResidue n q.val 0

@[simp] theorem inverse_coordinate (n : ℕ) (F : ResidueHom n (-1)) :
    inverseMap n (coordinateMap n F) = F := by
  apply reference_injective (residueAction n (-1))
  change reference (residueAction n (-1)) (inverseFun n (coordinateMap n F)) =
    reference (residueAction n (-1)) F
  rw [inverseFun_reference]
  exact canonical_recovery n _ (hom_relations _ F)

/-- The literal binary coordinate is a linear equivalence between actual full residue functionals and binary periods. -/
def periodEquiv (n : ℕ) : ResidueHom n (-1) ≃ₗ[ℚ] periodSpace (n+1) where
  toFun := coordinateMap n
  invFun := inverseMap n
  left_inv := inverse_coordinate n
  right_inv := coordinate_inverse n
  map_add' := (coordinateMap n).map_add
  map_smul' := (coordinateMap n).map_smul

@[simp] theorem periodEquiv_val (n : ℕ) (F : ResidueHom n (-1)) :
    (periodEquiv n F).val = coordinatePeriod n 0 F := rfl

@[simp] theorem periodEquiv_symm_reference (n : ℕ) (q : periodSpace (n+1)) :
    reference (residueAction n (-1)) ((periodEquiv n).symm q) = canonicalMap n q.val :=
  inverseFun_reference n q

end TernaryPoly.OrdinaryResiduePeriod
