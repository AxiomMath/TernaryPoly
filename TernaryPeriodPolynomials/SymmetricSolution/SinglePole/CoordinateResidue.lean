module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.CoordinateRestriction

@[expose] public section


open MvPolynomial
open scoped DirectSum
noncomputable section
namespace TernaryPoly.SinglePoleCoordinate
open SinglePole OrdinaryResidueSupport
attribute [local instance] Classical.propDecidable

/-- Restriction divided by the actual chosen normal scalar, giving the literal 1/X_i coefficient. -/
def scaledRestriction (n : ℕ) (i : Fin 3) : V (n+1) →ₗ[ℚ] BinaryV (n+1) :=
  (axisScale i)⁻¹ • homogeneousRestrict (n+1) i

theorem scaledRestriction_eq_zero_iff (n : ℕ) (i : Fin 3) (p : V (n+1)) :
    scaledRestriction n i p = 0 ↔ denominator (axis i) ∣ p.val := by
  change (axisScale i)⁻¹ • homogeneousRestrict (n+1) i p = 0 ↔ _
  constructor
  · intro h
    have hr := (smul_eq_zero.mp h).resolve_left (inv_ne_zero (axisScale_ne_zero i))
    apply (denominator_axis_dvd_iff i p.val).mpr
    apply (restrict_zero_iff i p.val).mp
    exact congrArg Subtype.val hr
  · intro h
    have hr : homogeneousRestrict (n+1) i p = 0 :=
      Subtype.ext ((restrict_zero_iff i p.val).mpr ((denominator_axis_dvd_iff i p.val).mp h))
    rw [hr,smul_zero]

/-- The literal coordinate map on the actual principal-part quotient fiber. -/
def literalFiberMap (n : ℕ) (i : Fin 3) : ResidueFiber n (axis i) →ₗ[ℚ] BinaryV (n+1) :=
  (numeratorRelations n (axis i)).liftQ (scaledRestriction n i) (by
    intro p hp
    apply (scaledRestriction_eq_zero_iff n i p).mpr
    apply (residueFiber_eq_zero_iff n (axis i) p).mp
    change Submodule.Quotient.mk p = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hp)

@[simp] theorem literalFiberMap_mk (n : ℕ) (i : Fin 3) (p : V (n+1)) :
    literalFiberMap n i ((numeratorRelations n (axis i)).mkQ p) = scaledRestriction n i p := rfl

/-- The canonical numerator cancels the chosen-normal scalar, exactly. -/
theorem scaledRestriction_scaledLift (n : ℕ) (i : Fin 3) (q : BinaryV (n+1)) :
    scaledRestriction n i (axisScale i • homogeneousLift (n+1) i q) = q := by
  change (axisScale i)⁻¹ • homogeneousRestrict (n+1) i
    (axisScale i • homogeneousLift (n+1) i q) = q
  rw [map_smul,homogeneousRestrict_lift,smul_smul,inv_mul_cancel₀ (axisScale_ne_zero i),one_smul]

theorem literalFiberMap_surjective (n : ℕ) (i : Fin 3) : Function.Surjective (literalFiberMap n i) := by
  intro q
  refine ⟨(numeratorRelations n (axis i)).mkQ (axisScale i • homogeneousLift (n+1) i q),?_⟩
  rw [literalFiberMap_mk,scaledRestriction_scaledLift]

theorem literalFiberMap_injective (n : ℕ) (i : Fin 3) : Function.Injective (literalFiberMap n i) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  change z = 0
  obtain ⟨p,rfl⟩ := (numeratorRelations n (axis i)).mkQ_surjective z
  change literalFiberMap n i ((numeratorRelations n (axis i)).mkQ p) = 0 at hz
  rw [literalFiberMap_mk] at hz
  exact (residueFiber_eq_zero_iff n (axis i) p).mpr ((scaledRestriction_eq_zero_iff n i p).mp hz)

/-- Every coordinate fiber is canonically identified with the literal homogeneous binary numerator. -/
def literalFiberEquiv (n : ℕ) (i : Fin 3) : ResidueFiber n (axis i) ≃ₗ[ℚ] BinaryV (n+1) :=
  LinearEquiv.ofBijective (literalFiberMap n i)
    ⟨literalFiberMap_injective n i,literalFiberMap_surjective n i⟩

@[simp] theorem literalFiberEquiv_apply (n : ℕ) (i : Fin 3) (z : ResidueFiber n (axis i)) :
    literalFiberEquiv n i z = literalFiberMap n i z := rfl

/-- Literal coefficient of 1/X_i in an actual single-pole rational function. -/
def coordinateResidue (n : ℕ) (i : Fin 3) : singlePole n →ₗ[ℚ] BinaryV (n+1) :=
  (literalFiberMap n i).comp ((SinglePoleSupport.component n (axis i)).comp (residue n))

@[simp] theorem coordinateResidue_apply (n : ℕ) (i : Fin 3) (x : singlePole n) :
    coordinateResidue n i x = literalFiberMap n i (residue n x (axis i)) := rfl

/-- The literal binary numerators of the three coordinate principal parts. -/
def coordinateTuple (n : ℕ) (r : Residues n) (i : Fin 3) : BinaryV (n+1) :=
  literalFiberMap n i (r (axis i))

/-- The actual rational fraction q/(X_i), with the complementary variables ordered literally. -/
def coordinatePole (n : ℕ) (i : Fin 3) (q : BinaryV (n+1)) : singlePole n :=
  simplePole n (axis i) (axisScale i • homogeneousLift (n+1) i q)

@[simp] theorem coordinatePole_val (n : ℕ) (i : Fin 3) (q : BinaryV (n+1)) :
    (coordinatePole n i q).val = embed (lift i q.val) / embed (X i) := by
  simp only [coordinatePole,simplePole_val,fractionMap_apply,SetLike.val_smul]
  rw [denominator_axis,divide_scaled_form,smul_smul,inv_mul_cancel₀ (axisScale_ne_zero i),one_smul]
  rfl

/-- Canonical coordinate fractions have precisely their literal numerator as principal coefficient. -/
@[simp] theorem coordinateResidue_coordinatePole (n : ℕ) (i : Fin 3) (q : BinaryV (n+1)) :
    coordinateResidue n i (coordinatePole n i q) = q := by
  rw [coordinateResidue_apply,coordinatePole,residue_simplePole]
  rw [DirectSum.lof_apply,literalFiberMap_mk,scaledRestriction_scaledLift]

/-- Terms with a different actual normal denominator have no residue at the selected coordinate. -/
theorem coordinateResidue_simplePole_ne (n : ℕ) (i : Fin 3) (H : SinglePole.Normal)
    (h : axis i ≠ H) (p : V (n+1)) : coordinateResidue n i (simplePole n H p) = 0 := by
  rw [coordinateResidue_apply,residue_simplePole]
  have he : (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) H
      ((numeratorRelations n H).mkQ p)) (axis i) = 0 := DirectSum.of_eq_of_ne H _ _ h
  rw [he,map_zero]

theorem coordinateResidue_coordinatePole_ne (n : ℕ) (i j : Fin 3) (h : i ≠ j)
    (q : BinaryV (n+1)) : coordinateResidue n i (coordinatePole n j q) = 0 :=
  coordinateResidue_simplePole_ne n i (axis j) (axis_injective.ne h) _

/-- Original homogeneous polynomials have zero literal coordinate residue. -/
@[simp] theorem coordinateResidue_polynomial (n : ℕ) (i : Fin 3) (p : V n) :
    coordinateResidue n i (polynomialInclusion n p) = 0 := by
  rw [coordinateResidue_apply,residue_polynomial]
  exact map_zero _

/-- Explicit a=0 coordinate: q(b,c)/a has residue exactly q(b,c). -/
theorem residue_a_canonical (n : ℕ) (q : BinaryV (n+1)) :
    (coordinatePole n 0 q).val = embed (rename (![1,2] : Fin 2 → Fin 3) q.val) / embed (X 0) ∧
    coordinateResidue n 0 (coordinatePole n 0 q) = q :=
  ⟨coordinatePole_val n 0 q,coordinateResidue_coordinatePole n 0 q⟩

end TernaryPoly.SinglePoleCoordinate
