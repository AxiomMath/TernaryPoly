module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.CoordinateActions

@[expose] public section


open scoped DirectSum
noncomputable section
namespace TernaryPoly.SinglePoleCoordinate
open SinglePole OrdinaryResidueSupport SinglePoleSupport PolynomialGLAction
attribute [local instance] Classical.propDecidable

/-- An actual rational function with exactly the requested three coordinate principal parts. -/
def reconstruct (n : ℕ) (r : Residues n) : singlePole n :=
  ∑ i : Fin 3, coordinatePole n i (coordinateTuple n r i)

@[simp] theorem coordinateResidue_reconstruct (n : ℕ) (r : Residues n) (i : Fin 3) :
    coordinateResidue n i (reconstruct n r) = coordinateTuple n r i := by
  rw [reconstruct,map_sum]
  rw [Finset.sum_eq_single i]
  · exact coordinateResidue_coordinatePole n i _
  · intro j _ hji
    exact coordinateResidue_coordinatePole_ne n i j (Ne.symm hji) _
  · simp

/-- Coordinate-supported actual principal parts are recovered by actual canonical simple fractions. -/
theorem residue_reconstruct (n : ℕ) (r : Residues n)
    (hr : ∀ H, ¬Coordinate H → r H = 0) : residue n (reconstruct n r) = r := by
  apply DFinsupp.ext
  intro H
  by_cases hc : Coordinate H
  · obtain ⟨i,rfl⟩ := hc
    apply literalFiberMap_injective n i
    exact coordinateResidue_reconstruct n r i
  · rw [hr H hc]
    change SinglePoleSupport.component n H (residue n (reconstruct n r)) = 0
    rw [reconstruct,map_sum,map_sum]
    apply Finset.sum_eq_zero
    intro i _
    change (residue n (simplePole n (axis i)
      (axisScale i • homogeneousLift (n+1) i (coordinateTuple n r i)))) H = 0
    rw [residue_simplePole]
    exact DirectSum.of_eq_of_ne _ _ _ (fun he => hc ⟨i,he⟩)

/-- Explicit rational-function formula; all three numerators are literal coordinate restrictions. -/
theorem reconstruct_val (n : ℕ) (r : Residues n) :
    (reconstruct n r).val =
      embed (lift 0 (coordinateTuple n r 0).val) / embed (MvPolynomial.X 0) +
      embed (lift 1 (coordinateTuple n r 1).val) / embed (MvPolynomial.X 1) +
      embed (lift 2 (coordinateTuple n r 2).val) / embed (MvPolynomial.X 2) := by
  simp only [reconstruct,Fin.sum_univ_three,Submodule.coe_add,coordinatePole_val]

/-- In particular, actual symmetric separately odd norm residues admit the literal reconstruction. -/
theorem residue_reconstruct_of_norm (n : ℕ) (e : ℤ) (r : Residues n)
    (hsym : SinglePoleSupport.SymmetricResidue n e r)
    (hodd : SinglePoleSupport.SeparatelyOddResidue n e r)
    (hnorm : r + SinglePoleSupport.integralResidueAction n e ReferenceCoefficientMatrices.a r +
      SinglePoleSupport.integralResidueAction n e (ReferenceCoefficientMatrices.a^2) r = 0) :
    residue n (reconstruct n r) = r :=
  residue_reconstruct n r (SinglePoleSupport.residue_coordinate_support n e r hsym hodd hnorm)

/-- Symmetry identifies all three literal coordinate numerators, without chosen-normal sign assumptions. -/
theorem coordinateTuple_eq_of_symmetric (n : ℕ) (e : ℤ) (r : Residues n)
    (hr : SymmetricResidue n e r) (i : Fin 3) : coordinateTuple n r i = coordinateTuple n r 0 := by
  have he := coordinateTuple_action n e (permutationMatrix (toAxisPermutation i)) 0 i r
    (coordinateTuple n r 0) (toAxisPermutation_source i)
    (toAxisPermutation_lift i (coordinateTuple n r 0).val) (by
      rw [substitute_permutation,MvPolynomial.rename_X,toAxisPermutation_zero])
  rw [hr,coordinateTuple_smul] at he
  exact smul_right_injective (BinaryV (n+1)) (determinantCharacter_ne_zero e _) he

/-- The a-coordinate binary numerator inherits literal interchange of b and c. -/
theorem coordinateTuple_swap (n : ℕ) (e : ℤ) (r : Residues n) (hr : SymmetricResidue n e r) :
    binarySwap (n+1) (coordinateTuple n r 0) = coordinateTuple n r 0 := by
  have he := coordinateTuple_action n e (permutationMatrix (Equiv.swap 1 2)) 0 0 r
    (binarySwap (n+1) (coordinateTuple n r 0))
    (by rw [rowAction_permutation_axis]; rfl)
    (swap12_lift (n+1) (coordinateTuple n r 0))
    (by rw [substitute_permutation,MvPolynomial.rename_X]; rfl)
  rw [hr,coordinateTuple_smul] at he
  exact (smul_right_injective (BinaryV (n+1)) (determinantCharacter_ne_zero e _) he).symm

/-- Literal separate oddness passes to the first binary variable b. -/
theorem coordinateTuple_odd_first (n : ℕ) (e : ℤ) (r : Residues n) (hr : SeparatelyOddResidue n e r) :
    binaryNegFirst (n+1) (coordinateTuple n r 0) = -coordinateTuple n r 0 := by
  have he := coordinateTuple_action n e (signMatrix firstBinarySign) 0 0 r
    (binaryNegFirst (n+1) (coordinateTuple n r 0)) (rowAction_sign_axis firstBinarySign 0)
    (firstBinarySign_lift (n+1) (coordinateTuple n r 0))
    (by rw [substitute_sign,MvPolynomial.bind₁_X_right]; rfl)
  rw [hr,coordinateTuple_smul,oddSign_firstBinarySign,mul_smul,neg_one_smul] at he
  exact (smul_right_injective (BinaryV (n+1)) (determinantCharacter_ne_zero e _) he).symm

/-- Literal separate oddness passes to the second binary variable c. -/
theorem coordinateTuple_odd_second (n : ℕ) (e : ℤ) (r : Residues n) (hr : SeparatelyOddResidue n e r) :
    binaryNegSecond (n+1) (coordinateTuple n r 0) = -coordinateTuple n r 0 := by
  have he := coordinateTuple_action n e (signMatrix secondBinarySign) 0 0 r
    (binaryNegSecond (n+1) (coordinateTuple n r 0)) (rowAction_sign_axis secondBinarySign 0)
    (secondBinarySign_lift (n+1) (coordinateTuple n r 0))
    (by rw [substitute_sign,MvPolynomial.bind₁_X_right]; rfl)
  rw [hr,coordinateTuple_smul,oddSign_secondBinarySign,mul_smul,neg_one_smul] at he
  exact (smul_right_injective (BinaryV (n+1)) (determinantCharacter_ne_zero e _) he).symm

/-- The exact common-numerator rational representative q(b,c)/a+q(a,c)/b+q(a,b)/c. -/
def canonicalRepresentative (n : ℕ) (q : BinaryV (n+1)) : singlePole n :=
  coordinatePole n 0 q + coordinatePole n 1 q + coordinatePole n 2 q

theorem canonicalRepresentative_val (n : ℕ) (q : BinaryV (n+1)) :
    (canonicalRepresentative n q).val =
      embed (MvPolynomial.rename (![1,2] : Fin 2 → Fin 3) q.val) / embed (MvPolynomial.X 0) +
      embed (MvPolynomial.rename (![0,2] : Fin 2 → Fin 3) q.val) / embed (MvPolynomial.X 1) +
      embed (MvPolynomial.rename (![0,1] : Fin 2 → Fin 3) q.val) / embed (MvPolynomial.X 2) := by
  simp only [canonicalRepresentative,Submodule.coe_add,coordinatePole_val]
  rfl

theorem reconstruct_eq_canonical (n : ℕ) (e : ℤ) (r : Residues n) (hr : SymmetricResidue n e r) :
    reconstruct n r = canonicalRepresentative n (coordinateTuple n r 0) := by
  rw [reconstruct,Fin.sum_univ_three]
  rw [coordinateTuple_eq_of_symmetric n e r hr 1,coordinateTuple_eq_of_symmetric n e r hr 2]
  rfl

/-- Every actual symmetric separately odd coordinate residue has the exact common binary representative.
The binary period/norm relation is deliberately a separate obligation. -/
theorem exists_canonical_representative (n : ℕ) (e : ℤ) (r : Residues n)
    (hsym : SymmetricResidue n e r) (hodd : SeparatelyOddResidue n e r)
    (hcoord : ∀ H, ¬Coordinate H → r H = 0) :
    ∃ q : BinaryV (n+1),
      MvPolynomial.bind₁ ![MvPolynomial.X 1,MvPolynomial.X 0] q.val = q.val ∧
      MvPolynomial.bind₁ ![-MvPolynomial.X 0,MvPolynomial.X 1] q.val = -q.val ∧
      MvPolynomial.bind₁ ![MvPolynomial.X 0,-MvPolynomial.X 1] q.val = -q.val ∧
      residue n (canonicalRepresentative n q) = r := by
  refine ⟨coordinateTuple n r 0,?_,?_,?_,?_⟩
  · exact congrArg Subtype.val (coordinateTuple_swap n e r hsym)
  · exact congrArg Subtype.val (coordinateTuple_odd_first n e r hodd)
  · exact congrArg Subtype.val (coordinateTuple_odd_second n e r hodd)
  · rw [← reconstruct_eq_canonical n e r hsym]
    exact residue_reconstruct n r hcoord

end TernaryPoly.SinglePoleCoordinate
