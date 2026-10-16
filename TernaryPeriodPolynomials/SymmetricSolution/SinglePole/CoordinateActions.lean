module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.CoordinateResidue

@[expose] public section


open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.SinglePoleCoordinate
open SinglePole SinglePoleSupport PolynomialGLAction OrdinaryResidueSupport ModThreeGoodAction
attribute [local instance] Classical.propDecidable

/-- Literal inverse substitution by the chosen permutation matrix permutes the variables by π. -/
theorem substitute_permutation (π : Equiv.Perm (Fin 3)) :
    substitute ((integralRational (permutationMatrix π))⁻¹ : GL3) = rename π := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [substitute_X,rename_X]
  change linearForm ((π.permMatrix ℤ).map (Int.castRingHom ℚ)) i = X (π i)
  simp [linearForm,Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply]

/-- Literal inverse substitution by a coordinate-sign matrix. -/
theorem substitute_sign (s : Fin 3 → Bool) :
    substitute ((integralRational (signMatrix s))⁻¹ : GL3) =
      bind₁ (fun i => if s i then -X i else X i) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [substitute_X,bind₁_X_right]
  change linearForm ((diagonal (signEntry s)).map (Int.castRingHom ℚ)) i = _
  cases hs : s i <;> simp [linearForm,diagonal_apply,signEntry,hs,apply_ite,ite_mul]

/-- Changing coordinates of a canonical pole is an equality of actual rational functions. -/
theorem action_coordinatePole (n : ℕ) (e : ℤ) (g : IntegralGL) (i j : Fin 3)
    (q q' : BinaryV (n+1))
    (hnum : substitute ((integralRational g)⁻¹ : GL3) (lift i q.val) = lift j q'.val)
    (hden : substitute ((integralRational g)⁻¹ : GL3) (X i) = X j) :
    integralSinglePoleAction n e g (coordinatePole n i q) =
      determinantCharacter e (integralRational g) • coordinatePole n j q' := by
  apply Subtype.ext
  change fractionAction e (integralRational g) (coordinatePole n i q).val =
    determinantCharacter e (integralRational g) • (coordinatePole n j q').val
  rw [coordinatePole_val,coordinatePole_val,fractionAction_apply,map_div₀,
    fractionEquiv_embed,fractionEquiv_embed,hnum,hden]

/-- Equal actual source components have equal actual transformed target components. -/
theorem component_action_congr (n : ℕ) (e : ℤ) (g : IntegralGL) (H : SinglePole.Normal)
    (r t : Residues n) (h : r (rowAction g H) = t (rowAction g H)) :
    (integralResidueAction n e g r) H = (integralResidueAction n e g t) H := by
  have hr := LinearMap.congr_fun (component_action_factor n e g H) r
  have ht := LinearMap.congr_fun (component_action_factor n e g H) t
  change (integralResidueAction n e g r) H =
    (integralResidueAction n e g
      (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) (rowAction g H) (r (rowAction g H)))) H at hr
  change (integralResidueAction n e g t) H =
    (integralResidueAction n e g
      (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) (rowAction g H) (t (rowAction g H)))) H at ht
  rw [hr,ht,h]

/-- Actual coordinate tuples transform by the literal substituted binary numerator. -/
theorem coordinateTuple_action (n : ℕ) (e : ℤ) (g : IntegralGL) (i j : Fin 3)
    (r : Residues n) (q' : BinaryV (n+1))
    (hsource : rowAction g (axis j) = axis i)
    (hnum : substitute ((integralRational g)⁻¹ : GL3) (lift i (coordinateTuple n r i).val) = lift j q'.val)
    (hden : substitute ((integralRational g)⁻¹ : GL3) (X i) = X j) :
    coordinateTuple n (integralResidueAction n e g r) j =
      determinantCharacter e (integralRational g) • q' := by
  have he := component_action_congr n e g (axis j) r
    (residue n (coordinatePole n i (coordinateTuple n r i))) (by
      rw [hsource]
      apply literalFiberMap_injective n i
      exact (coordinateResidue_coordinatePole n i (coordinateTuple n r i)).symm)
  change literalFiberMap n j ((integralResidueAction n e g r) (axis j)) = _
  rw [he,residue_integral_equivariant,action_coordinatePole n e g i j _ q' hnum hden]
  change coordinateResidue n j
    (determinantCharacter e (integralRational g) • coordinatePole n j q') = _
  rw [map_smul,coordinateResidue_coordinatePole]

@[simp] theorem coordinateTuple_smul (n : ℕ) (c : ℚ) (r : Residues n) (i : Fin 3) :
    coordinateTuple n (c • r) i = c • coordinateTuple n r i := by
  change literalFiberMap n i (c • r (axis i)) = _
  exact map_smul _ _ _

/-- Coordinate axes under the exact row-permutation convention. -/
theorem rowAction_permutation_axis (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    rowAction (permutationMatrix π) (axis i) = axis (π.symm i) := by
  change rowAction (permutationMatrix π) (normalOfRow (Pi.single i 1) (axis_primitive i)) = _
  rw [rowAction_normalOfRow]
  apply (normalOfRow_eq_iff _ _).mpr
  left
  change Matrix.vecMul (Pi.single i (1 : ℤ)) ((π⁻¹).permMatrix ℤ) = Pi.single (π.symm i) 1
  rw [vecMul_permMatrix]
  funext j
  change (Pi.single i (1 : ℤ) : Fin 3 → ℤ) (π j) =
    (Pi.single (π.symm i) (1 : ℤ) : Fin 3 → ℤ) j
  by_cases hj : j = π.symm i
  · subst j; simp
  · have hpi : π j ≠ i := by
      intro h
      exact hj ((Equiv.eq_symm_apply π).mpr h)
    simp [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne hpi]

/-- Coordinate sign changes preserve each actual coordinate normal. -/
theorem rowAction_sign_axis (s : Fin 3 → Bool) (i : Fin 3) : rowAction (signMatrix s) (axis i) = axis i := by
  rw [rowAction_signMatrix]
  change signNormal s (normalOfRow (Pi.single i 1) (axis_primitive i)) = _
  rw [signNormal_normalOfRow]
  apply (normalOfRow_eq_iff _ _).mpr
  cases hs : s i
  · left
    funext j
    by_cases hj : j = i
    · subst j; simp [signRow,hs]
    · simp [signRow,Pi.single_eq_of_ne hj]
  · right
    funext j
    by_cases hj : j = i
    · subst j; simp [signRow,hs]
    · simp [signRow,Pi.single_eq_of_ne hj]

/-- Permutations which carry (a,b,c) to (a,b,c), (b,a,c), and (c,a,b). -/
def toAxisPermutation : Fin 3 → Equiv.Perm (Fin 3) :=
  ![1,Equiv.swap 0 1,Equiv.swap 0 1 * Equiv.swap 0 2]

theorem toAxisPermutation_zero (i : Fin 3) : toAxisPermutation i 0 = i := by
  fin_cases i <;> simp [toAxisPermutation,Equiv.Perm.mul_apply,Equiv.swap_apply_def]

theorem toAxisPermutation_source (i : Fin 3) :
    rowAction (permutationMatrix (toAxisPermutation i)) (axis i) = axis 0 := by
  rw [rowAction_permutation_axis]
  congr 1
  apply (toAxisPermutation i).injective
  rw [Equiv.apply_symm_apply,toAxisPermutation_zero]

/-- These permutations carry a canonical a-pole to the canonical i-pole with the same ordered numerator. -/
theorem toAxisPermutation_lift (i : Fin 3) (q : Binary) :
    substitute ((integralRational (permutationMatrix (toAxisPermutation i)))⁻¹ : GL3) (lift 0 q) = lift i q := by
  rw [substitute_permutation]
  have h : (rename (toAxisPermutation i)).comp (lift 0) = lift i := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply,lift,rename_X]
    fin_cases i <;> fin_cases j <;>
      simp [plane,toAxisPermutation,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
  exact AlgHom.congr_fun h q

def binarySwap (n : ℕ) (q : BinaryV n) : BinaryV n :=
  ⟨bind₁ ![X 1,X 0] q.val, isHomogeneous_bind₁_linear q.property _
    (by intro i; fin_cases i <;> exact isHomogeneous_X ℚ _)⟩

def binaryNegFirst (n : ℕ) (q : BinaryV n) : BinaryV n :=
  ⟨bind₁ ![-X 0,X 1] q.val, isHomogeneous_bind₁_linear q.property _
    (by intro i; fin_cases i
        · exact (isHomogeneous_X ℚ (0 : Fin 2)).neg
        · exact isHomogeneous_X ℚ _)⟩

def binaryNegSecond (n : ℕ) (q : BinaryV n) : BinaryV n :=
  ⟨bind₁ ![X 0,-X 1] q.val, isHomogeneous_bind₁_linear q.property _
    (by intro i; fin_cases i
        · exact isHomogeneous_X ℚ _
        · exact (isHomogeneous_X ℚ (1 : Fin 2)).neg)⟩

/-- Swapping b,c fixes the a-pole and literally swaps the binary numerator variables. -/
theorem swap12_lift (n : ℕ) (q : BinaryV n) :
    substitute ((integralRational (permutationMatrix (Equiv.swap 1 2)))⁻¹ : GL3) (lift 0 q.val) =
      lift 0 (binarySwap n q).val := by
  rw [substitute_permutation]
  have h : (rename (Equiv.swap (1 : Fin 3) 2)).comp (lift 0) =
      (lift 0).comp (bind₁ ![X 1,X 0]) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [lift,plane]
  exact AlgHom.congr_fun h q.val

def firstBinarySign : Fin 3 → Bool := ![false,true,false]
def secondBinarySign : Fin 3 → Bool := ![false,false,true]

theorem firstBinarySign_lift (n : ℕ) (q : BinaryV n) :
    substitute ((integralRational (signMatrix firstBinarySign))⁻¹ : GL3) (lift 0 q.val) =
      lift 0 (binaryNegFirst n q).val := by
  rw [substitute_sign]
  have h : (bind₁ (fun i : Fin 3 => if firstBinarySign i then -X i else X i)).comp (lift 0) =
      (lift 0).comp (bind₁ ![-X 0,X 1]) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [lift,plane,firstBinarySign]
  exact AlgHom.congr_fun h q.val

theorem secondBinarySign_lift (n : ℕ) (q : BinaryV n) :
    substitute ((integralRational (signMatrix secondBinarySign))⁻¹ : GL3) (lift 0 q.val) =
      lift 0 (binaryNegSecond n q).val := by
  rw [substitute_sign]
  have h : (bind₁ (fun i : Fin 3 => if secondBinarySign i then -X i else X i)).comp (lift 0) =
      (lift 0).comp (bind₁ ![X 0,-X 1]) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [lift,plane,secondBinarySign]
  exact AlgHom.congr_fun h q.val

@[simp] theorem oddSign_firstBinarySign : oddSign firstBinarySign = -1 := by
  simp [oddSign,signEntry,firstBinarySign,Fin.prod_univ_three]

@[simp] theorem oddSign_secondBinarySign : oddSign secondBinarySign = -1 := by
  simp [oddSign,signEntry,secondBinarySign,Fin.prod_univ_three]

end TernaryPoly.SinglePoleCoordinate
