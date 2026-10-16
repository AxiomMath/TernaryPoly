module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.CoefficientResidue
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.SupportRational

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryFullCoefficient
open ModThreeGoodAction OrdinaryFullAction OrdinaryApartmentFrames SinglePoleSupport
open PolynomialGLAction
attribute [local instance] Classical.propDecidable

/-- The literal three-cycle and transposition in the existing permutation-matrix convention. -/
def cyclePermutation : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem permutationMatrix_cycle : permutationMatrix cyclePermutation = ReferenceCoefficientMatrices.c := by
  apply Units.ext
  decide +kernel

theorem permutationMatrix_swap : permutationMatrix (Equiv.swap 0 1) = ReferenceCoefficientMatrices.s := by
  apply Units.ext
  decide +kernel

theorem signFrame_eq_signMatrix (s : Finset (Fin 3)) :
    signFrame s = signMatrix (fun i => decide (i ∈ s)) := by
  apply Units.ext
  apply congrArg Matrix.diagonal
  funext i
  simp [OrdinaryApartmentFrames.signEntry,SinglePoleSupport.signEntry]

theorem determinantCharacter_cycle :
    determinantCharacter (-1) (integral ReferenceCoefficientMatrices.c) = 1 := by
  have hd : ((Matrix.GeneralLinearGroup.det (integral ReferenceCoefficientMatrices.c) : ℚˣ) : ℚ) = 1 := by
    rw [integral,Matrix.GeneralLinearGroup.map_det,ReferenceCoefficientMatrices.det_c,map_one]
    rfl
  change (((Matrix.GeneralLinearGroup.det (integral ReferenceCoefficientMatrices.c) : ℚˣ) : ℚ)) ^ (-1 : ℤ) = 1
  rw [hd,one_zpow]

theorem determinantCharacter_swap :
    determinantCharacter (-1) (integral ReferenceCoefficientMatrices.s) = -1 := by
  have hd : ((Matrix.GeneralLinearGroup.det (integral ReferenceCoefficientMatrices.s) : ℚˣ) : ℚ) = -1 := by
    rw [integral,Matrix.GeneralLinearGroup.map_det,ReferenceCoefficientMatrices.det_s]
    rfl
  change (((Matrix.GeneralLinearGroup.det (integral ReferenceCoefficientMatrices.s) : ℚˣ) : ℚ)) ^ (-1 : ℤ) = -1
  rw [hd,zpow_neg_one,inv_neg,inv_one]

/-- Full permutation symmetry and literal sign invariance imply precisely the apartment equations. -/
theorem relations_of_symmetry {E : Type*} [AddCommGroup E] [Module ℚ E]
    (ρ : Representation ℚ OrdinaryFullAction.GL3 E) (v : E)
    (hsym : ∀ π, ρ (integral (permutationMatrix π)) v =
      determinantCharacter (-1) (integral (permutationMatrix π)) • v)
    (hsign : ∀ s, ρ (integral (signMatrix s)) v = v)
    (hnorm : v + ρ (integral ReferenceCoefficientMatrices.a) v +
      ρ (integral (ReferenceCoefficientMatrices.a^2)) v = 0) : Relations ρ v where
  signs s := by rw [signFrame_eq_signMatrix,hsign]
  cyclic := by
    have h := hsym cyclePermutation
    rw [permutationMatrix_cycle,determinantCharacter_cycle,one_smul] at h
    exact h
  swap := by
    have h := hsym (Equiv.swap 0 1)
    rw [permutationMatrix_swap,determinantCharacter_swap,neg_one_smul] at h
    exact h
  norm := hnorm

/-- Actual symmetric separately odd norm-zero residue coefficients define full-level ordinary functionals. -/
theorem residue_relations_of_symmetry (n : ℕ) (r : SinglePole.Residues n)
    (hsym : SymmetricResidue n (-1) r) (hodd : SeparatelyOddResidue n (-1) r)
    (hnorm : r + integralResidueAction n (-1) ReferenceCoefficientMatrices.a r +
      integralResidueAction n (-1) (ReferenceCoefficientMatrices.a^2) r = 0) :
    Relations (SinglePole.residueAction n (-1)) r :=
  relations_of_symmetry _ r hsym ((separatelyOddResidue_neg_one_iff n r).mp hodd) hnorm

/-- Actual symmetric sign-invariant single-pole norm coefficients define full-level ordinary functionals. -/
theorem singlePole_relations_of_symmetry (n : ℕ) (x : SinglePole.singlePole n)
    (hsym : ∀ π, integralSinglePoleAction n (-1) (permutationMatrix π) x =
      determinantCharacter (-1) (integralRational (permutationMatrix π)) • x)
    (hsign : ∀ s, integralSinglePoleAction n (-1) (signMatrix s) x = x)
    (hnorm : x + integralSinglePoleAction n (-1) ReferenceCoefficientMatrices.a x +
      integralSinglePoleAction n (-1) (ReferenceCoefficientMatrices.a^2) x = 0) :
    Relations (SinglePole.singlePoleAction n (-1)) x :=
  relations_of_symmetry _ x hsym hsign hnorm

end TernaryPoly.OrdinaryFullCoefficient
