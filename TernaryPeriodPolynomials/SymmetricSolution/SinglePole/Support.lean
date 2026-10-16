module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.SupportTransport
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.SupportSymmetry
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Support

@[expose] public section


noncomputable section
namespace TernaryPoly.SinglePoleSupport
open SinglePole PolynomialGLAction OrdinaryResidueSupport ModThreeGoodAction
attribute [local instance] Classical.propDecidable

/-- The determinant character never annihilates a principal part. -/
theorem determinantCharacter_ne_zero (e : ℤ) (g : GL3) : determinantCharacter e g ≠ 0 := by
  change ((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ)^e ≠ 0
  exact zpow_ne_zero e (Units.ne_zero _)

/-- Literal permutation symmetry in the stated determinant-twisted coefficient convention. -/
def SymmetricResidue (n : ℕ) (e : ℤ) (r : Residues n) : Prop :=
  ∀ π, integralResidueAction n e (permutationMatrix π) r =
    determinantCharacter e (integralRational (permutationMatrix π)) • r

/-- Literal separate oddness under simultaneous coordinate signs, retaining the determinant twist. -/
def SeparatelyOddResidue (n : ℕ) (e : ℤ) (r : Residues n) : Prop :=
  ∀ s, integralResidueAction n e (signMatrix s) r =
    (determinantCharacter e (integralRational (signMatrix s)) * oddSign s) • r

/-- The determinant of the literal sign matrix is exactly the product of its coordinate signs. -/
theorem determinantCharacter_signMatrix (e : ℤ) (s : Fin 3 → Bool) :
    determinantCharacter e (integralRational (signMatrix s)) = oddSign s ^ e := by
  change (((Matrix.diagonal (signEntry s)).map (Int.castRingHom ℚ)).det)^e = _
  rw [← RingHom.mapMatrix_apply,← RingHom.map_det,Matrix.det_diagonal,map_prod]
  rfl

/-- In the paper convention e=-1, the determinant and odd-coordinate signs cancel exactly. -/
theorem odd_scalar_neg_one (s : Fin 3 → Bool) :
    determinantCharacter (-1) (integralRational (signMatrix s)) * oddSign s = 1 := by
  rw [determinantCharacter_signMatrix,zpow_neg_one,inv_mul_cancel₀ (oddSign_ne_zero s)]

/-- Separate oddness is sign-matrix invariance for the explicit inverse-determinant convention. -/
theorem separatelyOddResidue_neg_one_iff (n : ℕ) (r : Residues n) :
    SeparatelyOddResidue n (-1) r ↔ ∀ s, integralResidueAction n (-1) (signMatrix s) r = r := by
  simp only [SeparatelyOddResidue,odd_scalar_neg_one,one_smul]

/-- A nonzero scalar symmetry of the actual action transports nonzero actual components. -/
theorem component_ne_zero_of_eigenvector (n : ℕ) (e : ℤ) (g : IntegralGL)
    (r : Residues n) (c : ℚ) (hc : c ≠ 0)
    (hr : integralResidueAction n e g r = c • r) (H : SinglePole.Normal) (hH : r H ≠ 0) :
    r (rowAction g H) ≠ 0 := by
  intro hzero
  have he := (component_action_zero_iff n e g H r).mpr hzero
  change component n H (integralResidueAction n e g r) = 0 at he
  rw [hr,map_smul] at he
  exact hH ((smul_eq_zero.mp he).resolve_left hc)

/-- Actual representation oddness forces sign invariance of the finite residue support. -/
theorem sign_support_of_odd (n : ℕ) (e : ℤ) (r : Residues n)
    (hr : SeparatelyOddResidue n e r) (s : Fin 3 → Bool) (H : SinglePole.Normal)
    (hH : r H ≠ 0) : r (signNormal s H) ≠ 0 := by
  rw [← rowAction_signMatrix]
  exact component_ne_zero_of_eigenvector n e (signMatrix s) r _
    (mul_ne_zero (determinantCharacter_ne_zero e _) (oddSign_ne_zero s)) (hr s) H hH

/-- Actual representation symmetry forces permutation invariance of the finite residue support. -/
theorem permutation_support_of_symmetric (n : ℕ) (e : ℤ) (r : Residues n)
    (hr : SymmetricResidue n e r) (π : Equiv.Perm (Fin 3)) (H : SinglePole.Normal)
    (hH : r H ≠ 0) : r (permuteNormal π H) ≠ 0 := by
  rw [← rowAction_permutationMatrix]
  exact component_ne_zero_of_eigenvector n e (permutationMatrix π) r _
    (determinantCharacter_ne_zero e _) (hr π) H hH

/-- The actual symmetric separately odd residue norm kernel is supported on coordinate hyperplanes. -/
theorem residue_coordinate_support (n : ℕ) (e : ℤ) (r : Residues n)
    (hsym : SymmetricResidue n e r) (hodd : SeparatelyOddResidue n e r)
    (hnorm : r + integralResidueAction n e ReferenceCoefficientMatrices.a r +
      integralResidueAction n e (ReferenceCoefficientMatrices.a^2) r = 0) :
    ∀ H, ¬Coordinate H → r H = 0 := by
  apply representation_norm_support (integralResidueAction n e) (component n) r
  · exact DFinsupp.finite_support r
  · exact sign_support_of_odd n e r hodd
  · exact permutation_support_of_symmetric n e r hsym
  · exact fun g H => component_action_zero_iff n e g H r
  · exact hnorm

/-- Every nonzero actual principal part lies at one of the three literal coordinate normals. -/
theorem residue_support_subset_axes (n : ℕ) (e : ℤ) (r : Residues n)
    (hsym : SymmetricResidue n e r) (hodd : SeparatelyOddResidue n e r)
    (hnorm : r + integralResidueAction n e ReferenceCoefficientMatrices.a r +
      integralResidueAction n e (ReferenceCoefficientMatrices.a^2) r = 0) :
    {H | r H ≠ 0} ⊆ Set.range axis := by
  intro H hH
  have hcoord : Coordinate H := by
    by_contra hn
    exact hH (residue_coordinate_support n e r hsym hodd hnorm H hn)
  obtain ⟨i,hi⟩ := hcoord
  exact ⟨i,hi.symm⟩

end TernaryPoly.SinglePoleSupport
