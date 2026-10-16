module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.CanonicalOdd

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueGeneral
open OrdinaryResiduePolynomial SinglePoleCoordinate SinglePoleSupport PolynomialGLAction

/-- Every axis of the canonical representative has exactly the displayed common binary numerator. -/
theorem canonical_coordinateResidue (n : ℕ) (q : BinaryV (n+1)) (i : Fin 3) :
    coordinateResidue n i (canonicalRepresentative n q)=q := by
  have he (i j : Fin 3) : coordinateResidue n i (coordinatePole n j q)=if i=j then q else 0 := by
    by_cases h : i=j
    · subst j
      rw [ite_eq_left rfl,coordinateResidue_coordinatePole]
    · rw [ite_eq_right h]
      exact coordinateResidue_coordinatePole_ne n i j h q
  simp only [canonicalRepresentative,map_add,he]
  fin_cases i <;> norm_num [Fin.ext_iff]

/-- The polynomial correction never changes the actual literal coordinate residue. -/
theorem coordinateResidue_of_correction (n : ℕ) (x : SinglePole.singlePole n)
    (q : BinaryV (n+1)) (p : SinglePole.V n)
    (hx : x.val=representative q.val (X 0) (X 1) (X 2)+embed p.val) (i : Fin 3) :
    coordinateResidue n i x=q := by
  have he : x=canonicalRepresentative n q+SinglePole.polynomialInclusion n p := by
    apply Subtype.ext
    simpa only [Submodule.coe_add,SinglePole.polynomialInclusion_val,canonicalRepresentative_literal] using hx
  rw [he,map_add,coordinateResidue_polynomial,add_zero,canonical_coordinateResidue]

/-- The proved extreme obstruction applies to each actual coordinate residue, not merely
an existentially chosen binary numerator. -/
theorem actual_coordinate_extreme (n : ℕ) (e : ℤ) (x : SinglePole.singlePole n)
    (hsym : ∀ π, integralSinglePoleAction n e (permutationMatrix π) x =
      determinantCharacter e (integralRational (permutationMatrix π)) • x)
    (hodd : ∀ s, integralSinglePoleAction n e (signMatrix s) x =
      (determinantCharacter e (integralRational (signMatrix s))*oddSign s) • x)
    (hnorm : x+integralSinglePoleAction n e ReferenceCoefficientMatrices.a x+
      integralSinglePoleAction n e (ReferenceCoefficientMatrices.a^2) x=0)
    (i : Fin 3) (m : Fin 1 →₀ ℕ) :
    (coordinateResidue n i x).val.coeff (Finsupp.cons 1 m)=0 := by
  obtain ⟨q,p,_hq,hp,_ho,he⟩ := exists_period_lift_extreme n e x hsym hodd hnorm
  rw [coordinateResidue_of_correction n x q p hp i]
  exact he m

end TernaryPoly.OrdinaryResidueGeneral
