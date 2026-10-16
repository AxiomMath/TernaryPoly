module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.CoordinateReconstruction
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.LiftObstruction

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueGeneral
open OrdinaryResiduePolynomial SinglePoleCoordinate SinglePoleSupport PolynomialGLAction

/-- The canonical residue representative has exactly the literal fraction formula. -/
theorem canonicalRepresentative_literal (n : ℕ) (q : BinaryV (n+1)) :
    (canonicalRepresentative n q).val=representative q.val (X 0) (X 1) (X 2) := by
  rw [canonicalRepresentative_val]
  have hl (u v : Fin 3) : (rename (![u,v] : Fin 2 → Fin 3) : BP →ₐ[ℚ] TP)=
      bind₁ ![X u,X v] := by
    apply algHom_ext
    intro i
    fin_cases i <;> simp
  simp only [representative,binaryLiftEval,hl]

/-- Equal actual residues differ by an actual homogeneous polynomial. -/
theorem exists_polynomial_correction (n : ℕ) (x : SinglePole.singlePole n)
    (q : BinaryV (n+1))
    (hq : SinglePole.residue n (canonicalRepresentative n q)=SinglePole.residue n x) :
    ∃ p : SinglePole.V n,
      x.val=representative q.val (X 0) (X 1) (X 2)+embed p.val := by
  have hk : x-canonicalRepresentative n q ∈ (SinglePole.residue n).ker := by
    change SinglePole.residue n (x-canonicalRepresentative n q)=0
    rw [map_sub,hq,sub_self]
  rw [SinglePole.residue_exact] at hk
  obtain ⟨p,hp⟩ := hk
  refine ⟨p,?_⟩
  have he := congrArg Subtype.val hp
  simp only [SinglePole.polynomialInclusion_val,Submodule.coe_sub] at he
  rw [canonicalRepresentative_literal] at he
  linear_combination -he

/-- The actual single-pole norm is the actual fraction-field norm on values. -/
theorem singlePole_norm_value (n : ℕ) (e : ℤ) (x : SinglePole.singlePole n)
    (hn : x+integralSinglePoleAction n e ReferenceCoefficientMatrices.a x+
      integralSinglePoleAction n e (ReferenceCoefficientMatrices.a^2) x=0) :
    fractionNorm e x.val=0 := by
  have he := congrArg Subtype.val hn
  exact he

/-- Every actual symmetric separately odd norm-zero single-pole coefficient has a
homogeneous binary period numerator and a homogeneous polynomial correction.
The binary period relation is a conclusion of the actual rational norm. -/
theorem exists_period_polynomial_correction (n : ℕ) (e : ℤ) (x : SinglePole.singlePole n)
    (hsym : ∀ π, integralSinglePoleAction n e (permutationMatrix π) x =
      determinantCharacter e (integralRational (permutationMatrix π)) • x)
    (hodd : ∀ s, integralSinglePoleAction n e (signMatrix s) x =
      (determinantCharacter e (integralRational (signMatrix s))*oddSign s) • x)
    (hnorm : x+integralSinglePoleAction n e ReferenceCoefficientMatrices.a x+
      integralSinglePoleAction n e (ReferenceCoefficientMatrices.a^2) x=0) :
    ∃ q : BinaryV (n+1), ∃ p : SinglePole.V n,
      ∃ hq : SymmetricBinaryPeriodRelations q.val,
      x.val=representative q.val (X 0) (X 1) (X 2)+embed p.val ∧
      N p.val= -defect q.val hq := by
  have hrs : SymmetricResidue n e (SinglePole.residue n x) := by
    intro π
    rw [residue_integral_equivariant,hsym,map_smul]
  have hro : SeparatelyOddResidue n e (SinglePole.residue n x) := by
    intro s
    rw [residue_integral_equivariant,hodd,map_smul]
  obtain ⟨q,hq1,hq2,hq3,hqr⟩ := exists_canonical_representative n e (SinglePole.residue n x)
    hrs hro (singlePole_residue_coordinate_support n e x hsym hodd hnorm)
  obtain ⟨p,hp⟩ := exists_polynomial_correction n x q hqr
  have hn := singlePole_norm_value n e x hnorm
  rw [hp] at hn
  have hq := period_of_norm_zero_lift e q.val ⟨hq1,hq2,hq3⟩ p.val hn
  exact ⟨q,p,hq,hp,polynomial_correction_norm e q.val hq p.val hn⟩

end TernaryPoly.OrdinaryResidueGeneral
