module

public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.Operators
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantPlaneInvariants

@[expose] public section


open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant

/-- Adding the coordinate reflection to the finite group leaves no positive-degree invariants. -/
theorem three_fixed_zero {d : ℕ} (hd : 0<d) (p : H d)
    (hs : swap d p=p) (ha : rotation d p=p) (hD : negateFirst d p=p) : p=0 := by
  have hu : operator d (!![1,-1;0,1] : Mat) = rotation d * negateFirst d * swap d := by
    rw [rotation,negateFirst,swap,←operator_mul,←operator_mul]
    congr 1
    decide +kernel
  have hl : operator d (!![1,0;-1,1] : Mat) =
      swap d * operator d (!![1,-1;0,1] : Mat) * swap d := by
    rw [swap,←operator_mul,←operator_mul]
    congr 1
    decide +kernel
  have hup : operator d (!![1,-1;0,1] : Mat) p=p := by
    rw [hu,Module.End.mul_apply,Module.End.mul_apply,hs,hD,ha]
  have hlp : operator d (!![1,0;-1,1] : Mat) p=p := by
    rw [hl,Module.End.mul_apply,Module.End.mul_apply,hs,hup,hs]
  apply RadicalCoinvariantAlgebra.binary_transvections_fixed_zero hd p
  · have he : BinaryModularSymbolCoefficients.linearForm (!![1,-1;0,1] : Mat)=
        (![X 0-X 1,X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) := by
      funext i
      fin_cases i <;> simp [BinaryModularSymbolCoefficients.linearForm,Fin.sum_univ_two,sub_eq_add_neg]
    have hv := congrArg Subtype.val hup
    change bind₁ (BinaryModularSymbolCoefficients.linearForm _) p.val=p.val at hv
    simpa only [he] using hv
  · have he : BinaryModularSymbolCoefficients.linearForm (!![1,0;-1,1] : Mat)=
        (![X 0,X 1-X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) := by
      funext i
      fin_cases i <;> simp [BinaryModularSymbolCoefficients.linearForm,Fin.sum_univ_two,sub_eq_add_neg,add_comm]
    have hv := congrArg Subtype.val hlp
    change bind₁ (BinaryModularSymbolCoefficients.linearForm _) p.val=p.val at hv
    simpa only [he] using hv

end TernaryPoly.BinaryFiniteInvariant
