module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.CoefficientParity

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoNorm

/-- The common square-invariant coefficient ring for the final finite source. -/
def squaredInvariantEval : Poly →ₐ[ZMod 2] Poly := bind₁ ![d4^2,d6^2,d7^2]

/-- Four representatives for the parities of the d4 and d6 powers. -/
def fourFactor : Fin 4 → Poly := ![1,d4,d6,d4*d6]

/-- Polynomial parity division in two coefficient variables, with no localization. -/
theorem invariantEven_square_split (p : Poly) :
    ∃ q0 q1 q2 q3 : Poly, invariantEvenEval p =
      squaredInvariantEval q0 + d4*squaredInvariantEval q1 +
        d6*squaredInvariantEval q2 + (d4*d6)*squaredInvariantEval q3 := by
  induction p using MvPolynomial.induction_on with
  | C t => exact ⟨C t,0,0,0,by simp [invariantEvenEval,squaredInvariantEval]⟩
  | add f g hf hg =>
    obtain ⟨p0,p1,p2,p3,hf⟩ := hf
    obtain ⟨q0,q1,q2,q3,hg⟩ := hg
    refine ⟨p0+q0,p1+q1,p2+q2,p3+q3,?_⟩
    rw [map_add,hf,hg]
    simp only [map_add]
    ring
  | mul_X f i hf =>
    obtain ⟨p0,p1,p2,p3,hf⟩ := hf
    fin_cases i
    · refine ⟨p1*X 0,p0,p3*X 0,p2,?_⟩
      rw [map_mul,hf]
      simp [invariantEvenEval,squaredInvariantEval]
      ring
    · refine ⟨p2*X 1,p3*X 1,p0,p1,?_⟩
      rw [map_mul,hf]
      simp [invariantEvenEval,squaredInvariantEval]
      ring
    · refine ⟨p0*X 2,p1*X 2,p2*X 2,p3*X 2,?_⟩
      rw [map_mul,hf]
      simp [invariantEvenEval,squaredInvariantEval]
      ring

/-- The same parity split, in a finite-index form suitable for source assembly. -/
theorem invariantEven_square_split_fin (p : Poly) :
    ∃ q : Fin 4 → Poly, invariantEvenEval p = ∑ i, squaredInvariantEval (q i)*fourFactor i := by
  obtain ⟨q0,q1,q2,q3,hq⟩ := invariantEven_square_split p
  refine ⟨![q0,q1,q2,q3],?_⟩
  rw [hq]
  simp [Fin.sum_univ_succ,fourFactor]
  ring

/-- A finite R0 expansion gives four times as many generators over the square invariants. -/
theorem expansion_over_squared_invariants {ι : Type*} [Fintype ι]
    (q : ι → Poly) (v : ι → Poly) :
    ∃ r : ι × Fin 4 → Poly,
      (∑ i, invariantEvenEval (q i)*v i) =
        ∑ i, squaredInvariantEval (r i)*(fourFactor i.2*v i.1) := by
  classical
  choose r hr using fun i => invariantEven_square_split_fin (q i)
  refine ⟨fun i => r i.1 i.2,?_⟩
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [hr,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end TernaryPoly.CharTwoNorm
