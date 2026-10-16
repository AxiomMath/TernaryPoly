module

public import TernaryPeriodPolynomials.SymmetricSolution.ToddBoundary
public import TernaryPeriodPolynomials.Analysis.Scalar.Coboundary

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The complete symmetric Todd scalar in its genuine binary coefficient ring. -/
def symmetricScalar (f : TernaryPolynomial) : MvPolynomial (Fin 2) ℚ :=
  (finSuccEquiv ℚ 2 (symmetricTodd f)).coeff 0

theorem symmetricScalar_lowerAxis {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hs : S f=f) (hg : f.IsHomogeneous n) :
    ScalarCoboundary.lowerAxis (symmetricScalar f)=0 := by
  have h := congrArg (fun p => (finSuccEquiv ℚ 2 p).coeff 0)
    (symmetricTodd_axisY hf hs hg)
  rw [finSuccEquiv_toddAxisY] at h
  simpa [symmetricScalar,Polynomial.coeff_map,ScalarCoboundary.lowerAxis,
    toddAxisYCoeff,ScalarCoboundary.z] using h

theorem symmetricTodd_zero_of_scalar_zero {f : TernaryPolynomial}
    (hf : PeriodRelations f) (hs : S f=f) (hz : symmetricScalar f=0) :
    symmetricTodd f=0 := by
  apply (finSuccEquiv ℚ 2).injective
  rw [finSuccEquiv_symmetricTodd_eq_C hf.1 hs hf.2]
  change Polynomial.C (symmetricScalar f)=finSuccEquiv ℚ 2 0
  rw [hz,map_zero,map_zero]

/-- The polynomial injection needed after actual mixed-coordinate class vanishing. -/
theorem symmetricTodd_zero_of_scalar_coboundary {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hs : S f=f) (hg : f.IsHomogeneous n)
    (m : ScalarCoboundary.Poly) (hb : ScalarCoboundary.B m=m)
    (hr : ScalarCoboundary.R m=m)
    (hj : symmetricScalar f=m-ScalarCoboundary.A m) : symmetricTodd f=0 := by
  apply symmetricTodd_zero_of_scalar_zero hf hs
  exact ScalarCoboundary.zero_of_coboundary hb hr hj
    (symmetricScalar_lowerAxis hf hs hg)

end TernaryPoly
