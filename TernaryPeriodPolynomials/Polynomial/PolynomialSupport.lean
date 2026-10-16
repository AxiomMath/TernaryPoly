module

public import TernaryPeriodPolynomials.Polynomial.Pairwise
public import TernaryPeriodPolynomials.Polynomial.Operators
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyPolynomials
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyAlgebra

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- Pairwise support is preserved by an actual permutation of the three coordinates. -/
theorem Pairwise.rename {p : TernaryPolynomial} (hp : Pairwise p)
    (e : Equiv.Perm (Fin 3)) : Pairwise (MvPolynomial.rename e p) := by
  intro d hd
  apply coeff_rename_eq_zero
  intro u hu
  apply hp u
  intro i
  have hi := hd (e i)
  rw [←hu,Finsupp.mapDomain_apply_of_injective e.injective] at hi
  exact hi

/-- Vanishing of any single partial derivative already gives the exact requested support. -/
theorem pairwise_of_pderiv_eq_zero (i : Fin 3) {p : TernaryPolynomial}
    (h : pderiv i p=0) : Pairwise p := by
  intro d hd
  let m := d-Finsupp.single i 1
  have he : m+Finsupp.single i 1=d := by
    apply tsub_add_cancel_of_le
    exact Finsupp.single_le_iff.mpr (hd i)
  have hc := congrArg (·.coeff m) h
  rw [coeff_pderiv,he,AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  exact (mul_eq_zero.mp hc).resolve_right (Nat.cast_add_one_ne_zero (m i))

/-- Every polynomial independent of one coordinate is pairwise supported. -/
theorem pairwise_erase (i : Fin 3) (p : TernaryPolynomial) :
    Pairwise (RadicalCoinvariantAlgebra.erase i p) := by
  apply pairwise_of_pderiv_eq_zero i
  induction p using MvPolynomial.induction_on with
  | C r => simp [RadicalCoinvariantAlgebra.erase]
  | add p q hp hq => simp only [map_add,hp,hq,add_zero]
  | mul_X p j hp =>
    by_cases hj : j=i
    · subst j; simp
    · simp [hp,hj]

/-- A nonzero rational root translation forces a missing coordinate, with no degree hypothesis. -/
theorem pairwise_of_first_shearStep_fixed (j : Fin 2) (c : ℚ) (hc : c≠0)
    {p : TernaryPolynomial} (hp : RelativeEdgeCohomologyPolynomials.shearStep 0 j.succ c p=p) :
    Pairwise p := by
  apply pairwise_of_pderiv_eq_zero 0
  have ht := congrArg (finSuccEquiv ℚ 2) hp
  rw [RelativeEdgeCohomologyPolynomials.finSuccEquiv_shearStep] at ht
  have hu : -(MvPolynomial.C c * X j : MvPolynomial (Fin 2) ℚ)≠0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr hc) (X_ne_zero j))
  have he := polynomial_eq_constant_of_translation (finSuccEquiv ℚ 2 p)
    (-(MvPolynomial.C c*X j)) hu ht
  apply (finSuccEquiv ℚ 2).injective
  rw [finSuccEquiv_pderiv_zero,map_zero,he,Polynomial.derivative_C]

/-- The first-two-coordinate swap preserves pairwise support. -/
theorem Pairwise.swap {p : TernaryPolynomial} (hp : Pairwise p) : Pairwise (S p) := by
  have he : S=MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [S, Equiv.swap_apply_def]
  rw [he]
  exact hp.rename _

/-- The literal cyclic substitution preserves pairwise support. -/
theorem Pairwise.cyclic {p : TernaryPolynomial} (hp : Pairwise p) : Pairwise (C p) := by
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective (![1,2,0] : Fin 3 → Fin 3) (by decide)
  have he : C=MvPolynomial.rename e := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [C,e]
  rw [he]
  exact hp.rename _

end TernaryPoly
