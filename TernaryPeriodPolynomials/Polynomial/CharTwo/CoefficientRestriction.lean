module

public import TernaryPeriodPolynomials.Polynomial.Divisibility
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Order.Ring.Finset
public import Mathlib.Data.Fintype.Order
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoFormal

abbrev Poly := MvPolynomial (Fin 3) (ZMod 2)

/-- The formal elementary coordinates, not the actual ternary coordinate functions. -/
def a : Poly := X 0
def b : Poly := X 1
def c : Poly := X 2

def d4 : Poly := a^4+b^2+a*c
def d6 : Poly := a^2*b^2+a^3*c+a*b*c+c^2
def d7 : Poly := a*c*(a*b+c)

def B2 : Poly := a^2+b
def B7 : Poly := a^6+a^3*c+b^3+c^2

/-- Coefficient coordinates are evaluated at `d4,d6,d7²`. -/
def formalEvenEval : Poly →ₐ[ZMod 2] Poly := bind₁ ![d4,d6,d7^2]

/-- Restriction of formal elementary coordinates to `a=0`. -/
def restrictA : Poly →ₐ[ZMod 2] Poly := bind₁ ![0,X 1,X 2]

/-- The induced coefficient substitution on the plane `a=0`. -/
def squareRestriction : Poly →ₐ[ZMod 2] Poly := bind₁ ![(X 1)^2,(X 2)^2,0]

/-- Killing the last coefficient coordinate. -/
def dropThird : Poly →ₐ[ZMod 2] Poly := bind₁ ![X 0,X 1,0]

def cycle : Fin 3 → Fin 3 := ![1,2,0]

/-- Square restriction factors through the injective variable expansion. -/
theorem squareRestriction_eq_expand_rename (p : Poly) :
    squareRestriction p = expand 2 (rename cycle (dropThird p)) := by
  have he : squareRestriction = (expand 2).comp ((rename cycle).comp dropThird) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [squareRestriction, dropThird, cycle]
  exact DFunLike.congr_fun he p

/-- Every partial derivative of a square restriction vanishes in characteristic two. -/
theorem pderiv_squareRestriction_zero (p : Poly) (i : Fin 3) :
    pderiv i (squareRestriction p) = 0 := by
  have he (q : Poly) : pderiv i (expand 2 q) = 0 := by
    induction q using MvPolynomial.induction_on with
    | C r => simp
    | add f g hf hg => simp [hf,hg]
    | mul_X f j hf => simp [map_mul, hf, CharTwo.two_eq_zero]
  rw [squareRestriction_eq_expand_rename]
  exact he _

/-- The kernel of square restriction consists exactly of multiples of the third coordinate. -/
theorem squareRestriction_eq_zero_iff (p : Poly) :
    squareRestriction p = 0 ↔ (X 2 : Poly) ∣ p := by
  constructor
  · intro hp
    rw [squareRestriction_eq_expand_rename] at hp
    have he : rename cycle (dropThird p) = 0 := (expand_eq_zero (by decide)).mp hp
    have hz : dropThird p = 0 := by
      apply rename_injective cycle (by decide)
      simpa only [map_zero] using he
    have hv : Function.update (X : Fin 3 → Poly) 2 0 = ![X 0,X 1,0] := by
      funext i
      fin_cases i <;> simp
    simpa only [sub_zero] using linear_factor_dvd_of_substitution_zero p 2 0
      (by rw [hv]; exact hz)
  · rintro ⟨q,rfl⟩
    simp [squareRestriction]

/-- Restricting an even-invariant expression gives precisely the coefficient square map. -/
theorem restrictA_formalEvenEval (p : Poly) :
    restrictA (formalEvenEval p) = squareRestriction p := by
  have he : restrictA.comp formalEvenEval = squareRestriction := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [formalEvenEval, restrictA, squareRestriction, d4, d6, d7, a, b, c]
  exact DFunLike.congr_fun he p

/-- The three surviving basis terms split into even and odd powers of the formal variable `b`. -/
theorem restriction_identity (p0 p2 p7 : Poly) :
    restrictA (formalEvenEval p0 + formalEvenEval p2*B2 + formalEvenEval p7*B7) =
      squareRestriction (p0+X 1*p7) + X 1*squareRestriction (p2+X 0*p7) := by
  simp only [map_add, map_mul, restrictA_formalEvenEval]
  simp [restrictA, B2, B7, a, b, c, squareRestriction]
  ring

/-- Differentiation separates the two parity sectors of a square-restricted expression. -/
theorem squareRestriction_parity {A B : Poly}
    (h : squareRestriction A + X 1*squareRestriction B = 0) :
    squareRestriction A = 0 ∧ squareRestriction B = 0 := by
  have hd := congrArg (pderiv (1 : Fin 3)) h
  have hB : squareRestriction B = 0 := by
    simpa [pderiv_squareRestriction_zero] using hd
  refine ⟨?_,hB⟩
  simpa only [hB, mul_zero, add_zero] using h

/-- Vanishing at `a=0` forces polynomial, rather than localized, coefficient divisibilities. -/
theorem coefficient_restriction {p0 p2 p7 : Poly}
    (h : restrictA (formalEvenEval p0 + formalEvenEval p2*B2 + formalEvenEval p7*B7) = 0) :
    ∃ u0 u2 : Poly, p0 = X 1*p7+X 2*u0 ∧ p2 = X 0*p7+X 2*u2 := by
  rw [restriction_identity] at h
  obtain ⟨h0,h2⟩ := squareRestriction_parity h
  obtain ⟨u0,hu0⟩ := (squareRestriction_eq_zero_iff _).mp h0
  obtain ⟨u2,hu2⟩ := (squareRestriction_eq_zero_iff _).mp h2
  refine ⟨u0,u2,?_,?_⟩
  · calc
      p0 = (p0+X 1*p7)+X 1*p7 := by simp [add_assoc, CharTwo.add_self_eq_zero]
      _ = X 1*p7+X 2*u0 := by rw [hu0,add_comm]
  · calc
      p2 = (p2+X 0*p7)+X 0*p7 := by simp [add_assoc, CharTwo.add_self_eq_zero]
      _ = X 0*p7+X 2*u2 := by rw [hu2,add_comm]

/-- The coefficient divisibilities are also sufficient for vanishing of this restriction. -/
theorem coefficient_restriction_iff (p0 p2 p7 : Poly) :
    restrictA (formalEvenEval p0 + formalEvenEval p2*B2 + formalEvenEval p7*B7) = 0 ↔
      ∃ u0 u2 : Poly, p0 = X 1*p7+X 2*u0 ∧ p2 = X 0*p7+X 2*u2 := by
  refine ⟨coefficient_restriction, ?_⟩
  rintro ⟨u0,u2,rfl,rfl⟩
  rw [restriction_identity]
  simp [squareRestriction, add_assoc, CharTwo.add_self_eq_zero]

/-- The formal basis relation used after coefficient restriction. -/
theorem B7_add_d6_add_d4_mul_B2 : B7+d6+d4*B2 = a^3*(a*b+c) := by
  have h3 : (3 : Poly) = 1 := by simpa using CharP.cast_eq_mod Poly 2 3
  unfold B7 d6 d4 B2
  ring_nf
  simp [CharTwo.two_eq_zero, h3]

end TernaryPoly.CharTwoFormal
