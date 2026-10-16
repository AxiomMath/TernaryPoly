module

public import TernaryPeriodPolynomials.ModularForm.Endpoint.Ray
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Polynomial

@[expose] public section


noncomputable section
open MvPolynomial

namespace TernaryPoly.BinaryCuspPeriod

/-- Literal evaluation of the finite odd projection. -/
theorem eval_oddPeriod {d : ℕ} (f : Forms d) (x y : ℂ) :
    eval ![x,y] (oddPeriod f) = ∑ j ∈ (Finset.range (d+1)).filter Odd,
      periodCoefficient f j * x^j * y^(d-j) := by
  simp [oddPeriod, monomial_exponent]

/-- The actual finite odd projection is exactly one half of the odd part of the full period. -/
theorem two_mul_eval_oddPeriod {d : ℕ} (f : Forms d) (x y : ℂ) :
    2 * eval ![x,y] (oddPeriod f) = eval ![x,y] (period f) - eval ![-x,y] (period f) := by
  classical
  rw [eval_oddPeriod, eval_period, eval_period, Finset.sum_filter, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rcases Nat.even_or_odd j with he | ho
  · have hn : ¬Odd j := Nat.not_odd_iff_even.mpr he
    simp [hn, he.neg_pow]
  · simp [ho, ho.neg_pow]
    ring

/-- Binary substitution and literal evaluation commute with the exact two-entry tuple. -/
theorem eval_bind_binary (p a b : MvPolynomial (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    eval v (bind₁ ![a,b] p) = eval ![eval v a, eval v b] p := by
  change eval₂Hom (RingHom.id ℂ) v (bind₁ ![a,b] p) = _
  rw [eval₂Hom_bind₁]
  have ht : (fun i => eval₂Hom (RingHom.id ℂ) v (![a,b] i)) = ![eval v a,eval v b] := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  rfl

/-- Evaluation of the actual odd period is separately odd in the second coordinate. -/
theorem eval_oddPeriod_neg_second {d : ℕ} (hd : Even d) (f : Forms d) (x y : ℂ) :
    eval ![x,-y] (oddPeriod f) = -eval ![x,y] (oddPeriod f) := by
  have h := congrArg (eval ![x,y]) (oddPeriod_odd_second hd f)
  rw [eval_bind_binary] at h
  simpa using h

end TernaryPoly.BinaryCuspPeriod
