module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BernoulliDetection.Bernoulli

@[expose] public section


open GeneralEisenstein MvPolynomial

namespace TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers

theorem polynomial_lattice_cocycle_unique (first second : ℂ)
    (left right : ℤ × ℤ → Polynomial ℂ)
    (left_cocycle : ∀ firstPair secondPair, left (firstPair + secondPair) =
      left firstPair + Polynomial.taylor
        (-((firstPair.1 : ℂ) * first + (firstPair.2 : ℂ) * second)) (left secondPair))
    (right_cocycle : ∀ firstPair secondPair, right (firstPair + secondPair) =
      right firstPair + Polynomial.taylor
        (-((firstPair.1 : ℂ) * first + (firstPair.2 : ℂ) * second)) (right secondPair))
    (first_eq : left (1, 0) = right (1, 0))
    (second_eq : left (0, 1) = right (0, 1)) : left = right := by
  have origin (function : ℤ × ℤ → Polynomial ℂ)
      (cocycle : ∀ firstPair secondPair, function (firstPair + secondPair) =
        function firstPair + Polynomial.taylor
          (-((firstPair.1 : ℂ) * first + (firstPair.2 : ℂ) * second)) (function secondPair)) :
      function (0, 0) = 0 := by
    have equality := cocycle (0, 0) (0, 0)
    simp only [Prod.mk_add_mk, add_zero, Int.cast_zero, zero_mul, neg_zero,
      Polynomial.taylor_zero] at equality
    linear_combination -equality
  have first_axis (integer : ℤ) : left (integer, 0) = right (integer, 0) := by
    induction integer using Int.induction_on with
    | zero => rw [origin left left_cocycle, origin right right_cocycle]
    | succ integer induction_hypothesis =>
      have left_eq := left_cocycle (integer, 0) (1, 0)
      have right_eq := right_cocycle (integer, 0) (1, 0)
      rw [induction_hypothesis, first_eq] at left_eq
      simpa only [Prod.mk_add_mk, add_zero] using left_eq.trans right_eq.symm
    | pred integer induction_hypothesis =>
      have left_eq := left_cocycle (-(integer : ℤ) - 1, 0) (1, 0)
      have right_eq := right_cocycle (-(integer : ℤ) - 1, 0) (1, 0)
      simp only [Prod.mk_add_mk, sub_add_cancel, add_zero] at left_eq right_eq
      rw [first_eq, induction_hypothesis] at left_eq
      linear_combination right_eq - left_eq
  have second_axis (integer : ℤ) : left (0, integer) = right (0, integer) := by
    induction integer using Int.induction_on with
    | zero => rw [origin left left_cocycle, origin right right_cocycle]
    | succ integer induction_hypothesis =>
      have left_eq := left_cocycle (0, integer) (0, 1)
      have right_eq := right_cocycle (0, integer) (0, 1)
      rw [induction_hypothesis, second_eq] at left_eq
      simpa only [Prod.mk_add_mk, add_zero] using left_eq.trans right_eq.symm
    | pred integer induction_hypothesis =>
      have left_eq := left_cocycle (0, -(integer : ℤ) - 1) (0, 1)
      have right_eq := right_cocycle (0, -(integer : ℤ) - 1) (0, 1)
      simp only [Prod.mk_add_mk, sub_add_cancel, add_zero] at left_eq right_eq
      rw [second_eq, induction_hypothesis] at left_eq
      linear_combination right_eq - left_eq
  funext pair
  have left_eq := left_cocycle (pair.1, 0) (0, pair.2)
  have right_eq := right_cocycle (pair.1, 0) (0, pair.2)
  rw [first_axis, second_axis] at left_eq
  simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.eta] using
    left_eq.trans right_eq.symm

theorem polynomial_lattice_cocycle_expression (degree : ℕ) (first second : ℂ)
    (first_ne : first ≠ 0) (cocycle : ℤ × ℤ → Polynomial ℂ)
    (cocycle_eq : ∀ firstPair secondPair, cocycle (firstPair + secondPair) =
      cocycle firstPair + Polynomial.taylor
        (-((firstPair.1 : ℂ) * first + (firstPair.2 : ℂ) * second)) (cocycle secondPair))
    (degree_bound : ∀ pair, (cocycle pair).natDegree ≤ degree) :
    ∃ antiderivative : Polynomial ℂ, ∃ coefficient : ℂ,
      antiderivative.natDegree ≤ degree + 1 ∧
        ∀ pair, cocycle pair =
          Polynomial.taylor (-((pair.1 : ℂ) * first + (pair.2 : ℂ) * second)) antiderivative -
            antiderivative + Polynomial.C ((pair.2 : ℂ) * coefficient) := by
  obtain ⟨antiderivative, antiderivative_bound, difference⟩ :=
    polynomial_antidifference degree first first_ne (cocycle (1, 0)) (degree_bound (1, 0))
  let remainder := cocycle (0, 1) - (Polynomial.taylor (-second) antiderivative - antiderivative)
  have commuting : Polynomial.taylor (-first) (Polynomial.taylor (-second) antiderivative) =
      Polynomial.taylor (-second) (Polynomial.taylor (-first) antiderivative) := by
    rw [Polynomial.taylor_taylor, Polynomial.taylor_taylor, add_comm]
  have commutation := (cocycle_eq (1, 0) (0, 1)).symm.trans
    ((congrArg cocycle (add_comm (1, 0) (0, 1))).trans
      (cocycle_eq (0, 1) (1, 0)))
  simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero, zero_add] at commutation
  rw [← difference] at commutation
  simp only [map_sub] at commutation
  rw [← commuting] at commutation
  have periodic : Polynomial.taylor (-first) remainder = remainder := by
    dsimp [remainder]
    simp only [map_sub]
    linear_combination commutation
  have constant : remainder = Polynomial.C (remainder.eval 0) :=
    polynomial_periodic_constant remainder (-first) (neg_ne_zero.mpr first_ne)
      (fun point => by
        simpa only [Polynomial.taylor_eval] using
          congrArg (fun polynomial : Polynomial ℂ => polynomial.eval point) periodic)
  let candidate (pair : ℤ × ℤ) :=
    Polynomial.taylor (-((pair.1 : ℂ) * first + (pair.2 : ℂ) * second)) antiderivative -
      antiderivative + Polynomial.C ((pair.2 : ℂ) * remainder.eval 0)
  have candidate_cocycle : ∀ firstPair secondPair, candidate (firstPair + secondPair) =
      candidate firstPair + Polynomial.taylor
        (-((firstPair.1 : ℂ) * first + (firstPair.2 : ℂ) * second)) (candidate secondPair) := by
    intro firstPair secondPair
    simp only [candidate, map_add, map_sub, Polynomial.taylor_C, Polynomial.taylor_taylor,
      Prod.fst_add, Prod.snd_add, Int.cast_add]
    have parameter_eq :
        -(((firstPair.1 : ℂ) + secondPair.1) * first +
          ((firstPair.2 : ℂ) + secondPair.2) * second) =
        -((secondPair.1 : ℂ) * first + (secondPair.2 : ℂ) * second) +
          -((firstPair.1 : ℂ) * first + (firstPair.2 : ℂ) * second) := by ring
    rw [parameter_eq, add_mul, map_add]
    abel_nf
  have first_eq : cocycle (1, 0) = candidate (1, 0) := by
    simpa [candidate] using difference.symm
  have second_eq : cocycle (0, 1) = candidate (0, 1) := by
    dsimp [remainder] at constant
    simp only [candidate, Int.cast_zero, Int.cast_one, zero_mul, one_mul, zero_add]
    linear_combination constant
  have equality := polynomial_lattice_cocycle_unique first second cocycle candidate
    cocycle_eq candidate_cocycle first_eq second_eq
  exact ⟨antiderivative, remainder.eval 0, antiderivative_bound,
    fun pair => congrFun equality pair⟩

end TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers
