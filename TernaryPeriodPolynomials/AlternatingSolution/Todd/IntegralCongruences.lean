module

public import TernaryPeriodPolynomials.SymmetricSolution.BernoulliTwoIntegral
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Naturality
public import TernaryPeriodPolynomials.Polynomial.TaylorHasse
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

open Polynomial
open scoped BigOperators
noncomputable section
namespace TernaryPoly.ToddIntegralCongruences
open BernoulliTwoIntegral

/-- Exact Hasse coefficients of the integral operator B₄. -/
def b4Coeff (k : ℕ) : ℤ :=
  if k = 0 then 4 else if k = 1 then 2 else if k = 2 then -2
  else if Even k then 2 else 0

/-- Residues modulo two of the Hasse coefficients of the second integral operator. -/
def b2Coeff (k : ℕ) : ℤ :=
  if k = 1 ∨ (0 < k ∧ Even k) then 1 else 0

/-- The exact second-operator coefficients retain its two low-index correction terms. -/
def b2ExactCoeff (k : ℕ) : ℤ :=
  1 + k + (if k = 0 then 1 else 0) + (if k = 1 then 1 else 0)

/-- The all-index Bernoulli congruence for the genuine B₄ Hasse coefficients. -/
theorem b4Coeff_congruence (k : ℕ) :
    TwoIntegral ((4*(-1 : ℚ)^k*bernoulli k-(b4Coeff k : ℚ))/8) := by
  by_cases hk0 : k = 0
  · subst k
    norm_num [b4Coeff, bernoulli_zero]
    exact twoIntegral_zero
  by_cases hk1 : k = 1
  · subst k
    norm_num [b4Coeff, bernoulli_one]
    exact twoIntegral_zero
  by_cases hk2 : k = 2
  · subst k
    norm_num [b4Coeff, bernoulli_two, TwoIntegral]
    decide
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨m, hm⟩ := he
    have hk : k = 2*m := by omega
    have hm2 : 2 ≤ m := by omega
    obtain ⟨t, ht, hbt⟩ := twiceBernoulli_modFour_one m hm2
    have hs : (-1 : ℚ)^k = 1 := (show Even k from ⟨m, hm⟩).neg_one_pow
    simp only [b4Coeff, ite_eq_right hk0, ite_eq_right hk1, ite_eq_right hk2,
      ite_eq_left (show Even k from ⟨m, hm⟩), Int.cast_ofNat, hs, mul_one]
    rw [hk]
    have heq : (4*bernoulli (2*m)-2)/8 = t := by
      dsimp [twiceBernoulli] at hbt
      linarith
    rwa [heq]
  · rw [bernoulli_eq_zero_of_odd ho (by omega), mul_zero]
    simp [b4Coeff, hk0, hk1, hk2, Nat.not_even_iff_odd.mpr ho]
    exact twoIntegral_zero

private theorem b4Coeff_b2Coeff (k : ℕ) :
    b4Coeff k = 2*b2Coeff k + 4*(if k = 0 then 1 else if k = 2 then -1 else 0) := by
  by_cases hk0 : k = 0
  · subst k; norm_num [b4Coeff, b2Coeff]
  by_cases hk1 : k = 1
  · subst k; norm_num [b4Coeff, b2Coeff]
  by_cases hk2 : k = 2
  · subst k; norm_num [b4Coeff, b2Coeff]
  by_cases he : Even k <;> simp [b4Coeff, b2Coeff, hk0, hk1, hk2, he, Nat.pos_of_ne_zero hk0]

/-- The all-index congruence with the second operator's parity residues. -/
theorem b2Coeff_congruence (k : ℕ) :
    TwoIntegral ((2*(-1 : ℚ)^k*bernoulli k-(b2Coeff k : ℚ))/2) := by
  have h : (2*(-1 : ℚ)^k*bernoulli k-(b2Coeff k : ℚ))/2 =
      2*((4*(-1 : ℚ)^k*bernoulli k-(b4Coeff k : ℚ))/8) +
        ((if k = 0 then 1 else if k = 2 then -1 else 0 : ℤ) : ℚ) := by
    rw [b4Coeff_b2Coeff]
    push_cast
    ring
  rw [h]
  exact ((twoIntegral_nat 2).mul (b4Coeff_congruence k)).add (twoIntegral_int _)

/-- The exact second-operator coefficient and its stated parity residue differ by an even integer. -/
theorem b2ExactCoeff_sub_even (k : ℕ) : Even (b2ExactCoeff k-b2Coeff k) := by
  by_cases hk0 : k = 0
  · subst k; norm_num [b2ExactCoeff, b2Coeff]
  by_cases hk1 : k = 1
  · subst k; norm_num [b2ExactCoeff, b2Coeff]
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨m, hm⟩ := he
    have hk : k = 2*m := by omega
    refine ⟨(m : ℤ), ?_⟩
    simp [b2ExactCoeff, b2Coeff, hk0, hk1, Nat.pos_of_ne_zero hk0,
      show Even k from ⟨m, hm⟩]
    omega
  · obtain ⟨m, hm⟩ := ho
    have hk : k = 2*m+1 := by omega
    refine ⟨(m+1 : ℤ), ?_⟩
    simp [b2ExactCoeff, b2Coeff, hk0, hk1,
      Nat.not_even_iff_odd.mpr (show Odd k from ⟨m, hm⟩)]
    omega

/-- The congruence also holds for the exact second-operator coefficients. -/
theorem b2ExactCoeff_congruence (k : ℕ) :
    TwoIntegral ((2*(-1 : ℚ)^k*bernoulli k-(b2ExactCoeff k : ℚ))/2) := by
  obtain ⟨z, hz⟩ := b2ExactCoeff_sub_even k
  have hd : ((b2ExactCoeff k : ℚ)-(b2Coeff k : ℚ))/2 = (z : ℚ) := by
    have hq := congrArg (fun t : ℤ => (t : ℚ)) hz
    push_cast at hq
    linarith
  have h : (2*(-1 : ℚ)^k*bernoulli k-(b2ExactCoeff k : ℚ))/2 =
      (2*(-1 : ℚ)^k*bernoulli k-(b2Coeff k : ℚ))/2 - z := by
    rw [← hd]
    ring
  rw [h]
  exact (b2Coeff_congruence k).sub (twoIntegral_int z)

/-- A finitely supported coefficient correction. -/
def deltaCoeff (j : ℕ) (r : ℤ) (k : ℕ) : ℤ := if k = j then r else 0

private theorem b4Coeff_formula (k : ℕ) : b4Coeff k =
    deltaCoeff 0 2 k + 1 + (-1)^k + deltaCoeff 1 2 k - deltaCoeff 2 4 k := by
  by_cases hk0 : k = 0
  · subst k; norm_num [b4Coeff, deltaCoeff]
  by_cases hk1 : k = 1
  · subst k; norm_num [b4Coeff, deltaCoeff]
  by_cases hk2 : k = 2
  · subst k; norm_num [b4Coeff, deltaCoeff]
  rcases Nat.even_or_odd k with he | ho
  · simp [b4Coeff, deltaCoeff, hk0, hk1, hk2, he, (show Even k from he).neg_one_pow]
  · simp [b4Coeff, deltaCoeff, hk0, hk1, hk2, Nat.not_even_iff_odd.mpr ho,
      (show Odd k from ho).neg_one_pow]

section IntegralOperators
variable {R : Type*} [CommRing R]

/-- The integer-coefficient finite Hasse operator at a chosen cutoff. -/
def integerHasseSum (c : ℕ → ℤ) (u : R) (N : ℕ) (p : Polynomial R) : Polynomial R :=
  ∑ k ∈ Finset.range N, ((c k : R)*u^k) • hasseDeriv k p

/-- The actual translation-and-derivative operator B₄. -/
def b4Operator (u : R) (p : Polynomial R) : Polynomial R :=
  (2 : R) • p + taylor u p + taylor (-u) p + (2*u) • derivative p -
    (2*u^2) • derivative (derivative p)

/-- The actual composition (translation + identity)(identity + u times derivative). -/
def b2Operator (u : R) (p : Polynomial R) : Polynomial R :=
  taylor u (p + u • derivative p) + (p + u • derivative p)

private theorem integerHasseSum_add (c d : ℕ → ℤ) (u : R) (N : ℕ) (p : Polynomial R) :
    integerHasseSum (fun k => c k+d k) u N p =
      integerHasseSum c u N p + integerHasseSum d u N p := by
  simp [integerHasseSum, add_mul, add_smul, Finset.sum_add_distrib]

private theorem integerHasseSum_sub (c d : ℕ → ℤ) (u : R) (N : ℕ) (p : Polynomial R) :
    integerHasseSum (fun k => c k-d k) u N p =
      integerHasseSum c u N p - integerHasseSum d u N p := by
  simp [integerHasseSum, sub_mul, sub_smul, Finset.sum_sub_distrib]

private theorem integerHasseSum_delta (j : ℕ) (r : ℤ) (u : R) (N : ℕ)
    (p : Polynomial R) (hj : j < N) :
    integerHasseSum (deltaCoeff j r) u N p = ((r : R)*u^j) • hasseDeriv j p := by
  simp [integerHasseSum, deltaCoeff, ite_mul, ite_smul, Finset.sum_ite_eq', hj]

private theorem integerHasseSum_one (u : R) (N : ℕ) (p : Polynomial R)
    (hN : p.natDegree < N) : integerHasseSum (fun _ => 1) u N p = taylor u p := by
  simpa [integerHasseSum] using (taylor_eq_hasse_sum u p N hN).symm

private theorem integerHasseSum_sign (u : R) (N : ℕ) (p : Polynomial R)
    (hN : p.natDegree < N) : integerHasseSum (fun k => (-1)^k) u N p = taylor (-u) p := by
  simpa only [integerHasseSum, Int.cast_pow, Int.cast_neg, Int.cast_one,
    ← mul_pow, neg_one_mul] using (taylor_eq_hasse_sum (-u) p N hN).symm

private theorem derivative_twice (p : Polynomial R) :
    derivative (derivative p) = (2 : R) • hasseDeriv 2 p := by
  have h := DFunLike.congr_fun (hasseDeriv_comp (R := R) 1 1) p
  simpa [LinearMap.comp_apply, LinearMap.smul_apply, hasseDeriv_one', two_smul] using h

/-- The exact B₄ operator equals its stated finite integer Hasse sum. -/
theorem b4Operator_eq_hasseSum (u : R) (p : Polynomial R) (N : ℕ)
    (hN : p.natDegree < N) (h3 : 3 ≤ N) :
    b4Operator u p = integerHasseSum b4Coeff u N p := by
  have hc : b4Coeff = fun k =>
      deltaCoeff 0 2 k + 1 + (-1)^k + deltaCoeff 1 2 k - deltaCoeff 2 4 k :=
    funext b4Coeff_formula
  rw [hc]
  simp only [integerHasseSum_sub, integerHasseSum_add]
  rw [integerHasseSum_delta 0 2 u N p (by omega),
    integerHasseSum_delta 1 2 u N p (by omega),
    integerHasseSum_delta 2 4 u N p (by omega),
    integerHasseSum_one u N p hN, integerHasseSum_sign u N p hN]
  simp only [b4Operator, derivative_twice, hasseDeriv_zero', hasseDeriv_one',
    pow_zero, pow_one, mul_one, Int.cast_ofNat, smul_smul]
  congr 2
  ring

private theorem hasseDeriv_derivative (k : ℕ) (p : Polynomial R) :
    hasseDeriv k (derivative p) = (k+1 : R) • hasseDeriv (k+1) p := by
  have h := DFunLike.congr_fun (hasseDeriv_comp (R := R) k 1) p
  rw [show (k+1 : R) = ((k+1 : ℕ) : R) by simp, Nat.cast_smul_eq_nsmul]
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, hasseDeriv_one',
    Nat.choose_succ_self_right] using h

private theorem integerHasseSum_index (u : R) (N : ℕ) (p : Polynomial R)
    (hN : p.natDegree < N) :
    integerHasseSum (fun k => (k : ℤ)) u N p = u • taylor u (derivative p) := by
  have hz : hasseDeriv N p = 0 := hasseDeriv_eq_zero_of_lt_natDegree p N hN
  have hshift := Finset.sum_range_succ' (fun k => ((k : R)*u^k) • hasseDeriv k p) N
  rw [Finset.sum_range_succ] at hshift
  simp only [hz, smul_zero, add_zero, Nat.cast_zero, zero_mul, zero_smul] at hshift
  rw [taylor_eq_hasse_sum u (derivative p) N
    (lt_of_le_of_lt ((natDegree_derivative_le p).trans (Nat.sub_le _ _)) hN), Finset.smul_sum]
  unfold integerHasseSum
  simp only [Int.cast_natCast]
  rw [hshift]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hasseDeriv_derivative, smul_smul, smul_smul]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  ring

/-- The exact second operator equals its integer Hasse sum, before reducing coefficients modulo two. -/
theorem b2Operator_eq_hasseSum (u : R) (p : Polynomial R) (N : ℕ)
    (hN : p.natDegree < N) (h2 : 2 ≤ N) :
    b2Operator u p = integerHasseSum b2ExactCoeff u N p := by
  change b2Operator u p = integerHasseSum
    (fun k => 1 + (k : ℤ) + deltaCoeff 0 1 k + deltaCoeff 1 1 k) u N p
  simp only [integerHasseSum_add]
  rw [integerHasseSum_one u N p hN, integerHasseSum_index u N p hN,
    integerHasseSum_delta 0 1 u N p (by omega),
    integerHasseSum_delta 1 1 u N p (by omega)]
  simp only [b2Operator, map_add, map_smul, Int.cast_one, one_mul,
    pow_zero, pow_one, one_smul, hasseDeriv_zero', hasseDeriv_one']
  abel

end IntegralOperators

/-- Coefficient maps commute with the integer Hasse operator. -/
theorem integerHasseSum_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (c : ℕ → ℤ) (u : R) (N : ℕ) (p : Polynomial R) :
    Polynomial.map φ (integerHasseSum c u N p) =
      integerHasseSum c (φ u) N (Polynomial.map φ p) := by
  simp [integerHasseSum, Polynomial.map_sum, Polynomial.map_smul, map_hasseDeriv,
    -Polynomial.hasseDeriv_map]

/-- A universal rational Hasse remainder, valid in every rational coefficient algebra. -/
theorem todd_hasse_remainder {R : Type*} [CommRing R] [Algebra ℚ R]
    (M D : ℤ) (hD : D ≠ 0) (c : ℕ → ℤ) (u : R) (p : Polynomial R) (N : ℕ)
    (hN : p.natDegree < N) :
    (M : R) • todd u p - integerHasseSum c u N p =
      (D : R) • ∑ k ∈ Finset.range N,
        (algebraMap ℚ R (((M : ℚ)*(-1)^k*bernoulli k-c k)/D)*u^k) • hasseDeriv k p := by
  rw [todd_eq_sum u p N hN]
  simp only [integerHasseSum, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib,
    ← sub_smul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hq : (D : ℚ)*(((M : ℚ)*(-1)^k*bernoulli k-c k)/D) =
      (M : ℚ)*(-1)^k*bernoulli k-c k := by field_simp
  have hqr := congrArg (algebraMap ℚ R) hq
  simp only [map_mul, map_intCast] at hqr
  have hneg : (-u)^k = (-1 : R)^k*u^k := by rw [← mul_pow, neg_one_mul]
  calc
    (M : R)*(algebraMap ℚ R (bernoulli k)*(-u)^k) - (c k : R)*u^k =
        algebraMap ℚ R ((M : ℚ)*(-1)^k*bernoulli k-c k)*u^k := by
      simp only [hneg, map_sub, map_mul, map_intCast, map_pow, map_neg, map_one]
      ring
    _ = _ := by rw [← hqr]; ring

/-- An integer polynomial in the coefficient variables, mapped to rational coefficients. -/
abbrev integerCoefficientMap {σ : Type*} :
    MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)

/-- Map an integer polynomial with polynomial parameters into the rational coefficient algebra. -/
def integerPolynomialMap {σ : Type*} (p : Polynomial (MvPolynomial σ ℤ)) :
    Polynomial (MvPolynomial σ ℚ) := Polynomial.map integerCoefficientMap p

/-- Every rational coefficient, including the parameter variables, has odd denominator. -/
def CoeffTwoIntegral {σ : Type*} (p : Polynomial (MvPolynomial σ ℚ)) : Prop :=
  ∀ (n : ℕ) (d : σ →₀ ℕ), TwoIntegral ((p.coeff n).coeff d)

lemma CoeffTwoIntegral.sum {σ ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (MvPolynomial σ ℚ)) (hf : ∀ i ∈ s, CoeffTwoIntegral (f i)) :
    CoeffTwoIntegral (∑ i ∈ s, f i) := by
  intro n d
  simp only [Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
  exact TwoIntegral.sum s _ (fun i hi => hf i hi n d)

lemma coeffTwoIntegral_smul_map {σ : Type*} (q : ℚ) (hq : TwoIntegral q)
    (p : Polynomial (MvPolynomial σ ℤ)) :
    CoeffTwoIntegral (q • integerPolynomialMap p) := by
  intro n d
  simpa [integerPolynomialMap, integerCoefficientMap, Polynomial.coeff_smul,
    MvPolynomial.coeff_smul, MvPolynomial.coeff_map] using
    hq.mul (twoIntegral_int ((p.coeff n).coeff d))

private theorem coeffTwoIntegral_hasse_term {σ : Type*} (q : ℚ) (hq : TwoIntegral q)
    (u : MvPolynomial σ ℤ) (p : Polynomial (MvPolynomial σ ℤ)) (k : ℕ) :
    CoeffTwoIntegral ((algebraMap ℚ (MvPolynomial σ ℚ) q*(integerCoefficientMap u)^k) •
      hasseDeriv k (integerPolynomialMap p)) := by
  have he : (algebraMap ℚ (MvPolynomial σ ℚ) q*(integerCoefficientMap u)^k) •
      hasseDeriv k (integerPolynomialMap p) =
      q • integerPolynomialMap (u^k • hasseDeriv k p) := by
    simp only [integerPolynomialMap, map_hasseDeriv, Polynomial.map_smul, map_pow,
      mul_smul, IsScalarTower.algebraMap_smul]
  rw [he]
  exact coeffTwoIntegral_smul_map q hq _

/-- The genuine B₄ operator agrees with four times Todd modulo eight, in every degree
and with arbitrary integer polynomial parameters. -/
theorem todd_b4_integral_remainder {σ : Type*} (u : MvPolynomial σ ℤ)
    (p : Polynomial (MvPolynomial σ ℤ)) :
    ∃ q : Polynomial (MvPolynomial σ ℚ), CoeffTwoIntegral q ∧
      (4 : MvPolynomial σ ℚ) • todd (integerCoefficientMap u) (integerPolynomialMap p) -
        integerPolynomialMap (b4Operator u p) = (8 : MvPolynomial σ ℚ) • q := by
  let N := p.natDegree+3
  have hpN : p.natDegree < N := by dsimp [N]; omega
  have hN : (integerPolynomialMap p).natDegree < N :=
    lt_of_le_of_lt Polynomial.natDegree_map_le hpN
  refine ⟨∑ k ∈ Finset.range N,
    (algebraMap ℚ (MvPolynomial σ ℚ)
      ((4*(-1 : ℚ)^k*bernoulli k-(b4Coeff k : ℚ))/8)*(integerCoefficientMap u)^k) •
        hasseDeriv k (integerPolynomialMap p), ?_, ?_⟩
  · apply CoeffTwoIntegral.sum
    intro k hk
    exact coeffTwoIntegral_hasse_term _ (b4Coeff_congruence k) u p k
  · rw [b4Operator_eq_hasseSum u p N hpN (by dsimp [N]; omega)]
    unfold integerPolynomialMap
    rw [integerHasseSum_map]
    exact todd_hasse_remainder 4 8 (by decide) b4Coeff _ _ N hN

/-- The genuine second operator agrees with twice Todd modulo two, in every degree
and with arbitrary integer polynomial parameters. -/
theorem todd_b2_integral_remainder {σ : Type*} (u : MvPolynomial σ ℤ)
    (p : Polynomial (MvPolynomial σ ℤ)) :
    ∃ q : Polynomial (MvPolynomial σ ℚ), CoeffTwoIntegral q ∧
      (2 : MvPolynomial σ ℚ) • todd (integerCoefficientMap u) (integerPolynomialMap p) -
        integerPolynomialMap (b2Operator u p) = (2 : MvPolynomial σ ℚ) • q := by
  let N := p.natDegree+2
  have hpN : p.natDegree < N := by dsimp [N]; omega
  have hN : (integerPolynomialMap p).natDegree < N :=
    lt_of_le_of_lt Polynomial.natDegree_map_le hpN
  refine ⟨∑ k ∈ Finset.range N,
    (algebraMap ℚ (MvPolynomial σ ℚ)
      ((2*(-1 : ℚ)^k*bernoulli k-(b2ExactCoeff k : ℚ))/2)*(integerCoefficientMap u)^k) •
        hasseDeriv k (integerPolynomialMap p), ?_, ?_⟩
  · apply CoeffTwoIntegral.sum
    intro k hk
    exact coeffTwoIntegral_hasse_term _ (b2ExactCoeff_congruence k) u p k
  · rw [b2Operator_eq_hasseSum u p N hpN (by dsimp [N]; omega)]
    unfold integerPolynomialMap
    rw [integerHasseSum_map]
    exact todd_hasse_remainder 2 2 (by decide) b2ExactCoeff _ _ N hN

end TernaryPoly.ToddIntegralCongruences
