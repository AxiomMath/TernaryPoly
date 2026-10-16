module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.MoveAdd
public import Mathlib.Tactic.Ring.NamePowerVars
public import Mathlib.Topology.WithTopology

@[expose] public section


open scoped BigOperators
namespace TernaryPoly.BernoulliTwoIntegral

/-- The concrete localization predicate at the prime two. -/
def TwoIntegral (q : ℚ) : Prop := Odd q.den

/-- Congruence modulo four in the localization of the integers at two. -/
def ModFour (q r : ℚ) : Prop := ∃ t : ℚ, TwoIntegral t ∧ q - r = 4 * t

lemma twoIntegral_zero : TwoIntegral 0 := by norm_num [TwoIntegral]
lemma twoIntegral_one : TwoIntegral 1 := by norm_num [TwoIntegral]
lemma twoIntegral_nat (n : ℕ) : TwoIntegral (n : ℚ) := by simp [TwoIntegral]
lemma twoIntegral_int (n : ℤ) : TwoIntegral (n : ℚ) := by simp [TwoIntegral]
lemma TwoIntegral.add {q r : ℚ} (hq : TwoIntegral q) (hr : TwoIntegral r) :
    TwoIntegral (q + r) :=
  (Odd.mul hq hr).of_dvd_nat (Rat.add_den_dvd q r)
lemma TwoIntegral.sub {q r : ℚ} (hq : TwoIntegral q) (hr : TwoIntegral r) :
    TwoIntegral (q - r) :=
  (Odd.mul hq hr).of_dvd_nat (Rat.sub_den_dvd q r)
lemma TwoIntegral.mul {q r : ℚ} (hq : TwoIntegral q) (hr : TwoIntegral r) :
    TwoIntegral (q * r) :=
  (Odd.mul hq hr).of_dvd_nat (Rat.mul_den_dvd q r)
lemma TwoIntegral.neg {q : ℚ} (hq : TwoIntegral q) : TwoIntegral (-q) := by
  simpa only [TwoIntegral, Rat.neg_den] using hq
lemma TwoIntegral.pow {q : ℚ} (hq : TwoIntegral q) (n : ℕ) : TwoIntegral (q^n) := by
  simpa only [TwoIntegral, Rat.den_pow] using (show Odd (q.den^n) from Odd.pow hq)
lemma twoIntegral_inv_odd_nat (n : ℕ) (hn : Odd n) : TwoIntegral ((n : ℚ)⁻¹) := by
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
  simpa only [TwoIntegral, Rat.inv_natCast_den, ite_eq_right hn0] using hn
lemma TwoIntegral.div_odd_nat {q : ℚ} (hq : TwoIntegral q) (n : ℕ) (hn : Odd n) :
    TwoIntegral (q / n) := by
  simpa only [div_eq_mul_inv] using hq.mul (twoIntegral_inv_odd_nat n hn)
lemma TwoIntegral.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, TwoIntegral (f i)) : TwoIntegral (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using twoIntegral_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma ModFour.refl (q : ℚ) : ModFour q q :=
  ⟨0, twoIntegral_zero, by ring⟩
lemma ModFour.add {q r u v : ℚ} (h : ModFour q r) (h' : ModFour u v) :
    ModFour (q+u) (r+v) := by
  obtain ⟨t, ht, he⟩ := h
  obtain ⟨s, hs, he'⟩ := h'
  exact ⟨t+s, ht.add hs, by linarith⟩
lemma ModFour.sub {q r u v : ℚ} (h : ModFour q r) (h' : ModFour u v) :
    ModFour (q-u) (r-v) := by
  obtain ⟨t, ht, he⟩ := h
  obtain ⟨s, hs, he'⟩ := h'
  exact ⟨t-s, ht.sub hs, by linarith⟩
lemma ModFour.trans {q r u : ℚ} (h : ModFour q r) (h' : ModFour r u) :
    ModFour q u := by
  obtain ⟨t, ht, he⟩ := h
  obtain ⟨s, hs, he'⟩ := h'
  exact ⟨t+s, ht.add hs, by linarith⟩
lemma ModFour.mul_left {q r : ℚ} (h : ModFour q r) (s : ℚ) (hs : TwoIntegral s) :
    ModFour (s*q) (s*r) := by
  obtain ⟨t, ht, he⟩ := h
  refine ⟨s*t, hs.mul ht, ?_⟩
  calc s*q-s*r = s*(q-r) := by ring
       _ = 4*(s*t) := by rw [he]; ring
lemma ModFour.sum {ι : Type*} (s : Finset ι) (f g : ι → ℚ)
    (h : ∀ i ∈ s, ModFour (f i) (g i)) :
    ModFour (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ModFour.refl 0
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
lemma ModFour.cancel_odd_nat {q r : ℚ} (n : ℕ) (hn : Odd n)
    (h : ModFour ((n : ℚ)*q) ((n : ℚ)*r)) : ModFour q r := by
  obtain ⟨t, ht, he⟩ := h
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  refine ⟨t/n, ht.div_odd_nat n hn, ?_⟩
  apply mul_right_cancel₀ hnQ
  calc (q-r)*n = n*q-n*r := by ring
       _ = 4*t := he
       _ = (4*(t/n))*n := by field_simp
lemma ModFour.twoIntegral {q r : ℚ} (h : ModFour q r) (hr : TwoIntegral r) :
    TwoIntegral q := by
  obtain ⟨t, ht, he⟩ := h
  have hq : q = r + 4*t := by linarith
  rw [hq]
  exact hr.add ((twoIntegral_nat 4).mul ht)

/-- The doubled even Bernoulli numbers, with the standard negative B₁ convention. -/
def twiceBernoulli (m : ℕ) : ℚ := 2 * bernoulli (2*m)

lemma sum_range_even_odd (f : ℕ → ℚ) (m : ℕ) :
    (∑ k ∈ Finset.range (2*m), f k) =
      ∑ j ∈ Finset.range m, (f (2*j) + f (2*j+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ]
    simp only [Finset.sum_range_succ] at *
    rw [ih]
    ring

/-- Removing the zero and odd Bernoulli terms gives an odd leading coefficient. -/
theorem twiceBernoulli_recurrence (m : ℕ) (hm : 0 < m) :
    (2*(m : ℚ)+1) * twiceBernoulli m = 2*(m : ℚ)-1 -
      ∑ j ∈ Finset.Ico 1 m, ((2*m+1).choose (2*j) : ℚ) * twiceBernoulli j := by
  have ho : (∑ j ∈ Finset.range m,
      ((2*m+1).choose (2*j+1) : ℚ) * bernoulli (2*j+1)) = -(2*(m : ℚ)+1)/2 := by
    rw [Finset.sum_eq_single 0]
    · simp [bernoulli_one]
      ring
    · intro j hj hj0
      rw [bernoulli_eq_zero_of_odd ⟨j, by omega⟩ (by omega), mul_zero]
    · intro h
      exact (h (Finset.mem_range.mpr hm)).elim
  have he : (∑ j ∈ Finset.range m,
      ((2*m+1).choose (2*j) : ℚ) * bernoulli (2*j)) =
      1 + ∑ j ∈ Finset.Ico 1 m, ((2*m+1).choose (2*j) : ℚ) * bernoulli (2*j) := by
    rw [Finset.sum_range_eq_add_Ico _ hm]
    simp
  have hs := sum_bernoulli (2*m+1)
  rw [ite_eq_right (by omega : 2*m+1 ≠ 1), Finset.sum_range_succ,
    sum_range_even_odd, Finset.sum_add_distrib, he, ho] at hs
  simp only [Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one] at hs
  have hscale : (∑ j ∈ Finset.Ico 1 m,
      ((2*m+1).choose (2*j) : ℚ) * twiceBernoulli j) =
      2 * ∑ j ∈ Finset.Ico 1 m, ((2*m+1).choose (2*j) : ℚ) * bernoulli (2*j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [twiceBernoulli]
    ring
  rw [hscale]
  dsimp [twiceBernoulli]
  linarith

/-- The sum of the even entries in an odd binomial row is a power of two. -/
theorem sum_even_choose (m : ℕ) :
    (∑ j ∈ Finset.range (m+1), ((2*m+1).choose (2*j) : ℚ)) = (2 : ℚ)^(2*m) := by
  have ht : (∑ k ∈ Finset.range (2*m+2), ((2*m+1).choose k : ℚ)) =
      (2 : ℚ)^(2*m+1) := by
    exact_mod_cast Nat.sum_range_choose (2*m+1)
  have ha : (∑ k ∈ Finset.range (2*m+2), (-1 : ℚ)^k * ((2*m+1).choose k : ℚ)) = 0 := by
    exact_mod_cast (Int.alternating_sum_range_choose_of_ne (by omega : 2*m+1 ≠ 0))
  rw [show 2*m+2 = 2*(m+1) by omega, sum_range_even_odd,
    Finset.sum_add_distrib] at ht ha
  simp [pow_add, pow_mul, Finset.sum_neg_distrib] at ha
  rw [pow_succ] at ht
  linarith

/-- Removing the two endpoint terms gives the exact inner even-binomial sum. -/
theorem sum_inner_even_choose (m : ℕ) (hm : 0 < m) :
    (∑ j ∈ Finset.Ico 1 m, ((2*m+1).choose (2*j) : ℚ)) =
      (2 : ℚ)^(2*m) - (2*(m : ℚ)+2) := by
  have h := sum_even_choose m
  rw [Finset.sum_range_succ, Finset.sum_range_eq_add_Ico _ hm] at h
  simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.cast_one,
    Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
  linarith

/-- The corrected inner binomial sum is always two modulo four. -/
theorem corrected_inner_choose_modFour (m : ℕ) (hm : 2 ≤ m) :
    ModFour ((∑ j ∈ Finset.Ico 1 m, ((2*m+1).choose (2*j) : ℚ)) +
      2*((2*m+1).choose 2 : ℚ)) 2 := by
  refine ⟨(2 : ℚ)^(2*m-2)+(m : ℚ)^2-1, ?_, ?_⟩
  · exact (((twoIntegral_nat 2).pow (2*m-2)).add ((twoIntegral_nat m).pow 2)).sub
      twoIntegral_one
  · rw [sum_inner_even_choose m (by omega), Nat.cast_choose_two]
    push_cast
    have hp : (2 : ℚ)^(2*m) = 4*(2 : ℚ)^(2*m-2) := by
      conv_lhs => rw [show 2*m = (2*m-2)+2 by omega, pow_add]
      ring
    rw [hp]
    ring

/-- The exceptional first even Bernoulli number has residue three. -/
theorem twiceBernoulli_one_modFour_three : ModFour (twiceBernoulli 1) 3 := by
  refine ⟨-2/3, ?_, ?_⟩
  · norm_num [TwoIntegral]
    decide
  · norm_num [twiceBernoulli, bernoulli_two]

/-- All positive even Bernoulli indices satisfy the exact mod-four residue law. -/
theorem twiceBernoulli_modFour : ∀ m : ℕ, 0 < m →
    ModFour (twiceBernoulli m) (if m = 1 then 3 else 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hm1 : m = 1
    · subst m
      simpa using twiceBernoulli_one_modFour_three
    have hm2 : 2 ≤ m := by omega
    rw [ite_eq_right hm1]
    have hs := ModFour.sum (Finset.Ico 1 m)
      (fun j => ((2*m+1).choose (2*j) : ℚ) * twiceBernoulli j)
      (fun j => ((2*m+1).choose (2*j) : ℚ) * (if j = 1 then 3 else 1))
      (fun j hj => (ih j (Finset.mem_Ico.mp hj).2 (by
        have := (Finset.mem_Ico.mp hj).1
        omega)).mul_left _ (twoIntegral_nat _))
    have he : (∑ j ∈ Finset.Ico 1 m,
        ((2*m+1).choose (2*j) : ℚ) * (if j = 1 then 3 else 1)) =
        (∑ j ∈ Finset.Ico 1 m, ((2*m+1).choose (2*j) : ℚ)) +
          2*((2*m+1).choose 2 : ℚ) := by
      have ht (j : ℕ) : ((2*m+1).choose (2*j) : ℚ) * (if j = 1 then 3 else 1) =
          ((2*m+1).choose (2*j) : ℚ) +
            (if j = 1 then 2*((2*m+1).choose (2*j) : ℚ) else 0) := by
        split_ifs <;> ring
      simp_rw [ht]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [Finset.mem_Ico, show 1 < m by omega]
    rw [he] at hs
    have hs2 := hs.trans (corrected_inner_choose_modFour m hm2)
    have hrec : ModFour ((2*(m : ℚ)+1)*twiceBernoulli m) (2*(m : ℚ)-3) := by
      rw [twiceBernoulli_recurrence m hm]
      convert (ModFour.refl (2*(m : ℚ)-1)).sub hs2 using 1; ring
    have hrhs : ModFour (2*(m : ℚ)-3) (2*(m : ℚ)+1) :=
      ⟨-1, twoIntegral_one.neg, by ring⟩
    apply ModFour.cancel_odd_nat (2*m+1) ⟨m, by omega⟩
    simpa using hrec.trans hrhs

/-- In every index the doubled even Bernoulli number has odd denominator. -/
theorem twiceBernoulli_twoIntegral (m : ℕ) : TwoIntegral (twiceBernoulli m) := by
  by_cases hm : m = 0
  · subst m
    norm_num [twiceBernoulli, TwoIntegral]
  · apply (twiceBernoulli_modFour m (by omega)).twoIntegral
    split_ifs
    · exact twoIntegral_nat 3
    · exact twoIntegral_one

/-- From the second positive even index onward the residue is one modulo four. -/
theorem twiceBernoulli_modFour_one (m : ℕ) (hm : 2 ≤ m) :
    ModFour (twiceBernoulli m) 1 := by
  simpa only [ite_eq_right (by omega : m ≠ 1)] using twiceBernoulli_modFour m (by omega)

end TernaryPoly.BernoulliTwoIntegral
