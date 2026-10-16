module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3CosetsConj

@[expose] public section


/-!
# The orbits of `T` and `L` on the Hecke cosets of `Γ₁'(3)`, and their transitions

Let `T = upper 1 = [[1,1],[0,1]]` and `L = lower 1 = [[1,0],[3,1]]`, the two cusp generators of
`Γ₁(3)`; `S = levelCosets p hp3` has index type `Option (Fin p)` (`α_∞ = none`, `α_b = some b`) and
base coset `baseIdx p = some 0`.

**`T`.**  `T` fixes the coset `∞` (`levelNext_upper_none`, transition `T^p`), permutes the cosets
`α_b` cyclically (`b ↦ b + 1`, transition `1`, except `α_{p-1} T = T α_0` with transition `T`:
`levelNext_upper_some`, `levelNext_upper_last`).  With the transversal `transv` the transitions
`r_j T r_{jT}⁻¹` are `1` (`transit_upper_some`), `T^p` (`transit_upper_last`) and
`s⁻¹ T s` (`transit_upper_none`); `sum_option_last` reduces a sum over the cosets to the last coset
and the cusp coset.

**`L`.**  `L` fixes the base coset (`levelNext_lower_base`, transition `L^p`, transit `L`) and
permutes the other `p` cosets in one cycle through `∞`: `cycleL i = (next L)^i ∞`,
`i = 0, …, p - 1` (`cycleL_injective`, `cycleL_ne_base`, `levelNext_lower_cycle`,
`levelNext_lower_last`, with `L^n ∞ = ∞` iff `p ∣ n`: `levelNext_lower_none_iff`).
`sum_option_cycle` reduces a sum over the cosets to the base coset and the cycle, and
`transit_lower_pow_none` is the transit `s⁻¹ L^p s` of the full cycle.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

section Basics

theorem upper_zero : upper 0 = 1 := by
  rw [upper_zpow 0, zpow_zero]

theorem lower_zero : lower 0 = 1 := by
  rw [lower_zpow 0, zpow_zero]

theorem levelNext_mul (g h : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    levelNext p hp3 (g * h) j = levelNext p hp3 h (levelNext p hp3 g j) :=
  (levelCosets p hp3).next_mul g h j

theorem levelNext_one (j : Option (Fin p.val)) : levelNext p hp3 1 j = j :=
  AdjCore.next_one (levelCosets p hp3) j

/-- The transition of `g` at `j`, as an element of the stabilizer of the base coset, along the
transversal `transv`. -/
abbrev transitL3 (g : binaryArithmeticLevel) (j : Option (Fin p.val)) : stabH p hp3 :=
  AdjCore.transit (S := levelCosets p hp3) (j₀ := baseIdx p) (transv p hp3)
    (levelNext_transv p hp3) g j

theorem transitL3_val (g : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    (transitL3 p hp3 g j : binaryArithmeticLevel) =
      transv p hp3 j * g * (transv p hp3 (levelNext p hp3 g j))⁻¹ := rfl

end Basics

section TOrbit

theorem upper_val_one :
    (((upper 1).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 1; 0, 1] := rfl

/-- `T` carries the coset `α_b`, `b + 1 < p`, to `α_{b+1}`, with trivial transition. -/
theorem levelNext_upper_some (b : Fin p.val) (hb : b.val + 1 < p.val) :
    levelNext p hp3 (upper 1) (some b) = some ⟨b.val + 1, hb⟩ := by
  refine levelNext_eq_of_mul p hp3 _ 1 _ _ ?_
  have h1 : (((1 : binaryArithmeticLevel).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
    rfl
  rw [h1, Matrix.one_mul, N_some, N_some, upper_val_one, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by push_cast; ring) (by ring) (by ring)

theorem levelDelta_upper_some (b : Fin p.val) (hb : b.val + 1 < p.val) :
    levelDelta p hp3 (upper 1) (some b) = 1 := by
  refine levelDelta_eq_of_mul p hp3 _ 1 _ (some ⟨b.val + 1, hb⟩) ?_
  have h1 : (((1 : binaryArithmeticLevel).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
    rfl
  rw [h1, Matrix.one_mul, N_some, N_some, upper_val_one, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by push_cast; ring) (by ring) (by ring)

/-- The last coset index `p - 1`. -/
def lastIdx : Fin p.val := ⟨p.val - 1, Nat.sub_lt p.property.pos one_pos⟩

/-- `T` carries the last coset `α_{p-1}` to the base coset, with transition `T`. -/
theorem levelNext_upper_last : levelNext p hp3 (upper 1) (some (lastIdx p)) = baseIdx p := by
  refine levelNext_eq_of_mul p hp3 _ (upper 1) _ _ ?_
  have hp := p.property.pos
  have hc : (((lastIdx p).val : ℕ) : ℤ) = (p.val : ℤ) - 1 := by
    show (((p.val - 1 : ℕ)) : ℤ) = _
    omega
  rw [baseIdx, N_some, N_some, upper_val_one, hc, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by push_cast; ring) (by ring) (by ring)

theorem levelDelta_upper_last : levelDelta p hp3 (upper 1) (some (lastIdx p)) = upper 1 := by
  refine levelDelta_eq_of_mul p hp3 _ (upper 1) _ (baseIdx p) ?_
  have hp := p.property.pos
  have hc : (((lastIdx p).val : ℕ) : ℤ) = (p.val : ℤ) - 1 := by
    show (((p.val - 1 : ℕ)) : ℤ) = _
    omega
  rw [baseIdx, N_some, N_some, upper_val_one, hc, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by push_cast; ring) (by ring) (by ring)

/-- `T` fixes the coset `∞`, with transition `T^p`. -/
theorem levelNext_upper_none : levelNext p hp3 (upper 1) none = none := by
  refine levelNext_eq_of_mul p hp3 _ (upper (p.val : ℤ)) _ _ ?_
  rw [N_none, upper_val, upper_val_one, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

theorem levelDelta_upper_none : levelDelta p hp3 (upper 1) none = upper (p.val : ℤ) := by
  refine levelDelta_eq_of_mul p hp3 _ (upper (p.val : ℤ)) _ none ?_
  rw [N_none, upper_val, upper_val_one, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

/-- The transition of `T` at a coset `α_b`, `b + 1 < p`, is trivial. -/
theorem transit_upper_some (b : Fin p.val) (hb : b.val + 1 < p.val) :
    (transitL3 p hp3 (upper 1) (some b) : binaryArithmeticLevel) = 1 := by
  rw [transitL3_val, levelNext_upper_some p hp3 b hb, transv_some, transv_some]
  show upper (b.val : ℤ) * upper 1 * (upper ((b.val + 1 : ℕ) : ℤ))⁻¹ = 1
  rw [upper_mul, Nat.cast_add, Nat.cast_one]
  exact mul_inv_cancel _

/-- The transition of `T` at the last coset is `T^p`. -/
theorem transit_upper_last :
    (transitL3 p hp3 (upper 1) (some (lastIdx p)) : binaryArithmeticLevel) =
      upper (p.val : ℤ) := by
  have hp := p.property.pos
  have hc : (((lastIdx p).val : ℕ) : ℤ) = (p.val : ℤ) - 1 := by
    show (((p.val - 1 : ℕ)) : ℤ) = _
    omega
  rw [transitL3_val, levelNext_upper_last p hp3, transv_some, baseIdx, transv_some]
  show upper (((lastIdx p).val : ℕ) : ℤ) * upper 1 * (upper (((0 : ℕ)) : ℤ))⁻¹ = _
  rw [upper_mul, hc, Nat.cast_zero, upper_zero, inv_one, mul_one, sub_add_cancel]

/-- The transition of `T` at the cusp coset is `s⁻¹ T s`. -/
theorem transit_upper_none :
    (transitL3 p hp3 (upper 1) none : binaryArithmeticLevel) =
      sInv p hp3 * upper 1 * sF p hp3 := by
  rw [transitL3_val, levelNext_upper_none p hp3, transv_none, sF_eq_inv p hp3]

/-- A sum over the cosets of a function vanishing at the cosets `α_b` with `b + 1 < p` is the sum
of its values at the last coset and at the cusp coset. -/
theorem sum_option_last {M : Type*} [AddCommMonoid M] (F : Option (Fin p.val) → M)
    (hF : ∀ b : Fin p.val, b.val + 1 < p.val → F (some b) = 0) :
    ∑ j, F j = F (some (lastIdx p)) + F none := by
  have hsum : ∑ b : Fin p.val, F (some b) = F (some (lastIdx p)) := by
    apply Finset.sum_eq_single (lastIdx p)
    · intro b _ hb
      apply hF b
      have hb' : b.val ≠ p.val - 1 := fun h => hb (Fin.ext h)
      have := b.isLt
      omega
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [Fintype.sum_option, hsum]
  exact add_comm _ _

end TOrbit

section LOrbit

theorem lower_val_one :
    (((lower 1).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 3, 1] := rfl

/-- `L^n` fixes the base coset, with transition `L^{p n}`. -/
theorem levelNext_lower_base (n : ℤ) : levelNext p hp3 (lower n) (baseIdx p) = baseIdx p := by
  refine levelNext_eq_of_mul p hp3 _ (lower ((p.val : ℤ) * n)) _ _ ?_
  rw [N_baseIdx, lower_val, lower_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

theorem levelDelta_lower_base (n : ℤ) :
    levelDelta p hp3 (lower n) (baseIdx p) = lower ((p.val : ℤ) * n) := by
  refine levelDelta_eq_of_mul p hp3 _ (lower ((p.val : ℤ) * n)) _ (baseIdx p) ?_
  rw [N_baseIdx, lower_val, lower_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

/-- The transition of `L` at the base coset is `L`. -/
theorem transit_lower_base :
    (transitL3 p hp3 (lower 1) (baseIdx p) : binaryArithmeticLevel) = lower 1 := by
  rw [transitL3_val, levelNext_lower_base p hp3, baseIdx, transv_some]
  show upper (((0 : ℕ)) : ℤ) * lower 1 * (upper (((0 : ℕ)) : ℤ))⁻¹ = lower 1
  rw [Nat.cast_zero, upper_zero, inv_one, one_mul, mul_one]

include hp3 in
/-- **`L^n` fixes the coset `∞` iff `p ∣ n`.** -/
theorem levelNext_lower_none_iff (n : ℤ) :
    levelNext p hp3 (lower n) none = none ↔ (p.val : ℤ) ∣ n := by
  have he := eps_mul_self p
  constructor
  · intro hn
    have spec := levelDelta_spec p hp3 (lower n) none
    rw [hn, N_none, lower_val] at spec
    have e : (levelDelta p hp3 (lower n) none).val.val 1 0 * ((eps p) * p.val) =
        (eps p) * (3 * n) := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun spec 1) 0
    have e2 : (p.val : ℤ) * (levelDelta p hp3 (lower n) none).val.val 1 0 = 3 * n := by
      linear_combination (eps p) * e +
        (3 * n - (p.val : ℤ) * (levelDelta p hp3 (lower n) none).val.val 1 0) * he
    have hd : (p.val : ℤ) ∣ 3 * n := ⟨_, e2.symm⟩
    have hpz : Prime (p.val : ℤ) := Nat.prime_iff_prime_int.mp p.property
    rcases hpz.dvd_or_dvd hd with h3 | hn'
    · exfalso
      have h3' : p.val ∣ 3 := by exact_mod_cast h3
      exact hp3 ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_three).mp h3')
    · exact hn'
  · rintro ⟨m, rfl⟩
    refine levelNext_eq_of_mul p hp3 _ (lower m) _ _ ?_
    rw [N_none, lower_val, lower_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
    exact mat2_eq (by ring) (by ring) (by ring) (by ring)

/-- The coset `(L^i)` applied to `∞`, `i = 0, …, p - 1`: the `p`-cycle of `L`. -/
def cycleL (i : Fin p.val) : Option (Fin p.val) := levelNext p hp3 (lower (i.val : ℤ)) none

theorem cycleL_zero (hp : 0 < p.val) : cycleL p hp3 ⟨0, hp⟩ = none := by
  show levelNext p hp3 (lower (((0 : ℕ)) : ℤ)) none = none
  rw [Nat.cast_zero, lower_zero, levelNext_one]

/-- `L` carries the `i`-th coset of the cycle to the `(i+1)`-st. -/
theorem levelNext_lower_cycle (i : Fin p.val) (hi : i.val + 1 < p.val) :
    levelNext p hp3 (lower 1) (cycleL p hp3 i) = cycleL p hp3 ⟨i.val + 1, hi⟩ := by
  unfold cycleL
  rw [← levelNext_mul, lower_mul]
  congr 2

/-- `L` carries the last coset of the cycle back to `∞`. -/
theorem levelNext_lower_last :
    levelNext p hp3 (lower 1) (cycleL p hp3 (lastIdx p)) = none := by
  unfold cycleL
  rw [← levelNext_mul, lower_mul, levelNext_lower_none_iff p hp3]
  have hp := p.property.pos
  have hc : (((lastIdx p).val : ℕ) : ℤ) = (p.val : ℤ) - 1 := by
    show (((p.val - 1 : ℕ)) : ℤ) = _
    omega
  rw [hc, sub_add_cancel]

theorem levelNext_lower_neg_cycle (i : Fin p.val) :
    levelNext p hp3 (lower (-(i.val : ℤ))) (cycleL p hp3 i) = none := by
  unfold cycleL
  rw [← levelNext_mul, lower_mul, add_neg_cancel, lower_zero, levelNext_one]

theorem cycleL_injective : Function.Injective (cycleL p hp3) := by
  intro i j hij
  have h1 := levelNext_lower_neg_cycle p hp3 i
  rw [hij] at h1
  unfold cycleL at h1
  rw [← levelNext_mul, lower_mul] at h1
  have hd := (levelNext_lower_none_iff p hp3 _).mp h1
  have hi := i.isLt
  have hj := j.isLt
  have hlt : |(j.val : ℤ) + -(i.val : ℤ)| < p.val := by
    rw [abs_lt]
    constructor <;> omega
  have hz := Int.eq_zero_of_abs_lt_dvd hd hlt
  exact Fin.ext (by omega)

theorem cycleL_ne_base (i : Fin p.val) : cycleL p hp3 i ≠ baseIdx p := by
  intro h
  have h1 := levelNext_lower_neg_cycle p hp3 i
  rw [h, levelNext_lower_base] at h1
  exact absurd h1 (by simp [baseIdx])

/-- **A sum over the cosets is the value at the base coset plus the sum over the `p`-cycle of
`L`.** -/
theorem sum_option_cycle {M : Type*} [AddCommMonoid M] (F : Option (Fin p.val) → M) :
    ∑ j, F j = F (baseIdx p) + ∑ i : Fin p.val, F (cycleL p hp3 i) := by
  let σ : Option (Fin p.val) → Option (Fin p.val) := fun j =>
    match j with
    | none => baseIdx p
    | some i => cycleL p hp3 i
  have hinj : Function.Injective σ := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j => exact absurd hab (cycleL_ne_base p hp3 j).symm
    | some i =>
      cases b with
      | none => exact absurd hab (cycleL_ne_base p hp3 i)
      | some j => exact congrArg some (cycleL_injective p hp3 hab)
  have hbij := Finite.injective_iff_bijective.mp hinj
  let e := Equiv.ofBijective σ hbij
  calc ∑ j, F j = ∑ j, F (e j) := (Equiv.sum_comp e F).symm
    _ = F (baseIdx p) + ∑ i, F (cycleL p hp3 i) := by
      rw [Fintype.sum_option]
      rfl

/-- The transit of the full cycle `L^p` at the cusp coset is `s⁻¹ L^p s`. -/
theorem transit_lower_pow_none :
    (transitL3 p hp3 (lower (p.val : ℤ)) none : binaryArithmeticLevel) =
      sInv p hp3 * lower (p.val : ℤ) * sF p hp3 := by
  rw [transitL3_val, (levelNext_lower_none_iff p hp3 _).mpr (dvd_refl _), transv_none,
    sF_eq_inv p hp3]

end LOrbit

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
