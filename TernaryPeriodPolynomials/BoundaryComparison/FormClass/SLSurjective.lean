module

public import Mathlib

@[expose] public section


/-!
# Surjectivity of `SL₂(ℤ) → SL₂(ℤ/N)` and `SL₃(ℤ) → SL₃(ℤ/N)`

Formalized by Claude Sonnet 5.5.

Mathlib has transvection generation only over fields; this file gives the integral statement by a direct argument.
* `exists_coprime_shift`: if `a, b, N` have no common prime factor and `b ≠ 0`, some `a + N t` is coprime to `b`.
* `exists_prim_lift2`, `exists_prim_lift3`: a unimodular pair/triple modulo `N` has a coprime/primitive integral lift.
* `exists_sl3_first_col`: a primitive vector of `ℤ³` is the first column of an element of `SL₃(ℤ)`.
* **`sl2_map_surjective`**, **`sl3_map_surjective`**: `SL_n(ℤ) → SL_n(ℤ/N)` is onto (`n = 2, 3`); for `n = 3` the first column is lifted to a primitive vector, completed to `T ∈ SL₃(ℤ)`, and the remaining `SL₂` block is lifted.
-/

open Finset
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

/-- Shifting `a` by a multiple of `N` makes it coprime to `b ≠ 0`, provided `a, b, N` have no common prime factor. -/
theorem exists_coprime_shift (a b N : ℤ) (hb : b ≠ 0)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b → (p : ℤ) ∣ N → False) :
    ∃ t : ℤ, IsCoprime (a + N * t) b := by
  classical
  let S : Finset ℕ := b.natAbs.primeFactors.filter (fun p => ¬ (p : ℤ) ∣ a)
  refine ⟨∏ p ∈ S, (p : ℤ), ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : (p : ℤ) ∣ a + N * ∏ q ∈ S, (q : ℤ) := (Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_left _ _)
  have h2 : (p : ℤ) ∣ b := (Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_right _ _)
  by_cases hpa : (p : ℤ) ∣ a
  · have h3 : (p : ℤ) ∣ N * ∏ q ∈ S, (q : ℤ) := (dvd_add_right hpa).1 h1
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rcases hpp.dvd_or_dvd h3 with h4 | h4
    · exact h p hp hpa h2 h4
    · obtain ⟨q, hqS, hq⟩ := (Prime.dvd_finsetProd_iff hpp _).1 h4
      have hq' : q ∈ b.natAbs.primeFactors ∧ ¬ (q : ℤ) ∣ a := Finset.mem_filter.1 hqS
      have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hq'.1
      have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).1 (Int.natCast_dvd_natCast.1 hq)
      exact hq'.2 (this ▸ hpa)
  · have hpS : p ∈ S := by
      refine Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, ?_, hb |> fun hb' => Int.natAbs_ne_zero.2 hb'⟩, hpa⟩
      exact Int.natCast_dvd.1 h2
    have h3 : (p : ℤ) ∣ ∏ q ∈ S, (q : ℤ) := Finset.dvd_prod_of_mem _ hpS
    have h4 : (p : ℤ) ∣ N * ∏ q ∈ S, (q : ℤ) := h3.mul_left N
    exact hpa ((dvd_add_left h4).1 h1)


/-- A unimodular pair modulo `N` has a coprime integral lift. -/
theorem exists_prim_lift2 (a c N : ℤ) (hN : N ≠ 0) (h : ∃ x y s : ℤ, x * a + y * c + s * N = 1) :
    ∃ k l : ℤ, IsCoprime (a + N * k) (c + N * l) := by
  obtain ⟨x, y, s, hxy⟩ := h
  have hl : ∃ l : ℤ, c + N * l ≠ 0 := by
    by_cases hc : c = 0
    · exact ⟨1, by simp [hc, hN]⟩
    · exact ⟨0, by simpa using hc⟩
  obtain ⟨l, hl⟩ := hl
  obtain ⟨k, hk⟩ := exists_coprime_shift a (c + N * l) N hl (fun p hp hpa hpc hpN => by
    have hpc' : (p : ℤ) ∣ c := by
      have : (p : ℤ) ∣ N * l := hpN.mul_right l
      exact (dvd_add_left this).1 hpc
    have : (p : ℤ) ∣ 1 := by
      rw [← hxy]
      exact dvd_add (dvd_add (hpa.mul_left x) (hpc'.mul_left y)) (hpN.mul_left s)
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this))
  exact ⟨k, l, hk⟩

/-- A unimodular triple modulo `N` has a primitive integral lift. -/
theorem exists_prim_lift3 (a b c N : ℤ) (hN : N ≠ 0) (h : ∃ x y z s : ℤ, x * a + y * b + z * c + s * N = 1) :
    ∃ k l m : ℤ, ∃ x y z : ℤ, x * (a + N * k) + y * (b + N * l) + z * (c + N * m) = 1 := by
  obtain ⟨x, y, z, s, hxy⟩ := h
  have hm : ∃ m : ℤ, c + N * m ≠ 0 := by
    by_cases hc : c = 0
    · exact ⟨1, by simp [hc, hN]⟩
    · exact ⟨0, by simpa using hc⟩
  obtain ⟨m, hm⟩ := hm
  -- `g = gcd (b) (c + N m)` may vanish only if `b = 0`; we use `b' = b` and handle via `d = gcd`.
  set c' := c + N * m with hc'
  have hg : (Int.gcd b c' : ℤ) ≠ 0 := by
    intro h0
    have : Int.gcd b c' = 0 := by exact_mod_cast h0
    exact hm (Int.gcd_eq_zero_iff.1 this).2
  obtain ⟨k, hk⟩ := exists_coprime_shift a (Int.gcd b c' : ℤ) N hg (fun p hp hpa hpg hpN => by
    have hpb : (p : ℤ) ∣ b := hpg.trans (Int.gcd_dvd_left _ _)
    have hpc2 : (p : ℤ) ∣ c' := hpg.trans (Int.gcd_dvd_right _ _)
    have hpc : (p : ℤ) ∣ c := by
      have : (p : ℤ) ∣ N * m := hpN.mul_right m
      exact (dvd_add_left this).1 hpc2
    have : (p : ℤ) ∣ 1 := by
      rw [← hxy]
      exact dvd_add (dvd_add (dvd_add (hpa.mul_left x) (hpb.mul_left y)) (hpc.mul_left z)) (hpN.mul_left s)
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this))
  obtain ⟨u, v, huv⟩ := hk
  -- `u (a + N k) + v gcd(b, c') = 1`, and `gcd(b, c') = α b + β c'`.
  obtain ⟨α, β, hαβ⟩ : ∃ α β : ℤ, α * b + β * c' = (Int.gcd b c' : ℤ) := ⟨Int.gcdA b c', Int.gcdB b c', by
    rw [mul_comm, mul_comm (Int.gcdB b c')]; exact (Int.gcd_eq_gcd_ab b c').symm⟩
  refine ⟨k, 0, m, u, v * α, v * β, ?_⟩
  simp only [mul_zero, add_zero]
  calc u * (a + N * k) + v * α * b + v * β * c' = u * (a + N * k) + v * (α * b + β * c') := by ring
    _ = 1 := by rw [hαβ]; exact huv


section SL2

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem zmod_int_cast_cast (z : ZMod N) : (((ZMod.cast z : ℤ)) : ZMod N) = z := ZMod.intCast_zmod_cast z

omit [NeZero N] in
theorem exists_int_bezout_of_zmod {n : ℕ} (a : Fin n → ZMod N) (x : Fin n → ZMod N) (h : ∑ i, x i * a i = 1) :
    ∃ (X : Fin n → ℤ) (s : ℤ), ∑ i, X i * (ZMod.cast (a i) : ℤ) + s * N = 1 := by
  refine ⟨fun i => (ZMod.cast (x i) : ℤ), ?_⟩
  have h0 : (((∑ i, (ZMod.cast (x i) : ℤ) * (ZMod.cast (a i) : ℤ)) - 1 : ℤ) : ZMod N) = 0 := by
    simp only [Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_one, zmod_int_cast_cast]
    rw [h]; ring
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 h0
  exact ⟨-k, by linarith⟩

/-- **`SL₂(ℤ) → SL₂(ℤ/N)` is surjective.** -/
theorem sl2_map_surjective :
    Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) : SL(2, ℤ) →* SL(2, ZMod N)) := by
  intro B
  have hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    have := B.2
    rw [Matrix.det_fin_two] at this
    exact this
  set a := B 0 0 with ha
  set b := B 0 1 with hb
  set c := B 1 0 with hc
  set d := B 1 1 with hd
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  obtain ⟨X, s, hX⟩ := exists_int_bezout_of_zmod N (![a, c]) (![d, -b]) (by
    simp [Fin.sum_univ_two]; linear_combination hdet)
  obtain ⟨k, l, hk⟩ := exists_prim_lift2 (ZMod.cast a : ℤ) (ZMod.cast c : ℤ) N hN
    ⟨X 0, X 1, s, by simpa [Fin.sum_univ_two] using hX⟩
  set a' : ℤ := (ZMod.cast a : ℤ) + N * k with ha'
  set c' : ℤ := (ZMod.cast c : ℤ) + N * l with hc'
  obtain ⟨u, v, huv⟩ := hk
  have hA : ((a' : ℤ) : ZMod N) = a := by simp [ha']
  have hC : ((c' : ℤ) : ZMod N) = c := by simp [hc']
  have huv' : (u : ZMod N) * a + (v : ZMod N) * c = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) huv
    push_cast at this
    rw [hA, hC] at this
    exact this
  -- the correction `s̄ = d v + b u`
  set s' : ZMod N := d * (v : ZMod N) + b * (u : ZMod N) with hs'
  have hsa : s' * a = b + (v : ZMod N) := by
    simp only [hs']
    linear_combination (v : ZMod N) * hdet + b * huv'
  have hsc : s' * c = d - (u : ZMod N) := by
    simp only [hs']
    linear_combination d * huv' - (u : ZMod N) * hdet
  set S : ℤ := ZMod.cast s' with hS
  have hSc : ((S : ℤ) : ZMod N) = s' := zmod_int_cast_cast N s'
  have hdetZ : a' * (u + c' * S) - (-v + a' * S) * c' = 1 := by linear_combination huv
  obtain ⟨M, hM⟩ : ∃ M : SL(2, ℤ), (M : Matrix (Fin 2) (Fin 2) ℤ) = !![a', -v + a' * S; c', u + c' * S] :=
    ⟨⟨!![a', -v + a' * S; c', u + c' * S], by rw [Matrix.det_fin_two_of]; linear_combination hdetZ⟩, rfl⟩
  refine ⟨M, ?_⟩
  apply Subtype.ext
  ext i j
  have key : ∀ (M : SL(2, ℤ)) (i j : Fin 2),
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) M : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) i j =
        ((M.1 i j : ℤ) : ZMod N) := fun _ _ _ => rfl
  rw [key, hM]
  fin_cases i <;> fin_cases j
  · simpa using hA
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    push_cast
    rw [hA, hSc]
    linear_combination hsa
  · simpa using hC
  · simp only [Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    push_cast
    rw [hC, hSc]
    linear_combination hsc

end SL2


section SL3

/-- A primitive vector of `ℤ³` (Bezout form) is the first column of an element of `SL₃(ℤ)`. -/
theorem exists_sl3_first_col (c : Fin 3 → ℤ) (h : ∃ x : Fin 3 → ℤ, ∑ i, x i * c i = 1) :
    ∃ T : SL(3, ℤ), ∀ i, (T : Matrix (Fin 3) (Fin 3) ℤ) i 0 = c i := by
  obtain ⟨x, hx⟩ := h
  simp only [Fin.sum_univ_three] at hx
  by_cases hd : Int.gcd (c 0) (c 1) = 0
  · have h0 : c 0 = 0 ∧ c 1 = 0 := Int.gcd_eq_zero_iff.1 hd
    have h2 : x 2 * c 2 = 1 := by rw [h0.1, h0.2] at hx; linarith
    have h22 : c 2 * c 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h4] <;> norm_num
    refine ⟨⟨!![0, 1, 0; 0, 0, c 2; c 2, 0, 0], ?_⟩, fun i => ?_⟩
    · rw [Matrix.det_fin_three]; simp; linear_combination h22
    · fin_cases i <;> simp [h0.1, h0.2]
  · have hdpos : (0 : ℤ) < Int.gcd (c 0) (c 1) := by exact_mod_cast Nat.pos_of_ne_zero hd
    set d : ℤ := (Int.gcd (c 0) (c 1) : ℤ) with hdd
    obtain ⟨a', ha'⟩ : d ∣ c 0 := Int.gcd_dvd_left _ _
    obtain ⟨b', hb'⟩ : d ∣ c 1 := Int.gcd_dvd_right _ _
    have hcop : IsCoprime a' b' := by
      have := Int.isCoprime_iff_gcd_eq_one.2 (Int.gcd_div_gcd_div_gcd (i := c 0) (j := c 1) (Nat.pos_of_ne_zero hd))
      have e0 : c 0 / d = a' := by rw [ha']; exact Int.mul_ediv_cancel_left _ hdpos.ne'
      have e1 : c 1 / d = b' := by rw [hb']; exact Int.mul_ediv_cancel_left _ hdpos.ne'
      rwa [e0, e1] at this
    obtain ⟨u, v, huv⟩ := hcop
    have hdc : x 0 * (d * a') + x 1 * (d * b') + x 2 * c 2 = 1 := by rw [← ha', ← hb']; exact hx
    have hA : a' * u + b' * v = 1 := by linarith
    let A : SL(3, ℤ) := ⟨!![a', -v, 0; b', u, 0; 0, 0, 1], by
      rw [Matrix.det_fin_three]; simp; linear_combination hA⟩
    let B : SL(3, ℤ) := ⟨!![d, 0, -x 2; 0, 1, 0; c 2, 0, x 0 * a' + x 1 * b'], by
      rw [Matrix.det_fin_three]; simp; linear_combination hdc⟩
    refine ⟨A * B, fun i => ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> simp [A, B, Matrix.mul_apply, Fin.sum_univ_three, ha', hb'] <;> ring


variable (N : ℕ) [NeZero N]

/-- **`SL₃(ℤ) → SL₃(ℤ/N)` is surjective.** -/
theorem sl3_map_surjective :
    Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) : SL(3, ℤ) →* SL(3, ZMod N)) := by
  intro M
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have key3 : ∀ (T : SL(3, ℤ)) (i j : Fin 3),
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) T : SL(3, ZMod N)) : Matrix (Fin 3) (Fin 3) (ZMod N)) i j =
        ((T.1 i j : ℤ) : ZMod N) := fun _ _ _ => rfl
  have key2 : ∀ (T : SL(2, ℤ)) (i j : Fin 2),
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) T : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) i j =
        ((T.1 i j : ℤ) : ZMod N) := fun _ _ _ => rfl
  have hadj : ∑ j, (Matrix.adjugate M.1) 0 j * M.1 j 0 = 1 := by
    have := congrArg (fun A : Matrix (Fin 3) (Fin 3) (ZMod N) => A 0 0) (Matrix.adjugate_mul M.1)
    simpa [Matrix.mul_apply, M.2] using this
  obtain ⟨X, s, hX⟩ := exists_int_bezout_of_zmod N (fun j => M.1 j 0) (fun j => Matrix.adjugate M.1 0 j) hadj
  obtain ⟨k, l, m, x, y, z, hxyz⟩ := exists_prim_lift3 (ZMod.cast (M.1 0 0) : ℤ) (ZMod.cast (M.1 1 0) : ℤ)
    (ZMod.cast (M.1 2 0) : ℤ) N hN ⟨X 0, X 1, X 2, s, by simpa [Fin.sum_univ_three] using hX⟩
  obtain ⟨T, hT⟩ := exists_sl3_first_col
    ![(ZMod.cast (M.1 0 0) : ℤ) + N * k, (ZMod.cast (M.1 1 0) : ℤ) + N * l, (ZMod.cast (M.1 2 0) : ℤ) + N * m]
    ⟨![x, y, z], by simpa [Fin.sum_univ_three] using hxyz⟩
  have hTcol : ∀ i, ((T.1 i 0 : ℤ) : ZMod N) = M.1 i 0 := by
    intro i
    rw [hT i]
    fin_cases i <;> simp
  set Tb : SL(3, ZMod N) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) T with hTb
  set M' : SL(3, ZMod N) := Tb⁻¹ * M with hM'
  have hM'col : ∀ i, M'.1 i 0 = (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i 0 := by
    intro i
    have h1 : (Matrix.adjugate Tb.1 * M.1) i 0 = (Matrix.adjugate Tb.1 * Tb.1) i 0 := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hTcol j]; rfl
    rw [Matrix.adjugate_mul, Tb.2] at h1
    have h2 : M'.1 i 0 = (Matrix.adjugate Tb.1 * M.1) i 0 := by
      rw [hM', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
    rw [h2, h1]; simp
  have h00 : M'.1 0 0 = 1 := by rw [hM'col]; simp
  have h10 : M'.1 1 0 = 0 := by rw [hM'col]; simp
  have h20 : M'.1 2 0 = 0 := by rw [hM'col]; simp
  have hdetB : M'.1 1 1 * M'.1 2 2 - M'.1 1 2 * M'.1 2 1 = 1 := by
    have := M'.2
    rw [Matrix.det_fin_three] at this
    simp only [h00, h10, h20] at this
    linear_combination this
  obtain ⟨Bt, hBt⟩ := sl2_map_surjective N
    (⟨!![M'.1 1 1, M'.1 1 2; M'.1 2 1, M'.1 2 2], by rw [Matrix.det_fin_two_of]; exact hdetB⟩ : SL(2, ZMod N))
  have hBe : ∀ i j : Fin 2, ((Bt.1 i j : ℤ) : ZMod N) = !![M'.1 1 1, M'.1 1 2; M'.1 2 1, M'.1 2 2] i j := by
    intro i j
    have := congrArg (fun A : SL(2, ZMod N) => (A : Matrix (Fin 2) (Fin 2) (ZMod N)) i j) hBt
    simpa [key2] using this
  have hBdet : Bt.1 0 0 * Bt.1 1 1 - Bt.1 0 1 * Bt.1 1 0 = 1 := by
    have := Bt.2
    rw [Matrix.det_fin_two] at this
    exact this
  obtain ⟨U, hU⟩ : ∃ U : SL(3, ℤ), (U : Matrix (Fin 3) (Fin 3) ℤ) =
      !![1, (ZMod.cast (M'.1 0 1) : ℤ), (ZMod.cast (M'.1 0 2) : ℤ); 0, Bt.1 0 0, Bt.1 0 1; 0, Bt.1 1 0, Bt.1 1 1] :=
    ⟨⟨_, by rw [Matrix.det_fin_three]; simp; linear_combination hBdet⟩, rfl⟩
  have hUM : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) U = M' := by
    apply Subtype.ext
    ext i j
    rw [key3, hU]
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, hBe]
  refine ⟨T * U, ?_⟩
  rw [map_mul, hUM, hM', mul_inv_cancel_left]

end SL3

end TernaryPeriodPolynomials.Argument.FormClassK
