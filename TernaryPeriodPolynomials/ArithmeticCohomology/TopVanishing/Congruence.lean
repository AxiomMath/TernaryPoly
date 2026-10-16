module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Boundary

@[expose] public section


/-!
# The principal congruence subgroup of level three

`Γ(3)` is the kernel of the reduction `GL₃(ℤ) → GL₃(ℤ/3)`, viewed inside `GL₃(ℚ)`. It lies in the
rational image of the arithmetic level, has finite index there, and is torsion free
(Minkowski): an integral matrix congruent to the identity modulo three whose power is the identity
is the identity.
-/

noncomputable section

namespace TernaryPeriodPolynomials.TopVanishing

open GeneralEisenstein Matrix

/-- The inclusion `GL₃(ℤ) → GL₃(ℚ)`. -/
def integralToRational : IntegralGL3 →* RationalGL3 :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)

/-- The principal congruence subgroup `Γ(3) = ker(GL₃(ℤ) → GL₃(ℤ/3))`, inside the rational group. -/
def principalLevel : Subgroup RationalGL3 :=
  reductionThree.ker.map integralToRational

theorem integralToRational_injective : Function.Injective integralToRational := by
  intro a b hab
  apply Units.ext
  ext i j
  have h1 := congrArg (fun g : GeneralLinearGroup (Fin 3) ℚ => (g : Matrix (Fin 3) (Fin 3) ℚ) i j) hab
  simpa [integralToRational] using h1

theorem rationalLevel_eq_map : rationalLevel = arithmeticLevel.map integralToRational := by
  ext x
  simp only [rationalLevel, MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem ker_le_arithmeticLevel : reductionThree.ker ≤ arithmeticLevel := by
  intro h hh
  have h1 : reductionThree h = 1 := MonoidHom.mem_ker.mp hh
  refine Subgroup.mem_comap.mpr ?_
  rw [h1]
  exact one_mem _

theorem principalLevel_le : principalLevel ≤ rationalLevel := by
  rw [rationalLevel_eq_map]
  exact Subgroup.map_mono ker_le_arithmeticLevel

theorem reductionThree_ker_index_ne_zero : reductionThree.ker.index ≠ 0 := by
  have : Finite (Matrix (Fin 3) (Fin 3) (ZMod 3)) :=
    inferInstanceAs (Finite (Fin 3 → Fin 3 → ZMod 3))
  have : Finite (GeneralLinearGroup (Fin 3) (ZMod 3)) :=
    Finite.of_injective (fun g : GeneralLinearGroup (Fin 3) (ZMod 3) =>
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3))) Units.val_injective
  rw [Subgroup.index_ker]
  exact Nat.card_pos.ne'

theorem principalLevel_relIndex_ne_zero : principalLevel.relIndex rationalLevel ≠ 0 := by
  have hdvd : reductionThree.ker.relIndex arithmeticLevel ∣ reductionThree.ker.index :=
    Subgroup.relIndex_dvd_index_of_le ker_le_arithmeticLevel
  have hne : reductionThree.ker.relIndex arithmeticLevel ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hdvd
    exact reductionThree_ker_index_ne_zero hdvd
  rw [rationalLevel_eq_map]
  unfold principalLevel
  rw [Subgroup.relIndex_map_map_of_injective _ _ integralToRational_injective]
  exact hne

/-! ### Integral matrix lemmas -/

theorem one_add_pow_expand {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℤ) (k : ℕ) :
    ∃ C : Matrix n n ℤ, (1 + N) ^ k = 1 + (k : ℤ) • N + N * N * C := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨(k : ℤ) • (1 : Matrix n n ℤ) + C + C * N, ?_⟩
    rw [pow_succ, hC]
    simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc,
      Nat.cast_succ, add_smul, one_smul]
    module

theorem one_add_pow_three {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n ℤ) :
    (1 + N) ^ 3 = 1 + (3 : ℤ) • N + (3 : ℤ) • (N * N) + N * N * N := by
  noncomm_ring

theorem three_dvd_aux_one {t q b x : ℤ} (ht : t ≠ 0) (hq : ¬ (3 : ℤ) ∣ q)
    (h : (3 * t * q) * b + (3 * t * (3 * t)) * x = 0) : (3 : ℤ) ∣ b := by
  have hne : 3 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have h1 : (3 * t) * (q * b + 3 * t * x) = 0 := by linear_combination h
  have h2 : q * b + 3 * t * x = 0 := (mul_eq_zero.mp h1).resolve_left hne
  have h3 : (3 : ℤ) ∣ q * b := ⟨-(t * x), by linear_combination h2⟩
  exact (Int.prime_three.dvd_or_dvd h3).resolve_left hq

theorem three_dvd_aux_three {t b x y : ℤ} (ht : t ≠ 0)
    (h : (3 * (3 * t)) * b + (3 * (3 * t * (3 * t))) * x
      + (3 * t * (3 * t) * (3 * t)) * y = 0) : (3 : ℤ) ∣ b := by
  have hne : 9 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have h1 : (9 * t) * (b + 3 * t * x + 3 * t ^ 2 * y) = 0 := by linear_combination h
  have h2 : b + 3 * t * x + 3 * t ^ 2 * y = 0 := (mul_eq_zero.mp h1).resolve_left hne
  exact ⟨-(t * x + t ^ 2 * y), by linear_combination h2⟩

theorem three_dvd_of_pow_eq_one_step {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℤ) (a : ℕ) (hA : A = 1 + ((3 : ℤ) ^ (a + 1)) • B)
    (q : ℕ) (hq : q.Prime) (hAq : A ^ q = 1) : ∀ i j, (3 : ℤ) ∣ B i j := by
  obtain ⟨t, htdef⟩ : ∃ t : ℤ, t = (3 : ℤ) ^ a := ⟨_, rfl⟩
  have ht' : t ≠ 0 := by rw [htdef]; exact pow_ne_zero _ (by norm_num)
  have h3a : ((3 : ℤ) ^ (a + 1)) = 3 * t := by rw [htdef]; ring
  rw [h3a] at hA
  obtain ⟨N, hN⟩ : ∃ N : Matrix n n ℤ, N = ((3 : ℤ) * t) • B := ⟨_, rfl⟩
  rw [← hN] at hA
  have hNN : N * N = ((3 * t) * (3 * t)) • (B * B) := by
    rw [hN, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hNNN : N * N * N = ((3 * t) * (3 * t) * (3 * t)) • (B * B * B) := by
    rw [hNN, hN, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hA] at hAq
  by_cases hq3 : q = 3
  · subst hq3
    rw [one_add_pow_three] at hAq
    have h0 : (3 : ℤ) • N + (3 : ℤ) • (N * N) + N * N * N = 0 := by
      calc (3 : ℤ) • N + (3 : ℤ) • (N * N) + N * N * N
          = (1 + (3 : ℤ) • N + (3 : ℤ) • (N * N) + N * N * N) - 1 := by abel
        _ = 0 := by rw [hAq, sub_self]
    rw [hNNN, hNN, hN] at h0
    intro i j
    have h4 := congrFun (congrFun h0 i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
    exact three_dvd_aux_three (x := (B * B) i j) (y := (B * B * B) i j) ht'
      (by linear_combination h4)
  · obtain ⟨C, hC⟩ := one_add_pow_expand N q
    rw [hC] at hAq
    have h0 : (q : ℤ) • N + N * N * C = 0 := by
      calc (q : ℤ) • N + N * N * C = (1 + (q : ℤ) • N + N * N * C) - 1 := by abel
        _ = 0 := by rw [hAq, sub_self]
    rw [hNN, hN, smul_mul_assoc] at h0
    have hq3' : ¬ (3 : ℤ) ∣ (q : ℤ) := by
      intro hd
      have hd' : 3 ∣ q := by exact_mod_cast hd
      exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp hd').symm
    intro i j
    have h4 := congrFun (congrFun h0 i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
    exact three_dvd_aux_one (x := (B * B * C) i j) ht' hq3' (by linear_combination h4)

theorem congruence_step {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℤ) (a : ℕ) (hA : A = 1 + ((3 : ℤ) ^ (a + 1)) • B)
    (q : ℕ) (hq : q.Prime) (hAq : A ^ q = 1) :
    ∃ B' : Matrix n n ℤ, A = 1 + ((3 : ℤ) ^ (a + 1 + 1)) • B' := by
  have hB := three_dvd_of_pow_eq_one_step A B a hA q hq hAq
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix n n ℤ, B = (3 : ℤ) • B' := by
    refine ⟨Matrix.of fun i j => B i j / 3, ?_⟩
    ext i j
    have hd := hB i j
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    omega
  refine ⟨B', ?_⟩
  rw [hA, hB', smul_smul, ← pow_succ]

theorem lt_three_pow (n : ℕ) : (n : ℤ) < 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h3 : (0 : ℤ) < 3 ^ k := by positivity
    have h4 : (3 : ℤ) ^ (k + 1) = 3 * 3 ^ k := by ring
    push_cast
    linarith

theorem abs_lt_three_pow_succ (x : ℤ) : |x| < 3 ^ (x.natAbs + 1) := by
  have h1 := lt_three_pow x.natAbs
  have h2 : (3 : ℤ) ^ (x.natAbs + 1) = 3 * 3 ^ x.natAbs := by ring
  have h3 : (0 : ℤ) < 3 ^ x.natAbs := by positivity
  rw [Int.abs_eq_natAbs]
  linarith

theorem eq_zero_of_forall_three_pow_dvd (x : ℤ) (h : ∀ a : ℕ, (3 : ℤ) ^ (a + 1) ∣ x) :
    x = 0 :=
  Int.eq_zero_of_abs_lt_dvd (h x.natAbs) (abs_lt_three_pow_succ x)

theorem eq_one_of_three_dvd_of_pow_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hA : ∃ B : Matrix n n ℤ, A = 1 + (3 : ℤ) • B)
    (q : ℕ) (hq : q.Prime) (hAq : A ^ q = 1) : A = 1 := by
  have key : ∀ a : ℕ, ∃ B : Matrix n n ℤ, A = 1 + ((3 : ℤ) ^ (a + 1)) • B := by
    intro a
    induction a with
    | zero => simpa using hA
    | succ a ih =>
      obtain ⟨B, hB⟩ := ih
      exact congruence_step A B a hB q hq hAq
  ext i j
  have hall : ∀ a : ℕ, (3 : ℤ) ^ (a + 1) ∣ A i j - (1 : Matrix n n ℤ) i j := by
    intro a
    obtain ⟨B, hB⟩ := key a
    refine ⟨B i j, ?_⟩
    have h1 := congrFun (congrFun hB i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1
    linear_combination h1
  exact sub_eq_zero.mp (eq_zero_of_forall_three_pow_dvd _ hall)

/-! ### From the group `Γ(3)` to integral matrices -/

theorem exists_three_smul_of_mem_ker (h : IntegralGL3) (hh : h ∈ reductionThree.ker) :
    ∃ B : Matrix (Fin 3) (Fin 3) ℤ, (h : Matrix (Fin 3) (Fin 3) ℤ) = 1 + (3 : ℤ) • B := by
  have h1 : reductionThree h = 1 := MonoidHom.mem_ker.mp hh
  have hdvd : ∀ i j, (3 : ℤ) ∣ (h : Matrix (Fin 3) (Fin 3) ℤ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
    intro i j
    have h3 : (((h : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod 3) =
        (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j := by
      have h2 := congrArg
        (fun x : GeneralLinearGroup (Fin 3) (ZMod 3) =>
          (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j) h1
      simpa [reductionThree, Matrix.GeneralLinearGroup.map_apply] using h2
    have h5 : ((((1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ)) : ZMod 3) =
        (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have h4 : ((((h : Matrix (Fin 3) (Fin 3) ℤ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ)) : ZMod 3) = 0 := by
      rw [Int.cast_sub, h3, h5, sub_self]
    have h6 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h4
    exact_mod_cast h6
  refine ⟨Matrix.of fun i j =>
    ((h : Matrix (Fin 3) (Fin 3) ℤ) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j) / 3, ?_⟩
  ext i j
  have hd := hdvd i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  omega

theorem eq_one_of_mem_ker_of_prime_pow (y : IntegralGL3) (hy : y ∈ reductionThree.ker)
    (q : ℕ) (hq : q.Prime) (hyq : y ^ q = 1) : y = 1 := by
  obtain ⟨B, hB⟩ := exists_three_smul_of_mem_ker y hy
  have hAq : (y : Matrix (Fin 3) (Fin 3) ℤ) ^ q = 1 := by
    have h1 := congrArg Units.val hyq
    simpa using h1
  have h1 : (y : Matrix (Fin 3) (Fin 3) ℤ) = 1 :=
    eq_one_of_three_dvd_of_pow_eq_one _ ⟨B, hB⟩ q hq hAq
  exact Units.ext (by simpa using h1)

theorem eq_one_of_mem_ker_of_pow_eq_one (h : IntegralGL3) (hh : h ∈ reductionThree.ker)
    (m : ℕ) (hm : 0 < m) (hpow : h ^ m = 1) : h = 1 := by
  by_contra hne
  have hdvd : orderOf h ∣ m := orderOf_dvd_of_pow_eq_one hpow
  have hd0 : 0 < orderOf h := Nat.pos_of_dvd_of_pos hdvd hm
  have hd1 : orderOf h ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
  have hq : (orderOf h).minFac.Prime := Nat.minFac_prime hd1
  have hqd : (orderOf h).minFac ∣ orderOf h := Nat.minFac_dvd _
  have hy : h ^ (orderOf h / (orderOf h).minFac) ∈ reductionThree.ker :=
    Subgroup.pow_mem _ hh _
  have hyq : (h ^ (orderOf h / (orderOf h).minFac)) ^ (orderOf h).minFac = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hqd]
    exact pow_orderOf_eq_one h
  have hy1 := eq_one_of_mem_ker_of_prime_pow _ hy _ hq hyq
  have hpos : 0 < orderOf h / (orderOf h).minFac :=
    Nat.div_pos (Nat.le_of_dvd hd0 hqd) hq.pos
  have hle := orderOf_le_of_pow_eq_one hpos hy1
  have hlt : orderOf h / (orderOf h).minFac < orderOf h := Nat.div_lt_self hd0 hq.one_lt
  exact absurd hle (not_le.mpr hlt)

/-- `Γ(3)` is torsion free (Minkowski). -/
theorem principalLevel_torsionFree (g : RationalGL3) (hg : g ∈ principalLevel) (m : ℕ)
    (hm : 0 < m) (h : g ^ m = 1) : g = 1 := by
  have hg' : g ∈ reductionThree.ker.map integralToRational := hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg'
  have hxm : x ^ m = 1 := by
    apply integralToRational_injective
    rw [map_pow, map_one]
    exact h
  rw [eq_one_of_mem_ker_of_pow_eq_one x hx m hm hxm, map_one]

end TernaryPeriodPolynomials.TopVanishing

end
