module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Petersson.Form
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Hecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneCosets

@[expose] public section


/-!
# Adjointness of the Hecke operators `T_p` on `S_k(Γ₁(3))`

The coset family `tpFamily` of `T_p` (`p ≠ 3`), consisting of `ε_p [[p,0],[0,1]]` and
`[[1,j],[0,p]]` (`0 ≤ j < p`), gives `CosetData` for `Γ = Γ₁(3)` (`tpData`): the cosets are
distinct (`tp_disjoint`, from the level-one statement by clearing the signs `ε_p`), permuted by
`Γ₁(3)` (`tpFamily.transition`), and form one orbit (`tp_base`): from `[[1,0],[0,p]]` one reaches
`[[1,j],[0,p]]` by `T^j` and `ε_p [[p,0],[0,1]]` by `[[p², (p²-1)/3],[3,1]]`, using
`[[1,0],[0,p]] [[p², b],[3,1]] = [[p, b],[3, p]] [[p,0],[0,1]]` with `p² - 3b = 1`.

Since `α_∞ α₀ = ε_p p · 1`, the abstract adjointness `LevelThreePeterssonAdjoint.adjoint` gives
`⟨f, T_p g⟩ = ε_p^{k-2} ⟨T_p f, g⟩`, that is (`petThree_hecke`)

  `⟨T_p f, g⟩ = χ_k(p) ⟨f, T_p g⟩`,

with `χ_k(p) = ε_p^k = ±1` the character of `levelThreeChar`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory
open scoped MatrixGroups Pointwise ModularForm

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonTp

open TernaryPeriodPolynomials.Spectral.PeterssonHecke
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (heckeMatrix)
open TernaryPeriodPolynomials.Spectral.PeterssonCosets (beta)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonDomain
  (mk_eq_one fdThree fdThree_isFundamentalDomain volume_fdThree_lt_top)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonAdjoint
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonForm
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeCosets
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (p : Nat.Primes)

/-! ### Rational and real matrices -/

theorem real_mul (a b : GL (Fin 2) ℚ) : real (a * b) = real a * real b :=
  map_mul (GeneralLinearGroup.map (Rat.castHom ℝ)) a b

theorem real_injective : Function.Injective (real : GL (Fin 2) ℚ → GL (Fin 2) ℝ) := by
  intro a b h
  apply Units.ext
  have hv := congrArg (fun x : GL (Fin 2) ℝ => (x : Matrix (Fin 2) (Fin 2) ℝ)) h
  exact Matrix.map_injective (f := Rat.castHom ℝ) (Rat.castHom ℝ).injective hv

theorem real_tpRep_det_pos (i : Option (Fin p.val)) :
    0 < (((real (tpRep p i)).det : ℝˣ) : ℝ) := by
  rw [real_det]
  exact_mod_cast tpRep_det_pos p i

theorem tpRep_real_some (j : Fin p.val) : real (tpRep p (some j)) = heckeMatrix p (some j) := by
  rw [tpRep_real]
  simp [heckeSign]

theorem tpRep_real_alpha0 : real (tpRep p (some ⟨0, p.property.pos⟩)) = alpha0 p :=
  tpRep_real_some p _

theorem det_alpha0 : ((GeneralLinearGroup.det (alpha0 p) : ℝˣ) : ℝ) = p.val := by
  change (alpha0 p : Matrix (Fin 2) (Fin 2) ℝ).det = p.val
  rw [alpha0_val, Matrix.det_fin_two_of]
  ring

theorem det_levelThree {γ : GL (Fin 2) ℝ} (hγ : γ ∈ levelThree) :
    ((γ.det : ℝˣ) : ℝ) = 1 := by
  obtain ⟨g, -, rfl⟩ := hγ
  exact det_mapGL g

/-! ### Permutation of the cosets -/

theorem next_of_family {ι : Type*} [Fintype ι] (F : CosetFamily ι) {x : GL (Fin 2) ℝ}
    (hx : x ∈ levelThree) (i : ι) :
    ∃ j, real (F.rep i) * x * (real (F.rep j))⁻¹ ∈ levelThree := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨π, hπ⟩ := F.transition g hg
  obtain ⟨γ, hγ, h⟩ := hπ (π.symm i)
  rw [Equiv.apply_symm_apply] at h
  refine ⟨π.symm i, ?_⟩
  rw [h, mul_inv_cancel_right]
  exact mapGL_mem_levelThree hγ

/-! ### Distinct cosets -/

theorem tp_disjoint (i j : Option (Fin p.val))
    (h : real (tpRep p i) * (real (tpRep p j))⁻¹ ∈ levelThree) : i = j := by
  obtain ⟨g0, -, hgeq⟩ := h
  have h1 : SpecialLinearGroup.mapGL ℝ g0 * real (tpRep p j) = real (tpRep p i) := by
    rw [hgeq, inv_mul_cancel_right]
  have h2 : toGLQ g0 * tpRep p j = tpRep p i := by
    apply real_injective
    rw [real_mul, real_toGLQ]
    exact h1
  have h3 : g0.val * tpInt p j = tpInt p i := by
    refine Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective ?_
    show (g0.val * tpInt p j).map (Int.castRingHom ℚ) = (tpInt p i).map (Int.castRingHom ℚ)
    rw [Matrix.map_mul, tpInt_rational, tpInt_rational]
    have := congrArg (fun x : GL (Fin 2) ℚ => (x : Matrix (Fin 2) (Fin 2) ℚ)) h2
    exact this
  have hs : (heckeSign p i).val * (heckeSign p i).val = 1 := by
    have := congrArg Subtype.val (heckeSign_mul_self p i)
    simpa using this
  unfold tpInt at h3
  apply Spectral.LevelOneCosets.disjoint_int p
    ((heckeSign p i * g0 * heckeSign p j).val) i j
  have hmul : ∀ A B : SL(2, ℤ), (A * B).val = A.val * B.val := fun _ _ => rfl
  rw [hmul, hmul]
  calc (heckeSign p i).val * g0.val * (heckeSign p j).val * modularHeckeMatrix p j
      = (heckeSign p i).val * (g0.val * ((heckeSign p j).val * modularHeckeMatrix p j)) := by
        simp only [Matrix.mul_assoc]
    _ = (heckeSign p i).val * ((heckeSign p i).val * modularHeckeMatrix p i) := by rw [h3]
    _ = modularHeckeMatrix p i := by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]

/-! ### One orbit -/

theorem tp_base_some (j : Fin p.val) :
    ∃ γ ∈ levelThree, real (tpRep p (some ⟨0, p.property.pos⟩)) * γ *
      (real (tpRep p (some j)))⁻¹ ∈ levelThree := by
  refine ⟨SpecialLinearGroup.mapGL ℝ (beta p (some j)),
    mapGL_mem_levelThree (zpow_mem gammaOneThree_T_mem (j.val : ℤ)), ?_⟩
  rw [tpRep_real_some, tpRep_real_some, heckeMatrix_some_eq p j]
  have h : heckeMatrix p (some ⟨0, p.property.pos⟩) *
      SpecialLinearGroup.mapGL ℝ (beta p (some j)) *
      (alpha0 p * SpecialLinearGroup.mapGL ℝ (beta p (some j)))⁻¹ = 1 := mul_inv_cancel _
  rw [h]
  exact levelThree.one_mem

/-- `p² ≡ 1 mod 3`, as an integral relation `p² - 3b = 1`. -/
theorem exists_b (hp : p.val ≠ 3) : ∃ b : ℤ, (p.val : ℤ) ^ 2 - 3 * b = 1 := by
  rcases mod_three_cases hp with h | h
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, p.val = 3 * m + 1 := ⟨p.val / 3, by omega⟩
    exact ⟨3 * (m : ℤ) ^ 2 + 2 * m, by rw [hm]; push_cast; ring⟩
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, p.val = 3 * m + 2 := ⟨p.val / 3, by omega⟩
    exact ⟨3 * (m : ℤ) ^ 2 + 4 * m + 1, by rw [hm]; push_cast; ring⟩

theorem natCast_sq (hp : p.val ≠ 3) : ((p.val : ℤ) : ZMod 3) ^ 2 = 1 := by
  have hc : ((p.val : ℕ) : ZMod 3) = ((p.val % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod _ _).symm
  rcases mod_three_cases hp with h | h <;> rw [h] at hc <;> simp only [Int.cast_natCast, hc] <;>
    decide

/-- The matrix `[[p², b], [3, 1]]` of `Γ₁(3)`. -/
def gamNone (b : ℤ) (hb : (p.val : ℤ) ^ 2 - 3 * b = 1) : SL(2, ℤ) :=
  ⟨!![(p.val : ℤ) ^ 2, b; 3, 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination hb⟩

/-- The matrix `[[p, b], [3, p]]`. -/
def etaNone (b : ℤ) (hb : (p.val : ℤ) ^ 2 - 3 * b = 1) : SL(2, ℤ) :=
  ⟨!![(p.val : ℤ), b; 3, p.val], by
    rw [Matrix.det_fin_two_of]
    linear_combination hb⟩

theorem gamNone_mem (hp : p.val ≠ 3) (b : ℤ) (hb : (p.val : ℤ) ^ 2 - 3 * b = 1) :
    gamNone p b hb ∈ CongruenceSubgroup.Gamma1 3 := by
  refine (CongruenceSubgroup.Gamma1_mem 3 _).mpr ?_
  change (((p.val : ℤ) ^ 2 : ℤ) : ZMod 3) = 1 ∧ ((1 : ℤ) : ZMod 3) = 1 ∧ ((3 : ℤ) : ZMod 3) = 0
  refine ⟨?_, by simp, by decide⟩
  rw [Int.cast_pow]
  exact natCast_sq p hp

theorem neg_one_mul_sl (x : SL(2, ℤ)) : (-1 : SL(2, ℤ)) * x = -x := by
  ext i j
  simp

theorem sign_etaNone_mem (hp : p.val ≠ 3) (b : ℤ) (hb : (p.val : ℤ) ^ 2 - 3 * b = 1) :
    heckeSign p none * etaNone p b hb ∈ CongruenceSubgroup.Gamma1 3 := by
  have hc : ((p.val : ℕ) : ZMod 3) = ((p.val % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod _ _).symm
  rcases mod_three_cases hp with h | h
  · have e : heckeSign p none = 1 := by simp [heckeSign, h]
    rw [e, one_mul]
    refine (CongruenceSubgroup.Gamma1_mem 3 _).mpr ?_
    change ((p.val : ℤ) : ZMod 3) = 1 ∧ ((p.val : ℤ) : ZMod 3) = 1 ∧ ((3 : ℤ) : ZMod 3) = 0
    rw [h] at hc
    simp only [Int.cast_natCast, hc]
    exact ⟨by simp, by simp, by decide⟩
  · have e : heckeSign p none = -1 := by simp [heckeSign, h]
    rw [e, neg_one_mul_sl]
    refine (CongruenceSubgroup.Gamma1_mem 3 _).mpr ?_
    simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    change (-((p.val : ℤ) : ZMod 3)) = 1 ∧ (-((p.val : ℤ) : ZMod 3)) = 1 ∧
      (-((3 : ℤ) : ZMod 3)) = 0
    rw [h] at hc
    simp only [Int.cast_natCast, hc]
    exact ⟨by decide, by decide, by decide⟩

theorem sign_conj (b : ℤ) (hb : (p.val : ℤ) ^ 2 - 3 * b = 1) :
    heckeSign p none * etaNone p b hb * heckeSign p none = etaNone p b hb := by
  unfold heckeSign
  split_ifs
  · ext i j
    simp
  · simp

theorem tp_none_relation (b : ℤ) (hb : (p.val : ℤ) ^ 2 - 3 * b = 1) :
    alpha0 p * SpecialLinearGroup.mapGL ℝ (gamNone p b hb) =
      SpecialLinearGroup.mapGL ℝ (etaNone p b hb) * heckeMatrix p none := by
  apply Units.ext
  simp only [Units.val_mul, alpha0_val, mapGL_val, heckeMatrix_none_val]
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, gamNone, etaNone] <;> ring

theorem tp_base_none (hp : p.val ≠ 3) :
    ∃ γ ∈ levelThree, real (tpRep p (some ⟨0, p.property.pos⟩)) * γ *
      (real (tpRep p none))⁻¹ ∈ levelThree := by
  obtain ⟨b, hb⟩ := exists_b p hp
  refine ⟨SpecialLinearGroup.mapGL ℝ (gamNone p b hb),
    mapGL_mem_levelThree (gamNone_mem p hp b hb), ?_⟩
  have h : real (tpRep p (some ⟨0, p.property.pos⟩)) *
      SpecialLinearGroup.mapGL ℝ (gamNone p b hb) =
      SpecialLinearGroup.mapGL ℝ (heckeSign p none * etaNone p b hb) * real (tpRep p none) := by
    calc real (tpRep p (some ⟨0, p.property.pos⟩)) * SpecialLinearGroup.mapGL ℝ (gamNone p b hb)
        = alpha0 p * SpecialLinearGroup.mapGL ℝ (gamNone p b hb) := by rw [tpRep_real_alpha0]
      _ = SpecialLinearGroup.mapGL ℝ (etaNone p b hb) * heckeMatrix p none :=
        tp_none_relation p b hb
      _ = SpecialLinearGroup.mapGL ℝ (heckeSign p none * etaNone p b hb * heckeSign p none) *
          heckeMatrix p none := by rw [sign_conj]
      _ = SpecialLinearGroup.mapGL ℝ (heckeSign p none * etaNone p b hb) * real (tpRep p none) := by
        rw [tpRep_real]
        simp only [map_mul, mul_assoc]
  have h' : real (tpRep p (some ⟨0, p.property.pos⟩)) *
      SpecialLinearGroup.mapGL ℝ (gamNone p b hb) * (real (tpRep p none))⁻¹ =
      SpecialLinearGroup.mapGL ℝ (heckeSign p none * etaNone p b hb) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact h
  rw [h']
  exact mapGL_mem_levelThree (sign_etaNone_mem p hp b hb)

theorem tp_base (hp : p.val ≠ 3) (j : Option (Fin p.val)) :
    ∃ γ ∈ levelThree, real (tpRep p (some ⟨0, p.property.pos⟩)) * γ *
      (real (tpRep p j))⁻¹ ∈ levelThree := by
  cases j with
  | none => exact tp_base_none p hp
  | some j => exact tp_base_some p j

/-- **Coset data of `T_p` for `Γ₁(3)`.** -/
def tpData (hp : p.val ≠ 3) : CosetData levelThree (Option (Fin p.val)) :=
  CosetData.ofBase levelThree (fun i => real (tpRep p i)) (fun i => real_tpRep_det_pos p i)
    (fun _ hx i => next_of_family (tpFamily hp) hx i) (fun i j h => tp_disjoint p i j h)
    (some ⟨0, p.property.pos⟩) (tp_base p hp)

/-! ### The scalar `α_∞ α₀ = ε_p p` -/

/-- The scalar `ε_p p`, a unit of `ℝ`. -/
def uTp : ℝˣ := if p.val % 3 = 2 then -pUnit p else pUnit p

theorem tp_alpha_mul :
    real (tpRep p none) * real (tpRep p (some ⟨0, p.property.pos⟩)) =
      GeneralLinearGroup.scalar (Fin 2) (uTp p) := by
  rw [tpRep_real, tpRep_real_alpha0]
  apply Units.ext
  by_cases h : p.val % 3 = 2
  · have e : heckeSign p none = -1 := by simp [heckeSign, h]
    rw [e]
    simp only [uTp, ite_eq_left h, Units.val_mul, mapGL_val, heckeMatrix_none_val, alpha0_val,
      scalar_val, Units.val_neg, pUnit_val]
    ext a c
    fin_cases a <;> fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have e : heckeSign p none = 1 := by simp [heckeSign, h]
    rw [e]
    simp only [uTp, ite_eq_right h, Units.val_mul, mapGL_val, heckeMatrix_none_val, alpha0_val,
      scalar_val, pUnit_val]
    ext a c
    fin_cases a <;> fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem neg_one_zpow_sub_two (k : ℤ) : (-1 : ℂ) ^ (k - 2) = (-1 : ℂ) ^ k := by
  rw [zpow_sub₀ (show (-1 : ℂ) ≠ 0 by norm_num)]
  norm_num

theorem uTp_zpow (k : ℤ) :
    (((uTp p : ℝˣ) : ℝ) : ℂ) ^ (k - 2) = levelThreeChar k p.val * ((p.val : ℝ) : ℂ) ^ (k - 2) := by
  unfold uTp levelThreeChar
  split_ifs with h
  · rw [Units.val_neg, pUnit_val, Complex.ofReal_neg,
      show (-((p.val : ℝ) : ℂ)) = (-1 : ℂ) * ((p.val : ℝ) : ℂ) by ring, mul_zpow,
      neg_one_zpow_sub_two]
  · rw [pUnit_val, one_mul]

theorem levelThreeChar_mul_self (k : ℤ) (n : ℕ) :
    levelThreeChar k n * levelThreeChar k n = 1 := by
  unfold levelThreeChar
  split_ifs
  · rw [← mul_zpow]
    norm_num
  · norm_num

theorem levelThreeChar_cases (k : ℤ) (n : ℕ) :
    levelThreeChar k n = 1 ∨ levelThreeChar k n = -1 := by
  unfold levelThreeChar
  split_ifs
  · rcases Int.even_or_odd k with h | h
    · exact Or.inl (Even.neg_one_zpow h)
    · exact Or.inr (Odd.neg_one_zpow h)
  · exact Or.inl rfl

/-! ### Adjointness -/

variable {k : ℤ}

/-- **Adjointness**, one direction: `⟨f, T_p g⟩ = χ_k(p) ⟨T_p f, g⟩`. -/
theorem petThree_hecke_right (hp : p.val ≠ 3) (f g : CuspForm levelThree k) :
    petThree k f (levelThreeHecke k p hp g) =
      levelThreeChar k p.val * petThree k (levelThreeHecke k p hp f) g := by
  have hF : ∀ γ ∈ levelThree, (f : ℍ → ℂ) ∣[k] γ = f :=
    fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ
  have hG : ∀ γ ∈ levelThree, (g : ℍ → ℂ) ∣[k] γ = g :=
    fun γ hγ => SlashInvariantFormClass.slash_action_eq g γ hγ
  have h := adjoint (Γ := levelThree) k (fun γ hγ => det_levelThree hγ)
    (fun γ hγ h => mk_eq_one hγ h)
    fdThree_isFundamentalDomain volume_fdThree_lt_top (tpData p hp) hF hG
    (continuous_slash_cuspForm k f) (continuous_slash_cuspForm k g) (pbounded_cuspForm k f)
    (pbounded_cuspForm k g) (some ⟨0, p.property.pos⟩) none (uTp p) (tp_alpha_mul p)
  have hα : (tpData p hp).α (some ⟨0, p.property.pos⟩) = alpha0 p := tpRep_real_alpha0 p
  rw [hα, det_alpha0, uTp_zpow] at h
  have hpne : ((p.val : ℝ) : ℂ) ^ (k - 2) ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast p.property.ne_zero)
  have e1 : petThree k f (levelThreeHecke k p hp g) =
      ∫ τ in fdThree, petersson k f (∑ i, (g : ℍ → ℂ) ∣[k] (tpData p hp).α i) τ := rfl
  have e2 : petThree k (levelThreeHecke k p hp f) g =
      ∫ τ in fdThree, petersson k (∑ i, (f : ℍ → ℂ) ∣[k] (tpData p hp).α i) g τ := rfl
  rw [e1, e2]
  apply mul_left_cancel₀ hpne
  rw [h]
  ring

/-- **The Hecke operator `T_p` is `χ_k(p)`-self-adjoint for the Petersson product on
`S_k(Γ₁(3))`**: `⟨T_p f, g⟩ = χ_k(p) ⟨f, T_p g⟩`. -/
theorem petThree_hecke (hp : p.val ≠ 3) (f g : CuspForm levelThree k) :
    petThree k (levelThreeHecke k p hp f) g =
      levelThreeChar k p.val * petThree k f (levelThreeHecke k p hp g) := by
  rw [petThree_hecke_right p hp f g, ← mul_assoc, levelThreeChar_mul_self, one_mul]

end TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonTp
