module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.HeckeCorrespondence
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.QExpansion

@[expose] public section


/-!
# Hecke operators on Mathlib's level-one cusp forms

For a prime `p` the operator `T_p f = ∑_α f ∣[k] α`, with `α` running over
`[[p,0],[0,1]]` and `[[1,j],[0,p]]` (`0 ≤ j < p`), maps level-one cusp forms of weight `k` to
level-one cusp forms (`levelOneHecke`). Its values are the right-hand side of the project's
`HasPrimeHeckeRelations`, and its `q`-expansion coefficients are
`a_n(T_p f) = a_{pn}(f) + p^{k-1} a_{n/p}(f)` (`levelOneHecke_coeff`).

Original work by Claude Opus 5.5 (AxiomCode, Sol).
-/

noncomputable section

open scoped ModularForm MatrixGroups Manifold
open Matrix UpperHalfPlane GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.LevelOneHecke

/-- The level-one group inside `GL₂(ℝ)`. -/
abbrev levelOne : Subgroup (GL (Fin 2) ℝ) :=
  (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range

/-- The `p + 1` Hecke matrices in `GL₂(ℝ)`. -/
def heckeMatrix (p : Nat.Primes) (i : Option (Fin p.val)) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative p i)

theorem map_toGL_eq_mapGL (g : SL(2, ℤ)) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL g)) =
      SpecialLinearGroup.mapGL ℝ g := by
  ext i j
  simp [SpecialLinearGroup.mapGL, GeneralLinearGroup.map_apply]

theorem heckeMatrix_transition (p : Nat.Primes) (g : SL(2, ℤ)) (i : Option (Fin p.val)) :
    heckeMatrix p (modularHeckePermutation p g i) * SpecialLinearGroup.mapGL ℝ g =
      SpecialLinearGroup.mapGL ℝ (modularHeckeTransition p g i) * heckeMatrix p i := by
  have h := congrArg (GeneralLinearGroup.map (algebraMap ℚ ℝ))
    (modularHeckeTransition_rational p g i)
  simp only [map_mul, map_toGL_eq_mapGL] at h
  exact h

theorem sum_slash {ι : Type*} (k : ℤ) (g : GL (Fin 2) ℝ) (s : Finset ι) (F : ι → ℍ → ℂ) :
    (∑ i ∈ s, F i) ∣[k] g = ∑ i ∈ s, F i ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

theorem heckeMatrix_det (p : Nat.Primes) (i : Option (Fin p.val)) :
    (heckeMatrix p i : Matrix (Fin 2) (Fin 2) ℝ).det = p.val := by
  cases i with
  | none => exact binaryHeckeDilate_det p.val p.property.pos
  | some j => exact binaryHeckeTranslate_det p.val p.property.pos j

theorem sigma_heckeMatrix (p : Nat.Primes) (i : Option (Fin p.val)) (a : ℂ) :
    σ (heckeMatrix p i) a = a := by
  have hpos : 0 < ((GeneralLinearGroup.det (heckeMatrix p i) : ℝˣ) : ℝ) := by
    change 0 < (heckeMatrix p i : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [heckeMatrix_det]
    exact_mod_cast p.property.pos
  simp only [σ]
  rw [ite_eq_left hpos]
  rfl

/-- The Hecke sum on functions. -/
def heckeFun (k : ℤ) (p : Nat.Primes) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i, f ∣[k] heckeMatrix p i

theorem heckeFun_slash (k : ℤ) (p : Nat.Primes) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ levelOne, f ∣[k] γ = f) (g : SL(2, ℤ)) :
    heckeFun k p f ∣[k] SpecialLinearGroup.mapGL ℝ g = heckeFun k p f := by
  unfold heckeFun
  rw [sum_slash]
  simp_rw [← SlashAction.slash_mul]
  rw [← Equiv.sum_comp (modularHeckePermutation p g)]
  apply Finset.sum_congr rfl
  intro i _
  rw [heckeMatrix_transition, SlashAction.slash_mul, hf _ ⟨_, rfl⟩]

theorem heckeMatrix_eq_cast (p : Nat.Primes) (i : Option (Fin p.val)) :
    heckeMatrix p i = (binaryHeckeRepresentative p i).map (Rat.castHom ℝ) := rfl

theorem heckeFun_mdifferentiable (k : ℤ) (p : Nat.Primes) (f : CuspForm levelOne k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeFun k p f) := by
  unfold heckeFun
  have hterm : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] heckeMatrix p i) :=
    fun i => (CuspForm.translate f (heckeMatrix p i)).holo'
  classical
  induction (Finset.univ : Finset (Option (Fin p.val))) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mdifferentiable_const
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hterm a).add ih

theorem isCusp_heckeMatrix_smul (p : Nat.Primes) (i : Option (Fin p.val)) {c : OnePoint ℝ}
    (hc : IsCusp c levelOne) : IsCusp (heckeMatrix p i • c) levelOne := by
  have h := hc.smul (heckeMatrix p i)
  have := Subgroup.IsArithmetic.conj levelOne (binaryHeckeRepresentative p i)
  rw [heckeMatrix_eq_cast] at h ⊢
  exact (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp h

theorem heckeFun_zeroAt (k : ℤ) (p : Nat.Primes) (f : CuspForm levelOne k) {c : OnePoint ℝ}
    (hc : IsCusp c levelOne) : c.IsZeroAt (heckeFun k p f) k := by
  intro g hg
  unfold heckeFun
  rw [sum_slash]
  simp_rw [← SlashAction.slash_mul]
  have hterm : ∀ i, IsZeroAtImInfty (⇑f ∣[k] (heckeMatrix p i * g)) := by
    intro i
    apply CuspFormClass.zero_at_cusps f (isCusp_heckeMatrix_smul p i hc)
    rw [mul_smul, hg]
  classical
  induction (Finset.univ : Finset (Option (Fin p.val))) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hterm a).add ih

/-- **The Hecke operator `T_p` on level-one cusp forms.** -/
def levelOneHecke (k : ℤ) (p : Nat.Primes) : CuspForm levelOne k →ₗ[ℂ] CuspForm levelOne k where
  toFun f :=
    { toFun := heckeFun k p f
      slash_action_eq' := by
        rintro γ ⟨g, rfl⟩
        exact heckeFun_slash k p f (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) g
      holo' := heckeFun_mdifferentiable k p f
      zero_at_cusps' := fun hc => heckeFun_zeroAt k p f hc }
  map_add' f g := by
    ext τ
    change heckeFun k p (⇑f + ⇑g) τ = heckeFun k p f τ + heckeFun k p g τ
    simp only [heckeFun, SlashAction.add_slash, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' a f := by
    ext τ
    change heckeFun k p (a • ⇑f) τ = a • heckeFun k p f τ
    simp only [heckeFun, ModularForm.smul_slash, Finset.smul_sum, Finset.sum_apply, Pi.smul_apply,
      sigma_heckeMatrix]

theorem levelOneHecke_apply (k : ℤ) (p : Nat.Primes) (f : CuspForm levelOne k) :
    (levelOneHecke k p f : ℍ → ℂ) = heckeFun k p f := rfl

theorem dilate_slash_apply (k : ℤ) (p : Nat.Primes) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] heckeMatrix p none) τ = (p.val : ℂ) ^ (k - 1) *
      f (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate p.val p.property.pos) • τ) := by
  rw [ModularForm.slash_def]
  simp only [sigma_heckeMatrix]
  have hdet : ((GeneralLinearGroup.det (heckeMatrix p none) : ℝˣ) : ℝ) = p.val :=
    heckeMatrix_det p none
  have hval : (heckeMatrix p none : Matrix (Fin 2) (Fin 2) ℝ) = !![(p.val : ℝ), 0; 0, 1] :=
    binaryHeckeDilate_real p.val p.property.pos
  have hdenom : UpperHalfPlane.denom (heckeMatrix p none) τ = 1 := by
    simp [UpperHalfPlane.denom, hval]
  rw [hdet, hdenom, abs_of_pos (by exact_mod_cast p.property.pos), _root_.one_zpow, mul_one,
    mul_comm]
  push_cast
  rfl

theorem translate_slash_apply (k : ℤ) (p : Nat.Primes) (j : Fin p.val) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] heckeMatrix p (some j)) τ = (p.val : ℂ)⁻¹ *
      f (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate p.val p.property.pos j) • τ) := by
  rw [ModularForm.slash_def]
  simp only [sigma_heckeMatrix]
  have hdet : ((GeneralLinearGroup.det (heckeMatrix p (some j)) : ℝˣ) : ℝ) = p.val :=
    heckeMatrix_det p (some j)
  have hval : (heckeMatrix p (some j) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, (j.val : ℝ); 0, (p.val : ℝ)] :=
    binaryHeckeTranslate_real p.val p.property.pos j
  have hdenom : UpperHalfPlane.denom (heckeMatrix p (some j)) τ = p.val := by
    simp [UpperHalfPlane.denom, hval]
  rw [hdet, hdenom, abs_of_pos (by exact_mod_cast p.property.pos)]
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  push_cast
  rw [mul_assoc, ← zpow_add₀ hp, show k - 1 + -k = -1 by ring, _root_.zpow_neg_one, mul_comm]
  rfl

/-- The Hecke sum is the right-hand side of `HasPrimeHeckeRelations`. -/
theorem heckeFun_apply (k : ℤ) (p : Nat.Primes) (f : ℍ → ℂ) (τ : ℍ) :
    heckeFun k p f τ =
      (p.val : ℂ) ^ (k - 1) *
          f (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate p.val p.property.pos) • τ) +
        (p.val : ℂ)⁻¹ * ∑ j : Fin p.val,
          f (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate p.val p.property.pos j) • τ) := by
  rw [heckeFun, Finset.sum_apply, Fintype.sum_option, dilate_slash_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact translate_slash_apply k p j f τ

theorem one_mem_strictPeriods : (1 : ℝ) ∈ levelOne.strictPeriods := by
  simpa only [Subgroup.strictWidthInfty_SL2Z] using levelOne.strictWidthInfty_mem_strictPeriods

/-- **`q`-expansion of `T_p f`**: `a_n(T_p f) = p^{k-1} a_{n/p}(f) + a_{pn}(f)`. -/
theorem levelOneHecke_coeff (k : ℤ) (p : Nat.Primes) (f : CuspForm levelOne k) (n : ℕ) :
    (qExpansion 1 (levelOneHecke k p f)).coeff n =
      (p.val : ℂ) ^ (k - 1) * qSeriesDilateCoefficients (fun m => (qExpansion 1 f).coeff m) p.val n +
        (qExpansion 1 f).coeff (p.val * n) := by
  have series (τ : ℍ) : HasSum (fun m =>
      ((p.val : ℂ) ^ (k - 1) * qSeriesDilateCoefficients (fun m => (qExpansion 1 f).coeff m) p.val m +
        (qExpansion 1 f).coeff (p.val * m)) • Function.Periodic.qParam 1 τ ^ m)
      (levelOneHecke k p f τ) := by
    rw [show (levelOneHecke k p f τ) = heckeFun k p f τ from rfl, heckeFun_apply]
    simp only [smul_eq_mul]
    apply qSeries_hecke_hasSum _ τ p.val p.property.pos
    · simpa only [binaryHeckeDilate_smul] using
        ModularForm.hasSum_qExpansion f (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate p.val p.property.pos) • τ)
    · intro j
      simpa only [binaryHeckeTranslate_smul] using
        ModularForm.hasSum_qExpansion f (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods
          (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate p.val p.property.pos j) • τ)
  exact (ModularFormClass.qExpansion_coeff_unique (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods
    series n).symm

/-- Two level-one cusp forms with the same `q`-expansion coefficients are equal. -/
theorem cuspForm_ext_coeff {k : ℤ} {f g : CuspForm levelOne k}
    (h : ∀ n, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) : f = g := by
  ext τ
  have hf := ModularForm.hasSum_qExpansion f (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods τ
  have hg := ModularForm.hasSum_qExpansion g (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods τ
  simp only [h] at hf
  exact hf.unique hg

section Commutation

variable {p q : ℕ}

theorem dvd_mul_iff_of_primes (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (n : ℕ) :
    p ∣ q * n ↔ p ∣ n := by
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp h) hpq
    · exact h
  · intro h
    exact Dvd.dvd.mul_left h q

theorem dilate_comp_mul (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (c : ℕ → ℂ) (n : ℕ) :
    qSeriesDilateCoefficients (fun m => c (q * m)) p n = qSeriesDilateCoefficients c p (q * n) := by
  unfold qSeriesDilateCoefficients
  by_cases h : p ∣ n
  · rw [ite_eq_left h, ite_eq_left ((dvd_mul_iff_of_primes hp hq hpq n).mpr h), Nat.mul_div_assoc _ h]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((dvd_mul_iff_of_primes hp hq hpq n).mp h'))]

theorem dilate_dilate (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (c : ℕ → ℂ) (n : ℕ) :
    qSeriesDilateCoefficients (qSeriesDilateCoefficients c q) p n =
      qSeriesDilateCoefficients (qSeriesDilateCoefficients c p) q n := by
  simp only [qSeriesDilateCoefficients]
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  by_cases hpn : p ∣ n <;> by_cases hqn : q ∣ n
  · have hqnp : q ∣ n / p := by
      obtain ⟨m, rfl⟩ := hpn
      rw [Nat.mul_div_cancel_left _ hp.pos]
      exact (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hqn)
    have hpnq : p ∣ n / q := by
      obtain ⟨m, rfl⟩ := hqn
      rw [Nat.mul_div_cancel_left _ hq.pos]
      exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hpn)
    rw [ite_eq_left hpn, ite_eq_left hqnp, ite_eq_left hqn, ite_eq_left hpnq, Nat.div_div_eq_div_mul,
      Nat.div_div_eq_div_mul, mul_comm]
  · have : ¬ q ∣ n / p := fun h => hqn (h.trans (Nat.div_dvd_of_dvd hpn))
    rw [ite_eq_left hpn, ite_eq_right this, ite_eq_right hqn]
  · have : ¬ p ∣ n / q := fun h => hpn (h.trans (Nat.div_dvd_of_dvd hqn))
    rw [ite_eq_right hpn, ite_eq_left hqn, ite_eq_right this]
  · rw [ite_eq_right hpn, ite_eq_right hqn]

theorem dilate_add_smul (c d : ℕ → ℂ) (a : ℂ) (n : ℕ) :
    qSeriesDilateCoefficients (fun m => a * c m + d m) p n =
      a * qSeriesDilateCoefficients c p n + qSeriesDilateCoefficients d p n := by
  unfold qSeriesDilateCoefficients
  split_ifs <;> simp

end Commutation

/-- **The level-one Hecke operators commute.** -/
theorem levelOneHecke_comm (k : ℤ) (p q : Nat.Primes) (f : CuspForm levelOne k) :
    levelOneHecke k p (levelOneHecke k q f) = levelOneHecke k q (levelOneHecke k p f) := by
  by_cases hpq : p = q
  · rw [hpq]
  have hne : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  apply cuspForm_ext_coeff
  intro n
  simp only [levelOneHecke_coeff, dilate_add_smul]
  rw [dilate_dilate p.property q.property hne,
    dilate_comp_mul p.property q.property hne (fun m => (qExpansion 1 f).coeff m),
    dilate_comp_mul q.property p.property hne.symm (fun m => (qExpansion 1 f).coeff m),
    show q.val * (p.val * n) = p.val * (q.val * n) by ring]
  ring

end TernaryPeriodPolynomials.Spectral.LevelOneHecke
