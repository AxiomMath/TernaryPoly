module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.DisjointSupport
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AwayGood

@[expose] public section


/-!
# Integrality away from a place; `Good` matrices are in the local level at three

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix IsDedekindDomain
open TernaryPeriodPolynomials.HeckeStability.AdelicApproximation

namespace TernaryPeriodPolynomials.HeckeCommutativity

theorem intAt_inv_intCast (v : FinitePlace) (n : ℤ) (h : ¬ (placePrime v : ℤ) ∣ n) :
    IntAt v ((n : ℚ)⁻¹) := by
  obtain ⟨u, hu⟩ := isUnit_intCast_of_not_dvd v n h
  unfold IntAt
  rw [map_inv₀, map_intCast]
  have h1 : ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) *
      (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) :
        v.adicCompletion ℚ) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv]
    rfl
  rw [hu] at h1
  have h2 : ((n : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = (n : v.adicCompletion ℚ) := by
    simp
  rw [h2] at h1
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact SetLike.coe_mem _

theorem placePrime_ne_three {v : FinitePlace} (hv : v ≠ placeThree) : placePrime v ≠ 3 := by
  intro h
  apply hv
  have : Rat.HeightOneSpectrum.primesEquiv v = primeThree := Subtype.ext h
  rw [placeThree, ← this, Equiv.symm_apply_apply]

theorem not_dvd_three_pow {v : FinitePlace} (hv : v ≠ placeThree) (k : ℕ) :
    ¬ (placePrime v : ℤ) ∣ (3 : ℤ) ^ k := by
  intro h
  have h' : placePrime v ∣ 3 ^ k := by exact_mod_cast h
  have hp := (placePrime_fact v).out
  have h3 := hp.dvd_of_dvd_pow h'
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ h3) with h1 | h1
  · exact hp.one_lt.ne' h1
  · exact placePrime_ne_three hv h1

theorem intAt_three_inv {n : ℤ} (h : ¬ (3 : ℤ) ∣ n) : IntAt placeThree ((n : ℚ)⁻¹) := by
  apply intAt_inv_intCast
  rw [TernaryPeriodPolynomials.HeckeStability.CosetDecomposition.placePrime_placeThree]
  exact_mod_cast h

theorem intAt_zsmul {v : FinitePlace} (n : ℤ) {q : ℚ} (hq : IntAt v q) : IntAt v (n • q) := by
  rw [zsmul_eq_mul]
  exact intAt_mul (intAt_intCast v n) hq

theorem intAt_det {v : FinitePlace} {A : Matrix (Fin 3) (Fin 3) ℚ} (hA : ∀ i j, IntAt v (A i j)) :
    IntAt v A.det := by
  rw [Matrix.det_apply]
  apply intAt_sum
  intro σ _
  rw [Units.smul_def]
  apply intAt_zsmul
  rw [Fin.prod_univ_three]
  exact intAt_mul (intAt_mul (hA _ _) (hA _ _)) (hA _ _)

theorem intAt_adjugate {v : FinitePlace} {A : Matrix (Fin 3) (Fin 3) ℚ}
    (hA : ∀ i j, IntAt v (A i j)) : ∀ i j, IntAt v (A.adjugate i j) := by
  intro i j
  rw [Matrix.adjugate_apply]
  apply intAt_det
  intro k l
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs
    · exact intAt_one v
    · exact intAt_zero v
  · exact hA _ _

/-- `Good` matrices lie in the local level at three. -/
theorem locK_three_of_good {x : RationalGL3} (hx : Good x) : LocK x placeThree := by
  obtain ⟨m, hm, X, hX, hXd, hXr⟩ := hx
  have hm3 : ¬ (3 : ℤ) ∣ m := fun h => hm ((ZMod.intCast_zmod_eq_zero_iff_dvd m 3).mpr
    (by exact_mod_cast h))
  have hd3 : ¬ (3 : ℤ) ∣ X.det := fun h => hXd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr
    (by exact_mod_cast h))
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h
    apply hm3
    rw [show m = 0 by exact_mod_cast h]
    exact dvd_zero _
  have hxval : x.val = (m : ℚ)⁻¹ • X.map (Int.cast : ℤ → ℚ) := by
    rw [← hX, smul_smul, inv_mul_cancel₀ hm0, one_smul]
  have hent : ∀ i j, IntAt placeThree (x.val i j) := by
    intro i j
    rw [hxval, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact intAt_mul (intAt_three_inv hm3) (intAt_intCast _ _)
  refine ⟨hent, ?_, ?_⟩
  · intro i j
    have hdet : x.val.det = (m : ℚ)⁻¹ ^ 3 * (X.det : ℚ) := by
      rw [hxval, Matrix.det_smul, Fintype.card_fin]
      congr 1
      have := RingHom.map_det (Int.castRingHom ℚ) X
      simpa using this.symm
    have hinv : (x⁻¹).val = (x.val.det)⁻¹ • x.val.adjugate := by
      rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
    rw [hinv, Matrix.smul_apply, smul_eq_mul]
    apply intAt_mul _ (intAt_adjugate hent i j)
    rw [hdet, mul_inv, inv_pow, inv_inv]
    have : ((m : ℚ) ^ 3) = ((m ^ 3 : ℤ) : ℚ) := by push_cast; ring
    rw [this]
    exact intAt_mul (intAt_intCast _ _) (intAt_three_inv hd3)
  · intro _ j
    have h3 : (3 : ℤ) ∣ X 2 j - if j = 2 then m else 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      push_cast
      rw [hXr j]
      split_ifs <;> simp
    obtain ⟨k, hk⟩ := h3
    have e : ((x.val 2 j - if j = 2 then 1 else 0) / 3 : ℚ) = (k : ℚ) * (m : ℚ)⁻¹ := by
      rw [hxval, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      have hk' : ((X 2 j : ℤ) : ℚ) - ((if j = 2 then m else 0 : ℤ) : ℚ) = 3 * k := by
        exact_mod_cast hk
      field_simp
      split_ifs at hk' ⊢ <;> push_cast at hk' <;> linear_combination hk'
    rw [e]
    exact intAt_mul (intAt_intCast _ _) (intAt_three_inv hm3)

end TernaryPeriodPolynomials.HeckeCommutativity
