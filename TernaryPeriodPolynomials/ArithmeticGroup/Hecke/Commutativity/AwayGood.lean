module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AwayDoubleCoset

@[expose] public section


/-!
# Away-from-three correspondences are `Good`

The defining matrix of an `AwayThree` correspondence, scaled by a common
denominator prime to three, is an integer matrix of determinant prime to three
whose last row is congruent to the scaled `e₃*`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.HeckeCommutativity

theorem ne_zero_of_zmod_ne_zero {b : ℤ} (hb : (b : ZMod 3) ≠ 0) : (b : ℚ) ≠ 0 := by
  intro h
  apply hb
  have : b = 0 := by exact_mod_cast h
  rw [this]
  simp

theorem exists_common_denominator (y : Matrix (Fin 3) (Fin 3) ℚ)
    (hy : ∀ i j, IntegralAtThree (y i j)) :
    ∃ m : ℤ, (m : ZMod 3) ≠ 0 ∧ ∃ Y : Matrix (Fin 3) (Fin 3) ℤ,
      (m : ℚ) • y = Y.map (Int.cast : ℤ → ℚ) := by
  classical
  choose a b hb hab using hy
  refine ⟨∏ ij : Fin 3 × Fin 3, b ij.1 ij.2, ?_,
    Matrix.of fun i j => a i j * ∏ ij ∈ Finset.univ.erase (i, j), b ij.1 ij.2, ?_⟩
  · rw [Int.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun ij _ => hb _ _)
  · apply Matrix.ext
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.of_apply]
    rw [← Finset.mul_prod_erase Finset.univ (fun ij : Fin 3 × Fin 3 => b ij.1 ij.2)
      (Finset.mem_univ (i, j)), hab i j]
    have hb0 := ne_zero_of_zmod_ne_zero (hb i j)
    push_cast
    field_simp

theorem good_of_integral (x : RationalGL3)
    (hint : ∀ i j, IntegralAtThree (x.val i j) ∧ IntegralAtThree ((x⁻¹).val i j))
    (hrow : ∀ j, IntegralAtThree ((x.val 2 j - if j = 2 then 1 else 0) / 3)) : Good x := by
  obtain ⟨m, hm, X, hX⟩ := exists_common_denominator x.val (fun i j => (hint i j).1)
  obtain ⟨m', hm', Y, hY⟩ := exists_common_denominator (x⁻¹).val (fun i j => (hint i j).2)
  refine ⟨m, hm, X, hX, ?_, ?_⟩
  · have hXY : X.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) =
        ((m * m' : ℤ) : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
      rw [← hX, ← hY, Matrix.smul_mul, Matrix.mul_smul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, smul_smul]
      push_cast
      ring_nf
    have hcast : ∀ M : Matrix (Fin 3) (Fin 3) ℤ,
        ((M.det : ℤ) : ℚ) = (M.map (Int.cast : ℤ → ℚ)).det := by
      intro M
      have := RingHom.map_det (Int.castRingHom ℚ) M
      simpa using this
    have hdetQ : ((X.det * Y.det : ℤ) : ℚ) = (((m * m') ^ 3 : ℤ) : ℚ) := by
      have := congrArg Matrix.det hXY
      rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
      rw [Int.cast_mul, hcast, hcast, this]
      push_cast
      ring
    have hdetZ : X.det * Y.det = (m * m') ^ 3 := by exact_mod_cast hdetQ
    intro h0
    have := congrArg (Int.cast : ℤ → ZMod 3) hdetZ
    rw [Int.cast_mul, Int.cast_pow, Int.cast_mul, h0, zero_mul] at this
    exact pow_ne_zero 3 (mul_ne_zero hm hm') this.symm
  · intro j
    obtain ⟨c, e, he, hce⟩ := hrow j
    have he0 := ne_zero_of_zmod_ne_zero he
    have hX2 : (X 2 j : ℚ) = m * x.val 2 j := by
      have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => M 2 j) hX
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at this
      exact this.symm
    have key : e * (X 2 j - if j = 2 then m else 0) = 3 * (m * c) := by
      have hQ : (e : ℚ) * ((X 2 j : ℚ) - if j = 2 then (m : ℚ) else 0) = 3 * ((m : ℚ) * c) := by
        rw [hX2]
        have h3 : (x.val 2 j - if j = 2 then 1 else 0) = 3 * ((c : ℚ) / e) := by
          rw [← hce]
          ring
        have h4 : (m : ℚ) * x.val 2 j - (if j = 2 then (m : ℚ) else 0) =
            (m : ℚ) * (x.val 2 j - if j = 2 then 1 else 0) := by
          split_ifs <;> ring
        rw [h4, h3]
        field_simp
      split_ifs at hQ ⊢ <;> exact_mod_cast hQ
    have hk := congrArg (Int.cast : ℤ → ZMod 3) key
    push_cast at hk
    have h30 : (3 : ZMod 3) = 0 := rfl
    rw [h30, zero_mul] at hk
    have := (mul_eq_zero.mp hk).resolve_left he
    split_ifs at this ⊢ with hj
    · exact sub_eq_zero.mp (by simpa using this)
    · erw [sub_zero] at this
      exact this

/-- Away-from-three correspondences have `Good` defining matrices. -/
theorem good_of_awayThree {t : HeckeCorrespondence} (ht : AwayThree t) : Good t.g :=
  good_of_integral t.g ht.1 ht.2

end TernaryPeriodPolynomials.HeckeCommutativity
