module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Parabolic.LevelThreeStabilizers

@[expose] public section


/-!
# Every rational cusp of `Γ₁'(3)` is equivalent to `∞` or `0`

For every frame of `GL₂(ℚ)` there is `h ∈ Γ = binaryArithmeticLevel` conjugating the cusp stabilizer
`binaryCuspLevel frame` into the stabilizer of `∞` (`binaryCuspLevel 1`) or of `0`
(`binaryCuspLevel swapQ`) (`exists_cusp_conj`). With `Parabolic/LevelThreeStabilizers` this shows that
a crossed class trivial at `T` and `L` is trivial at every cusp.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (swapQ swapQ_inv)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic

/-- The upper triangular subgroup of `GL₂(ℚ)`. -/
def borelQ : Subgroup (GeneralLinearGroup (Fin 2) ℚ) where
  carrier := {A | A.val 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB
    change (A.val * B.val) 1 0 = 0
    have hA' : A.val 1 0 = 0 := hA
    have hB' : B.val 1 0 = 0 := hB
    simp [Matrix.mul_apply, Fin.sum_univ_two, hA', hB']
  inv_mem' := by
    intro A hA
    have hA' : A.val 1 0 = 0 := hA
    change (A⁻¹).val 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [hA']

theorem conj_cusp (frame f : GeneralLinearGroup (Fin 2) ℚ) (h : binaryArithmeticLevel)
    (hb : f⁻¹ * (GeneralLinearGroup.map (Int.castRingHom ℚ) h.val)⁻¹ * frame ∈ borelQ) :
    ∀ γ ∈ binaryCuspLevel frame, h⁻¹ * γ * h ∈ binaryCuspLevel f := by
  intro γ hγ
  rw [mem_binaryCuspLevel_iff] at hγ ⊢
  set H := GeneralLinearGroup.map (Int.castRingHom ℚ) h.val with hH
  set b := f⁻¹ * H⁻¹ * frame with hbdef
  have hγ' : frame⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) γ.val * frame ∈ borelQ := hγ
  have e : frame⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) γ.val * frame =
      b⁻¹ * (f⁻¹ * (H⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) γ.val * H) * f) * b := by
    simp only [hbdef]; group
  rw [e] at hγ'
  have h2 : f⁻¹ * (H⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) γ.val * H) * f ∈ borelQ := by
    have := borelQ.mul_mem (borelQ.mul_mem hb hγ') (borelQ.inv_mem hb)
    simpa [mul_assoc] using this
  have e2 : GeneralLinearGroup.map (Int.castRingHom ℚ) (h⁻¹ * γ * h).val =
      H⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) γ.val * H := by
    simp [hH]
  rw [e2]
  exact h2

/-- The element of `Γ` with the given determinant-one integral matrix. -/
def levelOfEntries (a b c d : ℤ) (hdet : a * d - b * c = 1) (h10 : ((c : ℤ) : ZMod 3) = 0)
    (h11 : ((d : ℤ) : ZMod 3) = 1) : binaryArithmeticLevel :=
  ⟨SpecialLinearGroup.toGL
    (⟨!![a, b; c, d], by simpa [Matrix.det_fin_two] using hdet⟩ : SpecialLinearGroup (Fin 2) ℤ),
    (mem_binaryArithmeticLevel_iff _).mpr (by
      intro column
      fin_cases column
      · exact h10
      · exact h11)⟩

/-- Entries of the rational inverse of such a level element (the adjugate). -/
theorem map_levelOfEntries_inv (a b c d : ℤ) (hdet h10 h11) (i j : Fin 2) :
    ((GeneralLinearGroup.map (Int.castRingHom ℚ) (levelOfEntries a b c d hdet h10 h11).val)⁻¹).val
        i j =
      !![(d : ℚ), -(b : ℚ); -(c : ℚ), (a : ℚ)] i j := by
  set g : SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two] using hdet⟩ with hg
  rw [← map_inv]
  have this : (levelOfEntries a b c d hdet h10 h11).val⁻¹ = SpecialLinearGroup.toGL g⁻¹ := by
    change (SpecialLinearGroup.toGL g)⁻¹ = _
    rw [map_inv]
  rw [this]
  have e : ((SpecialLinearGroup.toGL g⁻¹ : GeneralLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![d, -b; -c, a] := by
    rw [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.SL2_inv_expl]
    rfl
  change (Int.castRingHom ℚ).mapMatrix
    ((SpecialLinearGroup.toGL g⁻¹ : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [e]
  fin_cases i <;> fin_cases j <;> simp

/-- Conjugation to the cusp `∞` from a primitive first column. -/
theorem conj_one_of_column (frame : GeneralLinearGroup (Fin 2) ℚ) (a b c d : ℤ)
    (hdet : a * d - b * c = 1) (h10 : ((c : ℤ) : ZMod 3) = 0) (h11 : ((d : ℤ) : ZMod 3) = 1)
    (hcol : -(c : ℚ) * frame.val 0 0 + (a : ℚ) * frame.val 1 0 = 0) :
    ∃ h : binaryArithmeticLevel, ∀ γ ∈ binaryCuspLevel frame, h⁻¹ * γ * h ∈ binaryCuspLevel 1 := by
  refine ⟨levelOfEntries a b c d hdet h10 h11, conj_cusp frame 1 _ ?_⟩
  change (1⁻¹ * (GeneralLinearGroup.map (Int.castRingHom ℚ)
    (levelOfEntries a b c d hdet h10 h11).val)⁻¹ * frame).val 1 0 = 0
  rw [inv_one, one_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
    map_levelOfEntries_inv, map_levelOfEntries_inv]
  simp
  linarith

/-- Conjugation to the cusp `0` from a primitive second column. -/
theorem conj_swap_of_column (frame : GeneralLinearGroup (Fin 2) ℚ) (a b c d : ℤ)
    (hdet : a * d - b * c = 1) (h10 : ((c : ℤ) : ZMod 3) = 0) (h11 : ((d : ℤ) : ZMod 3) = 1)
    (hcol : (d : ℚ) * frame.val 0 0 - (b : ℚ) * frame.val 1 0 = 0) :
    ∃ h : binaryArithmeticLevel, ∀ γ ∈ binaryCuspLevel frame,
      h⁻¹ * γ * h ∈ binaryCuspLevel swapQ := by
  refine ⟨levelOfEntries a b c d hdet h10 h11, conj_cusp frame swapQ _ ?_⟩
  change (swapQ⁻¹ * (GeneralLinearGroup.map (Int.castRingHom ℚ)
    (levelOfEntries a b c d hdet h10 h11).val)⁻¹ * frame).val 1 0 = 0
  rw [swapQ_inv]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, map_levelOfEntries_inv]
  simp [swapQ]
  linarith

theorem exists_sign (z : ℤ) (hz : ¬ (3 : ℤ) ∣ z) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (((s * z : ℤ)) : ZMod 3) = 1 := by
  have h : z % 3 = 1 ∨ z % 3 = 2 := by omega
  rcases h with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    have : ((1 : ℤ) : ZMod 3) = ((1 * z : ℤ) : ZMod 3) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      omega
    simpa using this.symm
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have : ((1 : ℤ) : ZMod 3) = ((-1 * z : ℤ) : ZMod 3) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      omega
    simpa using this.symm

/-- **Every cusp frame is conjugate under `Γ` to `∞` or `0`.** -/
theorem exists_cusp_conj (frame : GeneralLinearGroup (Fin 2) ℚ) :
    (∃ h : binaryArithmeticLevel,
      ∀ γ ∈ binaryCuspLevel frame, h⁻¹ * γ * h ∈ binaryCuspLevel 1) ∨
      (∃ h : binaryArithmeticLevel,
        ∀ γ ∈ binaryCuspLevel frame, h⁻¹ * γ * h ∈ binaryCuspLevel swapQ) := by
  by_cases hv1 : frame.val 1 0 = 0
  · refine Or.inl ⟨1, conj_cusp frame 1 1 ?_⟩
    change (1⁻¹ * (GeneralLinearGroup.map (Int.castRingHom ℚ) (1 : binaryArithmeticLevel).val)⁻¹ *
      frame).val 1 0 = 0
    simpa using hv1
  · set v0 := frame.val 0 0 with hv0
    set v1 := frame.val 1 0 with hv1'
    set t : ℚ := v0 / v1 with ht
    set p : ℤ := t.num with hp
    set q : ℤ := (t.den : ℤ) with hq
    have hqpos : (0 : ℚ) < q := by rw [hq]; exact_mod_cast t.den_pos
    have hcop : IsCoprime p q := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [hp, hq, Int.gcd] using t.reduced
    have hcross : v0 * q = v1 * p := by
      have h1 : (p : ℚ) / (q : ℚ) = v0 / v1 := by
        rw [← ht]; simp [hp, hq, Rat.num_div_den]
      field_simp at h1
      linarith
    by_cases h3 : (3 : ℤ) ∣ q
    · -- first column (s p, s q), with s p ≡ 1
      have hp3 : ¬ (3 : ℤ) ∣ p := by
        intro hdp
        have : IsCoprime (3 : ℤ) 3 := by
          exact (hcop.of_isCoprime_of_dvd_left hdp).of_isCoprime_of_dvd_right h3
        have h33 : IsUnit (3 : ℤ) := isCoprime_self.mp this
        exact absurd (Int.isUnit_iff.mp h33) (by decide)
      obtain ⟨s, hs, hsp⟩ := exists_sign p hp3
      have hcop' : IsCoprime (s * p) (s * q) := by
        rcases hs with rfl | rfl
        · simpa using hcop
        · simpa using hcop.neg_neg
      obtain ⟨u, w, huw⟩ := hcop'
      refine Or.inl (conj_one_of_column frame (s * p) (-w) (s * q) u (by linarith) ?_ ?_ ?_)
      · have : (3 : ℤ) ∣ s * q := Dvd.dvd.mul_left h3 s
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr this
      · have hz : ((u * (s * p) + w * (s * q) : ℤ) : ZMod 3) = 1 := by rw [huw]; simp
        have hq0 : ((s * q : ℤ) : ZMod 3) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (Dvd.dvd.mul_left h3 s)
        push_cast at hz hq0 hsp ⊢
        rw [hsp] at hz
        simpa [hq0] using hz
      · push_cast
        have : ((s : ℚ) * (v0 * q - v1 * p)) = 0 := by rw [hcross]; ring
        linarith
    · -- second column (s p, s q), with s q ≡ 1
      obtain ⟨s, hs, hsq⟩ := exists_sign q h3
      have hc3 : IsCoprime (3 : ℤ) q := (Int.prime_three.irreducible).coprime_iff_not_dvd.mpr h3
      have hcop' : IsCoprime (s * q) (3 * (s * p)) := by
        have h1 : IsCoprime (s * q) (s * p) := by
          rcases hs with rfl | rfl
          · simpa using hcop.symm
          · simpa using hcop.symm.neg_neg
        have h2 : IsCoprime (s * q) 3 := by
          rcases hs with rfl | rfl
          · simpa using hc3.symm
          · simpa using hc3.symm.neg_left
        exact h2.mul_right h1
      obtain ⟨u, w, huw⟩ := hcop'
      refine Or.inr (conj_swap_of_column frame u (s * p) (-(3 * w)) (s * q) (by linarith) ?_ hsq ?_)
      · have : (3 : ℤ) ∣ -(3 * w) := by simp
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr this
      · push_cast
        have : ((s : ℚ) * (v0 * q - v1 * p)) = 0 := by rw [hcross]; ring
        linarith

end TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
