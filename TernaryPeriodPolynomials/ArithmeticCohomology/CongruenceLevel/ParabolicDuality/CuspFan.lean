module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspOrientation

@[expose] public section


/-!
# The fan of triangles at a cusp and the stabilizer of a cusp in `Γ(N)`

Formalized by Claude Sonnet 5.5.  Context: `ar:eq:facepair`.

* `Tk k = [[1, k], [0, 1]]`: the translations, which fix the cusp `cusp₁ = ∞` and shift the fan of triangles `T^k •` at `∞`;
* `fan_classification`: the oriented dual edges whose head is `cusp₁` are exactly `Tk k • p0.swap`, `k ∈ ℤ` (`Tk_swap_inj`: distinct);
* `gammaN_stab_cusp1`: for `N ≥ 3` the stabilizer of `cusp₁` in `Γ(N)` is `{Tk (N j)}`;
* `gammaN_isSL`, `gammaN_conj`: `Γ(N) ⊆ SL₂(ℤ)` is normal in `GL₂(ℤ)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

section GammaFacts

theorem gammaN_conj {N : ℕ} {k g : IntegralGL} (hg : g ∈ gammaNGL N) : k * g * k⁻¹ ∈ gammaNGL N := by
  have := (MonoidHom.normal_ker (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod N)) :
    IntegralGL →* GL (Fin 2) (ZMod N))).conj_mem _ hg k
  simpa [gammaNGL] using this

/-- A unit in `{±1}` congruent to `1` modulo `N ≥ 3` is `1`. -/
theorem eq_one_of_cast {N : ℕ} (hN : 3 ≤ N) {a : ℤ} (ha : a = 1 ∨ a = -1) (h : ((a : ℤ) : ZMod N) = 1) : a = 1 := by
  rcases ha with ha | ha
  · exact ha
  · exfalso
    rw [ha] at h
    have h' : (-1 : ZMod N) = 1 := by simpa using h
    have h2 : ((2 : ℤ) : ZMod N) = 0 := by
      calc ((2 : ℤ) : ZMod N) = 1 - (-1) := by push_cast; ring
        _ = 1 - 1 := by rw [h']
        _ = 0 := sub_self _
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    have := Int.le_of_dvd (by norm_num) h2
    omega

theorem gammaN_isSL {N : ℕ} (hN : 3 ≤ N) {g : IntegralGL} (hg : g ∈ gammaNGL N) : IsSL g := by
  rw [mem_gammaNGL] at hg
  obtain ⟨a, b, c, d⟩ := hg
  have hd : ((g.val.det : ℤ) : ZMod N) = 1 := by
    rw [Matrix.det_fin_two]
    push_cast
    rw [a, b, c, d]; simp
  exact eq_one_of_cast hN (det_cases g) hd

end GammaFacts

section Fan

/-- The translation `[[1, k], [0, 1]]`. -/
def Tk (k : ℤ) : IntegralGL := colGL e1 (k • e1 + e2) (Or.inl (by simp [det2, e1, e2]))

theorem Tk_00 (k : ℤ) : (Tk k).val 0 0 = 1 := by simp [Tk, colGL_val_zero, e1]
theorem Tk_01 (k : ℤ) : (Tk k).val 0 1 = k := by simp [Tk, colGL_val_one, e1, e2]
theorem Tk_10 (k : ℤ) : (Tk k).val 1 0 = 0 := by simp [Tk, colGL_val_zero, e1]
theorem Tk_11 (k : ℤ) : (Tk k).val 1 1 = 1 := by simp [Tk, colGL_val_one, e1, e2]

theorem Tk_add (a b : ℤ) : Tk (a + b) = Tk a * Tk b := by
  apply eq_of_entries <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Tk_00, Tk_01, Tk_10, Tk_11, add_comm]

theorem Tk_zero : Tk 0 = 1 := by
  apply eq_of_entries <;> simp [Tk_00, Tk_01, Tk_10, Tk_11]

theorem Tk_isSL (k : ℤ) : IsSL (Tk k) := by
  simp [IsSL, Matrix.det_fin_two, Tk_00, Tk_01, Tk_10, Tk_11]

theorem Tk_cusp1 (k : ℤ) : Tk k • cusp1 = cusp1 :=
  smul_cusp1_eq isGen_cusp1 (Or.inl (by funext i; fin_cases i <;> simp [Tk_00, Tk_10, e1]))

/-- The matrix `-1`, which acts trivially. -/
def neg1 : IntegralGL := colGL (-e1) (-e2) (Or.inl (by simp [det2, e1, e2]))

theorem neg1_mem : neg1 ∈ MulAction.stabilizer IntegralGL p0 := by
  apply stab_p0_of_entries
  right; left
  simp [neg1, colGL_val_zero, colGL_val_one, e1, e2]

theorem neg1_smul (q : OTE) : neg1 • q = q := by
  obtain ⟨g, rfl⟩ := ote_transitive q
  have hc : neg1 * g = g * neg1 := by
    apply eq_of_entries <;>
      simp [neg1, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, colGL_val_zero, colGL_val_one, e1, e2]
  rw [← mul_smul, hc, mul_smul, MulAction.mem_stabilizer_iff.mp neg1_mem]

/-- The matrices of `SL₂(ℤ)` fixing `cusp₁` are `±` translations. -/
theorem stab_cusp1_form {m : IntegralGL} (hm : IsSL m) (h : m • cusp1 = cusp1) :
    ∃ b : ℤ, m = Tk b ∨ m = neg1 * Tk (-b) := by
  have hg : IsGen cusp1 (fun i => m.val i 0) := by
    rw [← h, smul_cusp1]; exact col_isGen m 0
  rcases isGen_cusp1.eq_or_neg hg with hc | hc
  · have a : m.val 0 0 = 1 := by simpa [e1] using congrFun hc 0
    have c : m.val 1 0 = 0 := by simpa [e1] using congrFun hc 1
    have hdet : m.val 1 1 = 1 := by
      have := hm
      unfold IsSL at this
      rw [Matrix.det_fin_two, a, c] at this
      linarith
    refine ⟨m.val 0 1, Or.inl ?_⟩
    apply eq_of_entries <;> simp [Tk_00, Tk_01, Tk_10, Tk_11, a, c, hdet]
  · have a : m.val 0 0 = -1 := by simpa [e1] using congrFun hc 0
    have c : m.val 1 0 = 0 := by simpa [e1] using congrFun hc 1
    have hdet : m.val 1 1 = -1 := by
      have := hm
      unfold IsSL at this
      rw [Matrix.det_fin_two, a, c] at this
      linarith
    refine ⟨m.val 0 1, Or.inr ?_⟩
    apply eq_of_entries <;>
      simp [neg1, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, colGL_val_zero, colGL_val_one, e1, e2,
        Tk_00, Tk_01, Tk_10, Tk_11, a, c, hdet]

/-- **The oriented dual edges whose head is `cusp₁`** are the translates `Tk k • p0.swap` (the fan of triangles at `∞`). -/
theorem fan_classification {q : OTE} (h : head q = cusp1) : ∃ k : ℤ, q = Tk k • p0.swap := by
  obtain ⟨h0, hsl, hq⟩ := ote_transitive_sl q
  rw [head_eq hsl hq] at h
  have hm : IsSL (h0 * wSwap⁻¹) := hsl.mul wSwap_det.inv
  have hm1 : (h0 * wSwap⁻¹) • cusp1 = cusp1 := by
    rw [mul_smul, inv_smul_eq_iff.mpr wSwap_cusp2.symm, h]
  have hq' : q = (h0 * wSwap⁻¹) • p0.swap := by
    rw [mul_smul, ← wSwap_p0, inv_smul_smul, hq]
  obtain ⟨b, hb | hb⟩ := stab_cusp1_form hm hm1
  · exact ⟨b, by rw [hq', hb]⟩
  · exact ⟨-b, by rw [hq', hb, mul_smul, neg1_smul]⟩

theorem Tk_swap_head (k : ℤ) : head (Tk k • p0.swap) = cusp1 := by
  rw [head_smul (Tk_isSL k), head_swap, tail_p0, Tk_cusp1]

theorem Tk_swap_fix {m : ℤ} (h : Tk m • p0.swap = p0.swap) : m = 0 := by
  have h1 : tail (Tk m • p0.swap) = tail p0.swap := by rw [h]
  rw [tail_smul (Tk_isSL m), tail_swap, head_p0] at h1
  have hg : IsGen cusp2 (fun i => (Tk m).val i 1) := by
    rw [← h1, smul_cusp2]; exact col_isGen (Tk m) 1
  rcases isGen_cusp2.eq_or_neg hg with hc | hc
  · simpa [e2, Tk_01] using congrFun hc 0
  · simpa [e2, Tk_01] using congrFun hc 0

theorem Tk_swap_inj {k l : ℤ} (h : Tk k • p0.swap = Tk l • p0.swap) : k = l := by
  have h1 : Tk (-k + l) • p0.swap = p0.swap := by
    rw [Tk_add, mul_smul, ← h, ← mul_smul, ← Tk_add]
    simp [Tk_zero]
  have := Tk_swap_fix h1
  omega

end Fan

section GammaStab

/-- **The stabilizer of the cusp `cusp₁` in `Γ(N)`** (`N ≥ 3`) consists of the translations `Tk (N j)`. -/
theorem gammaN_stab_cusp1 {N : ℕ} (hN : 3 ≤ N) {γ : IntegralGL} (hγ : γ ∈ gammaNGL N) (h : γ • cusp1 = cusp1) :
    ∃ j : ℤ, γ = Tk (N * j) := by
  have hsl := gammaN_isSL hN hγ
  have hmem := (mem_gammaNGL.mp hγ)
  obtain ⟨b, hb | hb⟩ := stab_cusp1_form hsl h
  · have h01 : ((γ.val 0 1 : ℤ) : ZMod N) = 0 := hmem.2.1
    rw [hb, Tk_01, ZMod.intCast_zmod_eq_zero_iff_dvd] at h01
    obtain ⟨j, hj⟩ := h01
    exact ⟨j, by rw [hb, hj]⟩
  · exfalso
    have h00 := hmem.1
    rw [hb] at h00
    have : (neg1 * Tk (-b)).val 0 0 = -1 := by
      simp [neg1, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, colGL_val_zero, colGL_val_one, e1, e2,
        Tk_00, Tk_10]
    rw [this] at h00
    have := eq_one_of_cast hN (Or.inr rfl) h00
    omega

theorem Tk_mem_gammaN {N : ℕ} (j : ℤ) : Tk (N * j) ∈ gammaNGL N := by
  rw [mem_gammaNGL]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Tk_00, Tk_01, Tk_10, Tk_11]

end GammaStab

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
