module

public import TernaryPeriodPolynomials.SymmetricSpace.CellGeometry.Radius

@[expose] public section


/-!
# Appendix B cell calculation: the Voronoi cell of `0` for `C(t)` is exactly the hexagon of the three Voronoi inequalities

Formalized by Claude Sonnet 5.5.  Paper: "For `t ≥ 0` this follows from the Voronoi inequalities
`|w₁ + t w₂|, |t w₁ + w₂| ≤ 1/2` and `|w₁ - w₂| ≤ 1`. ... A sign flip handles `t ≤ 0`."  "Conversely, the inequalities for `(1,z)` in that cell are exactly
the same Voronoi inequalities."

`voronoi_iff_nonneg` (`0 ≤ t ≤ 1/2`): `w ∈ Voronoi (C(t))` iff `|w₁ + t w₂| ≤ 1/2`, `|t w₁ + w₂| ≤ 1/2`, `|w₁ - w₂| ≤ 1`.
`voronoi_iff_nonpos` (`-1/2 ≤ t ≤ 0`): the same with `|w₁ + w₂| ≤ 1` in place of `|w₁ - w₂| ≤ 1`.
(`Geometry.voronoi_inequalities` proves the necessity; the sufficiency, by a lattice computation, is new.)
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBCellGeometry

open TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry Matrix

/-- `a² - 2aP ≥ 0` for an integer `a` and `|P| ≤ 1/2`. -/
theorem sq_sub_ge (a : ℤ) {P : ℝ} (hP : |P| ≤ 1 / 2) : 0 ≤ (a : ℝ) ^ 2 - 2 * a * P := by
  have h := abs_le.mp hP
  rcases le_or_gt 0 a with ha | ha
  · have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have := int_aux a
    nlinarith [mul_nonneg ha' (by linarith : (0 : ℝ) ≤ 1 / 2 - P)]
  · have ha' : (a : ℝ) ≤ 0 := by exact_mod_cast ha.le
    have := int_aux (-a)
    push_cast at this
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -(a : ℝ)) (by linarith : (0 : ℝ) ≤ P + 1 / 2)]

/-- The integer inequality `a² + c² - ac - 2a + c ≥ 0` for `a ≥ c ≥ 1`. -/
theorem int_E {a c : ℤ} (hc : 1 ≤ c) (hca : c ≤ a) :
    0 ≤ (a : ℝ) ^ 2 + (c : ℝ) ^ 2 - a * c - 2 * a + c := by
  have h1 := int_aux c
  have h2 := int_aux (a - c)
  push_cast at h2
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hd : (0 : ℝ) ≤ (a : ℝ) - c := by
    have : (c : ℝ) ≤ a := by exact_mod_cast hca
    linarith
  nlinarith [mul_nonneg hd (by linarith : (0 : ℝ) ≤ (c : ℝ) - 1)]

theorem mixed_core {t : ℝ} (h1 : t ≤ 1 / 2) (a c : ℤ) (ha : 1 ≤ a) (hc : 1 ≤ c) (P R : ℝ)
    (hP : |P| ≤ 1 / 2) (hR : |R| ≤ 1 / 2) (hPR : |P - R| ≤ 1 - t) :
    0 ≤ (a : ℝ) ^ 2 - 2 * t * a * c + (c : ℝ) ^ 2 - 2 * a * P + 2 * c * R := by
  have hP' := abs_le.mp hP
  have hR' := abs_le.mp hR
  have hPR' := abs_le.mp hPR
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  rcases le_total c a with hca | hac
  · have hE := int_E hc hca
    have hca' : (c : ℝ) ≤ a := by exact_mod_cast hca
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a) (by linarith : (0 : ℝ) ≤ 1 - t - (P - R)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (a : ℝ) - c) (by linarith : (0 : ℝ) ≤ 1 / 2 - R),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - t) (mul_nonneg (by linarith : (0 : ℝ) ≤ a) (by linarith : (0 : ℝ) ≤ (c : ℝ) - 1))]
  · have hE := int_E ha hac
    have hac' : (a : ℝ) ≤ c := by exact_mod_cast hac
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c) (by linarith : (0 : ℝ) ≤ 1 - t - (P - R)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (c : ℝ) - a) (by linarith : (0 : ℝ) ≤ P + 1 / 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - t) (mul_nonneg (by linarith : (0 : ℝ) ≤ c) (by linarith : (0 : ℝ) ≤ (a : ℝ) - 1))]

/-- The lattice inequality `a² + 2t ab + b² - 2aP - 2bR ≥ 0` under the three Voronoi inequalities (`0 ≤ t ≤ 1/2`). -/
theorem voronoi_suff {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) (a b : ℤ) (P R : ℝ) (hP : |P| ≤ 1 / 2) (hR : |R| ≤ 1 / 2)
    (hPR : |P - R| ≤ 1 - t) :
    0 ≤ (a : ℝ) ^ 2 + 2 * t * a * b + (b : ℝ) ^ 2 - 2 * a * P - 2 * b * R := by
  rcases le_or_gt 0 (a * b) with hab | hab
  · have hab' : (0 : ℝ) ≤ (a : ℝ) * b := by exact_mod_cast hab
    nlinarith [sq_sub_ge a hP, sq_sub_ge b hR, mul_nonneg h0 hab']
  · rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have := mixed_core h1 a (-b) (by omega) (by omega) P R hP hR hPR
      push_cast at this
      nlinarith [this]
    · have := mixed_core h1 (-a) b (by omega) (by omega) (-P) (-R) (by rwa [abs_neg]) (by rwa [abs_neg])
        (by rw [show -P - -R = -(P - R) by ring, abs_neg]; exact hPR)
      push_cast at this
      nlinarith [this]

theorem voronoi_iff_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) (w : Vec2) :
    w ∈ Voronoi (Ct t) ↔
      |w 0 + t * w 1| ≤ 1 / 2 ∧ |t * w 0 + w 1| ≤ 1 / 2 ∧ |w 0 - w 1| ≤ 1 := by
  have ht : |t| ≤ 1 / 2 := by rw [abs_of_nonneg h0]; exact h1
  rw [mem_Voronoi_iff ht]
  constructor
  · intro h
    obtain ⟨hp, hr, hd, -⟩ := voronoi_inequalities w h
    exact ⟨hp, hr, hd (by linarith)⟩
  · rintro ⟨hp, hr, hd⟩ z
    have hPR : |(w 0 + t * w 1) - (t * w 0 + w 1)| ≤ 1 - t := by
      have e : (w 0 + t * w 1) - (t * w 0 + w 1) = (1 - t) * (w 0 - w 1) := by ring
      rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
      nlinarith [abs_nonneg (w 0 - w 1)]
    have key := voronoi_suff h0 h1 (z 0) (z 1) _ _ hp hr hPR
    simp only [quad_Ct, Pi.sub_apply, intVec]
    nlinarith [key]

/-- The same for `-1/2 ≤ t ≤ 0` (the sign flip `(t, w₂) ↦ (-t, -w₂)`). -/
theorem voronoi_iff_nonpos {t : ℝ} (h0 : t ≤ 0) (h1 : -(1 / 2) ≤ t) (w : Vec2) :
    w ∈ Voronoi (Ct t) ↔
      |w 0 + t * w 1| ≤ 1 / 2 ∧ |t * w 0 + w 1| ≤ 1 / 2 ∧ |w 0 + w 1| ≤ 1 := by
  have ht : |t| ≤ 1 / 2 := by rw [abs_of_nonpos h0]; linarith
  have ht' : |-t| ≤ 1 / 2 := by rw [abs_neg]; exact ht
  let w' : Vec2 := ![w 0, -w 1]
  have hflip : w ∈ Voronoi (Ct t) ↔ w' ∈ Voronoi (Ct (-t)) := by
    rw [mem_Voronoi_iff ht, mem_Voronoi_iff ht']
    constructor
    · intro h z
      have := h ![z 0, -z 1]
      simp only [quad_Ct, Pi.sub_apply, intVec, w', Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_neg] at this ⊢
      nlinarith [this]
    · intro h z
      have := h ![z 0, -z 1]
      simp only [quad_Ct, Pi.sub_apply, intVec, w', Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_neg] at this ⊢
      nlinarith [this]
  rw [hflip, voronoi_iff_nonneg (by linarith) (by linarith)]
  simp only [w', Matrix.cons_val_zero, Matrix.cons_val_one]
  have e1 : w 0 + -t * -w 1 = w 0 + t * w 1 := by ring
  have e2 : -t * w 0 + -w 1 = -(t * w 0 + w 1) := by ring
  have e3 : w 0 - -w 1 = w 0 + w 1 := by ring
  rw [e1, e2, e3, abs_neg]

end TernaryPeriodPolynomials.Argument.AppendixBCellGeometry
