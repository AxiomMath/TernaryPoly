module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Geometry

@[expose] public section


/-!
# Appendix B cell calculation: the covering radius of `C(t)` is exactly `1/(2(1+|t|))`

Formalized by Claude Sonnet 5.5.  Paper: `lem:literal-residue-comparison`, proof, the paragraph
"For `C(t)` the covering radius squared is `1/(2(1+|t|)) ≤ 1/2`.  For `t ≥ 0` this follows from the Voronoi inequalities ...  All vertices have that
squared length.  A sign flip handles `t ≤ 0`."

The upper bound is `Geometry.deltaSq_Ct_le`.  Here the sharpness is added: the vertex `(s, s)`, `s = 1/(2(1+t))` (resp. `(s, -s)` for `t ≤ 0`) of the Voronoi
hexagon of `0` is at squared distance exactly `1/(2(1+|t|))` from the lattice (`deltaSq_vertex`), so
`coveringRadiusSq (Ct t) = 1/(2(1+|t|))` (`coveringRadiusSq_Ct`, as a greatest element).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBCellGeometry

open TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry Matrix

/-- The squared covering radius of the lattice `ℤ²` for the form `C`: the supremum of `δ_C(w)²`. -/
def coveringRadiusSq (C : Mat2) : ℝ := ⨆ w : Vec2, deltaSq C w

/-- The vertex of the Voronoi hexagon of `0` for `C(t)`: `w₁ + t w₂ = 1/2 = t w₁ + w₂` (`t ≥ 0`), with the sign flip for `t ≤ 0`. -/
def vertexPt (t : ℝ) : Vec2 := if 0 ≤ t then ![1 / (2 * (1 + t)), 1 / (2 * (1 + t))] else ![1 / (2 * (1 - t)), -(1 / (2 * (1 - t)))]

theorem int_aux (a : ℤ) : (0 : ℝ) ≤ (a : ℝ) ^ 2 - a := by
  rcases le_or_gt a 0 with h | h
  · have : (a : ℝ) ≤ 0 := by exact_mod_cast h
    nlinarith
  · have : (1 : ℝ) ≤ a := by exact_mod_cast h
    nlinarith

/-- The lattice inequality behind the Voronoi vertex: `a² + 2t a b + b² - a - b ≥ 0` for integers `a, b` and `0 ≤ t ≤ 1/2`. -/
theorem vertex_ineq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) (a b : ℤ) :
    0 ≤ (a : ℝ) ^ 2 + 2 * t * a * b + (b : ℝ) ^ 2 - a - b := by
  have hA := int_aux a
  have hB := int_aux b
  rcases le_or_gt 0 (a * b) with hab | hab
  · have hab' : (0 : ℝ) ≤ (a : ℝ) * b := by exact_mod_cast hab
    nlinarith [mul_nonneg h0 hab']
  · rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have hb'' : b ≤ -1 := by omega
      have hb' : (b : ℝ) ≤ -1 := by exact_mod_cast hb''
      have hneg : (a : ℝ) * b ≤ 0 := by nlinarith
      nlinarith [sq_nonneg ((a : ℝ) + b), mul_nonneg (by linarith : (0 : ℝ) ≤ (a : ℝ) + 1)
        (by linarith : (0 : ℝ) ≤ -((b : ℝ) + 1)), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * t)
        (by linarith : (0 : ℝ) ≤ -((a : ℝ) * b))]
    · have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have ha'' : a ≤ -1 := by omega
      have ha' : (a : ℝ) ≤ -1 := by exact_mod_cast ha''
      have hneg : (a : ℝ) * b ≤ 0 := by nlinarith
      nlinarith [sq_nonneg ((a : ℝ) + b), mul_nonneg (by linarith : (0 : ℝ) ≤ (b : ℝ) + 1)
        (by linarith : (0 : ℝ) ≤ -((a : ℝ) + 1)), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * t)
        (by linarith : (0 : ℝ) ≤ -((a : ℝ) * b))]

theorem quad_vertex {t : ℝ} (ht : |t| ≤ 1 / 2) : quad (Ct t) (vertexPt t) = 1 / (2 * (1 + |t|)) := by
  have h := abs_le.mp ht
  unfold vertexPt
  split_ifs with h0
  · rw [abs_of_nonneg h0, quad_Ct]
    have : (0 : ℝ) < 1 + t := by linarith
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  · push Not at h0
    rw [abs_of_neg h0, quad_Ct, show (1 : ℝ) + -t = 1 - t by ring]
    have : (1 : ℝ) - t ≠ 0 := by linarith
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring

/-- **The vertex is a deep hole**: `0` is a nearest lattice point of the vertex. -/
theorem vertex_nearest {t : ℝ} (ht : |t| ≤ 1 / 2) (z : Fin 2 → ℤ) :
    quad (Ct t) (vertexPt t) ≤ quad (Ct t) (vertexPt t - intVec z) := by
  have h := abs_le.mp ht
  unfold vertexPt
  split_ifs with h0
  · have key := vertex_ineq h0 h.2 (z 0) (z 1)
    have hs : (1 + t) * (1 / (2 * (1 + t))) = 1 / 2 := by
      have : (0 : ℝ) < 1 + t := by linarith
      field_simp
    generalize 1 / (2 * (1 + t)) = s at hs ⊢
    simp only [quad_Ct, Pi.sub_apply, intVec, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h2 : 2 * s * (1 + t) = 1 := by linarith [hs]
    have e2 : 2 * s * (1 + t) * ((z 0 : ℝ) + z 1) = (z 0 : ℝ) + z 1 := by rw [h2, one_mul]
    nlinarith [key, e2]
  · push Not at h0
    have key := vertex_ineq (t := -t) (by linarith) (by linarith) (z 0) (-(z 1))
    have hs : (1 - t) * (1 / (2 * (1 - t))) = 1 / 2 := by
      have : (0 : ℝ) < 1 - t := by linarith
      field_simp
    generalize 1 / (2 * (1 - t)) = s at hs ⊢
    simp only [quad_Ct, Pi.sub_apply, intVec, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast at key
    have h2 : 2 * s * (1 - t) = 1 := by linarith [hs]
    have e2 : 2 * s * (1 - t) * ((z 0 : ℝ) - z 1) = (z 0 : ℝ) - z 1 := by rw [h2, one_mul]
    nlinarith [key, e2]

/-- **All vertices have that squared length**: the distance of the Voronoi vertex to the lattice is `1/(2(1+|t|))`. -/
theorem deltaSq_vertex {t : ℝ} (ht : |t| ≤ 1 / 2) : deltaSq (Ct t) (vertexPt t) = 1 / (2 * (1 + |t|)) := by
  have hpsd : ∀ v, 0 ≤ quad (Ct t) v := quad_Ct_nonneg (by linarith [abs_nonneg t])
  apply le_antisymm
  · refine le_trans (deltaSq_le hpsd _ 0) ?_
    have e : intVec (0 : Fin 2 → ℤ) = 0 := by funext i; simp [intVec]
    rw [e, sub_zero, quad_vertex ht]
  · rw [← quad_vertex ht]
    exact le_deltaSq (vertex_nearest ht)

/-- **The covering radius**: for `|t| ≤ 1/2` the squared covering radius of `ℤ²` for `C(t)` is `1/(2(1+|t|))`, attained at the Voronoi vertex. -/
theorem coveringRadiusSq_isGreatest {t : ℝ} (ht : |t| ≤ 1 / 2) :
    IsGreatest (Set.range fun w : Vec2 => deltaSq (Ct t) w) (1 / (2 * (1 + |t|))) :=
  ⟨⟨vertexPt t, deltaSq_vertex ht⟩, by rintro _ ⟨w, rfl⟩; exact deltaSq_Ct_le ht w⟩

theorem coveringRadiusSq_Ct {t : ℝ} (ht : |t| ≤ 1 / 2) : coveringRadiusSq (Ct t) = 1 / (2 * (1 + |t|)) :=
  (coveringRadiusSq_isGreatest ht).csSup_eq

/-- The squared covering radius is at most `1/2` (the bound giving `1 - δ² ≥ 1/2`). -/
theorem coveringRadiusSq_le_half {t : ℝ} (ht : |t| ≤ 1 / 2) : coveringRadiusSq (Ct t) ≤ 1 / 2 := by
  rw [coveringRadiusSq_Ct ht, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [abs_nonneg t]

end TernaryPeriodPolynomials.Argument.AppendixBCellGeometry
