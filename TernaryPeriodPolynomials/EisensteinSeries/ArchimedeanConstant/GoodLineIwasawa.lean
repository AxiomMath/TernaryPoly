module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.ParabolicCompact
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.ArchimedeanIntegral

@[expose] public section


/-!
# The plane Iwasawa data of the real good-line argument

For any factorization `g = p k` of a real matrix with `p` in the plane parabolic and `k`
orthogonal, the scalar Levi entry satisfies `p₂₂² = ‖g₂‖²` (the squared norm of the last row of
`g`), and `|det A · p₂₂| = |det g|` for the `GL₂` block `A` of `p`. For the real good-line
argument `g(u) = w⁻¹ n_Q(u) γ_good` this gives `p₂₂² = 1 + |u|²` and `|det A| = (1 + |u|²)^{-1/2}`:
the modulus factors governing the decay of induced sections along the standard integral.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.ArchimedeanConstant

theorem orthogonal_rows {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) : k * kᵀ = 1 :=
  mul_eq_one_comm.mp hk

/-- The last row of `g = p k` is `p₂₂` times the unit last row of `k`. -/
theorem plane_factor_lastRow {g p k : RealGL3} (hp : p ∈ planeParabolic ℝ)
    (hk : k.val.transpose * k.val = 1) (h : g = p * k) :
    (p.val 2 2) ^ 2 = ∑ j, (g.val 2 j) ^ 2 := by
  obtain ⟨h0, h1⟩ := hp
  have hrow : ∀ j, g.val 2 j = p.val 2 2 * k.val 2 j := by
    intro j
    rw [h, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
    change p.val 2 0 * _ + p.val 2 1 * _ + _ = _
    rw [h0, h1]
    ring
  have hkk := congrFun (congrFun (orthogonal_rows hk) 2) 2
  rw [Matrix.mul_apply, Fin.sum_univ_three] at hkk
  simp only [transpose_apply, one_apply_eq] at hkk
  rw [Fin.sum_univ_three, hrow, hrow, hrow]
  linear_combination (p.val 2 2) ^ 2 * hkk.symm

/-- `|det A · p₂₂| = |det g|` for the plane factorization. -/
theorem plane_factor_det {g p k : RealGL3} (hp : p ∈ planeParabolic ℝ)
    (hk : k.val.transpose * k.val = 1) (h : g = p * k) :
    |(p.val 0 0 * p.val 1 1 - p.val 0 1 * p.val 1 0) * p.val 2 2| = |g.val.det| := by
  obtain ⟨h0, h1⟩ := hp
  have hdk : k.val.det ^ 2 = 1 := by
    have := congrArg Matrix.det hk
    rwa [det_mul, det_transpose, det_one, ← sq] at this
  have habs : |k.val.det| = 1 := by
    have : |k.val.det| ^ 2 = 1 := by rw [sq_abs, hdk]
    nlinarith [abs_nonneg k.val.det, sq_nonneg (|k.val.det| - 1)]
  have hdp : p.val.det = (p.val 0 0 * p.val 1 1 - p.val 0 1 * p.val 1 0) * p.val 2 2 := by
    rw [det_fin_three]
    change _ = _ at h0
    have e0 : p.val 2 0 = 0 := h0
    have e1 : p.val 2 1 = 0 := h1
    rw [e0, e1]
    ring
  rw [← hdp, h, Units.val_mul, det_mul, abs_mul, habs, mul_one]

theorem goodLineArgument_val (u : ℝ × ℝ) :
    (SphericalDetection.Helpers.standardGoodLineRealArgument u).val =
      !![0, 1, 0; 1, 0, 0; u.2, u.1, 1] := by
  have hw : ((weyl : RealGL3)⁻¹).val = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := rfl
  simp only [SphericalDetection.Helpers.standardGoodLineRealArgument, Units.val_mul, hw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SphericalDetection.Helpers.rationalGoodLine, lineUnipotent, upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]

/-- **Iwasawa data of the good-line argument.** For every plane factorization
`g(u) = p k`, `p₂₂² = 1 + |u|²` and `|det A| · |p₂₂| = 1`. -/
theorem goodLine_iwasawa_data (u : ℝ × ℝ) {p k : RealGL3} (hp : p ∈ planeParabolic ℝ)
    (hk : k.val.transpose * k.val = 1)
    (h : SphericalDetection.Helpers.standardGoodLineRealArgument u = p * k) :
    (p.val 2 2) ^ 2 = 1 + u.1 ^ 2 + u.2 ^ 2 ∧
      |p.val 0 0 * p.val 1 1 - p.val 0 1 * p.val 1 0| * |p.val 2 2| = 1 := by
  have h1 := plane_factor_lastRow hp hk h
  have h2 := plane_factor_det hp hk h
  rw [goodLineArgument_val, Fin.sum_univ_three] at h1
  rw [goodLineArgument_val, det_fin_three] at h2
  refine ⟨?_, ?_⟩
  · rw [h1]; simp; ring
  · rw [← abs_mul, h2]; simp

/-- Every good-line argument has a plane factorization, with these Iwasawa data. -/
theorem goodLine_iwasawa (u : ℝ × ℝ) :
    ∃ (p : planeParabolic ℝ) (k : RealGL3), k.val.transpose * k.val = 1 ∧
      SphericalDetection.Helpers.standardGoodLineRealArgument u = p.val * k ∧
      (p.val.val 2 2) ^ 2 = 1 + u.1 ^ 2 + u.2 ^ 2 ∧
      |p.val.val 0 0 * p.val.val 1 1 - p.val.val 0 1 * p.val.val 1 0| * |p.val.val 2 2| = 1 := by
  obtain ⟨p, k, hk, h⟩ :=
    SphericalDetection.Helpers.realGL_parabolic_compact_factorization
      (SphericalDetection.Helpers.standardGoodLineRealArgument u)
  exact ⟨p, k, hk, h, goodLine_iwasawa_data u p.property hk h⟩

end TernaryPeriodPolynomials.ArchimedeanConstant
