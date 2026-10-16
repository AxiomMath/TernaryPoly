module

public import TernaryPeriodPolynomials.EisensteinSeries.ArchimedeanConstant.GoodLineIwasawa
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.PlaneVectors
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PlaneParabolicDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.FlatSectionWeight
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.FlatParameterScaling
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.CompactReduction
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Norm

@[expose] public section


/-!
# Decay of plane-induced sections along the good-line standard integral

At the cohomological point the plane modulus exponent vanishes, so a plane-induced section `f`
satisfies `‖f(p g)‖ = ‖f(m_A g)‖` for a real plane-parabolic `p` with `GL₂` block `A`, and
`‖f(m_A g)‖ = |det A|^{(n+3)/2} ‖φ_g(A)‖` for the bounded cusp function `φ_g`. Along the good-line
argument `g(u) = p(u) k(u)` this gives the bound `(1+|u|²)^{-(n+3)/4} · C`, where `C` depends on
the compact factor `k(u)` and the remaining argument (the cusp bounds of `CuspidalRepresentation`
are per vector).

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.ArchimedeanConstant

variable {n : ℕ}

theorem plane_exponent_cohomological : inductionExponent .plane cohomologicalPoint = 0 := by
  simp only [inductionExponent, cohomologicalPoint]; norm_num

/-- At the cohomological point, a real plane-parabolic factor reduces to its `GL₂` block. -/
theorem induced_real_parabolic (D : InducingData n) {f : AdelicGL → ℂ}
    (hf : IsInduced D .plane cohomologicalPoint f) (p : planeParabolic ℝ) :
    ∃ B : BinaryRealGL, B.val.det * p.val.val 2 2 = p.val.val.det ∧
      ∀ g, ‖f (atInfinity p.val * g)‖ = ‖f (planeLevi (atInfinity B) 1 * g)‖ := by
  obtain ⟨a, b, s, B, hp⟩ := SphericalDetection.Helpers.planeParabolic_exists_decomposition p
  refine ⟨B, ?_, ?_⟩
  · rw [hp]
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.det_fin_three, Matrix.det_fin_two,
      Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · intro g
    obtain ⟨_, _, _, hunip, hlevi, _⟩ := hf
    rw [hp, EisensteinRegularization.Helpers.atInfinity_mul,
      EisensteinRegularization.Helpers.atInfinity_mul,
      EisensteinRegularization.Helpers.atInfinity_planeUnipotent,
      EisensteinRegularization.Helpers.atInfinity_planeLevi,
      EisensteinRegularization.Helpers.atInfinity_planeLevi, mul_assoc, mul_assoc, hunip]
    have h1 : atInfinity (1 : BinaryRealGL) = 1 := by
      apply Units.ext
      refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;> by_cases hij : i = j <;>
        simp [atInfinity, combineGL, pairMatrix, hij]
    have h2 : realAdeleUnit (1 : ℝˣ) = 1 := by
      apply Units.ext; rfl
    rw [h1, h2, hlevi, plane_exponent_cohomological, mul_zero,
      SphericalDetection.Helpers.normPower_zero_exponent, mul_one, norm_mul,
      D.chi.unitary, one_mul]

theorem normPower_norm (t : Adelesˣ) (z : ℝ) :
    ‖normPower t (z : ℂ)‖ = (adeleNorm t : ℝ) ^ z := by
  rw [normPower, Complex.norm_exp]
  have hpos : (0 : ℝ) < adeleNorm t := by
    have h := congrArg adeleNorm (mul_inv_cancel t)
    rw [map_mul, map_one] at h
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h))
  rw [← Complex.ofReal_mul, Complex.ofReal_re, Real.rpow_def_of_pos hpos, mul_comm]

/-- The `GL₂` block bound. -/
theorem induced_levi_bound (D : InducingData n) {f : AdelicGL → ℂ}
    (hf : IsInduced D .plane cohomologicalPoint f) (Y : AdelicGL) :
    ∃ C : ℝ, ∀ B : BinaryRealGL,
      ‖f (planeLevi (atInfinity B) 1 * Y)‖ ≤ |B.val.det| ^ (((n : ℝ) + 3) / 2) * C := by
  obtain ⟨_, _, _, _, _, hcusp⟩ := hf
  obtain ⟨v, hv⟩ := hcusp Y
  obtain ⟨C, hC⟩ := D.cusp.bounded v
  refine ⟨C, fun B => ?_⟩
  have hval := congrFun hv (atInfinity B)
  simp only [plane_exponent_cohomological, add_zero] at hval
  set t := GeneralLinearGroup.det (atInfinity B)
  have hinv := HeckeEigen.np_neg t (((n : ℂ) + 3) / 2)
  have hf' : f (planeLevi (atInfinity B) 1 * Y) =
      normPower t (((n : ℂ) + 3) / 2) * D.cusp.realize v (atInfinity B) := by
    rw [hval, ← mul_assoc, hinv, one_mul]
  have ht : (adeleNorm t : ℝ) = |B.val.det| := by
    change (adeleNorm (GeneralLinearGroup.det (atInfinity B)) : ℝ) = _
    rw [EisensteinRegularization.Helpers.det_atInfinity_binary,
      EisensteinRegularization.Helpers.adeleNorm_realAdeleUnit]
    rfl
  have hcast : ((n : ℂ) + 3) / 2 = ((((n : ℝ) + 3) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hf', norm_mul, hcast, normPower_norm, ht]
  exact mul_le_mul_of_nonneg_left (hC _) (Real.rpow_nonneg (abs_nonneg _) _)

/-- **Decay along the good-line argument**, with a constant depending on the compact factor. -/
theorem goodLine_induced_decay (D : InducingData n) {f : AdelicGL → ℂ}
    (hf : IsInduced D .plane cohomologicalPoint f) (u : ℝ × ℝ) (h : AdelicGL) :
    ∃ C : ℝ, ‖f (atInfinity (SphericalDetection.Helpers.standardGoodLineRealArgument u) * h)‖ ≤
      (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C := by
  obtain ⟨p, k, hk, hg, hsq, hdet⟩ := goodLine_iwasawa u
  obtain ⟨B, hB, hred⟩ := induced_real_parabolic D hf p
  obtain ⟨C, hC⟩ := induced_levi_bound D hf (atInfinity k * h)
  refine ⟨C, ?_⟩
  have hpos : (0 : ℝ) < 1 + u.1 ^ 2 + u.2 ^ 2 := by positivity
  -- `|det B| = (1+|u|²)^{-1/2}`
  have habsdet : |p.val.val.det| = |p.val.val 0 0 * p.val.val 1 1 - p.val.val 0 1 * p.val.val 1 0| *
      |p.val.val 2 2| := by
    rw [← abs_mul]
    congr 1
    have h0 : p.val.val 2 0 = 0 := p.property.1
    have h1 : p.val.val 2 1 = 0 := p.property.2
    rw [Matrix.det_fin_three, h0, h1]
    ring
  have h22 : |p.val.val 2 2| = Real.sqrt (1 + u.1 ^ 2 + u.2 ^ 2) := by
    rw [← hsq, Real.sqrt_sq_eq_abs]
  have hBdet : |B.val.det| = (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(1 / 2 : ℝ)) := by
    have e1 : |B.val.det| * |p.val.val 2 2| = 1 := by
      rw [← abs_mul, hB, habsdet, hdet]
    rw [h22] at e1
    rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow]
    exact eq_inv_of_mul_eq_one_left e1
  rw [hg, EisensteinRegularization.Helpers.atInfinity_mul, mul_assoc, hred]
  refine (hC B).trans (le_of_eq ?_)
  rw [hBdet, ← Real.rpow_mul hpos.le]
  congr 2
  ring

end TernaryPeriodPolynomials.ArchimedeanConstant
