module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers

theorem normPower_zero (t : Adelesˣ) : normPower t 0 = 1 := by
  simp [normPower]

theorem normPower_one (z : ℂ) : normPower 1 z = 1 := by
  simp [normPower]

theorem normPower_ne_zero (t : Adelesˣ) (z : ℂ) : normPower t z ≠ 0 :=
  Complex.exp_ne_zero _

theorem normPower_add (t : Adelesˣ) (z w : ℂ) :
    normPower t (z + w) = normPower t z * normPower t w := by
  simp [normPower, add_mul, Complex.exp_add]

theorem normPower_mul (t u : Adelesˣ) (z : ℂ) :
    normPower (t * u) z = normPower t z * normPower u z := by
  have ht : (adeleNorm t : ℝ) ≠ 0 := ne_of_gt (adeleNorm_pos t)
  have hu : (adeleNorm u : ℝ) ≠ 0 := ne_of_gt (adeleNorm_pos u)
  simp only [normPower, map_mul, NNReal.coe_mul, Real.log_mul ht hu,
    Complex.ofReal_add, mul_add, Complex.exp_add]

theorem normPower_neg (t : Adelesˣ) (z : ℂ) :
    normPower t (-z) = (normPower t z)⁻¹ := by
  simp [normPower, Complex.exp_neg]

theorem norm_normPower (t : Adelesˣ) (z : ℂ) :
    ‖normPower t z‖ = Real.exp (z.re * Real.log (adeleNorm t : ℝ)) := by
  simp [normPower, Complex.norm_exp, Complex.mul_re]

theorem binaryInductionExponent_plane_sub (n : ℕ) (s : ℂ) :
    binaryInductionExponent n .plane s -
      binaryInductionExponent n .plane cohomologicalPoint =
    (s - cohomologicalPoint) / 3 := by
  simp only [binaryInductionExponent, inductionExponent]
  ring

theorem flatSection_planeLevi {n : ℕ} {D : InducingData n}
    {F : ℂ → AdelicGL → ℂ} (hF : IsFlatSection D F)
    (s : ℂ) (A : BinaryAdelicGL) (k : AdelicGL) (hk : inMaximalCompact k) :
    F s (planeLevi A 1 * k) =
      normPower (Matrix.GeneralLinearGroup.det A) ((s - cohomologicalPoint) / 3) *
        F cohomologicalPoint (planeLevi A 1 * k) := by
  have heq := hF.2.2 s A k hk
  have hmul := congrArg
    (fun value => normPower (Matrix.GeneralLinearGroup.det A)
      (binaryInductionExponent n .plane s) * value) heq
  rw [normPower_neg, mul_inv_cancel_left₀ (normPower_ne_zero _ _),
    ← mul_assoc, ← normPower_add] at hmul
  simpa only [← sub_eq_add_neg, binaryInductionExponent_plane_sub] using hmul

theorem induced_planeOrbit_bound {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f) (g : AdelicGL) :
    ∃ C : ℝ, ∀ A : BinaryAdelicGL,
      ‖f (planeLevi A 1 * g)‖ ≤
        Real.exp ((binaryInductionExponent n .plane s).re *
          Real.log (adeleNorm (Matrix.GeneralLinearGroup.det A) : ℝ)) * C := by
  have horbit := hf.2.2.2.2.2 g
  rcases horbit with ⟨v, hv⟩
  rcases D.cusp.bounded v with ⟨C, hC⟩
  refine ⟨C, fun A => ?_⟩
  have heq := congrFun hv A
  have hvalue : f (planeLevi A 1 * g) =
      normPower (Matrix.GeneralLinearGroup.det A)
        (binaryInductionExponent n .plane s) * D.cusp.realize v A := by
    rw [heq, binaryInductionExponent, normPower_neg,
      mul_inv_cancel_left₀ (normPower_ne_zero _ _)]
  rw [hvalue, norm_mul, norm_normPower]
  exact mul_le_mul_of_nonneg_left (hC A) (Real.exp_pos _).le

theorem planeLevi_split (A : BinaryAdelicGL) (t : Adelesˣ) :
    planeLevi A t = planeLevi 1 t * planeLevi A 1 := by
  have h := (planeLeviHom Adeles).map_mul (1, t) (A, 1)
  change planeLevi (1 * A) (t * 1) = planeLevi 1 t * planeLevi A 1 at h
  simpa only [one_mul, mul_one] using h

theorem induced_planeLevi_scalar {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f)
    (A : BinaryAdelicGL) (t : Adelesˣ) (g : AdelicGL) :
    f (planeLevi A t * g) =
      D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane s) *
        f (planeLevi A 1 * g) := by
  rw [planeLevi_split, mul_assoc]
  exact hf.2.2.2.2.1 t _

theorem flatSection_planeCuspVector {n : ℕ} {D : InducingData n}
    {F : ℂ → AdelicGL → ℂ} (hF : IsFlatSection D F)
    (k : AdelicGL) (hk : inMaximalCompact k) :
    ∃ v : D.cusp.smooth, ∀ s A,
      F s (planeLevi A 1 * k) =
        normPower (Matrix.GeneralLinearGroup.det A)
          (binaryInductionExponent n .plane s) * D.cusp.realize v A := by
  rcases (hF.1 cohomologicalPoint).2.2.2.2.2 k with ⟨v, hv⟩
  refine ⟨v, fun s A => ?_⟩
  have hnormalized :
      normPower (Matrix.GeneralLinearGroup.det A)
        (-binaryInductionExponent n .plane s) * F s (planeLevi A 1 * k) =
      D.cusp.realize v A := by
    rw [hF.2.2 s A k hk]
    exact (congrFun hv A).symm
  have hvalue := congrArg
    (fun value => normPower (Matrix.GeneralLinearGroup.det A)
      (binaryInductionExponent n .plane s) * value) hnormalized
  simpa only [normPower_neg, mul_inv_cancel_left₀ (normPower_ne_zero _ _)] using hvalue

theorem flatSection_planeParabolic_formula {n : ℕ} {D : InducingData n}
    {F : ℂ → AdelicGL → ℂ} (hF : IsFlatSection D F)
    (k : AdelicGL) (hk : inMaximalCompact k) :
    ∃ v : D.cusp.smooth, ∀ s A t a b,
      F s (planeUnipotent a b * (planeLevi A t * k)) =
        D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane s) *
          (normPower (Matrix.GeneralLinearGroup.det A)
            (binaryInductionExponent n .plane s) * D.cusp.realize v A) := by
  rcases flatSection_planeCuspVector hF k hk with ⟨v, hv⟩
  refine ⟨v, fun s A t a b => ?_⟩
  rw [(hF.1 s).2.2.2.1 a b, induced_planeLevi_scalar (hF.1 s), hv]

theorem flatSection_planeParabolic_bound {n : ℕ} {D : InducingData n}
    {F : ℂ → AdelicGL → ℂ} (hF : IsFlatSection D F)
    (k : AdelicGL) (hk : inMaximalCompact k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s A t a b,
      ‖F s (planeUnipotent a b * (planeLevi A t * k))‖ ≤
        Real.exp ((-2 * inductionExponent .plane s).re *
          Real.log (adeleNorm t : ℝ)) *
        Real.exp ((binaryInductionExponent n .plane s).re *
          Real.log (adeleNorm (Matrix.GeneralLinearGroup.det A) : ℝ)) * C := by
  rcases flatSection_planeParabolic_formula hF k hk with ⟨v, hv⟩
  rcases D.cusp.bounded v with ⟨C, hC⟩
  refine ⟨C, (norm_nonneg _).trans (hC 1), fun s A t a b => ?_⟩
  rw [hv, norm_mul, norm_mul, norm_mul, D.chi.unitary, one_mul,
    norm_normPower, norm_normPower, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC A)
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)

theorem flatSection_summand_analytic {n : ℕ} {D : InducingData n}
    {F : ℂ → AdelicGL → ℂ} (hF : IsFlatSection D F)
    (g : AdelicGL) (q : Flags .plane) (s : ℂ) :
    AnalyticAt ℂ (fun z => eisensteinSummand F z g q) s :=
  hF.2.1 _ s

theorem continuation_summable {F E : ℂ → AdelicGL → ℂ}
    (hE : IsEisensteinContinuation F E) :
    ∃ R : ℝ, ∀ s : ℂ, R < s.re → ∀ g, Summable (eisensteinSummand F s g) := by
  rcases hE.2 with ⟨R, hR⟩
  exact ⟨R, fun s hs g => (hR s hs g).summable⟩

theorem continuation_eq_tsum {F E : ℂ → AdelicGL → ℂ}
    (hE : IsEisensteinContinuation F E) :
    ∃ R : ℝ, ∀ s : ℂ, R < s.re → ∀ g,
      E s g = ∑' q : Flags .plane, eisensteinSummand F s g q := by
  rcases hE.2 with ⟨R, hR⟩
  exact ⟨R, fun s hs g => (hR s hs g).tsum_eq.symm⟩

theorem continuation_eq_on_halfPlane {F E E' : ℂ → AdelicGL → ℂ}
    (hE : IsEisensteinContinuation F E) (hE' : IsEisensteinContinuation F E') :
    ∃ R : ℝ, ∀ s : ℂ, R < s.re → ∀ g, E s g = E' s g := by
  rcases hE.2 with ⟨R, hR⟩
  rcases hE'.2 with ⟨R', hR'⟩
  refine ⟨max R R', fun s hs g => ?_⟩
  exact (hR s (lt_of_le_of_lt (le_max_left _ _) hs) g).unique
    (hR' s (lt_of_le_of_lt (le_max_right _ _) hs) g)

theorem zero_eisensteinContinuation :
    IsEisensteinContinuation (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨fun _ s => MeromorphicAt.const 0 s, 0, fun _ _ _ => ?_⟩
  exact hasSum_zero

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers
