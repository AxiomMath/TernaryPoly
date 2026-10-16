module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Frozen
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.JetSmooth
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.JetCalculus
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Cauchy
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

@[expose] public section


/-!
# All-order bound for a single term of the series (Appendix C.3, Proposition C.4)

`term_jet_bound`: on a compact `K ⊂ Ω`, every iterated derivative of every coefficient of every
summand is bounded by a constant multiple of `t(g q)^{-(n+3)/2}`, uniformly in `g ∈ SL₃(ℝ)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### Uniform jets of the universal functions, and the all-order term bound -/

theorem jet_bound_family {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : Par → (Fin 5 → ℝ) → F)
    (hV : ∀ z, GoodPar z → ∀ x ∈ Omega,
      ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => V p.1 p.2) (z, x))
    {K : Set (Fin 5 → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Omega) (N : ℕ) :
    ∃ C : ℝ, ∀ z : Par, z.1 ∈ SOrth → z.2 ∈ K → ∀ r, r ≤ N →
      ‖iteratedFDeriv ℝ r (V z) z.2‖ ≤ C := by
  have hZ : IsCompact (SOrth ×ˢ K : Set Par) := isCompact_SOrth.prod hK
  set W : Set (Par × (Fin 5 → ℝ)) := (fun z : Par => (z, z.2)) '' (SOrth ×ˢ K) with hWdef
  have hW : IsCompact W := hZ.image (by fun_prop)
  have hgood : ∀ w ∈ W, ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => V p.1 p.2) w := by
    rintro w ⟨z, ⟨hz1, hz2⟩, rfl⟩
    exact hV z ⟨hz1.2, hKΩ hz2⟩ z.2 (hKΩ hz2)
  have hC : ∀ r : ℕ, ∃ C : ℝ, ∀ w ∈ W, ‖iteratedFDeriv ℝ r (V w.1) w.2‖ ≤ C :=
    fun r => exists_bound_iteratedFDeriv_family r V W hW hgood
  choose C hC using hC
  refine ⟨∑ r ∈ Finset.range (N + 1), |C r|, fun z hz1 hz2 r hr => ?_⟩
  have h1 := hC r (z, z.2) ⟨z, ⟨hz1, hz2⟩, rfl⟩
  refine h1.trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun r => |C r|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hr))

theorem Psi_basePt {z : Par} (hz : z.1 ∈ SOrth) (hq : z.2 ∈ Omega) : Psi z z.2 = basePt := by
  unfold Psi
  rw [planeAct_planePinv_self hq]
  exact planeAct_basePt_of_orthogonal hz.1

theorem Psi_mem {z : Par} (hz : z.1 ∈ SOrth) (hq : z.2 ∈ Omega) {x : Fin 5 → ℝ}
    (hx : x ∈ Omega) : Psi z x ∈ Omega :=
  planeAct_mem hz.2 (planeAct_mem (det_planePinv hq) hx)

theorem coeff_frozen_eq (n : ℕ) (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    {q : Fin 5 → ℝ} (hq : q ∈ Omega) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) :
    (summandPoly n h g x i j).coeff m =
      slashTwisted (n + 3) (planeA (planeAct g q)) h (uTau (matToFun (kFactor g q), q) x) *
        uTheta i j (matToFun (kFactor g q), q) x * uPoly n m (matToFun (kFactor g q), q) x := by
  rw [summandPoly_frozen n h hg hq hx i j, coeff_linear_pow, scalarPullback_seedForm0]
  rfl

theorem contDiffOn_of_family {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Par → (Fin 5 → ℝ) → F}
    (hV : ∀ z, GoodPar z → ∀ x ∈ Omega,
      ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => V p.1 p.2) (z, x))
    {z : Par} (hz : GoodPar z) : ContDiffOn ℝ ∞ (V z) Omega := by
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  have := (hV z hz x hx).comp x (contDiffAt_const.prodMk contDiffAt_id)
  exact this

theorem hV_uTau : ∀ z, GoodPar z → ∀ x ∈ Omega,
    ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => uTau p.1 p.2) (z, x) :=
  fun _ hz _ hx => contDiffAt_uTau hz hx

theorem hV_uTheta (i j : Fin 5) : ∀ z, GoodPar z → ∀ x ∈ Omega,
    ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => uTheta i j p.1 p.2) (z, x) :=
  fun _ hz _ hx => contDiffAt_uTheta i j hz hx

theorem hV_uPoly (n : ℕ) (m : Fin 3 →₀ ℕ) : ∀ z, GoodPar z → ∀ x ∈ Omega,
    ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => uPoly n m p.1 p.2) (z, x) :=
  fun _ hz _ hx => contDiffAt_uPoly n m hz hx

theorem contDiffOn_hA (n : ℕ) {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h upperHalf) {p : Fin 5 → ℝ}
    (hp : p ∈ Omega) : ContDiffOn ℝ ∞ (slashTwisted (n + 3) (planeA p) h) upperHalf :=
  (((differentiableOn_hA (n + 3) hd hp).contDiffOn isOpen_upperHalf).restrict_scalars ℝ).of_le
    (by exact_mod_cast le_top)

/-- **All-order bound for a single term.** On a compact `K ⊂ Ω`, every iterated derivative of
every coefficient of every summand is bounded by a constant multiple of `t(g q)^{-(n+3)/2}`. -/
theorem term_jet_bound (n : ℕ) (h : ℂ → ℂ) (Ch : ℝ)
    (hh : ∀ τ : ℂ, 0 < τ.im → ‖h τ‖ * τ.im ^ (((n : ℝ) + 3) / 2) ≤ Ch)
    (hd : DifferentiableOn ℂ h upperHalf) {K : Set (Fin 5 → ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ Omega) (N : ℕ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ∃ C : ℝ, ∀ (g : Matrix (Fin 3) (Fin 3) ℝ), g.det = 1 → ∀ q ∈ K,
      ‖iteratedFDeriv ℝ N (fun x => (summandPoly n h g x i j).coeff m) q‖ ≤
        C / (Real.sqrt (planeAct g q 4)) ^ (n + 3) := by
  obtain ⟨C₁, hC₁⟩ := jet_bound_family uTau hV_uTau hK hKΩ N
  obtain ⟨C₂, hC₂⟩ := jet_bound_family (uTheta i j) (hV_uTheta i j) hK hKΩ N
  obtain ⟨C₃, hC₃⟩ := jet_bound_family (uPoly n m) (hV_uPoly n m) hK hKΩ N
  set D : ℝ := max 1 C₁ with hDdef
  set T : ℝ := max C₂ 0 with hTdef
  set Y : ℝ := max C₃ 0 with hYdef
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := by linarith
  have hT0 : 0 ≤ T := le_max_right _ _
  have hY0 : 0 ≤ Y := le_max_right _ _
  have hCh : 0 ≤ Ch := by
    have := hh Complex.I (by simp)
    rw [Complex.I_im, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨jetConst N D * ((N.factorial : ℝ) * 2 ^ N) * T * Y *
    (Ch * 2 ^ (((n : ℝ) + 3) / 2)), fun g hg q hq => ?_⟩
  have hqΩ := hKΩ hq
  have hq'' := planeAct_mem hg hqΩ
  set z : Par := (matToFun (kFactor g q), q) with hzdef
  have hz1 : z.1 ∈ SOrth := kFactor_mem_SOrth hg hqΩ
  have hz : GoodPar z := ⟨hz1.2, hqΩ⟩
  have hev : (fun x => (summandPoly n h g x i j).coeff m) =ᶠ[nhds q]
      (fun x => slashTwisted (n + 3) (planeA (planeAct g q)) h (uTau z x) * uTheta i j z x *
        uPoly n m z x) :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hqΩ) fun x hx =>
      coeff_frozen_eq n h hg hqΩ hx i j m
  rw [(hev.iteratedFDeriv ℝ N).eq_of_nhds,
    ← iteratedFDerivWithin_of_isOpen N isOpen_Omega hqΩ]
  have hbpos : 0 < (Real.sqrt (planeAct g q 4)) ^ (n + 3) :=
    pow_pos (Real.sqrt_pos.2 hq''.2) _
  set M : ℝ := Ch * 2 ^ (((n : ℝ) + 3) / 2) / (Real.sqrt (planeAct g q 4)) ^ (n + 3) with hM
  have hM0 : 0 ≤ M := by positivity
  have hI : uTau z q = Complex.I := by
    show seedTau (Psi z z.2) = _
    rw [Psi_basePt hz1 hqΩ]; simp [seedTau, basePt]
  have hmaps : Set.MapsTo (uTau z) Omega upperHalf := by
    intro x hx
    have := (Psi_mem hz1 hqΩ hx).1
    show 0 < (seedTau (Psi z x)).im
    simpa [seedTau] using this
  have key := triple_jet_bound (E := Fin 5 → ℝ) isOpen_Omega hqΩ isOpen_upperHalf
    (contDiffOn_of_family hV_uTau hz) hmaps (contDiffOn_hA n hd hq'')
    (contDiffOn_of_family (hV_uTheta i j) hz) (contDiffOn_of_family (hV_uPoly n m) hz) N
    (c := (N.factorial : ℝ) * 2 ^ N * M) (D := D) (T := T) (Y := Y) hD0 hT0
    (fun r hr => by
      rw [hI]
      refine (hA_iteratedFDeriv_bound n h Ch hh hd hq'' r).trans ?_
      have h1 : (r.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hr
      have h2 : (2 : ℝ) ^ r ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hr
      calc (r.factorial : ℝ) * M * 2 ^ r ≤ (N.factorial : ℝ) * M * 2 ^ N := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hM0) h2 (by positivity)
              (by positivity)
        _ = _ := by ring)
    (fun r hr1 hr2 => by
      rw [iteratedFDerivWithin_of_isOpen r isOpen_Omega hqΩ]
      calc ‖iteratedFDeriv ℝ r (uTau z) q‖ ≤ C₁ := hC₁ z hz1 hq r hr2
        _ ≤ D := le_max_right _ _
        _ ≤ D ^ r := le_self_pow₀ hD1 (by omega))
    (fun r hr => by
      rw [iteratedFDerivWithin_of_isOpen r isOpen_Omega hqΩ]
      exact (hC₂ z hz1 hq r hr).trans (le_max_left _ _))
    (fun r hr => by
      rw [iteratedFDerivWithin_of_isOpen r isOpen_Omega hqΩ]
      exact (hC₃ z hz1 hq r hr).trans (le_max_left _ _))
  refine key.trans ?_
  have hjc : 0 ≤ jetConst N D := jetConst_nonneg N hD0
  rw [hM]
  rw [le_div_iff₀ hbpos]
  have : jetConst N D * ((N.factorial : ℝ) * 2 ^ N * (Ch * 2 ^ (((n : ℝ) + 3) / 2) /
      (Real.sqrt (planeAct g q 4)) ^ (n + 3))) * T * Y *
      (Real.sqrt (planeAct g q 4)) ^ (n + 3) =
      jetConst N D * ((N.factorial : ℝ) * 2 ^ N) * T * Y * (Ch * 2 ^ (((n : ℝ) + 3) / 2)) := by
    field_simp
  linarith

end TernaryPeriodPolynomials.Argument.ConvergenceC4
