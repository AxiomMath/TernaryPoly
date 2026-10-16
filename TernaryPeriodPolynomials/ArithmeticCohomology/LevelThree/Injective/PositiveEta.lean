module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.LowerBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Cocycle

@[expose] public section


/-!
# Positivity of eta quotients on the imaginary axis

For `t > 0` the Dedekind eta function takes a positive real value at `i t`, hence so does every
eta quotient `phi n N = η(z)^(9N-3n) η(3z)^(9n-3N)` (`phi_pos`). The product construction
`exists_cusp_product` is upgraded to a statement about the function itself
(`exists_cusp_product_eq`), and the weight-`6` cusp form `η(z)^6 η(3z)^6` for `Γ₁(3)` gives a
nonzero level-three cusp form of weight `4 + 2` that is positive real on the imaginary axis
(`exists_positive_form_four`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane ModularForm Filter Topology
open scoped MatrixGroups ModularForm Manifold
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
open TernaryPeriodPolynomials.LevelThree.LevelThreeModularForms
open TernaryPeriodPolynomials.LevelThree.LevelThreeLowerBound

namespace TernaryPeriodPolynomials.LevelThreeInjective.PositiveEta

/-- The cusp form built by `exists_cusp_product`, with the equation of functions. -/
theorem exists_cusp_product_eq {w k : ℤ} {e : ℕ} {s : ℍ → ℂ} {Ls : ℂ} (hs : IsMF w s)
    (hlead : HasLead s e Ls) (a b : ℕ) (hk : w + 3 * ((a : ℤ) + b) = k) (hInf : 1 ≤ e + a)
    (h0 : IsZeroAtImInfty (s ∣[w] (ModularGroup.S : SL(2, ℤ))) ∨ 1 ≤ b) :
    ∃ C : CuspForm binaryRealGammaOneThree k,
      (C : ℍ → ℂ) = s * fun z : ℍ => phi a b (z : ℂ) := by
  subst hk
  obtain ⟨Fphi, hFphi⟩ := exists_form_phi a b
  have hmf : IsMF (w + 3 * ((a : ℤ) + b)) (s * fun z : ℍ => phi a b (z : ℂ)) :=
    hs.mul rfl ⟨Fphi, hFphi⟩
  have hl : HasLead (s * fun z : ℍ => phi a b (z : ℂ)) (e + a) (Ls * 1) :=
    hlead.mul (hasLead_phi a b)
  have hinf' : IsZeroAtImInfty (s * fun z : ℍ => phi a b (z : ℂ)) := hl.isZeroAtImInfty hInf
  have h0' : IsZeroAtImInfty ((s * fun z : ℍ => phi a b (z : ℂ)) ∣[w + 3 * ((a : ℤ) + b)]
      (ModularGroup.S : SL(2, ℤ))) := by
    rw [ModularForm.mul_slash_SL2]
    rcases h0 with h0 | hb
    · exact isZero_mul_isBounded h0 (phi_slash_bdd a b)
    · exact isBounded_mul_isZero (hs.bdd_slash _) (phi_slash_zero a b hb)
  obtain ⟨F, hF⟩ := hmf
  have hinf : IsZeroAtImInfty (F : ℍ → ℂ) := by rw [hF]; exact hinf'
  have h0F : IsZeroAtImInfty ((F : ℍ → ℂ) ∣[w + 3 * ((a : ℤ) + b)]
      (ModularGroup.S : SL(2, ℤ))) := by
    rw [hF]; exact h0'
  refine ⟨toCusp F hinf h0F, ?_⟩
  rw [coe_toCusp, hF]

/-! ### Eta on the imaginary axis -/

theorem qParam_one_I_mul (t : ℝ) :
    Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) =
      ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * t) * Complex.I_sq

theorem cexp_eta_I_mul (t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (Complex.I * (t : ℂ)) / 24) =
      ((Real.exp (-(2 * Real.pi * t / 24)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * t / 24) * Complex.I_sq

/-- The product part of `η` is a positive real number on the positive imaginary axis. -/
theorem etaProd_I_mul (t : ℝ) (ht : 0 < t) :
    0 < (etaProd (Complex.I * (t : ℂ))).re ∧ (etaProd (Complex.I * (t : ℂ))).im = 0 := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.exp (-(2 * Real.pi * t)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (by positivity)
  have hq : Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) = (r : ℂ) := by
    rw [hr]; exact qParam_one_I_mul t
  have hz : (Complex.I * (t : ℂ)) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    show 0 < (Complex.I * (t : ℂ)).im
    simpa using ht
  have hne : etaProd (Complex.I * (t : ℂ)) ≠ 0 := ModularForm.eta_tprod_ne_zero hz
  have hmul : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (Complex.I * (t : ℂ))) := by
    have h := ModularForm.multipliable_one_sub_pow (q := (r : ℂ))
      (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    simpa only [ModularForm.eta_q, hq] using h
  have hlim := hmul.hasProd.tendsto_prod_nat
  have hf : ∀ n : ℕ, 1 - ModularForm.eta_q n (Complex.I * (t : ℂ)) =
      ((1 - r ^ (n + 1) : ℝ) : ℂ) := by
    intro n
    simp only [ModularForm.eta_q, hq]
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  have hpart : ∀ n : ℕ,
      ∏ i ∈ Finset.range n, (1 - ModularForm.eta_q i (Complex.I * (t : ℂ))) =
        ((∏ i ∈ Finset.range n, (1 - r ^ (i + 1)) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl (fun i _ => hf i)
  have hpos : ∀ n : ℕ, 0 < ∏ i ∈ Finset.range n, (1 - r ^ (i + 1)) := fun n =>
    Finset.prod_pos (fun i _ => sub_pos.mpr (pow_lt_one₀ hr0.le hr1 (Nat.succ_ne_zero i)))
  have hre : Tendsto (fun n : ℕ =>
      (∏ i ∈ Finset.range n, (1 - ModularForm.eta_q i (Complex.I * (t : ℂ)))).re) atTop
      (𝓝 (etaProd (Complex.I * (t : ℂ))).re) :=
    (Complex.continuous_re.tendsto _).comp hlim
  have him : Tendsto (fun n : ℕ =>
      (∏ i ∈ Finset.range n, (1 - ModularForm.eta_q i (Complex.I * (t : ℂ)))).im) atTop
      (𝓝 (etaProd (Complex.I * (t : ℂ))).im) :=
    (Complex.continuous_im.tendsto _).comp hlim
  have h0 : Tendsto (fun n : ℕ =>
      (∏ i ∈ Finset.range n, (1 - ModularForm.eta_q i (Complex.I * (t : ℂ)))).im) atTop
      (𝓝 0) := by
    have : (fun n : ℕ =>
        (∏ i ∈ Finset.range n, (1 - ModularForm.eta_q i (Complex.I * (t : ℂ)))).im) =
          fun _ => 0 := by
      funext n
      rw [hpart n, Complex.ofReal_im]
    rw [this]
    exact tendsto_const_nhds
  have him0 : (etaProd (Complex.I * (t : ℂ))).im = 0 := tendsto_nhds_unique him h0
  have hge : 0 ≤ (etaProd (Complex.I * (t : ℂ))).re :=
    ge_of_tendsto' hre (fun n => by
      simp only [hpart n, Complex.ofReal_re]
      exact (hpos n).le)
  refine ⟨lt_of_le_of_ne hge (fun h => hne ?_), him0⟩
  exact Complex.ext (by rw [Complex.zero_re]; exact h.symm)
    (by rw [Complex.zero_im]; exact him0)

/-- `η` takes a positive real value on the positive imaginary axis. -/
theorem eta_I_mul (t : ℝ) (ht : 0 < t) :
    ∃ x : ℝ, 0 < x ∧ ModularForm.eta (Complex.I * (t : ℂ)) = (x : ℂ) := by
  obtain ⟨hre, him⟩ := etaProd_I_mul t ht
  have hP : (((etaProd (Complex.I * (t : ℂ))).re : ℝ) : ℂ) = etaProd (Complex.I * (t : ℂ)) :=
    Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, him])
  refine ⟨Real.exp (-(2 * Real.pi * t / 24)) * (etaProd (Complex.I * (t : ℂ))).re,
    mul_pos (Real.exp_pos _) hre, ?_⟩
  rw [eta_eq_exp, cexp_eta_I_mul, Complex.ofReal_mul, hP]

/-- Every eta quotient `phi n N` is a positive real number on the positive imaginary axis. -/
theorem phi_pos (n N : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < (phi n N (Complex.I * (t : ℂ))).re ∧ (phi n N (Complex.I * (t : ℂ))).im = 0 := by
  obtain ⟨x, hx, hxe⟩ := eta_I_mul t ht
  obtain ⟨y, hy, hye⟩ := eta_I_mul (3 * t) (by positivity)
  have h3 : (3 : ℂ) * (Complex.I * (t : ℂ)) = Complex.I * ((3 * t : ℝ) : ℂ) := by
    push_cast
    ring
  have hphi : phi n N (Complex.I * (t : ℂ)) =
      ((x ^ (9 * (N : ℤ) - 3 * n) * y ^ (9 * (n : ℤ) - 3 * N) : ℝ) : ℂ) := by
    unfold phi
    rw [h3, hxe, hye]
    push_cast
    rfl
  rw [hphi, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨mul_pos (zpow_pos hx _) (zpow_pos hy _), rfl⟩

theorem coe_ofComplex_I_mul (t : ℝ) (ht : 0 < t) :
    ((UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) : ℍ) : ℂ) = Complex.I * (t : ℂ) := by
  have hz : 0 < (Complex.I * (t : ℂ)).im := by simpa using ht
  exact congrArg (fun w : ℍ => (w : ℂ)) (UpperHalfPlane.ofComplex_apply_of_im_pos hz)

/-- `phi_pos` at the point of `ℍ` given by `ofComplex (I t)`. -/
theorem phi_ofComplex_pos (n N : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < (phi n N ((UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) : ℍ) : ℂ)).re ∧
      (phi n N ((UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) : ℍ) : ℂ)).im = 0 := by
  rw [coe_ofComplex_I_mul t ht]
  exact phi_pos n N t ht

/-- A nonzero level-three cusp form of weight `4 + 2` taking positive real values on the positive
imaginary axis (namely `η(z)^6 η(3z)^6`). -/
theorem exists_positive_form_four :
    ∃ f₀ : TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle.S 4,
      f₀ ≠ 0 ∧ ∀ t : ℝ, 0 < t →
        0 < (f₀ (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).re ∧
          (f₀ (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).im = 0 := by
  have hk : (0 : ℤ) + 3 * (((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ)) =
      TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle.weight 4 := by
    show (0 : ℤ) + 3 * (((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ)) = ((4 : ℕ) : ℤ) + 2
    norm_num
  obtain ⟨C, hC⟩ := exists_cusp_product_eq isMF_one hasLead_one 1 1 hk (by norm_num)
    (Or.inr le_rfl)
  have hval : ∀ t : ℝ, 0 < t → C (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))) =
      phi 1 1 ((UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) : ℍ) : ℂ) := by
    intro t _
    exact (congrFun hC _).trans (by simp only [Pi.mul_apply, Pi.one_apply, one_mul])
  have hpos : ∀ t : ℝ, 0 < t →
      0 < (C (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).re ∧
        (C (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))).im = 0 := by
    intro t ht
    rw [hval t ht]
    exact phi_ofComplex_pos 1 1 t ht
  refine ⟨C, fun hC0 => ?_, hpos⟩
  have h1 := (hpos 1 one_pos).1
  rw [hC0] at h1
  simp at h1

end TernaryPeriodPolynomials.LevelThreeInjective.PositiveEta
