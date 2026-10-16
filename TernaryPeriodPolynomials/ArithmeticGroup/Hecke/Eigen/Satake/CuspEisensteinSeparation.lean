module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.LineEigen
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.SingleCharacter

@[expose] public section


/-!
# The cuspidal `T_p` eigenvalue is small

At the cohomological point the plane `T_p` eigenvalue of an inducing datum is
`χ(sAd p) + (p² + p) p^{-(n+3)/2} ω(diag(p,1))`, with `|χ| = 1` and `|ω| ≤ 1`. For `n ≥ 1` its
modulus is therefore at most `1 + (p² + p)/p² ≤ 5/2`. In particular it is never the degree
`p² + p + 1` of `T_p`, which is the eigenvalue on constant (trivial-constituent) functions.
This is the elementary cusp/trivial separation step of constituent separation.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.RepresentationTheory

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

/-- The cohomological plane `T_p` eigenvalue of `D`. -/
def cuspPlaneEigenvalue {n p : ℕ} (D : InducingData n) (hp : p.Prime) : ℂ :=
  D.chi.toMonoidHom (sAd (pUnit hp)) +
    ((p : ℂ) ^ 2 + p) * (Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ))) *
      omega D.cusp (Bo (dP hp)))

theorem cuspPlaneEigenvalue_norm_le {n p : ℕ} (D : InducingData n) (hp : p.Prime) :
    ‖cuspPlaneEigenvalue D hp‖ ≤
      1 + ((p : ℝ) ^ 2 + p) * Real.exp (-(((n : ℝ) + 3) / 2 * Real.log p)) := by
  unfold cuspPlaneEigenvalue
  refine (norm_add_le _ _).trans (add_le_add (le_of_eq (D.chi.unitary _)) ?_)
  exact prime_plane_cusp_part_bound_real D hp

/-- For `n ≥ 1` the weight factor is at most `p⁻²`. -/
theorem weight_factor_le {n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    Real.exp (-(((n : ℝ) + 3) / 2 * Real.log p)) ≤ ((p : ℝ) ^ 2)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hpos : (0 : ℝ) < p := by linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [show ((p : ℝ) ^ 2)⁻¹ = Real.exp (-(2 * Real.log p)) by
    rw [Real.exp_neg, ← Real.log_rpow hpos, Real.exp_log (by positivity)]
    norm_num]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem cuspPlaneEigenvalue_norm_le_five_halves {n p : ℕ} (D : InducingData n) (hp : p.Prime)
    (hn : 1 ≤ n) : ‖cuspPlaneEigenvalue D hp‖ ≤ 5 / 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < p := by linarith
  have hw := weight_factor_le hp hn
  have hpp : (0 : ℝ) ≤ (p : ℝ) ^ 2 + p := by positivity
  have h1 : ((p : ℝ) ^ 2 + p) * Real.exp (-(((n : ℝ) + 3) / 2 * Real.log p)) ≤
      ((p : ℝ) ^ 2 + p) * ((p : ℝ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hw hpp
  have h2 : ((p : ℝ) ^ 2 + p) * ((p : ℝ) ^ 2)⁻¹ ≤ 3 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  linarith [cuspPlaneEigenvalue_norm_le D hp]

/-- **Cusp/trivial separation.** For `n ≥ 1` the cohomological plane `T_p` eigenvalue of an
inducing datum is never the degree `p² + p + 1` of `T_p`. -/
theorem cuspPlaneEigenvalue_ne_degree {n p : ℕ} (D : InducingData n) (hp : p.Prime)
    (hn : 1 ≤ n) : cuspPlaneEigenvalue D hp ≠ (p : ℂ) ^ 2 + p + 1 := by
  intro h
  have hb := cuspPlaneEigenvalue_norm_le_five_halves D hp hn
  rw [h] at hb
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : ‖(p : ℂ) ^ 2 + p + 1‖ = (p : ℝ) ^ 2 + p + 1 := by
    have e : ((p : ℂ) ^ 2 + p + 1) = (((p : ℝ) ^ 2 + p + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [this] at hb
  nlinarith

/-- The plane `T_p` eigenvalue on induced sections is `cuspPlaneEigenvalue`. -/
theorem plane_Tp_eq_cusp {n p : ℕ} (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors D.cusp K3)] (f : AdelicGL → ℂ)
    (hf : IsInduced D .plane cohomologicalPoint f) (g : AdelicGL) :
    ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
      cuspPlaneEigenvalue D hp * f g :=
  prime_plane_eigenvalue_cohomological D hp h3 t ht hg f hf g

/-- The line `T_p` eigenvalue on induced sections is the same `cuspPlaneEigenvalue`. -/
theorem line_Tp_eq_cusp {n p : ℕ} (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors D.cusp K3)] (f : AdelicGL → ℂ)
    (hf : IsInduced D .line cohomologicalPoint f) (g : AdelicGL) :
    ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
      cuspPlaneEigenvalue D hp * f g :=
  prime_line_eigenvalue_cohomological D hp h3 t ht hg f hf g

/-- **`T_p` minus its degree does not kill a nonzero value of an induced section.** -/
theorem plane_Tp_ne_degree {n p : ℕ} (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (hn : 1 ≤ n) (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors D.cusp K3)] (f : AdelicGL → ℂ)
    (hf : IsInduced D .plane cohomologicalPoint f) (g : AdelicGL) (hfg : f g ≠ 0) :
    ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) ≠
      ((p : ℂ) ^ 2 + p + 1) * f g := by
  rw [plane_Tp_eq_cusp D hp h3 t ht hg f hf g]
  intro h
  exact cuspPlaneEigenvalue_ne_degree D hp hn (mul_right_cancel₀ hfg h)

/-- The central eigenvalue `χ(sAd p) p^{-(n+3)} ω_σ(sAd p)` has modulus `p^{-(n+3)} < 1`. -/
theorem central_eigenvalue_norm {n p : ℕ} (D : InducingData n) (hp : p.Prime) :
    ‖D.chi.toMonoidHom (sAd (pUnit hp)) *
        (Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ))) *
          D.cusp.centralCharacter (sAd (pUnit hp)))‖ =
      Real.exp (-(((n : ℝ) + 3) * Real.log p)) := by
  rw [norm_mul, norm_mul, D.chi.unitary, D.cusp.centralUnitary, one_mul, mul_one,
    Complex.norm_exp]
  congr 1
  have : -(((n : ℂ) + 3) * (Real.log p : ℂ)) = ((-(((n : ℝ) + 3) * Real.log p) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.ofReal_re]

/-- **Central separation.** The central eigenvalue is never `1`, its value on constants. -/
theorem central_eigenvalue_ne_one {n p : ℕ} (D : InducingData n) (hp : p.Prime) :
    D.chi.toMonoidHom (sAd (pUnit hp)) *
        (Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ))) *
          D.cusp.centralCharacter (sAd (pUnit hp))) ≠ 1 := by
  intro h
  have hn := central_eigenvalue_norm D hp
  rw [h, norm_one] at hn
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hneg : -(((n : ℝ) + 3) * Real.log p) < 0 := by
    have : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    nlinarith
  have := Real.exp_lt_exp.mpr hneg
  rw [Real.exp_zero] at this
  linarith

/-- The cohomological `diag(p,p,1)` plane eigenvalue of `D`. -/
def cuspPlaneEigenvalue2 {n p : ℕ} (D : InducingData n) (hp : p.Prime) : ℂ :=
  (p : ℂ) ^ 2 * (Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ))) *
      D.cusp.centralCharacter (sAd (pUnit hp))) +
    ((p : ℂ) + 1) * (D.chi.toMonoidHom (sAd (pUnit hp)) *
      (Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ))) * omega D.cusp (Bo (dP hp))))

theorem norm_exp_real_mul_log (c : ℝ) (p : ℕ) :
    ‖Complex.exp (-((c : ℂ) * (Real.log p : ℂ)))‖ = Real.exp (-(c * Real.log p)) := by
  rw [Complex.norm_exp]
  congr 1
  have : -((c : ℂ) * (Real.log p : ℂ)) = ((-(c * Real.log p) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

/-- **Bound for the `diag(p,p,1)` eigenvalue.** For `n ≥ 1` its modulus is at most `p + 2`,
so it is never the degree `p² + p + 1`. -/
theorem cuspPlaneEigenvalue2_norm_le {n p : ℕ} (D : InducingData n) (hp : p.Prime)
    (hn : 1 ≤ n) : ‖cuspPlaneEigenvalue2 D hp‖ ≤ (p : ℝ) + 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℝ) < p := by linarith
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e1 : ‖Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ)))‖ ≤ ((p : ℝ) ^ 2)⁻¹ := by
    have := norm_exp_real_mul_log ((n : ℝ) + 3) p
    rw [show ((((n : ℝ) + 3 : ℝ)) : ℂ) = (n : ℂ) + 3 by push_cast; ring] at this
    rw [this]
    refine le_trans (Real.exp_le_exp.mpr (by nlinarith : -(((n : ℝ) + 3) * Real.log p) ≤
      -(2 * Real.log p))) (le_of_eq ?_)
    rw [Real.exp_neg, ← Real.log_rpow hpos, Real.exp_log (by positivity)]
    norm_num
  have e2 : ‖Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ)))‖ ≤ 1 := by
    have := norm_exp_real_mul_log (((n : ℝ) + 3) / 2) p
    rw [show (((((n : ℝ) + 3) / 2 : ℝ)) : ℂ) = ((n : ℂ) + 3) / 2 by push_cast; ring] at this
    rw [this, Real.exp_le_one_iff]
    have : (0 : ℝ) < ((n : ℝ) + 3) / 2 := by positivity
    nlinarith
  have hω := omega_norm_le D.cusp (glAway2_mem (glF (dP hp)))
  unfold cuspPlaneEigenvalue2
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, D.cusp.centralUnitary, mul_one, norm_mul, norm_mul, D.chi.unitary,
    one_mul, norm_mul]
  have hp2 : ‖(p : ℂ) ^ 2‖ = (p : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_natCast]
  have hp1' : ‖(p : ℂ) + 1‖ = (p : ℝ) + 1 := by
    have e : ((p : ℂ) + 1) = (((p : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hp2, hp1']
  have a1 : (p : ℝ) ^ 2 * ‖Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ)))‖ ≤ 1 := by
    calc (p : ℝ) ^ 2 * ‖Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ)))‖
        ≤ (p : ℝ) ^ 2 * ((p : ℝ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have a2 : ‖Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ)))‖ *
      ‖omega D.cusp (Bo (dP hp))‖ ≤ 1 :=
    (mul_le_mul e2 hω (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul 1))
  have a3 : ((p : ℝ) + 1) * (‖Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ)))‖ *
      ‖omega D.cusp (Bo (dP hp))‖) ≤ (p : ℝ) + 1 :=
    (mul_le_mul_of_nonneg_left a2 (by positivity)).trans (le_of_eq (mul_one _))
  linarith

theorem cuspPlaneEigenvalue2_ne_degree {n p : ℕ} (D : InducingData n) (hp : p.Prime)
    (hn : 1 ≤ n) : cuspPlaneEigenvalue2 D hp ≠ (p : ℂ) ^ 2 + p + 1 := by
  intro h
  have hb := cuspPlaneEigenvalue2_norm_le D hp hn
  rw [h] at hb
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : ‖(p : ℂ) ^ 2 + p + 1‖ = (p : ℝ) ^ 2 + p + 1 := by
    have e : ((p : ℂ) ^ 2 + p + 1) = (((p : ℝ) ^ 2 + p + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [this] at hb
  nlinarith

/-- **The `T_p` eigenvalue determines `ω(diag(p,1))`** among inducing data with the same
character value at `sAd p`. -/
theorem omega_eq_of_cuspPlaneEigenvalue_eq {n n' p : ℕ} (D : InducingData n)
    (D' : InducingData n') (hn : n = n') (hp : p.Prime)
    (hχ : D.chi.toMonoidHom (sAd (pUnit hp)) = D'.chi.toMonoidHom (sAd (pUnit hp)))
    (h : cuspPlaneEigenvalue D hp = cuspPlaneEigenvalue D' hp) :
    omega D.cusp (Bo (dP hp)) = omega D'.cusp (Bo (dP hp)) := by
  subst hn
  unfold cuspPlaneEigenvalue at h
  rw [hχ, add_right_inj, ← mul_assoc, ← mul_assoc] at h
  have hpp : ((p : ℂ) ^ 2 + p) * Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log p : ℂ))) ≠ 0 := by
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    have hpos : (0 : ℝ) < (p : ℝ) ^ 2 + p := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    exact_mod_cast hpos.ne'
  exact mul_left_cancel₀ hpp h

/-- **The central eigenvalue determines the central character at `sAd p`** among inducing data
with the same character value at `sAd p`. -/
theorem centralCharacter_eq_of_central_eq {n p : ℕ} (D D' : InducingData n) (hp : p.Prime)
    (hχ : D.chi.toMonoidHom (sAd (pUnit hp)) = D'.chi.toMonoidHom (sAd (pUnit hp)))
    (h : D.chi.toMonoidHom (sAd (pUnit hp)) *
        (Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ))) *
          D.cusp.centralCharacter (sAd (pUnit hp))) =
      D'.chi.toMonoidHom (sAd (pUnit hp)) *
        (Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ))) *
          D'.cusp.centralCharacter (sAd (pUnit hp)))) :
    D.cusp.centralCharacter (sAd (pUnit hp)) = D'.cusp.centralCharacter (sAd (pUnit hp)) := by
  rw [hχ, ← mul_assoc, ← mul_assoc] at h
  have hχ0 : D'.chi.toMonoidHom (sAd (pUnit hp)) ≠ 0 := by
    intro h0
    have := D'.chi.unitary (sAd (pUnit hp))
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ (mul_ne_zero hχ0 (Complex.exp_ne_zero _)) h

/-- **Line `diag(p,p,1)` eigenvalue.** Whenever some plane induced section has a nonzero value,
the `diag(p,p,1)` operator acts on line induced sections by `cuspPlaneEigenvalue2`. This follows
from the plane formula and the plane/line comparison `plane_line_scalar`. -/
theorem line_Tp2_eq_cusp {n p : ℕ} (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP2 hp)
    (hsm : ∃ v ∈ D.cusp.smooth, v ≠ 0) [Nontrivial (fixedVectors D.cusp K3)]
    (hex : ∃ (f₀ : AdelicGL → ℂ) (g₀ : AdelicGL),
      IsInduced D .plane cohomologicalPoint f₀ ∧ f₀ g₀ ≠ 0)
    (f : AdelicGL → ℂ) (hf : IsInduced D .line cohomologicalPoint f) (g : AdelicGL) :
    ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
      cuspPlaneEigenvalue2 D hp * f g := by
  obtain ⟨μ, hP, hL⟩ := plane_line_scalar D t ht
  obtain ⟨f₀, g₀, hf₀, hne⟩ := hex
  have h1 := hP f₀ hf₀ g₀
  rw [prime2_plane_eigenvalue_cohomological D hp h3 t ht hg hsm f₀ hf₀ g₀] at h1
  have hμ : μ = cuspPlaneEigenvalue2 D hp := (mul_right_cancel₀ hne h1).symm
  rw [hL f hf g, hμ]

/-- **Line central eigenvalue**, under the same nonvanishing hypothesis. -/
theorem line_central_eq_cusp {n p : ℕ} (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = pScalar hp)
    (hsm : ∃ v ∈ D.cusp.smooth, v ≠ 0) [Nontrivial (fixedVectors D.cusp K3)]
    (hex : ∃ (f₀ : AdelicGL → ℂ) (g₀ : AdelicGL),
      IsInduced D .plane cohomologicalPoint f₀ ∧ f₀ g₀ ≠ 0)
    (f : AdelicGL → ℂ) (hf : IsInduced D .line cohomologicalPoint f) (g : AdelicGL) :
    ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
      (D.chi.toMonoidHom (sAd (pUnit hp)) *
        (Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ))) *
          D.cusp.centralCharacter (sAd (pUnit hp)))) * f g := by
  obtain ⟨μ, hP, hL⟩ := plane_line_scalar D t ht
  obtain ⟨f₀, g₀, hf₀, hne⟩ := hex
  have h1 := hP f₀ hf₀ g₀
  rw [central_plane_eigenvalue_cohomological D hp h3 t ht hg hsm f₀ hf₀ g₀] at h1
  rw [hL f hf g, (mul_right_cancel₀ hne h1).symm]

/-- **Line separation.** `T_p` minus its degree does not kill a nonzero value of a line induced
section. -/
theorem line_Tp_ne_degree {n p : ℕ} (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (hn : 1 ≤ n) (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors D.cusp K3)] (f : AdelicGL → ℂ)
    (hf : IsInduced D .line cohomologicalPoint f) (g : AdelicGL) (hfg : f g ≠ 0) :
    ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) ≠
      ((p : ℂ) ^ 2 + p + 1) * f g := by
  rw [line_Tp_eq_cusp D hp h3 t ht hg f hf g]
  intro h
  exact cuspPlaneEigenvalue_ne_degree D hp hn (mul_right_cancel₀ hfg h)

end TernaryPeriodPolynomials.HeckeEigen.Satake
