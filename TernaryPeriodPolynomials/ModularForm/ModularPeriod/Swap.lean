module

public import TernaryPeriodPolynomials.ModularForm.ModularPeriod.Linear

@[expose] public section


noncomputable section
open Complex MatrixGroups
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspPeriod

/-- Full level makes the S-translated function in Mathlib's FE pair equal to the original cusp form. -/
theorem weakFEPair_g_eq {d : ℕ} (f : Forms d) :
    (ModularForm.weakFEPair (weight_pos d) f).g =
      (fun t : ℝ => f (ofComplex (I*t))) := by
  have hs : (ModularGroup.S : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨ModularGroup.S, rfl⟩
  have ht : (ModularForm.translate f (ModularGroup.S : GL (Fin 2) ℝ) : ℍ → ℂ) = f := by
    rw [ModularForm.coe_translate, SlashInvariantFormClass.slash_action_eq f _ hs]
  funext t
  exact congrFun ht (ofComplex (I*t))

/-- The exact full-level cusp Mellin functional equation, with its i^(d+2) factor. -/
theorem moment_functional_equation {d : ℕ} (f : Forms d) (s : ℂ) :
    moment f ((d : ℂ)+2-s) = I ^ (d+2) * moment f s := by
  have he := (ModularForm.weakFEPair (weight_pos d) f).functional_equation s
  rw [(CuspForm.isStrongFEPair (weight_pos d) f).Λ_eq,
    (CuspForm.isStrongFEPair (weight_pos d) f).symm_Λ_eq, weakFEPair_g_eq] at he
  have hfun : (ModularForm.weakFEPair (weight_pos d) f).f =
      (fun t : ℝ => f (ofComplex (I*t))) := rfl
  rw [hfun] at he
  have hi : I ^ ((d : ℤ)+2) = I ^ (d+2) := by
    rw [show (d : ℤ)+2 = ((d+2 : ℕ) : ℤ) by omega, zpow_natCast]
  simpa only [moment, ModularForm.weakFEPair_k, ModularForm.weakFEPair_ε,
    Int.cast_add, Int.cast_natCast, Int.cast_ofNat, ofReal_add, ofReal_natCast,
    ofReal_ofNat, hi, smul_eq_mul] using he

/-- The functional equation reflected about the middle critical index. -/
theorem moment_reflection {d j : ℕ} (f : Forms d) (hj : j ≤ d) :
    moment f (j+1 : ℕ) = I ^ (d+2) * moment f (d-j+1 : ℕ) := by
  have he := moment_functional_equation f (d-j+1 : ℕ)
  have hc : (d : ℂ)+2-((d-j+1 : ℕ) : ℂ) = ((j+1 : ℕ) : ℂ) := by
    rw [Nat.cast_add, Nat.cast_sub hj]
    push_cast
    ring
  rwa [hc] at he

/-- The critical i-powers agree when the X exponent is odd. -/
theorem odd_phase_reflection {d j : ℕ} (hj : j ≤ d) (ho : Odd j) :
    I ^ (j+1) * I ^ (d+2) = I ^ (d-j+1) := by
  rw [← pow_add, I_pow_eq_pow_mod, I_pow_eq_pow_mod (d-j+1)]
  congr 1
  obtain ⟨r, hr⟩ := ho
  omega

/-- Reflection preserves each odd coefficient of the actual even-degree period polynomial. -/
theorem periodCoefficient_reflection {d j : ℕ} (hd : Even d) (f : Forms d)
    (hj : j ≤ d) (ho : Odd j) :
    periodCoefficient f (d-j) = periodCoefficient f j := by
  have ho' := Nat.Even.sub_odd hj hd ho
  simp only [periodCoefficient, Nat.choose_symm hj, Nat.sub_sub_self hj,
    ho.neg_one_pow, ho'.neg_one_pow]
  rw [moment_reflection f hj]
  linear_combination (-(d.choose j : ℂ) * moment f (d-j+1 : ℕ)) *
    odd_phase_reflection hj ho

end TernaryPoly.BinaryCuspPeriod
