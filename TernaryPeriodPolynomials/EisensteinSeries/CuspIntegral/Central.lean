module

public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Lift
public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.CentralIdele

@[expose] public section


/-!
# The central character of the adelic lift

`φ_f (z · g) = sign(z)^k φ_f (g)` where `sign : 𝔸ˣ →* ℤˣ` is the sign homomorphism of
`CentralIdele.lean`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.CuspIntegral

theorem scalar_mul_comm {R : Type*} [CommRing R] (z : Rˣ) (y : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.scalar (Fin 2) z * y = y * GeneralLinearGroup.scalar (Fin 2) z := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [scalar_val_apply, mul_comm]

/-- `ε ↦ ε^k` from `{±1}` to `ℂˣ`-valued scalars. -/
def signPow (k : ℤ) : ℤˣ →* ℂ where
  toFun e := ((e : ℤ) : ℂ) ^ k
  map_one' := by simp
  map_mul' a b := by simp [mul_zpow]

/-- The central character of the lift of a weight-`k` form. -/
def centralChar (k : ℤ) : Adelesˣ →* ℂ := (signPow k).comp ideleSign

theorem norm_centralChar (k : ℤ) (z : Adelesˣ) : ‖centralChar k z‖ = 1 := by
  change ‖(((ideleSign z : ℤˣ) : ℤ) : ℂ) ^ k‖ = 1
  rcases Int.units_eq_one_or (ideleSign z) with h | h <;> simp [h]

theorem ideleSign_eq_of_decomp {z : Adelesˣ} {q : ℚˣ} {t : ℝˣ} {w : IntegralAdelesˣ}
    (hw : integralReduction w.val = 1)
    (h : GeneralLinearGroup.scalar (Fin 2) z =
      ratGL (GeneralLinearGroup.scalar (Fin 2) q) *
        (infGL (GeneralLinearGroup.scalar (Fin 2) t) *
          finGL (intGL (GeneralLinearGroup.scalar (Fin 2) w)))) :
    ideleSign z = if t.val < 0 then -1 else 1 := by
  rw [scalar_ideleOf] at h
  exact congrArg signUnit (ideleReal_eq ⟨hw, scalar_injective h⟩)

theorem centralChar_eq_of_decomp {k : ℤ} {z : Adelesˣ} {q : ℚˣ} {t : ℝˣ}
    {w : IntegralAdelesˣ} (hw : integralReduction w.val = 1)
    (h : GeneralLinearGroup.scalar (Fin 2) z =
      ratGL (GeneralLinearGroup.scalar (Fin 2) q) *
        (infGL (GeneralLinearGroup.scalar (Fin 2) t) *
          finGL (intGL (GeneralLinearGroup.scalar (Fin 2) w)))) :
    centralChar k z = if t.val < 0 then (-1 : ℂ) ^ k else 1 := by
  change (((ideleSign z : ℤˣ) : ℤ) : ℂ) ^ k = _
  rw [ideleSign_eq_of_decomp hw h]
  split_ifs <;> simp

theorem det_scalar_mul_pos (t : ℝˣ) (r : BinaryRealGL)
    (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) :
    0 < (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) t * r) : ℝˣ).val := by
  rw [map_mul, Units.val_mul, det_scalar_real]
  exact mul_pos (by have := t.ne_zero; positivity) hr

/-- The central character of the adelic lift. -/
theorem adelicLift_central {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (z : Adelesˣ)
    (x : BinaryAdelicGL) :
    adelicLift f (GeneralLinearGroup.scalar (Fin 2) z * x) = centralChar k z * adelicLift f x := by
  obtain ⟨q, t, w, hw, hz⟩ := exists_idele_decomp z
  have hK : intGL (GeneralLinearGroup.scalar (Fin 2) w) ∈ levelGroup :=
    scalar_intGL_mem_levelGroup w hw
  obtain ⟨γ, r, κ, hx⟩ := exists_isDecomp x
  have hc3 : finGL (intGL (GeneralLinearGroup.scalar (Fin 2) w)) * x =
      x * finGL (intGL (GeneralLinearGroup.scalar (Fin 2) w)) := by
    rw [intGL_scalar, finGL_scalar]
    exact scalar_mul_comm _ _
  have step1 : GeneralLinearGroup.scalar (Fin 2) z * x =
      ratGL (GeneralLinearGroup.scalar (Fin 2) q) *
        (infGL (GeneralLinearGroup.scalar (Fin 2) t) *
          (x * finGL (intGL (GeneralLinearGroup.scalar (Fin 2) w)))) := by
    rw [hz, mul_assoc, mul_assoc, hc3]
  have hx' := isDecomp_mul_levelGroup hx hK
  have hcomm : infGL (GeneralLinearGroup.scalar (Fin 2) t) * ratGL γ =
      ratGL γ * infGL (GeneralLinearGroup.scalar (Fin 2) t) := by
    rw [infGL_scalar]
    exact scalar_mul_comm _ _
  have hdec : IsDecomp (infGL (GeneralLinearGroup.scalar (Fin 2) t) *
      (x * finGL (intGL (GeneralLinearGroup.scalar (Fin 2) w))))
      γ (GeneralLinearGroup.scalar (Fin 2) t * r)
      (κ * intGL (GeneralLinearGroup.scalar (Fin 2) w)) := by
    refine ⟨det_scalar_mul_pos t r hx.1, hx'.2.1, ?_⟩
    rw [hx'.2.2]
    calc infGL (GeneralLinearGroup.scalar (Fin 2) t) * (ratGL γ * (infGL r *
          finGL (κ * intGL (GeneralLinearGroup.scalar (Fin 2) w))))
        = (infGL (GeneralLinearGroup.scalar (Fin 2) t) * ratGL γ) * (infGL r *
          finGL (κ * intGL (GeneralLinearGroup.scalar (Fin 2) w))) := (mul_assoc _ _ _).symm
      _ = ratGL γ * (infGL (GeneralLinearGroup.scalar (Fin 2) t) * (infGL r *
          finGL (κ * intGL (GeneralLinearGroup.scalar (Fin 2) w)))) := by
        rw [hcomm, mul_assoc]
      _ = ratGL γ * (infGL (GeneralLinearGroup.scalar (Fin 2) t * r) *
          finGL (κ * intGL (GeneralLinearGroup.scalar (Fin 2) w))) := by
        rw [map_mul infGL, mul_assoc]
  rw [step1, adelicLift_ratGL_mul f (GeneralLinearGroup.scalar (Fin 2) q),
    adelicLift_eq_of_isDecomp f hdec, adelicLift_eq_of_isDecomp f hx,
    liftReal_scalar f t r hx.1, centralChar_eq_of_decomp hw hz]

end TernaryPeriodPolynomials.CuspIntegral
