module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors

noncomputable def planeCuspVector {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f) (g : AdelicGL) :
    D.cusp.smooth :=
  Classical.choose (hf.2.2.2.2.2 g)

theorem realize_planeCuspVector {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f) (g : AdelicGL)
    (A : BinaryAdelicGL) :
    D.cusp.realize (planeCuspVector hf g) A =
      normPower (Matrix.GeneralLinearGroup.det A)
        (-binaryInductionExponent n .plane s) * f (planeLevi A 1 * g) :=
  congrFun (Classical.choose_spec (hf.2.2.2.2.2 g)) A

theorem planeCuspVector_unique {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f) (g : AdelicGL)
    (v : D.cusp.smooth)
    (hv : ∀ A, D.cusp.realize v A =
      normPower (Matrix.GeneralLinearGroup.det A)
        (-binaryInductionExponent n .plane s) * f (planeLevi A 1 * g)) :
    planeCuspVector hf g = v := by
  apply D.cusp.injective
  funext A
  rw [realize_planeCuspVector, hv]

theorem induced_eq_planeCuspVector {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f) (g : AdelicGL)
    (A : BinaryAdelicGL) :
    f (planeLevi A 1 * g) =
      normPower (Matrix.GeneralLinearGroup.det A)
        (binaryInductionExponent n .plane s) * D.cusp.realize (planeCuspVector hf g) A := by
  rw [realize_planeCuspVector, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_neg,
    mul_inv_cancel_left₀ (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_ne_zero _ _)]

theorem induced_eq_planeCuspVector_one {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f) (g : AdelicGL) :
    f g = D.cusp.realize (planeCuspVector hf g) 1 := by
  have h := induced_eq_planeCuspVector hf g 1
  have hone : planeLevi (1 : BinaryAdelicGL) 1 = 1 :=
    (planeLeviHom Adeles).map_one
  simpa only [hone, one_mul, map_one, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_one] using h

theorem flatSection_planeCuspVector_eq {n : ℕ} {D : InducingData n}
    {F : ℂ → AdelicGL → ℂ} (hF : IsFlatSection D F)
    (s : ℂ) (k : AdelicGL) (hk : inMaximalCompact k) :
    planeCuspVector (hF.1 s) k = planeCuspVector (hF.1 cohomologicalPoint) k := by
  apply planeCuspVector_unique
  intro A
  rw [realize_planeCuspVector]
  exact (hF.2.2 s A k hk).symm

theorem planeCuspVector_finiteLevel {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f)
    (g : AdelicGL) (k : finiteLevel) :
    planeCuspVector hf (g * atFinite k.val) = planeCuspVector hf g := by
  apply planeCuspVector_unique
  intro A
  rw [realize_planeCuspVector, ← mul_assoc, hf.2.1 k]

theorem planeCuspVector_unipotent {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f)
    (a b : Adeles) (g : AdelicGL) :
    planeCuspVector hf (planeUnipotent a b * g) = planeCuspVector hf g := by
  apply D.cusp.injective
  funext A
  rw [realize_planeCuspVector, realize_planeCuspVector]
  congr 1
  have hconj : planeLevi A 1 * planeUnipotent a b =
      planeUnipotent (A.val 0 0 * a + A.val 0 1 * b)
        (A.val 1 0 * a + A.val 1 1 * b) * planeLevi A 1 := by
    apply Units.ext
    apply Matrix.ext
    intro row column
    fin_cases row <;> fin_cases column <;>
      simp [planeLevi, planeBlock, planeUnipotent, Matrix.mul_apply,
        Fin.sum_univ_three]
  rw [← mul_assoc, hconj, mul_assoc, hf.2.2.2.1]

theorem planeCuspVector_scalar {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f)
    (t : Adelesˣ) (g : AdelicGL) :
    planeCuspVector hf (planeLevi 1 t * g) =
      (D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane s)) •
        planeCuspVector hf g := by
  apply D.cusp.injective
  funext A
  rw [map_smul]
  change _ = (D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane s)) * _
  rw [realize_planeCuspVector, realize_planeCuspVector]
  have hcomm : planeLevi A 1 * planeLevi 1 t = planeLevi 1 t * planeLevi A 1 := by
    have hleft := (planeLeviHom Adeles).map_mul (A, 1) (1, t)
    have hright := (planeLeviHom Adeles).map_mul (1, t) (A, 1)
    change planeLevi (A * 1) (1 * t) = planeLevi A 1 * planeLevi 1 t at hleft
    change planeLevi (1 * A) (t * 1) = planeLevi 1 t * planeLevi A 1 at hright
    simp only [mul_one, one_mul] at hleft hright
    exact hleft.symm.trans hright
  rw [← mul_assoc, hcomm, mul_assoc, hf.2.2.2.2.1]
  ring

theorem planeCuspVector_binaryLevi {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f)
    (B : BinaryAdelicGL) (g : AdelicGL) :
    planeCuspVector hf (planeLevi B 1 * g) =
      normPower (Matrix.GeneralLinearGroup.det B) (binaryInductionExponent n .plane s) •
        (⟨D.cusp.π B (planeCuspVector hf g).val,
          D.cusp.smooth_stable B _ (planeCuspVector hf g).property⟩ : D.cusp.smooth) := by
  apply D.cusp.injective
  funext A
  rw [map_smul]
  change _ = normPower (Matrix.GeneralLinearGroup.det B)
    (binaryInductionExponent n .plane s) * _
  rw [D.cusp.equivariant, realize_planeCuspVector, realize_planeCuspVector,
    map_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_mul]
  have hmul := (planeLeviHom Adeles).map_mul (A, 1) (B, 1)
  have hlevi : planeLevi (A * B) 1 = planeLevi A 1 * planeLevi B 1 := by
    change planeLevi (A * B) (1 * 1) = planeLevi A 1 * planeLevi B 1 at hmul
    simpa only [mul_one] using hmul
  rw [hlevi, mul_assoc]
  simp only [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_neg, mul_assoc]
  rw [mul_left_comm (normPower (Matrix.GeneralLinearGroup.det B)
    (binaryInductionExponent n .plane s)),
    mul_inv_cancel_left₀ (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_ne_zero _ _)]

theorem norm_planeCuspVector_binaryLevi {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f)
    (B : BinaryAdelicGL) (g : AdelicGL) :
    ‖(planeCuspVector hf (planeLevi B 1 * g)).val‖ =
      Real.exp ((binaryInductionExponent n .plane s).re *
        Real.log (adeleNorm (Matrix.GeneralLinearGroup.det B) : ℝ)) *
          ‖(planeCuspVector hf g).val‖ := by
  rw [planeCuspVector_binaryLevi]
  change ‖normPower (Matrix.GeneralLinearGroup.det B)
    (binaryInductionExponent n .plane s) • D.cusp.π B (planeCuspVector hf g).val‖ = _
  rw [norm_smul, D.cusp.unitary, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.norm_normPower]

theorem planeCuspVector_smooth {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f) (g : AdelicGL) :
    Smooth (fun x : Fin 1 → RealGL3 =>
      (planeCuspVector hf (g * atInfinity (x 0))).val) := by
  rcases hf.2.2.1 g with ⟨v, hv, heval⟩
  have hvector : ∀ x : Fin 1 → RealGL3,
      planeCuspVector hf (g * atInfinity (x 0)) = v x := by
    intro x
    apply planeCuspVector_unique
    intro A
    exact heval x A
  simpa only [hvector] using hv

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors
