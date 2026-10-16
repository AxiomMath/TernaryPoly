module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section


/-! The `v₂ = E₁₃` tangent-direction branch of Appendix C.5's tangent entry, i.e. the perturbation
`V = Matrix.single 0 2 1`. -/


namespace TernaryPeriodPolynomials.Argument

theorem gramSchur_v2_eq (s t ε : ℝ) (hQne : (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 : ℝ) ≠ 0) :
    gramSchur !![1, 0, s; 0, 1, t + ε; s, t + ε, 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2] =
      !![(1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - s ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2),
          -(s * (t + ε)) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2);
         -(s * (t + ε)) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2),
          (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - (t + ε) ^ 2) /
            (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (1 : ℝ) - s * s / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) =
      (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - s ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)
    rw [show (s * s : ℝ) = s ^ 2 from by ring]
    exact one_sub_div_eq _ _ hQne
  · change (0 : ℝ) - s * (t + ε) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) =
      -(s * (t + ε)) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)
    ring
  · change (0 : ℝ) - (t + ε) * s / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) =
      -(s * (t + ε)) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)
    ring
  · change (1 : ℝ) - (t + ε) * (t + ε) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) =
      (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - (t + ε) ^ 2) /
        (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)
    rw [show ((t + ε) * (t + ε) : ℝ) = (t + ε) ^ 2 from by ring]
    exact one_sub_div_eq _ _ hQne

theorem gramPlaneTau_v2_eq (s t ε : ℝ) (hQpos : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)
    (hApos : (0 : ℝ) < 1 + s ^ 2) :
    gramPlaneTau
        (!![1, 0, s; 0, 1, t + ε; s, t + ε, 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2] :
          Matrix (Fin 3) (Fin 3) ℝ) =
      ((-(s * (t + ε)) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) := by
  have hQne := hQpos.ne'
  have hAne := hApos.ne'
  have hS := gramSchur_v2_eq s t ε hQne
  have hC11 : (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - (t + ε) ^ 2) /
        (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) =
      (1 + s ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) := by
    rw [show (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - (t + ε) ^ 2 : ℝ) = 1 + s ^ 2 from by ring]
  have hdet :
      (!![(1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - s ^ 2) /
              (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2),
            -(s * (t + ε)) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2);
          -(s * (t + ε)) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2),
            (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - (t + ε) ^ 2) /
              (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)] :
          Matrix (Fin 2) (Fin 2) ℝ).det =
        1 / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) := by
    rw [Matrix.det_fin_two_of, div_mul_div_comm, div_mul_div_comm, div_sub_div_same,
      div_eq_div_iff (mul_ne_zero hQne hQne) hQne]
    ring
  unfold gramPlaneTau
  rw [hS]
  change
      ((-(s * (t + ε)) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) /
          ((1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - (t + ε) ^ 2) /
            (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)) : ℝ) : ℂ) +
        Complex.I *
          ((Real.sqrt
                ((!![(1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - s ^ 2) /
                        (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2),
                      -(s * (t + ε)) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2);
                    -(s * (t + ε)) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2),
                      (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - (t + ε) ^ 2) /
                        (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)] :
                    Matrix (Fin 2) (Fin 2) ℝ).det) /
              ((1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 - (t + ε) ^ 2) /
                (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)) : ℝ) : ℂ) =
      ((-(s * (t + ε)) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ)
  rw [hdet, hC11]
  congr 2
  · exact div_div_eq_div _ _ _ hQne hAne
  · exact_mod_cast sqrt_div_lemma _ _ hQpos hApos

theorem single_v2_eq : (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply_same, Matrix.single_apply_of_ne]

theorem one_add_eps_v2_eq (ε : ℝ) :
    (1 + ε • (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) : Matrix (Fin 3) (Fin 3) ℝ) =
      !![1, 0, ε; 0, 1, 0; 0, 0, 1] := by
  rw [single_v2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem entryCurve_v2_eq (s t ε : ℝ) :
    entryCurve s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε =
      !![1, 0, s; 0, 1, t + ε; s, t + ε, 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2] := by
  have hA : (1 + ε • (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) : Matrix (Fin 3) (Fin 3) ℝ) =
      !![1, 0, ε; 0, 1, 0; 0, 0, 1] := one_add_eps_v2_eq ε
  unfold entryCurve entryFrame
  rw [hA]
  have hM : (!![0, 1, 0; 0, 0, 1; 1, s, t] : Matrix (Fin 3) (Fin 3) ℝ) *
      !![1, 0, ε; 0, 1, 0; 0, 0, 1] = !![0, 1, 0; 0, 0, 1; 1, s, t + ε] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]; ring
  rw [hM]
  have hN : (!![0, 1, 0; 0, 0, 1; 1, s, t + ε] : Matrix (Fin 3) (Fin 3) ℝ) *
      (!![1, 0, ε; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).transpose =
      !![0, 1, 0; ε, 0, 1; 1 + t * ε + ε ^ 2, s, t + ε] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]; ring
  rw [hN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> ring

theorem gramPlaneTau_entryCurve_v2_eq (s t ε : ℝ)
    (hQpos : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) (hApos : (0 : ℝ) < 1 + s ^ 2) :
    gramPlaneTau (entryCurve s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε) =
      ((-(s * (t + ε)) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) := by
  rw [entryCurve_v2_eq]
  exact gramPlaneTau_v2_eq s t ε hQpos hApos

theorem Q_v2_pos (s t ε : ℝ) : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 := by
  have h : (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2 : ℝ) = (1 + s ^ 2) + (t + ε) ^ 2 := by ring
  rw [h]; positivity

theorem entryDTau_v2_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun ε : ℝ => gramPlaneTau
        (entryCurve s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε))
      (((-s / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ)) 0 := by
  have hApos : (0 : ℝ) < 1 + s ^ 2 := by positivity
  have hfun : (fun ε : ℝ => gramPlaneTau
        (entryCurve s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε)) =
      (fun ε : ℝ => ((-(s * (t + ε)) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I *
          ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ)) :=
    funext fun ε => gramPlaneTau_entryCurve_v2_eq s t ε (Q_v2_pos s t ε) hApos
  rw [hfun]
  have hR1 : HasDerivAt (fun ε : ℝ => -(s * (t + ε)) / (1 + s ^ 2)) (-s / (1 + s ^ 2)) 0 := by
    have hid : HasDerivAt (fun ε : ℝ => t + ε) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add t
    have hmul : HasDerivAt (fun ε : ℝ => (-s) * (t + ε)) (1 * (-s)) 0 :=
      hasDerivAt_const_mul_comp (-s) hid
    have hval : (1 * (-s) : ℝ) = -s := by ring
    rw [hval] at hmul
    have hdiv := hasDerivAt_div_const_comp (1 + s ^ 2) hmul
    have hfe : (fun ε : ℝ => -s * (t + ε) / (1 + s ^ 2)) =
        (fun ε : ℝ => -(s * (t + ε)) / (1 + s ^ 2)) := by funext ε; ring
    rwa [hfe] at hdiv
  have hR2 : HasDerivAt (fun ε : ℝ => Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2))
      (t / Real.sqrt (1 + s ^ 2 + t ^ 2)) 0 := by
    have hid : HasDerivAt (fun ε : ℝ => t + ε) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add t
    have hpow : HasDerivAt (fun ε : ℝ => (t + ε) ^ 2) (2 * (t + 0) ^ 1 * 1) 0 := hid.pow 2
    have hQ0 : HasDerivAt (fun ε : ℝ => (1 + s ^ 2) + (t + ε) ^ 2) (2 * (t + 0) ^ 1 * 1) 0 :=
      hpow.const_add (1 + s ^ 2)
    have hfe : (fun ε : ℝ => (1 + s ^ 2) + (t + ε) ^ 2) =
        (fun ε : ℝ => 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) := funext fun ε => by ring
    have hval : (2 * (t + 0) ^ 1 * 1 : ℝ) = 2 * t := by ring
    have hQ : HasDerivAt (fun ε : ℝ => 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) (2 * t) (0 : ℝ) := by
      rw [← hfe, ← hval]; exact hQ0
    have hz : (1 + s ^ 2 + t ^ 2 + 2 * t * (0 : ℝ) + (0 : ℝ) ^ 2 : ℝ) = 1 + s ^ 2 + t ^ 2 := by
      ring
    have hne : (1 + s ^ 2 + t ^ 2 + 2 * t * (0 : ℝ) + (0 : ℝ) ^ 2 : ℝ) ≠ 0 := by
      rw [hz]; positivity
    have hsqrt := hQ.sqrt hne
    have hval2 : (2 * t / (2 * Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * t * (0 : ℝ) + (0 : ℝ) ^ 2))
        : ℝ) = t / Real.sqrt (1 + s ^ 2 + t ^ 2) := by
      rw [hz, mul_div_mul_left t (Real.sqrt (1 + s ^ 2 + t ^ 2)) (two_ne_zero)]
    rw [hval2] at hsqrt
    exact hsqrt
  have hC1 : HasDerivAt (fun ε : ℝ => ((-(s * (t + ε)) / (1 + s ^ 2) : ℝ) : ℂ))
      ((-s / (1 + s ^ 2) : ℝ) : ℂ) 0 := hasDerivAt_ofReal_comp hR1
  have hR2' :
      HasDerivAt (fun ε : ℝ => Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) / (1 + s ^ 2))
        (t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2)) 0 :=
    hasDerivAt_div_const_comp (1 + s ^ 2) hR2
  have hC2 :
      HasDerivAt
        (fun ε : ℝ =>
          ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ))
        ((t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) 0 := hasDerivAt_ofReal_comp hR2'
  have hC2' : HasDerivAt (fun ε : ℝ => Complex.I *
      ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ))
      (Complex.I * ((t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ)) 0 := by
    have h := hasDerivAt_const_mul_C_comp Complex.I hC2
    have hv : ((t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) * Complex.I
        = Complex.I * ((t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) := mul_comm _ _
    rwa [hv] at h
  exact hasDerivAt_add_C hC1 hC2'

theorem entryDTau_v2 (s t : ℝ) :
    entryDTau s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) =
      ((-s / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) := by
  unfold entryDTau
  exact (entryDTau_v2_hasDerivAt s t).deriv

theorem gramPlaneU_entryCurve_v2_eq (s t ε : ℝ) :
    gramPlaneU (entryCurve s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε) =
      (s / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2),
        (t + ε) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)) := by
  rw [entryCurve_v2_eq]
  rfl

theorem entryDU1_v2_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun ε : ℝ =>
        (gramPlaneU (entryCurve s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε)).1)
      (-(2 * s * t) / (1 + s ^ 2 + t ^ 2) ^ 2) 0 := by
  have hfun : (fun ε : ℝ =>
      (gramPlaneU (entryCurve s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε)).1) =
      (fun ε : ℝ => s / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)) :=
    funext fun ε => congrArg Prod.fst (gramPlaneU_entryCurve_v2_eq s t ε)
  rw [hfun]
  have hf : HasDerivAt (fun _ : ℝ => s) (0 : ℝ) 0 := hasDerivAt_const 0 s
  have hid : HasDerivAt (fun ε : ℝ => t + ε) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add t
  have hpow : HasDerivAt (fun ε : ℝ => (t + ε) ^ 2) (2 * (t + 0) ^ 1 * 1) 0 := hid.pow 2
  have hQ0 : HasDerivAt (fun ε : ℝ => (1 + s ^ 2) + (t + ε) ^ 2) (2 * (t + 0) ^ 1 * 1) 0 :=
    hpow.const_add (1 + s ^ 2)
  have hfe : (fun ε : ℝ => (1 + s ^ 2) + (t + ε) ^ 2) =
      (fun ε : ℝ => 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) := funext fun ε => by ring
  have hval : (2 * (t + 0) ^ 1 * 1 : ℝ) = 2 * t := by ring
  have hg : HasDerivAt (fun ε : ℝ => 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) (2 * t) (0 : ℝ) := by
    rw [← hfe, ← hval]; exact hQ0
  have hne := (Q_v2_pos s t 0).ne'
  have hdiv := hf.div hg hne
  have hv : ((0 : ℝ) * (1 + s ^ 2 + t ^ 2 + 2 * t * 0 + 0 ^ 2) - s * (2 * t)) /
      (1 + s ^ 2 + t ^ 2 + 2 * t * 0 + 0 ^ 2) ^ 2 = -(2 * s * t) / (1 + s ^ 2 + t ^ 2) ^ 2 := by
    ring
  rwa [hv] at hdiv

theorem entryDU2_v2_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun ε : ℝ =>
        (gramPlaneU (entryCurve s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε)).2)
      ((1 + s ^ 2 - t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2) 0 := by
  have hfun : (fun ε : ℝ =>
      (gramPlaneU (entryCurve s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε)).2) =
      (fun ε : ℝ => (t + ε) / (1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2)) :=
    funext fun ε => congrArg Prod.snd (gramPlaneU_entryCurve_v2_eq s t ε)
  rw [hfun]
  have hid : HasDerivAt (fun ε : ℝ => t + ε) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add t
  have hpow : HasDerivAt (fun ε : ℝ => (t + ε) ^ 2) (2 * (t + 0) ^ 1 * 1) 0 := hid.pow 2
  have hQ0 : HasDerivAt (fun ε : ℝ => (1 + s ^ 2) + (t + ε) ^ 2) (2 * (t + 0) ^ 1 * 1) 0 :=
    hpow.const_add (1 + s ^ 2)
  have hfe : (fun ε : ℝ => (1 + s ^ 2) + (t + ε) ^ 2) =
      (fun ε : ℝ => 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) := funext fun ε => by ring
  have hval : (2 * (t + 0) ^ 1 * 1 : ℝ) = 2 * t := by ring
  have hg : HasDerivAt (fun ε : ℝ => 1 + s ^ 2 + t ^ 2 + 2 * t * ε + ε ^ 2) (2 * t) (0 : ℝ) := by
    rw [← hfe, ← hval]; exact hQ0
  have hne := (Q_v2_pos s t 0).ne'
  have hdiv := hid.div hg hne
  have hv : ((1 : ℝ) * (1 + s ^ 2 + t ^ 2 + 2 * t * 0 + 0 ^ 2) - (t + 0) * (2 * t)) /
      (1 + s ^ 2 + t ^ 2 + 2 * t * 0 + 0 ^ 2) ^ 2 =
      (1 + s ^ 2 - t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2 := by
    ring
  rwa [hv] at hdiv

theorem entryBeta_v2 (s t : ℝ) :
    entryBeta s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) =
      ((-(2 * s * t) / (1 + s ^ 2 + t ^ 2) ^ 2 : ℝ) : ℂ) -
        gramPlaneTau (entryCurve s t (Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : ℝ)) 0) *
          (((1 + s ^ 2 - t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2 : ℝ) : ℂ) := by
  unfold entryBeta
  rw [(hasDerivAt_ofReal_comp (entryDU1_v2_hasDerivAt s t)).deriv,
    (hasDerivAt_ofReal_comp (entryDU2_v2_hasDerivAt s t)).deriv]

end TernaryPeriodPolynomials.Argument
