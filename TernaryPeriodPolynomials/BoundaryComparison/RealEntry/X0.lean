module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section


/-! The `x₀ = E₂₃` tangent-direction branch of Appendix C.5's tangent entry, i.e. the perturbation
`V = Matrix.single 1 2 1`. -/


namespace TernaryPeriodPolynomials.Argument

theorem single_x0_eq :
    (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) = !![0, 0, 0; 0, 0, 1; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply_same, Matrix.single_apply_of_ne]

theorem one_add_eps_x0_eq (ε : ℝ) :
    (1 + ε • (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) : Matrix (Fin 3) (Fin 3) ℝ) =
      !![1, 0, 0; 0, 1, ε; 0, 0, 1] := by
  rw [single_x0_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem entryCurve_x0_eq (s t ε : ℝ) :
    entryCurve s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε =
      !![1 + ε ^ 2, ε, s + s * ε ^ 2 + t * ε;
         ε, 1, s * ε + t;
         s + s * ε ^ 2 + t * ε, s * ε + t, 1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2] := by
  have hA : (1 + ε • (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) : Matrix (Fin 3) (Fin 3) ℝ) =
      !![1, 0, 0; 0, 1, ε; 0, 0, 1] := one_add_eps_x0_eq ε
  unfold entryCurve entryFrame
  rw [hA]
  have hM : (!![0, 1, 0; 0, 0, 1; 1, s, t] : Matrix (Fin 3) (Fin 3) ℝ) *
      !![1, 0, 0; 0, 1, ε; 0, 0, 1] = !![0, 1, ε; 0, 0, 1; 1, s, s * ε + t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  rw [hM]
  have hN : (!![0, 1, ε; 0, 0, 1; 1, s, s * ε + t] : Matrix (Fin 3) (Fin 3) ℝ) *
      (!![1, 0, 0; 0, 1, ε; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).transpose =
      !![0, 1 + ε ^ 2, ε; 0, ε, 1; 1, s + s * ε ^ 2 + t * ε, s * ε + t] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> ring
  rw [hN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> ring

theorem hasDerivAt_add_const_comp {f : ℝ → ℝ} {d x : ℝ} (hf : HasDerivAt f d x) (c : ℝ) :
    HasDerivAt (fun y => f y + c) d x := by
  have h := hf.add (hasDerivAt_const x c)
  have hv : (d + 0 : ℝ) = d := by ring
  rwa [hv] at h

theorem gramSchur_x0_eq (s t ε : ℝ)
    (hQne : (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2 : ℝ) ≠ 0) :
    gramSchur !![1 + ε ^ 2, ε, s + s * ε ^ 2 + t * ε;
                  ε, 1, s * ε + t;
                  s + s * ε ^ 2 + t * ε, s * ε + t,
                    1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2] =
      !![(1 + t ^ 2 + ε ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2),
          (ε - s * t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2);
         (ε - s * t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2),
          (1 + s ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (1 + ε ^ 2 : ℝ) - (s + s * ε ^ 2 + t * ε) * (s + s * ε ^ 2 + t * ε) /
        (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) =
      (1 + t ^ 2 + ε ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)
    rw [sub_eq_iff_eq_add, ← add_div, eq_div_iff hQne]
    ring
  · change (ε : ℝ) - (s + s * ε ^ 2 + t * ε) * (s * ε + t) /
        (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) =
      (ε - s * t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)
    rw [sub_eq_iff_eq_add, ← add_div, eq_div_iff hQne]
    ring
  · change (ε : ℝ) - (s * ε + t) * (s + s * ε ^ 2 + t * ε) /
        (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) =
      (ε - s * t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)
    rw [sub_eq_iff_eq_add, ← add_div, eq_div_iff hQne]
    ring
  · change (1 : ℝ) - (s * ε + t) * (s * ε + t) /
        (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) =
      (1 + s ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)
    rw [sub_eq_iff_eq_add, ← add_div, eq_div_iff hQne]
    ring

theorem Q_x0_pos (s t ε : ℝ) : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2 := by
  have h : (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2 : ℝ) = (1 + s ^ 2) + (s * ε + t) ^ 2 := by
    ring
  rw [h]; positivity

theorem gramPlaneTau_x0_eq (s t ε : ℝ)
    (hQpos : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)
    (hApos : (0 : ℝ) < 1 + s ^ 2) :
    gramPlaneTau
        (!![1 + ε ^ 2, ε, s + s * ε ^ 2 + t * ε;
            ε, 1, s * ε + t;
            s + s * ε ^ 2 + t * ε, s * ε + t, 1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2] :
          Matrix (Fin 3) (Fin 3) ℝ) =
      (((ε - s * t) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) := by
  have hQne := hQpos.ne'
  have hAne := hApos.ne'
  have hS := gramSchur_x0_eq s t ε hQne
  have hdet :
      (!![(1 + t ^ 2 + ε ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2),
            (ε - s * t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2);
          (ε - s * t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2),
            (1 + s ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)] :
          Matrix (Fin 2) (Fin 2) ℝ).det =
        1 / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) := by
    rw [Matrix.det_fin_two_of, div_mul_div_comm, div_mul_div_comm, div_sub_div_same,
      div_eq_div_iff (mul_ne_zero hQne hQne) hQne]
    ring
  unfold gramPlaneTau
  rw [hS]
  change
      (((ε - s * t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) /
          ((1 + s ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)) : ℝ) : ℂ) +
        Complex.I *
          ((Real.sqrt
                ((!![(1 + t ^ 2 + ε ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2),
                      (ε - s * t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2);
                    (ε - s * t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2),
                      (1 + s ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)] :
                    Matrix (Fin 2) (Fin 2) ℝ).det) /
              ((1 + s ^ 2) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)) : ℝ) : ℂ) =
      (((ε - s * t) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ)
  rw [hdet]
  congr 2
  · exact div_div_eq_div _ _ _ hQne hAne
  · exact_mod_cast sqrt_div_lemma _ _ hQpos hApos

theorem gramPlaneTau_entryCurve_x0_eq (s t ε : ℝ)
    (hQpos : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) (hApos : (0 : ℝ) < 1 + s ^ 2) :
    gramPlaneTau (entryCurve s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε) =
      (((ε - s * t) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) := by
  rw [entryCurve_x0_eq]
  exact gramPlaneTau_x0_eq s t ε hQpos hApos

theorem linEps_x0_hasDerivAt (s t : ℝ) : HasDerivAt (fun ε : ℝ => s * ε + t) s 0 := by
  have hlin : HasDerivAt (fun ε : ℝ => s * ε) (1 * s) 0 :=
    hasDerivAt_const_mul_comp s (hasDerivAt_id (0 : ℝ))
  have h' : HasDerivAt (fun ε : ℝ => s * ε + t) (1 * s) 0 := hasDerivAt_add_const_comp hlin t
  have hval : (1 * s : ℝ) = s := by ring
  rwa [hval] at h'

theorem Q_x0_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun ε : ℝ => 1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) (2 * s * t) 0 := by
  have hid2 := linEps_x0_hasDerivAt s t
  have hpow : HasDerivAt (fun ε : ℝ => (s * ε + t) ^ 2) (2 * (s * 0 + t) ^ 1 * s) 0 := hid2.pow 2
  have hQ0 : HasDerivAt (fun ε : ℝ => (1 + s ^ 2) + (s * ε + t) ^ 2) (2 * (s * 0 + t) ^ 1 * s) 0 :=
    hpow.const_add (1 + s ^ 2)
  have hfe : (fun ε : ℝ => (1 + s ^ 2) + (s * ε + t) ^ 2) =
      (fun ε : ℝ => 1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) := funext fun ε => by ring
  have hval : (2 * (s * 0 + t) ^ 1 * s : ℝ) = 2 * s * t := by ring
  rw [← hfe, ← hval]
  exact hQ0

theorem entryDTau_x0_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun ε : ℝ => gramPlaneTau
        (entryCurve s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε))
      (((1 / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((s * t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ)) 0 := by
  have hApos : (0 : ℝ) < 1 + s ^ 2 := by positivity
  have hfun : (fun ε : ℝ => gramPlaneTau
        (entryCurve s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε)) =
      (fun ε : ℝ => (((ε - s * t) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I *
          ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ)) :=
    funext fun ε => gramPlaneTau_entryCurve_x0_eq s t ε (Q_x0_pos s t ε) hApos
  rw [hfun]
  have hR1 : HasDerivAt (fun ε : ℝ => (ε - s * t) / (1 + s ^ 2)) (1 / (1 + s ^ 2)) 0 := by
    have hid2 : HasDerivAt (fun ε : ℝ => ε + -(s * t)) 1 0 :=
      hasDerivAt_add_const_comp (hasDerivAt_id (0 : ℝ)) (-(s * t))
    have hfe2 : (fun ε : ℝ => ε + -(s * t)) = (fun ε : ℝ => ε - s * t) := funext fun ε => by ring
    rw [hfe2] at hid2
    exact hasDerivAt_div_const_comp (1 + s ^ 2) hid2
  have hQ := Q_x0_hasDerivAt s t
  have hz : (1 + s ^ 2 + t ^ 2 + 2 * s * t * (0 : ℝ) + s ^ 2 * (0 : ℝ) ^ 2 : ℝ) = 1 + s ^ 2 + t ^ 2 := by
    ring
  have hne : (1 + s ^ 2 + t ^ 2 + 2 * s * t * (0 : ℝ) + s ^ 2 * (0 : ℝ) ^ 2 : ℝ) ≠ 0 := by
    rw [hz]; positivity
  have hsqrt := hQ.sqrt hne
  have hval2 : (2 * s * t /
        (2 * Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * s * t * (0 : ℝ) + s ^ 2 * (0 : ℝ) ^ 2)) : ℝ) =
      s * t / Real.sqrt (1 + s ^ 2 + t ^ 2) := by
    have hsqrtne : Real.sqrt (1 + s ^ 2 + t ^ 2) ≠ 0 := by
      have hp : (0 : ℝ) < 1 + s ^ 2 + t ^ 2 := by positivity
      exact (Real.sqrt_pos.mpr hp).ne'
    rw [hz, div_eq_div_iff (mul_ne_zero two_ne_zero hsqrtne) hsqrtne]
    ring
  rw [hval2] at hsqrt
  have hC1 : HasDerivAt (fun ε : ℝ => (((ε - s * t) / (1 + s ^ 2) : ℝ) : ℂ))
      ((1 / (1 + s ^ 2) : ℝ) : ℂ) 0 := hasDerivAt_ofReal_comp hR1
  have hR2' : HasDerivAt
      (fun ε : ℝ => Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) / (1 + s ^ 2))
      (s * t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2)) 0 :=
    hasDerivAt_div_const_comp (1 + s ^ 2) hsqrt
  have hC2 : HasDerivAt
      (fun ε : ℝ =>
        ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ))
      ((s * t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) 0 := hasDerivAt_ofReal_comp hR2'
  have hC2' : HasDerivAt (fun ε : ℝ => Complex.I *
      ((Real.sqrt (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2) / (1 + s ^ 2) : ℝ) : ℂ))
      (Complex.I * ((s * t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ)) 0 := by
    have h := hasDerivAt_const_mul_C_comp Complex.I hC2
    have hv : ((s * t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) * Complex.I
        = Complex.I * ((s * t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) := mul_comm _ _
    rwa [hv] at h
  exact hasDerivAt_add_C hC1 hC2'

theorem entryDTau_x0 (s t : ℝ) :
    entryDTau s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) =
      ((1 / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((s * t / Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) := by
  unfold entryDTau
  exact (entryDTau_x0_hasDerivAt s t).deriv

theorem gramPlaneU_entryCurve_x0_eq (s t ε : ℝ) :
    gramPlaneU (entryCurve s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε) =
      ((s + s * ε ^ 2 + t * ε) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2),
        (s * ε + t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)) := by
  rw [entryCurve_x0_eq]
  rfl

theorem entryDU1_x0_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun ε : ℝ =>
        (gramPlaneU (entryCurve s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε)).1)
      (t * (1 - s ^ 2 + t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2) 0 := by
  have hfun : (fun ε : ℝ =>
      (gramPlaneU (entryCurve s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε)).1) =
      (fun ε : ℝ => (s + s * ε ^ 2 + t * ε) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)) :=
    funext fun ε => congrArg Prod.fst (gramPlaneU_entryCurve_x0_eq s t ε)
  rw [hfun]
  have hsq : HasDerivAt (fun ε : ℝ => ε ^ 2) (2 * (0 : ℝ) ^ 1 * 1) 0 := (hasDerivAt_id (0 : ℝ)).pow 2
  have hssq : HasDerivAt (fun ε : ℝ => s * ε ^ 2) ((2 * (0 : ℝ) ^ 1 * 1) * s) 0 :=
    hasDerivAt_const_mul_comp s hsq
  have htlin : HasDerivAt (fun ε : ℝ => t * ε) (1 * t) 0 :=
    hasDerivAt_const_mul_comp t (hasDerivAt_id (0 : ℝ))
  have hsum1 : HasDerivAt (fun ε : ℝ => s * ε ^ 2 + t * ε) ((2 * (0 : ℝ) ^ 1 * 1) * s + 1 * t) 0 :=
    hssq.add htlin
  have hsum2 : HasDerivAt (fun ε : ℝ => s + (s * ε ^ 2 + t * ε)) ((2 * (0 : ℝ) ^ 1 * 1) * s + 1 * t) 0 :=
    hsum1.const_add s
  have hfe1 : (fun ε : ℝ => s + (s * ε ^ 2 + t * ε)) = (fun ε : ℝ => s + s * ε ^ 2 + t * ε) :=
    funext fun ε => by ring
  have hval1 : ((2 * (0 : ℝ) ^ 1 * 1) * s + 1 * t : ℝ) = t := by ring
  have hN1 : HasDerivAt (fun ε : ℝ => s + s * ε ^ 2 + t * ε) t 0 := by
    have h := hsum2
    rw [hval1] at h
    rwa [hfe1] at h
  have hQ := Q_x0_hasDerivAt s t
  have hne := (Q_x0_pos s t 0).ne'
  have hdiv := hN1.div hQ hne
  have hv : (t * (1 + s ^ 2 + t ^ 2 + 2 * s * t * 0 + s ^ 2 * 0 ^ 2) -
        (s + s * 0 ^ 2 + t * 0) * (2 * s * t)) /
      (1 + s ^ 2 + t ^ 2 + 2 * s * t * 0 + s ^ 2 * 0 ^ 2) ^ 2 =
      t * (1 - s ^ 2 + t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2 := by
    ring
  rwa [hv] at hdiv

theorem entryDU2_x0_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun ε : ℝ =>
        (gramPlaneU (entryCurve s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε)).2)
      (s * (1 + s ^ 2 - t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2) 0 := by
  have hfun : (fun ε : ℝ =>
      (gramPlaneU (entryCurve s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) ε)).2) =
      (fun ε : ℝ => (s * ε + t) / (1 + s ^ 2 + t ^ 2 + 2 * s * t * ε + s ^ 2 * ε ^ 2)) :=
    funext fun ε => congrArg Prod.snd (gramPlaneU_entryCurve_x0_eq s t ε)
  rw [hfun]
  have hN2 := linEps_x0_hasDerivAt s t
  have hQ := Q_x0_hasDerivAt s t
  have hne := (Q_x0_pos s t 0).ne'
  have hdiv := hN2.div hQ hne
  have hv : (s * (1 + s ^ 2 + t ^ 2 + 2 * s * t * 0 + s ^ 2 * 0 ^ 2) -
        (s * 0 + t) * (2 * s * t)) /
      (1 + s ^ 2 + t ^ 2 + 2 * s * t * 0 + s ^ 2 * 0 ^ 2) ^ 2 =
      s * (1 + s ^ 2 - t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2 := by
    ring
  rwa [hv] at hdiv

theorem entryBeta_x0 (s t : ℝ) :
    entryBeta s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) =
      ((t * (1 - s ^ 2 + t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2 : ℝ) : ℂ) -
        gramPlaneTau (entryCurve s t (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : ℝ)) 0) *
          ((s * (1 + s ^ 2 - t ^ 2) / (1 + s ^ 2 + t ^ 2) ^ 2 : ℝ) : ℂ) := by
  unfold entryBeta
  rw [(hasDerivAt_ofReal_comp (entryDU1_x0_hasDerivAt s t)).deriv,
    (hasDerivAt_ofReal_comp (entryDU2_x0_hasDerivAt s t)).deriv]

end TernaryPeriodPolynomials.Argument
