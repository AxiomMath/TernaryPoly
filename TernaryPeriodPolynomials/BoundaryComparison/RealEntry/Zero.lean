module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Basic

@[expose] public section


/-! The unperturbed (`ε = 0`, any `V`) branch: `entryCurve s t V 0 = L Lᵀ` is independent of `V`,
giving Clauses 1-2 of `real_entry_tangent`, plus the general bridge
`gramPlaneTau (entryCurve s t V 0) = entryTau (s, t)` used to simplify `entryBeta_v2`/`entryBeta_x0`
(which are stated in terms of `gramPlaneTau (entryCurve s t V 0)`). -/


namespace TernaryPeriodPolynomials.Argument

theorem entryCurve_const (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    entryCurve s t V 0 = entryFrame s t * (entryFrame s t).transpose := by
  unfold entryCurve
  rw [zero_smul, add_zero, Matrix.transpose_one, mul_one, mul_one]

theorem entryFrame_mul_transpose (s t : ℝ) :
    entryFrame s t * (entryFrame s t).transpose = !![1, 0, s; 0, 1, t; s, t, 1 + s ^ 2 + t ^ 2] := by
  unfold entryFrame
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  all_goals ring

theorem entryCurve_zero_eq (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    entryCurve s t V 0 = !![1, 0, s; 0, 1, t; s, t, 1 + s ^ 2 + t ^ 2] := by
  rw [entryCurve_const, entryFrame_mul_transpose]

theorem gramPlaneU_zero_eq (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    gramPlaneU (entryCurve s t V 0) = (s / (1 + s ^ 2 + t ^ 2), t / (1 + s ^ 2 + t ^ 2)) := by
  rw [entryCurve_zero_eq]
  rfl

theorem gramSchur_zero_eq (s t : ℝ) (hQne : (1 + s ^ 2 + t ^ 2 : ℝ) ≠ 0) :
    gramSchur !![1, 0, s; 0, 1, t; s, t, 1 + s ^ 2 + t ^ 2] =
      !![(1 + t ^ 2) / (1 + s ^ 2 + t ^ 2), -(s * t) / (1 + s ^ 2 + t ^ 2);
         -(s * t) / (1 + s ^ 2 + t ^ 2), (1 + s ^ 2) / (1 + s ^ 2 + t ^ 2)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (1 : ℝ) - s * s / (1 + s ^ 2 + t ^ 2) = (1 + t ^ 2) / (1 + s ^ 2 + t ^ 2)
    rw [show (s * s : ℝ) = s ^ 2 from by ring, one_sub_div_eq _ _ hQne]
    congr 1; ring
  · change (0 : ℝ) - s * t / (1 + s ^ 2 + t ^ 2) = -(s * t) / (1 + s ^ 2 + t ^ 2)
    ring
  · change (0 : ℝ) - t * s / (1 + s ^ 2 + t ^ 2) = -(s * t) / (1 + s ^ 2 + t ^ 2)
    ring
  · change (1 : ℝ) - t * t / (1 + s ^ 2 + t ^ 2) = (1 + s ^ 2) / (1 + s ^ 2 + t ^ 2)
    rw [show (t * t : ℝ) = t ^ 2 from by ring, one_sub_div_eq _ _ hQne]
    congr 1; ring

theorem gramPlaneTau_zero_eq (s t : ℝ) (hQpos : (0 : ℝ) < 1 + s ^ 2 + t ^ 2)
    (hApos : (0 : ℝ) < 1 + s ^ 2) :
    gramPlaneTau (!![1, 0, s; 0, 1, t; s, t, 1 + s ^ 2 + t ^ 2] : Matrix (Fin 3) (Fin 3) ℝ) =
      ((-(s * t) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) := by
  have hQne := hQpos.ne'
  have hAne := hApos.ne'
  have hS := gramSchur_zero_eq s t hQne
  have hdet :
      (!![(1 + t ^ 2) / (1 + s ^ 2 + t ^ 2), -(s * t) / (1 + s ^ 2 + t ^ 2);
          -(s * t) / (1 + s ^ 2 + t ^ 2), (1 + s ^ 2) / (1 + s ^ 2 + t ^ 2)] :
          Matrix (Fin 2) (Fin 2) ℝ).det = 1 / (1 + s ^ 2 + t ^ 2) := by
    rw [Matrix.det_fin_two_of, div_mul_div_comm, div_mul_div_comm, div_sub_div_same,
      div_eq_div_iff (mul_ne_zero hQne hQne) hQne]
    ring
  unfold gramPlaneTau
  rw [hS]
  change
      ((-(s * t) / (1 + s ^ 2 + t ^ 2) / ((1 + s ^ 2) / (1 + s ^ 2 + t ^ 2)) : ℝ) : ℂ) +
        Complex.I *
          ((Real.sqrt
                ((!![(1 + t ^ 2) / (1 + s ^ 2 + t ^ 2), -(s * t) / (1 + s ^ 2 + t ^ 2);
                    -(s * t) / (1 + s ^ 2 + t ^ 2), (1 + s ^ 2) / (1 + s ^ 2 + t ^ 2)] :
                    Matrix (Fin 2) (Fin 2) ℝ).det) /
              ((1 + s ^ 2) / (1 + s ^ 2 + t ^ 2)) : ℝ) : ℂ) =
      ((-(s * t) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ)
  rw [hdet]
  congr 2
  · exact div_div_eq_div _ _ _ hQne hAne
  · exact_mod_cast sqrt_div_lemma _ _ hQpos hApos

/-- The two-term closed form of `gramPlaneTau (entryCurve s t V 0)`, matching
`gramPlaneTau_zero_eq`'s shape (used directly in the Clause 5 algebra). -/
theorem gramPlaneTau_entryCurve_zero_eq' (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    gramPlaneTau (entryCurve s t V 0) =
      ((-(s * t) / (1 + s ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) := by
  rw [entryCurve_zero_eq]
  exact gramPlaneTau_zero_eq s t (by positivity) (by positivity)

theorem entryRadius_sq (s t : ℝ) : entryRadius (s, t) ^ 2 = 1 + s ^ 2 + t ^ 2 := by
  show Real.sqrt (1 + s ^ 2 + t ^ 2) ^ 2 = 1 + s ^ 2 + t ^ 2
  rw [sq, Real.mul_self_sqrt (by positivity)]

theorem entryRadius_pos (s t : ℝ) : 0 < entryRadius (s, t) := by
  show 0 < Real.sqrt (1 + s ^ 2 + t ^ 2)
  exact Real.sqrt_pos.mpr (by positivity)

/-- `gramPlaneTau (entryCurve s t V 0) = entryTau (s, t)`, i.e. Clause 2 of `real_entry_tangent`
for an arbitrary tangent direction `V` (Clause 2 itself is the special case `V = 0`). -/
theorem gramPlaneTau_entryCurve_zero_eq (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    gramPlaneTau (entryCurve s t V 0) = entryTau (s, t) := by
  rw [gramPlaneTau_entryCurve_zero_eq']
  show ((-(s * t) / (1 + s ^ 2) : ℝ) : ℂ) +
      Complex.I * ((Real.sqrt (1 + s ^ 2 + t ^ 2) / (1 + s ^ 2) : ℝ) : ℂ) =
    (((-(s * t) : ℝ) : ℂ) + Complex.I * (Real.sqrt (1 + s ^ 2 + t ^ 2) : ℂ)) /
      ((1 + s ^ 2 : ℝ) : ℂ)
  rw [Complex.ofReal_div, Complex.ofReal_div, add_div, mul_div_assoc]

theorem real_entry_tangent_clause1 (s t : ℝ) :
    gramPlaneU (entryCurve s t 0 0) = (s / entryRadius (s, t) ^ 2, t / entryRadius (s, t) ^ 2) := by
  rw [gramPlaneU_zero_eq, entryRadius_sq]

theorem real_entry_tangent_clause2 (s t : ℝ) :
    gramPlaneTau (entryCurve s t 0 0) = entryTau (s, t) :=
  gramPlaneTau_entryCurve_zero_eq s t 0

end TernaryPeriodPolynomials.Argument
