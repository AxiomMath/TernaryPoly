module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualMeasure
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Main

@[expose] public section


/-!
# Proposition C.1 for the dual coefficient system

For the dual `E* = Sym^n ℝ³` of the polynomial coefficient bundle `E = Sym^n((ℝ³)*)`, with the flat
metric `‖ρ*(g)⁻¹ v‖`, the coercivity estimate `‖Dω‖² + ‖D*ω‖² ≥ c ‖ω‖²` holds with the same constant `c`
as for `E`, for every admissible group `Γ`.  Here `D` is the exterior derivative of dual forms and
`D*` is *the* formal adjoint of `D` for the dual `L²` pairing (an adjoint exists and is unique);
the estimate is stated for every formal adjoint `e`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive

variable {Γ : Subgroup RealGL} {n k : ℕ}

/-- `e` is a formal adjoint of the exterior derivative of dual forms at `b`, for the dual `L²`
pairing. -/
def IsDualFormalAdjoint (h : Admissible Γ) (b : DForm Γ n (k + 1)) (e : DForm Γ n k) : Prop :=
  ∀ a : DForm Γ n k, dualL2 (dualD h n k a) b = dualL2 a e

theorem toStd_dualD (h : Admissible Γ) (a : DForm Γ n k) :
    toStd h n (k + 1) (dualD h n k a) = CForm.d (thetaImage Γ) n k (toStd h n k a) :=
  toStd_ofStd h _

theorem isDualFormalAdjoint_iff (h : Admissible Γ) (b : DForm Γ n (k + 1)) (e : DForm Γ n k) :
    IsDualFormalAdjoint h b e ↔
      IsFormalAdjoint (thetaImage Γ) n k (toStd h n (k + 1) b) (toStd h n k e) := by
  constructor
  · intro hd a'
    have h1 := hd (ofStd h n k a')
    have e1 := dualL2_eq h (dualD h n k (ofStd h n k a')) b
    have t1 : toStd h n (k + 1) (dualD h n k (ofStd h n k a')) = CForm.d (thetaImage Γ) n k a' :=
      (toStd_dualD h _).trans (congrArg (CForm.d (thetaImage Γ) n k) (toStd_ofStd h a'))
    have e1' := e1.trans
      (congrArg (fun x => l2Form (thetaImage Γ) n (k + 1) x (toStd h n (k + 1) b)) t1)
    have e2 := dualL2_eq h (ofStd h n k a') e
    have e2' := e2.trans
      (congrArg (fun x => l2Form (thetaImage Γ) n k x (toStd h n k e)) (toStd_ofStd h a'))
    exact e1'.symm.trans (h1.trans e2')
  · intro hf a
    have e1 := dualL2_eq h (dualD h n k a) b
    have e1' := e1.trans
      (congrArg (fun x => l2Form (thetaImage Γ) n (k + 1) x (toStd h n (k + 1) b)) (toStd_dualD h a))
    have e2 := dualL2_eq h a e
    exact e1'.trans ((hf (toStd h n k a)).trans e2.symm)

/-- The dual formal adjoint, transported from the explicit local adjoint. -/
def dualDelta (h : Admissible Γ) (n k : ℕ) : DForm Γ n (k + 1) →ₗ[ℝ] DForm Γ n k :=
  (ofStd h n k).comp ((CForm.delta (thetaImage Γ) n k).comp (toStd h n (k + 1)))

theorem toStd_dualDelta (h : Admissible Γ) (b : DForm Γ n (k + 1)) :
    toStd h n k (dualDelta h n k b) = CForm.delta (thetaImage Γ) n k (toStd h n (k + 1) b) :=
  toStd_ofStd h _

/-- The dual formal adjoint exists: `dualDelta` is one. -/
theorem dualDelta_isFormalAdjoint (h : Admissible Γ) (b : DForm Γ n (k + 1)) :
    IsDualFormalAdjoint h b (dualDelta h n k b) := by
  rw [isDualFormalAdjoint_iff, toStd_dualDelta]
  exact h.theta.delta_isFormalAdjoint _

/-- The dual formal adjoint is unique. -/
theorem dual_adjoint_unique (h : Admissible Γ) (b : DForm Γ n (k + 1)) (e : DForm Γ n k)
    (he : IsDualFormalAdjoint h b e) : e = dualDelta h n k b := by
  have h1 := h.theta.delta_unique _ _ ((isDualFormalAdjoint_iff h b e).mp he)
  have h1' : toStd h n k e = toStd h n k (dualDelta h n k b) :=
    h1.trans (toStd_dualDelta h b).symm
  exact (ofStd_toStd h e).symm.trans ((congrArg (ofStd h n k) h1').trans (ofStd_toStd h _))

/-- **Proposition C.1, dual coefficients.**  The constant of the standard coefficient system works
for the dual coefficient system and every admissible group: `c ‖a‖² ≤ ‖D a‖²` in degree zero and
`c ‖a‖² ≤ ‖e‖² + ‖D a‖²` in degree `k + 1` for every formal adjoint `e` of `D` at `a`. -/
theorem general_coercivity_dual (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Γ : Subgroup RealGL) (h : Admissible Γ),
      (∀ a : DForm Γ n 0, c * dualNormSq a ≤ dualNormSq (dualD h n 0 a)) ∧
        ∀ (k : ℕ) (a : DForm Γ n (k + 1)) (e : DForm Γ n k), IsDualFormalAdjoint h a e →
          c * dualNormSq a ≤ dualNormSq e + dualNormSq (dualD h n (k + 1) a) := by
  obtain ⟨c, hc, H⟩ := general_coercivity n hn
  refine ⟨c, hc, fun Γ h => ⟨fun a => ?_, fun k a e hae => ?_⟩⟩
  · have h1 := (H _ h.theta).1 (toStd h n 0 a)
    exact (congrArg (c * ·) (dualNormSq_eq h a)).trans_le
      (h1.trans_eq ((congrArg normSq (toStd_dualD h a)).symm.trans (dualNormSq_eq h _).symm))
  · have he : toStd h n k e = CForm.delta (thetaImage Γ) n k (toStd h n (k + 1) a) :=
      h.theta.delta_unique _ _ ((isDualFormalAdjoint_iff h a e).mp hae)
    have h1 := (H _ h.theta).2 k (toStd h n (k + 1) a)
    exact (congrArg (c * ·) (dualNormSq_eq h a)).trans_le
      (h1.trans_eq (congrArg₂ (· + ·) ((congrArg normSq he).symm.trans (dualNormSq_eq h e).symm)
        ((congrArg normSq (toStd_dualD h a)).symm.trans (dualNormSq_eq h _).symm)))

/-- The estimate with the explicit dual formal adjoint. -/
theorem general_coercivity_dualDelta (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Γ : Subgroup RealGL) (h : Admissible Γ) (k : ℕ) (a : DForm Γ n (k + 1)),
      c * dualNormSq a ≤ dualNormSq (dualDelta h n k a) + dualNormSq (dualD h n (k + 1) a) := by
  obtain ⟨c, hc, H⟩ := general_coercivity_dual n hn
  exact ⟨c, hc, fun Γ h k a => (H Γ h).2 k a _ (dualDelta_isFormalAdjoint h a)⟩

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
