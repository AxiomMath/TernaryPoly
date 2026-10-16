module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualSpace

@[expose] public section


/-!
# General coercivity, dual coefficients: the Cartan isomorphism of form spaces

For an admissible group `Γ` the Cartan pullback `ioPull` is a linear isomorphism
`dualEquiv : DForm Γ n k ≃ₗ[ℝ] CForm (θΓ) n k`; the exterior derivative of dual forms is the exterior
derivative of the underlying functions and corresponds to the exterior derivative of `CForm`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormConnection
open Set Filter
open scoped ContDiff Topology

variable {Γ : Subgroup RealGL} {n k : ℕ}

/-- The Cartan pullback as a linear map of smooth forms. -/
def ioPullForm (n k : ℕ) : Form (F := Coefficients n) positiveCoordinates k →ₗ[ℝ]
    Form (F := Coefficients n) positiveCoordinates k where
  toFun w := restrictForm positiveCoordinates (ioPull n k (w : Coordinates → FormValue n k))
    (contDiffOn_ioPull n k (Form.smooth w))
  map_add' w z := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ positiveCoordinates
    · simp only [restrictForm, Submodule.coe_add, Pi.add_apply, indicator_of_mem hx,
        ioPull_apply n k _ hx]
      ext v
      simp
    · simp only [restrictForm, Submodule.coe_add, Pi.add_apply, indicator_of_notMem hx, add_zero]
  map_smul' c w := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ positiveCoordinates
    · simp only [restrictForm, SetLike.val_smul, Pi.smul_apply, indicator_of_mem hx,
        ioPull_apply n k _ hx, RingHom.id_apply]
      ext v
      simp
    · simp only [restrictForm, SetLike.val_smul, Pi.smul_apply, indicator_of_notMem hx, smul_zero]

theorem ioPullForm_coe (w : Form (F := Coefficients n) positiveCoordinates k) :
    (ioPullForm n k w : Coordinates → FormValue n k) =
      ioPull n k (w : Coordinates → FormValue n k) := by
  funext x
  by_cases hx : x ∈ positiveCoordinates
  · exact restrictForm_apply (ioPull n k (w : Coordinates → FormValue n k))
      (contDiffOn_ioPull n k (Form.smooth w)) hx
  · rw [Form.outside _ hx, ioPull_of_notMem n k _ hx]

theorem ioPullForm_ioPullForm (w : Form (F := Coefficients n) positiveCoordinates k) :
    ioPullForm n k (ioPullForm n k w) = w := by
  apply Form.ext
  intro x hx
  rw [ioPullForm_coe, ioPullForm_coe]
  exact ioPull_ioPull n k _ hx

theorem thetaImage_mem_iff {a : RealGL} : a ∈ thetaImage Γ → thetaHom a ∈ Γ := by
  rintro ⟨g, hg, rfl⟩
  rw [thetaHom_thetaHom]
  exact hg

theorem theta_mem_thetaImage {a : RealGL} (ha : a ∈ Γ) : thetaHom a ∈ thetaImage Γ := ⟨a, ha, rfl⟩

/-- Dual forms of `Γ` correspond to standard forms of `θΓ`. -/
def toStd (h : Admissible Γ) (n k : ℕ) : DForm Γ n k →ₗ[ℝ] CForm (thetaImage Γ) n k where
  toFun w := ⟨ioPullForm n k w, by
      rw [ioPullForm_coe]; exact isEquivariant_ioPull_std w.2.1, by
      have := h.theta.t2
      rw [ioPullForm_coe]
      exact isCompact_projSupport_ioPull Γ (thetaImage Γ) (fun a ha => theta_mem_thetaImage ha)
        w.2.2⟩
  map_add' w z := Subtype.ext ((ioPullForm n k).map_add _ _)
  map_smul' c w := Subtype.ext ((ioPullForm n k).map_smul _ _)

/-- Standard forms of `θΓ` correspond to dual forms of `Γ`. -/
def ofStd (h : Admissible Γ) (n k : ℕ) : CForm (thetaImage Γ) n k →ₗ[ℝ] DForm Γ n k where
  toFun w := ⟨ioPullForm n k w, by
      rw [ioPullForm_coe]; exact isRepEquivariant_ioPull_dual w.2.1, by
      have := h.t2
      rw [ioPullForm_coe]
      exact isCompact_projSupport_ioPull (thetaImage Γ) Γ (fun a ha => thetaImage_mem_iff ha)
        w.2.2⟩
  map_add' w z := Subtype.ext ((ioPullForm n k).map_add _ _)
  map_smul' c w := Subtype.ext ((ioPullForm n k).map_smul _ _)

theorem toStd_fn (h : Admissible Γ) (w : DForm Γ n k) :
    CForm.fn (toStd h n k w) = ioPull n k (DForm.fn w) := ioPullForm_coe _

theorem ofStd_fn (h : Admissible Γ) (w : CForm (thetaImage Γ) n k) :
    DForm.fn (ofStd h n k w) = ioPull n k (CForm.fn w) := ioPullForm_coe _

theorem ofStd_toStd (h : Admissible Γ) (w : DForm Γ n k) : ofStd h n k (toStd h n k w) = w :=
  Subtype.ext (ioPullForm_ioPullForm _)

theorem toStd_ofStd (h : Admissible Γ) (w : CForm (thetaImage Γ) n k) :
    toStd h n k (ofStd h n k w) = w :=
  Subtype.ext (ioPullForm_ioPullForm _)

/-- The Cartan isomorphism between dual forms of `Γ` and standard forms of `θΓ`. -/
def dualEquiv (h : Admissible Γ) (n k : ℕ) : DForm Γ n k ≃ₗ[ℝ] CForm (thetaImage Γ) n k :=
  LinearEquiv.ofLinearMap (toStd h n k) (ofStd h n k)
    (LinearMap.ext fun w => toStd_ofStd h w) (LinearMap.ext fun w => ofStd_toStd h w)

/-- The exterior derivative of dual forms, transported along the Cartan isomorphism. -/
def dualD (h : Admissible Γ) (n k : ℕ) : DForm Γ n k →ₗ[ℝ] DForm Γ n (k + 1) :=
  (ofStd h n (k + 1)).comp ((CForm.d (thetaImage Γ) n k).comp (toStd h n k))

theorem ioPull_congr (n k : ℕ) {f g : Coordinates → FormValue n k}
    (hfg : EqOn f g positiveCoordinates) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    ioPull n k f x = ioPull n k g x := by
  rw [ioPull_apply n k f hx, ioPull_apply n k g hx, hfg (iotaC_mem hx)]

/-- The exterior derivative of a dual form is the exterior derivative of its coordinate function. -/
theorem dualD_apply (h : Admissible Γ) (a : DForm Γ n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    DForm.fn (dualD h n k a) x = extDeriv (DForm.fn a) x := by
  calc DForm.fn (dualD h n k a) x
      = ioPull n (k + 1) (CForm.fn (CForm.d (thetaImage Γ) n k (toStd h n k a))) x := by
        show DForm.fn (ofStd h n (k + 1) (CForm.d (thetaImage Γ) n k (toStd h n k a))) x = _
        rw [ofStd_fn]
    _ = ioPull n (k + 1) (ioPull n (k + 1) (extDeriv (DForm.fn a))) x := by
        exact ioPull_congr n (k + 1) (fun y hy => by
          rw [CForm.d_apply _ hy, toStd_fn, extDeriv_ioPull n k (DForm.smooth a) hy]) hx
    _ = extDeriv (DForm.fn a) x := ioPull_ioPull n (k + 1) _ hx

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
