module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Forms.Basic
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Linear

@[expose] public section



/-! # General coercivity: the operators `d`, `δ`, `S⁺`, `S⁻` on compactly supported equivariant forms

The exterior derivative `CForm.d`, the explicit local adjoint `CForm.delta` and the symmetric
exterior and contraction operators `CForm.symExt`, `CForm.symCon` descend to the spaces `CForm Γ n k`
of an admissible group `Γ`.  For a subgroup that is not admissible the operators are defined to be
zero (the covariance of the metric needs determinant one); every statement about them carries the
hypothesis `Admissible Γ`.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.PolynomialFormConnection TernaryPoly.PolynomialFormGeometricEnergy
  TernaryPoly.PolynomialFormCoordinates
open TernaryPoly.SmoothLocalDeRham
open Set Filter
open scoped ContDiff Topology

variable {Γ : Subgroup RealGL} {n k l : ℕ}

theorem Admissible.det_sq (h : Admissible Γ) (γ : Γ) : (γ : RealGL).val.det ^ 2 = 1 := by
  rw [h.det_one γ.1 γ.2]
  norm_num

/-! ### Form-level linear maps -/

/-- The explicit local adjoint as a linear map of smooth forms on the positive coordinates. -/
def adjointForm (n k : ℕ) :
    Form (F := Coefficients n) positiveCoordinates (k + 1) →ₗ[ℝ]
      Form (F := Coefficients n) positiveCoordinates k where
  toFun w := restrictForm positiveCoordinates (localAdjoint n k (w : Coordinates → FormValue n (k + 1)))
    (contDiffOn_localAdjoint n k (Form.smooth w))
  map_add' w z := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, AddMemClass.coe_add, Pi.add_apply]
    exact localAdjoint_add n k (Form.smooth w) (Form.smooth z) hx
  map_smul' c w := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
    exact localAdjoint_smul n k c (Form.smooth w) hx

theorem adjointForm_apply (w : Form (F := Coefficients n) positiveCoordinates (k + 1))
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    (adjointForm n k w : Coordinates → FormValue n k) x =
      localAdjoint n k (w : Coordinates → FormValue n (k + 1)) x :=
  restrictForm_apply _ (contDiffOn_localAdjoint n k (Form.smooth w)) hx

/-- A smooth fiberwise linear operator as a linear map of smooth forms. -/
def zeroOrderForm (n k l : ℕ) (A : Coordinates → FormValue n k →L[ℝ] FormValue n l)
    (hA : ContDiffOn ℝ ∞ A positiveCoordinates) :
    Form (F := Coefficients n) positiveCoordinates k →ₗ[ℝ]
      Form (F := Coefficients n) positiveCoordinates l where
  toFun w := restrictForm positiveCoordinates (fun x => A x ((w : Coordinates → FormValue n k) x))
    (hA.clm_apply (Form.smooth w))
  map_add' w z := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, AddMemClass.coe_add, Pi.add_apply, map_add]
  map_smul' c w := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, SetLike.val_smul, Pi.smul_apply, map_smul,
      RingHom.id_apply]

theorem zeroOrderForm_apply (A : Coordinates → FormValue n k →L[ℝ] FormValue n l)
    (hA : ContDiffOn ℝ ∞ A positiveCoordinates)
    (w : Form (F := Coefficients n) positiveCoordinates k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    (zeroOrderForm n k l A hA w : Coordinates → FormValue n l) x =
      A x ((w : Coordinates → FormValue n k) x) :=
  restrictForm_apply _ (hA.clm_apply (Form.smooth w)) hx

/-! ### Equivariance and locality -/

theorem d_isEquivariant (w : Form (F := Coefficients n) positiveCoordinates k)
    (hw : IsEquivariant Γ n k (w : Coordinates → FormValue n k)) :
    IsEquivariant Γ n (k + 1)
      (SmoothLocalDeRham.d isOpen_positiveCoordinates k w : Coordinates → FormValue n (k + 1)) := by
  rw [isEquivariant_iff] at hw ⊢
  intro γ x hx
  have h1 := extDeriv_equivariantAt n k (γ : RealGL) (Form.smooth w)
    (fun y hy => hw γ y hy) hx
  exact h1.congr_of_eqOn hx (fun y hy => (SmoothLocalDeRham.d_apply _ w hy).symm)

theorem d_isLocal (w : Form (F := Coefficients n) positiveCoordinates k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) (he : (w : Coordinates → FormValue n k) =ᶠ[𝓝 x] 0) :
    (SmoothLocalDeRham.d isOpen_positiveCoordinates k w : Coordinates → FormValue n (k + 1)) x = 0 := by
  rw [SmoothLocalDeRham.d_apply _ w hx]
  exact extDeriv_eq_zero_of_notMem_tsupport n k _ (notMem_tsupport_iff_eventuallyEq.mpr he)

theorem adjointForm_isEquivariant (h : Admissible Γ)
    (w : Form (F := Coefficients n) positiveCoordinates (k + 1))
    (hw : IsEquivariant Γ n (k + 1) (w : Coordinates → FormValue n (k + 1))) :
    IsEquivariant Γ n k (adjointForm n k w : Coordinates → FormValue n k) := by
  rw [isEquivariant_iff] at hw ⊢
  intro γ x hx
  have h1 := localAdjoint_equivariantAt n k (γ : RealGL) (h.det_sq γ) (Form.smooth w)
    (fun y hy => hw γ y hy) hx
  exact h1.congr_of_eqOn hx (fun y hy => (adjointForm_apply w hy).symm)

theorem adjointForm_isLocal (w : Form (F := Coefficients n) positiveCoordinates (k + 1))
    {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (he : (w : Coordinates → FormValue n (k + 1)) =ᶠ[𝓝 x] 0) :
    (adjointForm n k w : Coordinates → FormValue n k) x = 0 := by
  rw [adjointForm_apply w hx, localAdjoint_congr n k he]
  simp

theorem zeroOrderForm_isEquivariant (A : Coordinates → FormValue n k →L[ℝ] FormValue n l)
    (hA : ContDiffOn ℝ ∞ A positiveCoordinates)
    (hcov : ∀ γ : Γ, IsActionOperator n k l (γ : RealGL) A)
    (w : Form (F := Coefficients n) positiveCoordinates k)
    (hw : IsEquivariant Γ n k (w : Coordinates → FormValue n k)) :
    IsEquivariant Γ n l (zeroOrderForm n k l A hA w : Coordinates → FormValue n l) := by
  rw [isEquivariant_iff] at hw ⊢
  intro γ x hx
  have h1 := (hcov γ).equivariantAt hx (hw γ x hx)
  exact h1.congr_of_eqOn hx (fun y hy => (zeroOrderForm_apply A hA w hy).symm)

theorem zeroOrderForm_isLocal (A : Coordinates → FormValue n k →L[ℝ] FormValue n l)
    (hA : ContDiffOn ℝ ∞ A positiveCoordinates)
    (w : Form (F := Coefficients n) positiveCoordinates k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) (he : (w : Coordinates → FormValue n k) =ᶠ[𝓝 x] 0) :
    (zeroOrderForm n k l A hA w : Coordinates → FormValue n l) x = 0 := by
  rw [zeroOrderForm_apply A hA w hx, he.eq_of_nhds, Pi.zero_apply,
    TernaryPoly.PolynomialFormCoordinates.clm_map_zero]

/-! ### The operators on `CForm` -/

open Classical in
/-- The exterior derivative on compactly supported equivariant forms. -/
def CForm.d (Γ : Subgroup RealGL) (n k : ℕ) : CForm Γ n k →ₗ[ℝ] CForm Γ n (k + 1) :=
  CForm.map (SmoothLocalDeRham.d isOpen_positiveCoordinates k) d_isEquivariant
    (fun w _ hx he => d_isLocal w hx he)

open Classical in
/-- The explicit local adjoint of the exterior derivative (zero for a non-admissible group). -/
def CForm.delta (Γ : Subgroup RealGL) (n k : ℕ) : CForm Γ n (k + 1) →ₗ[ℝ] CForm Γ n k :=
  if h : Admissible Γ then
    CForm.map (adjointForm n k) (adjointForm_isEquivariant h)
      (fun w _ hx he => adjointForm_isLocal w hx he)
  else 0

open Classical in
/-- The symmetric exterior operator `S⁺` (zero for a non-admissible group). -/
def CForm.symExt (Γ : Subgroup RealGL) (n k : ℕ) : CForm Γ n k →ₗ[ℝ] CForm Γ n (k + 1) :=
  if h : Admissible Γ then
    CForm.map (zeroOrderForm n k (k + 1) (symmetricExteriorCLM n k)
        (contDiffOn_symmetricExteriorCLM n k))
      (zeroOrderForm_isEquivariant _ _
        (fun γ => symmetricExteriorCLM_isActionOperator n k (γ : RealGL) (h.det_sq γ)))
      (fun w _ hx he => zeroOrderForm_isLocal _ _ w hx he)
  else 0

open Classical in
/-- The symmetric contraction operator `S⁻` (zero for a non-admissible group). -/
def CForm.symCon (Γ : Subgroup RealGL) (n k : ℕ) : CForm Γ n (k + 1) →ₗ[ℝ] CForm Γ n k :=
  if h : Admissible Γ then
    CForm.map (zeroOrderForm n (k + 1) k (symmetricContractionCLM n k)
        (contDiffOn_symmetricContractionCLM n k))
      (zeroOrderForm_isEquivariant _ _
        (fun γ => symmetricContractionCLM_isActionOperator n k (γ : RealGL) (h.det_sq γ)))
      (fun w _ hx he => zeroOrderForm_isLocal _ _ w hx he)
  else 0

/-! ### Pointwise formulas -/

theorem CForm.d_apply (w : CForm Γ n k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    CForm.fn (CForm.d Γ n k w) x = extDeriv (CForm.fn w) x :=
  SmoothLocalDeRham.d_apply _ _ hx

theorem CForm.delta_apply (h : Admissible Γ) (w : CForm Γ n (k + 1)) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    CForm.fn (CForm.delta Γ n k w) x = localAdjoint n k (CForm.fn w) x := by
  unfold CForm.delta
  rw [dite_eq_left h]
  exact adjointForm_apply _ hx

theorem CForm.symExt_apply (h : Admissible Γ) (w : CForm Γ n k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    CForm.fn (CForm.symExt Γ n k w) x = symmetricExterior n k x (CForm.fn w x) := by
  unfold CForm.symExt
  rw [dite_eq_left h]
  exact (zeroOrderForm_apply _ _ _ hx).trans (symmetricExteriorCLM_apply n k x _)

theorem CForm.symCon_apply (h : Admissible Γ) (w : CForm Γ n (k + 1)) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    CForm.fn (CForm.symCon Γ n k w) x = symmetricContraction n k x (CForm.fn w x) := by
  unfold CForm.symCon
  rw [dite_eq_left h]
  exact (zeroOrderForm_apply _ _ _ hx).trans (symmetricContractionCLM_apply n k x _)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
