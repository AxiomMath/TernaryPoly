module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Forms.Pull

@[expose] public section


/-! # General coercivity: smooth equivariant forms with compact support in the orbit space

`CForm Γ n k` is the space of smooth `Coefficients n`-valued `k`-forms on the positive coordinates
of `Space` that are `Γ`-equivariant for the literal real homogeneous action and whose closed
projected support in the actual orbit space `OrbitSpace Γ` is compact.  The compact support
condition is exactly the one of the covering de Rham complex
(`TernaryPoly.SmoothCoveringDeRham.quotientSupport`).

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.PolynomialFormMetric TernaryPoly.PolynomialFormConnection
open Set Filter
open scoped ContDiff Topology

/-! ### The coefficient representation and equivariance -/

/-- The coefficient representation of `Γ`: restriction of the real homogeneous action of
`GL₃(ℝ)` (substitution by the inverse matrix) on the degree-`n` homogeneous polynomials. -/
def coefficientRep (Γ : Subgroup RealGL) (n : ℕ) : Representation ℝ Γ (Coefficients n) :=
  (realHomogeneousAction n).comp Γ.subtype

/-- The continuous coefficient action of `g` is the literal real homogeneous action. -/
theorem realCoefficientMap_eq_action (n : ℕ) (g : RealGL) :
    realCoefficientMap n g = (realHomogeneousAction n g).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro p
  apply Subtype.ext
  change TernaryPoly.SL3PolynomialCoercivity.realSubstitute g.val⁻¹ p.val =
    TernaryPoly.SL3PolynomialCoercivity.realSubstitute (g⁻¹ : RealGL) p.val
  rw [Matrix.GeneralLinearGroup.coe_inv]

theorem coefficientRep_eq (Γ : Subgroup RealGL) (n : ℕ) (γ : Γ) :
    (coefficientRep Γ n γ).toContinuousLinearMap = realCoefficientMap n (γ : RealGL) :=
  (realCoefficientMap_eq_action n (γ : RealGL)).symm

/-- `Γ`-equivariance of a form on the positive coordinates: pulling `w` back along the coordinate
action of `γ` is the same as applying the coefficient action of `γ` to `w`. -/
def IsEquivariant (Γ : Subgroup RealGL) (n k : ℕ) (w : Coordinates → FormValue n k) : Prop :=
  ∀ (γ : Γ) (x : Coordinates), x ∈ positiveCoordinates →
    pullRaw (coordinateAction (γ : RealGL)) w x =
      coefficientFormMap (coefficientRep Γ n γ).toContinuousLinearMap k (w x)

variable {Γ : Subgroup RealGL} {n k : ℕ}

theorem isEquivariant_iff {w : Coordinates → FormValue n k} :
    IsEquivariant Γ n k w ↔
      ∀ γ : Γ, ∀ x ∈ positiveCoordinates, EquivariantAt n k (γ : RealGL) w x := by
  refine forall_congr' fun γ => forall_congr' fun x => forall_congr' fun hx => ?_
  have hr := coefficientRep_eq Γ n γ
  constructor
  · intro h'
    rw [hr] at h'
    exact h'
  · intro h
    show _ = coefficientFormMap (coefficientRep Γ n γ).toContinuousLinearMap k (w x)
    rw [hr]
    exact h

theorem EquivariantAt.congr_of_eqOn {g : RealGL} {w z : Coordinates → FormValue n k}
    {x : Coordinates} (hx : x ∈ positiveCoordinates) (h : EquivariantAt n k g w x)
    (hwz : EqOn w z positiveCoordinates) : EquivariantAt n k g z x := by
  unfold EquivariantAt at *
  rwa [← hwz hx, ← hwz (coordinateAction_mem g x hx)]

theorem isEquivariant_zero : IsEquivariant Γ n k 0 := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simp [pullRaw, coefficientFormMap]

theorem IsEquivariant.add {w z : Coordinates → FormValue n k} (hw : IsEquivariant Γ n k w)
    (hz : IsEquivariant Γ n k z) : IsEquivariant Γ n k (w + z) := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simpa [pullRaw, coefficientFormMap] using
    congrArg (fun z : Coordinates [⋀^Fin k]→L[ℝ] Coefficients n => z v)
      (congrArg₂ (· + ·) (hw g x hx) (hz g x hx))

theorem IsEquivariant.smul (c : ℝ) {w : Coordinates → FormValue n k}
    (hw : IsEquivariant Γ n k w) : IsEquivariant Γ n k (c • w) := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simpa [pullRaw, coefficientFormMap] using
    congrArg (fun z : Coordinates [⋀^Fin k]→L[ℝ] Coefficients n => z v)
      (congrArg (c • ·) (hw g x hx))

/-! ### Projected support in the orbit space -/

theorem continuous_chart_coordinates : Continuous (fun S : Space => coordinateChart S) :=
  continuous_subtype_val.comp chartHomeomorph.continuous

/-- The orbit-space projection in coordinates is continuous on the positive coordinates. -/
theorem continuousOn_coordProj : ContinuousOn (coordProj Γ) positiveCoordinates :=
  continuous_proj.comp_continuousOn (coordinateChart.continuousOn_symm.mono (by simp))

/-- Closed support in the actual orbit space: the closure of the projection of the nonzero set. -/
def projSupport (Γ : Subgroup RealGL) {M : Type*} [Zero M] (w : Coordinates → M) :
    Set (OrbitSpace Γ) :=
  closure (coordProj Γ '' Function.support w)

theorem projSupport_zero : projSupport Γ (0 : Coordinates → FormValue n k) = ∅ := by
  simp [projSupport]

theorem projSupport_add (w z : Coordinates → FormValue n k) :
    projSupport Γ (w + z) ⊆ projSupport Γ w ∪ projSupport Γ z := by
  unfold projSupport
  rw [← closure_union, ← image_union]
  exact closure_mono (image_mono (Function.support_add _ _))

theorem projSupport_smul (c : ℝ) (w : Coordinates → FormValue n k) :
    projSupport Γ (c • w) ⊆ projSupport Γ w := by
  unfold projSupport
  exact closure_mono (image_mono (Function.support_const_smul_subset c w))

/-- Away from the projected support a function vanishes on a neighbourhood. -/
theorem eventuallyEq_zero_of_notMem_projSupport {M : Type*} [Zero M] {w : Coordinates → M}
    {x : Coordinates} (hx : x ∈ positiveCoordinates) (hq : coordProj Γ x ∉ projSupport Γ w) :
    w =ᶠ[𝓝 x] 0 := by
  have hnear : ∀ᶠ y in 𝓝 x, coordProj Γ y ∉ closure (coordProj Γ '' Function.support w) :=
    (continuousOn_coordProj.continuousAt (isOpen_positiveCoordinates.mem_nhds hx)).eventually
      (isClosed_closure.isOpen_compl.mem_nhds hq)
  filter_upwards [hnear] with y hy
  by_contra hn
  exact hy (subset_closure ⟨y, hn, rfl⟩)

/-- A local operator does not enlarge the projected support. -/
theorem projSupport_mono_of_local {M N : Type*} [Zero M] [Zero N] {w : Coordinates → M}
    {z : Coordinates → N} (hz : ∀ x, x ∉ positiveCoordinates → z x = 0)
    (hloc : ∀ x ∈ positiveCoordinates, w =ᶠ[𝓝 x] 0 → z x = 0) :
    projSupport Γ z ⊆ projSupport Γ w := by
  unfold projSupport
  apply closure_minimal _ isClosed_closure
  rintro q ⟨x, hx, rfl⟩
  have hxp : x ∈ positiveCoordinates := by
    by_contra hn
    exact hx (hz x hn)
  by_contra hq
  exact hx (hloc x hxp (eventuallyEq_zero_of_notMem_projSupport hxp hq))

/-! ### The space of compactly supported equivariant forms -/

variable (Γ) (n k) in
/-- Smooth `Γ`-equivariant `Coefficients n`-valued `k`-forms on the positive coordinates whose
closed projected support in the actual orbit space `OrbitSpace Γ` is compact. -/
def CForm : Submodule ℝ (Form (F := Coefficients n) positiveCoordinates k) where
  carrier := {w | IsEquivariant Γ n k (w : Coordinates → FormValue n k) ∧
    IsCompact (projSupport Γ (w : Coordinates → FormValue n k))}
  zero_mem' := ⟨isEquivariant_zero, by simp [projSupport_zero]⟩
  add_mem' := by
    rintro w z ⟨hw, hwc⟩ ⟨hz, hzc⟩
    exact ⟨hw.add hz, (hwc.union hzc).of_isClosed_subset isClosed_closure (projSupport_add _ _)⟩
  smul_mem' := by
    rintro c w ⟨hw, hwc⟩
    exact ⟨hw.smul c, hwc.of_isClosed_subset isClosed_closure (projSupport_smul c _)⟩

/-- The underlying function on `Coordinates` of a compactly supported equivariant form. -/
abbrev CForm.fn (w : CForm Γ n k) : Coordinates → FormValue n k :=
  ((w : Form (F := Coefficients n) positiveCoordinates k) : RawForm Coordinates (Coefficients n) k)

theorem CForm.equivariant (w : CForm Γ n k) : IsEquivariant Γ n k (CForm.fn w) := w.2.1

theorem CForm.compact (w : CForm Γ n k) : IsCompact (projSupport Γ (CForm.fn w)) := w.2.2

theorem CForm.smooth (w : CForm Γ n k) : ContDiffOn ℝ ∞ (CForm.fn w) positiveCoordinates :=
  Form.smooth (w : Form (F := Coefficients n) positiveCoordinates k)

theorem CForm.outside (w : CForm Γ n k) {x : Coordinates} (hx : x ∉ positiveCoordinates) :
    CForm.fn w x = 0 :=
  Form.outside (w : Form (F := Coefficients n) positiveCoordinates k) hx

theorem CForm.equivariantAt (w : CForm Γ n k) (γ : Γ) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) : EquivariantAt n k (γ : RealGL) (CForm.fn w) x :=
  isEquivariant_iff.mp (CForm.equivariant w) γ x hx

@[ext] theorem CForm.ext {w z : CForm Γ n k}
    (h : ∀ x ∈ positiveCoordinates, CForm.fn w x = CForm.fn z x) : w = z :=
  Subtype.ext (Form.ext h)

@[simp] theorem CForm.fn_add (w z : CForm Γ n k) : CForm.fn (w + z) = CForm.fn w + CForm.fn z :=
  rfl

@[simp] theorem CForm.fn_smul (c : ℝ) (w : CForm Γ n k) : CForm.fn (c • w) = c • CForm.fn w :=
  rfl

@[simp] theorem CForm.fn_zero : CForm.fn (0 : CForm Γ n k) = 0 := rfl

/-- Build a linear map between spaces of compactly supported equivariant forms from a linear
map of smooth forms that preserves equivariance and is local. -/
def CForm.map {l : ℕ} (T : Form (F := Coefficients n) positiveCoordinates k →ₗ[ℝ]
      Form (F := Coefficients n) positiveCoordinates l)
    (hE : ∀ w : Form (F := Coefficients n) positiveCoordinates k,
      IsEquivariant Γ n k (w : Coordinates → FormValue n k) →
        IsEquivariant Γ n l (T w : Coordinates → FormValue n l))
    (hloc : ∀ (w : Form (F := Coefficients n) positiveCoordinates k) (x : Coordinates),
      x ∈ positiveCoordinates → (w : Coordinates → FormValue n k) =ᶠ[𝓝 x] 0 →
        (T w : Coordinates → FormValue n l) x = 0) :
    CForm Γ n k →ₗ[ℝ] CForm Γ n l where
  toFun w := ⟨T w, hE _ w.2.1, w.2.2.of_isClosed_subset isClosed_closure
    (projSupport_mono_of_local (fun _ hx => Form.outside (T w) hx) (hloc w))⟩
  map_add' _ _ := Subtype.ext (T.map_add _ _)
  map_smul' _ _ := Subtype.ext (T.map_smul _ _)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
