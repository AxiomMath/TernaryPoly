module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualForms

@[expose] public section


/-!
# General coercivity, dual coefficients: the space of dual forms and the Cartan isomorphism

`DForm Γ n k` consists of smooth `Γ`-equivariant `Coefficients n`-valued `k`-forms on the positive
coordinates, equivariant for the dual representation `ρ ∘ θ`, with compact closed projected support in
the orbit space `OrbitSpace Γ`.  The Cartan pullback `ioPull` identifies `DForm Γ n k` with the space
`CForm (θΓ) n k` of standard forms of the Cartan image `θΓ = Γ.map thetaHom`.

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

/-- The dual coefficient representation of `Γ`: the standard representation composed with the Cartan
involution `g ↦ (g⁻¹)ᵀ`. -/
def dualRep (Γ : Subgroup RealGL) (n : ℕ) : Representation ℝ Γ (Coefficients n) :=
  (realHomogeneousAction n).comp (thetaHom.comp Γ.subtype)

/-- Equivariance of a form for a given coefficient representation. -/
def IsRepEquivariant (Γ : Subgroup RealGL) (n : ℕ) (ρ : Representation ℝ Γ (Coefficients n))
    (k : ℕ) (w : Coordinates → FormValue n k) : Prop :=
  ∀ (γ : Γ) (x : Coordinates), x ∈ positiveCoordinates →
    pullRaw (coordinateAction (γ : RealGL)) w x =
      coefficientFormMap (ρ γ).toContinuousLinearMap k (w x)

variable {Γ : Subgroup RealGL} {n k : ℕ}

theorem IsRepEquivariant.zero (ρ : Representation ℝ Γ (Coefficients n)) :
    IsRepEquivariant Γ n ρ k 0 := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simp [pullRaw, coefficientFormMap]

theorem IsRepEquivariant.add {ρ : Representation ℝ Γ (Coefficients n)}
    {w z : Coordinates → FormValue n k} (hw : IsRepEquivariant Γ n ρ k w)
    (hz : IsRepEquivariant Γ n ρ k z) : IsRepEquivariant Γ n ρ k (w + z) := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simpa [pullRaw, coefficientFormMap] using
    congrArg (fun z : Coordinates [⋀^Fin k]→L[ℝ] Coefficients n => z v)
      (congrArg₂ (· + ·) (hw g x hx) (hz g x hx))

theorem IsRepEquivariant.smul {ρ : Representation ℝ Γ (Coefficients n)} (c : ℝ)
    {w : Coordinates → FormValue n k} (hw : IsRepEquivariant Γ n ρ k w) :
    IsRepEquivariant Γ n ρ k (c • w) := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simpa [pullRaw, coefficientFormMap] using
    congrArg (fun z : Coordinates [⋀^Fin k]→L[ℝ] Coefficients n => z v)
      (congrArg (c • ·) (hw g x hx))

variable (Γ n k) in
/-- Smooth `Γ`-equivariant forms with values in the dual coefficient bundle, with compact closed
projected support in the orbit space. -/
def DForm : Submodule ℝ (Form (F := Coefficients n) positiveCoordinates k) where
  carrier := {w | IsRepEquivariant Γ n (dualRep Γ n) k (w : Coordinates → FormValue n k) ∧
    IsCompact (projSupport Γ (w : Coordinates → FormValue n k))}
  zero_mem' := ⟨IsRepEquivariant.zero _, by simp [projSupport_zero]⟩
  add_mem' := by
    rintro w z ⟨hw, hwc⟩ ⟨hz, hzc⟩
    exact ⟨hw.add hz, (hwc.union hzc).of_isClosed_subset isClosed_closure (projSupport_add _ _)⟩
  smul_mem' := by
    rintro c w ⟨hw, hwc⟩
    exact ⟨hw.smul c, hwc.of_isClosed_subset isClosed_closure (projSupport_smul c _)⟩

/-- The underlying function of a dual form. -/
abbrev DForm.fn (w : DForm Γ n k) : Coordinates → FormValue n k :=
  ((w : Form (F := Coefficients n) positiveCoordinates k) : RawForm Coordinates (Coefficients n) k)

theorem DForm.equivariant (w : DForm Γ n k) :
    IsRepEquivariant Γ n (dualRep Γ n) k (DForm.fn w) := w.2.1

theorem DForm.compact (w : DForm Γ n k) : IsCompact (projSupport Γ (DForm.fn w)) := w.2.2

theorem DForm.smooth (w : DForm Γ n k) : ContDiffOn ℝ ∞ (DForm.fn w) positiveCoordinates :=
  Form.smooth (w : Form (F := Coefficients n) positiveCoordinates k)

theorem DForm.outside (w : DForm Γ n k) {x : Coordinates} (hx : x ∉ positiveCoordinates) :
    DForm.fn w x = 0 :=
  Form.outside (w : Form (F := Coefficients n) positiveCoordinates k) hx

@[ext] theorem DForm.ext {w z : DForm Γ n k}
    (h : ∀ x ∈ positiveCoordinates, DForm.fn w x = DForm.fn z x) : w = z :=
  Subtype.ext (Form.ext h)

/-! ### Equivariance under the Cartan pullback -/

/-- The Cartan image of `Γ`. -/
abbrev thetaImage (Γ : Subgroup RealGL) : Subgroup RealGL := Γ.map thetaHom

theorem isRepEquivariant_ioPull_dual {w : Coordinates → FormValue n k}
    (hw : IsEquivariant (thetaImage Γ) n k w) :
    IsRepEquivariant Γ n (dualRep Γ n) k (ioPull n k w) := by
  intro γ x hx
  have hw' : pullRaw (coordinateAction (thetaHom (γ : RealGL))) w (iotaC x) =
      coefficientFormMap (dualRep Γ n γ).toContinuousLinearMap k (w (iotaC x)) :=
    hw ⟨thetaHom (γ : RealGL), γ, γ.2, rfl⟩ (iotaC x) (iotaC_mem hx)
  rw [pullRaw_ioPull n k (γ : RealGL) w hx, hw', coefficientFormMap_compCLM,
    ioPull_apply n k w hx]

theorem isEquivariant_ioPull_std {v : Coordinates → FormValue n k}
    (hv : IsRepEquivariant Γ n (dualRep Γ n) k v) :
    IsEquivariant (thetaImage Γ) n k (ioPull n k v) := by
  rintro ⟨_, γ, hγ, rfl⟩ x hx
  have hv' : pullRaw (coordinateAction γ) v (iotaC x) =
      coefficientFormMap (dualRep Γ n ⟨γ, hγ⟩).toContinuousLinearMap k (v (iotaC x)) :=
    hv ⟨γ, hγ⟩ (iotaC x) (iotaC_mem hx)
  change pullRaw (coordinateAction (thetaHom γ)) (ioPull n k v) x =
    coefficientFormMap (realHomogeneousAction n (thetaHom γ)).toContinuousLinearMap k
      (ioPull n k v x)
  rw [pullRaw_ioPull n k (thetaHom γ) v hx, thetaHom_thetaHom, hv', coefficientFormMap_compCLM,
    ioPull_apply n k v hx]
  rfl

/-! ### Projected supports under the Cartan pullback -/

/-- The map of orbit spaces induced by the Cartan involution. -/
def quotIota (A B : Subgroup RealGL) (h : ∀ a ∈ A, thetaHom a ∈ B) : OrbitSpace A → OrbitSpace B :=
  Quotient.map (sa := MulAction.orbitRel A Space) (sb := MulAction.orbitRel B Space) iota
    (fun S T hST => by
      obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.mp hST
      refine MulAction.orbitRel_apply.mpr ⟨⟨thetaHom (a : RealGL), h a a.2⟩, ?_⟩
      rw [← ha]
      exact (iota_act (a : RealGL) T).symm)

theorem quotIota_proj (A B : Subgroup RealGL) (h : ∀ a ∈ A, thetaHom a ∈ B) (S : Space) :
    quotIota A B h (proj A S) = proj B (iota S) := rfl

theorem continuous_quotIota (A B : Subgroup RealGL) (h : ∀ a ∈ A, thetaHom a ∈ B) :
    Continuous (quotIota A B h) :=
  Continuous.quotient_map' (s := MulAction.orbitRel A Space) (t := MulAction.orbitRel B Space)
    continuous_iota _

theorem quotIota_coordProj (A B : Subgroup RealGL) (h : ∀ a ∈ A, thetaHom a ∈ B) {y : Coordinates}
    (hy : y ∈ positiveCoordinates) : quotIota A B h (coordProj A y) = coordProj B (iotaC y) := by
  obtain ⟨S, rfl⟩ : ∃ S : Space, y = coordinateChart S :=
    ⟨coordinateChart.symm y, (coordinateChart.right_inv (by simpa using hy)).symm⟩
  rw [coordProj_chart, iotaC_chart, coordProj_chart]
  rfl

theorem ioPull_support_subset (A B : Subgroup RealGL) (h : ∀ a ∈ A, thetaHom a ∈ B)
    (w : Coordinates → FormValue n k) :
    coordProj B '' Function.support (ioPull n k w) ⊆
      quotIota A B h '' (coordProj A '' Function.support w) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxp : x ∈ positiveCoordinates := by
    by_contra hn
    exact hx (ioPull_of_notMem n k w hn)
  have hw : w (iotaC x) ≠ 0 := by
    intro h0
    apply hx
    rw [ioPull_apply n k w hxp, h0]
    ext v
    simp
  refine ⟨coordProj A (iotaC x), ⟨iotaC x, hw, rfl⟩, ?_⟩
  rw [quotIota_coordProj A B h (iotaC_mem hxp), iotaC_iotaC hxp]

theorem isCompact_projSupport_ioPull (A B : Subgroup RealGL) (h : ∀ a ∈ A, thetaHom a ∈ B)
    [T2Space (OrbitSpace B)] {w : Coordinates → FormValue n k}
    (hw : IsCompact (projSupport A w)) : IsCompact (projSupport B (ioPull n k w)) := by
  have hc : IsCompact (quotIota A B h '' projSupport A w) := hw.image (continuous_quotIota A B h)
  refine hc.of_isClosed_subset isClosed_closure ?_
  apply closure_minimal _ hc.isClosed
  refine (ioPull_support_subset A B h w).trans ?_
  exact image_mono (subset_closure)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
