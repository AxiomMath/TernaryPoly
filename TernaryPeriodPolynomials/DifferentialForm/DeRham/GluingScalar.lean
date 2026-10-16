module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Consumer
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology Manifold

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace} {n : ℕ}

/-- Lift an actual scalar function on the quotient through the actual coordinate projection. -/
def liftScalar (φ : OrbitSpace → ℝ) : Coordinates → ℝ := φ ∘ coordinateProjection

theorem liftScalar_deck (φ : OrbitSpace → ℝ) (g : DeckGroup) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) : liftScalar φ (deckMap g x) = liftScalar φ x := by
  simp only [liftScalar, Function.comp_apply, coordinateProjection_deck g hx]

theorem liftScalar_smooth {φ : OrbitSpace → ℝ}
    (hφ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ U) :
    ContDiffOn ℝ ∞ (liftScalar φ) (liftedDomain U) := by
  have hp : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) ∞ coordinateProjection positiveCoordinates := by
    unfold SmoothCoveringDeRham.coordinateProjection
    simpa only [coordinateChart_target, Function.comp_def] using
      quotientProjection_contMDiff.comp_contMDiffOn coordinateChart_symm_contMDiffOn
  exact contMDiffOn_iff_contDiffOn.mp (hφ.comp (hp.mono inter_subset_left) (fun _ hx => hx.2))

/-- The exact wedge term in the scalar Leibniz rule, with Mathlib's exterior normalization. -/
def scalarWedge (α : Coordinates →L[ℝ] ℝ) (w : Coordinates [⋀^Fin n]→L[ℝ] F) :
    Coordinates [⋀^Fin (n + 1)]→L[ℝ] F := alternatizeUncurryFin (α.smulRight w)

omit [FiniteDimensional ℝ F] in
theorem extDeriv_scalar {φ : Coordinates → ℝ} {w : RawForm Coordinates F n} {x : Coordinates}
    (hφ : DifferentiableAt ℝ φ x) (hw : DifferentiableAt ℝ w x) :
    extDeriv (fun y => φ y • w y) x =
      scalarWedge (fderiv ℝ φ x) (w x) + φ x • extDeriv w x := by
  unfold extDeriv scalarWedge
  rw [fderiv_fun_smul hφ hw]
  change (alternatizeUncurryFinCLM ℝ Coordinates F (n := n)) (_ + _) = _
  rw [map_add, map_smul]
  exact add_comm _ _

/-- Pointwise multiplication of actual equivariant forms by smooth quotient scalars. -/
def scalarMultiply (φ : OrbitSpace → ℝ)
    (hφ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ U) (n : ℕ) :
    EquivariantForm ρ U n →ₗ[ℝ] EquivariantForm ρ U n where
  toFun w := ⟨⟨fun x => liftScalar φ x • (w.val : RawForm Coordinates F n) x,
    (liftScalar_smooth hφ).smul (Form.smooth w.val), by
      intro x hx
      dsimp only
      rw [Form.outside w.val hx, smul_zero]⟩, by
    intro g x hx
    have he := w.property g x hx
    ext v
    have hev := congrArg (fun z : Coordinates [⋀^Fin n]→L[ℝ] F => z v) he
    simpa [pullRaw, coefficientFormMap, liftScalar_deck φ g hx.1] using
      congrArg (liftScalar φ x • ·) hev⟩
  map_add' w z := by apply Subtype.ext; apply Form.ext; intro x hx; simp [smul_add]
  map_smul' c w := by apply Subtype.ext; apply Form.ext; intro x hx; simp [smul_smul, mul_comm]

@[simp] theorem scalarMultiply_apply (φ : OrbitSpace → ℝ)
    (hφ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ U) (w : EquivariantForm ρ U n)
    (x : Coordinates) :
    ((scalarMultiply ρ φ hφ n w).val : RawForm Coordinates F n) x =
      liftScalar φ x • (w.val : RawForm Coordinates F n) x := rfl

/-- Exact scalar Leibniz identity for the literal local-coefficient exterior differential. -/
theorem differential_scalarMultiply (hU : IsOpen U) (φ : OrbitSpace → ℝ)
    (hφ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ U)
    (w : EquivariantForm ρ U n) {x : Coordinates} (hx : x ∈ liftedDomain U) :
    ((differential ρ hU n (scalarMultiply ρ φ hφ n w)).val : RawForm Coordinates F (n + 1)) x =
      scalarWedge (fderiv ℝ (liftScalar φ) x) ((w.val : RawForm Coordinates F n) x) +
        liftScalar φ x • ((differential ρ hU n w).val : RawForm Coordinates F (n + 1)) x := by
  change (d (liftedDomain_isOpen hU) n (scalarMultiply ρ φ hφ n w).val : RawForm Coordinates F (n + 1)) x = _
  rw [d_apply (liftedDomain_isOpen hU) _ hx]
  change extDeriv (fun y => liftScalar φ y • (w.val : RawForm Coordinates F n) y) x = _
  rw [extDeriv_scalar (((liftScalar_smooth hφ x hx).contDiffAt
    ((liftedDomain_isOpen hU).mem_nhds hx)).differentiableAt (by simp))
    (((Form.smooth w.val x hx).contDiffAt ((liftedDomain_isOpen hU).mem_nhds hx)).differentiableAt (by simp))]
  rw [differential_coe, d_apply (liftedDomain_isOpen hU) _ hx]

end TernaryPoly.SmoothDeRhamGluing
