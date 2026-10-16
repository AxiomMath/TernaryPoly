module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingPartitionSupport

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter Function SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology Manifold

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U V : Set OrbitSpace} {n : ℕ}

/-- A scalar cutoff that vanishes near the relative domain boundary makes the true zero
extension smooth on a larger covering preimage. -/
theorem weighted_extension_smooth (hU : IsOpen U) (hV : IsOpen V)
    (φ : OrbitSpace → ℝ) (hφ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ V)
    (hzero : ∀ q ∈ V, q ∉ U → φ =ᶠ[𝓝 q] 0) (w : EquivariantForm ρ U n) :
    ContDiffOn ℝ ∞ (fun x => liftScalar φ x • (w.val : RawForm Coordinates F n) x) (liftedDomain V) := by
  intro x hx
  by_cases hq : coordinateProjection x ∈ U
  · have hxU : x ∈ liftedDomain U := ⟨hx.1, hq⟩
    exact (((liftScalar_smooth hφ x hx).contDiffAt ((liftedDomain_isOpen hV).mem_nhds hx)).smul
      ((Form.smooth w.val x hxU).contDiffAt ((liftedDomain_isOpen hU).mem_nhds hxU))).contDiffWithinAt
  · have hp := coordinateProjection_continuousOn.continuousAt (isOpen_positiveCoordinates.mem_nhds hx.1)
    have he : (fun y => liftScalar φ y • (w.val : RawForm Coordinates F n) y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hp.eventually (hzero _ hx.2 hq)] with y hy
      change φ (coordinateProjection y) • _ = 0
      rw [hy]
      simp only [Pi.zero_apply, zero_smul]
    exact ((contDiffAt_const (c := (0 : Coordinates [⋀^Fin n]→L[ℝ] F))).congr_of_eventuallyEq he).contDiffWithinAt

/-- Actual scalar-weighted extension, linear in the equivariant form. -/
def weightedExtend (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (φ : OrbitSpace → ℝ) (hφ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ V)
    (hzero : ∀ q ∈ V, q ∉ U → φ =ᶠ[𝓝 q] 0) (n : ℕ) :
    EquivariantForm ρ U n →ₗ[ℝ] EquivariantForm ρ V n where
  toFun w := zeroExtendOfSmooth hUV (scalarMultiply ρ φ (hφ.mono hUV) n w)
    (weighted_extension_smooth hU hV φ hφ hzero w)
  map_add' w z := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    change liftScalar φ x • ((w.val : RawForm Coordinates F n) x + (z.val : RawForm Coordinates F n) x) =
      liftScalar φ x • (w.val : RawForm Coordinates F n) x + liftScalar φ x • (z.val : RawForm Coordinates F n) x
    exact smul_add _ _ _
  map_smul' c w := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    change liftScalar φ x • (c • (w.val : RawForm Coordinates F n) x) =
      c • (liftScalar φ x • (w.val : RawForm Coordinates F n) x)
    exact smul_comm _ _ _

@[simp] theorem weightedExtend_apply (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (φ : OrbitSpace → ℝ) (hφ : ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ φ V)
    (hzero : ∀ q ∈ V, q ∉ U → φ =ᶠ[𝓝 q] 0) (w : EquivariantForm ρ U n) (x : Coordinates) :
    ((weightedExtend hU hV hUV φ hφ hzero n w).val : RawForm Coordinates F n) x =
      liftScalar φ x • (w.val : RawForm Coordinates F n) x := rfl

end TernaryPoly.SmoothDeRhamGluing
