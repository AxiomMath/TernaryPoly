module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Geometry
public import Mathlib.RepresentationTheory.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham
  SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The actual linear coefficient action, made continuous by finite dimension. -/
def coefficientMap (ρ : Representation ℝ DeckGroup F) (g : DeckGroup) : F →L[ℝ] F :=
  (ρ g).toContinuousLinearMap

@[simp] theorem coefficientMap_apply (ρ : Representation ℝ DeckGroup F) (g : DeckGroup) (v : F) :
    coefficientMap ρ g v = ρ g v := rfl

/-- Equivariance convention: the actual deck pullback equals the specified coefficient action.
In degree zero this is `w (g • x) = ρ(g) w(x)`. -/
def IsEquivariant (ρ : Representation ℝ DeckGroup F) (U : Set OrbitSpace) {n : ℕ}
    (w : RawForm Coordinates F n) : Prop :=
  ∀ (g : DeckGroup) (x : Coordinates), x ∈ liftedDomain U →
    pullRaw (deckMap g) w x = coefficientFormMap (coefficientMap ρ g) n (w x)

/-- Smooth local-coefficient sections over U, represented on its actual covering preimage. -/
def equivariantSubmodule (ρ : Representation ℝ DeckGroup F) (U : Set OrbitSpace) (n : ℕ) :
    Submodule ℝ (Form (F := F) (liftedDomain U) n) where
  carrier := {w | IsEquivariant ρ U (w : RawForm Coordinates F n)}
  zero_mem' := by intro g x hx; ext v; simp [pullRaw, coefficientFormMap]
  add_mem' := by
    intro w z hw hz g x hx
    ext v
    simpa [pullRaw, coefficientFormMap] using
      congrArg (fun z : Coordinates [⋀^Fin n]→L[ℝ] F => z v)
        (congrArg₂ (· + ·) (hw g x hx) (hz g x hx))
  smul_mem' := by
    intro c w hw g x hx
    ext v
    simpa [pullRaw, coefficientFormMap] using
      congrArg (fun z : Coordinates [⋀^Fin n]→L[ℝ] F => z v)
        (congrArg (c • ·) (hw g x hx))

abbrev EquivariantForm (ρ : Representation ℝ DeckGroup F) (U : Set OrbitSpace) (n : ℕ) :=
  equivariantSubmodule ρ U n

theorem equivariant_d (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace} (hU : IsOpen U)
    {n : ℕ} (w : Form (F := F) (liftedDomain U) n)
    (he : IsEquivariant ρ U (w : RawForm Coordinates F n)) :
    IsEquivariant ρ U (d (liftedDomain_isOpen hU) n w : RawForm Coordinates F (n + 1)) := by
  intro g x hx
  have hs := liftedDomain_isOpen hU
  have hg := deckMap_liftedDomain g U hx
  have hdiff : DifferentiableAt ℝ (w : RawForm Coordinates F n) x :=
    ((Form.smooth w x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hgdiff : DifferentiableAt ℝ (w : RawForm Coordinates F n) (deckMap g x) :=
    ((Form.smooth w _ hg).contDiffAt (hs.mem_nhds hg)).differentiableAt (by simp)
  have hge : pullRaw (deckMap g) (w : RawForm Coordinates F n) =ᶠ[𝓝 x]
      coefficientRaw (coefficientMap ρ g) (w : RawForm Coordinates F n) := by
    filter_upwards [hs.mem_nhds hx] with y hy using he g y hy
  change ((d hs n w : RawForm Coordinates F (n + 1)) (deckMap g x)).compContinuousLinearMap
    (fderiv ℝ (deckMap g) x) = coefficientFormMap (coefficientMap ρ g) (n + 1)
      ((d hs n w : RawForm Coordinates F (n + 1)) x)
  rw [d_apply hs w hg, d_apply hs w hx]
  change pullRaw (deckMap g) (extDeriv (w : RawForm Coordinates F n)) x = _
  rw [← extDeriv_pullRaw ((deckMap_smooth g x hx.1).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx.1)) hgdiff,
    hge.extDeriv_eq, extDeriv_coefficientRaw _ hdiff]

end TernaryPoly.SmoothCoveringDeRham
