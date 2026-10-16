module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.LevelOneBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH1

@[expose] public section


/-!
# The parabolic cup pairing on `SL₂(ℤ)` with coefficients on which `-1` acts trivially

A's amalgam presentation (`ModularH1`) supplies the two inputs of `LevelOneBridge`:
cocycles are determined by their values at `S` and `U = S T` (`cocycle_ext`), and `w ↦ z_w`
(`boundaryCocycle`) gives, for every `w` fixed by `S² = -1`, a cocycle with `z_w S = 0`,
`z_w U = (U - 1) w`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.LevelOneInstance

open CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH1
open TripleModel LinearDuality CocycleBridge EpsilonSplit LevelOneBridge

variable (W : Rep.{0, 0, 0} ℂ Modular)

/-- A one-cocycle of Mathlib's convention is a crossed homomorphism in ours. -/
theorem isCocycle_of_cocycles₁ (z : groupCohomology.cocycles₁ W) :
    IsCocycle W.ρ (fun g => z g) := by
  intro g h
  have := (groupCohomology.mem_cocycles₁_iff _).mp z.property g h
  exact this.trans (add_comm _ _)

/-- Cocycles of `SL₂(ℤ)` are determined by their values at `S` and `U = S T`. -/
theorem generated (z z' : Modular → W) (hz : IsCocycle W.ρ z) (hz' : IsCocycle W.ρ z')
    (hS : z ModularGroup.S = z' ModularGroup.S)
    (hU : z (ModularGroup.S * ModularGroup.T) = z' (ModularGroup.S * ModularGroup.T)) :
    z = z' := by
  have mem : ∀ y : Modular → W, IsCocycle W.ρ y → y ∈ groupCohomology.cocycles₁ W := by
    intro y hy
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    rw [hy g h, add_comm]
  have := cocycle_ext W (z := ⟨z, mem z hz⟩) (z' := ⟨z', mem z' hz'⟩) hS hU
  exact congrArg (fun c : groupCohomology.cocycles₁ W => (c : Modular → W)) this

/-- The connecting cocycles `z_w`, when `-1` acts trivially. -/
theorem exb (hS2 : ∀ w, W.ρ (ModularGroup.S * ModularGroup.S) w = w) (w : W) :
    ∃ z : Modular → W, IsCocycle W.ρ z ∧ z ModularGroup.S = 0 ∧
      z (ModularGroup.S * ModularGroup.T) = (W.ρ (ModularGroup.S * ModularGroup.T) - 1) w := by
  have hw : W.ρ (ModularGroup.S ^ 2) w = w := by rw [pow_two]; exact hS2 w
  refine ⟨fun g => boundaryCocycle w hw g, isCocycle_of_cocycles₁ W (boundaryCocycle w hw),
    boundaryCocycle_S w hw, ?_⟩
  have := boundaryCocycle_U w hw
  change boundaryCocycle w hw (ModularGroup.S * ModularGroup.T) = _
  rw [LinearMap.sub_apply, Module.End.one_apply]
  exact this

variable (W' : Rep.{0, 0, 0} ℂ Modular) {B : W →ₗ[ℂ] W' →ₗ[ℂ] ℂ}

/-- **Poincaré duality for the parabolic cohomology of `SL₂(ℤ)`** (coefficients on which `-1` acts
trivially): a parabolic crossed homomorphism whose cup pairing with every crossed homomorphism
vanishes is a coboundary. -/
theorem left_nondegenerate [FiniteDimensional ℂ W] [FiniteDimensional ℂ W']
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (hinv : ∀ g v w, B (W.ρ g v) (W'.ρ g w) = B v w)
    (hS2' : ∀ w, W'.ρ (ModularGroup.S * ModularGroup.S) w = w)
    {z : Modular → W} (hz : IsCocycle W.ρ z) {v : W × W × W}
    (hv : IsPrimitive W.ρ ModularGroup.S ModularGroup.T⁻¹ z v)
    (zero : ∀ (z' : Modular → W') (v' : W' × W' × W'), IsCocycle W'.ρ z' →
      IsPrimitive W'.ρ ModularGroup.S ModularGroup.T⁻¹ z' v' →
      tripleForm B W'.ρ ModularGroup.S ModularGroup.T⁻¹ v v' = 0) :
    ∃ u : W, ∀ g, z g = W.ρ g u - u :=
  LevelOneBridge.left_nondegenerate W.ρ ModularGroup.S ModularGroup.T hL hR hinv (generated W)
    hS2' (exb W' hS2') hz hv zero

/-- The reflection-invariant version (`GL₂(ℤ)`; twisted coefficients). -/
theorem left_nondegenerate_reflect [FiniteDimensional ℂ W] [FiniteDimensional ℂ W']
    (hL : ∀ v, (∀ w, B v w = 0) → v = 0) (hR : ∀ w, (∀ v, B v w = 0) → w = 0)
    (hinv : ∀ g v w, B (W.ρ g v) (W'.ρ g w) = B v w)
    (D : ReflectData W.ρ W'.ρ B ModularGroup.S ModularGroup.T⁻¹ (-1 : ℂ))
    (hS2' : ∀ w, W'.ρ (ModularGroup.S * ModularGroup.S) w = w)
    {z : Modular → W} (hz : IsCocycle W.ρ z) {v : W × W × W}
    (hv : IsPrimitive W.ρ ModularGroup.S ModularGroup.T⁻¹ z v)
    (zinv : reflect D.σ D.e z = z)
    (zero : ∀ (z' : Modular → W') (v' : W' × W' × W'), IsCocycle W'.ρ z' →
      IsPrimitive W'.ρ ModularGroup.S ModularGroup.T⁻¹ z' v' → reflect D.σ D.e' z' = z' →
      cupFormula B W'.ρ ModularGroup.S ModularGroup.T⁻¹ z z' v = 0) :
    ∃ u : W, D.e u = u ∧ ∀ g, z g = W.ρ g u - u :=
  LevelOneBridge.left_nondegenerate_reflect W.ρ ModularGroup.S ModularGroup.T hL hR hinv D
    (generated W) hS2' (exb W' hS2') hz hv zinv zero

end TernaryPeriodPolynomials.BoundaryDuality.LevelOneInstance
