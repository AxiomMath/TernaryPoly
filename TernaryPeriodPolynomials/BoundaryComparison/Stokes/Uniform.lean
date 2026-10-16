module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MixedEdge

@[expose] public section


/-!
# The literal Stokes lemma at `Γ(N)`: uniform constants of the face factorisation

Formalized by Claude Sonnet 5.5.

`FaceFactorisation6U`: the constants of (a′) are UNIFORM, `lineFacePairM = c · can6` on every line face and `planeFacePairM = -c · can6P` on every plane face of `Γ(6)`, with one nonzero `c`.
The relative sign `-1` is the relative orientation of the two kinds of faces in the cone differential `d(α, β, u) = (dα, dβ, α|_{F_B} - β|_{F_B} - du)` (plane `+`, line `-`); with it the Stokes identity of the cone
becomes `∑_P can6P = ∑_Q can6` and the paper's `⟨ , ⟩_P + ⟨ , ⟩_Q = 0` holds for the oriented pairing `⟨ , ⟩_Q = -∑ can6`.  `FaceFactorisation6U.toFF6` shows it implies the per-face form `FaceFactorisation6`.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4

/-- **Uniform factorisation of the `Γ(6)` cone pairings through the canonical pairings**, with the relative orientation sign `-1` of the plane faces. -/
def FaceFactorisation6U : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (gammaN 6) V),
      (∀ (i : LineFaces 6) (x : lineMixedSub ρ i) (y : lineMixedSub ρ.dual i),
        lineFacePairM ρ i x.1 y.1 = c * can6 ρ i x y) ∧
      (∀ (i : PlaneFaces 6) (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i),
        planeFacePairM ρ i x.1 y.1 = -c * can6P ρ i x y)

theorem FaceFactorisation6U.toFF6 (h : FaceFactorisation6U) : FaceFactorisation6 := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨fun _ => c, fun _ => -c, fun _ => hc, fun _ => neg_ne_zero.mpr hc, fun V _ _ _ _ _ ρ => h V ρ⟩

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
