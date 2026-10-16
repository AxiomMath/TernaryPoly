module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitStokes

@[expose] public section


/-!
# The Stokes cycle is the cycle of the line and plane glue

Formalized by Claude Sonnet 5.5.

`stokesCycle` (`OrbitStokes`) is the cycle of `exists_pairGeo`, and `stokesCycle_geoData` retains its comparison data.  Consequently:

* `stokesCycle_glue`: with the same `Ψ`, `κ`, `c₀`, the line glue `LineGlue Ψ (κ c₀)` and the plane glue `PlaneGlue Ψ (-(κ c₀))` of the face pairings hold, and the cone pairing at `stokesCycle` of
  cone cocycles pulling back along `Ψ` to boundary cocycles is `κ` times their geometric pairing (`PairGeo`);
* `conePairC_geo`: for any complex coefficient module and its literal complex dual, `r` of the complex cone pairing at `stokesCycle` of two cone cocycles `X`, `Y` is `κ` times the geometric
  pairing of any boundary cocycles pulling back to `X` and to `Y ≫ dualEmb r`.  In particular the cone pairing of the lifts of mixed classes is the geometric pairing of their boundary classes,
  independently of the choice of the lifts.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.SingularLocalDuality (dualRepresentation dualValue)
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open GeneralEisenstein
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains ambient)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.CoinvScalar
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

/-- **The Stokes cycle is the cycle of the line and plane glue.** -/
theorem stokesCycle_glue : ∃ (Ψ : coneR ⟶ boundaryChains) (κ : ℚ) (c₀ : ℂ), IsCarriedPsi Ψ ∧ QuasiIso Ψ ∧
    Ψ ≫ augB = augR ∧ κ ≠ 0 ∧ c₀ ≠ 0 ∧ PairGeo Ψ stokesCycle κ ∧
    LineGlue Ψ ((κ : ℂ) * c₀) ∧ PlaneGlue Ψ (-((κ : ℂ) * c₀)) := by
  obtain ⟨Ψ, κ, c₀, hcar, hq, haug, hκ, hc₀, pg, htr⟩ := stokesCycle_geoData
  exact ⟨Ψ, κ, c₀, hcar, hq, haug, hκ, hc₀, pg, glue_of_pairGeo stokesCycle_isCoinvCycle hq hκ hc₀ pg htr⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  {G : Type} [Group G] (ι : Γ6 →* G) (ρ : Representation ℂ G V)

/-- **The complex cone pairing at the Stokes cycle is the geometric pairing of the boundary classes.** -/
theorem conePairC_geo : ∃ (Ψ : coneR ⟶ boundaryChains) (κ : ℚ), κ ≠ 0 ∧ QuasiIso Ψ ∧ Ψ ≫ augB = augR ∧
    ∀ (X : coneR.X 2 ⟶ qRep ι ρ) (_ : coneR.d 3 2 ≫ X = 0)
      (Y : coneR.X 2 ⟶ qRep ι ρ.dual) (_ : coneR.d 3 2 ≫ Y = 0) (r : ℂ →ₗ[ℚ] ℚ),
      (∃ (β : boundaryChains.X 2 ⟶ qRep ι ρ) (_ : boundaryChains.d (2 + 1) 2 ≫ β = 0)
          (α : boundaryChains.X 2 ⟶ dualRepresentation (qRep ι ρ)) (_ : boundaryChains.d (2 + 1) 2 ≫ α = 0),
        PullsBackTo Ψ β X ∧ PullsBackTo Ψ α (Y ≫ dualEmb ι ρ r)) ∧
      ∀ (β : boundaryChains.X 2 ⟶ qRep ι ρ) (hβ : boundaryChains.d (2 + 1) 2 ≫ β = 0)
        (α : boundaryChains.X 2 ⟶ dualRepresentation (qRep ι ρ)) (hα : boundaryChains.d (2 + 1) 2 ≫ α = 0),
        PullsBackTo Ψ β X → PullsBackTo Ψ α (Y ≫ dualEmb ι ρ r) →
        r (conePairC (evalC ι ρ) stokesCycle X Y) = κ * geoOf (qRep ι ρ) α hα β hβ := by
  obtain ⟨Ψ, κ, c₀, hcar, hq, haug, hκ, hc₀, pg, htr⟩ := stokesCycle_geoData
  refine ⟨Ψ, κ, hκ, hq, haug, fun X hX Y hY r => ?_⟩
  have hA : coneR.d 3 2 ≫ Y ≫ dualEmb ι ρ r = 0 := by
    rw [← Category.assoc, hY, zero_comp]
  refine ⟨?_, fun β hβ α hα hPB hPA => ?_⟩
  · obtain ⟨β, hβ, hPB⟩ := exists_pullsBackTo hq _ hX
    obtain ⟨α, hα, hPA⟩ := exists_pullsBackTo hq _ hA
    exact ⟨β, hβ, α, hα, hPB, hPA⟩
  · have h := pg X (Y ≫ dualEmb ι ρ r) β hβ α hα hA hPB hPA
    rw [← conePair_dualEmb]
    exact h

end TernaryPeriodPolynomials.Argument.GammaNStokes
