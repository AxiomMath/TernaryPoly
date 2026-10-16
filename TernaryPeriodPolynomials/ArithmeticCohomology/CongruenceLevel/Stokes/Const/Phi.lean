module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Decomp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CornerChain
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitStokes
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Stab
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.CoordRes

@[expose] public section


/-!
# The corner functional of the Stokes cycle on the flag orbits

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.GammaNFaceFactor
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.EquivariantSingularSmall
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

/-- The trivial rational coefficients. -/
abbrev Wq : Rep.{0} ℚ Γ6 := 𝟙_ (Rep.{0} ℚ Γ6)

/-- The flag cochains with trivial rational coefficients. -/
abbrev flagK : CochainComplex (ModuleCat.{0} ℚ) ℕ := homCochains (prodComplex Γ6 RationalGL3 Flag) Wq

/-- The corner chain `pA 3 Ω` of the Stokes cycle, a 3-chain of the flag complex. -/
def cornerX : (prodComplex Γ6 RationalGL3 Flag).X 3 := (modelPush.pA 3).hom stokesCycle

theorem cornerX_cycle : ∀ φ : (prodComplex Γ6 RationalGL3 Flag).X 2 ⟶ 𝟙_ (Rep.{0} ℚ Γ6),
    φ.hom ((prodComplex Γ6 RationalGL3 Flag).d 3 2 cornerX) = 0 :=
  fun φ => PushCone.corner_cycle modelPush stokesCycle_isCoinvCycle φ


/-- **The functionals `φ_o`**: the corner functional of the Stokes cycle on the cohomology of the flag complex, decomposed over the flag orbits. -/
def flagPhi : ∀ o : labelOrbits Γ6 Flag, groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype Wq) 3 →ₗ[ℚ] ℚ :=
  Classical.choose (corner_functional_decomp cornerX cornerX_cycle)

theorem flagPhi_spec (θ : flagK.X (2 + 1)) (hθ : (flagK.d (2 + 1) (2 + 1 + 1)).hom θ = 0) :
    θ.hom cornerX = ∑ o, flagPhi o (flagCoordPi Wq (clsS flagK θ hθ) o) :=
  Classical.choose_spec (corner_functional_decomp cornerX cornerX_cycle) θ hθ

/-- The line cochains with trivial rational coefficients. -/
abbrev lineK : CochainComplex (ModuleCat.{0} ℚ) ℕ := homCochains (prodComplex Γ6 RationalGL3 Line) Wq

/-- The plane cochains with trivial rational coefficients. -/
abbrev planeK : CochainComplex (ModuleCat.{0} ℚ) ℕ := homCochains (prodComplex Γ6 RationalGL3 Plane) Wq

theorem flagPhi_line_pullback (s : lineK.homology 3) :
    ∑ o, flagPhi o (flagCoordPi Wq ((HomologicalComplex.homologyMap (homPullback flagLineHom.hom Wq) 3).hom s) o) = 0 := by
  obtain ⟨σ, hσ, rfl⟩ := exists_clsS lineK s
  have hc := mapS_cocycle lineK (homPullback flagLineHom.hom Wq) σ hσ
  rw [clsS_map lineK (homPullback flagLineHom.hom Wq) σ hσ hc, ← flagPhi_spec _ hc]
  have hcl : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ σ = 0 := by
    have := hσ
    exact this
  exact PushCone.corner_line modelPush stokesCycle_isCoinvCycle σ hcl

theorem flagPhi_plane_pullback (s : planeK.homology 3) :
    ∑ o, flagPhi o (flagCoordPi Wq ((HomologicalComplex.homologyMap (homPullback flagPlaneHom.hom Wq) 3).hom s) o) = 0 := by
  obtain ⟨σ, hσ, rfl⟩ := exists_clsS planeK s
  have hc := mapS_cocycle planeK (homPullback flagPlaneHom.hom Wq) σ hσ
  rw [clsS_map planeK (homPullback flagPlaneHom.hom Wq) σ hσ hc, ← flagPhi_spec _ hc]
  have hcl : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ σ = 0 := by
    have := hσ
    exact this
  exact PushCone.corner_plane modelPush stokesCycle_isCoinvCycle σ hcl

end TernaryPeriodPolynomials.Argument.GammaNStokes
