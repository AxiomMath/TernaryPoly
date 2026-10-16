module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Phi
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Glue
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceEvaluation
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.CornerCycle

@[expose] public section


/-!
# The corner functional of the Stokes cycle is not zero

Formalized by Claude Sonnet 5.5.

The level trace of the boundary is nonzero on a closed edge three-cochain (`exists_closed_levelTrace_ne_zero`) and is `c₀ ≠ 0` times the evaluation on the corner chain of the Stokes cycle
(`GeoData`).  Hence the evaluation of the corner chain `pA 3 Ω` on some closed flag three-cocycle with rational coefficients is nonzero, so some `flagPhi o` is nonzero.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFaceFactor
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

/-- **The corner chain of the Stokes cycle evaluates nontrivially on a closed flag three-cocycle.** -/
theorem exists_cocycle_corner_ne_zero :
    ∃ (θ : flagK.X (2 + 1)) (_ : (flagK.d (2 + 1) (2 + 1 + 1)).hom θ = 0), θ.hom cornerX ≠ 0 := by
  obtain ⟨f₀, hf₀⟩ := exists_closed_levelTrace_ne_zero
  obtain ⟨Ψ, κ, c₀, -, -, -, -, hc₀, -, htr⟩ := stokesCycle_geoData
  have hev : evalOmega (cornerChain stokesCycle) f₀.1 ≠ 0 := fun h => hf₀ (by rw [htr f₀, h, mul_zero])
  obtain ⟨r, hr⟩ : ∃ r : ℂ →ₗ[ℚ] ℚ, r (evalOmega (cornerChain stokesCycle) f₀.1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hev (eq_zero_of_forall_rat_functional hcon)
  let f6 : closedEdgeCochains N6 := ⟨f₀.1, closedEdgeCochains_mono N6_le_rationalLevel f₀.2⟩
  let θ : resFlag.complex.X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6) := edgeHom f6 ≫ rHom r
  have hval : ∀ (x : Fin 4 → RationalGL3) (ε : Flag),
      θ.hom (MonoidAlgebra.single (x, ε) 1) = r (f₀.1 x (psiEdge.symm ε)) :=
    fun x ε => congrArg r (toHom_val psiEdge psiEdge_smul 3 _ x ε)
  have h := FacePairingFull.Glue.hom_eq_evalOmega_r θ r f₀.1 hval stokesCycle
  refine ⟨θ, ?_, ?_⟩
  · change (prodComplex Γ6 RationalGL3 Flag).d (2 + 1 + 1) (2 + 1) ≫ θ = 0
    rw [show θ = edgeHom f6 ≫ rHom r from rfl, ← Category.assoc, edgeHom_closed f6, zero_comp]
  · intro hz
    apply hr
    rw [← h]
    exact hz

/-- Some functional `flagPhi o` is nonzero. -/
theorem exists_flagPhi_ne_zero : ∃ o, flagPhi o ≠ 0 := by
  obtain ⟨θ, hθ, hne⟩ := exists_cocycle_corner_ne_zero
  by_contra hcon
  push Not at hcon
  apply hne
  rw [flagPhi_spec θ hθ]
  exact Finset.sum_eq_zero fun o _ => by rw [hcon o]; rfl

end TernaryPeriodPolynomials.Argument.GammaNStokes
