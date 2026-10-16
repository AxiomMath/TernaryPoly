module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDLiteralBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadOdd

@[expose] public section


/-!
# The bad-line face coefficient systems computed from the literal contragredient `E*`

Formalized by Claude Sonnet 5.5.

The level-three analogue of `FacePDLiteralBridge`: the bad line `L₀` over `Γ₁'(3)`.  `LiteralLevelThreeBridge` has the data of `LevelThreeBridge` for the literal dual `E*` (evaluation pairing
`E ⊗ E* → ℂ`); `LevelThreeBridge.toLiteral` transports every level-three bridge of the model dual along `Θ⁻¹` with the same modules, pairing, constant and coordinates
`Φ`, `Ψ ∘ (Θ⁻¹)_*`; `levelThreeBridgeBadLiteral` (`n` even, `M = M' = Sym^{n+1}`, `c = (n+1)!/3`) and `levelThreeBridgeBadOddLiteral` (`n` odd, `M = Sym^{n+1}`,
`M' = Sym^{n+1} ⊗ det⁻¹`, `c = -(n+1)!/3`) are the library's bridges for the literal dual.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.BoundaryDuality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.LiteralBridge

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L L₀)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.FiberParabolicL0 (LevelThreeBridge)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel crossedCocycles)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)

local notation "Tm" => TernaryPeriodPolynomials.BoundaryDuality.L2Matrices.T

section Bridge

variable {n : ℕ} {χ : RankOneCharacter}

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- **The level-three bridge for the literal contragredient.** -/
structure LiteralLevelThreeBridge (n : ℕ) (χ : RankOneCharacter)
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (θU : (Fin 2 → RationalGL3) → Module.Dual ℂ (HomogeneousPoly n)) {V' W' : Type}
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    (ρb : Representation ℂ binaryArithmeticLevel V') (ρb' : Representation ℂ binaryArithmeticLevel W')
    (B₂ : V' →ₗ[ℂ] W' →ₗ[ℂ] ℂ) (x : crossedCocycles ρb) (x' : crossedCocycles ρb') (c : ℂ) where
  levi : binaryArithmeticLevel →* RationalGL3
  Φ : ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] V'
  Ψ : ((Fin 2 → RationalGL3) → Module.Dual ℂ (HomogeneousPoly n)) →ₗ[ℂ] W'
  levi_T : levi (upper 1) = Tm
  levi_L : levi (lower 1) = L
  pairing : ∀ f g, UCocycle (rationalCoefficientComponent n χ) latL0.sub f →
    UCocycle (litRep n χ) latL0.sub g → kostant (evPairing n) latL0.σ f g = c * B₂ (Φ f) (Ψ g)
  alpha : ∀ γ, Φ (leviCocycle (rationalCoefficientComponent n χ) ωU (levi γ)⁻¹) = x.1 γ
  beta : ∀ γ, Ψ (leviCocycle (litRep n χ) θU (levi γ)⁻¹) = x'.1 γ
  equivΦ : ∀ γ f, UCocycle (rationalCoefficientComponent n χ) latL0.sub f →
    Φ (cochainRep (rationalCoefficientComponent n χ) (levi γ) f) = ρb γ (Φ f)
  equivΨ : ∀ γ g, UCocycle (litRep n χ) latL0.sub g →
    Ψ (cochainRep (litRep n χ) (levi γ) g) = ρb' γ (Ψ g)

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- **Transport of a level-three bridge to the literal contragredient** (same modules, pairing, constant, Levi embedding, `Φ`; the coordinate `Ψ ∘ (Θ⁻¹)_*`). -/
def LevelThreeBridge.toLiteral {ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    {V' W' : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρb : Representation ℂ binaryArithmeticLevel V'} {ρb' : Representation ℂ binaryArithmeticLevel W'}
    {B₂ : V' →ₗ[ℂ] W' →ₗ[ℂ] ℂ} {x : crossedCocycles ρb} {x' : crossedCocycles ρb'} {c : ℂ}
    (Br : LevelThreeBridge (dualityData n χ) ωU θU ρb ρb' B₂ x x' c) :
    LiteralLevelThreeBridge n χ ωU (comp1 (thetaModelEquiv n).toLinearMap θU) ρb ρb' B₂ x x' c where
  levi := Br.levi
  Φ := Br.Φ
  Ψ := Br.Ψ.comp (comp1L (thetaModelEquiv n).symm.toLinearMap)
  levi_T := Br.levi_T
  levi_L := Br.levi_L
  pairing f g hf hg := by
    rw [kostant_literal_comp' n latL0.σ f g]
    exact Br.pairing f _ hf (uCocycle_comp (thetaModelEquiv n).symm.toLinearMap
      (fun h w => thetaInv_equivariant n χ h w) hg)
  alpha := Br.alpha
  beta γ := by
    have h := Br.beta γ
    rw [← h]
    change Br.Ψ (comp1 (thetaModelEquiv n).symm.toLinearMap
      (leviCocycle (litRep n χ) (comp1 (thetaModelEquiv n).toLinearMap θU) (Br.levi γ)⁻¹)) = _
    rw [leviCocycle_comp (thetaModelEquiv n).toLinearMap (fun h w => theta_equivariant n χ h w)]
    have e : comp1 (thetaModelEquiv n).symm.toLinearMap
        (comp1 (thetaModelEquiv n).toLinearMap (leviCocycle (dualRep (dualityData n χ)) θU (Br.levi γ)⁻¹)) =
        leviCocycle (dualRep (dualityData n χ)) θU (Br.levi γ)⁻¹ := by
      funext y
      exact (thetaModelEquiv n).symm_apply_apply _
    rw [e]
  equivΦ := Br.equivΦ
  equivΨ γ g hg := by
    change Br.Ψ (comp1 (thetaModelEquiv n).symm.toLinearMap (cochainRep (litRep n χ) (Br.levi γ) g)) = _
    rw [← cochainRep_comp (thetaModelEquiv n).symm.toLinearMap (fun h w => thetaInv_equivariant n χ h w)]
    exact Br.equivΨ γ _ (uCocycle_comp (thetaModelEquiv n).symm.toLinearMap
      (fun h w => thetaInv_equivariant n χ h w) hg)

end Bridge

section Instances

variable {n : ℕ} {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **The level-three bridge at the bad line for the literal dual, `n` even** (trivial character): `M = M' = Sym^{n+1}`, constant `(n+1)!/3`. -/
def levelThreeBridgeBadLiteral (positive : 0 < n) (heven : Even n)
    (hF : FiberHyp (rationalCoefficientComponent n trivialCharacter)
      (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
      (levelStabilizer L₀) Λe latL0.sub ζ η ω ωU θU) :=
  LevelThreeBridge.toLiteral (levelThreeBridgeBad positive heven hF)

/-- **The level-three bridge at the bad line for the literal dual, `n` odd** (trivial character): `M = Sym^{n+1}`, `M' = Sym^{n+1} ⊗ det⁻¹`, constant `-(n+1)!/3`. -/
def levelThreeBridgeBadOddLiteral (hodd : Odd n)
    (hF : FiberHyp (rationalCoefficientComponent n trivialCharacter)
      (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
      (levelStabilizer L₀) Λe latL0.sub ζ η ω ωU θU) :=
  LevelThreeBridge.toLiteral (levelThreeBridgeBadOdd hodd hF)

end Instances

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.LiteralBridge
