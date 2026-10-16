module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.T3Chain
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Top
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.PHLevi
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.EdgeGen
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.TreeInstance

@[expose] public section


/-!
# Lemma B.1: the data of the tree maps from the oriented cell resolution

Formalized by Claude Sonnet 5.5.

`TreeData` is the bundle of hypotheses of `faceEvalAvg_of_tree` (`FaceMain`): a one-dimensional `P_H/U`-module `L`, the
`P_H/U`-equivariant maps `t₃ : L ⊗ Res P1 → Φ(RG₃)`, `t₂ : L ⊗ Res P0 → Φ(RG₂)` (`Φ` = `U`-coinvariants) compatible with the
Farey boundary (`hi`, `hii`), the non-vanishing `h3` of `t₂(ℓ₀ ⊗ s₀)` modulo the boundaries, and the normalization `ht3` that
`t₃(ℓ₀ ⊗ edgeGen)` is the class of the generator of the oriented cell `T₀`.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.HochschildSerre
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames

/-- The data of the tree maps (`F3`): a one-dimensional `P_H/U`-module `L` and the equivariant maps `t₃, t₂` from
the oriented cell resolution, with the standard normalization. -/
structure TreeData where
  L : Rep.{0} ℚ (PH ⧸ U)
  ℓ₀ : L.V
  hℓ : ℓ₀ ≠ 0
  hL : Module.finrank ℚ L.V = 1
  t3 : L ⊗ Rep.res pibar P1 ⟶ (Phi U).obj ((RG_projRes PH).complex.X 3)
  t2 : L ⊗ Rep.res pibar P0 ⟶ (Phi U).obj ((RG_projRes PH).complex.X 2)
  hi : t3 ≫ (Phi U).map ((RG_projRes PH).complex.d 3 2) = (L ◁ Rep.resMap pibar d1) ≫ t2
  hii : t2 ≫ (Phi U).map ((RG_projRes PH).complex.d 2 1) = 0
  h3 : t2.hom (ℓ₀ ⊗ₜ[ℚ] sZero (Rep.res pibar P1) (Rep.res pibar P0) (Rep.resMap pibar d1) (epsQ pibar)
      (resD1_epsQ pibar) (sesQ_shortExact pibar)) ∉
    LinearMap.range ((Phi U).map ((RG_projRes PH).complex.d 3 2)).hom.toLinearMap
  ht3 : t3.hom (ℓ₀ ⊗ₜ[ℚ] edgeGen) = Coinvariants.mk (((RG_projRes PH).complex.X 3).ρ.comp U.subtype) genT0

end TernaryPeriodPolynomials.Argument.AppendixBResidue
