module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.QDiAlignInst
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel

@[expose] public section


/-!
# `𝒞_Q(E^∨)` is exactly the group of mixed classes of the literal dual

Formalized by Claude Sonnet 5.5.

`toLiteral_mem_lineMixedAt`: for `η ∈ 𝒞_Q(E^∨)` the literal class `toLiteral η` lies in `lineMixedAt N h (dualRepG (lineFaceRep N h n))`; conversely (`exists_dualCuspidal_of_mixed`) every mixed
class of the literal dual is `toLiteral η` for an `η ∈ 𝒞_Q(E^∨)` (the `cuspEdge_bijective`).
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4

section DualMixed

variable (N n : ℕ) [NeZero N] (h : SL(3, ℤ))

/-- `toLiteral`, with target typed as the cohomology of `dualRepG (lineFaceRep N h n)`. -/
def toLitG : groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))) →ₗ[ℂ]
    groupCohomology.H2 (dualRepG (lineFaceRep N h n)) :=
  toLiteral (gammaNQAt N h) (gammaNQAt_le_N N h) n

theorem toLitG_mem_lineMixedAt (η : groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))))
    (hη : η ∈ dualCuspidalQ N n h) :
    toLitG N n h η ∈ lineMixedAt N h (dualRepG (lineFaceRep N h n)) := by
  have hy : toLiteral (gammaNQAt N h) (gammaNQAt_le_N N h) n η ∈ dualCuspidalQLiteral N n h := Submodule.mem_map_of_mem hη
  have hrad := dualCuspidalQLiteral_le_ker N n h _ hy
  have hcusp := (cuspEdge N n h ⟨_, hy⟩).2
  have hB : ∀ (F : GL (Fin 2) ℚ) (V : Rep ℂ ↥(leviCuspStab (CongruenceSubgroup.Gamma N) F))
      (z : groupCohomology.H2 V), z = 0 := fun F V z =>
    LocallyInner.h2_zero_subgroup
      (fun A z => H2_vanish_level (CongruenceSubgroup.Gamma N) A z) _ V z
  have hmix := (LocallyInner.edge_mem_cuspidalFamily_iff (lineFaceSplitting N h) (lineFaceRepLit N n h)
    (leviCuspStab (CongruenceSubgroup.Gamma N)) hB _ hrad).mp hcusp
  exact (Submodule.mem_iInf _).2 fun F => LinearMap.mem_ker.2 (hmix F)

theorem exists_dualCuspidal_of_mixed (y : groupCohomology.H2 (dualRepG (lineFaceRep N h n)))
    (hy : y ∈ lineMixedAt N h (dualRepG (lineFaceRep N h n))) :
    ∃ η ∈ dualCuspidalQ N n h, toLitG N n h η = y := by
  obtain ⟨η', hη'⟩ := (cuspEdge_bijective N n h).2 (mixedEdgeAt N h (dualRepG (lineFaceRep N h n)) ⟨y, hy⟩)
  have h1 : edgeL N n h (cuspToKer N n h η') = edgeL N n h ⟨y, res_radical_of_lineMixedAt (⟨y, hy⟩ : lineMixedAt N h (dualRepG (lineFaceRep N h n)))⟩ :=
    congrArg Subtype.val hη'
  have h2 := edgeL_injective N n h h1
  obtain ⟨η, hη, hηe⟩ := η'.2
  refine ⟨η, hη, ?_⟩
  have h3 := congrArg Subtype.val h2
  exact hηe.trans h3

end DualMixed

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
