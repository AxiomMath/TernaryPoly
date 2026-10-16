module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.EdgeSurjective

@[expose] public section


/-!
# The Hochschild-Serre edge is a bijection from the mixed classes onto the cuspidal group

Formalized by Claude Sonnet 5.5.

`mixedEdgeAt_bijective N h W`: `mixedEdgeAt N h W : lineMixedAt N h W → 𝒞(H¹(N_{Q'}, W))` is bijective (injective since `H²(Γ₂(N), ·) = 0`, surjective since the edge is onto and a class whose edge is
cuspidal vanishes on the flag stabilizers), for every coefficient module `W`.  `canAt_left_perfect`: hence `canAt` is left nondegenerate.
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

section Bij

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (W : Rep ℂ ↥(gammaNQAt N h))

theorem mixedEdgeAt_injective : Function.Injective (mixedEdgeAt N h W) := by
  intro a b hab
  have hinj := splitCohomologyEdge_injective_of_invariant_H2_zero (lineFaceSplitting N h) W
    (fun x => H2_vanish_level (CongruenceSubgroup.Gamma N) _ x)
  have h1 : splitCohomologyEdge (lineFaceSplitting N h) W ⟨a.1, res_radical_of_lineMixedAt a⟩ =
      splitCohomologyEdge (lineFaceSplitting N h) W ⟨b.1, res_radical_of_lineMixedAt b⟩ := congrArg Subtype.val hab
  have h2 := hinj h1
  have h3 := congrArg (fun z : ↥(LinearMap.ker (twoCohomologyRestriction (lineFaceExt N h).inl W)) => z.1) h2
  exact Subtype.ext h3

theorem mixedEdgeAt_surjective : Function.Surjective (mixedEdgeAt N h W) := by
  intro w
  obtain ⟨⟨y, hy⟩, hedge⟩ := splitCohomologyEdge_surjective (lineFaceSplitting N h) W (leviH2Vanishes_subgroup _) w.1
  have hB : ∀ (F : GL (Fin 2) ℚ) (V : Rep ℂ ↥(leviCuspStab (CongruenceSubgroup.Gamma N) F))
      (z : groupCohomology.H2 V), z = 0 := fun F V z =>
    LocallyInner.h2_zero_subgroup
      (fun A z => H2_vanish_level (CongruenceSubgroup.Gamma N) A z) _ V z
  have hcusp : splitCohomologyEdge (lineFaceSplitting N h) W ⟨y, hy⟩ ∈
      cuspidalFamily (leviCuspStab (CongruenceSubgroup.Gamma N)) (splitRadicalH1Representation (lineFaceSplitting N h) W) := by
    rw [hedge]; exact w.2
  have hmix := (LocallyInner.edge_mem_cuspidalFamily_iff (lineFaceSplitting N h) W
    (leviCuspStab (CongruenceSubgroup.Gamma N)) hB y hy).mp hcusp
  refine ⟨⟨y, (Submodule.mem_iInf _).2 fun F => LinearMap.mem_ker.2 (hmix F)⟩, ?_⟩
  exact Subtype.ext hedge

theorem mixedEdgeAt_bijective : Function.Bijective (mixedEdgeAt N h W) :=
  ⟨mixedEdgeAt_injective N h W, mixedEdgeAt_surjective N h W⟩

/-- **`canAt` is left nondegenerate.** -/
theorem canAt_left_perfect (hN : 3 ≤ N) [FiniteDimensional ℂ W] (x : lineMixedAt N h W)
    (hx : ∀ y : lineMixedAt N h (dualRepG W), canAt N h hN W x y = 0) : x = 0 := by
  apply mixedEdgeAt_injective N h W
  rw [map_zero]
  refine (facePairingCan_perfect hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) W).1 _ (fun w => ?_)
  obtain ⟨y, rfl⟩ := mixedEdgeAt_surjective N h (dualRepG W) w
  exact hx y

end Bij

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
