module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallCover

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open SphereOddDegree FreeActionLinearization
variable {ι : Type*} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
  (V : Set OrbitSpace) (hcover : V ⊆ ⋃ i, U i)

/-- Smallness is exactly containment of the actual projected simplex in one quotient-cover member. -/
theorem coveringSimplex_small_iff {n : ℕ} (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    IsSmallSimplex (liftedOpenCover U hU V hcover) σ ↔
      ∃ i, ∀ t, coordinateProjection (mvSimplexMap σ t).val ∈ U i := by
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩
    exact ⟨i, fun t => h ⟨t, rfl⟩⟩
  · rintro ⟨i, h⟩
    refine ⟨coverProjection V ⁻¹' U i, ⟨i, rfl⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact h t

/-- The actual equivariant subdivision homotopy equivalence keeps the literal small-chain inclusion. -/
theorem coveringSmallHomotopyEquiv_hom :
    (coveringSmallHomotopyEquiv U hU V hcover).hom =
      smallInclusion DeckGroup (TopCat.of (CoverOpen V)) (liftedOpenCover U hU V hcover)
        (liftedOpenCover_invariant U hU V hcover) :=
  smallHomotopyEquiv_hom DeckGroup (TopCat.of (CoverOpen V)) (liftedOpenCover U hU V hcover)
    (liftedOpenCover_invariant U hU V hcover)

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- Restriction after genuine equivariant Hom is literal precomposition by the actual small-chain inclusion. -/
theorem coveringSmallRestriction_apply (n : ℕ)
    (f : (coveringCochains ρ V).X n) (c : (coveringSmallChains U hU V hcover).X n) :
    (((coveringSmallRestriction ρ U hU V hcover).f n f).hom c) = f.hom c.val := rfl

/-- For every true quotient open cover, the actual global and cover-small real local-coefficient
singular Hom complexes have the same cohomology via literal restriction in all degrees. -/
theorem globalSingular_subdivision_descent : QuasiIso (coveringSmallRestriction ρ U hU V hcover) :=
  coveringSmallRestriction_quasiIso ρ U hU V hcover

end TernaryPoly.SmoothSingularGlobal
