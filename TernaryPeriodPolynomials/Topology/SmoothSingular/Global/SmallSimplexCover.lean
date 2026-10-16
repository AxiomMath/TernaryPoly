module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Subdivision
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechFlags

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set FreeActionLinearization SphereOddDegree
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts

variable {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
  (hcover : Set.univ ⊆ ⋃ i, U i)

/-- The actual cover-small simplex subtype of the original global covering. -/
abbrev CoverSmallSimplex (n : ℕ) :=
  {σ : SingularSimplex (TopCat.of (CoverOpen Set.univ)) n //
    IsSmallSimplex (liftedOpenCover U hU Set.univ hcover) σ}

/-- The genuine deck action on actual small simplices, restricted from the real singular model. -/
instance coverSmallSimplexMulAction (n : ℕ) : MulAction DeckGroup (CoverSmallSimplex U hU hcover n) :=
  predicateMulAction DeckGroup (TopCat.of (CoverOpen Set.univ)) n
    (IsSmallSimplex (liftedOpenCover U hU Set.univ hcover))
    (hP := ⟨small_invariant DeckGroup (TopCat.of (CoverOpen Set.univ))
      (liftedOpenCover U hU Set.univ hcover) (liftedOpenCover_invariant U hU Set.univ hcover) n⟩)

/-- Projected actual singular simplices are unchanged under the actual deck action. -/
theorem projectedSimplex_smul (n : ℕ) (g : DeckGroup)
    (σ : SingularSimplex (TopCat.of (CoverOpen Set.univ)) n) (t : Convexity.StdSimplex ℝ (Fin (n+1))) :
    coordinateProjection (mvSimplexMap (g • σ) t).val =
      coordinateProjection (mvSimplexMap σ t).val := by
  change coverProjection Set.univ (mvSimplexMap (g • σ) t) =
    coverProjection Set.univ (mvSimplexMap σ t)
  rw [simplexMap_smul]
  exact coverProjection_deck Set.univ g (mvSimplexMap σ t)

/-- Each actual small simplex belongs to the invariant set of simplices contained in some
actual quotient-cover member. This supplies the honest flag contraction data. -/
def smallSimplexIndexCover (n : ℕ) :
    InvariantSetCover DeckGroup (CoverSmallSimplex U hU hcover n) ι where
  mem i σ := ∀ t, coordinateProjection (mvSimplexMap σ.val t).val ∈ U i
  covers σ := (coveringSimplex_small_iff U hU Set.univ hcover σ.val).mp σ.property
  invariant i g σ := by
    change (∀ t, coordinateProjection (mvSimplexMap (g • σ.val) t).val ∈ U i) ↔ _
    constructor
    · intro h t
      exact (projectedSimplex_smul n g σ.val t) ▸ h t
    · intro h t
      exact (projectedSimplex_smul n g σ.val t).symm ▸ h t

/-- The chosen cover index actually contains every point of the true projected small simplex. -/
theorem smallSimplex_selected_contains (n : ℕ) (σ : CoverSmallSimplex U hU hcover n) :
    ∀ t, coordinateProjection (mvSimplexMap σ.val t).val ∈
      U ((smallSimplexIndexCover U hU hcover n).index σ) :=
  (smallSimplexIndexCover U hU hcover n).index_mem σ

/-- The actual containing-index choice is deck-invariant, hence may be used inside equivariant Hom. -/
theorem smallSimplex_selected_invariant (n : ℕ) (g : DeckGroup) (σ : CoverSmallSimplex U hU hcover n) :
    (smallSimplexIndexCover U hU hcover n).index (g • σ) =
      (smallSimplexIndexCover U hU hcover n).index σ :=
  (smallSimplexIndexCover U hU hcover n).index_smul g σ

end TernaryPoly.SmoothSingularGlobal
