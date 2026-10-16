module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.DisjointCochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory FreeActionLinearization SphereOddDegree
open SmoothCoveringDeRham SymmetricSpaceCovering
namespace DisjointQuotientCover
variable {V : Set OrbitSpace} {ι : Type} (U : DisjointQuotientCover V ι)
  {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- Restricting the actual extension returns every original actual component cochain. -/
theorem restrict_extendCochains (n : ℕ) (w : ∀ i, (coveringCochains ρ (U.domain i)).X n) :
    U.restrictCochains ρ n (U.extendCochains ρ n w) = w := by
  funext i
  apply (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (U.domain i))) (Rep.of ρ) n).injective
  apply Subtype.ext
  funext σ
  have hσ : SimplexInDomain (U.domain i) (globalizeSimplex V n (U.includeSimplex i n σ)) :=
    fun t => (mvSimplexMap σ t).property.2
  have he := U.extensionValues_at ρ n w (U.includeSimplex i n σ) i (U.simplexIndex_include i n σ) hσ
  have hr := congrArg (fun τ => cochainFunctionEquiv DeckGroup
    (TopCat.of (CoverOpen (U.domain i))) (Rep.of ρ) n (w i) τ)
      (U.restrictGlobal_include i n σ hσ)
  exact (U.restrictCochains_evaluate ρ n (U.extendCochains ρ n w) i σ).trans
    ((U.extendCochains_evaluate ρ n w (U.includeSimplex i n σ)).trans (he.trans hr))

/-- The actual disjoint restriction is a genuine linear equivalence in every degree. -/
def cochainEquiv (n : ℕ) : (coveringCochains ρ V).X n ≃ₗ[ℝ]
    (∀ i, (coveringCochains ρ (U.domain i)).X n) :=
  LinearEquiv.ofBijective (U.restrictCochains ρ n)
    ⟨U.restrictCochains_injective ρ n, fun w => ⟨U.extendCochains ρ n w,U.restrict_extendCochains ρ n w⟩⟩

/-- The genuine disjoint equivalence commutes with the actual singular coboundary. -/
theorem cochainEquiv_d (n : ℕ) (w : (coveringCochains ρ V).X n) :
    U.cochainEquiv ρ (n+1) ((coveringCochains ρ V).d n (n+1) w) =
      fun i => (coveringCochains ρ (U.domain i)).d n (n+1) (U.cochainEquiv ρ n w i) := by
  funext i
  exact (congrArg (fun f => f.hom w) ((coveringCochainRestriction ρ (U.subset i)).comm n (n+1))).symm

end DisjointQuotientCover
end TernaryPoly.SmoothSingularGlobal
