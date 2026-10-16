module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.DisjointSimplices

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory FreeActionLinearization
open SmoothCoveringDeRham SymmetricSpaceCovering
namespace DisjointQuotientCover
variable {V : Set OrbitSpace} {ι : Type} (U : DisjointQuotientCover V ι)
  {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- The actual degreewise restriction to all disjoint quotient components. -/
def restrictCochains (n : ℕ) : (coveringCochains ρ V).X n →ₗ[ℝ]
    (∀ i, (coveringCochains ρ (U.domain i)).X n) where
  toFun w i := (coveringCochainRestriction ρ (U.subset i)).f n w
  map_add' w z := funext fun i => map_add ((coveringCochainRestriction ρ (U.subset i)).f n).hom w z
  map_smul' a w := funext fun i => map_smul ((coveringCochainRestriction ρ (U.subset i)).f n).hom a w

/-- A family of actual component cochains defines genuine simplex values using the unique
component containing the whole simplex. -/
def extensionValues (n : ℕ) (w : ∀ i, (coveringCochains ρ (U.domain i)).X n)
    (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) : F :=
  cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (U.domain (U.simplexIndex n σ))))
    (Rep.of ρ) n (w (U.simplexIndex n σ)) (U.componentSimplex n σ)

/-- A known component label gives the literal value on that component, retaining all
codomain-restriction witnesses explicitly. -/
theorem extensionValues_at (n : ℕ) (w : ∀ i, (coveringCochains ρ (U.domain i)).X n)
    (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) (i : ι) (hi : U.simplexIndex n σ = i)
    (hσ : SimplexInDomain (U.domain i) (globalizeSimplex V n σ)) :
    U.extensionValues ρ n w σ =
      cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (U.domain i))) (Rep.of ρ) n (w i)
        (restrictGlobalSimplex (U.domain i) n (globalizeSimplex V n σ) hσ) := by
  subst i
  rfl

/-- These literal simplex values are equivariant under the actual deck representation. -/
theorem extensionValues_smul (n : ℕ) (w : ∀ i, (coveringCochains ρ (U.domain i)).X n)
    (g : DeckGroup) (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    U.extensionValues ρ n w (g • σ) = ρ g (U.extensionValues ρ n w σ) := by
  have hi := U.simplexIndex_smul n g σ
  have hgσ : SimplexInDomain (U.domain (U.simplexIndex n σ)) (globalizeSimplex V n (g • σ)) :=
    (congrArg (fun i => SimplexInDomain (U.domain i) (globalizeSimplex V n (g • σ))) hi).mp
      (U.simplexInDomain n (g • σ))
  have he := U.extensionValues_at ρ n w (g • σ) (U.simplexIndex n σ) hi hgσ
  have hs := restrict_globalize_smul (U.domain (U.simplexIndex n σ)) n g σ
    (U.simplexInDomain n σ) hgσ
  have hv := congrArg (fun τ => cochainFunctionEquiv DeckGroup
    (TopCat.of (CoverOpen (U.domain (U.simplexIndex n σ)))) (Rep.of ρ) n
      (w (U.simplexIndex n σ)) τ) hs
  exact he.trans (hv.trans ((cochainFunctionEquiv DeckGroup
    (TopCat.of (CoverOpen (U.domain (U.simplexIndex n σ))))
      (Rep.of ρ) n (w (U.simplexIndex n σ))).property g _))

/-- Genuine extension of disjoint component cochains, on the actual singular generator basis. -/
def extendCochains (n : ℕ) (w : ∀ i, (coveringCochains ρ (U.domain i)).X n) :
    (coveringCochains ρ V).X n :=
  (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen V)) (Rep.of ρ) n).symm
    ⟨U.extensionValues ρ n w, U.extensionValues_smul ρ n w⟩

/-- The genuine extension evaluates to its actual selected-component value. -/
theorem extendCochains_evaluate (n : ℕ) (w : ∀ i, (coveringCochains ρ (U.domain i)).X n)
    (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen V)) (Rep.of ρ) n
      (U.extendCochains ρ n w) σ = U.extensionValues ρ n w σ :=
  congrArg (fun f : equivariantFunctions DeckGroup (TopCat.of (CoverOpen V)) (Rep.of ρ) n => f σ)
    ((cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen V)) (Rep.of ρ) n).apply_symm_apply _)

/-- Restricting actual cochains is exactly evaluation on the included actual simplex. -/
theorem restrictCochains_evaluate (n : ℕ) (w : (coveringCochains ρ V).X n) (i : ι)
    (σ : SingularSimplex (TopCat.of (CoverOpen (U.domain i))) n) :
    cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (U.domain i))) (Rep.of ρ) n
      (U.restrictCochains ρ n w i) σ =
      cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen V)) (Rep.of ρ) n w
        (U.includeSimplex i n σ) :=
  cochainPullback_evaluate (coverInclusion (U.subset i)) (coverInclusion_equivariant (U.subset i))
    (Rep.of ρ) n w σ

/-- Actual disjoint restrictions determine every genuine singular cochain. -/
theorem restrictCochains_injective (n : ℕ) : Function.Injective (U.restrictCochains ρ n) := by
  intro w z h
  apply (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen V)) (Rep.of ρ) n).injective
  apply Subtype.ext
  funext σ
  have hi := congrFun h (U.simplexIndex n σ)
  have he := congrArg (fun c => cochainFunctionEquiv DeckGroup
    (TopCat.of (CoverOpen (U.domain (U.simplexIndex n σ)))) (Rep.of ρ) n c
      (U.componentSimplex n σ)) hi
  rw [restrictCochains_evaluate, restrictCochains_evaluate, include_componentSimplex] at he
  exact he

end DisjointQuotientCover
end TernaryPoly.SmoothSingularGlobal
