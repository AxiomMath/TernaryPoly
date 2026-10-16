module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.DeRhamNatural

@[expose] public section


open CategoryTheory groupCohomology

/-!
# Restriction commutes with pullback along a group homomorphism (functoriality of `H²`)

Formalized by Claude Sonnet 5.5.

Paper: "apply the preceding construction to `ȷ(Γ)` and pull back".  The only cohomological input of the
transport of the constant terms: for a commutative square of group homomorphisms `α ∘ β = β' ∘ α'` the restriction of a pulled-back
class is the pullback of the restricted class (`restrict_pullback`, from `groupCohomology.map_comp`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument.EisensteinClass

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K K' G G' : Type} [Group K] [Group K'] [Group G] [Group G']

/-- **Restriction commutes with pullback along a group homomorphism** (functoriality of `H²`): for a commutative square of
group homomorphisms `α ∘ β = β' ∘ α'`, representations related by the identity of the underlying module
(`ρ_G = ρ_{G'} ∘ α`, `ρ_K = ρ_G ∘ β`, `ρ_{K'} = ρ_{G'} ∘ β'`, `ρ_K = ρ_{K'} ∘ α'`), restricting the pulled-back class to `K` is the
pullback along `α'` of the restricted class. -/
theorem restrict_pullback (β : K →* G) (α : G →* G') (α' : K →* K') (β' : K' →* G')
    (hcomm : ∀ k, α (β k) = β' (α' k))
    (ρG : Representation ℝ G F) (ρG' : Representation ℝ G' F) (hG : ∀ g, ρG g = ρG' (α g))
    (ρK : Representation ℝ K F) (hK : ∀ k, ρK k = ρG (β k))
    (ρK' : Representation ℝ K' F) (hK' : ∀ k, ρK' k = ρG' (β' k))
    (hKK : ∀ k, ρK k = ρK' (α' k))
    (x : groupCohomology.H2 (Rep.of ρG')) :
    (groupCohomology.map β (resMor β ρK ρG hK) 2).hom
        ((groupCohomology.map α (resMor α ρG ρG' hG) 2).hom x) =
      (groupCohomology.map α' (resMor α' ρK ρK' hKK) 2).hom
        ((groupCohomology.map β' (resMor β' ρK' ρG' hK') 2).hom x) := by
  have h1 := groupCohomology.map_comp α β (resMor α ρG ρG' hG) (resMor β ρK ρG hK) 2
  have h2 := groupCohomology.map_comp β' α' (resMor β' ρK' ρG' hK') (resMor α' ρK ρK' hKK) 2
  have h3 : groupCohomology.map (α.comp β) ((Rep.resFunctor β).map (resMor α ρG ρG' hG) ≫
      resMor β ρK ρG hK) 2 =
    groupCohomology.map (β'.comp α') ((Rep.resFunctor α').map (resMor β' ρK' ρG' hK') ≫
      resMor α' ρK ρK' hKK) 2 := by
    apply groupCohomology.map_congr (MonoidHom.ext hcomm)
    rfl
  have h4 := congrArg (fun m => m.hom x) (h1.symm.trans (h3.trans h2))
  exact h4

/-- **Restriction is transitive** (functoriality of `H²`): for `γ : K' → K`, `β : K → G` and `β' = β ∘ γ`, restricting directly to `K'`
is restricting to `K` and then pulling back along `γ`. -/
theorem restrict_comp (γ : K' →* K) (β : K →* G) (β' : K' →* G) (hβ : ∀ k, β (γ k) = β' k)
    (ρG : Representation ℝ G F) (ρK : Representation ℝ K F) (hK : ∀ k, ρK k = ρG (β k))
    (ρK' : Representation ℝ K' F) (hK' : ∀ k, ρK' k = ρK (γ k)) (hK'' : ∀ k, ρK' k = ρG (β' k))
    (x : groupCohomology.H2 (Rep.of ρG)) :
    (groupCohomology.map β' (resMor β' ρK' ρG hK'') 2).hom x =
      (groupCohomology.map γ (resMor γ ρK' ρK hK') 2).hom
        ((groupCohomology.map β (resMor β ρK ρG hK) 2).hom x) := by
  have h1 := groupCohomology.map_comp β γ (resMor β ρK ρG hK) (resMor γ ρK' ρK hK') 2
  have h3 : groupCohomology.map β' (resMor β' ρK' ρG hK'') 2 =
      groupCohomology.map (β.comp γ) ((Rep.resFunctor γ).map (resMor β ρK ρG hK) ≫ resMor γ ρK' ρK hK') 2 := by
    apply groupCohomology.map_congr (MonoidHom.ext hβ).symm
    rfl
  exact congrArg (fun m => m.hom x) (h3.trans h1)

end TernaryPeriodPolynomials.Argument.EisensteinDual
