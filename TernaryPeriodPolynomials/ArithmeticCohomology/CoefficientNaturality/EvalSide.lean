module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonOrdinaryIso

@[expose] public section


/-!
# Coefficient naturality of the ordinary evaluation isomorphism

Postcomposition with a morphism `f : W ⟶ W'` of coefficient representations is a cochain map
`coefHomPost C f : Hom(C, W) ⟶ Hom(C, W')` on the literal Hom cochains of any chain complex `C` of
representations.  The canonical evaluation of Hom cohomology on chain homology, and the literal
`relativeOrdinaryCohomologyIso`, commute with it: evaluating the postcomposed class is the
postcomposition of the evaluated class (`homologyEvaluation_coefHomPost`,
`relativeOrdinaryCohomologyIso_natural`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CoefficientNaturality

open TernaryPoly.EquivariantSingularSmall TernaryPoly.OrdinaryTopBoundaryComparison

section Post

variable {G : Type} [Group G] (C : ChainComplex (Rep.{0} ℚ G) ℕ) {W W' : Rep.{0} ℚ G}

/-- Postcomposition with a morphism of coefficient representations, as a cochain map. -/
def coefHomPost (f : W ⟶ W') : homCochains C W ⟶ homCochains C W' where
  f n := ModuleCat.ofHom
    { toFun := fun c => c ≫ f
      map_add' := fun c c' => Preadditive.add_comp _ _ _ c c' f
      map_smul' := fun r c => by simp }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change C.d j i ≫ (c ≫ f) = (C.d j i ≫ c) ≫ f
    exact (Category.assoc _ _ _).symm

theorem coefHomPost_apply (f : W ⟶ W') (n : ℕ) (c : C.X n ⟶ W) :
    ((coefHomPost C f).f n).hom c = c ≫ f := rfl

/-- The canonical evaluation of Hom cohomology on chain homology is natural in the coefficients. -/
theorem homologyEvaluation_coefHomPost (f : W ⟶ W') (n : ℕ)
    (y : (homCochains C W).homology n) :
    homologyEvaluation C W' n (homologyMap (coefHomPost C f) n y) =
      homologyEvaluation C W n y ≫ f := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective ((homCochains C W).homologyπ n)).1 inferInstance y
  have h1 : homologyMap (coefHomPost C f) n ((homCochains C W).homologyπ n x) =
      (homCochains C W').homologyπ n (cyclesMap (coefHomPost C f) n x) := by
    have := congrArg (fun g => g x) (homologyπ_naturality (coefHomPost C f) n)
    exact this
  rw [h1]
  have e1 : ∀ {V : Rep.{0} ℚ G} (z : (homCochains C V).cycles n),
      homologyEvaluation C V n ((homCochains C V).homologyπ n z) = cocycleEvaluation C V n z := by
    intro V z
    have h := congrArg (fun f => f z) (homologyEvaluation_projection C V n)
    exact h
  rw [e1, e1]
  apply (cancel_epi (C.homologyπ n)).mp
  rw [cocycleEvaluation_projection, ← Category.assoc, cocycleEvaluation_projection,
    Category.assoc]
  congr 1
  have hv := congrArg (fun g => g x) (cyclesMap_i (coefHomPost C f) n)
  exact hv

end Post

/-- The literal relative ordinary evaluation isomorphism is natural in the coefficients. -/
theorem relativeOrdinaryCohomologyIso_natural {W W' : Rep.{0} ℚ TernaryPoly.IntegralGL3Congruence.principalSix}
    (f : W ⟶ W') (y : (homCochains upstairsRelativeChains W).homology 2) :
    (relativeOrdinaryCohomologyIso W').hom (homologyMap (coefHomPost upstairsRelativeChains f) 2 y) =
      (relativeOrdinaryCohomologyIso W).hom y ≫ f := by
  rw [relativeOrdinaryCohomologyIso_apply, relativeOrdinaryCohomologyIso_apply,
    homologyEvaluation_coefHomPost, Category.assoc]

end TernaryPeriodPolynomials.Argument.CoefficientNaturality

