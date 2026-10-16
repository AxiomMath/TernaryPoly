module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.SpaceFibers

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory HomologicalComplex FreeActionLinearization CoveringSingularOrbits
open scoped Classical

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  (F : E ⟶ E') (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)

/-- The actual coinvariant singular chain map of an equivariant map of spaces. -/
def coinvariantSpaceMap : coinvariantChains G E V ⟶ coinvariantChains G E' V :=
  (((Rep.coinvariantsTensor ℚ G).obj V).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (SingularCoverNaturality.chainMap F hF)

/-- The actual singular-chain space map postcomposes the simplex and retains its coefficient. -/
theorem coinvariantSpaceMap_generator (n : ℕ) (τ : SingularSimplex E n) (v : V) :
    (coinvariantSpaceMap F hF V).f n (generator G E V n τ v) =
      generator G E' V n (projection F n τ) v := by
  have h := congrArg (fun m => m.hom 1) (SingularCoverNaturality.generator_map F n τ)
  change ((SingularCoverNaturality.underlyingMap F).f n) (chainElement G E n τ) =
    chainElement G E' n (projection F n τ) at h
  change Rep.coinvariantsTensorMk V (EquivariantSingularResolution.chainRep G E' n) v
    (((SingularCoverNaturality.underlyingMap F).f n) (chainElement G E n τ)) =
      Rep.coinvariantsTensorMk V (EquivariantSingularResolution.chainRep G E' n) v
        (chainElement G E' n (projection F n τ))
  exact congrArg (Rep.coinvariantsTensorMk V (EquivariantSingularResolution.chainRep G E' n) v) h

variable [IsCancelSMul G E] [IsCancelSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)

/-- The genuine covariant geometric local-coefficient chain map induced by the cover square. -/
def localSpaceMap : localChains p hp V ⟶ localChains p' hp' V :=
  (chainIso p hp V).inv ≫ coinvariantSpaceMap F hF V ≫ (chainIso p' hp' V).hom

/-- An elementary chain maps to its actual image simplex with the actual pushed fiber coefficient. -/
theorem localSpaceMap_single (n : ℕ) (σ : SingularSimplex B n)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    (localSpaceMap F hF V p p' hp hp').f n (DFinsupp.single σ c) =
      DFinsupp.single (projection f n σ)
        (coefficientPushforward p p' F f hsquare hp hp' hF V (atVertex σ) c) := by
  apply (degreeEquiv p' hp' V n).symm.injective
  change (degreeEquiv p' hp' V n).symm ((degreeEquiv p' hp' V n)
    ((coinvariantSpaceMap F hF V).f n
      ((degreeEquiv p hp V n).symm (DFinsupp.single σ c)))) = _
  rw [LinearEquiv.symm_apply_apply]
  let τ := chosenLift p hp n σ
  rw [degreeEquiv_symm_single_lift p hp V n τ, coinvariantSpaceMap_generator]
  have h := degreeEquiv_symm_single_lift p' hp' V n
    (SingularCoverNaturality.liftMap p p' F f hsquare τ)
    (coefficientPushforward p p' F f hsquare hp hp' hF V (atVertex σ) c)
  apply Eq.trans _ h.symm
  apply congrArg (generator G E' V n (projection F n τ.val))
  exact (coefficientPushforward_apply p p' F f hsquare hp hp' hF V (atVertex σ) c
    (liftVertexEquiv p hp σ τ)).symm

/-- The actual singular/geometric chain isomorphisms commute with the covariant space map. -/
theorem chainIso_space_natural :
    (chainIso p hp V).hom ≫ localSpaceMap F hF V p p' hp hp' =
      coinvariantSpaceMap F hF V ≫ (chainIso p' hp' V).hom := by
  simp [localSpaceMap]

end TernaryPoly.SingularLocalHomology
