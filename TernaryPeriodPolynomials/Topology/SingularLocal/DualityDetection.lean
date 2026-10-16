module

public import TernaryPeriodPolynomials.Topology.SingularLocal.DualityNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalDuality
open CategoryTheory HomologicalComplex FreeActionLinearization CoveringSingularOrbits
open SingularLocalCoefficient SingularLocalHomology SingularCoverNaturality
open scoped Classical

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E'] [IsCancelSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)

/-- Actual local-system homology and full-dual coefficient cohomology evaluation. -/
def homologyPairing (n : ℕ) :
    (localCochains p hp (dualRepresentation V)).homology n →ₗ[ℚ]
      Module.Dual ℚ ((localChains p hp V).homology n) :=
  (universalCoefficientIso p hp V n).hom.hom

/-- The actual local-system homology pairing is natural for a map of covers. -/
theorem homologyPairing_natural (n : ℕ)
    (φ : (localCochains p' hp' (dualRepresentation V)).homology n)
    (x : (localChains p hp V).homology n) :
    homologyPairing p hp V n
        (homologyMap (localPullback p p' F f hsquare hp hp' hF (dualRepresentation V)) n φ) x =
      homologyPairing p' hp' V n φ
        (homologyMap (localSpaceMap F hF V p p' hp hp') n x) :=
  congrArg (fun a => a.hom φ x)
    (universalCoefficientIso_natural p p' F f hsquare hp hp' hF V n)

/-- Full-dual local cohomology detects actual local homology classes. -/
theorem homology_eq_zero_iff_pairing (n : ℕ) (x : (localChains p hp V).homology n) :
    x = 0 ↔ ∀ φ, homologyPairing p hp V n φ x = 0 := by
  constructor
  · rintro rfl φ
    exact map_zero _
  · intro h
    apply (Module.forall_dual_apply_eq_zero_iff ℚ x).mp
    intro φ
    obtain ⟨ψ, rfl⟩ := (universalCoefficientIso p hp V n).toLinearEquiv.surjective φ
    exact h ψ

/-- An actual homology map is onto iff actual geometric cohomology pullback with the full
contragredient coefficient system is injective. -/
theorem homologyMap_surjective_iff_dualCohomology_injective (n : ℕ) :
    Function.Surjective (homologyMap (localSpaceMap F hF V p p' hp hp') n).hom ↔
      Function.Injective
        (homologyMap (localPullback p p' F f hsquare hp hp' hF (dualRepresentation V)) n).hom := by
  rw [← LinearMap.dualMap_injective_iff]
  let U := (universalCoefficientIso p hp V n).toLinearEquiv
  let U' := (universalCoefficientIso p' hp' V n).toLinearEquiv
  have hn (φ) : U (homologyMap
      (localPullback p p' F f hsquare hp hp' hF (dualRepresentation V)) n φ) =
      (homologyMap (localSpaceMap F hF V p p' hp hp') n).hom.dualMap (U' φ) :=
    congrArg (fun a => a.hom φ)
      (universalCoefficientIso_natural p p' F f hsquare hp hp' hF V n)
  constructor
  · intro h φ ψ heq
    apply U'.injective
    apply h
    exact (hn φ).symm.trans ((congrArg U heq).trans (hn ψ))
  · intro h φ ψ heq
    obtain ⟨φ, rfl⟩ := U'.surjective φ
    obtain ⟨ψ, rfl⟩ := U'.surjective ψ
    apply congrArg U'
    apply h
    apply U.injective
    exact (hn φ).trans (heq.trans (hn ψ).symm)

end TernaryPoly.SingularLocalDuality
