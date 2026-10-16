module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cls
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Product

@[expose] public section


/-!
# `H²` of a product of cochain complexes of rational vector spaces is the product of the `H²`

For a family `C` of cochain complexes of rational vector spaces, the canonical map from the degree-two
cohomology of `Family.productComplex C` to the product of the degree-two cohomologies of the factors is
bijective (`prodHomologyMap_bijective`), proved with the degree-two class API `cls2`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPoly.BoundaryFaceResolutionComparison

variable {I : Type} (C : I → CochainComplex (ModuleCat.{0} ℚ) ℕ)

/-- The projection of a product complex to a factor. -/
def prodProj (i : I) : Family.productComplex C ⟶ C i where
  f n := ModuleCat.ofHom (LinearMap.proj i)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl

/-- The canonical map `H²(∏ C i) → ∏ H²(C i)`. -/
def prodHomologyMap : (Family.productComplex C).homology 2 →ₗ[ℚ] (∀ i, (C i).homology 2) :=
  LinearMap.pi fun i => (HomologicalComplex.homologyMap (prodProj C i) 2).hom

theorem prodHomologyMap_cls2 (a : (Family.productComplex C).X 2)
    (ha : ((Family.productComplex C).d 2 3).hom a = 0) (i : I) :
    prodHomologyMap C (cls2 (Family.productComplex C) a ha) i =
      cls2 (C i) (a i) (congrFun ha i) := by
  have h := cls2_map (Family.productComplex C) (prodProj C i) a ha (congrFun ha i)
  exact h

theorem prodHomologyMap_bijective : Function.Bijective (prodHomologyMap C) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨a, ha, rfl⟩ := exists_cls2 _ x
    rw [(cls2_eq_zero_iff _ a ha)]
    have hi : ∀ i, ∃ b : (C i).X 1, ((C i).d 1 2).hom b = a i := fun i => by
      have := congrFun hx i
      rw [prodHomologyMap_cls2] at this
      exact (cls2_eq_zero_iff _ _ _).1 this
    choose b hb using hi
    exact ⟨b, funext hb⟩
  · intro y
    have hi : ∀ i, ∃ (a : (C i).X 2) (ha : ((C i).d 2 3).hom a = 0), cls2 (C i) a ha = y i :=
      fun i => exists_cls2 _ (y i)
    choose a ha hy using hi
    refine ⟨cls2 (Family.productComplex C) a (funext ha), funext fun i => ?_⟩
    exact (prodHomologyMap_cls2 C a (funext ha) i).trans (hy i)

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
