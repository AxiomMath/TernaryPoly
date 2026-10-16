module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ClsS
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Product

@[expose] public section


/-!
# `H²` of a product of cochain complexes of rational vector spaces is the product of the `H²`

For a family `C` of cochain complexes of rational vector spaces, the canonical map from the degree-two
cohomology of `Family.productComplex C` to the product of the degree-two cohomologies of the factors is
bijective (`prodHomologyMapS_bijective`), proved with the degree-two class API `clsS`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPoly.BoundaryFaceResolutionComparison

variable (m : ℕ) {I : Type} (C : I → CochainComplex (ModuleCat.{0} ℚ) ℕ)

/-- The projection of a product complex to a factor. -/
def prodProjS (i : I) : Family.productComplex C ⟶ C i where
  f n := ModuleCat.ofHom (LinearMap.proj i)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl

/-- The canonical map `H²(∏ C i) → ∏ H²(C i)`. -/
def prodHomologyMapS : (Family.productComplex C).homology (m+1) →ₗ[ℚ] (∀ i, (C i).homology (m+1)) :=
  LinearMap.pi fun i => (HomologicalComplex.homologyMap (prodProjS C i) (m+1)).hom

theorem prodHomologyMapS_clsS (a : (Family.productComplex C).X (m+1))
    (ha : ((Family.productComplex C).d (m+1) (m+1+1)).hom a = 0) (i : I) :
    prodHomologyMapS m C (clsS (Family.productComplex C) a ha) i =
      clsS (C i) (a i) (congrFun ha i) := by
  have h := clsS_map (Family.productComplex C) (prodProjS C i) a ha (congrFun ha i)
  exact h

theorem prodHomologyMapS_bijective : Function.Bijective (prodHomologyMapS m C) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨a, ha, rfl⟩ := exists_clsS _ x
    rw [(clsS_eq_zero_iff _ a ha)]
    have hi : ∀ i, ∃ b : (C i).X m, ((C i).d m (m+1)).hom b = a i := fun i => by
      have := congrFun hx i
      rw [prodHomologyMapS_clsS] at this
      exact (clsS_eq_zero_iff _ _ _).1 this
    choose b hb using hi
    exact ⟨b, funext hb⟩
  · intro y
    have hi : ∀ i, ∃ (a : (C i).X (m+1)) (ha : ((C i).d (m+1) (m+1+1)).hom a = 0), clsS (C i) a ha = y i :=
      fun i => exists_clsS _ (y i)
    choose a ha hy using hi
    refine ⟨clsS (Family.productComplex C) a (funext ha), funext fun i => ?_⟩
    exact (prodHomologyMapS_clsS m C a (funext ha) i).trans (hy i)

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
