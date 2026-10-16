module

public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionFunctions

@[expose] public section


noncomputable section
open CategoryTheory
open scoped Simplicial
namespace TernaryPoly.SingularBoundaryRestriction
open FreeActionLinearization CoveringSingularOrbits EquivariantSingularResolution
  EquivariantSingularCohomology SingularCoverNaturality

variable {G : Type} [Group G] {E E' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  (F : E ⟶ E') (hF : ∀ (g : G) (x : E),F (g • x)=g • F x)

omit [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E'] in
/-- An injective continuous map is injective on actual singular simplices. -/
theorem simplexMap_injective (hinj : Function.Injective F) (n : ℕ) :
    Function.Injective (projection F n) := by
  intro σ τ he
  apply (TopCat.toSSetObjEquiv E (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  apply hinj
  exact congrArg (fun s => TopCat.toSSetObjEquiv E' (.op ⦋n⦌) s z) he

include hF in
/-- The actual map on singular simplices is equivariant for postcomposition. -/
theorem simplexMap_equivariant (n : ℕ) (g : G) (σ : SingularSimplex E n) :
    projection F n (g • σ)=g • projection F n σ := by
  apply (TopCat.toSSetObjEquiv E' (.op ⦋n⦌)).injective
  rw [projection_equiv,singularEquiv_smul,singularEquiv_smul,projection_equiv]
  apply ContinuousMap.ext
  intro z
  exact hF g _

/-- A graded linear extension by zero on actual equivariant simplex functions. -/
def functionExtension (hinj : Function.Injective F) (V : Rep ℚ G) (n : ℕ) :
    equivariantFunctions G E V n →ₗ[ℚ] equivariantFunctions G E' V n where
  toFun c := ⟨zeroExtension (projection F n) c.val,
    zeroExtension_equivariant (projection F n) (simplexMap_injective F hinj n)
      (simplexMap_equivariant F hF n) V c.val c.property⟩
  map_add' c d := by
    apply Subtype.ext
    exact map_add (zeroExtension (projection F n)) c.val d.val
  map_smul' r c := by
    apply Subtype.ext
    exact map_smul (zeroExtension (projection F n)) r c.val

/-- A graded linear section of pullback. It is not asserted to commute with differentials. -/
def cochainExtension (hinj : Function.Injective F) (V : Rep ℚ G) (n : ℕ) :
    (chainRep G E n ⟶ V) →ₗ[ℚ] (chainRep G E' n ⟶ V) :=
  (cochainFunctionEquiv G E' V n).symm.toLinearMap.comp
    ((functionExtension F hF hinj V n).comp (cochainFunctionEquiv G E V n).toLinearMap)

/-- Restricting the graded extension recovers the original actual singular cochain. -/
theorem cochainPullback_extension (hinj : Function.Injective F) (V : Rep ℚ G) (n : ℕ)
    (c : chainRep G E n ⟶ V) :
    (cochainPullback F hF V).f n (cochainExtension F hF hinj V n c)=c := by
  apply (cochainFunctionEquiv G E V n).injective
  apply Subtype.ext
  funext σ
  rw [cochainPullback_evaluate]
  change (cochainFunctionEquiv G E' V n
    ((cochainFunctionEquiv G E' V n).symm
      (functionExtension F hF hinj V n (cochainFunctionEquiv G E V n c))))
        (projection F n σ)=_
  rw [LinearEquiv.apply_symm_apply]
  exact zeroExtension_image (projection F n) (simplexMap_injective F hinj n)
    (cochainFunctionEquiv G E V n c).val σ

/-- Literal equivariant singular restriction along an injective map is surjective in every degree. -/
theorem cochainPullback_surjective (hinj : Function.Injective F) (V : Rep ℚ G) (n : ℕ) :
    Function.Surjective ((cochainPullback F hF V).f n) :=
  fun c => ⟨cochainExtension F hF hinj V n c,cochainPullback_extension F hF hinj V n c⟩

end TernaryPoly.SingularBoundaryRestriction
