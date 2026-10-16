module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Fibers
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityTransport

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSection
open CategoryTheory CoveringSingularOrbits SingularLocalCoefficient SingularLocalConstant

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
    (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (s : B ⟶ E) (hs : s ≫ p = 𝟙 B)

/-- A continuous section selects an actual point in every covering fiber. -/
def sectionFiber (x : B) : Fiber p x :=
  ⟨s x, congrArg (fun f : B ⟶ B => f x) hs⟩

/-- Actual covering monodromy carries the selected section point to the selected endpoint. -/
theorem sectionFiber_transport {x y : B} (γ : Path.Homotopic.Quotient x y) :
    fiberTransport p hp γ (sectionFiber p s hs x) = sectionFiber p s hs y := by
  apply hp.isCoveringMap.monodromy_eq_of_map_eq (γ.map s.hom)
  have hcomp : p.hom.comp s.hom = ContinuousMap.id B := by
    ext x
    exact congrArg (fun f : B ⟶ B => f x) hs
  change (γ.map s.hom).map p.hom = γ.cast (sectionFiber p s hs x).property
    (sectionFiber p s hs y).property
  rw [← Path.Homotopic.Quotient.map_comp, SingularCoverNaturality.pathMap_congr hcomp]
  obtain ⟨γ⟩ := γ
  rfl

/-- Evaluation at the actual continuous section trivializes every rational coefficient fiber. -/
def sectionEvaluation (V : Rep.{0} ℚ G) (x : B) : FiberCoefficient p hp V x ≃ₗ[ℚ] V :=
  coefficientEvaluationLinearEquiv p hp (sectionFiber p s hs x)

/-- The section evaluation is compatible with every actual path transport. -/
theorem sectionEvaluation_transport (V : Rep.{0} ℚ G) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (c : FiberCoefficient p hp V x) :
    sectionEvaluation p hp s hs V y (coefficientTransportLinear p hp γ c) =
      sectionEvaluation p hp s hs V x c := by
  have h := coefficientTransport_apply_transport p hp γ c (sectionFiber p s hs x)
  rw [sectionFiber_transport p hp s hs γ] at h
  exact h

/-- The geometric fiber comparison to the genuine identity-cover constant system. -/
def constantFiberEquiv (V : Rep.{0} ℚ G) (x : B) :
    FiberCoefficient p hp V x ≃ₗ[ℚ]
      FiberCoefficient (𝟙 B) (identityCover B) (constantRep (ModuleCat.of ℚ V)) x :=
  sectionEvaluation p hp s hs V x ≪≫ₗ (fiberEquiv B (ModuleCat.of ℚ V) x).symm

/-- The actual coefficient-system comparison commutes with path transport. -/
theorem constantFiberEquiv_transport (V : Rep.{0} ℚ G) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (c : FiberCoefficient p hp V x) :
    constantFiberEquiv p hp s hs V y (coefficientTransportLinear p hp γ c) =
      coefficientTransportLinear (𝟙 B) (identityCover B) γ (constantFiberEquiv p hp s hs V x c) := by
  apply (fiberEquiv B (ModuleCat.of ℚ V) y).injective
  rw [fiberEquiv_transport]
  change (fiberEquiv B (ModuleCat.of ℚ V) y) ((fiberEquiv B (ModuleCat.of ℚ V) y).symm _) =
    (fiberEquiv B (ModuleCat.of ℚ V) x) ((fiberEquiv B (ModuleCat.of ℚ V) x).symm _)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact sectionEvaluation_transport p hp s hs V γ c

end TernaryPoly.SingularLocalSection
