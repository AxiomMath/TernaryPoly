module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapSupportKernel

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanCompactCap
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalCap SingularLocalCapNormalization SingularLocalSupport
open SingularLocalCoefficient EquivariantSingularSmall
variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- Every V-valued linear map on actual relative chains is evaluation by an actual
support cochain, with no finiteness assumption on V or the singular chains. -/
theorem supportEvaluation_surjective (K : Set X) (a : ℕ) :
    Function.Surjective (supportEvaluation X V K a) := by
  intro ψ
  let π := (cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f a
  let φ := (cochainHomEquiv X V a).symm (ψ.comp π.hom)
  have he : evaluation X V a φ = ψ.comp π.hom :=
    (cochainHomEquiv X V a).apply_symm_apply _
  have hφ : (localRestriction (𝟙 X) Kᶜ (constantRep V)).f a φ = 0 := by
    apply restriction_zero_of_evaluation X V K a φ
    intro c
    rw [he, LinearMap.comp_apply]
    have h := congrArg (fun f => f c) (HomologicalComplex.congr_hom
      (cokernel.condition (RationalRelativeSingular.inclusion Kᶜ)) a)
    change π ((RationalRelativeSingular.inclusion Kᶜ).f a c) = 0 at h
    rw [h, map_zero]
  obtain ⟨φ',hφ'⟩ := kernel_degree_exists (localRestriction (𝟙 X) Kᶜ (constantRep V)) a φ hφ
  refine ⟨φ', ?_⟩
  apply LinearMap.ext
  intro c
  obtain ⟨z,rfl⟩ := RelativeAlgebra.projection_surjective (RationalRelativeSingular.inclusion Kᶜ) a c
  rw [supportEvaluation_projection]
  change evaluation X V a ((kernel.ι (localRestriction (𝟙 X) Kᶜ (constantRep V))).f a φ') z = _
  rw [hφ', he]
  rfl

/-- Actual fixed-support cochains are exactly the full V-valued linear dual of actual
relative scalar chains, by the independent literal evaluation map. -/
def supportEvaluationEquiv (K : Set X) (a : ℕ) :
    (supportCochains (𝟙 X) (constantRep V) K).X a ≃ₗ[ℚ]
      ((RationalManifoldCompact.supportChains K).X a →ₗ[ℚ] V) :=
  LinearEquiv.ofBijective (supportEvaluation X V K a)
    ⟨supportEvaluation_injective X V K a, supportEvaluation_surjective X V K a⟩

end TernaryPoly.EuclideanCompactCap
