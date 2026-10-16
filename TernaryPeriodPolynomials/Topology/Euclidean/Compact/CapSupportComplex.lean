module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapSupportEquiv
public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.HomComplex

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanCompactCap
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalCap SingularLocalCapNormalization SingularLocalSupport
open SingularLocalCoefficient
variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- The literal ordinary cochain comparison is the arbitrary-chain Hom comparison. -/
def ordinaryHomCochainIso : cochains X V ≅ RationalHomologyCoefficients.homCochains (scalarChains X) V :=
  homCochainIso X V

/-- In every pair of degrees the ordinary evaluation commutes with the actual differentials. -/
theorem ordinaryEvaluation_d (i j : ℕ) (φ : (cochains X V).X i) (c : (scalarChains X).X j) :
    evaluation X V j ((cochains X V).d i j φ) c =
      evaluation X V i φ ((scalarChains X).d j i c) := by
  have h := congrArg (fun f => (f φ) c) ((ordinaryHomCochainIso X V).hom.comm i j)
  rw [RationalHomologyCoefficients.homCochains_d] at h
  exact h.symm

/-- Independent actual support evaluation commutes with the support and relative differentials. -/
theorem supportEvaluation_d (K : Set X) (i j : ℕ)
    (φ : (supportCochains (𝟙 X) (constantRep V) K).X i)
    (c : (RationalManifoldCompact.supportChains K).X j) :
    supportEvaluation X V K j ((supportCochains (𝟙 X) (constantRep V) K).d i j φ) c =
      supportEvaluation X V K i φ ((RationalManifoldCompact.supportChains K).d j i c) := by
  obtain ⟨z,rfl⟩ := RelativeAlgebra.projection_surjective (RationalRelativeSingular.inclusion Kᶜ) j c
  have hπ := congrArg (fun f => f z)
    ((cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).comm j i)
  change (RationalManifoldCompact.supportChains K).d j i
      ((cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f j z) =
    (cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f i ((scalarChains X).d j i z) at hπ
  rw [hπ, supportEvaluation_projection, supportEvaluation_projection]
  have hι := congrArg (fun f => f φ) ((supportInclusion (𝟙 X) (constantRep V) K).comm i j)
  change (cochains X V).d i j ((supportInclusion (𝟙 X) (constantRep V) K).f i φ) =
    (supportInclusion (𝟙 X) (constantRep V) K).f j
      ((supportCochains (𝟙 X) (constantRep V) K).d i j φ) at hι
  rw [← hι]
  exact ordinaryEvaluation_d X V i j _ z

/-- Actual support cochains identify, as cochain complexes, with V-valued Hom of the
actual relative scalar chains through the independent literal evaluation map. -/
def supportHomCochainIso (K : Set X) :
    supportCochains (𝟙 X) (constantRep V) K ≅
      RationalHomologyCoefficients.homCochains (RationalManifoldCompact.supportChains K) V :=
  HomologicalComplex.Hom.isoOfComponents (fun a => (supportEvaluationEquiv X V K a).toModuleIso)
    (fun i j _ => by
      rw [RationalHomologyCoefficients.homCochains_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro c
      change supportEvaluation X V K i φ
        ((RationalManifoldCompact.supportChains K).d j i c) = _
      exact (supportEvaluation_d X V K i j φ c).symm)

end TernaryPoly.EuclideanCompactCap
