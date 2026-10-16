module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.LocalSmallChains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Module CategoryTheory FreeActionLinearization SphereOddDegree

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (n : ℕ) (P : SingularSimplex E n → Prop)
  [hP : Fact (∀ (g : G) (σ : SingularSimplex E n), P σ → P (g • σ))]

/-- The actual invariant predicate basis transforms by its literal simplex action. -/
theorem predicateBasis_smul (g : G) (σ : {σ // P σ}) :
    (predicateRep G E n P).ρ g (predicateBasis E n P σ) =
      predicateBasis E n P (g • σ) := by
  apply Subtype.ext
  exact (congrArg (chainAction G E n g) (predicateBasis_apply E n P σ)).trans
    ((chainAction_generator G E n g σ.val).trans (predicateBasis_apply E n P (g • σ)).symm)

/-- Projection on actual singular generators, keeping precisely the allowed family. -/
def predicateGeneratorProjection (σ : SingularSimplex E n) : predicateRep G E n P := by
  classical
  exact if h : P σ then predicateBasis E n P ⟨σ,h⟩ else 0

/-- The graded projection keeps an actual allowed simplex. -/
theorem predicateGeneratorProjection_mem (σ : SingularSimplex E n) (hσ : P σ) :
    predicateGeneratorProjection G E n P σ = predicateBasis E n P ⟨σ,hσ⟩ := by
  classical
  unfold predicateGeneratorProjection
  exact dite_eq_left hσ

/-- The graded projection annihilates an actual disallowed simplex. -/
theorem predicateGeneratorProjection_not_mem (σ : SingularSimplex E n) (hσ : ¬P σ) :
    predicateGeneratorProjection G E n P σ = 0 := by
  classical
  unfold predicateGeneratorProjection
  exact dite_eq_right hσ

/-- The literal projection on generators is equivariant because the predicate is invariant. -/
theorem predicateGeneratorProjection_smul (g : G) (σ : SingularSimplex E n) :
    predicateGeneratorProjection G E n P (g • σ) =
      (predicateRep G E n P).ρ g (predicateGeneratorProjection G E n P σ) := by
  classical
  by_cases hσ : P σ
  · have hg := hP.out g σ hσ
    rw [predicateGeneratorProjection_mem G E n P _ hg,predicateGeneratorProjection_mem G E n P _ hσ]
    exact (predicateBasis_smul G E n P g ⟨σ,hσ⟩).symm
  · have hg : ¬P (g • σ) := by
      intro h
      have hh := hP.out g⁻¹ (g • σ) h
      exact hσ (by simpa only [inv_smul_smul] using hh)
    rw [predicateGeneratorProjection_not_mem G E n P _ hg,predicateGeneratorProjection_not_mem G E n P _ hσ,map_zero]

/-- Linear graded projection onto the genuine allowed-simplex span. -/
def predicateGradedProjectionLinear : (underlyingChains E).X n →ₗ[ℝ] predicateRep G E n P :=
  (generatorBasis E n).constr ℝ (predicateGeneratorProjection G E n P)

/-- The graded projection keeps its actual prescribed simplex values. -/
theorem predicateGradedProjectionLinear_generator (σ : SingularSimplex E n) :
    predicateGradedProjectionLinear G E n P (generatorBasis E n σ) =
      predicateGeneratorProjection G E n P σ :=
  Basis.constr_basis _ ℝ _ σ

/-- The linear graded projection genuinely intertwines the deck actions. -/
theorem predicateGradedProjectionLinear_equivariant (g : G) :
    (predicateGradedProjectionLinear G E n P).comp (chainAction G E n g) =
      ((predicateRep G E n P).ρ g).comp (predicateGradedProjectionLinear G E n P) := by
  apply (generatorBasis E n).ext
  intro σ
  change predicateGradedProjectionLinear G E n P (chainAction G E n g (generatorBasis E n σ)) =
    (predicateRep G E n P).ρ g (predicateGradedProjectionLinear G E n P (generatorBasis E n σ))
  rw [generatorBasis_smul,predicateGradedProjectionLinear_generator,
    predicateGeneratorProjection_smul,predicateGradedProjectionLinear_generator]

/-- An actual graded retraction as a representation morphism. No chain-map assertion is made. -/
def predicateGradedProjection : chainRep G E n ⟶ predicateRep G E n P :=
  Rep.ofHom ⟨predicateGradedProjectionLinear G E n P,
    predicateGradedProjectionLinear_equivariant G E n P⟩

/-- The actual graded projection is a left inverse on the genuine predicate-span module. -/
theorem predicateGradedProjection_leftInverse (c : predicateRep G E n P) :
    (predicateGradedProjection G E n P).hom c.val = c := by
  classical
  have h : (predicateGradedProjectionLinear G E n P).comp (predicateSpan E n P).subtype =
      LinearMap.id := by
    apply (predicateBasis E n P).ext
    intro σ
    change predicateGradedProjectionLinear G E n P (predicateBasis E n P σ).val = _
    rw [predicateBasis_apply,←generatorBasis_apply,predicateGradedProjectionLinear_generator]
    exact predicateGeneratorProjection_mem G E n P σ.val σ.property
  exact congrArg (fun l => l c) h

end TernaryPoly.SmoothSingularGlobal
