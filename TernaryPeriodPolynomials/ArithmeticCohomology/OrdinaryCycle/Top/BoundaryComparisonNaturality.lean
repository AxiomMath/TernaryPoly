module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonEvaluation

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryTopBoundaryComparison
open CategoryTheory HomologicalComplex EquivariantSingularSmall

variable {G : Type} [Group G] {C D : ChainComplex (Rep.{0} ℚ G) ℕ}
  (f : C ⟶ D) (W : Rep.{0} ℚ G) (n : ℕ)

/-- The cocycle induced by an actual chain map is literal precomposition. -/
theorem cocycleValue_pullback (x : (homCochains D W).cycles n) :
    cocycleValue C W n (cyclesMap (homPullback f W) n x) =
      f.f n ≫ cocycleValue D W n x :=
  congrArg (fun k => k x) (cyclesMap_i (homPullback f W) n)

/-- Canonical cocycle descent is natural for actual equivariant chain maps. -/
theorem cocycleEvaluation_pullback (x : (homCochains D W).cycles n) :
    cocycleEvaluation C W n (cyclesMap (homPullback f W) n x) =
      homologyMap f n ≫ cocycleEvaluation D W n x := by
  apply (cancel_epi (C.homologyπ n)).mp
  erw [cocycleEvaluation_projection C W n _, ← Category.assoc,
    homologyπ_naturality f n, Category.assoc, cocycleEvaluation_projection D W n x,
    cocycleValue_pullback f W n x, ← Category.assoc (cyclesMap f n),
    cyclesMap_i f n, Category.assoc]

/-- Literal precomposition of equivariant homology functionals. -/
def homologyFunctionalPullback : ModuleCat.of ℚ (D.homology n ⟶ W) ⟶
    ModuleCat.of ℚ (C.homology n ⟶ W) :=
  ModuleCat.ofHom {
    toFun := fun φ => homologyMap f n ≫ φ
    map_add' := fun _ _ => by simp only [Preadditive.comp_add]
    map_smul' := fun _ _ => by simp only [Linear.comp_smul, RingHom.id_apply] }

/-- Canonical Hom-cohomology evaluation is natural for literal chain maps. -/
theorem homologyEvaluation_natural :
    homologyMap (homPullback f W) n ≫ homologyEvaluation C W n =
      homologyEvaluation D W n ≫ homologyFunctionalPullback f W n := by
  apply (cancel_epi ((homCochains D W).homologyπ n)).mp
  rw [← Category.assoc, homologyπ_naturality, Category.assoc,
    homologyEvaluation_projection, ← Category.assoc, homologyEvaluation_projection]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact cocycleEvaluation_pullback f W n x

end TernaryPoly.OrdinaryTopBoundaryComparison
