module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.Support
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Cohomology

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSection
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalConstant SingularLocalSupport

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
    (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (V : Rep.{0} ℚ G)
local instance : Fact (IsQuotientCoveringMap (𝟙 B) Unit) := ⟨identityCover B⟩

/-- Actual support cohomology diagrams are isomorphic under section evaluation. -/
def compactDiagramIso (a : ℕ) : compactCohomologyDiagram p V a ≅
    compactCohomologyDiagram (𝟙 B) (constantRep (ModuleCat.of ℚ V)) a :=
  NatIso.ofComponents (fun K => (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) a).mapIso
    (supportIso p s hs V (K : Set B))) (fun {K L} f => by
      change homologyMap (supportMap p V K L (leOfHom f)) a ≫ homologyMap (supportIso p s hs V L).hom a =
        homologyMap (supportIso p s hs V K).hom a ≫
          homologyMap (supportMap (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K L (leOfHom f)) a
      rw [← homologyMap_comp,← homologyMap_comp,supportIso_natural])

/-- Actual compactly supported cohomology trivializes along a genuine continuous section. -/
def compactCohomologyIso (a : ℕ) : compactCohomology p V a ≅
    compactCohomology (𝟙 B) (constantRep (ModuleCat.of ℚ V)) a :=
  colim.mapIso (compactDiagramIso p s hs V a)

/-- The compact-support comparison retains the section evaluation on every actual support class. -/
theorem compactCohomologyIso_classMap (a : ℕ) (K : Compacts B) :
    compactClassMap p V K a ≫ (compactCohomologyIso p s hs V a).hom =
      homologyMap (supportIso p s hs V K).hom a ≫
        compactClassMap (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K a := by
  exact colimit.ι_map (compactDiagramIso p s hs V a).hom K

end TernaryPoly.SingularLocalSection
