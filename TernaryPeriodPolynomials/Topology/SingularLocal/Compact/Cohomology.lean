module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Cochains
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalCoefficient

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- The directed diagram of actual relative local-cochain complexes on compact supports. -/
def compactSupportDiagram : Compacts B ⥤ CochainComplex (ModuleCat.{0} ℚ) ℕ where
  obj K := supportCochains p V (K : Set B)
  map f := supportMap p V _ _ (leOfHom f)
  map_id K := supportMap_self p V K
  map_comp f g := (supportMap_comp p V _ _ _ (leOfHom f) (leOfHom g)).symm

/-- Actual relative cohomology over compact supports, with the actual support-enlargement maps. -/
def compactCohomologyDiagram (k : ℕ) : Compacts B ⥤ ModuleCat.{0} ℚ :=
  compactSupportDiagram p V ⋙ homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) k

/-- Compactly supported local cohomology is the colimit of actual relative local cohomologies. -/
def compactCohomology (k : ℕ) : ModuleCat.{0} ℚ := colimit (compactCohomologyDiagram p V k)

/-- The actual canonical map from a fixed compact-support relative cohomology group. -/
def compactClassMap (K : Compacts B) (k : ℕ) :
    (supportCochains p V (K : Set B)).homology k ⟶ compactCohomology p V k :=
  colimit.ι (compactCohomologyDiagram p V k) K

/-- Enlargement of compact support does not change the resulting compact-support class. -/
theorem compactClassMap_natural (K L : Compacts B) (hKL : K ≤ L) (k : ℕ) :
    homologyMap (supportMap p V (K : Set B) (L : Set B) hKL) k ≫ compactClassMap p V L k =
      compactClassMap p V K k :=
  colimit.w (compactCohomologyDiagram p V k) (homOfLE hKL)

/-- A compatible family of actual relative-cohomology maps defines a compact-support map. -/
def compactCohomologyDesc (k : ℕ) (M : ModuleCat.{0} ℚ)
    (f : ∀ K : Compacts B, (supportCochains p V (K : Set B)).homology k ⟶ M)
    (hf : ∀ (K L : Compacts B) (hKL : K ≤ L),
      homologyMap (supportMap p V (K : Set B) (L : Set B) hKL) k ≫ f L = f K) :
    compactCohomology p V k ⟶ M :=
  colimit.desc (compactCohomologyDiagram p V k) ⟨M,{
    app := f
    naturality := fun K L h => by
      change homologyMap (supportMap p V (K : Set B) (L : Set B) (leOfHom h)) k ≫ f L = f K ≫ 𝟙 M
      simpa only [Category.comp_id] using hf K L (leOfHom h) }⟩

/-- The descended map retains the specified map on every actual compact-support class. -/
@[simp] theorem compactCohomologyDesc_ι (k : ℕ) (M : ModuleCat.{0} ℚ)
    (f : ∀ K : Compacts B, (supportCochains p V (K : Set B)).homology k ⟶ M)
    (hf : ∀ (K L : Compacts B) (hKL : K ≤ L),
      homologyMap (supportMap p V (K : Set B) (L : Set B) hKL) k ≫ f L = f K)
    (K : Compacts B) : compactClassMap p V K k ≫ compactCohomologyDesc p V k M f hf = f K :=
  colimit.ι_desc _ _

end TernaryPoly.SingularLocalSupport
