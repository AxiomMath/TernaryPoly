module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallSupportDiagram
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SubcomplexLift
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FilteredHomology

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory Limits HomologicalComplex TopologicalSpace
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  (C : CompactConvexCover)

/-- Every actual cochain with a fixed compact complement support has finite actual chart restrictions. -/
theorem smallSupport_finiteRestriction (K : Compacts OrbitSpace) (n : ℕ)
    (x : (smallSupport ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge K).X n) :
    (kernel.ι (smallSupportRestriction ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge K)).f n x ∈
        (finiteRestrictionSmallSubmodules ρ C).term n :=
  (finiteRestriction_iff_exists_complement_kernel ρ C n _).mpr
    ⟨K,cochainKernel_condition _ n x⟩

/-- Actual fixed compact-support small cochains map into the genuine finite-restriction complex. -/
def smallSupportToFinite (K : Compacts OrbitSpace) :
    smallSupport ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge K ⟶ finiteRestrictionSmallComplex ρ C :=
  (finiteRestrictionSmallSubmodules ρ C).lift (kernel.ι _) (smallSupport_finiteRestriction ρ C K)

/-- The fixed-support map retains exactly its literal ambient small cochain. -/
theorem smallSupportToFinite_forget (K : Compacts OrbitSpace) :
    smallSupportToFinite ρ C K ≫ (finiteRestrictionSmallSubmodules ρ C).inclusion =
      kernel.ι (smallSupportRestriction ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge K) :=
  (finiteRestrictionSmallSubmodules ρ C).lift_inclusion _ _

/-- The genuine fixed-support map to finite-restriction cochains is degreewise injective. -/
theorem smallSupportToFinite_injective (K : Compacts OrbitSpace) (n : ℕ) :
    Function.Injective ((smallSupportToFinite ρ C K).f n) := by
  intro x y h
  apply (ModuleCat.mono_iff_injective ((kernel.ι (smallSupportRestriction ρ
    (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen)
      C.covers.ge K)).f n)).mp inferInstance
  exact congrArg Subtype.val h

/-- Actual support enlargement and the finite-restriction inclusion commute literally. -/
theorem smallSupportToFinite_natural (K L : Compacts OrbitSpace) (hKL : K ≤ L) :
    smallSupportMap ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge K L hKL ≫ smallSupportToFinite ρ C L =
        smallSupportToFinite ρ C K := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun f => (f.f n).hom x)
    (smallSupportMap_forget ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge K L hKL)

/-- The finite-restriction small complex is a genuine cocone of the actual compact relative kernels. -/
def smallFiniteCocone : Cocone (smallSupportDiagram ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge) where
  pt := finiteRestrictionSmallComplex ρ C
  ι := {
    app := smallSupportToFinite ρ C
    naturality K L f := by
      change smallSupportMap ρ _ _ _ K L (leOfHom f) ≫ smallSupportToFinite ρ C L =
        smallSupportToFinite ρ C K ≫ 𝟙 _
      rw [Category.comp_id]
      exact smallSupportToFinite_natural ρ C K L (leOfHom f) }

/-- Every actual finite-restriction small cochain occurs in a genuine compact relative kernel. -/
theorem smallFiniteCocone_representative (n : ℕ) (x : (finiteRestrictionSmallComplex ρ C).X n) :
    ∃ K : Compacts OrbitSpace, ∃ y : (smallSupport ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge K).X n,
        (smallSupportToFinite ρ C K).f n y = x := by
  obtain ⟨K,hK⟩ := (finiteRestriction_iff_exists_complement_kernel ρ C n x.val).mp x.property
  obtain ⟨y,hy⟩ := cochainKernel_element (smallSupportRestriction ρ
    (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen)
      C.covers.ge K) n x.val hK
  exact ⟨K,y,Subtype.ext hy⟩

/-- The actual compact relative small-cohomology colimit is the finite-restriction small cohomology. -/
def smallCompactFiniteIso (n : ℕ) :
    colimit (smallCompactDiagram ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n) ≅
        (finiteRestrictionSmallComplex ρ C).homology n :=
  filteredHomologyIso _ (smallFiniteCocone ρ C) (smallSupportToFinite_injective ρ C)
    (smallFiniteCocone_representative ρ C) n

/-- The compact-colimit isomorphism retains the actual fixed-support inclusion on every class. -/
theorem smallCompactFiniteIso_ι (n : ℕ) (K : Compacts OrbitSpace) :
    colimit.ι (smallCompactDiagram ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n) K ≫
        (smallCompactFiniteIso ρ C n).hom = homologyMap (smallSupportToFinite ρ C K) n :=
  filteredHomologyMap_ι _ (smallFiniteCocone ρ C) n K

/-- The genuine compact-colimit identification preserves the exact support-forgetting map. -/
theorem smallCompactFiniteIso_forget (n : ℕ) :
    (smallCompactFiniteIso ρ C n).hom ≫ homologyMap (finiteRestrictionSmallSubmodules ρ C).inclusion n =
      colimit.desc _ (smallCompactForgetCocone ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n) := by
  apply colimit.hom_ext
  intro K
  erw [←Category.assoc,smallCompactFiniteIso_ι,←homologyMap_comp,smallSupportToFinite_forget,colimit.ι_desc]
  rfl

end TernaryPoly.SmoothSingularGlobal
