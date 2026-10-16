module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteSingularBicomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Subcomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularTotalExact

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SymmetricSpaceCovering

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  (C : CompactConvexCover)

/-- Cover-small cochains whose literal restrictions have finite nonzero tuple support.
Identification with the original compact relative model is a separate theorem. -/
def finiteRestrictionSmallSubmodules : CochainSubmodules
    (coveringSmallCochains ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) Set.univ C.covers.ge) where
  term n := (finiteFamilySubmodule (fun t : Fin 1 → C.Index =>
    (coveringCochains ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t)).X n)).comap
      (smallCechAugmentationDegree ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n)
  differential_mem n w hw := by
    have hc := congrArg (fun f => f.hom w)
      ((smallCechAugmentationChain ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge).comm n (n+1))
    have hv := congrArg (fun f : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) n 1 →ₗ[ℝ]
      SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) (n+1) 1 =>
        f (smallCechAugmentationDegree ρ (fun i => (C.sheet i).quotientDomain)
          (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n w))
      (singularCechBicomplex_vertical ρ (fun i => (C.sheet i).quotientDomain) 0 n)
    have he := hv.symm.trans hc
    exact (congrArg (fun z : SingularCechTerms ρ (fun i => (C.sheet i).quotientDomain) (n+1) 1 =>
      (familySupport z).Finite) he).mp (singularCechVertical_finiteSupport ρ C n 1 _ hw)

/-- The auxiliary actual small-singular complex with finite restriction support. -/
def finiteRestrictionSmallComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  (finiteRestrictionSmallSubmodules ρ C).toComplex

/-- The actual finite-restriction small augmentation on each degree. -/
def finiteSmallAugment (n : ℕ) : (finiteRestrictionSmallSubmodules ρ C).term n →ₗ[ℝ]
    (finiteSingularSubmodules ρ C).term 0 n where
  toFun w := ⟨smallCechAugmentationDegree ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n w.val,w.property⟩
  map_add' w z := Subtype.ext (map_add _ w.val z.val)
  map_smul' c w := Subtype.ext (map_smul _ c w.val)

/-- The actual finite small cochains augment the finite singular Čech column. -/
def finiteSmallColumnAugmentation : finiteRestrictionSmallComplex ρ C ⟶
    (finiteSingularBicomplex ρ C).X 0 :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (finiteSmallAugment ρ C n)) (by
    intro n
    simp only [finiteRestrictionSmallComplex,CochainSubmodules.toComplex,
      finiteSingularBicomplex,BicomplexSubmodules.toBicomplex,BicomplexSubmodules.column,
      CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact congrArg (fun f => f.hom w.val)
      ((smallCechAugmentationChain ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge).comm n (n+1)))

/-- Literal compatibility with the original small-cochain augmentation and actual inclusions. -/
theorem finiteSmallColumnAugmentation_forget : finiteSmallColumnAugmentation ρ C ≫
    (finiteSingularSubmodules ρ C).columnInclusion 0 =
      (finiteRestrictionSmallSubmodules ρ C).inclusion ≫
        smallCechAugmentationChain ρ (fun i => (C.sheet i).quotientDomain)
          (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  rfl

/-- Genuine horizontal closedness of the finite small augmentation. -/
theorem finiteSmallColumnAugmentation_horizontal : finiteSmallColumnAugmentation ρ C ≫
    (finiteSingularBicomplex ρ C).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have h := (singularCechTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge).augment_horizontal n w.val
  exact (congrArg (fun f => (f (finiteSmallAugment ρ C n w)).val)
    ((finiteSingularSubmodules ρ C).horizontal_eq 0 n)).trans h

/-- Actual finite small cochains augment the genuine finite-support singular bicomplex. -/
def finiteSmallTotalAugmentation : TotalAugmentation (finiteRestrictionSmallComplex ρ C)
    (finiteSingularBicomplex ρ C) where
  map := finiteSmallColumnAugmentation ρ C
  horizontal_zero := finiteSmallColumnAugmentation_horizontal ρ C

end TernaryPoly.SmoothSingularGlobal
