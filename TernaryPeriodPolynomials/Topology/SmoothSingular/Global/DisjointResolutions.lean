module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.DisjointCochainIso
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.DisjointForms
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ProductExact
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoverFormAugmentation
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularZero

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering
namespace DisjointQuotientCover
variable {V : Set OrbitSpace} {ι : Type} (U : DisjointQuotientCover V ι)

section Singular
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- Actual singular coefficient resolutions glue over a genuine disjoint quotient open cover.
The maps are the original coefficient augmentation and actual cochain restrictions. -/
theorem singularAugmentation_quasiIso
    (hq : ∀ i, QuasiIso (coveringSingularAugmentation ρ (U.domain i))) :
    QuasiIso (coveringSingularAugmentation ρ V) := by
  have hm : Mono (ModuleCat.ofHom (coefficientSingularMap ρ V)) :=
    (ModuleCat.mono_iff_injective _).mpr (coefficientSingularMap_injective ρ V)
  unfold coveringSingularAugmentation
  refine @augmentation_quasiIso_of_product_equivs ι (coveringCochains ρ V)
    (fun i => coveringCochains ρ (U.domain i)) (ModuleCat.of ℝ (coefficientSections ρ V))
    (fun i => ModuleCat.of ℝ (coefficientSections ρ (U.domain i)))
    (ModuleCat.ofHom (coefficientSingularMap ρ V)) _ hm
    (fun i => ModuleCat.ofHom (coefficientSingularMap ρ (U.domain i)))
    (fun i => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact coefficientSingularMap_closed ρ (U.domain i))
    (U.coefficientEquiv ρ) (U.cochainEquiv ρ)
    (fun n w i => congrFun (U.cochainEquiv_d ρ n w) i)
    (fun f i => coefficientSingularMap_restrict ρ (U.subset i) f) hq

end Singular
section Forms
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- Actual smooth coefficient resolutions glue over a genuine disjoint quotient open cover.
The proof uses actual form gluing and the literal exterior differential. -/
theorem formAugmentation_quasiIso (hV : IsOpen V)
    (hq : ∀ i, QuasiIso (coveringFormAugmentation ρ (U.isOpen_domain i))) :
    QuasiIso (coveringFormAugmentation ρ hV) := by
  have hm : Mono (ModuleCat.ofHom (coefficientFormMap ρ hV)) :=
    (ModuleCat.mono_iff_injective _).mpr (coefficientForm_injective ρ hV)
  unfold coveringFormAugmentation
  refine @augmentation_quasiIso_of_product_equivs ι (coveringComplex ρ hV)
    (fun i => coveringComplex ρ (U.isOpen_domain i)) (ModuleCat.of ℝ (coefficientSections ρ V))
    (fun i => ModuleCat.of ℝ (coefficientSections ρ (U.domain i)))
    (ModuleCat.ofHom (coefficientFormMap ρ hV)) _ hm
    (fun i => ModuleCat.ofHom (coefficientFormMap ρ (U.isOpen_domain i)))
    (fun i => coveringCoefficientForm_closed ρ (U.isOpen_domain i))
    (U.coefficientEquiv ρ) (U.formEquiv ρ)
    (fun n w i => by
      simp only [coveringComplex, CochainComplex.of_d]
      exact congrFun (U.formEquiv_d ρ hV n w) i)
    (fun f i => coefficientForm_restrict ρ hV (U.isOpen_domain i) (U.subset i) f) hq

end Forms
end DisjointQuotientCover
end TernaryPoly.SmoothSingularGlobal
