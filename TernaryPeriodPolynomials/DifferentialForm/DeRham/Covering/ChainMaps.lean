module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactSupport

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set SmoothLocalDeRham SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- The actual compact-support complex includes into the ordinary covering complex. -/
def compactInclusion {U : Set OrbitSpace} (hU : IsOpen U) :
    compactCoveringComplex ρ hU ⟶ coveringComplex ρ hU :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (compactSupportSubmodule ρ U n).subtype) (by
    intro n
    simp only [compactCoveringComplex, coveringComplex, CochainComplex.of_d]
    rfl)

/-- Genuine quotient restriction as a morphism of cochain complexes. -/
def restrictionChainMap {U V : Set OrbitSpace} (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) :
    coveringComplex ρ hU ⟶ coveringComplex ρ hV :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (restrictEquivariant ρ hVU n)) (by
    intro n
    simp only [coveringComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact (restrictEquivariant_d ρ hU hV hVU w).symm)

/-- The genuine local trivialization as a morphism to the actual smooth chart complex. -/
def chartRestrictionChainMap (S : Space) :
    coveringComplex ρ (quotientChart S).open_source ⟶ complex (F := F) (quotientChart S).open_target :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (chartRestrict ρ S n)) (by
    intro n
    simp only [coveringComplex, complex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact (chartRestrict_d ρ S w).symm)

def chartExtensionChainMap (S : Space) :
    complex (F := F) (quotientChart S).open_target ⟶ coveringComplex ρ (quotientChart S).open_source :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (chartExtend ρ S n)) (by
    intro n
    simp only [coveringComplex, complex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact (chartExtend_d ρ S w).symm)

/-- Isomorphism of the actual covering de Rham complex with ordinary forms on each lifting chart. -/
def chartComplexIso (S : Space) :
    coveringComplex ρ (quotientChart S).open_source ≅ complex (F := F) (quotientChart S).open_target where
  hom := chartRestrictionChainMap ρ S
  inv := chartExtensionChainMap ρ S
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact chartExtend_restrict ρ S w
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact chartRestrict_extend ρ S w

end TernaryPoly.SmoothCoveringDeRham
