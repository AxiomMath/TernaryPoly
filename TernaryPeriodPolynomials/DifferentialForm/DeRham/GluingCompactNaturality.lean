module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering CategoryTheory
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U V U' V' : Set OrbitSpace}
  (hU : IsOpen U) (hV : IsOpen V) (hU' : IsOpen U') (hV' : IsOpen V')
  (hUU' : U ⊆ U') (hVV' : V ⊆ V')

def compactPairExtension : compactPairComplex ρ hU hV ⟶ compactPairComplex ρ hU' hV' :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    ((compactZeroExtend hU hUU' n).prodMap (compactZeroExtend hV hVV' n))) (by
      intro n
      simp only [compactPairComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      exact Prod.ext (compactZeroExtend_d hU hU' hUU' p.1) (compactZeroExtend_d hV hV' hVV' p.2))

/-- The compact Mayer-Vietoris complexes are covariantly natural under actual zero extension
for inclusions of pairs of quotient opens. -/
def compactSequenceExtension : compactSequence ρ hU hV ⟶ compactSequence ρ hU' hV' where
  τ₁ := compactExtensionChainMap (hU.inter hV) (hU'.inter hV') (inter_subset_inter hUU' hVV')
  τ₂ := compactPairExtension ρ hU hV hU' hV' hUU' hVV'
  τ₃ := compactExtensionChainMap (hU.union hV) (hU'.union hV') (union_subset_union hUU' hVV')
  comm₁₂ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      apply Form.ext
      intro x hx
      rfl
    · apply Subtype.ext
      apply Subtype.ext
      apply Form.ext
      intro x hx
      rfl
  comm₂₃ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    apply Subtype.ext
    apply Form.ext
    intro x hx
    rfl

/-- Naturality of the compact-support connecting homomorphism under extension of open pairs. -/
theorem compactConnecting_natural (n : ℕ) :
    compactConnecting ρ hU hV n ≫
      HomologicalComplex.homologyMap
        (compactExtensionChainMap (ρ := ρ) (hU.inter hV) (hU'.inter hV') (inter_subset_inter hUU' hVV')) (n + 1) =
      HomologicalComplex.homologyMap
        (compactExtensionChainMap (ρ := ρ) (hU.union hV) (hU'.union hV') (union_subset_union hUU' hVV')) n ≫
        compactConnecting ρ hU' hV' n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (compactSequenceExtension ρ hU hV hU' hV' hUU' hVV')
    (compactSequence_shortExact ρ hU hV) (compactSequence_shortExact ρ hU' hV') n (n + 1) rfl

/-- The actual compact-support-to-ordinary map on de Rham cohomology. -/
def compactToOrdinaryCohomology (n : ℕ) :
    (compactCoveringComplex ρ hU).homology n ⟶ (coveringComplex ρ hU).homology n :=
  HomologicalComplex.homologyMap (compactInclusion ρ hU) n

/-- Forgetting support is compatible with zero extension followed by ordinary restriction. -/
theorem compactToOrdinary_extension_restriction (n : ℕ) :
    HomologicalComplex.homologyMap (compactExtensionChainMap (ρ := ρ) hU hU' hUU') n ≫
      compactToOrdinaryCohomology ρ hU' n ≫
      HomologicalComplex.homologyMap (restrictionChainMap ρ hU' hU hUU') n =
        compactToOrdinaryCohomology ρ hU n := by
  unfold compactToOrdinaryCohomology
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    compactInclusion_extension_restriction hU hU' hUU']

end TernaryPoly.SmoothDeRhamGluing
