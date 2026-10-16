module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Duality
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapOpen

@[expose] public section



/-!
# Locality for the Poincaré duality of an oriented manifold: the support lemma

If a homology class of the base lies in the image of an open subset `D`, its dual in compact-support
cohomology is the extension by zero of the dual class on `D` (`dual_of_open`), hence it has a representative
cochain supported in a compact subset of `D` (`dual_supported_in_open`).  Both are formal consequences of
the isomorphism `manifold_compactCap_isIso` for the open manifold `D` and of the naturality of the compact cap
for extension by zero (`compactCapMap_open_canonical`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly TernaryPoly.RationalManifoldCompact
  TernaryPoly.SingularLocalSupport TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCompactDuality TernaryPoly.RationalLocalOrientation
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall

section
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [SecondCountableTopology B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  (D : Opens B) [ChartedSpace H D]

/-- **Support lemma.**  If a homology class of the base is the image of a class of an open subset
`D`, its Poincaré dual in compact-support cohomology is the extension by zero of the dual class on
`D`. -/
theorem dual_of_open (a b : ℕ) (hab : a + b = n + 2)
    (zD : (coveringLocalChains (restrictedProjection p D) V).homology b) :
    ∃ xD : compactCohomology (restrictedProjection p D) V a,
      compactCapMap p V n e o a b hab (openExtension p V D a xD) =
        homologyMap (openLocalChainMap p V D) b zD := by
  let _ : IsCancelSMul G E := hp.out.isCancelSMul
  have hiso := manifold_compactCap_isIso (restrictedProjection p D) V n
    (H := H) e (openOrientation n e o D) a b hab
  set f := compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) a b hab with hf
  refine ⟨inv f zD, ?_⟩
  have h := compactCapMap_open_canonical p V n e o D a b hab
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) (inv f zD)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  rw [h']
  congr 1
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (IsIso.inv_hom_id f)) zD

/-- **Support lemma, fixed-support form.**  A class of the base lying in the image of an open
subset `D` has a dual represented by a cohomology class with support in a compact `K ⊆ D`. -/
theorem dual_supported_in_open (a b : ℕ) (hab : a + b = n + 2)
    (zD : (coveringLocalChains (restrictedProjection p D) V).homology b) :
    ∃ (K : Compacts B) (_ : (K : Set B) ⊆ D)
      (y : (supportCochains p V (K : Set B)).homology a),
      compactCapMap p V n e o a b hab (compactClassMap p V K a y) =
        homologyMap (openLocalChainMap p V D) b zD := by
  obtain ⟨xD, hxD⟩ := dual_of_open p V n e o D a b hab zD
  obtain ⟨K0, y0, hy0⟩ := Concrete.colimit_exists_rep
    (compactCohomologyDiagram (restrictedProjection p D) V a) xD
  refine ⟨openCompactImage D K0, openCompactImage_subset D K0,
    (openSupportIso p V D K0 a).inv y0, ?_⟩
  have h1 : compactClassMap p V (openCompactImage D K0) a ((openSupportIso p V D K0 a).inv y0) =
      openExtension p V D a xD := by
    rw [← hy0]
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (openExtension_classMap p V D K0 a)) y0).symm
  rw [h1]
  exact hxD

end

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
