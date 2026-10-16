module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.StalkExactness
public import Mathlib.Topology.Sheaves.Sheafify

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Opposite TopologicalSpace Set
open TopCat.Presheaf SymmetricSpaceCovering

/-- The genuine sheafification unit induces an isomorphism on every real-module stalk. -/
def quotientSheafificationStalkIso (q : OrbitSpace) :
    stalkFunctor (ModuleCat ℝ) q ≅
      quotientSheafification ⋙ TopCat.Sheaf.forget (ModuleCat ℝ) (TopCat.of OrbitSpace) ⋙
        stalkFunctor (ModuleCat ℝ) q := by
  let η := Functor.whiskerRight (toSheafification (Opens.grothendieckTopology (TopCat.of OrbitSpace))
    (ModuleCat ℝ)) (stalkFunctor (ModuleCat ℝ) q)
  have : ∀ P, IsIso (η.app P) := by
    intro P
    change IsIso ((stalkFunctor (ModuleCat ℝ) q).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of OrbitSpace)) P))
    exact stalkFunctor_map_unit_toSheafify_isIso q (ModuleCat ℝ) P
  have : IsIso η := NatIso.isIso_of_isIso_app η
  let e := asIso η
  exact e

/-- Local stalk exactness of the actual presheaf sequence proves exactness of its genuine
sheafification; this is proved using the real sheafification unit, not an assumed descent map. -/
theorem sheafification_exact_of_stalk_exact
    (S : ShortComplex (TopCat.Presheaf (ModuleCat ℝ) (TopCat.of OrbitSpace)))
    (h : ∀ q : OrbitSpace, (S.map (stalkFunctor (ModuleCat ℝ) q)).Exact) :
    (S.map quotientSheafification).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro q
  exact ShortComplex.exact_of_iso (S.mapNatIso (quotientSheafificationStalkIso q)) (h q)

end TernaryPoly.SmoothSingularGlobal
