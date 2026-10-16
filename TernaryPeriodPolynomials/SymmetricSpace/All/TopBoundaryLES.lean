module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.CochainSequence

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceAllTopBoundary
open CategoryTheory HomologicalComplex

/-- An actual commuting square with isomorphic horizontal maps preserves surjectivity
between its two vertical maps. -/
theorem surjective_iff_of_iso_square {A B C D : ModuleCat.{0} ℚ}
    (e : A ≅ B) (f : C ≅ D) (u : B ⟶ D) (v : A ⟶ C)
    (h : e.hom ≫ u = v ≫ f.hom) :
    Function.Surjective u.hom ↔ Function.Surjective v.hom := by
  have hleft := Function.Surjective.of_comp_iff u.hom e.toLinearEquiv.surjective
  have hright := Function.Surjective.of_comp_iff' f.toLinearEquiv.bijective v.hom
  change Function.Surjective (e.hom ≫ u).hom ↔ _ at hleft
  change Function.Surjective (v ≫ f.hom).hom ↔ _ at hright
  rw [h] at hleft
  exact hleft.symm.trans hright

/-- Exactness of an actual cochain pair sequence makes its connecting map onto precisely
when the following relative-to-absolute map vanishes. -/
theorem connecting_surjective_iff_relative_zero
    {K L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (r : K ⟶ L) [Epi r] (n : ℕ) :
    Function.Surjective (RelativeCochainSequence.connecting r n).hom ↔
      RelativeCochainSequence.relativeMap r (n+1) = 0 := by
  rw [← LinearMap.range_eq_top,RelativeCochainSequence.range_connecting_eq_kernel_relative,
    LinearMap.ker_eq_top]
  exact ModuleCat.hom_ext_iff.symm

end TernaryPoly.SymmetricSpaceAllTopBoundary
