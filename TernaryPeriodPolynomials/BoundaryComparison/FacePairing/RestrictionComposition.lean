module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RelativeTwoCocycleNormalization

@[expose] public section


/-!
# Restriction along a composite group homomorphism (M1a, bridging step)

`twoCohomologyRestriction` (`RelativeTwoCocycleNormalization.lean`) restricts a degree-two group
cohomology class along a monoid homomorphism, via Mathlib's `groupCohomology.map` applied to the
identity morphism on the restricted representation. Restricting along a composite `f.comp g` is
the same as restricting along `f` and then along `g`: this is a direct consequence of Mathlib's
functoriality lemma `groupCohomology.map_comp`, specialized to identity morphisms (using that
`Rep.res` composes definitionally, `Rep.res (f.comp g) representation = Rep.res g (Rep.res f
representation)`, by `rfl`).
-/

noncomputable section

open CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- Restricting a degree-two cohomology class along a composite homomorphism `f.comp g` is the
same as restricting along `f` and then along `g`. -/
theorem twoCohomologyRestriction_comp {G H K : Type} [Group G] [Group H] [Group K]
    (f : H →* K) (g : G →* H) (representation : Rep ℂ K)
    (x : groupCohomology.H2 representation) :
    twoCohomologyRestriction (f.comp g) representation x =
      twoCohomologyRestriction g (Rep.res f representation)
        (twoCohomologyRestriction f representation x) := by
  have e1 : Rep.resMap g (𝟙 (Rep.res f representation)) =
      𝟙 (Rep.res g (Rep.res f representation)) := rfl
  have key := groupCohomology.map_comp f g (𝟙 (Rep.res f representation))
    (𝟙 (Rep.res g (Rep.res f representation))) 2
  simp only [e1, Category.comp_id] at key
  have key' := congrArg (fun φ => φ.hom x) key
  show (groupCohomology.map (f.comp g) (𝟙 (Rep.res (f.comp g) representation)) 2).hom x = _
  exact key'

end TernaryPeriodPolynomials.Argument.FacePairing
