module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSNormalForm

@[expose] public section


/-!
# Normal form with both `U = 0` and vanishing mixed values

Formalized by Claude Sonnet 5.5.

`exists_normal_form_mixed`: under `H²(L, -) = 0`, every class `x` of `H²(E, W)` restricting to zero on the radical has a relative two-cocycle representative `z`
with `z(s a, s b) = 0` AND `z(inl r, s l) = 0` for all `a, b, l, r`.  (Apply `splitMixedNormalize` to the `U = 0` representative: it changes the cocycle by the
coboundary of a primitive vanishing on `inl N` and on `s L`, so `U` stays `0` while the mixed values become `0`.)  No lift to `Z¹(N, W)` is needed.
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable {N E L : Type} [Group N] [Group E] [Group L]

theorem exists_normal_form_mixed {extension : GroupExtension N E L} (splitting : extension.Splitting) (W : Rep ℂ E)
    (hvan : ∀ (A : Rep ℂ L) (x : groupCohomology.H2 A), x = 0)
    (x : (twoCohomologyRestriction extension.inl W).ker) :
    ∃ z : relativeTwoCocycles extension.inl W,
      relativeTwoCocycleClass extension.inl W z = x ∧ (∀ a b : L, z.val (splitting a, splitting b) = 0) ∧
      ∀ (r : N) (l : L), z.val (extension.inl r, splitting l) = 0 := by
  obtain ⟨z0, hz0, hU⟩ := exists_normal_form splitting W hvan x
  refine ⟨splitMixedNormalize splitting W z0, ?_, ?_, splitMixedNormalize_mixed splitting W z0⟩
  · apply Subtype.ext
    rw [← hz0]
    exact splitMixedNormalize_H2 splitting W z0
  · intro a b
    rw [splitMixedNormalize_val]
    change z0.val (splitting a, splitting b) +
      twoBoundaryCycle W (splitMixedPrimitive splitting W z0) (splitting a, splitting b) = 0
    rw [twoBoundaryCycle_apply, ← map_mul, splitMixedPrimitive_splitting, splitMixedPrimitive_splitting,
      splitMixedPrimitive_splitting, map_zero, hU a b]
    abel

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
