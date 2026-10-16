module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.OddCase
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.ParabolicPeriod

@[expose] public section


/-!
# `PlanePeriodParabolicRealized`, reduced to the cuspidal supply at level one

`ParabolicPeriod.lean`'s docstring describes, but does not state as a theorem,
`parabolicPeriodRealized_of_cuspFormRealized`: realizing *every* parabolic class of
`H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` (`OddCase.lean`'s `PlanePeriodParabolicRealized`) follows from
realizing the period class `per r (-1) f` of *every individual* level-one cusp form `f` of weight
`n + 3`, via `parabolicH1_le_range_per` (every parabolic class *is* `per r (-1) f` for some `f`).
This file states and proves that reduction as an actual theorem, closing the gap between the
docstring's prose and the Lean code.

## What this does **not** close

The hypothesis `h` below — "the cuspidal supply": for every level-one cusp form `f`, a bad-plane,
good-vanishing element of `automorphicPlaneSpan n` whose edge is exactly `per r (-1) f` — is **not**
discharged here. No existing "classical level-one cusp form ⟹ automorphic
cuspidal datum" construction anywhere in the active tree:

* `Proofs/SphericalDetection/` (642 files) builds the *converse* direction only (automorphic datum
  ⟹ classical period/Fourier data: `cuspClassicalArithmeticPeriodMap`, `binaryEndpointHolomorphicForm`,
  `binaryHilbertCoefficient`, etc. — all consume a `cusp : CuspidalRepresentation`; none produce one
  from a classical form).
* `Definitions/ManuscriptDecompositionDefs.lean`'s `SphericalCusp`/`BadPlaneRepresentative` and the
  top-level theorems `BadPlaneSupportSphericity.bad_plane_support_sphericity` (a representative
  forces sphericity — the necessary direction) and
  `BadPlaneSameConstituentRepresentative.bad_plane_same_constituent_representative` (a
  class-preserving "cut to the bad plane" tool for an *already-existing* good-vanishing boundary
  element) give exactly the vocabulary this gap needs, but neither constructs a new boundary element
  from a prescribed classical form.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.LevelOneHecke

/-- **The cuspidal supply at level one, reduction.** If every level-one cusp form `f` of weight
`n + 3` has its Eichler–Shimura period class `per r (-1) f` (`r := k + 1`, for `k` the witness that
`n` is odd) realized by a bad-plane, good-vanishing element of `automorphicPlaneSpan n`, then every
parabolic class is realized, i.e. `PlanePeriodParabolicRealized n hn hodd` holds. This formalizes the
equivalence described (but not proved) in `ParabolicPeriod.lean`'s docstring, via
`parabolicH1_le_range_per`. -/
theorem parabolicPeriodRealized_of_cuspFormRealized (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (h : ∀ (k : ℕ) (hnk : n = 2 * k + 1), ∀ f : CuspForm levelOne (-2 * hw (k + 1)),
      ∃ b ∈ automorphicPlaneSpan n, cuspRes n trivialCharacter .plane true b = 0 ∧
        edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false b) =
          (show 2 * (k + 1) = n + 1 by rw [hnk]; omega) ▸ per (k + 1) (-1) f) :
    PlanePeriodParabolicRealized n hn hodd := by
  obtain ⟨k, hk⟩ := hodd
  subst hk
  intro y hy
  obtain ⟨f, hf⟩ := parabolicH1_le_range_per (k + 1) (by omega) (-1) hy
  obtain ⟨b, hb, hbgood, hbedge⟩ := h k rfl f
  exact ⟨b, hb, hbgood, hbedge.trans hf⟩

end TernaryPeriodPolynomials.Argument.CuspidalSpan
