module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Vectors
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.BadLineFinite

@[expose] public section


/-!
# The bad-line level subspace is the level-three subspace

Workstream SC builds the finite part of a bad-line source (`badLineVector`, on the identity cell
`P_line(𝔸_f) · K₁`) from vectors of `badLevelSubspace σ`, the vectors fixed by every `k ∈ GL₂(ℤ̂)`
with `diag(1, k)` in the finite level.  By `planeLeviLevel_iff_lineLevi_mem` this is exactly the
level-three subspace `levelThreeValues σ` (`k₁₀ ≡ 0`, `k₁₁ ≡ 1` modulo three), which is also the
Levi level of the good plane.  So the level-three weight vectors `levelThreeWeightVectors` feed both
SC's bad-line cell and the good-plane cell `goodPlaneVector`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction (badLevelSubspace)
open TernaryPeriodPolynomials.MultiplicityOne (levelThreeValues)

namespace TernaryPeriodPolynomials.LevelThreeSource

/-- **The bad-line Levi level is the level-three level.** -/
theorem levelThreeValues_eq_badLevelSubspace (σ : CuspidalRepresentation) :
    levelThreeValues σ = badLevelSubspace σ := by
  ext v
  constructor
  · intro hv k hk
    exact hv k ((planeLeviLevel_iff_lineLevi_mem k).mpr hk)
  · intro hv k hk
    exact hv k ((planeLeviLevel_iff_lineLevi_mem k).mp hk)

/-- A level-three weight vector lies in SC's bad-line level subspace. -/
theorem mem_badLevelSubspace_of_weightVector {σ : CuspidalRepresentation} {weight : ℤ}
    {v : σ.smooth} (hv : v ∈ levelThreeWeightVectors σ weight) :
    v.val ∈ badLevelSubspace σ := by
  rw [← levelThreeValues_eq_badLevelSubspace]
  exact hv.1

end TernaryPeriodPolynomials.LevelThreeSource
