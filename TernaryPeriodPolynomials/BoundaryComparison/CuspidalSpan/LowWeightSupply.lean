module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.CuspidalSupply

@[expose] public section


/-!
# The cuspidal supply at the excluded weight (`n = 1`, `k = 0`)

`CuspidalSupply.lean`'s hypothesis `h` ranges over every `k` with `n = 2 * k + 1`. This file
closes the `k = 0` branch (`n = 1`) directly and unconditionally: the input is a level-one cusp
form `f` of weight `-2 * hw 1 = 4`, and `dim S_4(SL₂(ℤ)) = 0` (Mathlib's
`CuspForm.rank_eq_zero_of_weight_lt_twelve`, already used identically elsewhere in this project,
e.g. `Proofs/AxiomCodeLevelThree/SturmBound.lean`), so `f = 0`; the zero element of
`automorphicPlaneSpan n` then trivially realizes the (necessarily zero) period class of `f`.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.LevelOneHecke
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Any level-one cusp form of weight exactly `4` is zero (`dim S_4(SL₂(ℤ)) = 0`). Mirrors the
proof idiom of `Proofs/AxiomCodeLevelThree/SturmBound.lean`'s `levelOne_eq_zero_of_isBigO`
base case. -/
theorem cuspForm_eq_zero_of_weight_eq_four {w : ℤ} (hw4 : w = 4) (f : CuspForm levelOne w) :
    f = 0 := by
  subst hw4
  obtain ⟨scalar, scalar_nonzero, scalar_zero⟩ :=
    rank_eq_zero_iff.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num : (4 : ℤ) < 12)) f
  exact (smul_eq_zero.mp scalar_zero).resolve_left scalar_nonzero

/-- Transport of `0` along a dependent equality of cohomological degrees is `0`. -/
theorem transport_H1_zero {σ : ℤ} {a b : ℕ} (heq : a = b) :
    heq ▸ (0 : groupCohomology.H1 (arithmeticBinaryRep a σ)) =
      (0 : groupCohomology.H1 (arithmeticBinaryRep b σ)) := by
  subst heq; rfl

/-- **The cuspidal supply at the excluded weight `n = 1` (`k = 0`).** The zero element of
`automorphicPlaneSpan n` realizes the (necessarily zero) period class of every weight-`4`
level-one cusp form; shaped to match `CuspidalSupply.lean`'s hypothesis `h` at `k = 0`. -/
theorem cuspidalSupply_weightFour (n : ℕ) (hn : 0 < n) (hodd : Odd n) (hnk : n = 2 * 0 + 1)
    (f : CuspForm levelOne (-2 * hw (0 + 1))) :
    ∃ b ∈ automorphicPlaneSpan n, cuspRes n trivialCharacter .plane true b = 0 ∧
      edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false b) =
        (show 2 * (0 + 1) = n + 1 by omega) ▸ per (0 + 1) (-1) f := by
  have hf0 : f = 0 := cuspForm_eq_zero_of_weight_eq_four (by norm_num [hw]) f
  have ecusp : cuspRes n trivialCharacter .plane false
      (0 : StratumH2 n trivialCharacter .plane) = 0 := map_zero _
  have ebad : edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false
      (0 : StratumH2 n trivialCharacter .plane)) = 0 := by
    rw [ecusp]; exact map_zero _
  have eper : per (0 + 1) (-1) f = 0 := by rw [hf0]; exact map_zero _
  refine ⟨0, Submodule.zero_mem _, by simp, ?_⟩
  rw [ebad, eper]
  exact (transport_H1_zero _).symm

end TernaryPeriodPolynomials.Argument.CuspidalSpan
