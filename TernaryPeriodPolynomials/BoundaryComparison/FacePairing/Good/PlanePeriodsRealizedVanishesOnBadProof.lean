module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.OddBadLineAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.PlaneSupply
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.CutoffPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelThree

@[expose] public section


/-!
# Discharging `GoodPlanePeriodsRealizedVanishesOnBad` (odd `n`)

Proves `OddBadLineAnchor.GoodPlanePeriodsRealizedVanishesOnBad`, the input consumed by
`OddBadLineAnchor.face_pairing_perfect_odd_badLine`.

This file uses
`TernaryPeriodPolynomials.Separation.exists_cutoff_plane`. That lemma is a
support/cutoff statement about which single cusp-flag coordinate of a boundary-summand witness
is kept vs. killed (it produces a *different element of the same summand* agreeing with the
original at one flag and vanishing at the other); it is not a Hecke-isotypical projector and
is not used here to separate Hecke eigenspaces. The same primitive, applied to the identical
cutoff-and-span-lift pattern, is already used by the (committed, predecessor) file
`TernaryPeriodPolynomials/BoundaryComparison/CuspidalSpan/BadPlaneSupplyPiece.lean`, and
`TernaryPeriodPolynomials/BoundaryComparison/GoodPlaneSpan/PlaneSupply.lean` — whose unconditional
theorem `goodPlanePeriodsRealized` is the other main input consumed below — itself already
opens `AxiomCodeSeparation` and is built on it.

## Proof idea

`GoodPlanePeriodsRealized` (already proved unconditionally, `goodPlanePeriodsRealized`) says
every element of `parabolicH1 (levelRep (n+1) (-1)) (upper 1) (lower 1)` is the good-plane edge
of *some* `automorphicPlaneSpan` witness (with no control on the bad-flag residue). The bridge
`thetaPar_surjective` identifies `parabolicCrossedH1 (levelRep (n+1) (-1))` with the image, under
the injective transport `thetaH1`, of exactly that `parabolicH1 (upper 1) (lower 1)` (via
`parabolicCrossedH1_eq`). So every target class `cl` lifts to a good-plane-edge witness `ξ'₀`;
the new lemma `exists_cutoff_automorphicPlaneSpan` (`Submodule.span_induction` on the generators
of `automorphicPlaneSpan`, using that `cuspRes` is a bundled linear map) replaces `ξ'₀` by a
span witness `ξ'` with the *same* good-flag residue and *zero* bad-flag residue, as required.
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers (CrossedH1)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3 (goodPlaneEdge)
open TernaryPeriodPolynomials.LevelThree.TwoGenerator (parabolicH1)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd
  (thetaH1 thetaPar thetaPar_surjective thetaPar_coe)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1 parabolicCrossedH1_eq)
open TernaryPeriodPolynomials.Argument (automorphicPlaneSpan)
open TernaryPeriodPolynomials.Argument.GoodPlaneSpan (goodPlanePeriodsRealized)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **Cutoff lifted to the automorphic plane span.** Any span witness can be replaced by another
span witness with the same `good`-flag cusp residue and zero `(!good)`-flag cusp residue. -/
theorem exists_cutoff_automorphicPlaneSpan {n : ℕ} (good : Bool)
    {ξ : StratumH2 n trivialCharacter .plane} (hξ : ξ ∈ automorphicPlaneSpan n) :
    ∃ ξ' ∈ automorphicPlaneSpan n,
      cuspRes n trivialCharacter .plane good ξ' = cuspRes n trivialCharacter .plane good ξ ∧
        cuspRes n trivialCharacter .plane (!good) ξ' = 0 := by
  induction hξ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨D, hD⟩ := hx
      obtain ⟨a', ha', hkeep, hkill⟩ :=
        TernaryPeriodPolynomials.Separation.exists_cutoff_plane
          D.inducingData good hD
      exact ⟨a', Submodule.subset_span ⟨D, ha'⟩, hkeep, hkill⟩
  | zero => exact ⟨0, Submodule.zero_mem _, rfl, map_zero _⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨x', hx', hxkeep, hxkill⟩ := ihx
      obtain ⟨y', hy', hykeep, hykill⟩ := ihy
      refine ⟨x' + y', Submodule.add_mem _ hx' hy', ?_, ?_⟩
      · rw [map_add, map_add, hxkeep, hykeep]
      · rw [map_add, hxkill, hykill, add_zero]
  | smul c x _ ihx =>
      obtain ⟨x', hx', hxkeep, hxkill⟩ := ihx
      refine ⟨c • x', Submodule.smul_mem _ c hx', ?_, ?_⟩
      · rw [map_smul, map_smul, hxkeep]
      · rw [map_smul, hxkill, smul_zero]

/-- **`GoodPlanePeriodsRealizedVanishesOnBad`, proved.** Combines the unconditional good-plane
supply (`goodPlanePeriodsRealized`), the `thetaH1`/`parabolicCrossedH1` bridge
(`thetaPar_surjective`, `parabolicCrossedH1_eq`), and `exists_cutoff_automorphicPlaneSpan`. -/
theorem goodPlanePeriodsRealizedVanishesOnBad_proof (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    GoodPlanePeriodsRealizedVanishesOnBad n hn hodd := by
  intro cl hcl
  obtain ⟨x, hx⟩ := thetaPar_surjective hodd ⟨cl, hcl⟩
  have hxmem : (x : CrossedH1 (levelRep (n + 1) (-1))) ∈
      parabolicH1 (levelRep (n + 1) (-1)) (upper 1) (lower 1) := by
    rw [← parabolicCrossedH1_eq (levelRep (n + 1) (-1))]
    exact x.2
  obtain ⟨ξ'₀, hξ'₀, hedge⟩ :=
    goodPlanePeriodsRealized n hn (x : CrossedH1 (levelRep (n + 1) (-1))) hxmem
  obtain ⟨ξ', hξ', hkeep, hkill⟩ := exists_cutoff_automorphicPlaneSpan (n := n) true hξ'₀
  have hval : thetaH1 hodd (x : CrossedH1 (levelRep (n + 1) (-1))) = cl := by
    rw [← thetaPar_coe hodd x]
    exact congrArg Subtype.val hx
  refine ⟨ξ', hξ', hkill, ?_⟩
  rw [hkeep, hedge]
  exact hval

end TernaryPeriodPolynomials.Argument.FacePairing
