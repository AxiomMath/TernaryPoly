module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneCharacter
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly

@[expose] public section


/-!
# Local finiteness at the good plane of level three

`Separation.LocalJointFinite D hecke hhecke .plane true` asks, for a nonzero associate
pair, for some bound `m` on the local joint generalized eigenspace of the pair character at the
good-plane cusp. The local joint eigenspace embeds (`GoodPlaneJoint`) into the classical
level-three joint eigenspace `levelJoint n c ⊆ H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`, a subspace of a
finite-dimensional space; so `m = dim (levelJoint n c)` works. This is stated for every character
`χ` with `χ(-1_∞) = 1`, in particular for the trivial character.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneFinite

open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThree.GoodPlaneCharacter (signValue)

/-- **Local finiteness at the good plane for characters with `χ(-1_∞) = 1`** (`n > 0`). -/
theorem localJointFinite_plane_true_of_signValue_one {n : ℕ} (hn : 0 < n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (h : signValue D.chi = 1) : LocalJointFinite D hecke hhecke .plane true := by
  intro _
  exact ⟨Module.finrank ℂ (GoodPlaneJoint.levelJoint n (pairCharacter D hecke hhecke)),
    GoodPlaneCharacter.localUpperBound_of_signValue_one D.chi h n hn _ _ le_rfl⟩

/-- **Local finiteness at the good plane for the trivial character** (`n > 0`): the exact
`LocalJointFinite` shape. -/
theorem localJointFinite_plane_true_of_trivial {n : ℕ} (hn : 0 < n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) : LocalJointFinite D hecke hhecke .plane true := by
  refine localJointFinite_plane_true_of_signValue_one hn D hecke hhecke ?_
  calc signValue D.chi = signValue trivialCharacter := by rw [hχ]
    _ = 1 := rfl

end TernaryPeriodPolynomials.LevelThree.GoodPlaneFinite
