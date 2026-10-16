module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Dimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.ParityHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.JointGen
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Petersson.Semisimple

@[expose] public section


/-!
# The local upper bound `2` at the bad line of level three

At the bad line (trivial character) the local joint generalized eigenspace of a system of Hecke
eigenvalues `c` with `‖c(T_2) - 1‖ ≤ 3/4` embeds, through the edge map of `BadLineBound`, into the
joint generalized eigenspace of the level-three Hecke operators on `H¹(Γ₁'(3), Sym^{n+1})`. Given
injectivity of the parity-projected period map `levelPeriodMap (n + 1) 0`
 (shared with the good plane), its image is the parabolic
cohomology, it intertwines `T_p` with the classical Hecke operator, and the classical joint
generalized eigenspace has dimension at most two (Petersson semisimplicity and Atkin–Lehner at
three). Hence `LocalUpperBound n trivialCharacter c .line false 2`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.LevelThree.BadLineUpper

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke (levelThreeHecke)

/-- **The local upper bound `2` at the bad line** (trivial character, `3 ≤ n`), given injectivity of
the parity-projected period map `levelPeriodMap (n + 1) 0`. -/
theorem localUpperBound_badLine_two (n : ℕ) (hn : 3 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (hinj : Function.Injective (levelPeriodMap (n + 1) 0)) :
    Separation.LocalUpperBound n trivialCharacter c .line false 2 := by
  have hm : 0 < n + 1 := Nat.succ_pos n
  have hpos : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) + 2 := by omega
  have : FiniteDimensional ℂ (S (n + 1)) :=
    SturmBound.cuspForm_finiteDimensional (((n + 1 : ℕ) : ℤ) + 2)
  have hrange := LevelThreePeriodDimension.levelPeriodMap_range_eq_parabolic_of_injective
    (m := n + 1) (e := 0) hm hinj
  exact BadLineBound.localUpperBound_badLine_two_of_period hn c hc
    (fun p : BadLineBound.Away => levelThreeHecke (((n + 1 : ℕ) : ℤ) + 2) p.1 p.2)
    (levelPeriodMap (n + 1) 0) hinj
    (fun p v => by
      have h := LevelThreePeriodParityHecke.levelHecke_levelPeriodMap (m := n + 1) 0 p.1 p.2 hm v
      rw [neg_zero, zpow_zero, one_smul] at h
      exact h)
    hrange
    (fun eig => LevelThreeJointGen.finrank_jointGenEigenspace_le_two hpos
      (LevelThreePeterssonSemisimple.levelThree_semisimple (((n + 1 : ℕ) : ℤ) + 2)) eig)

end TernaryPeriodPolynomials.LevelThree.BadLineUpper
