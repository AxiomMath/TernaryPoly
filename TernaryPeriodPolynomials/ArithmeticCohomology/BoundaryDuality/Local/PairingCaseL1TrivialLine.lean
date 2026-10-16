module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelOneEigen
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembership
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly

@[expose] public section


/-!
# The line side of local nondegeneracy at the good line `L₁`, trivial character

For the trivial character and `3 ≤ n`, the Shapiro coordinate at the reference good line of a class
of the line summand lies in the local joint generalized eigenspace of the pair character, hence in
`ML` (`LocalUniqueness.localJoint_le_ML`), and its good-line edge `phiL` is a parabolic class of
`H¹(GL₂(ℤ), Sym^{n+1})` (`phiL_mem_parabolicH1`).  This file packages the edge image of the
coordinate as a linear map `lineEdge` from the line summand to the parabolic classes, shows that it
is an eigen-edge for every prime Hecke operator `T_p` (`p ≠ 3`) with the pair-character eigenvalue
(`lineEdge_eigen`: `x + p^{-(n+1)} T_p x = c_p x`, because the summand classes are genuine
eigenvectors), and that it is nonzero as soon as the coordinate is (`lineEdge_ne_zero`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership (trivialData)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (parabolicH1 phiL_mem_parabolicH1 parabolicPairing twistedPairing_goodLine_trivial)
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1 (arithmeticHecke)
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelOne (parabolicHecke)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)

variable {n : ℕ} {cusp : CuspidalRepresentation} {coh : Cohomological cusp n}
  {hecke : BoundaryHecke n trivialCharacter}
  {hhecke : ActualBoundaryHecke n trivialCharacter hecke}

/-- The pair character is within `3/4` of `1` at `T₂`. -/
theorem pair_two_sub_one (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥) :
    ‖pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp LocalUniqueness.two) - 1‖ ≤
      3 / 4 :=
  Separation.pairCharacter_two_sub_one_norm_le_of_trivial (trivialData cusp coh) rfl
    hecke hhecke hn hne

/-- The good-line coordinate of the line summand, as a linear map into `ML`. -/
def lineCoord (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥) :
    boundarySummand (trivialData cusp coh) .line →ₗ[ℂ] LocalUniqueness.ML n :=
  LinearMap.codRestrict (LocalUniqueness.ML n)
    ((cuspRes n trivialCharacter .line true).comp
      (boundarySummand (trivialData cusp coh) .line).subtype)
    (fun b => HeckeAdjointMembership.cuspRes_line_true_mem_ML cusp coh hecke hhecke hn hne b.2)

/-- The edge image of the good-line coordinate of a line summand class: a linear map into the
parabolic classes of `H¹(GL₂(ℤ), Sym^{n+1})`. -/
def lineEdge (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥) :
    boundarySummand (trivialData cusp coh) .line →ₗ[ℂ]
      parabolicH1 (arithmeticBinaryRep (n + 1) 0) :=
  LinearMap.codRestrict (parabolicH1 (arithmeticBinaryRep (n + 1) 0))
    ((LocalUniqueness.phiL n (by omega)).comp
      (lineCoord (hecke := hecke) (hhecke := hhecke) hn hne))
    (fun b => by
      have := phiL_mem_parabolicH1 n (by omega) (pairCharacter (trivialData cusp coh) hecke hhecke)
        (pair_two_sub_one (hecke := hecke) (hhecke := hhecke) hn hne)
        (y := cuspRes n trivialCharacter .line true b.1)
        (Separation.cuspRes_mem_localJoint_of_mem (trivialData cusp coh) hecke hhecke
          .line true b.2)
      exact this)

theorem lineEdge_coe (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)
    (b : boundarySummand (trivialData cusp coh) .line) :
    ((lineEdge (hecke := hecke) (hhecke := hhecke) hn hne b :
        parabolicH1 (arithmeticBinaryRep (n + 1) 0)) :
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) =
      LocalUniqueness.phiL n (by omega) (lineCoord (hecke := hecke) (hhecke := hhecke) hn hne b) :=
  rfl

/-- A line summand class is an eigenclass of the local operator of `T_p` at the good line. -/
theorem localOp_lineCoord (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (b : boundarySummand (trivialData cusp coh) .line) :
    localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line true
        (cuspRes n trivialCharacter .line true b.1) =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
        cuspRes n trivialCharacter .line true b.1 := by
  have h1 := cuspRes_hecke hecke hhecke (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
    .line true b.1
  have h2 := Separation.hecke_eq_pairCharacter_smul (trivialData cusp coh) hecke hhecke
    (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line b.2
  refine h1.symm.trans ?_
  exact (congrArg (cuspRes n trivialCharacter .line true) h2).trans (map_smul _ _ _)

theorem parabolic_eigen_of_coe (p : Nat.Primes) (c s : ℂ)
    (x : parabolicH1 (arithmeticBinaryRep (n + 1) 0))
    (h : (x : groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) +
        s • arithmeticHecke (n + 1) 0 p x =
      c • (x : groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0))) :
    x + s • parabolicHecke (n + 1) 0 p x = c • x :=
  Subtype.ext h

/-- **The edge image of a line summand class is an eigen-edge**: `x + p^{-(n+1)} T_p x = c_p x`. -/
theorem lineEdge_eigen (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)
    (p : Nat.Primes) (hp3 : p.val ≠ 3) (b : boundarySummand (trivialData cusp coh) .line) :
    lineEdge (hecke := hecke) (hhecke := hhecke) hn hne b +
        ((((p.val : ℕ) : ℂ)) ^ (n + 1))⁻¹ •
          parabolicHecke (n + 1) 0 p (lineEdge (hecke := hecke) (hhecke := hhecke) hn hne b) =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
        lineEdge (hecke := hecke) (hhecke := hhecke) hn hne b := by
  refine parabolic_eigen_of_coe p _ _ _ ?_
  have h := LocalUniqueness.phiL_localOpML (n := n) (by omega) p hp3
    (lineCoord (hecke := hecke) (hhecke := hhecke) hn hne b)
  have hy : LocalUniqueness.localOpML n (by omega) p hp3
      (lineCoord (hecke := hecke) (hhecke := hhecke) hn hne b) =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
        lineCoord (hecke := hecke) (hhecke := hhecke) hn hne b :=
    Subtype.ext (localOp_lineCoord p hp3 b)
  have h2 : LocalUniqueness.phiL n (by omega) (LocalUniqueness.localOpML n (by omega) p hp3
      (lineCoord (hecke := hecke) (hhecke := hhecke) hn hne b)) =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
        LocalUniqueness.phiL n (by omega)
          (lineCoord (hecke := hecke) (hhecke := hhecke) hn hne b) :=
    (congrArg (LocalUniqueness.phiL n (by omega)) hy).trans (map_smul _ _ _)
  exact h.symm.trans h2

/-- The edge image of a line summand class with nonzero good-line coordinate is nonzero. -/
theorem lineEdge_ne_zero (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)
    {b : boundarySummand (trivialData cusp coh) .line}
    (hb : cuspRes n trivialCharacter .line true b.1 ≠ 0) :
    lineEdge (hecke := hecke) (hhecke := hhecke) hn hne b ≠ 0 := by
  intro h0
  apply hb
  have h1 : LocalUniqueness.phiL n (by omega)
      (lineCoord (hecke := hecke) (hhecke := hhecke) hn hne b) = 0 :=
    congrArg Subtype.val h0
  have h2 := LocalUniqueness.phiL_injective (n := n) (by omega)
    (h1.trans (map_zero _).symm)
  exact congrArg Subtype.val h2

/-- **The level-one Hecke adjointness hypothesis** at the good line: the parabolic cup pairing of
`H¹(GL₂(ℤ), Sym^{n+1})` with `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is Hecke adjoint with the scalar
`p⁻¹`. It is `AdjointLevelOne.ParabolicPairingHeckeAdjoint (n + 1) 0 (-1)`. -/
abbrev GoodLineAdjoint (n : ℕ) (hodd : Odd n) : Prop :=
  AdjointLevelOne.ParabolicHeckeAdjoint (n + 1) 0 (-1)
    (parabolicPairing (twistedPairing_goodLine_trivial hodd)) (AdjointLevelOne.heckeScalar 0 (-1))

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial

end
