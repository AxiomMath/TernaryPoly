module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBad
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.ParabolicL0
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Exact
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ParityCases
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GenEqGood

@[expose] public section


/-!
# Local nondegeneracy at the bad line `L₀`, trivial character, even degree

For the trivial character and even `n` the local value at the bad line `L₀` of the boundary trace is
nondegenerate against the local cohomology at the good plane (the dual plane of `L₀`).

* **The line coordinate.**  A line summand class `b` has Shapiro coordinate `cuspRes b` at `L₀`
  in the radical kernel (`HeckeAdjointMembership`); its bad-line edge, with the sign of the bridge,
  is the parabolic class `lineEdge b ∈ H¹_par(Γ₁'(3), Sym^{n+1})` (`BadIdentLine`).  It is a genuine
  eigenvector of the Hecke operators `T_p` with `x + p^{-(n+1)} T_p x = c(T_p) x`.
* **The plane coordinate.**  The good-plane edge, restricted to the joint generalized eigenspace `J`
  of the prime operators, lands in `H¹_par(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`; the pairing is
  `badGoodPairingEven` (transport by `α` and `planeComparison`).
* **Nondegeneracy** (`exists_pairing_ne_zero`): the functional `η ↦ ⟨x, E η⟩` on the (Hecke-stable)
  subspace of local classes with parabolic edge is an eigenfunctional of the commuting operators
  `T_p`, by the level-three adjointness hypothesis `BadGoodHeckeAdjointEven` and the edge formula
  `E (T_p y) = E y + p^{-(n+2)} T_p E y`, whose dual eigenvalue is `c(T_p)` again; it is nonzero by
  the left nondegeneracy of the pairing and the surjectivity of the good-plane
  edge; hence nonzero on the joint generalized eigenspace.
* **Value** (`lineValue_eq_pairing_bridge`): the local value is `(n+1)!/3` times the pairing of the
  classes of the Levi cocycles of the bridge `levelThreeBridgeBad`, which are the edge classes
  (`BadIdentLine`, `BadIdentPlane`).
* **Assembly** by `HeckeGenerators.localNondegenerate_of_edges_gen`, with `J ⊆ L` for the good plane
  from `HeckeGenEq.localJointGen_eq_localJoint_goodPlane_trivial`; the final statements are
  `localNondegenerate_L0_even` and `badLineEvenInput` (`ParityCases.BadLineEvenInput n`), whose only
  extra hypothesis is the level-three adjointness `BadGoodHeckeAdjointEven`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLinear
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

open TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators
  (localJointGen localNondegenerate_of_edges_gen)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership (trivialData)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed parabolicCrossedH1 parabolicPairing mem_parabolicCrossed_of_mem
    twistedPairing_binaryArithmeticRepresentation jointEdgeMap_mem_parabolicCrossedH1
    goodPlaneEdge_mem_parabolicCrossedH1)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
  (goodPlaneEdge goodPlane_finiteDimensional)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree
  (LevelThreeParabolicAdjoint levelThreeKappa levelThreeKappa_ne_zero dualEigenvalue_badGood
    goodPlane_pairing_eigen_parabolic parabolicHecke parabolicHecke_coe
    levelHecke_mem_parabolicCrossedH1)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)

variable {n : ℕ}

/-! ### Assembly -/

section Assembly

variable (cusp : CuspidalRepresentation) (coh : Cohomological cusp n)
  (hecke : BoundaryHecke n trivialCharacter) (hhecke : ActualBoundaryHecke n trivialCharacter hecke)
  (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)

include hn hne in
/-- The pair character is close to `1` at `T_2`. -/
theorem pair_bound :
    ‖pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp LocalUniqueness.two) - 1‖ ≤
      3 / 4 :=
  Separation.pairCharacter_two_sub_one_norm_le_of_trivial (trivialData cusp coh) rfl
    hecke hhecke hn hne

/-- **The good-plane edge on the prime joint generalized eigenspace**, with values in the parabolic
classes (given `J ⊆ L`). -/
def planeEdgeJ
    (hJ : localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane true ≤
      localJoint n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane true) :
    localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane true →ₗ[ℂ] parabolicCrossedH1 (levelRep (n + 1) (-1)) :=
  LinearMap.codRestrict _ ((goodPlaneEdge (by omega : 0 < n)).comp (Submodule.subtype _))
    (fun η => goodPlaneEdge_mem_parabolicCrossedH1 n (by omega) _
      (pair_bound cusp coh hecke hhecke hn hne) (hJ η.2))

/-- **The `nondegenerate` field.** -/
theorem nondeg_field (heven : Even n) (hadj : BadGoodHeckeAdjointEven heven)
    (hJ : localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane true ≤
      localJoint n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke) .plane true)
    (b : boundarySummand (trivialData cusp coh) .line)
    (hb : cuspRes n trivialCharacter .line false b.1 ≠ 0) :
    ∃ η : localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane true,
      badGoodPairingEven heven (lineEdge cusp coh hecke hhecke hn hne b)
        (planeEdgeJ cusp coh hecke hhecke hn hne hJ η) ≠ 0 := by
  obtain ⟨η, hηJ, hpar, hne'⟩ := exists_pairing_ne_zero (by omega : 0 < n) heven hecke hhecke
    (pairCharacter (trivialData cusp coh) hecke hhecke) hadj
    (lineEdge cusp coh hecke hhecke hn hne b) (lineEdge_ne_zero cusp coh hecke hhecke hn hne b hb)
    (fun p hp3 => lineEdge_eigen cusp coh hecke hhecke hn hne b p hp3)
  exact ⟨⟨η, hηJ⟩, hne'⟩

/-- **The `value` field.** -/
theorem value_field (heven : Even n)
    (hJ : localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane true ≤
      localJoint n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke) .plane true)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (trivialData cusp coh) .line)
    (hy : cuspRes n trivialCharacter .plane true (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ∈
        localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
          .plane true)
    (hw : EdgePrimitive z w)
    (hne' : badGoodPairingEven heven (lineEdge cusp coh hecke hhecke hn hne ⟨_, hz⟩)
      (planeEdgeJ cusp coh hecke hhecke hn hne hJ ⟨_, hy⟩) ≠ 0) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y ≠ 0 := by
  have hyP : goodPlaneEdge (by omega : 0 < n) (cuspRes n trivialCharacter .plane true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)) ∈
      parabolicCrossedH1 (levelRep (n + 1) (-1)) :=
    goodPlaneEdge_mem_parabolicCrossedH1 n (by omega) _ (pair_bound cusp coh hecke hhecke hn hne)
      (hJ hy)
  have key := lineValue_eq_pairing_bridge cusp coh hecke hhecke hn hne heven z w y hz hw hyP
  intro h0
  have hc : (((n + 1).factorial : ℂ) / 3) ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) (by norm_num)
  exact hne' ((mul_eq_zero.mp (key.symm.trans h0)).resolve_left hc)

include hn hne in
/-- **Local nondegeneracy at the bad line, trivial character, even degree**, given the comparison
`J ⊆ L` of the prime joint generalized eigenspace and the full joint generalized eigenspace at the
good plane, and the Hecke adjointness for the even pairing. -/
theorem localNondegenerate_L0_even_of_gen (heven : Even n) (hadj : BadGoodHeckeAdjointEven heven)
    (hJ : localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane true ≤
      localJoint n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane true) :
    LocalNondegenerate traceDataL2 (trivialData cusp coh) (dualityData n trivialCharacter) hecke
      hhecke 0 true :=
  by
  refine localNondegenerate_of_edges_gen (D := trivialData cusp coh)
    (X := parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (Y := parabolicCrossedH1 (levelRep (n + 1) (-1)))
    traceDataL2 (dualityData n trivialCharacter) hecke hhecke 0 true hJ ?_ ?_ ?_ ?_ ?_
  · exact badGoodPairingEven heven
  · exact lineEdge cusp coh hecke hhecke hn hne
  · exact planeEdgeJ cusp coh hecke hhecke hn hne hJ
  · exact fun b hb => nondeg_field cusp coh hecke hhecke hn hne heven hadj hJ b hb
  · exact fun z w y hz hy hw _ hne' =>
      value_field cusp coh hecke hhecke hn hne heven hJ z w y hz hy hw hne'

end Assembly

/-- **Local nondegeneracy at the bad line `L₀` for the trivial character and even `n`**, for an
arbitrary inducing datum with trivial character, from the comparison `J ⊆ L` of the prime joint
generalized eigenspace and the full joint generalized eigenspace at the good plane, and the Hecke
adjointness `BadGoodHeckeAdjointEven` of the even pairing. -/
theorem localNondegenerate_L0_even_of_gen' (hn : 3 ≤ n) (heven : Even n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hadj : BadGoodHeckeAdjointEven heven)
    (hJ : localJointGen n D.chi (pairCharacter D hecke hhecke) .plane true ≤
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane true) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 0
      (TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2.good 0) := by
  obtain ⟨cusp, chi, coh⟩ := D
  change chi = trivialCharacter at hχ
  subst hχ
  exact localNondegenerate_L0_even_of_gen cusp coh hecke hhecke hn hne heven hadj hJ

/-- **Local nondegeneracy at the bad line `L₀`, trivial character, even degree.**  The only
hypothesis besides `3 ≤ n` and a nonzero associate pair is the level-three Hecke adjointness
`BadGoodHeckeAdjointEven` of the even pairing. -/
theorem localNondegenerate_L0_even (hn : 3 ≤ n) (heven : Even n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hadj : BadGoodHeckeAdjointEven heven) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 0
      (TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2.good 0) :=
  localNondegenerate_L0_even_of_gen' hn heven D hχ hecke hhecke hne hadj
    (HeckeGenEq.localJointGen_eq_localJoint_goodPlane_trivial hn D hχ hecke hhecke hne).le

/-- **The bad-line case of even degree** (`ParityCases.BadLineEvenInput`), from the level-three
Hecke adjointness `BadGoodHeckeAdjointEven` for the even pairing. -/
theorem badLineEvenInput (hn : 3 ≤ n) (hadj : ∀ heven : Even n, BadGoodHeckeAdjointEven heven) :
    ParityCases.BadLineEvenInput n :=
  fun D hecke hhecke hχ heven hne =>
    localNondegenerate_L0_even hn heven D hχ hecke hhecke hne (hadj heven)

/-- **The bad-line case of even degree from the plain adjointness**: the only hypothesis is
`PlainEvenHeckeAdjoint` (`⟨T_p x, y⟩ = ε_p ⟨x, T_p y⟩` for the cup pairing of
`H¹_par(Γ₁'(3), Sym^{n+1})` with itself); the transport factor `ε_p / p` is proved
(`levelHecke_planeTransport`). -/
theorem badLineEvenInput_of_plain (hn : 3 ≤ n)
    (hplain : ∀ heven : Even n, PlainEvenHeckeAdjoint heven) : ParityCases.BadLineEvenInput n :=
  badLineEvenInput hn fun heven => badGoodHeckeAdjointEven_of_plain heven (hplain heven)

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
