module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1TrivialValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GenEqIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ParityCases

@[expose] public section


/-!
# Local nondegeneracy at the good line `L₁` for the trivial character

For the trivial character, the line `L₁` of the boundary trace is the reference good line and its
dual plane is the identity plane.  For even `n` local nondegeneracy is vacuous
(`ParityCases.localNondegenerate_goodLine_of_even`).  For odd `n` it is assembled from
`HeckeGenerators.localNondegenerate_of_edges_gen`, with

* the pairing the parabolic cup pairing of `H¹(GL₂(ℤ), Sym^{n+1})` with
  `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` (`twistedPairing_goodLine_trivial`);
* `xb` the good-line edge of the coordinate of a line summand class (`lineEdge`);
* `g'` the identity-plane edge on the joint generalized eigenspace `localJointGen` of the prime
  operators, which is the local joint eigenspace (`HeckeGenEq`) as
  soon as the line summand has a nonzero coordinate at the good line
  (`HeckeGenEq.localJointGen_eq_localJoint_identityPlane_trivial_of_line`);
* `nondegenerate` from `exists_partner` (left nondegeneracy of the cup pairing, bijectivity of the
  identity-plane edge, Hecke adjointness);
* `value` from `lineValue_ne_zero` (fiber integration, Kostant bridge, identification of the bridge
  cocycles with the edge images).

The only hypothesis that is not discharged is the Hecke adjointness `GoodLineAdjoint n hodd` of the
parabolic cup pairing at level one, which is `AdjointLevelOne.ParabolicPairingHeckeAdjoint`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership (trivialData)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness (LocalNondegenerate)
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2 (good)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators (localJointGen)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (parabolicH1 parabolicPairing twistedPairing_goodLine_trivial edgeH2_mem_parabolicH1)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)

variable {n : ℕ} {cusp : CuspidalRepresentation} {coh : Cohomological cusp n}
  {hecke : BoundaryHecke n trivialCharacter}
  {hhecke : ActualBoundaryHecke n trivialCharacter hecke}

/-- The identity-plane edge on the joint generalized eigenspace `localJointGen`, as a linear map into
the parabolic classes, when `localJointGen` lies in the local joint eigenspace. -/
def planeEdgeJ (hn : 3 ≤ n) (hodd : Odd n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)
    (hJ : localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane false ≤
      localJoint n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane false) :
    localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane false →ₗ[ℂ] parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) :=
  LinearMap.codRestrict (parabolicH1 (arithmeticBinaryRep (n + 1) (-1)))
    ((IdentityPlaneHecke.edgeH2 n (by omega) hodd).comp
      (localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane false).subtype)
    (fun η => edgeH2_mem_parabolicH1 n (by omega) hodd
      (pairCharacter (trivialData cusp coh) hecke hhecke)
      (pair_two_sub_one (hecke := hecke) (hhecke := hhecke) hn hne) (hJ η.2))

/-- **Local nondegeneracy at `L₁`, trivial character, odd degree.** -/
theorem localNondegenerate_L1_trivial_odd (hn : 3 ≤ n) (hodd : Odd n)
    (hadj : GoodLineAdjoint n hodd) (hne : associatePair (trivialData cusp coh) ≠ ⊥) :
    LocalNondegenerate traceDataL2 (trivialData cusp coh) (dualityData n trivialCharacter)
      hecke hhecke 1 (good 1) := by
  have hn0 : 0 < n := by omega
  by_cases hbot : coordinateImage (trivialData cusp coh) .line true = ⊥
  · refine ParityCases.localNondegenerate_of_coordinates_eq_zero traceDataL2
      (D := trivialData cusp coh) (dualityData n trivialCharacter) hecke hhecke 1 (good 1)
      (fun b hb => ?_)
    have hmem : cuspRes n trivialCharacter .line true b ∈
        coordinateImage (trivialData cusp coh) .line true := ⟨b, hb, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact ParityCases.fixedPointH2_eq_zero_of_cuspRes_side ParityCases.goodLine_orbit hmem
  · have hJ : localJointGen n trivialCharacter
        (pairCharacter (trivialData cusp coh) hecke hhecke) .plane false ≤
        localJoint n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
          .plane false :=
      (HeckeGenEq.localJointGen_eq_localJoint_identityPlane_trivial_of_line hn
        (trivialData cusp coh) rfl hecke hhecke hne hbot).le
    have hgood : good 1 = false := rfl
    rw [hgood]
    refine HeckeGenerators.localNondegenerate_of_edges_gen traceDataL2
      (D := trivialData cusp coh) (dualityData n trivialCharacter) hecke hhecke 1 false hJ
      (parabolicPairing (twistedPairing_goodLine_trivial hodd))
      (lineEdge (hecke := hecke) (hhecke := hhecke) hn hne)
      (planeEdgeJ (hecke := hecke) (hhecke := hhecke) hn hodd hne hJ) ?_ ?_
    · intro b hb
      have hb' : cuspRes n trivialCharacter .line true b.1 ≠ 0 := fun h0 =>
        hb (ParityCases.fixedPointH2_eq_zero_of_cuspRes_side ParityCases.goodLine_orbit h0)
      obtain ⟨a, haJ, hne0⟩ := exists_partner (hecke := hecke) (hhecke := hhecke) hn hodd
        hadj hne hb'
      exact ⟨⟨cuspRes n trivialCharacter .plane false a.1, haJ⟩, hne0⟩
    · intro z w y hz hy hw _ hnz
      exact lineValue_ne_zero (hecke := hecke) (hhecke := hhecke) hn hodd hne z w y hz hw (hJ hy) hnz

/-- **Local nondegeneracy at the good line `L₁` for the trivial character**, in every degree: vacuous
in even degree, and in odd degree a consequence of the Hecke adjointness of the level-one parabolic
cup pairing. -/
theorem localNondegenerate_L1_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hadj : ∀ hodd : Odd n, GoodLineAdjoint n hodd) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 1 (good 1) := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact ParityCases.localNondegenerate_goodLine_of_even hn D hecke hhecke heven hne
  · obtain ⟨cusp, chi, coh⟩ := D
    change chi = trivialCharacter at hχ
    subst hχ
    exact localNondegenerate_L1_trivial_odd hn hodd (hadj hodd) hne

/-- **The good-line trivial-character input of `LocalPairingL2`.** -/
theorem goodLineTrivialInput (hn : 3 ≤ n) (hadj : ∀ hodd : Odd n, GoodLineAdjoint n hodd) :
    LocalPairingL2.GoodLineTrivialInput n :=
  fun D hecke hhecke hχ _ hne => localNondegenerate_L1_trivial hn D hχ hecke hhecke hne hadj

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial

end
