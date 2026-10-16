module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1OddValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1OddEta
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GenEqIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelOneEigen
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ParityCases
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Sign

@[expose] public section


/-!
# Local nondegeneracy at the good line `L₁` for an odd character of conductor three

For a nontrivial character `χ` with a nonzero associate pair (so `χ` is the odd character of
conductor three, `χ(-1_∞) = -1`), the local value at the good line `L₁` is nondegenerate
(`localNondegenerate_L1_odd`). In even degree the local joint eigenspace at the good line vanishes
(`ParityCases`), and in odd degree the proof assembles

* the pairing `π`, the parabolic cup pairing of `GL₂(ℤ)` on `Sym^{n+1} ⊗ det⁻¹ × Sym^{n+1}`
  (`twistedPairing_goodLine_odd`), with left nondegeneracy;
* the edge `lineEdge` of the Shapiro coordinate of a line summand class at the twisted good line,
  which is a parabolic class and an eigenvector of the Hecke operators `T_p` with the pair
  character (`eigen_lineEdge`);
* the edge `planeEdge` of the twisted identity plane on the joint generalized eigenspace
  `localJointGen` of the prime operators, which equals the local joint eigenspace (`HeckeGenEq`);
* nonvanishing of the pairing on the prime eigenspace from the Hecke adjointness of `π`
  (`AdjointLevelOne.goodLine_identityPlane_odd_pairing_eigen`, `LocalPairingCaseL1OddEta`);
* the local value as the pairing of the edges (`LocalPairingCaseL1OddValue`).

The only hypothesis not discharged is the Hecke adjointness `AdjointnessInput` of the parabolic
cup pairing for the twists `(-1, 0)`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Odd

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2 (good)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelOne
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction

variable {n : ℕ}

/-- **The Hecke adjointness hypothesis** of the parabolic cup pairing of `GL₂(ℤ)` on
`Sym^{n+1} ⊗ det⁻¹ × Sym^{n+1}` (the twists `(e, e') = (-1, 0)`), with the scalar `p`. -/
abbrev AdjointnessInput (n : ℕ) (hodd : Odd n) : Prop :=
  ParabolicHeckeAdjoint (n + 1) (-1) 0 (parabolicPairing (twistedPairing_goodLine_odd hodd))
    (heckeScalar (-1) 0)

/-! ### The edges -/

/-- **The twisted good-line edge of a line summand class**: a parabolic class of
`H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`. -/
def lineEdge (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (hc : ‖pairCharacter D hecke hhecke (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4) :
    boundarySummand D .line →ₗ[ℂ] parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) :=
  LinearMap.codRestrict _
    ((Twisted.edgeH2LT n D.chi hneg hn).comp ((Twisted.psiLT n D.chi).comp
      ((cuspRes n D.chi .line true).comp (boundarySummand D .line).subtype)))
    fun b => edgeH2LT_mem_parabolicH1 n D.chi hneg hn _ hc
      (Separation.cuspRes_mem_localJoint_of_mem D hecke hhecke .line true b.2)

/-- **The twisted identity-plane edge on the prime eigenspace**: a parabolic class of
`H¹(GL₂(ℤ), Sym^{n+1})`. -/
def planeEdge (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n)
    (hc : ‖pairCharacter D hecke hhecke (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    (hJ : localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false ≤
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane false) :
    localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false →ₗ[ℂ]
      parabolicH1 (arithmeticBinaryRep (n + 1) 0) :=
  LinearMap.codRestrict _
    ((Twisted.edgeH2T n D.chi hneg hn hodd).comp
      (localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false).subtype)
    fun η => edgeH2T_mem_parabolicH1 n D.chi hneg hn hodd _ hc (hJ η.2)

/-- **The line edge is a Hecke eigenvector**: `a_p x + p^{-(n+2)} T_p x = c_p x`. -/
theorem eigen_lineEdge (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (hc : ‖pairCharacter D hecke hhecke (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    (b : boundarySummand D .line) (p : Nat.Primes) (hp3 : p.val ≠ 3) :
    ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • lineEdge D hecke hhecke hneg hn hc b +
        ((p.val : ℂ) ^ (n + 2))⁻¹ •
          parabolicHecke (n + 1) (-1) p (lineEdge D hecke hhecke hneg hn hc b) =
      pairCharacter D hecke hhecke (TpExistence.tp p) • lineEdge D hecke hhecke hneg hn hc b := by
  have hloc : localOp n D.chi (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line true
      (cuspRes n D.chi .line true b.1) =
        pairCharacter D hecke hhecke (TpExistence.tp p) • cuspRes n D.chi .line true b.1 := by
    rw [← cuspRes_hecke hecke hhecke (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
      .line true b.1, Separation.hecke_eq_pairCharacter_smul D hecke hhecke
      (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line b.2, map_smul]
  apply Subtype.ext
  have h := Twisted.edgeH2LT_localOp_tp n D.chi hneg hn p hp3
    (cuspRes n D.chi .line true b.1)
  have e : Twisted.edgeH2LT n D.chi hneg hn (Twisted.psiLT n D.chi
        (pairCharacter D hecke hhecke (TpExistence.tp p) • cuspRes n D.chi .line true b.1)) =
      pairCharacter D hecke hhecke (TpExistence.tp p) •
        Twisted.edgeH2LT n D.chi hneg hn
          (Twisted.psiLT n D.chi (cuspRes n D.chi .line true b.1)) := by
    rw [map_smul, map_smul]
  have h' := e.symm.trans
    ((congrArg (fun u => Twisted.edgeH2LT n D.chi hneg hn
      (Twisted.psiLT n D.chi u)) hloc).symm.trans h)
  simp only [Submodule.coe_add, Submodule.coe_smul, coe_parabolicHecke]
  exact h'.symm

/-- **The line edge of a class with nonzero coordinate at `L₁` is nonzero.** -/
theorem lineEdge_ne_zero (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (hc : ‖pairCharacter D hecke hhecke (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    (b : boundarySummand D .line)
    (hb : fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi)
      (traceDataL2.lineRep 1) b.1 ≠ 0) :
    lineEdge D hecke hhecke hneg hn hc b ≠ 0 := by
  intro h0
  have hy₀ne : cuspRes n D.chi .line true b.1 ≠ 0 := fun h =>
    hb (ParityCases.fixedPointH2_eq_zero_of_cuspRes_side ParityCases.goodLine_orbit h)
  apply hy₀ne
  have h1 : Twisted.edgeH2LT n D.chi hneg hn (Twisted.psiLT n D.chi
      (cuspRes n D.chi .line true b.1)) = 0 := congrArg Subtype.val h0
  have h2 := Twisted.edgeH2LT_injective n D.chi hneg hn (h1.trans (map_zero _).symm)
  exact Twisted.psiLT_injective n D.chi (h2.trans (map_zero _).symm)

/-! ### The nondegeneracy field -/

/-- **A class with nonzero line edge pairs nontrivially with the edge of a prime eigenclass.** -/
theorem exists_pairing_ne_zero (hn3 : 3 ≤ n) (hodd : Odd n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hc : ‖pairCharacter D hecke hhecke (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    (hJ : localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false ≤
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane false)
    (hadj : AdjointnessInput n hodd) (b : boundarySummand D .line)
    (hb : fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi)
      (traceDataL2.lineRep 1) b.1 ≠ 0) :
    ∃ η : localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false,
      parabolicPairing (twistedPairing_goodLine_odd hodd)
        (lineEdge D hecke hhecke hneg (by omega) hc b)
        (planeEdge D hecke hhecke hneg (by omega) hodd hc hJ η) ≠ 0 := by
  have hn0 : 0 < n := by omega
  have hxb0 := lineEdge_ne_zero D hecke hhecke hneg hn0 hc b hb
  have hψ0 : parabolicPairing (twistedPairing_goodLine_odd hodd)
      (lineEdge D hecke hhecke hneg hn0 hc b) ≠ 0 := by
    intro h0
    exact hxb0 (goodLine_left_nondegenerate_odd hodd _ fun cl' => by simp [h0])
  have hψ : ∀ p : Nat.Primes, p.val ≠ 3 → ∀ y : parabolicH1 (arithmeticBinaryRep (n + 1) 0),
      parabolicPairing (twistedPairing_goodLine_odd hodd) (lineEdge D hecke hhecke hneg hn0 hc b)
        (((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • y +
          ((p.val : ℂ) ^ (n + 1))⁻¹ • parabolicHecke (n + 1) 0 p y) =
        pairCharacter D hecke hhecke (TpExistence.tp p) *
          parabolicPairing (twistedPairing_goodLine_odd hodd)
            (lineEdge D hecke hhecke hneg hn0 hc b) y := fun p hp3 y =>
    goodLine_identityPlane_odd_pairing_eigen n hodd p hadj
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) (pairCharacter D hecke hhecke (TpExistence.tp p))
      (eigen_lineEdge D hecke hhecke hneg hn0 hc b p hp3) rfl
  obtain ⟨η, hη, hne⟩ := LocalPairingCaseL1OddEta.exists_localJointGen_pairing_ne_zero D hneg hn0
    hodd hecke hhecke hc hJ _ hψ0 hψ
  exact ⟨⟨η, hη⟩, hne⟩

/-- **Local nondegeneracy at the good line `L₁` for an odd character of conductor three, in odd
degree**, from the Hecke adjointness of the cup pairing. -/
theorem localNondegenerate_L1_odd_of_odd (hn : 3 ≤ n) (hodd : Odd n) (D : InducingData n)
    (hχ : D.chi ≠ trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hadj : AdjointnessInput n hodd) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 1 (good 1) := by
  change LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 1 false
  by_cases hex : ∃ b ∈ boundarySummand D .line,
      fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi)
        (traceDataL2.lineRep 1) b ≠ 0
  swap
  · exact ParityCases.localNondegenerate_of_coordinates_eq_zero traceDataL2
      (dualityData n D.chi) hecke hhecke 1 false (by simpa using hex)
  obtain ⟨b₀, hb₀, hb₀ne⟩ := hex
  have hJ := HeckeGenEq.localJointGen_eq_localJoint_identityPlane_odd hn D hχ hecke hhecke hne
    hb₀ hb₀ne
  have h3 := LevelOneNontrivial.conductorThree_of_associatePair_ne_bot D hne
  have hneg := LevelOneNontrivial.chi_realNegOne_eq_neg_one hχ h3
  have hc := Twisted.pairCharacter_two_add_one_norm_le D h3 hneg hecke hhecke hn hne
  have hn0 : 0 < n := by omega
  refine localNondegenerate_of_edges_gen traceDataL2 (dualityData n D.chi) hecke hhecke 1 false
    hJ.le (parabolicPairing (twistedPairing_goodLine_odd hodd))
    (lineEdge D hecke hhecke hneg hn0 hc) (planeEdge D hecke hhecke hneg hn0 hodd hc hJ.le)
    (fun b hb => exists_pairing_ne_zero hn hodd D hecke hhecke hneg hc hJ.le hadj b hb) ?_
  intro z w y hz hy hw _ hne'
  have hzl := Separation.cuspRes_mem_localJoint_of_mem D hecke hhecke .line true hz
  have hyp := hJ.le hy
  rw [LocalPairingCaseL1OddValue.lineValue_goodLine_odd_eq hneg hn0 hodd _ hc z w y hw hzl hyp]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) hne'

/-- **Local nondegeneracy at the good line `L₁` for a nontrivial character** (so, for a nonzero
associate pair, the odd character of conductor three), from the Hecke adjointness of the parabolic
cup pairing in odd degree. In even degree the local joint eigenspace at the good line is zero. -/
theorem localNondegenerate_L1_odd (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi ≠ trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hadj : ∀ hodd : Odd n, AdjointnessInput n hodd) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 1 (good 1) := by
  rcases Nat.even_or_odd n with he | ho
  · exact ParityCases.localNondegenerate_goodLine_of_even hn D hecke hhecke he hne
  · exact localNondegenerate_L1_odd_of_odd hn ho D hχ hecke hhecke hne (hadj ho)

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Odd

end
