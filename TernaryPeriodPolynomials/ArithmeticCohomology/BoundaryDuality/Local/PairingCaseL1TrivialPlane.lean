module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1TrivialLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GeneratorsJoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EdgeSurjIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspLift

@[expose] public section


/-!
# The plane side of local nondegeneracy at the good line `L₁`, trivial character

Let `x` be the (parabolic) edge image of a line summand class `b` with nonzero good-line coordinate.
We find a class `a` of the plane stratum whose Shapiro coordinate `η` at the identity plane lies in
the joint generalized eigenspace `localJointGen` of the local operators of the prime correspondences
`T_p` (`p ≠ 3`), has parabolic identity-plane edge image, and pairs nontrivially with `x`.

The pairing `y ↦ ⟨x, y⟩` of the parabolic classes of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is nonzero by
the left nondegeneracy of the parabolic cup pairing, and `y` lifts to a class of the stratum because
the identity-plane edge is bijective (`EdgeSurjIdentity.edgeH2_surjective`) and the Shapiro
coordinate is split (`cuspRes_cuspLift`).  On the Hecke-stable subspace `paraSub` of the stratum on
which the edge image is parabolic, the functional `a ↦ ⟨x, edge (cuspRes a)⟩` is an eigenfunctional of
every `T_p` with the pair-character eigenvalue, by the Hecke adjointness of the parabolic cup pairing
and the edge formulas (`lineEdge_eigen`, `edgeH2_localOp_tp`); the operators commute, so it is
nonzero on a joint generalized eigenvector.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspLift (cuspLift cuspRes_cuspLift)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership (trivialData)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLinear
  (jointSpace mem_jointSpace_iff exists_mem_jointSpace_of_functional)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators (localJointGen)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (parabolicH1 parabolicPairing twistedPairing_goodLine_trivial
    goodLine_left_nondegenerate_trivial)
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1 (arithmeticHecke)
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelOne (parabolicHecke)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)

variable {n : ℕ} {cusp : CuspidalRepresentation} {coh : Cohomological cusp n}
  {hecke : BoundaryHecke n trivialCharacter}
  {hhecke : ActualBoundaryHecke n trivialCharacter hecke}

/-- The identity-plane edge of the Shapiro coordinate, on the plane stratum. -/
def planeEdgeMap (hn : 0 < n) (hodd : Odd n) :
    StratumH2 n trivialCharacter .plane →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) :=
  (IdentityPlaneHecke.edgeH2 n hn hodd).comp (cuspRes n trivialCharacter .plane false)

include hhecke in
/-- The edge image of the Shapiro coordinate intertwines the plane Hecke operator of `T_p` with
`1 + p^{-(n+2)} T_p`. -/
theorem planeEdgeMap_hecke (hn : 0 < n) (hodd : Odd n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (a : StratumH2 n trivialCharacter .plane) :
    planeEdgeMap hn hodd (hecke .plane (TpExistence.tp p) a) =
      planeEdgeMap hn hodd a + (((p.val : ℕ) : ℂ) ^ (n + 2))⁻¹ •
        arithmeticHecke (n + 1) (-1) p (planeEdgeMap hn hodd a) := by
  have h1 := cuspRes_hecke hecke hhecke (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
    .plane false a
  have h2 := IdentityPlaneLocalOp.edgeH2_localOp_tp (p := p) n hn hodd hp3
    (cuspRes n trivialCharacter .plane false a)
  exact (congrArg (IdentityPlaneHecke.edgeH2 n hn hodd) h1).trans h2

/-- The classes of the plane stratum whose identity-plane edge image is parabolic. -/
def paraSub (hn : 0 < n) (hodd : Odd n) : Submodule ℂ (StratumH2 n trivialCharacter .plane) :=
  (parabolicH1 (arithmeticBinaryRep (n + 1) (-1))).comap (planeEdgeMap hn hodd)

include hhecke in
/-- The prime Hecke operators preserve `paraSub`. -/
theorem hecke_mem_paraSub (hn : 0 < n) (hodd : Odd n) (p : {p : Nat.Primes // p.val ≠ 3})
    {a : StratumH2 n trivialCharacter .plane} (ha : a ∈ paraSub hn hodd) :
    hecke .plane (TpExistence.tp p.1) a ∈ paraSub hn hodd := by
  have ha' : planeEdgeMap hn hodd a ∈ parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) := ha
  show planeEdgeMap hn hodd (hecke .plane (TpExistence.tp p.1) a) ∈
    parabolicH1 (arithmeticBinaryRep (n + 1) (-1))
  rw [planeEdgeMap_hecke (hecke := hecke) (hhecke := hhecke) hn hodd p.1 p.2 a]
  exact Submodule.add_mem _ ha' (Submodule.smul_mem _ _
    (AdjointLevelOne.arithmeticHecke_mem_parabolicH1 (n + 1) (-1) p.1 ha'))

include hhecke in
/-- The prime Hecke operators restricted to `paraSub`. -/
def heckeOnPara (hn : 0 < n) (hodd : Odd n) (p : {p : Nat.Primes // p.val ≠ 3}) :
    Module.End ℂ (paraSub hn hodd) :=
  (hecke .plane (TpExistence.tp p.1)).restrict
    (fun _ ha => hecke_mem_paraSub (hecke := hecke) (hhecke := hhecke) hn hodd p ha)

include hhecke in
/-- The restricted prime Hecke operators commute. -/
theorem heckeOnPara_comm (hn : 0 < n) (hodd : Odd n) (s t : {p : Nat.Primes // p.val ≠ 3}) :
    Commute (heckeOnPara (hecke := hecke) (hhecke := hhecke) hn hodd s)
      (heckeOnPara (hecke := hecke) (hhecke := hhecke) hn hodd t) := by
  have h := TernaryPeriodPolynomials.HeckeCommutativity.realizesHecke_comm_all
    (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
    (hecke .plane) (hhecke .plane)
    (TernaryPeriodPolynomials.HeckeCommutativity.good_of_awayThree
      (TpExistence.tp_awayThree s.1 s.2)) (TpExistence.tp t.1)
  have h' : hecke .plane (TpExistence.tp s.1) * hecke .plane (TpExistence.tp t.1) =
      hecke .plane (TpExistence.tp t.1) * hecke .plane (TpExistence.tp s.1) := h
  exact LinearMap.ext fun a => Subtype.ext (LinearMap.congr_fun h' a.1)

/-- The edge image of an element of `paraSub`, as a parabolic class. -/
def paraEdge (hn : 0 < n) (hodd : Odd n) :
    paraSub hn hodd →ₗ[ℂ] parabolicH1 (arithmeticBinaryRep (n + 1) (-1)) :=
  (planeEdgeMap hn hodd).restrict (fun _ ha => ha)

include hhecke in
/-- The edge of a Hecke translate. -/
theorem paraEdge_hecke (hn : 0 < n) (hodd : Odd n) (p : {p : Nat.Primes // p.val ≠ 3})
    (a : paraSub hn hodd) :
    paraEdge hn hodd (heckeOnPara (hecke := hecke) (hhecke := hhecke) hn hodd p a) =
      paraEdge hn hodd a + (((p.1.val : ℕ) : ℂ) ^ (n + 2))⁻¹ •
        parabolicHecke (n + 1) (-1) p.1 (paraEdge hn hodd a) :=
  Subtype.ext (planeEdgeMap_hecke (hecke := hecke) (hhecke := hhecke) hn hodd p.1 p.2 a.1)

/-- Every class of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is the identity-plane edge of a stratum class. -/
theorem exists_stratum_lift (hn : 0 < n) (hodd : Odd n)
    (y : groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) :
    ∃ a : StratumH2 n trivialCharacter .plane, planeEdgeMap hn hodd a = y := by
  obtain ⟨η₀, hη₀⟩ := EdgeSurjIdentity.edgeH2_surjective n hn hodd y
  have h := cuspRes_cuspLift (n := n) (χ := trivialCharacter) .plane false
    (η₀ : CuspH2 n trivialCharacter .plane false)
  exact ⟨cuspLift n trivialCharacter .plane false η₀,
    (congrArg (IdentityPlaneHecke.edgeH2 n hn hodd) h).trans hη₀⟩

/-- Every nonzero line edge pairs nontrivially with some parabolic class (left nondegeneracy). -/
theorem exists_left_partner (hodd : Odd n) (x : parabolicH1 (arithmeticBinaryRep (n + 1) 0))
    (hx : x ≠ 0) :
    ∃ y : parabolicH1 (arithmeticBinaryRep (n + 1) (-1)),
      parabolicPairing (twistedPairing_goodLine_trivial hodd) x y ≠ 0 := by
  by_contra hcon
  exact hx (goodLine_left_nondegenerate_trivial hodd _
    (fun cl' => by_contra fun h => hcon ⟨cl', h⟩))

/-- Every parabolic class is the edge image of an element of `paraSub`. -/
theorem exists_para_lift (hn : 0 < n) (hodd : Odd n)
    (y : parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) :
    ∃ a : paraSub hn hodd, paraEdge hn hodd a = y := by
  obtain ⟨a₀, hFa₀⟩ := exists_stratum_lift hn hodd y.1
  exact ⟨⟨a₀, by rw [paraSub, Submodule.mem_comap, hFa₀]; exact y.2⟩, Subtype.ext hFa₀⟩

/-- The functional `a ↦ ⟨edge b, edge a⟩` on `paraSub`, for a line summand class `b`. -/
def phiB (hn : 3 ≤ n) (hodd : Odd n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)
    (b : boundarySummand (trivialData cusp coh) .line) : paraSub (by omega : 0 < n) hodd →ₗ[ℂ] ℂ :=
  (parabolicPairing (twistedPairing_goodLine_trivial hodd)
    (lineEdge (hecke := hecke) (hhecke := hhecke) hn hne b)).comp (paraEdge (by omega) hodd)

/-- The functional `phiB` is nonzero for a line class with nonzero good-line coordinate. -/
theorem phiB_ne_zero (hn : 3 ≤ n) (hodd : Odd n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)
    {b : boundarySummand (trivialData cusp coh) .line}
    (hb : cuspRes n trivialCharacter .line true b.1 ≠ 0) :
    phiB (hecke := hecke) (hhecke := hhecke) hn hodd hne b ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_left_partner hodd _
    (lineEdge_ne_zero (hecke := hecke) (hhecke := hhecke) hn hne hb)
  obtain ⟨a₀, ha₀y⟩ := exists_para_lift (by omega : 0 < n) hodd y
  intro h0
  apply hy
  rw [← ha₀y]
  exact LinearMap.congr_fun h0 a₀

include hhecke in
/-- The functional `phiB` is an eigenfunctional of the prime Hecke operators on `paraSub`, by the
Hecke adjointness of the parabolic cup pairing. -/
theorem phiB_hecke (hn : 3 ≤ n) (hodd : Odd n) (hadj : GoodLineAdjoint n hodd)
    (hne : associatePair (trivialData cusp coh) ≠ ⊥)
    (b : boundarySummand (trivialData cusp coh) .line) (p : {p : Nat.Primes // p.val ≠ 3})
    (a : paraSub (by omega : 0 < n) hodd) :
    phiB (hecke := hecke) (hhecke := hhecke) hn hodd hne b
        (heckeOnPara (hecke := hecke) (hhecke := hhecke) (by omega) hodd p a) =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p.1) *
        phiB (hecke := hecke) (hhecke := hhecke) hn hodd hne b a :=
  AdjointLevelOne.goodLine_identityPlane_pairing_eigen n hodd p.1 hadj
    (pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p.1))
    (lineEdge_eigen (hecke := hecke) (hhecke := hhecke) hn hne p.1 p.2 b)
    (paraEdge_hecke (hecke := hecke) (hhecke := hhecke) (by omega) hodd p a)

/-- **A plane class with nonzero pairing against the edge of a line class.**  For a line summand
class `b` with nonzero coordinate at the good line there is a class `a` of the plane stratum whose
identity-plane coordinate lies in `localJointGen`, with parabolic edge image, pairing nontrivially
with the edge image of `b`. -/
theorem exists_partner (hn : 3 ≤ n) (hodd : Odd n) (hadj : GoodLineAdjoint n hodd)
    (hne : associatePair (trivialData cusp coh) ≠ ⊥)
    {b : boundarySummand (trivialData cusp coh) .line}
    (hb : cuspRes n trivialCharacter .line true b.1 ≠ 0) :
    ∃ a : paraSub (by omega : 0 < n) hodd,
      cuspRes n trivialCharacter .plane false a.1 ∈
        localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
          .plane false ∧
      phiB (hecke := hecke) (hhecke := hhecke) hn hodd hne b a ≠ 0 := by
  have := HeckeAdjointLocal.finiteDimensional_plane n trivialCharacter
  obtain ⟨a, haJ, hφa⟩ := exists_mem_jointSpace_of_functional
    (heckeOnPara (hecke := hecke) (hhecke := hhecke) (by omega) hodd)
    (heckeOnPara_comm (hecke := hecke) (hhecke := hhecke) (by omega) hodd)
    (phiB (hecke := hecke) (hhecke := hhecke) hn hodd hne b)
    (phiB_ne_zero (hecke := hecke) (hhecke := hhecke) hn hodd hne hb)
    (fun p => pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p.1))
    (fun p a => phiB_hecke (hecke := hecke) (hhecke := hhecke) hn hodd hadj hne b p a)
  refine ⟨a, ?_, hφa⟩
  simp only [HeckeGenerators.localJointGen, Submodule.mem_iInf]
  intro p
  exact intertwine_mem_maxGenEigenspace
    ((cuspRes n trivialCharacter .plane false).comp (paraSub (by omega : 0 < n) hodd).subtype)
    (heckeOnPara (hecke := hecke) (hhecke := hhecke) (by omega) hodd p)
    (localOp n trivialCharacter (TpExistence.tp p.1) (TpExistence.tp_awayThree p.1 p.2)
      .plane false)
    (fun a => cuspRes_hecke hecke hhecke (TpExistence.tp p.1) (TpExistence.tp_awayThree p.1 p.2)
      .plane false a.1)
    (pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p.1))
    (mem_jointSpace_iff.mp haJ p)

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial

end
