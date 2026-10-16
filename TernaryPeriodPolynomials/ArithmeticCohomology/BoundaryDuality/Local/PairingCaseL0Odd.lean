module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GeneratorsJoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipBad
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadOdd
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.ParabolicL0
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Exact
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EdgeSurjGoodPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ParityCases
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GenEqGood

@[expose] public section


/-!
# Local nondegeneracy at the bad line `L₀`, trivial character, odd degree

For the trivial character and odd `n` the local value at the bad line `L₀` of the boundary trace is
nondegenerate against the local cohomology at the good plane (the dual plane of `L₀`).  Here
`-I ∉ Γ₁'(3)`, so the local cohomology at `L₀` is not forced to vanish by parity
(`ParityCases.BadLineOddInput`); the bridge of the Kostant pairing is the odd-degree bridge
`levelThreeBridgeBadOdd` with coefficients `Sym^{n+1}` (bad-line coordinate) and
`Sym^{n+1} ⊗ det⁻¹` (rotated dual coordinate).

* **The line coordinate.**  A line summand class `b` has Shapiro coordinate `cuspRes b` at `L₀` in the
  radical kernel (`HeckeAdjointMembership`); its bad-line edge, with the sign of the bridge, is the
  parabolic class `lineEdge b ∈ H¹_par(Γ₁'(3), Sym^{n+1})` (`BadIdentLine`).  It is a genuine
  eigenvector of the Hecke operators `T_p` with `x + p^{-(n+1)} T_p x = c(T_p) x`.
* **The plane coordinate.**  The good-plane edge, restricted to the joint generalized eigenspace `J`
  of the prime operators, lands in `H¹_par(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`.  The Levi class of the dual
  plane in the bridge is its transport by `thetaH1` (`BadIdentPlane.badXOdd'_apply`), so the pairing
  is `badGoodPairingOdd` (`LocalPairingCaseL0OddPairing`).
* **Nondegeneracy** (`exists_pairing_ne_zero`): the functional `η ↦ ⟨x, E η⟩` on the (Hecke-stable)
  subspace of local classes with parabolic edge is an eigenfunctional of the commuting operators
  `T_p`, by the level-three adjointness hypothesis `BadGoodHeckeAdjointOdd` and the edge formula
  `E (T_p y) = E y + p^{-(n+2)} T_p E y`, whose dual eigenvalue is `c(T_p)` again; it is nonzero by
  the left nondegeneracy of the pairing and the surjectivity of the good-plane edge; hence nonzero on
  the joint generalized eigenspace.
* **Value** (`lineValue_eq_pairing`): the local value is `-(n+1)!/3` times the pairing of the classes
  of the Levi cocycles of the bridge `levelThreeBridgeBadOdd`, which are the edge classes
  (`BadIdentLine`, `BadIdentPlane`).
* **Assembly** by `HeckeGenerators.localNondegenerate_of_edges_gen`, with `J ⊆ L` for the good plane
  from `HeckeGenEq.localJointGen_eq_localJoint_goodPlane_trivial`; the final statements are
  `localNondegenerate_L0_odd` and `badLineOddInput` (`ParityCases.BadLineOddInput n`), whose only
  extra hypothesis is the level-three adjointness `BadGoodHeckeAdjointOdd`, or, in
  `localNondegenerate_L0_odd_of_adjoint` and `badLineOddInput_of_adjoint`, the standard adjointness
  `AdjointLevelThreePairing.BadGoodHeckeAdjoint` together with `ThetaHeckeCommute`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLinear
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd

open TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators
  (localJointGen localNondegenerate_of_edges_gen)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership (trivialData)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed parabolicCrossedH1 parabolicPairing mem_parabolicCrossed_of_mem
    twistedPairing_badLine_goodPlane jointEdgeMap_mem_parabolicCrossedH1
    goodPlaneEdge_mem_parabolicCrossedH1)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
  (relG goodPlaneEdge_cusp_eq badXOdd'_apply)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (badX badXOdd' levelThreeBridgeBadOdd)
open TernaryPeriodPolynomials.LevelThree.BadLineFinal
  (badLineEdge badLineEdge_injective badLine_localOp_eq badLine_localOp_mem_kernel)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal (badLineLocalRadicalKernel)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (badLevelHecke)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
  (goodPlaneEdge goodPlane_finiteDimensional)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (goodPlaneEdgeCocycle)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot (qcls)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddTransport
  (transportH1_qcls transportCocycles)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree
  (badGoodPairing BadGoodHeckeAdjoint LevelThreeParabolicAdjoint levelThreeKappa
    levelThreeKappa_ne_zero dualEigenvalue_badGood goodPlane_pairing_eigen_parabolic
    parabolicHecke parabolicHecke_coe levelHecke_mem_parabolicCrossedH1)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
  (latL0 latL0_le latL0_le_e₀)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₀ endpoint_line_e₀)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
  (exists_omegaU exists_thetaU)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL0 (fiberHyp_line)
open TernaryPeriodPolynomials.BoundaryDuality.FiberParabolicL0
  (lineValue_badLine_parabolicPairing)

variable {n : ℕ}

/-! ### Commutation of the local operators -/

/-- **The local operators of away-from-three correspondences commute.**  Every local class is a
Shapiro coordinate (`cuspLift`), and the Hecke operators of the stratum commute. -/
theorem localOp_comm {χ : RankOneCharacter} (hecke : BoundaryHecke n χ)
    (hhecke : ActualBoundaryHecke n χ hecke) (s t : HeckeCorrespondence) (hs : AwayThree s)
    (ht : AwayThree t) (side : Side) (good : Bool) :
    Commute (localOp n χ s hs side good) (localOp n χ t ht side good) := by
  have hcomm := TernaryPeriodPolynomials.HeckeCommutativity.realizesHecke_comm_all
    (flagRepresentation (rationalCoefficientComponent n χ) side) (hecke side) (hhecke side)
    (TernaryPeriodPolynomials.HeckeCommutativity.good_of_awayThree hs) t
  change localOp n χ s hs side good * localOp n χ t ht side good =
    localOp n χ t ht side good * localOp n χ s hs side good
  apply LinearMap.ext
  intro η
  obtain ⟨a, rfl⟩ : ∃ a, cuspRes n χ side good a = η :=
    ⟨CuspLift.cuspLift n χ side good η, CuspLift.cuspRes_cuspLift side good η⟩
  calc localOp n χ s hs side good (localOp n χ t ht side good (cuspRes n χ side good a))
      = cuspRes n χ side good (hecke side s (hecke side t a)) := by
        rw [cuspRes_hecke hecke hhecke s hs, cuspRes_hecke hecke hhecke t ht]
    _ = cuspRes n χ side good (hecke side t (hecke side s a)) := by
        rw [show hecke side s (hecke side t a) = hecke side t (hecke side s a) from
          LinearMap.congr_fun hcomm a]
    _ = localOp n χ t ht side good (localOp n χ s hs side good (cuspRes n χ side good a)) := by
        rw [cuspRes_hecke hecke hhecke t ht, cuspRes_hecke hecke hhecke s hs]

/-! ### The line side -/

/-- **Negation and restriction of an eigen-relation** (generic): if `c z = z + s H z` and `q` is the
element of a `H`-stable submodule with underlying vector `-z`, then `q + s H q = c q`. -/
theorem restrict_eigen_neg {X : Type*} [AddCommGroup X] [Module ℂ X] (Q : Submodule ℂ X)
    (H : Module.End ℂ X) (hQ : ∀ x ∈ Q, H x ∈ Q) (s c : ℂ) (z : X) (q : Q) (hq : (q : X) = -z)
    (h : c • z = z + s • H z) :
    (1 : ℂ) • q + s • (H.restrict hQ) q = c • q := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, one_smul,
    LinearMap.coe_restrict_apply, hq, map_neg, smul_neg, smul_neg, ← neg_add, ← h]

/-- **The eigen-relation of the bad-line edge of an eigenvector of the local operator** (stated for
an abstract element of the radical kernel). -/
theorem badLineEdge_eigen_aux (hn0 : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3) (c : ℂ)
    (y : badLineLocalRadicalKernel n)
    (hy : localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
      .line false y.1 = c • y.1) :
    c • badLineEdge n hn0 y = badLineEdge n hn0 y +
      ((p.val : ℂ) ^ (n + 1))⁻¹ • badLevelHecke p hp3 n (badLineEdge n hn0 y) := by
  have hy'' := badLine_localOp_mem_kernel n p hp3 y.1 y.2
  have h1 := badLine_localOp_eq n hn0 p hp3 y.1 y.2 hy''
  have h2 : (⟨localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
      .line false y.1, hy''⟩ : badLineLocalRadicalKernel n) = c • y := Subtype.ext hy
  exact (map_smul (badLineEdge n hn0) c y).symm.trans ((congrArg (badLineEdge n hn0) h2).symm.trans h1)


section LineSide

variable (cusp : CuspidalRepresentation) (coh : Cohomological cusp n)
  (hecke : BoundaryHecke n trivialCharacter) (hhecke : ActualBoundaryHecke n trivialCharacter hecke)
  (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)

include hn hne in
/-- **The Shapiro coordinate at the bad line of a line summand class**, in the radical kernel. -/
def lineCoord : boundarySummand (trivialData cusp coh) .line →ₗ[ℂ] badLineLocalRadicalKernel n :=
  LinearMap.codRestrict (badLineLocalRadicalKernel n)
    ((cuspRes n trivialCharacter .line false).comp
      (boundarySummand (trivialData cusp coh) .line).subtype)
    (fun b => HeckeAdjointMembership.cuspRes_line_false_mem_radicalKernel cusp coh hecke hhecke hn
      hne b.2)

/-- The bad-line edge of the coordinate of a line summand class, with the sign of the bridge. -/
def lineEdgeCl : boundarySummand (trivialData cusp coh) .line →ₗ[ℂ]
    CrossedH1 (levelRep (n + 1) 0) :=
  -((badLineEdge n (by omega : 0 < n)).comp (lineCoord cusp coh hecke hhecke hn hne))

/-- The class `lineEdgeCl b` is parabolic. -/
theorem lineEdgeCl_mem (b : boundarySummand (trivialData cusp coh) .line) :
    lineEdgeCl cusp coh hecke hhecke hn hne b ∈
      parabolicCrossedH1 (levelRep (n + 1) 0) := by
  have hc := Separation.pairCharacter_two_sub_one_norm_le_of_trivial
    (trivialData cusp coh) rfl hecke hhecke hn hne
  have hy := Separation.cuspRes_mem_localJoint_of_mem (trivialData cusp coh) hecke
    hhecke .line false b.2
  change -badLineEdge n (by omega : 0 < n) (lineCoord cusp coh hecke hhecke hn hne b) ∈ _
  exact Submodule.neg_mem _ (jointEdgeMap_mem_parabolicCrossedH1 n hn _ hc ⟨_, hy⟩)

/-- **The parabolic bad-line edge class of a line summand class.** -/
def lineEdge : boundarySummand (trivialData cusp coh) .line →ₗ[ℂ]
    parabolicCrossedH1 (levelRep (n + 1) 0) :=
  LinearMap.codRestrict _ (lineEdgeCl cusp coh hecke hhecke hn hne)
    (lineEdgeCl_mem cusp coh hecke hhecke hn hne)

/-- The underlying class of `lineEdge`. -/
theorem lineEdge_coe (b : boundarySummand (trivialData cusp coh) .line) :
    ((lineEdge cusp coh hecke hhecke hn hne b : parabolicCrossedH1 (levelRep (n + 1) 0)) :
      CrossedH1 (levelRep (n + 1) 0)) =
      -badLineEdge n (by omega : 0 < n) (lineCoord cusp coh hecke hhecke hn hne b) := rfl

/-- A line summand class with nonzero coordinate at `L₀` has nonzero edge class. -/
theorem lineEdge_ne_zero (b : boundarySummand (trivialData cusp coh) .line)
    (hb : cuspRes n trivialCharacter .line false b.1 ≠ 0) :
    lineEdge cusp coh hecke hhecke hn hne b ≠ 0 := by
  intro h
  apply hb
  have h1 : -badLineEdge n (by omega : 0 < n) (lineCoord cusp coh hecke hhecke hn hne b) = 0 :=
    congrArg Subtype.val h
  have h2 := neg_eq_zero.mp h1
  have h3 := badLineEdge_injective n (by omega : 0 < n) (h2.trans (map_zero _).symm)
  exact congrArg Subtype.val h3

/-- **The bad-line edge class of a line summand class is an eigenvector** of the parabolic Hecke
operators: `x + p^{-(n+1)} T_p x = c(T_p) x`. -/
theorem lineEdge_eigen (b : boundarySummand (trivialData cusp coh) .line) (p : Nat.Primes)
    (hp3 : p.val ≠ 3) :
    (1 : ℂ) • lineEdge cusp coh hecke hhecke hn hne b +
        ((p.val : ℂ) ^ (n + 1))⁻¹ •
          parabolicHecke (n + 1) 0 p hp3 (lineEdge cusp coh hecke hhecke hn hne b) =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
        lineEdge cusp coh hecke hhecke hn hne b := by
  have hn0 : 0 < n := by omega
  have heig : localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
      .line false (lineCoord cusp coh hecke hhecke hn hne b).1 =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
        (lineCoord cusp coh hecke hhecke hn hne b).1 := by
    have hy1 : (lineCoord cusp coh hecke hhecke hn hne b).1 =
        cuspRes n trivialCharacter .line false b.1 := rfl
    rw [hy1, ← cuspRes_hecke hecke hhecke (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
      .line false,
      Separation.hecke_eq_pairCharacter_smul (trivialData cusp coh) hecke hhecke _
        (TpExistence.tp_awayThree p hp3) .line b.2, map_smul]
    rfl
  have key := badLineEdge_eigen_aux hn0 p hp3
    (pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p))
    (lineCoord cusp coh hecke hhecke hn hne b) heig
  exact restrict_eigen_neg (parabolicCrossedH1 (levelRep (n + 1) 0))
    (TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1.levelHecke (n + 1) 0 p
      hp3)
    (fun _ hx => levelHecke_mem_parabolicCrossedH1 (n + 1) 0 p hp3 hx) _ _
    (badLineEdge n hn0 (lineCoord cusp coh hecke hhecke hn hne b))
    (lineEdge cusp coh hecke hhecke hn hne b) (lineEdge_coe cusp coh hecke hhecke hn hne b) key

end LineSide

/-! ### The plane side and the nonvanishing of the pairing -/

section Nondegenerate

/-- **Nonvanishing of the pairing on the joint generalized eigenspace.**  Let `x` be a nonzero
parabolic class of the bad-line Levi cohomology which is an eigenvector of the Hecke operators
`x + p^{-(n+1)} T_p x = c(T_p) x`, and assume the level-three adjointness for the odd pairing.  Then
some local class `η` at the good plane in the joint generalized eigenspace of the prime operators for
`c` has parabolic edge and `⟨x, E η⟩ ≠ 0`. -/
theorem exists_pairing_ne_zero (hn0 : 0 < n) (hodd : Odd n) (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (c : HeckeCorrespondence → ℂ)
    (hadj : BadGoodHeckeAdjointOdd hodd) (x : parabolicCrossedH1 (levelRep (n + 1) 0))
    (hx0 : x ≠ 0)
    (hx : ∀ (p : Nat.Primes) (hp3 : p.val ≠ 3), (1 : ℂ) • x +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • parabolicHecke (n + 1) 0 p hp3 x = c (TpExistence.tp p) • x) :
    ∃ η ∈ localJointGen n trivialCharacter c .plane true,
      ∃ hpar : goodPlaneEdge hn0 η ∈ parabolicCrossedH1 (levelRep (n + 1) (-1)),
        badGoodPairingOdd hodd x ⟨goodPlaneEdge hn0 η, hpar⟩ ≠ 0 := by
  have := goodPlane_finiteDimensional hn0
  -- the local classes with parabolic edge
  let PE : Submodule ℂ (CuspH2 n trivialCharacter .plane true) :=
    (parabolicCrossedH1 (levelRep (n + 1) (-1))).comap (goodPlaneEdge hn0)
  let A : {p : Nat.Primes // p.val ≠ 3} → Module.End ℂ (CuspH2 n trivialCharacter .plane true) :=
    fun p => localOp n trivialCharacter (TpExistence.tp p.1) (TpExistence.tp_awayThree p.1 p.2)
      .plane true
  have hA : ∀ (p : {p : Nat.Primes // p.val ≠ 3}) (η : CuspH2 n trivialCharacter .plane true),
      η ∈ PE → A p η ∈ PE := by
    intro p η hη
    change goodPlaneEdge hn0 (A p η) ∈ parabolicCrossedH1 (levelRep (n + 1) (-1))
    rw [show goodPlaneEdge hn0 (A p η) = goodPlaneEdge hn0 η + ((p.1.val : ℂ) ^ (n + 2))⁻¹ •
      TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1.levelHecke (n + 1) (-1)
        p.1 p.2 (goodPlaneEdge hn0 η) from
      TernaryPeriodPolynomials.LevelThree.GoodPlaneLocalOp.goodPlaneEdge_localOp_tp
        p.1 p.2 n hn0 η]
    exact Submodule.add_mem _ hη (Submodule.smul_mem _ _
      (levelHecke_mem_parabolicCrossedH1 (n + 1) (-1) p.1 p.2 hη))
  let B : {p : Nat.Primes // p.val ≠ 3} → Module.End ℂ PE := fun p =>
    (A p).restrict (fun η hη => hA p η hη)
  have hfinPE : FiniteDimensional ℂ PE := FiniteDimensional.finiteDimensional_submodule PE
  have hcomm : ∀ p q, Commute (B p) (B q) := by
    intro p q
    have h := localOp_comm hecke hhecke (TpExistence.tp p.1) (TpExistence.tp q.1)
      (TpExistence.tp_awayThree p.1 p.2) (TpExistence.tp_awayThree q.1 q.2) .plane true
    have key : B p * B q = B q * B p :=
      LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun h.eq w.1)
    exact key
  -- the functional
  let φ : PE →ₗ[ℂ] ℂ := (badGoodPairingOdd hodd x).comp
    ((goodPlaneEdge hn0).restrict (fun _ hη => hη))
  have hφ : ∀ (p : {p : Nat.Primes // p.val ≠ 3}) (w : PE),
      φ (B p w) = c (TpExistence.tp p.1) * φ w := by
    intro p w
    have h := goodPlane_pairing_eigen_parabolic n hn0 p.1 p.2 (badGoodPairingOdd hodd)
      levelThreeKappa hadj (levelThreeKappa_ne_zero p.1) (a := 1)
      (s := ((p.1.val : ℂ) ^ (n + 1))⁻¹) (c := c (TpExistence.tp p.1))
      (inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.1.property.ne_zero))) (hx p.1 p.2) PE
      (fun η hη => hA p η hη) (fun η hη => hη) w.1 w.2
    rw [dualEigenvalue_badGood] at h
    exact h
  have hφ0 : φ ≠ 0 := by
    have : ∃ y, badGoodPairingOdd hodd x y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx0 (badGoodPairingOdd_left_nondegenerate hodd x hcon)
    obtain ⟨y, hy⟩ := this
    obtain ⟨η, hη⟩ := EdgeSurjGoodPlane.goodPlaneEdge_surjective (n := n) hn0 (y : CrossedH1 _)
    have hmem : η ∈ PE := by
      change goodPlaneEdge hn0 η ∈ parabolicCrossedH1 (levelRep (n + 1) (-1))
      rw [hη]
      exact y.2
    intro h0
    apply hy
    have h3 := LinearMap.congr_fun h0 ⟨η, hmem⟩
    have e : (⟨goodPlaneEdge hn0 η, hmem⟩ : parabolicCrossedH1 (levelRep (n + 1) (-1))) = y :=
      Subtype.ext hη
    change badGoodPairingOdd hodd x ⟨goodPlaneEdge hn0 η, hmem⟩ = 0 at h3
    rw [e] at h3
    exact h3
  obtain ⟨w, hw, hφw⟩ := exists_mem_jointSpace_of_functional B hcomm φ hφ0
    (fun p => c (TpExistence.tp p.1)) hφ
  have hJ : w.1 ∈ localJointGen n trivialCharacter c .plane true := by
    simp only [localJointGen, Submodule.mem_iInf]
    intro p
    exact intertwine_mem_maxGenEigenspace PE.subtype (B p) (A p) (fun _ => rfl)
      (c (TpExistence.tp p.1)) (mem_jointSpace_iff.mp hw p)
  exact ⟨w.1, hJ, w.2, hφw⟩

end Nondegenerate

/-! ### The value -/

section Value

/-- The quotient map and the class of a cocycle agree (generic statement). -/
theorem mkQ_eq_qcls {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (c : crossedCocycles ρ) :
    (crossedBoundaries ρ).mkQ c = qcls ρ c := rfl

/-- A parabolic cocycle together with the parabolic class it represents (generic statement). -/
theorem mkQ_pair_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ binaryArithmeticLevel V) (x : crossedCocycles ρ) (hx : x ∈ parabolicCrossed ρ)
    (q : parabolicCrossedH1 ρ) (h : (crossedBoundaries ρ).mkQ x = (q : CrossedH1 ρ)) :
    (⟨(crossedBoundaries ρ).mkQ x, Submodule.mem_map_of_mem hx⟩ : parabolicCrossedH1 ρ) = q :=
  Subtype.ext h

/-- **The class of the dual-coordinate cocycle `badXOdd'` is the transported good-plane edge.** -/
theorem qcls_badXOdd'_eq {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n} (hodd : Odd n) (hn0 : 0 < n)
    (hF : ParabolicDuality.IdentBad.BadLineFiber n Λe ζ η ω ωU θU)
    (y : MaximalCycles n trivialCharacter .plane)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane)) :
    qcls (levelRep (n + 1) (-1)) (badXOdd' hodd hF) =
      thetaH1 hodd (goodPlaneEdge hn0 (cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y))) := by
  have h := transportH1_qcls (levelRep (n + 1) (-1)) alphaHom (planeNeg n)
    (planeNeg_intertwines hodd) (goodPlaneEdgeCocycle (relG hF y hη))
  have hc : badXOdd' hodd hF = transportCocycles (levelRep (n + 1) (-1)) alphaHom (planeNeg n)
      (planeNeg_intertwines hodd) (goodPlaneEdgeCocycle (relG hF y hη)) :=
    Subtype.ext (funext fun γ => badXOdd'_apply hodd hF y hη γ)
  rw [goodPlaneEdge_cusp_eq hn0 hF y hη, hc]
  exact h.symm

variable (cusp : CuspidalRepresentation) (coh : Cohomological cusp n)
  (hecke : BoundaryHecke n trivialCharacter) (hhecke : ActualBoundaryHecke n trivialCharacter hecke)
  (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)

/-- **The class of the line cocycle `badX` is the bad-line edge class.** -/
theorem mkQ_badX_eq_lineEdge {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n} (hn0 : 0 < n)
    (hF : ParabolicDuality.IdentBad.BadLineFiber n Λe ζ η ω ωU θU)
    (z : MaximalCycles n trivialCharacter .line) (hζ : ∀ x, ζ x = z.val.val x L₀)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (trivialData cusp coh) .line) :
    (crossedBoundaries (levelRep (n + 1) 0)).mkQ (badX hn0 hF) =
      ((lineEdge cusp coh hecke hhecke hn hne ⟨_, hz⟩ :
        parabolicCrossedH1 (levelRep (n + 1) 0)) :
        CrossedH1 (levelRep (n + 1) 0)) :=
  (ParabolicDuality.IdentBad.mkQ_badX_eq_neg_badLineEdge_cusp hn0 hF z hζ).trans
    (lineEdge_coe cusp coh hecke hhecke hn hne ⟨_, hz⟩).symm

include hecke hhecke hn hne in
/-- **The `U`-primitives of the fiber integration at `L₀`** for a line summand class and an
arbitrary plane cocycle (restriction vanishing on the radical lattice). -/
theorem exists_primitives (hn0 : 0 < n)
    (z : MaximalCycles n trivialCharacter .line)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (trivialData cusp coh) .line)
    (y : MaximalCycles n trivialCharacter .plane) :
    ∃ ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n,
      (∀ γ ∈ latL0.sub, ∀ a b,
        ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b])) ∧
      (∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀) ∧
      ∃ θU : (Fin 2 → RationalGL3) → HomogeneousPoly n,
        (∀ γ ∈ latL0.sub, ∀ a b, θU ![γ * a, γ * b] =
          rationalCoefficientComponent n trivialCharacter
            ((dualityData n trivialCharacter).φ γ) (θU ![a, b])) ∧
        (∀ a b c, differentialOneRaw θU ![a, b, c] =
          y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
            (dualityData n trivialCharacter).φ c]
            ((dualityData n trivialCharacter).dualFlag L₀)) := by
  obtain ⟨ωU, hωU, hdωU⟩ := exists_omegaU z L₀ latL0.sub latL0_le
    (HeckeAdjointMembershipBad.classOf_lineRestriction_L₀_eq_zero cusp coh hecke hhecke hn hne z hz)
  obtain ⟨θU, hθU, hdθU⟩ := exists_thetaU (dualityData n trivialCharacter) y L₀ latL0.sub
    latL0_le (HeckeAdjointMembershipPlane.classOf_planeRestriction_L₀_eq_zero hn0 y)
  exact ⟨ωU, hωU, hdωU, θU, hθU, hdθU⟩

/-- **The local value at the bad line is a multiple of the pairing of the edge classes**, for
given `U`-primitives. -/
theorem lineValue_eq_pairing_of_primitives (hodd : Odd n)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (trivialData cusp coh) .line)
    (hw : EdgePrimitive z w)
    (hyP : goodPlaneEdge (by omega : 0 < n) (cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)) ∈
      parabolicCrossedH1 (levelRep (n + 1) (-1)))
    (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b, θU ![γ * a, γ * b] =
      rationalCoefficientComponent n trivialCharacter ((dualityData n trivialCharacter).φ γ)
        (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₀)) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y =
      (-((n + 1).factorial : ℂ) / 3) *
        badGoodPairingOdd hodd (lineEdge cusp coh hecke hhecke hn hne ⟨_, hz⟩)
          ⟨goodPlaneEdge (by omega : 0 < n) (cuspRes n trivialCharacter .plane true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
            hyP⟩ := by
  have hn0 : 0 < n := by omega
  have hF := fiberHyp_line (dualityData n trivialCharacter) endpoint_line_e₀ latL0_le latL0_le_e₀
    z w y hw ωU hωU hdωU θU hθU hdθU
  have hη' := ParabolicDuality.IdentBad.hη_flag
    (η := fun x => y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      ((dualityData n trivialCharacter).dualFlag L₀)) y (fun _ => rfl)
  have hxcls := mkQ_badX_eq_lineEdge cusp coh hecke hhecke hn hne hn0 hF z (fun _ => rfl) hz
  have hycls := qcls_badXOdd'_eq hodd hn0 hF y hη'
  have hx : badX hn0 hF ∈ parabolicCrossed (levelRep (n + 1) 0) :=
    mem_parabolicCrossed_of_mem _ (Eq.mp (congrArg (· ∈ parabolicCrossedH1 (levelRep (n + 1) 0))
      hxcls.symm) (lineEdge cusp coh hecke hhecke hn hne _).2)
  have hx' : badXOdd' hodd hF ∈ parabolicCrossed (levelRep (n + 1) (-1)) :=
    ParabolicDuality.IdentBad.mem_parabolicCrossed_of_qcls _ _
      (Eq.mp (congrArg (· ∈ parabolicCrossedH1 (levelRep (n + 1) (-1))) hycls.symm)
        (thetaH1_mem hodd hyP))
  have e1 := mkQ_pair_eq (levelRep (n + 1) 0) (badX hn0 hF) hx
    (lineEdge cusp coh hecke hhecke hn hne ⟨_, hz⟩) hxcls
  have e2 := mkQ_pair_eq (levelRep (n + 1) (-1)) (badXOdd' hodd hF) hx'
    (thetaPar hodd ⟨goodPlaneEdge hn0 (cuspRes n trivialCharacter .plane true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
      hyP⟩) ((mkQ_eq_qcls _ _).trans hycls)
  have hval := lineValue_badLine_parabolicPairing (dualityData n trivialCharacter) z w y hw
    (StabilizerVanishing.topVanishing_levelStabilizer L₀) ωU hωU hdωU θU hθU hdθU
    (twistedPairing_badLine_goodPlane hodd) hx hx' (levelThreeBridgeBadOdd hodd hF)
  refine hval.trans ?_
  refine congrArg (fun t => (-((n + 1).factorial : ℂ) / 3) * t) ?_
  exact congrArg₂ (fun u v => badGoodPairing hodd u v) e1 e2

/-- **The local value at the bad line is a multiple of the pairing of the edge classes.** -/
theorem lineValue_eq_pairing (hodd : Odd n)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (trivialData cusp coh) .line)
    (hw : EdgePrimitive z w)
    (hyP : goodPlaneEdge (by omega : 0 < n) (cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)) ∈
      parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y =
      (-((n + 1).factorial : ℂ) / 3) *
        badGoodPairingOdd hodd (lineEdge cusp coh hecke hhecke hn hne ⟨_, hz⟩)
          ⟨goodPlaneEdge (by omega : 0 < n) (cuspRes n trivialCharacter .plane true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
            hyP⟩ := by
  obtain ⟨ωU, hωU, hdωU, θU, hθU, hdθU⟩ :=
    exists_primitives cusp coh hecke hhecke hn hne (by omega : 0 < n) z hz y
  exact lineValue_eq_pairing_of_primitives cusp coh hecke hhecke hn hne hodd z w y hz hw hyP ωU θU
    hωU hdωU hθU hdθU

end Value

/-! ### Assembly -/

section Assembly

variable (cusp : CuspidalRepresentation) (coh : Cohomological cusp n)
  (hecke : BoundaryHecke n trivialCharacter) (hhecke : ActualBoundaryHecke n trivialCharacter hecke)

/-- **Local nondegeneracy at the bad line, trivial character, odd degree**, given the comparison
`J ⊆ L` of the prime joint generalized eigenspace and the full joint generalized eigenspace at the
good plane, and the Hecke adjointness for the odd pairing. -/
theorem localNondegenerate_L0_odd_of_gen (hn : 3 ≤ n) (hodd : Odd n)
    (hne : associatePair (trivialData cusp coh) ≠ ⊥) (hadj : BadGoodHeckeAdjointOdd hodd)
    (hJ : localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
        .plane true ≤
      localJoint n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke) .plane true) :
    LocalNondegenerate traceDataL2 (trivialData cusp coh) (dualityData n trivialCharacter) hecke
      hhecke 0 true := by
  have hn0 : 0 < n := by omega
  have hc := Separation.pairCharacter_two_sub_one_norm_le_of_trivial
    (trivialData cusp coh) rfl hecke hhecke hn hne
  let g' : localJointGen n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke)
      .plane true →ₗ[ℂ] parabolicCrossedH1 (levelRep (n + 1) (-1)) :=
    LinearMap.codRestrict _ ((goodPlaneEdge hn0).comp (Submodule.subtype _))
      (fun η => goodPlaneEdge_mem_parabolicCrossedH1 n (by omega) _ hc (hJ η.2))
  refine localNondegenerate_of_edges_gen traceDataL2 (D := trivialData cusp coh)
    (dualityData n trivialCharacter) hecke hhecke 0 true hJ (badGoodPairingOdd hodd) (lineEdge cusp coh hecke hhecke hn hne) g' ?_ ?_
  · intro b hb
    have hb' : cuspRes n trivialCharacter .line false b.1 ≠ 0 := fun h0 =>
      hb (ParityCases.fixedPointH2_eq_zero_of_cuspRes_side ParityCases.badLine_orbit h0)
    obtain ⟨η, hηJ, hpar, hne'⟩ := exists_pairing_ne_zero hn0 hodd hecke hhecke
      (pairCharacter (trivialData cusp coh) hecke hhecke) hadj
      (lineEdge cusp coh hecke hhecke hn hne b)
      (lineEdge_ne_zero cusp coh hecke hhecke hn hne b hb')
      (fun p hp3 => lineEdge_eigen cusp coh hecke hhecke hn hne b p hp3)
    exact ⟨⟨η, hηJ⟩, hne'⟩
  · intro z w y hz hy hw _ hne'
    have hyP : goodPlaneEdge hn0 (cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)) ∈
        parabolicCrossedH1 (levelRep (n + 1) (-1)) :=
      goodPlaneEdge_mem_parabolicCrossedH1 n (by omega) _ hc (hJ hy)
    have hv := lineValue_eq_pairing cusp coh hecke hhecke hn hne hodd z w y hz hw hyP
    have hfac : (-((n + 1).factorial : ℂ) / 3) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
        (by norm_num)
    exact fun h0 => mul_ne_zero hfac hne' (hv.symm.trans h0)

end Assembly

/-- **Local nondegeneracy at the bad line `L₀` for the trivial character and odd `n`**, for an
arbitrary inducing datum with trivial character, from the comparison `J ⊆ L` of the prime joint
generalized eigenspace and the full joint generalized eigenspace at the good plane, and the Hecke
adjointness `BadGoodHeckeAdjointOdd` of the odd pairing. -/
theorem localNondegenerate_L0_odd_of_gen' (hn : 3 ≤ n) (hodd : Odd n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hadj : BadGoodHeckeAdjointOdd hodd)
    (hJ : localJointGen n D.chi (pairCharacter D hecke hhecke) .plane true ≤
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane true) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 0
      (TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2.good 0) := by
  obtain ⟨cusp, chi, coh⟩ := D
  change chi = trivialCharacter at hχ
  subst hχ
  exact localNondegenerate_L0_odd_of_gen cusp coh hecke hhecke hn hodd hne hadj hJ

/-- **Local nondegeneracy at the bad line `L₀`, trivial character, odd degree.**  The only
hypothesis besides `3 ≤ n` and a nonzero associate pair is the level-three Hecke adjointness
`BadGoodHeckeAdjointOdd` of the odd pairing. -/
theorem localNondegenerate_L0_odd (hn : 3 ≤ n) (hodd : Odd n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hadj : BadGoodHeckeAdjointOdd hodd) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 0
      (TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2.good 0) :=
  localNondegenerate_L0_odd_of_gen' hn hodd D hχ hecke hhecke hne hadj
    (HeckeGenEq.localJointGen_eq_localJoint_goodPlane_trivial hn D hχ hecke hhecke hne).le

/-- **The bad-line case of odd degree** (`ParityCases.BadLineOddInput`), from the level-three Hecke
adjointness `BadGoodHeckeAdjointOdd` for the odd pairing. -/
theorem badLineOddInput (hn : 3 ≤ n) (hadj : ∀ hodd : Odd n, BadGoodHeckeAdjointOdd hodd) :
    ParityCases.BadLineOddInput n :=
  fun D hecke hhecke hχ hodd hne =>
    localNondegenerate_L0_odd hn hodd D hχ hecke hhecke hne (hadj hodd)

/-- **Local nondegeneracy at the bad line `L₀`, trivial character, odd degree**, from the standard
level-three adjointness `AdjointLevelThreePairing.BadGoodHeckeAdjoint` of the bad-line / good-plane
Lefschetz pairing and the commutation of the transport with the Hecke operators. -/
theorem localNondegenerate_L0_odd_of_adjoint (hn : 3 ≤ n) (hodd : Odd n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hcomm : ThetaHeckeCommute hodd) (hadj : BadGoodHeckeAdjoint hodd) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 0
      (TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2.good 0) :=
  localNondegenerate_L0_odd hn hodd D hχ hecke hhecke hne
    (badGoodHeckeAdjointOdd_of_commute hodd hcomm hadj)

/-- **The bad-line case of odd degree** (`ParityCases.BadLineOddInput`) from the standard
level-three adjointness and the commutation of the transport with the Hecke operators. -/
theorem badLineOddInput_of_adjoint (hn : 3 ≤ n) (hcomm : ∀ hodd : Odd n, ThetaHeckeCommute hodd)
    (hadj : ∀ hodd : Odd n, BadGoodHeckeAdjoint hodd) : ParityCases.BadLineOddInput n :=
  badLineOddInput hn fun hodd => badGoodHeckeAdjointOdd_of_commute hodd (hcomm hodd) (hadj hodd)

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd

end
