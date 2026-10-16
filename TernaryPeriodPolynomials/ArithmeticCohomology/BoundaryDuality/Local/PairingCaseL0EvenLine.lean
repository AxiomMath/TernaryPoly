module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GeneratorsJoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipBad
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EdgeSurjGoodPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelThree

@[expose] public section


/-!
# The line side and the nonvanishing of the even pairing on the prime eigenspace

* `lineEdge`: the parabolic bad-line edge class `lineEdge b ∈ H¹_par(Γ₁'(3), Sym^{n+1})` of a line
  summand class `b`, an eigenvector of the Hecke operators `x + p^{-(n+1)} T_p x = c(T_p) x`
  (`lineEdge_eigen`), nonzero when the coordinate of `b` at `L₀` is (`lineEdge_ne_zero`);
* `exists_pairing_ne_zero`: for a nonzero such eigenvector, the even pairing against the good-plane
  edge is nonzero on the joint generalized eigenspace of the prime operators, from the level-three
  adjointness `BadGoodHeckeAdjointEven`, the surjectivity of the good-plane edge, and the left
  nondegeneracy of the pairing.

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

open TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators (localJointGen)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership (trivialData)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed parabolicCrossedH1 parabolicPairing mem_parabolicCrossed_of_mem
    twistedPairing_binaryArithmeticRepresentation jointEdgeMap_mem_parabolicCrossedH1
    goodPlaneEdge_mem_parabolicCrossedH1)
open TernaryPeriodPolynomials.LevelThree.BadLineFinal
  (badLineEdge badLineEdge_injective badLine_localOp_eq badLine_localOp_mem_kernel)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal (badLineLocalRadicalKernel)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
  (goodPlaneEdge goodPlane_finiteDimensional)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (badLevelHecke)
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree
  (LevelThreeParabolicAdjoint levelThreeKappa levelThreeKappa_ne_zero dualEigenvalue_badGood
    goodPlane_pairing_eigen_parabolic parabolicHecke parabolicHecke_coe
    levelHecke_mem_parabolicCrossedH1)

variable {n : ℕ}

/-- The parabolic Hecke operator `T_p` of the bad-line Levi cohomology `H¹_par(Γ₁'(3), Sym^{n+1})`,
as an endomorphism of `parabolicCrossedH1 (binaryArithmeticRepresentation n)`. -/
abbrev heckeBad (p : Nat.Primes) (hp3 : p.val ≠ 3) :
    Module.End ℂ (parabolicCrossedH1 (binaryArithmeticRepresentation n)) :=
  parabolicHecke (n + 1) 0 p hp3

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
    CrossedH1 (binaryArithmeticRepresentation n) :=
  -((badLineEdge n (by omega : 0 < n)).comp (lineCoord cusp coh hecke hhecke hn hne))

/-- The value of `lineEdgeCl`. -/
theorem lineEdgeCl_apply (b : boundarySummand (trivialData cusp coh) .line) :
    lineEdgeCl cusp coh hecke hhecke hn hne b =
      -badLineEdge n (by omega : 0 < n) (lineCoord cusp coh hecke hhecke hn hne b) := rfl

/-- The class `lineEdgeCl b` is parabolic. -/
theorem lineEdgeCl_mem (b : boundarySummand (trivialData cusp coh) .line) :
    lineEdgeCl cusp coh hecke hhecke hn hne b ∈
      parabolicCrossedH1 (binaryArithmeticRepresentation n) := by
  have hc := Separation.pairCharacter_two_sub_one_norm_le_of_trivial
    (trivialData cusp coh) rfl hecke hhecke hn hne
  have hy := Separation.cuspRes_mem_localJoint_of_mem (trivialData cusp coh) hecke
    hhecke .line false b.2
  change -badLineEdge n (by omega : 0 < n) (lineCoord cusp coh hecke hhecke hn hne b) ∈ _
  exact Submodule.neg_mem _ (jointEdgeMap_mem_parabolicCrossedH1 n hn _ hc ⟨_, hy⟩)

/-- **The parabolic bad-line edge class of a line summand class.** -/
def lineEdge : boundarySummand (trivialData cusp coh) .line →ₗ[ℂ]
    parabolicCrossedH1 (binaryArithmeticRepresentation n) :=
  LinearMap.codRestrict _ (lineEdgeCl cusp coh hecke hhecke hn hne)
    (lineEdgeCl_mem cusp coh hecke hhecke hn hne)

/-- The underlying class of `lineEdge`. -/
theorem lineEdge_coe (b : boundarySummand (trivialData cusp coh) .line) :
    ((lineEdge cusp coh hecke hhecke hn hne b :
      parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
      CrossedH1 (binaryArithmeticRepresentation n)) =
      -badLineEdge n (by omega : 0 < n) (lineCoord cusp coh hecke hhecke hn hne b) := rfl

/-- A negated injective image of a nonzero vector is nonzero. -/
theorem ne_zero_of_injective_neg {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] (f : A →ₗ[ℂ] B) (hf : Function.Injective f) (a : A) (ha : a ≠ 0) : -f a ≠ 0 := by
  intro h
  apply ha
  apply hf
  rw [f.map_zero]
  exact neg_eq_zero.mp h

/-- A line summand class with nonzero coordinate at `L₀` has nonzero edge class. -/
theorem lineEdge_ne_zero (b : boundarySummand (trivialData cusp coh) .line)
    (hb : cuspRes n trivialCharacter .line false b.1 ≠ 0) :
    lineEdge cusp coh hecke hhecke hn hne b ≠ 0 := by
  intro h
  have hcoord : lineCoord cusp coh hecke hhecke hn hne b ≠ 0 := fun h0 =>
    hb (congrArg Subtype.val h0)
  exact ne_zero_of_injective_neg (badLineEdge n (by omega : 0 < n))
    (badLineEdge_injective n (by omega : 0 < n)) _ hcoord
    ((lineEdge_coe cusp coh hecke hhecke hn hne b).symm.trans (congrArg Subtype.val h))

/-- Negating an eigen-edge `c e = e + s T e` gives the same relation. -/
theorem eigen_neg {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (e : V)
    (c s : ℂ) (h : c • e = e + s • T e) : (1 : ℂ) • (-e) + s • T (-e) = c • (-e) := by
  rw [map_neg, smul_neg, smul_neg, smul_neg, one_smul, ← neg_add, ← h]

/-- **The bad-line edge of a line summand class is an eigenvector** of the Hecke operators:
`x + p^{-(n+1)} T_p x = c(T_p) x`, on the crossed `H¹`. -/
theorem lineEdgeCl_eigen (b : boundarySummand (trivialData cusp coh) .line) (p : Nat.Primes)
    (hp3 : p.val ≠ 3) :
    (1 : ℂ) • lineEdgeCl cusp coh hecke hhecke hn hne b +
        ((p.val : ℂ) ^ (n + 1))⁻¹ •
          badLevelHecke p hp3 n (lineEdgeCl cusp coh hecke hhecke hn hne b) =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
        lineEdgeCl cusp coh hecke hhecke hn hne b := by
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
        (TpExistence.tp_awayThree p hp3) .line b.2,
      (cuspRes n trivialCharacter .line false).map_smul]
    rfl
  have hy'' := badLine_localOp_mem_kernel n p hp3 (lineCoord cusp coh hecke hhecke hn hne b).1
    (lineCoord cusp coh hecke hhecke hn hne b).2
  have h1 := badLine_localOp_eq n hn0 p hp3 (lineCoord cusp coh hecke hhecke hn hne b).1
    (lineCoord cusp coh hecke hhecke hn hne b).2 hy''
  have h2 : (⟨localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
      .line false (lineCoord cusp coh hecke hhecke hn hne b).1, hy''⟩ :
        badLineLocalRadicalKernel n) =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
        lineCoord cusp coh hecke hhecke hn hne b :=
    Subtype.ext heig
  have hmap : badLineEdge n hn0 (pairCharacter (trivialData cusp coh) hecke hhecke
      (TpExistence.tp p) • lineCoord cusp coh hecke hhecke hn hne b) =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
        badLineEdge n hn0 (lineCoord cusp coh hecke hhecke hn hne b) :=
    (badLineEdge n hn0).map_smul _ _
  have h3 : pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
      badLineEdge n hn0 (lineCoord cusp coh hecke hhecke hn hne b) =
      badLineEdge n hn0 (lineCoord cusp coh hecke hhecke hn hne b) +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • badLevelHecke p hp3 n
          (badLineEdge n hn0 (lineCoord cusp coh hecke hhecke hn hne b)) :=
    hmap.symm.trans ((congrArg (fun t => badLineEdge n hn0 t) h2.symm).trans h1)
  rw [lineEdgeCl_apply]
  exact eigen_neg (badLevelHecke p hp3 n)
    (badLineEdge n hn0 (lineCoord cusp coh hecke hhecke hn hne b)) _ _ h3

/-- An eigen-relation of a vector of a submodule stable under `T`, in the ambient module, gives the
relation in the submodule. -/
theorem subtype_eigen {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V)
    (T : Module.End ℂ V) (hT : ∀ x ∈ S, T x ∈ S) (x : S) (a s c : ℂ)
    (h : a • (x : V) + s • T x = c • (x : V)) :
    a • x + s • (T.restrict hT) x = c • x :=
  Subtype.ext h

/-- The underlying class of `lineEdge` is `lineEdgeCl`. -/
theorem lineEdge_val (b : boundarySummand (trivialData cusp coh) .line) :
    ((lineEdge cusp coh hecke hhecke hn hne b :
      parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
      CrossedH1 (binaryArithmeticRepresentation n)) = lineEdgeCl cusp coh hecke hhecke hn hne b :=
  rfl

/-- **The parabolic edge class of a line summand class is an eigenvector** of the parabolic Hecke
operators. -/
theorem lineEdge_eigen (b : boundarySummand (trivialData cusp coh) .line) (p : Nat.Primes)
    (hp3 : p.val ≠ 3) :
    (1 : ℂ) • lineEdge cusp coh hecke hhecke hn hne b +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • heckeBad p hp3 (lineEdge cusp coh hecke hhecke hn hne b) =
      pairCharacter (trivialData cusp coh) hecke hhecke (TpExistence.tp p) •
        lineEdge cusp coh hecke hhecke hn hne b :=
  subtype_eigen (parabolicCrossedH1 (binaryArithmeticRepresentation n)) (badLevelHecke p hp3 n)
    (fun _ hx => levelHecke_mem_parabolicCrossedH1 (n + 1) 0 p hp3 hx)
    (lineEdge cusp coh hecke hhecke hn hne b) 1 _ _
    (by rw [lineEdge_val]; exact lineEdgeCl_eigen cusp coh hecke hhecke hn hne b p hp3)

end LineSide

/-! ### The plane side and the nonvanishing of the pairing -/

section Nondegenerate

/-- **Nonvanishing of the pairing on the joint generalized eigenspace.**  Let `x` be a nonzero
parabolic class of the bad-line Levi cohomology which is an eigenvector of the Hecke operators
`x + p^{-(n+1)} T_p x = c(T_p) x`, and assume the level-three adjointness for the even pairing.
Then some local class `η` at the good plane in the joint generalized eigenspace of the prime
operators for `c` has parabolic edge and `⟨x, E η⟩ ≠ 0`. -/
theorem exists_pairing_ne_zero (hn0 : 0 < n) (heven : Even n)
    (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (c : HeckeCorrespondence → ℂ)
    (hadj : BadGoodHeckeAdjointEven heven)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (hx0 : x ≠ 0)
    (hx : ∀ (p : Nat.Primes) (hp3 : p.val ≠ 3), (1 : ℂ) • x +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • heckeBad p hp3 x = c (TpExistence.tp p) • x) :
    ∃ η ∈ localJointGen n trivialCharacter c .plane true,
      ∃ hpar : goodPlaneEdge hn0 η ∈ parabolicCrossedH1 (levelRep (n + 1) (-1)),
        badGoodPairingEven heven x ⟨goodPlaneEdge hn0 η, hpar⟩ ≠ 0 := by
  have hfd := goodPlane_finiteDimensional hn0
  -- the local classes with parabolic edge
  let PP : Submodule ℂ (CuspH2 n trivialCharacter .plane true) :=
    (parabolicCrossedH1 (levelRep (n + 1) (-1))).comap (goodPlaneEdge hn0)
  have hfdPP : FiniteDimensional ℂ PP := FiniteDimensional.finiteDimensional_submodule PP
  let A : {p : Nat.Primes // p.val ≠ 3} → Module.End ℂ (CuspH2 n trivialCharacter .plane true) :=
    fun p => localOp n trivialCharacter (TpExistence.tp p.1) (TpExistence.tp_awayThree p.1 p.2)
      .plane true
  have hA : ∀ (p : {p : Nat.Primes // p.val ≠ 3}) (η : CuspH2 n trivialCharacter .plane true),
      η ∈ PP → A p η ∈ PP := by
    intro p η hη
    change goodPlaneEdge hn0 (A p η) ∈ parabolicCrossedH1 (levelRep (n + 1) (-1))
    rw [show goodPlaneEdge hn0 (A p η) = goodPlaneEdge hn0 η + ((p.1.val : ℂ) ^ (n + 2))⁻¹ •
      TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1.levelHecke (n + 1) (-1)
        p.1 p.2 (goodPlaneEdge hn0 η) from
      TernaryPeriodPolynomials.LevelThree.GoodPlaneLocalOp.goodPlaneEdge_localOp_tp
        p.1 p.2 n hn0 η]
    exact Submodule.add_mem _ hη (Submodule.smul_mem _ _
      (levelHecke_mem_parabolicCrossedH1 (n + 1) (-1) p.1 p.2 hη))
  let B : {p : Nat.Primes // p.val ≠ 3} → Module.End ℂ PP := fun p =>
    (A p).restrict (fun η hη => hA p η hη)
  have hcomm : ∀ p q, Commute (B p) (B q) := by
    intro p q
    have h := localOp_comm hecke hhecke (TpExistence.tp p.1) (TpExistence.tp q.1)
      (TpExistence.tp_awayThree p.1 p.2) (TpExistence.tp_awayThree q.1 q.2) .plane true
    have key : B p * B q = B q * B p :=
      LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun h.eq w.1)
    exact key
  -- the functional
  let φ : PP →ₗ[ℂ] ℂ := (badGoodPairingEven heven x).comp
    ((goodPlaneEdge hn0).restrict (fun _ hη => hη))
  have hφ : ∀ (p : {p : Nat.Primes // p.val ≠ 3}) (w : PP),
      φ (B p w) = c (TpExistence.tp p.1) * φ w := by
    intro p w
    have h := goodPlane_pairing_eigen_parabolic n hn0 p.1 p.2 (badGoodPairingEven heven)
      levelThreeKappa hadj (levelThreeKappa_ne_zero p.1) (a := 1)
      (s := ((p.1.val : ℂ) ^ (n + 1))⁻¹) (c := c (TpExistence.tp p.1))
      (inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.1.property.ne_zero))) (hx p.1 p.2) PP
      (fun η hη => hA p η hη) (fun η hη => hη) w.1 w.2
    rw [dualEigenvalue_badGood] at h
    exact h
  have hφ0 : φ ≠ 0 := by
    have : ∃ y, badGoodPairingEven heven x y ≠ 0 := by
      by_contra hcon
      exact hx0 (badGoodPairingEven_left_nondegenerate heven x fun y =>
        not_not.mp fun h => hcon ⟨y, h⟩)
    obtain ⟨y, hy⟩ := this
    obtain ⟨η, hη⟩ := EdgeSurjGoodPlane.goodPlaneEdge_surjective (n := n) hn0 (y : CrossedH1 _)
    have hmem : η ∈ PP := by
      change goodPlaneEdge hn0 η ∈ parabolicCrossedH1 (levelRep (n + 1) (-1))
      rw [hη]
      exact y.2
    intro h0
    apply hy
    have h3 := LinearMap.congr_fun h0 ⟨η, hmem⟩
    have e : (⟨goodPlaneEdge hn0 η, hmem⟩ : parabolicCrossedH1 (levelRep (n + 1) (-1))) = y :=
      Subtype.ext hη
    change badGoodPairingEven heven x ⟨goodPlaneEdge hn0 η, hmem⟩ = 0 at h3
    rw [e] at h3
    exact h3
  obtain ⟨w, hw, hφw⟩ := exists_mem_jointSpace_of_functional B hcomm φ hφ0
    (fun p => c (TpExistence.tp p.1)) hφ
  have hJ : w.1 ∈ localJointGen n trivialCharacter c .plane true := by
    simp only [localJointGen, Submodule.mem_iInf]
    intro p
    exact intertwine_mem_maxGenEigenspace PP.subtype (B p) (A p) (fun _ => rfl)
      (c (TpExistence.tp p.1)) (mem_jointSpace_iff.mp hw p)
  exact ⟨w.1, hJ, w.2, hφw⟩

end Nondegenerate

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
