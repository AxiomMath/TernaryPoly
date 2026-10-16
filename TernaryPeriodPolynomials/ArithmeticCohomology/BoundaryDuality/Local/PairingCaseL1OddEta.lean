module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GeneratorsJoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EdgeSurjTwisted
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelOneParabolic

@[expose] public section


/-!
# A nonzero pairing on the prime eigenspace at the twisted identity plane

Let `ψ` be a nonzero functional on the parabolic classes of `H¹(GL₂(ℤ), Sym^{n+1})` which is an
eigenfunctional (`ψ (sgn_p y + p^{-(n+1)} T_p y) = c_p ψ(y)`, `c_p` the pair character at `T_p`) for
the Hecke operators `T_p`, `p ≠ 3`. Then `ψ ∘ E` is nonzero on the joint generalized eigenspace
`localJointGen` of the prime operators at the identity plane, where `E` is the twisted binary edge
(`exists_localJointGen_pairing_ne_zero`).

The functional `a ↦ ψ (E (cuspRes a))` lives on the subspace of plane strata classes whose edge is
parabolic; it is an eigenfunctional of the commuting Hecke operators of the plane, so it is nonzero
on a joint generalized eigenvector `a`, whose Shapiro coordinate lies in `localJointGen`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1OddEta

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLinear
  (exists_mem_jointSpace_of_functional mem_jointSpace_iff)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1 (arithmeticHecke)
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelOne
  (arithmeticHecke_mem_parabolicH1 parabolicHecke coe_parabolicHecke)

variable {n : ℕ}

/-- The plane classes whose twisted identity-plane edge is parabolic. -/
def paraSub (D : InducingData n) (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hn : 0 < n) (hodd : Odd n) : Submodule ℂ (StratumH2 n D.chi .plane) :=
  Submodule.comap
    ((Twisted.edgeH2T n D.chi hneg hn hodd).comp (cuspRes n D.chi .plane false))
    (parabolicH1 (arithmeticBinaryRep (n + 1) 0))

theorem mem_paraSub_iff (D : InducingData n)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n)
    (a : StratumH2 n D.chi .plane) :
    a ∈ paraSub D hneg hn hodd ↔
      Twisted.edgeH2T n D.chi hneg hn hodd (cuspRes n D.chi .plane false a) ∈
        parabolicH1 (arithmeticBinaryRep (n + 1) 0) :=
  Iff.rfl

/-- **The edge formula for an actual Hecke operator of the plane stratum.** -/
theorem edge_cuspRes_hecke (D : InducingData n)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (p : Nat.Primes) (hp3 : p.val ≠ 3) (a : StratumH2 n D.chi .plane) :
    Twisted.edgeH2T n D.chi hneg hn hodd
        (cuspRes n D.chi .plane false (hecke .plane (TpExistence.tp p) a)) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) •
          Twisted.edgeH2T n D.chi hneg hn hodd (cuspRes n D.chi .plane false a) +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • arithmeticHecke (n + 1) 0 p
          (Twisted.edgeH2T n D.chi hneg hn hodd (cuspRes n D.chi .plane false a)) := by
  rw [cuspRes_hecke hecke hhecke (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)]
  exact Twisted.edgeH2T_localOp_tp n D.chi hneg p hn hodd hp3 _

theorem hecke_mem_paraSub (D : InducingData n)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (p : Nat.Primes) (hp3 : p.val ≠ 3) {a : StratumH2 n D.chi .plane}
    (ha : a ∈ paraSub D hneg hn hodd) :
    hecke .plane (TpExistence.tp p) a ∈ paraSub D hneg hn hodd := by
  rw [mem_paraSub_iff] at ha ⊢
  rw [edge_cuspRes_hecke D hneg hn hodd hecke hhecke p hp3]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha)
    (Submodule.smul_mem _ _ (arithmeticHecke_mem_parabolicH1 (n + 1) 0 p ha))

/-- The restriction of the Hecke operator `T_p` of the plane stratum to the classes with parabolic
edge. -/
def heckeRestrict (D : InducingData n) (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hn : 0 < n) (hodd : Odd n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (p : {p : Nat.Primes // p.val ≠ 3}) :
    Module.End ℂ (paraSub D hneg hn hodd) :=
  (hecke .plane (TpExistence.tp p.1)).restrict fun _ ha =>
    hecke_mem_paraSub D hneg hn hodd hecke hhecke p.1 p.2 ha

/-- Powers of `f - μ` restricted to a submodule. -/
theorem coe_restrict_pow_sub {M : Type*} [AddCommGroup M] [Module ℂ M] (P : Submodule ℂ M)
    (f : Module.End ℂ M) (h : ∀ a ∈ P, f a ∈ P) (μ : ℂ) (k : ℕ) (a : P) :
    ((((f.restrict h - μ • 1) ^ k) a : P) : M) = ((f - μ • 1) ^ k) (a : M) := by
  have hone : ∀ a : P, (((f.restrict h - μ • 1) a : P) : M) = (f - μ • 1) (a : M) := by
    intro a
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Submodule.coe_sub, Submodule.coe_smul, LinearMap.coe_restrict_apply]
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, hone, pow_succ, Module.End.mul_apply]

theorem coe_heckeRestrict_pow_sub (D : InducingData n)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (p : {p : Nat.Primes // p.val ≠ 3}) (μ : ℂ) (k : ℕ) (a : paraSub D hneg hn hodd) :
    ((((heckeRestrict D hneg hn hodd hecke hhecke p - μ • 1) ^ k) a :
        paraSub D hneg hn hodd) : StratumH2 n D.chi .plane) =
      ((hecke .plane (TpExistence.tp p.1) - μ • 1) ^ k) (a : StratumH2 n D.chi .plane) :=
  coe_restrict_pow_sub _ _ _ μ k a

theorem heckeRestrict_comm (D : InducingData n)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (s t : {p : Nat.Primes // p.val ≠ 3}) :
    Commute (heckeRestrict D hneg hn hodd hecke hhecke s)
      (heckeRestrict D hneg hn hodd hecke hhecke t) := by
  have h := TernaryPeriodPolynomials.HeckeCommutativity.realizesHecke_comm_all
    (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) (hecke .plane)
    (hhecke .plane)
    (TernaryPeriodPolynomials.HeckeCommutativity.good_of_awayThree
      (TpExistence.tp_awayThree s.1 s.2)) (TpExistence.tp t.1)
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact LinearMap.congr_fun h a.1

/-- The edge of the Shapiro coordinate, on the plane classes with parabolic edge. -/
def edgeMap (D : InducingData n) (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hn : 0 < n) (hodd : Odd n) :
    paraSub D hneg hn hodd →ₗ[ℂ] parabolicH1 (arithmeticBinaryRep (n + 1) 0) :=
  LinearMap.codRestrict _
    (((Twisted.edgeH2T n D.chi hneg hn hodd).comp (cuspRes n D.chi .plane false)).comp
      (paraSub D hneg hn hodd).subtype) fun a => a.2

theorem coe_edgeMap (D : InducingData n) (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hn : 0 < n) (hodd : Odd n) (a : paraSub D hneg hn hodd) :
    (edgeMap D hneg hn hodd a : groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)) =
      Twisted.edgeH2T n D.chi hneg hn hodd (cuspRes n D.chi .plane false a.1) :=
  rfl

theorem edgeMap_heckeRestrict (D : InducingData n)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (p : {p : Nat.Primes // p.val ≠ 3}) (a : paraSub D hneg hn hodd) :
    edgeMap D hneg hn hodd (heckeRestrict D hneg hn hodd hecke hhecke p a) =
      ((IdentityPlaneLocalOp.sgnP p.1 : ℤ) : ℂ) • edgeMap D hneg hn hodd a +
        ((p.1.val : ℂ) ^ (n + 1))⁻¹ • parabolicHecke (n + 1) 0 p.1 (edgeMap D hneg hn hodd a) := by
  apply Subtype.ext
  rw [coe_edgeMap]
  exact edge_cuspRes_hecke D hneg hn hodd hecke hhecke p.1 p.2 a.1

/-- A nonzero functional on the parabolic classes composed with the edge is nonzero on the plane
classes with parabolic edge, since the edge is surjective and the Shapiro coordinate has a
section. -/
theorem comp_edgeMap_ne_zero (D : InducingData n)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n)
    (ψ : parabolicH1 (arithmeticBinaryRep (n + 1) 0) →ₗ[ℂ] ℂ) (hψ0 : ψ ≠ 0) :
    ψ.comp (edgeMap D hneg hn hodd) ≠ 0 := by
  obtain ⟨y', hy'⟩ := DFunLike.ne_iff.mp hψ0
  rw [LinearMap.zero_apply] at hy'
  obtain ⟨x, hx⟩ : ∃ x : CuspH2 n D.chi .plane false,
      Twisted.edgeH2T n D.chi hneg hn hodd x = y'.1 :=
    EdgeSurjTwisted.edgeH2T_surjective n D.chi hneg hn hodd y'.1
  have hmem : CuspLift.cuspLift n D.chi .plane false x ∈ paraSub D hneg hn hodd := by
    rw [mem_paraSub_iff, CuspLift.cuspRes_cuspLift, hx]
    exact y'.2
  have h2 : edgeMap D hneg hn hodd ⟨CuspLift.cuspLift n D.chi .plane false x, hmem⟩ = y' := by
    apply Subtype.ext
    rw [coe_edgeMap]
    change Twisted.edgeH2T n D.chi hneg hn hodd
      (cuspRes n D.chi .plane false (CuspLift.cuspLift n D.chi .plane false x)) = _
    rw [CuspLift.cuspRes_cuspLift, hx]
  intro h0
  apply hy'
  have h1 : ψ (edgeMap D hneg hn hodd ⟨CuspLift.cuspLift n D.chi .plane false x, hmem⟩) = 0 :=
    LinearMap.congr_fun h0 ⟨CuspLift.cuspLift n D.chi .plane false x, hmem⟩
  exact (congrArg ψ h2).symm.trans h1

/-- **A nonzero pairing on the prime eigenspace.** If `ψ` is a nonzero eigenfunctional of the
Hecke operators `T_p` (`p ≠ 3`) on the parabolic classes of `H¹(GL₂(ℤ), Sym^{n+1})`, with the
eigenvalues of the pair character, then `ψ ∘ E` is nonzero on the joint generalized eigenspace of
the prime operators at the twisted identity plane. -/
theorem exists_localJointGen_pairing_ne_zero (D : InducingData n)
    (hneg : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hc : ‖pairCharacter D hecke hhecke (TpExistence.tp LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    (hJ : localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false ≤
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane false)
    (ψ : parabolicH1 (arithmeticBinaryRep (n + 1) 0) →ₗ[ℂ] ℂ) (hψ0 : ψ ≠ 0)
    (hψ : ∀ (p : Nat.Primes), p.val ≠ 3 → ∀ y : parabolicH1 (arithmeticBinaryRep (n + 1) 0),
      ψ (((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • y +
          ((p.val : ℂ) ^ (n + 1))⁻¹ • parabolicHecke (n + 1) 0 p y) =
        pairCharacter D hecke hhecke (TpExistence.tp p) * ψ y) :
    ∃ (η : CuspH2 n D.chi .plane false)
      (hη : η ∈ localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false),
      ψ ⟨Twisted.edgeH2T n D.chi hneg hn hodd η,
        edgeH2T_mem_parabolicH1 n D.chi hneg hn hodd _ hc (hJ hη)⟩ ≠ 0 := by
  classical
  have hfin : FiniteDimensional ℂ (StratumH2 n D.chi .plane) :=
    HeckeAdjointLocal.finiteDimensional_plane n D.chi
  set φ : paraSub D hneg hn hodd →ₗ[ℂ] ℂ := ψ.comp (edgeMap D hneg hn hodd) with hφ
  have hφT : ∀ (p : {p : Nat.Primes // p.val ≠ 3}) (a : paraSub D hneg hn hodd),
      φ (heckeRestrict D hneg hn hodd hecke hhecke p a) =
        pairCharacter D hecke hhecke (TpExistence.tp p.1) * φ a := by
    intro p a
    simp only [hφ, LinearMap.comp_apply]
    rw [edgeMap_heckeRestrict]
    exact hψ p.1 p.2 _
  have hφ0 : φ ≠ 0 := comp_edgeMap_ne_zero D hneg hn hodd ψ hψ0
  obtain ⟨w, hw, hφw⟩ := exists_mem_jointSpace_of_functional
    (heckeRestrict D hneg hn hodd hecke hhecke) (heckeRestrict_comm D hneg hn hodd hecke hhecke)
    φ hφ0 (fun p => pairCharacter D hecke hhecke (TpExistence.tp p.1)) hφT
  refine ⟨cuspRes n D.chi .plane false w.1, ?_, ?_⟩
  · simp only [localJointGen, Submodule.mem_iInf]
    intro p
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (mem_jointSpace_iff.mp hw p)
    refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, ?_⟩
    rw [← cuspRes_hecke_sub_pow' hecke hhecke (TpExistence.tp p.1)
      (TpExistence.tp_awayThree p.1 p.2) .plane false _ k w.1,
      ← coe_heckeRestrict_pow_sub D hneg hn hodd hecke hhecke p _ k w, hk]
    simp
  · exact hφw

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1OddEta

end
