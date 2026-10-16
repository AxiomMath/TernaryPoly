module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.LocalChain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.Quotient
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Interface

@[expose] public section


/-!
# The bad-line edge map and the local upper bound from the period data

At the bad line (`cuspFlag .line false`, trivial character) the classes of the local cohomology
`H²(Γ_F, V)` with zero radical restriction form the subspace `K = badLineLocalRadicalKernel n`, and

* `badLineEdge`: the injective edge map `K → H¹(Γ₁'(3), Sym^{n+1})` (Sol's mixed map);
* `badLineEdge_localOp`: it intertwines `localOp (T_p)` with `1 + p^{-(n+1)} T_p`, where `T_p` is the
  level-three Hecke operator `badLevelHecke`;
* `localJoint_le_radicalKernel`: if `c(T_2)` is within `3/4` of `1`, the local joint generalized
  eigenspace lies in `K`, because `localOp (T_p) - λ_p` maps everything into `K`
  (`BadLineRestriction`) and `λ_2 = 3 ± 2^{-(n+1)}` has norm at least `2`;
* `localJoint_edge_mem_parabolic`: its edge image lies in the parabolic classes
  (`LevelThreeBoundaryQuotient`);
* `localUpperBound_badLine_two_of_period`: given an injective Hecke-equivariant period map from a
  finite-dimensional space `V` of cusp forms onto the parabolic classes, with joint generalized
  eigenspaces of dimension at most two, `LocalUpperBound n trivialCharacter c .line false 2`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Module
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators

namespace TernaryPeriodPolynomials.LevelThree.BadLineBound

open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThree
open BadLineLocal LevelThreeHeckeH1 LevelThreeCosets IdentityPlaneCosets

variable {n : ℕ}

/-- The primes `p ≠ 3`, indexing the away-from-three Hecke operators `T_p`. -/
abbrev Away := {p : Nat.Primes // p.val ≠ 3}

/-! ### The edge map and its Hecke equivariance -/

open TernaryPeriodPolynomials.LevelThree.BadLineFinal (badLineEdge badLineEdge_injective)

/-- **Intertwining**: `edge (localOp T_p y) = edge y + p^{-(n+1)} T_p (edge y)`. -/
theorem badLineEdge_localOp (n : ℕ) (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : badLineLocalRadicalKernel n) :
    badLineEdge n hn ⟨localOp n trivialCharacter (TpExistence.tp p)
        (TpExistence.tp_awayThree p hp3) .line false y.1,
      BadLineFinal.badLine_localOp_mem_kernel n p hp3 y.1 y.2⟩ =
      badLineEdge n hn y + ((p.val : ℂ) ^ (n + 1))⁻¹ •
        badLevelHecke p hp3 n (badLineEdge n hn y) :=
  BadLineFinal.badLine_localOp_eq n hn p hp3 y.1 y.2 _

/-! ### Numerics at `p = 2` -/

theorem norm_epsP_inv_le (p : Nat.Primes) : ‖((epsP p : ℤ) : ℂ)⁻¹‖ ≤ 1 := by
  have hne : epsP p ≠ 0 := by
    intro h0
    have h := epsP_natAbs p
    rw [h0] at h
    exact p.property.ne_zero (by simpa using h.symm)
  have h1 : (1 : ℝ) ≤ ‖((epsP p : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ h1

/-- The scalar `λ_p = p + 1 + ε_p^{-(n+1)}` has norm at least `2`. -/
theorem two_le_norm_lamB (n : ℕ) (p : Nat.Primes) : 2 ≤ ‖BadLineRestriction.lamB n p‖ := by
  have h1 : ‖(p.val : ℂ) + 1‖ = (p.val : ℝ) + 1 := by
    have := Complex.norm_natCast (p.val + 1)
    push_cast at this
    exact this
  have h2 : ‖(((epsP p : ℤ) : ℂ)⁻¹) ^ (n + 1)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_epsP_inv_le p)
  have h3 := norm_sub_le ((p.val : ℂ) + 1 + (((epsP p : ℤ) : ℂ)⁻¹) ^ (n + 1))
    ((((epsP p : ℤ) : ℂ)⁻¹) ^ (n + 1))
  rw [add_sub_cancel_right] at h3
  have hp : (2 : ℝ) ≤ p.val := by exact_mod_cast p.property.two_le
  unfold BadLineRestriction.lamB
  linarith

theorem ne_lamB_of_norm_le (n : ℕ) (p : Nat.Primes) (μ : ℂ) (h : ‖μ - 1‖ ≤ 3 / 4) :
    μ ≠ BadLineRestriction.lamB n p := by
  intro hμ
  have h1 := two_le_norm_lamB n p
  rw [← hμ] at h1
  have h3 : ‖μ‖ ≤ ‖μ - 1‖ + 1 := by
    have := norm_add_le (μ - 1) 1
    rwa [sub_add_cancel, norm_one] at this
  linarith

/-- An eigenvalue `(c - 1) p^{n+1}` with `c` within `3/4` of `1` is neither `q_∞` nor `q_0`. -/
theorem ne_qInf_qZero_two (hn : 1 ≤ n) (μ : ℂ) (h : ‖μ - 1‖ ≤ 3 / 4) :
    (μ - 1) / (((2 : ℕ) : ℂ) ^ (n + 1))⁻¹ ≠
        LevelThreeBoundaryHecke.qInf (n + 1) 0 LevelThreeBoundaryEisenstein.two ∧
      (μ - 1) / (((2 : ℕ) : ℂ) ^ (n + 1))⁻¹ ≠
        LevelThreeBoundaryZeroHecke.qZero (n + 1) 0 LevelThreeBoundaryEisenstein.two := by
  have hpow : ‖(((2 : ℕ) : ℂ) ^ (n + 1))⁻¹‖ = ((2 : ℝ) ^ (n + 1))⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
    norm_num
  have hnorm : ‖(μ - 1) / (((2 : ℕ) : ℂ) ^ (n + 1))⁻¹‖ ≤ 3 / 4 * (2 : ℝ) ^ (n + 1 + 1) := by
    rw [norm_div, hpow, div_inv_eq_mul]
    have h4 : (2 : ℝ) ^ (n + 1) ≤ 2 ^ (n + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc ‖μ - 1‖ * (2 : ℝ) ^ (n + 1) ≤ 3 / 4 * (2 : ℝ) ^ (n + 1) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ ≤ 3 / 4 * (2 : ℝ) ^ (n + 1 + 1) := mul_le_mul_of_nonneg_left h4 (by norm_num)
  exact LevelThreeBoundaryQuotient.ne_qInf_two_of_norm_le (by omega) _ hnorm

/-! ### The local joint eigenspace lies in the radical kernel -/

/-- The local Hecke operator `T_p` of the bad line, indexed by the primes `p ≠ 3`. -/
abbrev tpOp (n : ℕ) (p : Away) : Module.End ℂ (CuspH2 n trivialCharacter .line false) :=
  localOp n trivialCharacter (TpExistence.tp p.1) (TpExistence.tp_awayThree p.1 p.2) .line false

theorem localJoint_le_iInf (n : ℕ) (c : HeckeCorrespondence → ℂ) :
    localJoint n trivialCharacter c .line false ≤
      ⨅ p : Away, (tpOp n p).maxGenEigenspace (c (TpExistence.tp p.1)) :=
  le_iInf fun p => iInf_le_of_le ⟨TpExistence.tp p.1, TpExistence.tp_awayThree p.1 p.2⟩ le_rfl

/-- **The local joint generalized eigenspace lies in the classes with zero radical restriction**,
as soon as `c(T_2)` is within `3/4` of `1`. -/
theorem localJoint_le_radicalKernel (n : ℕ) (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    localJoint n trivialCharacter c .line false ≤ badLineLocalRadicalKernel n := by
  have h2 : LocalUniqueness.two.val ≠ 3 := by decide
  have hle : (tpOp n ⟨LocalUniqueness.two, h2⟩).maxGenEigenspace
      (c (TpExistence.tp LocalUniqueness.two)) ≤ badLineLocalRadicalKernel n :=
    LocalAssembly.maxGenEigenspace_le_of_sub_mem
    (tpOp n ⟨LocalUniqueness.two, h2⟩) (badLineLocalRadicalKernel n)
    (BadLineRestriction.lamB n LocalUniqueness.two) (c (TpExistence.tp LocalUniqueness.two))
    (fun y => BadLineRestriction.badLine_localOp_sub_mem_kernel n hn LocalUniqueness.two h2 y)
    (ne_lamB_of_norm_le n LocalUniqueness.two _ hc)
  have hi := iInf_le (fun p : Away => (tpOp n p).maxGenEigenspace (c (TpExistence.tp p.1)))
    ⟨LocalUniqueness.two, h2⟩
  exact le_trans (localJoint_le_iInf n c) (le_trans hi hle)

/-- **The joint edge map**: on the local joint generalized eigenspace, the edge map. -/
def jointEdgeMap (n : ℕ) (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    localJoint n trivialCharacter c .line false →ₗ[ℂ]
      CrossedH1 (binaryArithmeticRepresentation n) :=
  (badLineEdge n hn).comp
    (Submodule.inclusion (localJoint_le_radicalKernel n hn c hc))

theorem jointEdgeMap_injective (n : ℕ) (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    Function.Injective (jointEdgeMap n hn c hc) :=
  (badLineEdge_injective n hn).comp (Submodule.inclusion_injective _)

/-- The edge image of a local joint generalized eigenvector is a generalized eigenvector of the
level-three Hecke operator `T_2`. -/
theorem jointEdgeMap_mem_maxGenEigenspace (n : ℕ) (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (y : localJoint n trivialCharacter c .line false) :
    jointEdgeMap n hn c hc y ∈
      (badLevelHecke LocalUniqueness.two (by decide) n).maxGenEigenspace
        ((c (TpExistence.tp LocalUniqueness.two) - 1) /
          (((LocalUniqueness.two.val : ℕ) : ℂ) ^ (n + 1))⁻¹) := by
  have h2 : LocalUniqueness.two.val ≠ 3 := by decide
  have hy : y.1 ∈ (tpOp n ⟨LocalUniqueness.two, h2⟩).maxGenEigenspace
      (c (TpExistence.tp LocalUniqueness.two)) :=
    (Submodule.mem_iInf _).mp (localJoint_le_iInf n c y.2) ⟨LocalUniqueness.two, h2⟩
  have hβ : (((LocalUniqueness.two.val : ℕ) : ℂ) ^ (n + 1))⁻¹ ≠ 0 := by
    have : ((LocalUniqueness.two.val : ℕ) : ℂ) ≠ 0 := by
      simp [LocalUniqueness.two]
    exact inv_ne_zero (pow_ne_zero _ this)
  exact LocalAssembly.edge_mem_maxGenEigenspace (tpOp n ⟨LocalUniqueness.two, h2⟩)
    (badLineLocalRadicalKernel n) (badLevelHecke LocalUniqueness.two h2 n) (badLineEdge n hn) 1
    (((LocalUniqueness.two.val : ℕ) : ℂ) ^ (n + 1))⁻¹
    (fun y hy => BadLineFinal.badLine_localOp_mem_kernel n LocalUniqueness.two h2 y hy)
    (fun y => by
      have h := badLineEdge_localOp n hn LocalUniqueness.two h2 y
      rw [one_smul]
      exact h)
    hβ _ ⟨y.1, localJoint_le_radicalKernel n hn c hc y.2⟩ hy

/-- **The edge image of the local joint generalized eigenspace is parabolic.** -/
theorem jointEdgeMap_mem_parabolic (n : ℕ) (hn : 3 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (y : localJoint n trivialCharacter c .line false) :
    jointEdgeMap n (by omega) c hc y ∈
      TwoGenerator.parabolicH1 (ParabolicBounds.levelRep (n + 1) 0) (upper 1) (lower 1) := by
  have hne := ne_qInf_qZero_two (n := n) (by omega) (c (TpExistence.tp LocalUniqueness.two)) hc
  exact LevelThreeBoundaryQuotient.mem_parabolicH1_of_mem_maxGenEigenspace_of_ne (n + 1) 0
    LocalUniqueness.two (by decide) _ hne.1 hne.2
    (jointEdgeMap_mem_maxGenEigenspace n (by omega) c hc y)

/-! ### The local upper bound -/

/-- **The sharp local upper bound at the bad line, from the period data.** Let `V` be a
finite-dimensional space with operators `U p` and an injective linear map `Φ` to
`H¹(Γ₁'(3), Sym^{n+1})` with `T_p Φ = Φ U_p`, whose image is the parabolic subspace, and such that
every joint generalized eigenspace of the `U p` has dimension at most two. Then for `c(T_2)` within
`3/4` of `1` the local joint generalized eigenspace of `c` at the bad line has dimension at most two. -/
theorem localUpperBound_badLine_two_of_period (hn : 3 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Away → Module.End ℂ V) (Φ : V →ₗ[ℂ] CrossedH1 (binaryArithmeticRepresentation n))
    (hΦ : Function.Injective Φ)
    (hint : ∀ (p : Away) (v : V), badLevelHecke p.1 p.2 n (Φ v) = Φ (U p v))
    (hrange : LinearMap.range Φ =
      TwoGenerator.parabolicH1 (ParabolicBounds.levelRep (n + 1) 0) (upper 1) (lower 1))
    (hbound : ∀ eig : Nat.Primes → ℂ,
      finrank ℂ (⨅ p : Away, (U p).maxGenEigenspace (eig p.1) : Submodule ℂ V) ≤ 2) :
    Separation.LocalUpperBound n trivialCharacter c .line false 2 := by
  have hn0 : 0 < n := by omega
  have h2 : LocalUniqueness.two.val ≠ 3 := by decide
  have hH : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation n)) :=
    ParabolicBounds.level_H1_finiteDimensional 0 (Nat.succ_pos n)
  have hβ : ∀ p : Away, ((p.1.val : ℂ) ^ (n + 1))⁻¹ ≠ 0 := fun p =>
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.1.property.ne_zero))
  have hne' := ne_qInf_qZero_two (n := n) (by omega) (c (TpExistence.tp LocalUniqueness.two)) hc
  exact LocalChain.local_bound (fun p : Away => tpOp n p) (badLineLocalRadicalKernel n)
    (fun p : Away => badLevelHecke p.1 p.2 n) U (badLineEdge n hn0) Φ
    (fun _ => (1 : ℂ)) (fun p => ((p.1.val : ℂ) ^ (n + 1))⁻¹) (fun _ => (1 : ℂ))
    (fun p => BadLineRestriction.lamB n p.1)
    (fun p => LevelThreeBoundaryHecke.qInf (n + 1) 0 p.1)
    (fun p => c (TpExistence.tp p.1))
    (fun p y hy => BadLineFinal.badLine_localOp_mem_kernel n p.1 p.2 y hy)
    (fun p y => by
      have h := badLineEdge_localOp n hn0 p.1 p.2 y
      rw [one_smul]
      exact h)
    hβ (badLineEdge_injective n hn0) ⟨LocalUniqueness.two, h2⟩
    (fun y => BadLineRestriction.badLine_localOp_sub_mem_kernel n hn0 LocalUniqueness.two h2 y)
    (ne_lamB_of_norm_le n LocalUniqueness.two _ hc) (fun _ => one_ne_zero) hΦ
    (fun p v => by rw [one_smul]; exact hint p v) ⟨LocalUniqueness.two, h2⟩
    (fun y => by
      rw [hrange]
      exact LevelThreeBoundaryEisenstein.badLevelHecke_sub_mem_parabolic n LocalUniqueness.two
        h2 y)
    hne'.1 2
    (hbound (fun q => (c (TpExistence.tp q) - 1) / ((q.val : ℂ) ^ (n + 1))⁻¹ / 1))
    (localJoint n trivialCharacter c .line false)
    (localJoint_le_iInf n c)

end TernaryPeriodPolynomials.LevelThree.BadLineBound
