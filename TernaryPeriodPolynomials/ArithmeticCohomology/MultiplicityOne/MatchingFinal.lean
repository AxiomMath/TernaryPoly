module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Matching
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.OmegaInv
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryTraceAL
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryInjective
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.ClassicalOldSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Assembly

@[expose] public section


/-!
# The matching inputs

Let `D` have trivial character, a nonzero pair, `D.cusp` not spherical, and a nonzero local joint
eigenspace of the pair character at a level-one cusp. For a holomorphic level-three vector `v` of
weight `n + 3`:

* the level-one cusp gives a nonzero level-one eigenform `f` with eigenvalues
  `levelOneEigenvalue n D.cusp` (`exists_levelOne_eigenform_pair_identityPlane`/`_goodLine`);
* the classical form `g = levelThreeForm v` has the level-three eigenvalues
  `levelThreeEigenvalue`, which agree with those of `f`
  (`levelThreeEigenvalue_eq_levelOneEigenvalue`, using that level-one eigenvalues are real and
  `omega_inv`);
* both traces `Tr g`, `Tr (g ∣ W)` are classical forms of `GL₂(ℤ̂)`-fixed vectors of the
  non-spherical `D.cusp`, hence vanish;
* so `g = 0` (`Classical.eq_zero_of_traceThree_eq_zero`) and `v = 0` (`levelThreeForm_eq_zero`).
-/

noncomputable section

open ComplexConjugate
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.HeckeEigen.Satake
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.LevelThree

namespace TernaryPeriodPolynomials.MultiplicityOne

theorem map_atkinLehnerQ :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ = Classical.atkinLehnerMatrix := by
  apply Units.ext
  rw [Classical.atkinLehnerMatrix_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [atkinLehnerQ, Matrix.GeneralLinearGroup.map_apply]

theorem omega_dP_inv (σ : CuspidalRepresentation) (p : Nat.Primes) :
    omega σ (Bo (dP p.property)⁻¹) = conj (omega σ (Bo (dP p.property))) := by
  rw [Bo_inv]
  exact omega_inv σ (glAway2_mem _)

/-- **The core of the matching**: a nonzero level-one eigenform with the eigenvalues
`levelOneEigenvalue n σ` forces every holomorphic level-three vector of weight `n + 3` of a
non-spherical `σ` to vanish. -/
theorem levelThreeVector_eq_zero (σ : CuspidalRepresentation) {n : ℕ} (hodd : Odd n)
    (central : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (hns : ¬ SphericalCusp σ) {halfWeight : ℤ} (hw : 2 * halfWeight = -((n : ℤ) + 3))
    {f : CuspForm LevelOneHecke.levelOne (-2 * halfWeight)} (hf0 : f ≠ 0)
    (hf : ∀ p : Nat.Primes, p.val ≠ 3 →
      LevelOneHecke.levelOneHecke (-2 * halfWeight) p f = levelOneEigenvalue n σ p • f)
    (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectors σ halfWeight) : v = 0 := by
  have hneg : halfWeight < 0 := by omega
  have hkeven : Even (-2 * halfWeight) := ⟨-halfWeight, by ring⟩
  have hk0 : 0 < -2 * halfWeight := by omega
  have hf' : f ∈ LevelOneMultiplicityOne.eigenspaceAwayThree (-2 * halfWeight)
      (levelOneEigenvalue n σ) := LevelOneMultiplicityOne.mem_eigenspaceAwayThree.mpr hf
  have hg : levelThreeForm σ halfWeight hneg v hv ∈
      LevelThreeMultiplicity.eigenspaceAwayThree (-2 * halfWeight) (levelOneEigenvalue n σ) := by
    rw [LevelThreeMultiplicity.mem_eigenspaceAwayThree]
    intro p hp
    rw [levelThreeHecke_levelThreeForm σ central halfWeight hneg p hp v hv,
      levelThreeEigenvalue_eq_levelOneEigenvalue σ hodd hw p (omega_dP_inv σ p)
        (levelOneHecke_eigenvalue_conj p hf0 (hf p hp))]
  have h1 : Classical.traceThree (-2 * halfWeight) hkeven (levelThreeForm σ halfWeight hneg v hv)
      = 0 := by
    apply DFunLike.coe_injective
    rw [Classical.coe_traceThree, FunLike.coe_zero]
    exact trace_sum_slash_eq_zero_of_not_spherical σ halfWeight v hv.1 hv.2.1 hns
  have hS : ∑ i : Option (Fin 3), SlashAction.map (-2 * halfWeight)
      (LevelThreePeterssonDomain.rep i)
      (SlashAction.map (-2 * halfWeight)
        (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ)
        (cuspScalarWeightedLinear σ halfWeight 1 v)) = 0 := by
    have h0 := traceVector_atkinLehner_scalar σ central halfWeight v hv.2.1
    rw [traceVector_atkinLehner_eq_zero_of_not_spherical σ halfWeight v hv.1 hv.2.1 hns,
      map_zero] at h0
    have h3 : (3 : ℂ) ^ (halfWeight + 1) ≠ 0 := zpow_ne_zero _ (by norm_num)
    exact (smul_eq_zero.mp h0.symm).resolve_left h3
  have h2 : Classical.traceThree (-2 * halfWeight) hkeven
      (Classical.atkinLehnerThree (-2 * halfWeight) (levelThreeForm σ halfWeight hneg v hv)) =
        0 := by
    apply DFunLike.coe_injective
    rw [Classical.coe_traceThree, FunLike.coe_zero, Classical.coe_atkinLehnerThree,
      ← map_atkinLehnerQ]
    exact hS
  exact levelThreeForm_eq_zero σ central halfWeight hneg v hv
    (Classical.eq_zero_of_traceThree_eq_zero hkeven hk0 hf0 hf' hg h1 h2)

/-- **The matching input at the identity plane** (`3 ≤ n`). -/
theorem levelThreeMatching {n : ℕ} (hn : 3 ≤ n) : LevelThreeMatching n := by
  intro D hecke hhecke hχ hne hns hloc halfWeight hw v hv
  rcases Nat.even_or_odd n with heven | hodd
  · exact absurd (sphericalForcedByLocal_of_even D hχ hecke hhecke (by omega) heven hloc) hns
  obtain ⟨f, hf0, hf⟩ := exists_levelOne_eigenform_pair_identityPlane (k := -2 * halfWeight) D hχ
    (by omega) hecke hhecke hodd hn hne hloc
  exact levelThreeVector_eq_zero D.cusp hodd
    (cohomological_centralCharacter_positive D.cusp D.cohomological) hns hw hf0 hf v hv

/-- **The matching input at the good line** (`3 ≤ n`). -/
theorem levelThreeMatchingLine {n : ℕ} (hn : 3 ≤ n) : LevelThreeMatchingLine n := by
  intro D hecke hhecke hχ hne hns hloc halfWeight hw v hv
  rcases Nat.even_or_odd n with heven | hodd
  · exact absurd (sphericalForcedByLocalLine_of_even D hχ hecke hhecke hn heven hne hloc) hns
  obtain ⟨f, hf0, hf⟩ := exists_levelOne_eigenform_pair_goodLine (k := -2 * halfWeight) D hχ
    (by omega) hecke hhecke hodd hn hne hloc
  exact levelThreeVector_eq_zero D.cusp hodd
    (cohomological_centralCharacter_positive D.cusp D.cohomological) hns hw hf0 hf v hv

/-- **The prime-three input at the identity plane, consumer form, given the level-three bridge.** -/
theorem sphericalForcedByLocal_of_bridge (hbridge : LevelThreeBridge) {n : ℕ} (hn : 3 ≤ n)
    (D : InducingData n) (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    Separation.SphericalForcedByLocal D hecke hhecke :=
  sphericalForcedByLocal_of_inputs hbridge (levelThreeMatching hn) D hχ hecke hhecke
    (by omega) hne

/-- **The prime-three input at the good line, consumer form, given the level-three bridge.** -/
theorem sphericalForcedByLocalLine_of_bridge (hbridge : LevelThreeBridge) {n : ℕ} (hn : 3 ≤ n)
    (D : InducingData n) (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    Separation.SphericalForcedByLocalLine D hecke hhecke :=
  sphericalForcedByLocalLine_of_inputs hbridge (levelThreeMatchingLine hn) D hχ hecke hhecke hn hne

end TernaryPeriodPolynomials.MultiplicityOne
