module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Dimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.ParityHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.JointGen

@[expose] public section


/-!
# The bad-line local joint eigenspace inside a classical joint eigenspace

At the bad line of level three (trivial character), for `‖c(T_2) - 1‖ ≤ 3/4`, the local joint
generalized eigenspace of `c` embeds through the edge map of `BadLineBound` into the joint
generalized eigenspace of the Hecke operators on `H¹(Γ₁'(3), Sym^{n+1})`, its image is parabolic,
and given injectivity of the parity-projected period map `levelPeriodMap (n + 1) 0` it pulls back
to the joint generalized eigenspace of the classical Hecke operators on `S_{n+3}(Γ₁(3))` with
eigenvalues `p^{n+1} (c(T_p) - 1)` (`finrank_localJoint_badLine_le`). This is the chain of
`BadLineBound.localUpperBound_badLine_two_of_period` (instantiated as in `BadLineUpper`) with the
classical dimension kept instead of the bound `2`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.RankTwo

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (CrossedH1 binaryArithmeticRepresentation)
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke (levelThreeHecke)

/-- **The bad-line local joint eigenspace inside the classical joint generalized eigenspace** with
eigenvalues `p^{n+1} (c(T_p) - 1)` (written as in `BadLineBound`), given injectivity of the
parity-projected period map. -/
theorem finrank_localJoint_badLine_le {n : ℕ} (hn : 3 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (hinj : Function.Injective (levelPeriodMap (n + 1) 0)) :
    Module.finrank ℂ (localJoint n trivialCharacter c .line false) ≤
      Module.finrank ℂ (LevelThreeJointGen.jointGenEigenspace (((n + 1 : ℕ) : ℤ) + 2)
        (fun q => (c (TpExistence.tp q) - 1) / ((q.val : ℂ) ^ (n + 1))⁻¹ / 1)) := by
  have hn0 : 0 < n := by omega
  have hm : 0 < n + 1 := Nat.succ_pos n
  have h2 : LocalUniqueness.two.val ≠ 3 := by decide
  have : FiniteDimensional ℂ (S (n + 1)) :=
    SturmBound.cuspForm_finiteDimensional (((n + 1 : ℕ) : ℤ) + 2)
  have : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation n)) :=
    ParabolicBounds.level_H1_finiteDimensional 0 (Nat.succ_pos n)
  have hrange := LevelThreePeriodDimension.levelPeriodMap_range_eq_parabolic_of_injective
    (m := n + 1) (e := 0) hm hinj
  have hβ : ∀ p : BadLineBound.Away, ((p.1.val : ℂ) ^ (n + 1))⁻¹ ≠ 0 := fun p =>
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.1.property.ne_zero))
  have hne' := BadLineBound.ne_qInf_qZero_two (n := n) (by omega)
    (c (TpExistence.tp LocalUniqueness.two)) hc
  exact (LocalChain.local_bound (fun p : BadLineBound.Away => BadLineBound.tpOp n p)
    (badLineLocalRadicalKernel n)
    (fun p : BadLineBound.Away => badLevelHecke p.1 p.2 n)
    (fun p : BadLineBound.Away => levelThreeHecke (((n + 1 : ℕ) : ℤ) + 2) p.1 p.2)
    (BadLineFinal.badLineEdge n hn0) (levelPeriodMap (n + 1) 0)
    (fun _ => (1 : ℂ)) (fun p => ((p.1.val : ℂ) ^ (n + 1))⁻¹) (fun _ => (1 : ℂ))
    (fun p => BadLineRestriction.lamB n p.1)
    (fun p => LevelThreeBoundaryHecke.qInf (n + 1) 0 p.1)
    (fun p => c (TpExistence.tp p.1))
    (fun p y hy => BadLineFinal.badLine_localOp_mem_kernel n p.1 p.2 y hy)
    (fun p y => by
      have h := BadLineBound.badLineEdge_localOp n hn0 p.1 p.2 y
      rw [one_smul]
      exact h)
    hβ (BadLineFinal.badLineEdge_injective n hn0) ⟨LocalUniqueness.two, h2⟩
    (fun y => BadLineRestriction.badLine_localOp_sub_mem_kernel n hn0 LocalUniqueness.two h2 y)
    (BadLineBound.ne_lamB_of_norm_le n LocalUniqueness.two _ hc) (fun _ => one_ne_zero) hinj
    (fun p v => by
      have h := LevelThreePeriodParityHecke.levelHecke_levelPeriodMap (m := n + 1) 0 p.1 p.2 hm v
      rw [neg_zero, zpow_zero, one_smul] at h
      rw [one_smul]
      exact h)
    ⟨LocalUniqueness.two, h2⟩
    (fun y => (SetLike.ext_iff.mp hrange _).mpr
      (LevelThreeBoundaryEisenstein.badLevelHecke_sub_mem_parabolic n LocalUniqueness.two
        h2 y))
    hne'.1 _ le_rfl
    (localJoint n trivialCharacter c .line false)
    (BadLineBound.localJoint_le_iInf n c)).2

/-- The bad-line eigenvalue normalization: `a / (p^{n+1})⁻¹ / 1 = p^{n+1} a`. -/
theorem badLine_eigenvalue (n : ℕ) (a p : ℂ) :
    a / (p ^ (n + 1))⁻¹ / 1 = p ^ (n + 1) * a := by
  rw [div_one, div_inv_eq_mul, mul_comm]

end TernaryPeriodPolynomials.RankTwo
