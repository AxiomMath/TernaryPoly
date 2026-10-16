module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Dimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.ParityHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.JointGen

@[expose] public section


/-!
# The good-plane local joint eigenspace inside a classical joint eigenspace

At the good plane of level three (trivial character) the edge map embeds the local joint
generalized eigenspace of `c` into the joint generalized eigenspace `levelJoint n c` of the Hecke
operators on `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` (`GoodPlaneJoint.finrank_localJoint_le`). When
`‖c(T_2) - 1‖ ≤ 3/4` these classes are parabolic, and given injectivity of the parity-projected
period map `levelPeriodMap (n + 1) (-1)` they pull back to the joint generalized eigenspace of the
classical Hecke operators on `S_{n+3}(Γ₁(3))` with eigenvalues `p^{n+1} (c(T_p) - 1)`
(`finrank_localJoint_goodPlane_le`). This is the dimension comparison of
`GoodPlaneBoundTwo.finrank_levelJoint_le_two` without the final bound `≤ 2`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.RankTwo

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.GoodPlaneJoint (levelJoint)
open TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryEisenstein (two)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (levelHecke)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke (levelThreeHecke)

/-- **`levelJoint` inside the classical joint generalized eigenspace**, given injectivity of the
parity-projected period map. -/
theorem finrank_levelJoint_le_jointGen (n : ℕ) (hn : 1 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    Module.finrank ℂ (levelJoint n c) ≤
      Module.finrank ℂ (LevelThreeJointGen.jointGenEigenspace (((n + 1 : ℕ) : ℤ) + 2)
        (fun q => (c (TpExistence.tp q) - 1) / ((q.val : ℂ) ^ (n + 2))⁻¹ /
          ((q.val : ℂ) ^ (-(-1 : ℤ))))) := by
  have hm : 0 < n + 1 := Nat.succ_pos n
  have hrange := LevelThreePeriodDimension.levelPeriodMap_range_eq_parabolic_of_injective
    (m := n + 1) (e := -1) hm hinj
  have hJR : levelJoint n c ≤ LinearMap.range (levelPeriodMap (n + 1) (-1)) := by
    rw [hrange]
    exact GoodPlaneBound.levelJoint_le_parabolic n hn c hc
  have : Module.Finite ℂ (S (n + 1)) :=
    SturmBound.cuspForm_finiteDimensional (((n + 1 : ℕ) : ℤ) + 2)
  let μ : {p : Nat.Primes // p.val ≠ 3} → ℂ := fun p =>
    (c (TpExistence.tp p.1) - 1) / ((p.1.val : ℂ) ^ (n + 2))⁻¹
  have h1 := GoodPlaneBound.finrank_le_of_injective_equivariant (levelPeriodMap (n + 1) (-1)) hinj
    (fun p : {p : Nat.Primes // p.val ≠ 3} =>
      (((p.1.val : ℂ) ^ (-(-1 : ℤ))) • levelThreeHecke (((n + 1 : ℕ) : ℤ) + 2) p.1 p.2 :
        Module.End ℂ (S (n + 1))))
    (fun p => levelHecke (n + 1) (-1) p.1 p.2)
    (fun p f => (LevelThreePeriodParityHecke.levelHecke_levelPeriodMap (-1) p.1 p.2 hm f).symm)
    μ (levelJoint n c) le_rfl hJR
  refine h1.trans ?_
  have h2 : (⨅ p : {p : Nat.Primes // p.val ≠ 3},
      Module.End.maxGenEigenspace
        (((p.1.val : ℂ) ^ (-(-1 : ℤ))) • levelThreeHecke (((n + 1 : ℕ) : ℤ) + 2) p.1 p.2 :
          Module.End ℂ (S (n + 1))) (μ p) : Submodule ℂ (S (n + 1))) ≤
      LevelThreeJointGen.jointGenEigenspace (((n + 1 : ℕ) : ℤ) + 2)
        (fun q => (c (TpExistence.tp q) - 1) / ((q.val : ℂ) ^ (n + 2))⁻¹ /
          ((q.val : ℂ) ^ (-(-1 : ℤ)))) := by
    refine iInf_mono (fun p => ?_)
    have hp : ((p.1.val : ℂ) ^ (-(-1 : ℤ))) ≠ 0 := by
      rw [neg_neg, zpow_one]
      exact_mod_cast p.1.property.ne_zero
    exact fun f hf => GoodPlaneBound.mem_maxGen_of_smul _ _ _ hp hf
  exact Submodule.finrank_mono h2

/-- **The good-plane local joint eigenspace inside the classical joint generalized eigenspace**
with eigenvalues `p^{n+1} (c(T_p) - 1)` (written as in `GoodPlaneBoundTwo`), given injectivity of
the parity-projected period map. -/
theorem finrank_localJoint_goodPlane_le (n : ℕ) (hn : 1 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    Module.finrank ℂ (CuspReduction.localJoint n trivialCharacter c .plane true) ≤
      Module.finrank ℂ (LevelThreeJointGen.jointGenEigenspace (((n + 1 : ℕ) : ℤ) + 2)
        (fun q => (c (TpExistence.tp q) - 1) / ((q.val : ℂ) ^ (n + 2))⁻¹ /
          ((q.val : ℂ) ^ (-(-1 : ℤ))))) :=
  (GoodPlaneJoint.finrank_localJoint_le n (by omega) c).2.trans
    (finrank_levelJoint_le_jointGen n hn c hc hinj)

/-- The good-plane eigenvalue normalization: `a / (p^{n+2})⁻¹ / p^{-(-1)} = p^{n+1} a`. -/
theorem goodPlane_eigenvalue (n : ℕ) (a p : ℂ) (hp : p ≠ 0) :
    a / (p ^ (n + 2))⁻¹ / p ^ (-(-1 : ℤ)) = p ^ (n + 1) * a := by
  rw [neg_neg, zpow_one, div_inv_eq_mul, div_eq_iff hp]
  ring

end TernaryPeriodPolynomials.RankTwo
