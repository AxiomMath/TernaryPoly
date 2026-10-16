module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneCharacter
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Dimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.ParityHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.JointGen
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Petersson.Semisimple

@[expose] public section


/-!
# Multiplicity at most two for the level-three joint eigenspace of the good plane

Let `c` be a system of Hecke eigenvalues with `‖c(T_2) - 1‖ ≤ 3/4`. The joint generalized
eigenspace `levelJoint n c ⊆ H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` of `T_p` (`p ≠ 3`) with eigenvalues
`p^{n+2}(c(T_p) - 1)` consists of parabolic classes (`GoodPlaneBound.levelJoint_le_parabolic`).
If the parity-projected period map `levelPeriodMap (n+1) (-1) : S_{n+3}(Γ₁(3)) → H¹(Γ₁'(3), ...)`
is injective (the Eichler–Shimura input), it is onto the parabolic cohomology and intertwines
`levelHecke p` with `p • T_p`, so `levelJoint` pulls back to the joint generalized eigenspace of the
`T_p` on cusp forms, which has dimension at most two (Petersson semisimplicity and Atkin–Lehner at
three). Hence `dim levelJoint ≤ 2` and, with `GoodPlaneJoint`, the good-plane local upper bound `2`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneBoundTwo

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.LevelThree.GoodPlaneJoint (levelJoint)
open TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryEisenstein (two)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (levelHecke)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke (levelThreeHecke)

/-- **`dim levelJoint ≤ 2`**, given injectivity of the parity-projected period map. -/
theorem finrank_levelJoint_le_two (n : ℕ) (hn : 1 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    Module.finrank ℂ (levelJoint n c) ≤ 2 := by
  have hm : 0 < n + 1 := Nat.succ_pos n
  have hrange := LevelThreePeriodDimension.levelPeriodMap_range_eq_parabolic_of_injective
    (m := n + 1) (e := -1) hm hinj
  have hJR : levelJoint n c ≤ LinearMap.range (levelPeriodMap (n + 1) (-1)) := by
    rw [hrange]
    exact GoodPlaneBound.levelJoint_le_parabolic n hn c hc
  have : Module.Finite ℂ (S (n + 1)) :=
    SturmBound.cuspForm_finiteDimensional (((n + 1 : ℕ) : ℤ) + 2)
  have hpos : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) + 2 := by omega
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
  have h3 := LevelThreeJointGen.finrank_jointGenEigenspace_le_two hpos
    (LevelThreePeterssonSemisimple.levelThree_semisimple (((n + 1 : ℕ) : ℤ) + 2))
    (fun q => (c (TpExistence.tp q) - 1) / ((q.val : ℂ) ^ (n + 2))⁻¹ /
      ((q.val : ℂ) ^ (-(-1 : ℤ))))
  exact (Submodule.finrank_mono h2).trans h3

/-- **The local upper bound `2` at the good plane** (trivial character), given injectivity of the
parity-projected period map. -/
theorem localUpperBound_two (n : ℕ) (hn : 1 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    Separation.LocalUpperBound n trivialCharacter c .plane true 2 :=
  GoodPlaneJoint.localUpperBound_of_levelJoint n (by omega) c 2
    (finrank_levelJoint_le_two n hn c hc hinj)

end TernaryPeriodPolynomials.LevelThree.GoodPlaneBoundTwo
