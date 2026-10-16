module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneLocalOp
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Interface

@[expose] public section


/-!
# The local joint generalized eigenspace at the good plane embeds into the level-three one

By `GoodPlaneLocalOp.goodPlaneEdge_localOp_tp`, the injective edge map `goodPlaneEdge` intertwines
the local Hecke operator of `T_p = Γ diag(p,1,1) Γ` (`p ≠ 3`) with `1 + p^{-(n+2)} T_p^{Γ₁'(3)}` on
`H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`. Since affine changes of an operator preserve generalized
eigenspaces (`mem_maxGen_of_affine`), the image of the local joint generalized eigenspace
`CuspReduction.localJoint n trivialCharacter c .plane true` lies in the joint generalized
eigenspace `levelJoint n c` of the level-three Hecke operators with eigenvalues
`p^{n+2} (c(T_p) - 1)` (`map_localJoint_le`), and therefore
`dim localJoint ≤ dim levelJoint` (`finrank_localJoint_le`), the local upper bound of the good
plane cusp in terms of the classical level-three joint eigenspace
 (`localUpperBound_of_levelJoint`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneJoint

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
  (CuspH2 localOp localJoint intertwine_mem_maxGenEigenspace)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
  (goodPlaneEdge goodPlaneEdge_injective goodPlane_finiteDimensional)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

/-- An affine change of an operator preserves generalized eigenspaces. -/
theorem mem_maxGen_of_affine {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (a μ : ℂ) (ha : a ≠ 0) {v : V} (hv : v ∈ (1 + a • T : Module.End ℂ V).maxGenEigenspace μ) :
    v ∈ T.maxGenEigenspace ((μ - 1) / a) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, ?_⟩
  have hmul : a * ((μ - 1) / a) = μ - 1 := by field_simp
  have h : (1 + a • T : Module.End ℂ V) - μ • 1 = a • (T - ((μ - 1) / a) • 1) := by
    apply LinearMap.ext
    intro w
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, smul_sub, smul_smul, hmul]
    module
  rw [h, smul_pow, LinearMap.smul_apply] at hk
  exact (smul_eq_zero.mp hk).resolve_left (pow_ne_zero k ha)

/-- The joint generalized eigenspace, in `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`, of the level-three Hecke
operators `T_p` (`p ≠ 3`) with eigenvalues `p^{n+2} (c(T_p) - 1)`. -/
def levelJoint (n : ℕ) (c : HeckeCorrespondence → ℂ) :
    Submodule ℂ (CrossedH1 (levelRep (n + 1) (-1))) :=
  ⨅ p : {p : Nat.Primes // p.val ≠ 3},
    (LevelThreeHeckeH1.levelHecke (n + 1) (-1) p.1 p.2).maxGenEigenspace
      ((c (TpExistence.tp p.1) - 1) / ((p.1.val : ℂ) ^ (n + 2))⁻¹)

/-- **The edge of the local joint generalized eigenspace lies in the level-three one.** -/
theorem map_localJoint_le (n : ℕ) (hn : 0 < n) (c : HeckeCorrespondence → ℂ) :
    (localJoint n trivialCharacter c .plane true).map (goodPlaneEdge hn) ≤ levelJoint n c := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [levelJoint, Submodule.mem_iInf, Subtype.forall]
  intro p hp3
  have hy0 : y ∈ localJoint n trivialCharacter c .plane true := hy
  rw [localJoint, Submodule.mem_iInf] at hy0
  have hy' := hy0 ⟨TpExistence.tp p, TpExistence.tp_awayThree p hp3⟩
  have hp : ((p.val : ℂ) ^ (n + 2))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.property.ne_zero))
  refine mem_maxGen_of_affine _ _ _ hp ?_
  refine intertwine_mem_maxGenEigenspace (goodPlaneEdge hn)
    (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .plane true)
    (1 + ((p.val : ℂ) ^ (n + 2))⁻¹ • LevelThreeHeckeH1.levelHecke (n + 1) (-1) p hp3) ?_ _ hy'
  intro x
  rw [GoodPlaneLocalOp.goodPlaneEdge_localOp_tp p hp3 n hn x]
  rfl

/-- **The local joint generalized eigenspace at the good plane is bounded by the level-three
one.** -/
theorem finrank_localJoint_le (n : ℕ) (hn : 0 < n) (c : HeckeCorrespondence → ℂ) :
    FiniteDimensional ℂ (localJoint n trivialCharacter c .plane true) ∧
      Module.finrank ℂ (localJoint n trivialCharacter c .plane true) ≤
        Module.finrank ℂ (levelJoint n c) := by
  have : FiniteDimensional ℂ (CuspH2 n trivialCharacter .plane true) :=
    goodPlane_finiteDimensional hn
  have : FiniteDimensional ℂ (CrossedH1 (levelRep (n + 1) (-1))) :=
    ParabolicBounds.level_H1_finiteDimensional (-1) (Nat.succ_pos n)
  refine ⟨inferInstance, ?_⟩
  have heq := LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (goodPlaneEdge hn) (goodPlaneEdge_injective hn)
      (localJoint n trivialCharacter c .plane true))
  rw [heq]
  exact Submodule.finrank_mono (map_localJoint_le n hn c)

/-- **Local upper bound at the good-plane cusp (trivial character)**, in the form of the
separation interface: a bound `m` on the classical level-three joint generalized eigenspace gives
the local upper bound at the good plane. -/
theorem localUpperBound_of_levelJoint (n : ℕ) (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (m : ℕ) (hm : Module.finrank ℂ (levelJoint n c) ≤ m) :
    Separation.LocalUpperBound n trivialCharacter c .plane true m := by
  obtain ⟨hfin, hle⟩ := finrank_localJoint_le n hn c
  exact ⟨hfin, hle.trans hm⟩

end TernaryPeriodPolynomials.LevelThree.GoodPlaneJoint
