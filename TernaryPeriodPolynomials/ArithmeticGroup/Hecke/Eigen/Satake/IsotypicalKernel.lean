module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.SingleCharacter

@[expose] public section


/-!
# Isotypical projections vanish off the associate eigencharacter

Every away-from-three Hecke operator acts on the associate pair `A_D` by one scalar `λ_D(t)`
(`plane_line_scalar`). An isotypical projection `p` onto `A_D` commutes with the Hecke operators,
so it kills every generalized eigenvector of `pairHecke t` whose eigenvalue differs from `λ_D(t)`.
What separation (`EigenSeparated`) adds is the behaviour of `p` on the `λ_D`-generalized
eigenspace itself.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n : ℕ}

/-- The common scalar of an away-from-three correspondence on the associate pair. -/
theorem pair_scalar (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (t : HeckeCorrespondence) (ht : AwayThree t) :
    ∃ c : ℂ, ∀ y ∈ associatePair D, pairHecke D hecke t y = c • y := by
  obtain ⟨μ, hP, hL⟩ := plane_line_scalar D t ht
  exact common_scalar_of_eq D hecke t μ μ
    (summand_scalar_of_source D .plane t hecke hhecke μ (source_scalar_of_function t μ hP))
    (summand_scalar_of_source D .line t hecke hhecke μ (source_scalar_of_function t μ hL))
    (fun _ _ => rfl)

/-- A projection with range `A`, commuting with `T`, kills generalized eigenvectors of `T` for
eigenvalues different from the scalar of `T` on `A`. -/
theorem proj_kills_of_ne {W : Type*} [AddCommGroup W] [Module ℂ W] (A : Submodule ℂ W)
    (p T : Module.End ℂ W) (hrange : LinearMap.range p = A) (hcomm : p * T = T * p)
    (c μ : ℂ) (hlam : ∀ y ∈ A, T y = c • y) (hne : μ ≠ c) (w : W) (k : ℕ)
    (hw : ((T - μ • 1) ^ k) w = 0) : p w = 0 := by
  have hpA : p w ∈ A := hrange ▸ LinearMap.mem_range_self p w
  have hcommk : p * (T - μ • 1) ^ k = (T - μ • 1) ^ k * p := by
    have h1 : Commute p (T - μ • 1) := by
      refine Commute.sub_right hcomm ?_
      exact Commute.smul_right (Commute.one_right p) μ
    exact (h1.pow_right k).eq
  have h0 : ((T - μ • 1) ^ k) (p w) = 0 := by
    rw [← Module.End.mul_apply, ← hcommk, Module.End.mul_apply, hw, map_zero]
  have hval : ∀ j : ℕ, ((T - μ • 1) ^ j) (p w) = (c - μ) ^ j • p w := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hlam _ hpA,
        LinearMap.smul_apply, Module.End.one_apply, ← sub_smul, smul_smul, pow_succ', mul_comm]
  rw [hval k] at h0
  exact (smul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hne.symm))

/-- **Isotypical projections vanish off the associate eigencharacter.** -/
theorem isotypical_kills_other (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (p : Module.End ℂ (BoundaryCoordinates n D.chi))
    (hp : IsIsotypicalProjection D hecke p) (t : HeckeCorrespondence) (ht : AwayThree t)
    (w : BoundaryCoordinates n D.chi) (μ : ℂ) (k : ℕ)
    (hw : ((pairHecke D hecke t - μ • 1) ^ k) w = 0)
    (hne : ∀ c : ℂ, (∀ y ∈ associatePair D, pairHecke D hecke t y = c • y) → μ ≠ c) :
    p w = 0 := by
  obtain ⟨c, hc⟩ := pair_scalar D hecke hhecke t ht
  have hcomm : p * pairHecke D hecke t = pairHecke D hecke t * p := hp.2.2 t
  exact proj_kills_of_ne (associatePair D) p (pairHecke D hecke t) hp.1 hcomm c μ hc (hne c hc)
    w k hw

end TernaryPeriodPolynomials.HeckeEigen.Satake
