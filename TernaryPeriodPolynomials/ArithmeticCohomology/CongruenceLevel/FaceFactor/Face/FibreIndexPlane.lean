module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.FibreIndex
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.FibrePlane

@[expose] public section


/-!
# The index of the plane group at level `M` in that at level `N`

Formalized by Claude Sonnet 5.5.

The plane analogue of `FaceFibreIndex`: `planeFace_relIndex_eq`, `[P_N : P_M] = (M/N)² · [Γ₂(N) : Γ₂(M)]` for the plane group `Γ(K) ∩ h⁻¹ P h` (radical `Kℤ²` in the last column, Levi `Γ₂(K)` the upper left block).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceFibre

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.FrameInvariance

theorem planeStd_relIndex_eq {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) :
    (gammaNP M).relIndex (gammaNP N) =
      (M / N) ^ 2 * (CongruenceSubgroup.Gamma M).relIndex (CongruenceSubgroup.Gamma N) := by
  obtain ⟨m, rfl⟩ := hNM
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hm : N * m / N = m := Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [hm]
  have key := index_split (gammaNExt N) (gammaNSplitting N) ((gammaNP (N * m)).subgroupOf (gammaNP N))
    ((CongruenceSubgroup.Gamma (N * m)).subgroupOf (CongruenceSubgroup.Gamma N)) (radMulSub m) ?_ ?_ ?_
  · rw [index_radMulSub] at key
    exact key.trans (mul_comm _ _)
  · intro l hl
    exact Subgroup.mem_subgroupOf.2 ⟨blockDiag_mem_gammaN (Subgroup.mem_subgroupOf.mp hl),
      blockDiag_mem_planeStab _⟩
  · intro e he
    exact Subgroup.mem_subgroupOf.2 (leviBlock_mem_Gamma (Subgroup.mem_subgroupOf.mp he).1 e.2.2)
  · intro r
    rw [mem_radMulSub, Subgroup.mem_subgroupOf]
    have hs := radElt_mem_planeStab N r
    show radElt N r ∈ gammaNP (N * m) ↔ (m : ℤ) ∣ r.toAdd.1 ∧ (m : ℤ) ∣ r.toAdd.2
    constructor
    · intro h
      have h02 := mem_gammaN.1 h.1 0 2
      have h12 := mem_gammaN.1 h.1 1 2
      simp [radElt] at h02 h12
      exact ⟨(mul_dvd_mul_iff_left hN).1 h02, (mul_dvd_mul_iff_left hN).1 h12⟩
    · rintro ⟨h1, h2⟩
      refine ⟨mem_gammaN.2 ?_, hs⟩
      intro i j
      fin_cases i <;> fin_cases j <;> simp [radElt]
      · exact (mul_dvd_mul_iff_left hN).2 h1
      · exact (mul_dvd_mul_iff_left hN).2 h2

theorem planeFace_relIndex_eq {N M : ℕ} [NeZero N] [NeZero M] (hN : 3 ≤ N) (hNM : N ∣ M) (h : SL(3, ℤ)) :
    (gammaNPAt M h).relIndex (gammaNPAt N h) =
      (M / N) ^ 2 * (CongruenceSubgroup.Gamma M).relIndex (CongruenceSubgroup.Gamma N) := by
  have hM : 3 ≤ M := hN.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hNM)
  rw [gammaNPAt_relIndex_eq hN hM, ← gammaNP_eq_inf N hN, ← gammaNP_eq_inf M hM]
  exact planeStd_relIndex_eq hNM

end TernaryPeriodPolynomials.Argument.FaceFibre
