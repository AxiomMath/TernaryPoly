module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.FibreIndexGeneric
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.FibreLine

@[expose] public section


/-!
# The index of the line group at level `M` in that at level `N`

Formalized by Claude Sonnet 5.5.

`lineFace_relIndex_eq`: for `3 ≤ N ∣ M` and every frame `h`, `[P_N : P_M] = (M/N)² · [Γ₂(N) : Γ₂(M)]`, where `P_K = Γ(K) ∩ h⁻¹ Q h` is the line group of the cusp `h⁻¹ Q h`, an extension of the Levi `Γ₂(K)` by the radical lattice `Kℤ²`:
the radical contributes the index `(M/N)²` of `(M/N)ℤ²` in `ℤ²`, the Levi the index of `Γ(M)` in `Γ(N)` in `SL₂(ℤ)`.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceFibre

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FrameInvariance

/-- The sublattice `mℤ²` of the radical lattice. -/
def radMulSub (m : ℕ) : Subgroup RadicalLattice :=
  ((AddSubgroup.zmultiples (m : ℤ)).prod (AddSubgroup.zmultiples (m : ℤ))).toSubgroup

theorem mem_radMulSub {m : ℕ} {r : RadicalLattice} :
    r ∈ radMulSub m ↔ (m : ℤ) ∣ r.toAdd.1 ∧ (m : ℤ) ∣ r.toAdd.2 := by
  simp [radMulSub, AddSubgroup.mem_prod, Int.mem_zmultiples_iff]

theorem index_radMulSub (m : ℕ) : (radMulSub m).index = m ^ 2 := by
  rw [radMulSub, AddSubgroup.index_toSubgroup, AddSubgroup.index_prod, Int.index_zmultiples]
  simp [sq]

theorem lineStd_relIndex_eq {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) :
    (gammaNQ M).relIndex (gammaNQ N) =
      (M / N) ^ 2 * (CongruenceSubgroup.Gamma M).relIndex (CongruenceSubgroup.Gamma N) := by
  obtain ⟨m, rfl⟩ := hNM
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hm : N * m / N = m := Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [hm]
  have key := index_split (lineExt N) (lineSplitting N) ((gammaNQ (N * m)).subgroupOf (gammaNQ N))
    ((CongruenceSubgroup.Gamma (N * m)).subgroupOf (CongruenceSubgroup.Gamma N)) (radMulSub m) ?_ ?_ ?_
  · rw [index_radMulSub] at key
    exact key.trans (mul_comm _ _)
  · intro l hl
    exact Subgroup.mem_subgroupOf.2 ⟨blockDiagQ_mem_gammaN (Subgroup.mem_subgroupOf.mp hl),
      blockDiagQ_mem_lineStab _⟩
  · intro e he
    exact Subgroup.mem_subgroupOf.2 (leviBlockQ_mem_Gamma (Subgroup.mem_subgroupOf.mp he).1 e.2.2)
  · intro r
    rw [mem_radMulSub, Subgroup.mem_subgroupOf]
    have hs := radEltQ_mem_lineStab N r
    show radEltQ N r ∈ gammaNQ (N * m) ↔ (m : ℤ) ∣ r.toAdd.1 ∧ (m : ℤ) ∣ r.toAdd.2
    constructor
    · intro h
      have h01 := mem_gammaN.1 h.1 0 1
      have h02 := mem_gammaN.1 h.1 0 2
      simp [radEltQ] at h01 h02
      exact ⟨(mul_dvd_mul_iff_left hN).1 h01, (mul_dvd_mul_iff_left hN).1 h02⟩
    · rintro ⟨h1, h2⟩
      refine ⟨mem_gammaN.2 ?_, hs⟩
      intro i j
      fin_cases i <;> fin_cases j <;> simp [radEltQ]
      · exact (mul_dvd_mul_iff_left hN).2 h1
      · exact (mul_dvd_mul_iff_left hN).2 h2

theorem lineFace_relIndex_eq {N M : ℕ} [NeZero N] [NeZero M] (hN : 3 ≤ N) (hNM : N ∣ M) (h : SL(3, ℤ)) :
    (gammaNQAt M h).relIndex (gammaNQAt N h) =
      (M / N) ^ 2 * (CongruenceSubgroup.Gamma M).relIndex (CongruenceSubgroup.Gamma N) := by
  have hM : 3 ≤ M := hN.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hNM)
  rw [gammaNQAt_relIndex_eq hN hM, ← gammaNQ_eq_inf N hN, ← gammaNQ_eq_inf M hM]
  exact lineStd_relIndex_eq hNM

end TernaryPeriodPolynomials.Argument.FaceFibre
