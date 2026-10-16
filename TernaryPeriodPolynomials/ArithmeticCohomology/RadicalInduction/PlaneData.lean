module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps

@[expose] public section


/-!
# The plane groups of the orbit decomposition: the four geometric inputs `P1`-`P4`

Formalized by Claude Sonnet 5.5.

For `P u : SL₃(ℤ)`, `6 ∣ M`, `h = P * u`, `K = gammaNPAt 6 P`, `K' = gammaNPAt M h`:
`plane_hmem` (P1) `u⁻¹ K u ∩ Γ(M) ⊆ K'`; `plane_hback` (P2) `u K' u⁻¹ ⊆ K`; `plane_hinl` (P3) `u · inl_M(r) · u⁻¹ = inl_6(r^{M/6})`; `plane_hspl` (P4) `u · s_M(m) · u⁻¹ = s_6(m)`.
-/

open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem gammaN_le_of_dvd {N M : ℕ} (h : N ∣ M) : gammaN M ≤ gammaN N := by
  intro g hg
  rw [mem_gammaN] at hg ⊢
  exact fun i j => dvd_trans (Int.natCast_dvd_natCast.mpr h) (hg i j)

theorem planeExt_inl_val (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (r : RadicalLattice) :
    (((faceExt N h).inl r : ↥(gammaNPAt N h)) : SL(3, ℤ)) = h⁻¹ * radElt N r * h := rfl

theorem planeSplitting_val (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (m : ↥(CongruenceSubgroup.Gamma N)) :
    (((faceSplitting N h m : ↥(gammaNPAt N h))) : SL(3, ℤ)) = h⁻¹ * blockDiag m.1 * h := rfl

theorem radElt_mul_pow (m0 : ℕ) (r : RadicalLattice) : radElt (6 * m0) r = radElt 6 (r ^ m0) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radElt, toAdd_pow] <;> ring

theorem radElt_div {M : ℕ} (h6 : 6 ∣ M) (r : RadicalLattice) : radElt M r = radElt 6 (r ^ (M / 6)) := by
  obtain ⟨m0, rfl⟩ := h6
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  exact radElt_mul_pow m0 r

variable {M : ℕ} (P u : SL(3, ℤ))

/-- **P1**: the elements of `K = Γ_{P⁻¹ P_0 P}` (level 6) whose `u`-conjugate is in `Γ(M)` lie in `K' = Γ_{(Pu)⁻¹ P_0 (Pu)}` (level `M`). -/
theorem plane_hmem : ∀ s ∈ gammaNPAt 6 P, s ∈ gammaN 6 → u⁻¹ * s * u ∈ gammaN M → u⁻¹ * s * u ∈ gammaNPAt M (P * u) := by
  intro s hs _ hM
  rw [mem_gammaNPAt] at hs ⊢
  have e : P * u * (u⁻¹ * s * u) * (P * u)⁻¹ = P * s * P⁻¹ := by group
  rw [e]
  refine ⟨?_, hs.2⟩
  have e2 : P * s * P⁻¹ = (P * u) * (u⁻¹ * s * u) * (P * u)⁻¹ := e.symm
  rw [e2]
  exact (inferInstance : (gammaN M).Normal).conj_mem _ hM _

/-- **P2**: `u K' u⁻¹ ⊆ K` when `6 ∣ M`. -/
theorem plane_hback (h6 : 6 ∣ M) : ∀ p ∈ gammaNPAt M (P * u), u * p * u⁻¹ ∈ gammaNPAt 6 P := by
  intro p hp
  rw [mem_gammaNPAt] at hp ⊢
  have e : P * (u * p * u⁻¹) * P⁻¹ = P * u * p * (P * u)⁻¹ := by group
  rw [e]
  exact ⟨gammaN_le_of_dvd h6 hp.1, hp.2⟩

/-- **P3**: the radical of the level-`M` face is the `M/6`-th power of the radical of the level-6 face. -/
theorem plane_hinl [NeZero M] (h6 : 6 ∣ M) (r : RadicalLattice) :
    u * (((faceExt M (P * u)).inl r : ↥(gammaNPAt M (P * u))) : SL(3, ℤ)) * u⁻¹ =
      (((faceExt 6 P).inl (r ^ (M / 6)) : ↥(gammaNPAt 6 P)) : SL(3, ℤ)) := by
  rw [planeExt_inl_val, planeExt_inl_val, radElt_div h6]
  group

/-- **P4**: the Levi splitting of the level-`M` face is the restriction of that of the level-6 face. -/
theorem plane_hspl [NeZero M] (hle : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma 6)
    (m : ↥(CongruenceSubgroup.Gamma M)) :
    u * ((faceSplitting M (P * u) m : ↥(gammaNPAt M (P * u))) : SL(3, ℤ)) * u⁻¹ =
      ((faceSplitting 6 P (Subgroup.inclusion hle m) : ↥(gammaNPAt 6 P)) : SL(3, ℤ)) := by
  rw [planeSplitting_val, planeSplitting_val]
  change _ = _ * blockDiag m.1 * _
  group

end TernaryPeriodPolynomials.Argument.RadicalInduction
