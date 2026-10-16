module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LtBij
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LtInj

@[expose] public section


/-!
# Permutation of the cyclic Hermite classes under left multiplication by `GL₂(ℤ_p)`

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For `k ∈ GL₂(ℤ_p)` (unit determinant) and a cyclic Hermite triple `t` of level `p^r`, the matrix
`k · Mz t` has column lattice `k · L_t`. The map `t ↦ σ t` sending `L_t` to `k · L_t` permutes
`cyclicHNF p r` (the image of a cyclic lattice of index `p^r` is again one, `hermLat_index_cyclic`
and `exists_cyclicHNF_hermLat`; injectivity is `hermLat_inj`). Two matrices with the same column
lattice differ by a right unit `U ∈ GL₂(ℤ_p)`, so for any `F` invariant under right multiplication by
such `U`, `∑_t F(k · Mz t) = ∑_t F(Mz t)` (`sum_perm`).

No analysis is used here; everything is over `ℤ_p`.
-/

open PadicInt Matrix
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp (mulLin mulLin_apply mulLin_mul Mz Mz_det)
open TernaryPeriodPolynomials.Argument.LatticeCounts (cyclicHNF hnfData mem_hnfData)
open TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HermitePerm

variable {p : ℕ} [hp : Fact p.Prime]

theorem mulLin_one' : mulLin (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext <;> simp [mulLin_apply]

/-- Left multiplication by a unit-determinant `2 × 2` matrix over `ℤ_p` is a linear equivalence. -/
def mulEquiv (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hk : IsUnit k.det) :
    (ℤ_[p] × ℤ_[p]) ≃ₗ[ℤ_[p]] (ℤ_[p] × ℤ_[p]) :=
  LinearEquiv.ofLinearMap (mulLin k) (mulLin k⁻¹)
    (by rw [← mulLin_mul, Matrix.mul_nonsing_inv k hk, mulLin_one'])
    (by rw [← mulLin_mul, Matrix.nonsing_inv_mul k hk, mulLin_one'])

theorem mulEquiv_injective (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hk : IsUnit k.det) :
    Function.Injective (mulLin k) :=
  (mulEquiv k hk).injective

/-- Mapping a lattice by `k` preserves its index. -/
theorem map_mulLin_index (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hk : IsUnit k.det)
    (Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])) :
    (Submodule.map (mulLin k) Λ).toAddSubgroup.index = Λ.toAddSubgroup.index := by
  have h : (Submodule.map (mulLin k) Λ).toAddSubgroup =
      AddSubgroup.map (mulEquiv k hk).toAddEquiv.toAddMonoidHom Λ.toAddSubgroup := by
    refine AddSubgroup.ext fun x => ?_
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [h]
  exact AddSubgroup.index_map_equiv Λ.toAddSubgroup (mulEquiv k hk).toAddEquiv

/-- Mapping a lattice by `k` preserves cyclicity of the quotient. -/
theorem map_mulLin_cyclic (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hk : IsUnit k.det)
    (Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]))
    (hc : IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)) :
    IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ (Submodule.map (mulLin k) Λ).toAddSubgroup) := by
  let f : (ℤ_[p] × ℤ_[p]) →+ (ℤ_[p] × ℤ_[p]) := (mulLin k).toAddMonoidHom
  let g : ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup) →+
      ((ℤ_[p] × ℤ_[p]) ⧸ (Submodule.map (mulLin k) Λ).toAddSubgroup) :=
    QuotientAddGroup.map Λ.toAddSubgroup (Submodule.map (mulLin k) Λ).toAddSubgroup f (by
      intro x hx
      exact Submodule.mem_map_of_mem hx)
  refine isAddCyclic_of_surjective g ?_
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hz : mulLin k (mulLin k⁻¹ x) = x := by
    rw [← LinearMap.comp_apply, ← mulLin_mul, Matrix.mul_nonsing_inv k hk, mulLin_one',
      LinearMap.id_apply]
  exact ⟨QuotientAddGroup.mk (mulLin k⁻¹ x), by
    show QuotientAddGroup.mk (mulLin k (mulLin k⁻¹ x)) = QuotientAddGroup.mk x
    rw [hz]⟩

/-- Mapping a lattice by `k` and then by `k⁻¹` is the identity. -/
theorem map_mulLin_inv (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hk : IsUnit k.det)
    (L : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])) :
    Submodule.map (mulLin k) (Submodule.map (mulLin k⁻¹) L) = L := by
  rw [← Submodule.map_comp, ← mulLin_mul, Matrix.mul_nonsing_inv k hk, mulLin_one', Submodule.map_id]

/-- A column-wise factorisation from an inclusion of column lattices. -/
theorem factor_of_range_le (M N : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (h : LinearMap.range (mulLin M) ≤ LinearMap.range (mulLin N)) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ_[p], M = N * U := by
  obtain ⟨c0, hc0⟩ := h (LinearMap.mem_range_self (mulLin M) (1, 0))
  obtain ⟨c1, hc1⟩ := h (LinearMap.mem_range_self (mulLin M) (0, 1))
  have a00 : N 0 0 * c0.1 + N 0 1 * c0.2 = M 0 0 := by
    have := congrArg Prod.fst hc0
    simpa [mulLin_apply] using this
  have a10 : N 1 0 * c0.1 + N 1 1 * c0.2 = M 1 0 := by
    have := congrArg Prod.snd hc0
    simpa [mulLin_apply] using this
  have a01 : N 0 0 * c1.1 + N 0 1 * c1.2 = M 0 1 := by
    have := congrArg Prod.fst hc1
    simpa [mulLin_apply] using this
  have a11 : N 1 0 * c1.1 + N 1 1 * c1.2 = M 1 1 := by
    have := congrArg Prod.snd hc1
    simpa [mulLin_apply] using this
  refine ⟨!![c0.1, c1.1; c0.2, c1.2], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, a00, a01, a10, a11]

/-- Equal column lattices with `N` of nonzero determinant differ by a right unit of `GL₂(ℤ_p)`. -/
theorem eq_mul_unit_of_range_eq (M N : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hN : N.det ≠ 0)
    (h : LinearMap.range (mulLin M) = LinearMap.range (mulLin N)) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ_[p], M = N * U ∧ IsUnit U.det := by
  obtain ⟨U, hU⟩ := factor_of_range_le M N h.le
  obtain ⟨V, hV⟩ := factor_of_range_le N M h.ge
  have h1 : N * (U * V) = N * 1 := by
    rw [← Matrix.mul_assoc, ← hU, ← hV, mul_one]
  have h2 : N.det • (U * V) = N.det • (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]) := by
    calc N.det • (U * V) = Matrix.adjugate N * (N * (U * V)) := by
          rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = Matrix.adjugate N * (N * 1) := by rw [h1]
      _ = N.det • (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]) := by
          rw [mul_one, Matrix.adjugate_mul]
  have hUV : U * V = 1 := by
    ext i j : 1
    have hij := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    exact mul_left_cancel₀ hN hij
  exact ⟨U, hU, Matrix.isUnit_det_of_right_inverse hUV⟩

/-- Every cyclic Hermite class is sent by `k` to a cyclic Hermite class of the same level. -/
theorem exists_perm_image (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hk : IsUnit k.det) {r : ℕ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF p r) :
    ∃ t' ∈ cyclicHNF p r, hermLat p t' = Submodule.map (mulLin k) (hermLat p t) := by
  obtain ⟨hidx, hcyc⟩ := hermLat_index_cyclic (p := p) ht
  exact exists_cyclicHNF_hermLat (s := r) (Λ := Submodule.map (mulLin k) (hermLat p t))
    (by rw [map_mulLin_index k hk]; exact hidx)
    (map_mulLin_cyclic k hk _ hcyc)

theorem hermLat_eq_range (t : ℕ × ℕ × ℕ) :
    hermLat p t = LinearMap.range (mulLin (Mz (q := p) t)) := rfl

omit hp in
theorem mem_hnf_of_cyclic {r : ℕ} {x : ℕ × ℕ × ℕ} (hx : x ∈ cyclicHNF p r) :
    x ∈ hnfData (p ^ r) :=
  (Finset.mem_filter.1 hx).1

theorem mz_det_ne_zero {r : ℕ} {x : ℕ × ℕ × ℕ} (hx : x ∈ cyclicHNF p r) :
    (Mz (q := p) x).det ≠ 0 := by
  obtain ⟨-, hd, -⟩ := (mem_hnfData (pow_pos hp.out.pos r) x).1 (Finset.mem_filter.1 hx).1
  rw [Mz_det, hd]
  exact_mod_cast pow_ne_zero r hp.out.ne_zero

/-- **Permutation of the cyclic classes.** For `F` invariant under right multiplication by
`GL₂(ℤ_p)`, the sum over the cyclic Hermite classes of `F(k · Mz t)` equals the sum of `F(Mz t)`. -/
theorem sum_perm (F : Matrix (Fin 2) (Fin 2) ℤ_[p] → ℂ)
    (hF : ∀ (M U : Matrix (Fin 2) (Fin 2) ℤ_[p]), IsUnit U.det → F (M * U) = F M)
    (k : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hk : IsUnit k.det) (r : ℕ) :
    ∑ t ∈ cyclicHNF p r, F (k * Mz (q := p) t) = ∑ t ∈ cyclicHNF p r, F (Mz (q := p) t) := by
  have hex : ∀ t ∈ cyclicHNF p r, ∃ t' ∈ cyclicHNF p r,
      hermLat p t' = Submodule.map (mulLin k) (hermLat p t) :=
    fun t ht => exists_perm_image k hk ht
  choose! σ hσ hσeq using hex
  have hrange : ∀ t ∈ cyclicHNF p r, ∃ U : Matrix (Fin 2) (Fin 2) ℤ_[p],
      k * Mz (q := p) t = Mz (q := p) (σ t) * U ∧ IsUnit U.det := by
    intro t ht
    apply eq_mul_unit_of_range_eq _ _ (mz_det_ne_zero (hσ t ht))
    have h1 : LinearMap.range (mulLin (k * Mz (q := p) t)) =
        Submodule.map (mulLin k) (LinearMap.range (mulLin (Mz (q := p) t))) := by
      rw [mulLin_mul, LinearMap.range_comp]
    have h2 : LinearMap.range (mulLin (Mz (q := p) (σ t))) =
        Submodule.map (mulLin k) (LinearMap.range (mulLin (Mz (q := p) t))) := hσeq t ht
    rw [h1, h2]
  refine Finset.sum_bij (fun t _ => σ t) (fun t ht => hσ t ht) ?_ ?_ ?_
  · intro a ha b hb hab
    have h1 : hermLat p (σ a) = hermLat p (σ b) := by rw [hab]
    rw [hσeq a ha, hσeq b hb] at h1
    have h2 : hermLat p a = hermLat p b :=
      Submodule.map_injective_of_injective (mulEquiv_injective k hk) h1
    exact hermLat_inj (mem_hnf_of_cyclic ha) (mem_hnf_of_cyclic hb) h2
  · intro b hb
    obtain ⟨a, ha, hae⟩ := exists_perm_image k⁻¹ (Matrix.isUnit_nonsing_inv_det k hk) hb
    refine ⟨a, ha, ?_⟩
    have h1 : hermLat p (σ a) = hermLat p b := by
      rw [hσeq a ha, hae, map_mulLin_inv k hk]
    exact hermLat_inj (mem_hnf_of_cyclic (hσ a ha)) (mem_hnf_of_cyclic hb) h1
  · intro a ha
    obtain ⟨U, hU, hUu⟩ := hrange a ha
    rw [hU, hF _ _ hUu]

end TernaryPeriodPolynomials.Argument.LatticeCounts.HermitePerm

end
