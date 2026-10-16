module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.IndexP
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Noncyclic

@[expose] public section


/-!
# Noncyclic `ℤ_p`-lattices of index `p^(s+2)` are `p` times lattices of index `p^s`

Formalized by Claude Haiku 5.5.
Imports: `PadicIndexP` (index `[ℤ_p : pℤ_p] = p`) and `PadicNoncyclic` (noncyclicity criterion).

For a `ℤ_p`-submodule `Λ'` of `ℤ_p²`, `mulP p Λ' = p Λ'` has index `[ℤ_p² : Λ'] · p²`
(`index_mulP`), since multiplication by `p` is injective with image `(pℤ_p)²`, of index `p²`.
It is noncyclic, and `Λ' ↦ pΛ'` is a bijection from lattices of index `p^s` onto noncyclic lattices
of index `p^(s+2)` (`mulPEquiv`), with inverse `Λ ↦ Λ.comap (p•)`.
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

open TernaryPeriodPolynomials.Argument.LatticeCounts.PadicIndex

variable {p : ℕ} [hp : Fact p.Prime]

/-- Multiplication by `p` on `ℤ_p²`, as a `ℤ_p`-linear map. -/
noncomputable def sP (p : ℕ) [Fact p.Prime] :
    (ℤ_[p] × ℤ_[p]) →ₗ[ℤ_[p]] (ℤ_[p] × ℤ_[p]) :=
  (p : ℤ_[p]) • (LinearMap.id : (ℤ_[p] × ℤ_[p]) →ₗ[ℤ_[p]] (ℤ_[p] × ℤ_[p]))

theorem sP_apply (x : ℤ_[p] × ℤ_[p]) : sP p x = (p : ℤ_[p]) • x := rfl

theorem p_ne_zero_padic : (p : ℤ_[p]) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

theorem sP_injective : Function.Injective (sP (p := p)) := by
  intro x y h
  rw [sP_apply, sP_apply] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  exact Prod.ext (mul_left_cancel₀ p_ne_zero_padic h1) (mul_left_cancel₀ p_ne_zero_padic h2)

/-- The image of `sP` is `{v | p ∣ v.1 ∧ p ∣ v.2}`. -/
theorem mem_range_sP (v : ℤ_[p] × ℤ_[p]) :
    v ∈ LinearMap.range (sP (p := p)) ↔ (p : ℤ_[p]) ∣ v.1 ∧ (p : ℤ_[p]) ∣ v.2 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [sP_apply]
    exact ⟨⟨x.1, by simp [smul_eq_mul]⟩, ⟨x.2, by simp [smul_eq_mul]⟩⟩
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    refine ⟨(c, d), ?_⟩
    rw [sP_apply]
    exact Prod.ext (by simp [smul_eq_mul, hc]) (by simp [smul_eq_mul, hd])

/-- `pΛ'`, the image of `Λ'` under multiplication by `p`. -/
noncomputable def mulP (p : ℕ) [Fact p.Prime]
    (Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])) : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) :=
  Λ.map (sP p)

theorem mulP_le_range (Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])) :
    mulP p Λ ≤ LinearMap.range (sP (p := p)) :=
  LinearMap.map_le_range

/-- The image of `ℤ_p²` under `p` is `(pℤ_p)²`. -/
theorem range_sP_eq_prod :
    ((sP (p := p) : (ℤ_[p] × ℤ_[p]) →+ (ℤ_[p] × ℤ_[p]))).range =
      (Ideal.span {(p : ℤ_[p])}).toAddSubgroup.prod (Ideal.span {(p : ℤ_[p])}).toAddSubgroup := by
  ext v
  rw [AddMonoidHom.mem_range, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup,
    Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  have key := mem_range_sP (p := p) v
  rw [LinearMap.mem_range] at key
  constructor
  · rintro ⟨x, hx⟩
    have := (key.mp ⟨x, hx⟩)
    exact this
  · intro h
    obtain ⟨x, hx⟩ := key.mpr h
    exact ⟨x, hx⟩

/-- The index of `pΛ'` is `[ℤ_p² : Λ'] · p²`. -/
theorem index_mulP (Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])) :
    (mulP p Λ).toAddSubgroup.index = Λ.toAddSubgroup.index * p ^ 2 := by
  rw [mulP, Submodule.map_toAddSubgroup]
  refine (AddSubgroup.index_map_of_injective (H := Λ.toAddSubgroup)
    (f := (sP p : (ℤ_[p] × ℤ_[p]) →+ (ℤ_[p] × ℤ_[p])))
    (sP_injective (p := p))).trans ?_
  rw [range_sP_eq_prod, AddSubgroup.index_prod, index_span_p, sq]

/-- `pΛ'` is noncyclic. -/
theorem not_isAddCyclic_mulP (Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])) :
    ¬ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ (mulP p Λ).toAddSubgroup) := by
  apply not_isAddCyclic_of_le
  intro v hv
  exact (mem_range_sP v).mp (mulP_le_range Λ (show v ∈ mulP p Λ from hv))

/-- A noncyclic lattice of index `p^r` is contained in `pℤ_p²`. -/
theorem le_range_of_not_isAddCyclic {r : ℕ} {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])}
    (hΛ : Λ.toAddSubgroup.index = p ^ r)
    (hn : ¬ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)) :
    Λ ≤ LinearMap.range (sP (p := p)) := by
  intro v hv
  rw [mem_range_sP]
  exact (not_isAddCyclic_iff hΛ).mp hn v hv

/-- `mulP` commutes with preimage: `p · (p⁻¹ Λ) = Λ` for noncyclic `Λ`. -/
theorem mulP_comap {r : ℕ} {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])}
    (hΛ : Λ.toAddSubgroup.index = p ^ r)
    (hn : ¬ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)) :
    mulP p (Λ.comap (sP p)) = Λ := by
  rw [mulP, Submodule.map_comap_eq, inf_of_le_right (le_range_of_not_isAddCyclic hΛ hn)]

/-- Index-`p^s` lattices `Λ'` correspond to noncyclic index-`p^(s+2)` lattices `pΛ'`. -/
noncomputable def mulPEquiv (p : ℕ) [hpp : Fact p.Prime] (s : ℕ) :
    {Λ' : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) // Λ'.toAddSubgroup.index = p ^ s} ≃
      {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) //
        Λ.toAddSubgroup.index = p ^ (s + 2) ∧
          ¬ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)} where
  toFun Λ' :=
    ⟨mulP p Λ'.1, by
      rw [index_mulP, Λ'.2, pow_add], not_isAddCyclic_mulP Λ'.1⟩
  invFun Λ :=
    ⟨Λ.1.comap (sP p), by
      have h1 : mulP p (Λ.1.comap (sP p)) = Λ.1 := mulP_comap Λ.2.1 Λ.2.2
      have h3 : (mulP p (Λ.1.comap (sP p))).toAddSubgroup.index = p ^ (s + 2) := by
        rw [h1]
        exact Λ.2.1
      have h4 : p ^ (s + 2) = p ^ s * p ^ 2 := pow_add _ _ _
      rw [index_mulP] at h3
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hpp.out.pos 2) (h3.trans h4)⟩
  left_inv Λ' := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective (sP_injective (p := p)) _
  right_inv Λ := by
    apply Subtype.ext
    exact mulP_comap Λ.2.1 Λ.2.2

/-- The count of noncyclic index-`p^(s+2)` lattices equals the count of all index-`p^s` lattices. -/
theorem card_noncyclic_eq_card_index (s : ℕ) :
    Nat.card {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) //
        Λ.toAddSubgroup.index = p ^ (s + 2) ∧
          ¬ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)} =
      Nat.card {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) // Λ.toAddSubgroup.index = p ^ s} :=
  (Nat.card_congr (mulPEquiv p s)).symm

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
