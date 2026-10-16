module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Dictionary
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Noncyclic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.CyclicCount

@[expose] public section


/-!
# Surjectivity of `Λ ↦ Λ ∩ ℤ²` on ℤ_p-lattices: obligations O1 and O2

Formalized by Claude Haiku 5.5.
Paper: Appendix C.

For `L ⊆ ℤ²` of index `p^r`, `latOfZ p r L` is the set of `x ∈ ℤ_p²` whose reduction modulo `p^r`
lies in the reduction of `L`. It is a `ℤ_p`-submodule (obligation O2, `latOfZ` is a `Submodule`),
of index `p^r` (`latOfZ_index`), and its integral part is `L` (`zPart_latOfZ`). Conversely a
`ℤ_p`-submodule `Λ` of index `p^r` is recovered as `latOfZ p r (zPart Λ)` (`latOfZ_zPart`).
Hence `Λ ↦ Λ ∩ ℤ²` is a bijection between index-`p^r` `ℤ_p`-lattices and index-`p^r` subgroups of
`ℤ²` (`latticeEquivZ`), and it preserves cyclicity (`cyclic_equiv`). The count of cyclic
`ℤ_p`-lattices of index `p^r` is therefore `p^r + p^(r-1)` (`card_cyclic_lattices`, `r ≥ 1`), and the
count of all of them is `∑_{i ≤ r} p^i` (`card_lattices`). These are the equalities that
`PadicDictionary` left as the O1 obligation.
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- Reduction `ℤ_p² → (ℤ/p^r)²` coordinatewise. -/
noncomputable def redP (r : ℕ) : ℤ_[p] × ℤ_[p] →+ ZMod (p ^ r) × ZMod (p ^ r) :=
  AddMonoidHom.mk' (fun v => (toZModPow r v.1, toZModPow r v.2)) (fun a b => by simp)

/-- Reduction `ℤ² → (ℤ/p^r)²` coordinatewise. -/
def redZ (p r : ℕ) : ℤ × ℤ →+ ZMod (p ^ r) × ZMod (p ^ r) :=
  AddMonoidHom.mk' (fun v => ((v.1 : ZMod (p ^ r)), (v.2 : ZMod (p ^ r)))) (fun a b => by simp)

theorem redP_iota (r : ℕ) (v : ℤ × ℤ) : redP (p := p) r (iota p v) = redZ p r v := by
  simp [redP, redZ, iota]

omit hp in
theorem redZ_surjective (r : ℕ) : Function.Surjective (redZ p r) := by
  intro q
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective q.1
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective q.2
  exact ⟨(a, b), Prod.ext ha hb⟩

theorem redP_surjective (r : ℕ) : Function.Surjective (redP (p := p) r) := by
  intro q
  obtain ⟨v, hv⟩ := redZ_surjective (p := p) r q
  exact ⟨iota p v, by rw [redP_iota]; exact hv⟩

omit hp in
/-- An integral vector reducing to zero modulo `p^r` lies in a subgroup of index `p^r`. -/
theorem mem_of_redZ_eq_zero {r : ℕ} {L : AddSubgroup (ℤ × ℤ)} (hL : L.index = p ^ r) {u : ℤ × ℤ}
    (hu : redZ p r u = 0) : u ∈ L := by
  have h1 : ((p ^ r : ℕ) : ℤ) ∣ u.1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd u.1 (p ^ r)).mp (congrArg Prod.fst hu)
  have h2 : ((p ^ r : ℕ) : ℤ) ∣ u.2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd u.2 (p ^ r)).mp (congrArg Prod.snd hu)
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hu' : u = (p ^ r) • ((a, b) : ℤ × ℤ) := by
    refine Prod.ext ?_ ?_
    · simpa [smul_eq_mul] using ha
    · simpa [smul_eq_mul] using hb
  have hm := AddSubgroup.nsmul_index_mem L (a, b)
  rw [hL] at hm
  rw [hu']
  exact hm

omit hp in
/-- For `L` of index `p^r`, the reduction of `v` lies in the reduction of `L` iff `v ∈ L`. -/
theorem redZ_mem_map_iff {r : ℕ} {L : AddSubgroup (ℤ × ℤ)} (hL : L.index = p ^ r) (v : ℤ × ℤ) :
    redZ p r v ∈ L.map (redZ p r) ↔ v ∈ L := by
  constructor
  · rintro ⟨w, hw, e⟩
    have hd : redZ p r (v - w) = 0 := by rw [map_sub, e, sub_self]
    have h := L.add_mem hw (mem_of_redZ_eq_zero hL hd)
    simpa using h
  · exact fun hv => ⟨v, hv, rfl⟩

omit hp in
/-- The index of the reduction of `L` in `(ℤ/p^r)²` is `p^r`. -/
theorem index_map_redZ {r : ℕ} {L : AddSubgroup (ℤ × ℤ)} (hL : L.index = p ^ r) :
    (L.map (redZ p r)).index = p ^ r := by
  have hker : (redZ p r).ker ≤ L := fun u hu => mem_of_redZ_eq_zero hL (AddMonoidHom.mem_ker.mp hu)
  have h1 := AddSubgroup.index_comap_of_surjective (L.map (redZ p r)) (redZ_surjective (p := p) r)
  rw [AddSubgroup.comap_map_eq, sup_eq_left.mpr hker, hL] at h1
  exact h1.symm

/-- The ℤ_p-lattice of an integral subgroup `L ⊆ ℤ²`: the points whose reduction modulo `p^r`
lies in the reduction of `L`. -/
noncomputable def latOfZ (p r : ℕ) [Fact p.Prime] (L : AddSubgroup (ℤ × ℤ)) :
    Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) where
  carrier := {x | redP (p := p) r x ∈ L.map (redZ p r)}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact AddSubgroup.add_mem _ ha hb
  zero_mem' := by
    show redP (p := p) r 0 ∈ L.map (redZ p r)
    rw [map_zero]
    exact AddSubgroup.zero_mem _
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (toZModPow r c)
    have e : redP (p := p) r (c • x) = k • redP (p := p) r x := by
      ext
      · simp [redP, zsmul_eq_mul, hk]
      · simp [redP, zsmul_eq_mul, hk]
    rw [e]
    exact AddSubgroup.zsmul_mem _ hx k

theorem latOfZ_toAddSubgroup {r : ℕ} (L : AddSubgroup (ℤ × ℤ)) :
    (latOfZ p r L).toAddSubgroup = AddSubgroup.comap (redP (p := p) r) (L.map (redZ p r)) :=
  rfl

/-- `ℤ_p²`-lattice index: the index of `latOfZ L` is `p^r`. -/
theorem latOfZ_index {r : ℕ} {L : AddSubgroup (ℤ × ℤ)} (hL : L.index = p ^ r) :
    (latOfZ p r L).toAddSubgroup.index = p ^ r := by
  rw [latOfZ_toAddSubgroup, AddSubgroup.index_comap_of_surjective _ (redP_surjective r),
    index_map_redZ hL]

/-- The integral part of `latOfZ L` is `L`. -/
theorem zPart_latOfZ {r : ℕ} {L : AddSubgroup (ℤ × ℤ)} (hL : L.index = p ^ r) :
    zPart (latOfZ p r L).toAddSubgroup = L := by
  ext v
  rw [mem_zPart]
  show redP (p := p) r (iota p v) ∈ L.map (redZ p r) ↔ v ∈ L
  rw [redP_iota]
  exact redZ_mem_map_iff hL v

theorem redP_pow_smul (r : ℕ) (y : ℤ_[p] × ℤ_[p]) : redP (p := p) r ((p ^ r) • y) = 0 := by
  have hk : ∀ z : ℤ_[p], toZModPow r ((p : ℤ_[p]) ^ r * z) = 0 := fun z => by
    have hmem : (p : ℤ_[p]) ^ r * z ∈ Ideal.span {(p : ℤ_[p]) ^ r} :=
      Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [← ker_toZModPow, RingHom.mem_ker] at hmem
    exact hmem
  ext
  · simp only [redP, AddMonoidHom.mk'_apply, nsmul_eq_mul, Prod.fst_zero]
    push_cast
    exact hk _
  · simp only [redP, AddMonoidHom.mk'_apply, nsmul_eq_mul, Prod.snd_zero]
    push_cast
    exact hk _

/-- Every `ℤ_p`-lattice of index `p^r` is recovered from its integral part. -/
theorem latOfZ_zPart {r : ℕ} {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])}
    (hΛ : Λ.toAddSubgroup.index = p ^ r) :
    latOfZ p r (zPart Λ.toAddSubgroup) = Λ := by
  ext x
  obtain ⟨v, y, hxy⟩ := approx_pair (p := p) r x
  have hy : (p ^ r) • y ∈ Λ.toAddSubgroup := pow_smul_mem_of_index hΛ y
  have hred : redP (p := p) r x = redZ p r v := by
    rw [hxy, map_add, redP_pow_smul, add_zero, redP_iota]
  show redP (p := p) r x ∈ (zPart Λ.toAddSubgroup).map (redZ p r) ↔ x ∈ Λ
  rw [hred, redZ_mem_map_iff (index_zPart hΛ) v, mem_zPart]
  rw [hxy]
  constructor
  · intro h
    exact Λ.toAddSubgroup.add_mem h hy
  · intro h
    have := Λ.toAddSubgroup.sub_mem h hy
    simpa using this

/-- **O1 and O2.** Index-`p^r` `ℤ_p`-lattices in `ℤ_p²` correspond bijectively to index-`p^r`
subgroups of `ℤ²`, by `Λ ↦ Λ ∩ ℤ²` with inverse `L ↦ latOfZ p r L`. -/
noncomputable def latticeEquivZ (p r : ℕ) [Fact p.Prime] :
    {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) // Λ.toAddSubgroup.index = p ^ r} ≃
      {L : AddSubgroup (ℤ × ℤ) // L.index = p ^ r} where
  toFun Λ := ⟨zPart Λ.1.toAddSubgroup, index_zPart Λ.2⟩
  invFun L := ⟨latOfZ p r L.1, latOfZ_index L.2⟩
  left_inv Λ := Subtype.ext (latOfZ_zPart Λ.2)
  right_inv L := Subtype.ext (zPart_latOfZ L.2)

/-- The number of `ℤ_p`-lattices of index `p^r` in `ℤ_p²` is `∑_{i ≤ r} p^i`. -/
theorem card_lattices (p r : ℕ) [Fact p.Prime] :
    Nat.card {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) // Λ.toAddSubgroup.index = p ^ r} =
      ∑ i ∈ Finset.range (r + 1), p ^ i := by
  rw [Nat.card_congr (latticeEquivZ p r), LatticeCounts.card_index_subgroups]

/-- Cyclicity transfers along `latticeEquivZ`: `ℤ_p²/Λ` is cyclic iff `ℤ²/(Λ ∩ ℤ²)` is. -/
noncomputable def cyclicEquiv (p r : ℕ) [Fact p.Prime] :
    {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) // Λ.toAddSubgroup.index = p ^ r ∧
        IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)} ≃
      {L : AddSubgroup (ℤ × ℤ) // L.index = p ^ r ∧ IsAddCyclic ((ℤ × ℤ) ⧸ L)} where
  toFun Λ := ⟨zPart Λ.1.toAddSubgroup, index_zPart Λ.2.1,
    (isAddCyclic_quot_iff Λ.2.1).mp Λ.2.2⟩
  invFun L := ⟨latOfZ p r L.1, latOfZ_index L.2.1,
    (isAddCyclic_quot_iff (latOfZ_index L.2.1)).mpr (by
      rw [zPart_latOfZ L.2.1]
      exact L.2.2)⟩
  left_inv Λ := Subtype.ext (latOfZ_zPart Λ.2.1)
  right_inv L := Subtype.ext (zPart_latOfZ L.2.1)

/-- The number of cyclic `ℤ_p`-lattices of index `p^r` in `ℤ_p²` is `p^r + p^(r-1)`, for `r ≥ 1`. -/
theorem card_cyclic_lattices (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r) :
    Nat.card {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) // Λ.toAddSubgroup.index = p ^ r ∧
        IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)} = p ^ r + p ^ (r - 1) := by
  rw [Nat.card_congr (cyclicEquiv p r), LatticeCounts.card_cyclic_index_subgroups hr]

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
