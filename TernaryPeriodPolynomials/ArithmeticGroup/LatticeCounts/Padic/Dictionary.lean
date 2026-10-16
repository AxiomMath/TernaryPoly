module

public import Mathlib
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.HNF
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.Cyclic

@[expose] public section


/-!
# Finite-quotient dictionary for ℤ_p-lattices in ℤ_p²

Formalized by Claude Haiku 5.5.
Paper: Appendix C.

Let `Λ ⊆ ℤ_p²` be an additive subgroup of finite index `p^r`. We show:
* `Λ ⊇ (p^r) ℤ_p²` (`pow_smul_mem_of_index`);
* `Λ ∩ ℤ²` has index `p^r` in `ℤ²` (`index_zPart`), and `Λ ↦ Λ ∩ ℤ²` is injective on such lattices
  (`zPart_injOn`);
* `ℤ_p²/Λ` is cyclic iff `ℤ²/(Λ ∩ ℤ²)` is cyclic (`isAddCyclic_quot_iff`);
* hence `Λ ↦ Λ ∩ ℤ²` sends cyclic index-`p^r` lattices injectively into the cyclic Hermite triples
  (`exists_latOf_zPart`, `isAddCyclic_quot_iff_gcd`).

Sibling files (namespace `Padic`):
* O1 (surjectivity of `Λ ↦ Λ ∩ ℤ²`) and O2 (`ℤ_p`-stability of the lift `latOfZ`): `PadicSurjective.lean`
  (`latticeEquivZ`, `card_lattices`, `card_cyclic_lattices`). The cyclic index-`p^r` lattices number
  `p^r + p^(r-1)` for `r ≥ 1`.
* O5 (noncyclic shape): `PadicNoncyclic.lean` (`not_isAddCyclic_iff`): `ℤ_p²/Λ` is
  noncyclic iff `Λ ⊆ pℤ_p²`.
* O3, shell as a union of `ℤ_p²`-cosets of measure one: `ShellCoset.lean`
  (`pairShell_eq_union_cosets`, `pairShell_coset_measure`, with `μ(ℤ_p²) = 1` as an explicit
  hypothesis), and `pairLat_index`, `isAddCyclic_pairLat` for `Λ_z`.

O3 (see `ShellCoset.lean` for the list):
* O3a: every cyclic `Λ` of index `p^r` equals `Λ_z` for some shell point `z` (`ShellSurj.lean`).
* O3b: the fibre of `z ↦ Λ_z` over a lattice has `(1-p^{-1})p^r` primitive pairs mod `p^r`, differing by
  units (`ShellFibre.lean`).
* O3c: the number of `ℤ_p²`-cosets in the shell is `p^{2r} - p^{2r-2}`, and the shell measure under
  `μ(ℤ_p²) = 1` is `p^{2r} - p^{2r-2}` (`ShellCount.lean`).
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- The inclusion `ℤ² → ℤ_p²`. -/
noncomputable def iota (p : ℕ) [Fact p.Prime] : ℤ × ℤ →+ ℤ_[p] × ℤ_[p] :=
  (Int.castAddHom ℤ_[p]).prodMap (Int.castAddHom ℤ_[p])

/-- The integral part `Λ ∩ ℤ²` of a subgroup `Λ ⊆ ℤ_p²`. -/
noncomputable def zPart (Λ : AddSubgroup (ℤ_[p] × ℤ_[p])) : AddSubgroup (ℤ × ℤ) :=
  Λ.comap (iota p)

theorem mem_zPart {Λ : AddSubgroup (ℤ_[p] × ℤ_[p])} {v : ℤ × ℤ} :
    v ∈ zPart Λ ↔ iota p v ∈ Λ :=
  Iff.rfl

/-- Every `ℤ_p`-coordinate is congruent to a natural number modulo `p^r`. -/
theorem approx_coord (r : ℕ) (x : ℤ_[p]) :
    ∃ n : ℕ, ∃ c : ℤ_[p], x = (n : ℤ_[p]) + (p : ℤ_[p]) ^ r * c := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  refine ⟨(toZModPow r x).val, ?_⟩
  have hmem : x - ((toZModPow r x).val : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ r} := by
    rw [← ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨c, by linear_combination -hc⟩

/-- Every point of `ℤ_p²` is `ι v + (p^r) y` with `v ∈ ℤ²` and `y ∈ ℤ_p²`. -/
theorem approx_pair (r : ℕ) (x : ℤ_[p] × ℤ_[p]) :
    ∃ v : ℤ × ℤ, ∃ y : ℤ_[p] × ℤ_[p], x = iota p v + (p ^ r) • y := by
  obtain ⟨n1, c1, h1⟩ := approx_coord (p := p) r x.1
  obtain ⟨n2, c2, h2⟩ := approx_coord (p := p) r x.2
  refine ⟨((n1 : ℤ), (n2 : ℤ)), (c1, c2), ?_⟩
  ext
  · simp only [iota, AddMonoidHom.coe_prodMap, Prod.map_apply, Prod.fst_add, Prod.smul_fst,
      Int.coe_castAddHom, Int.cast_natCast]
    rw [h1]; ring_nf
  · simp only [iota, AddMonoidHom.coe_prodMap, Prod.map_apply, Prod.snd_add, Prod.smul_snd,
      Int.coe_castAddHom, Int.cast_natCast]
    rw [h2]; ring_nf

/-- A subgroup of index `p^r` contains `(p^r) • x` for every `x`. -/
theorem pow_smul_mem_of_index {r : ℕ} {Λ : AddSubgroup (ℤ_[p] × ℤ_[p])} (hΛ : Λ.index = p ^ r)
    (x : ℤ_[p] × ℤ_[p]) : (p ^ r) • x ∈ Λ := by
  have h := AddSubgroup.nsmul_index_mem Λ x
  rwa [hΛ] at h

/-- The reduction `ℤ² → (ℤ_p²)/Λ`. -/
noncomputable def mkIota (Λ : AddSubgroup (ℤ_[p] × ℤ_[p])) : ℤ × ℤ →+ (ℤ_[p] × ℤ_[p]) ⧸ Λ :=
  (QuotientAddGroup.mk' Λ).comp (iota p)

theorem ker_mkIota (Λ : AddSubgroup (ℤ_[p] × ℤ_[p])) : (mkIota (p := p) Λ).ker = zPart Λ := by
  ext v
  simp [mkIota, zPart, QuotientAddGroup.eq_zero_iff]

theorem mkIota_surjective {r : ℕ} {Λ : AddSubgroup (ℤ_[p] × ℤ_[p])} (hΛ : Λ.index = p ^ r) :
    Function.Surjective (mkIota (p := p) Λ) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨v, y, hxy⟩ := approx_pair (p := p) r x
  refine ⟨v, ?_⟩
  simp only [mkIota, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
  rw [QuotientAddGroup.eq, hxy]
  have : -iota p v + (iota p v + (p ^ r) • y) = (p ^ r) • y := by abel
  rw [this]
  exact pow_smul_mem_of_index hΛ y

/-- The quotient `ℤ²/(Λ ∩ ℤ²)` is isomorphic to `ℤ_p²/Λ`. -/
noncomputable def quotZPartEquiv {r : ℕ} (Λ : AddSubgroup (ℤ_[p] × ℤ_[p])) (hΛ : Λ.index = p ^ r) :
    (ℤ × ℤ) ⧸ zPart Λ ≃+ (ℤ_[p] × ℤ_[p]) ⧸ Λ :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_mkIota Λ).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (mkIota (p := p) Λ) (mkIota_surjective hΛ))

/-- The index of `Λ ∩ ℤ²` in `ℤ²` equals the index of `Λ` in `ℤ_p²`. -/
theorem index_zPart {r : ℕ} {Λ : AddSubgroup (ℤ_[p] × ℤ_[p])} (hΛ : Λ.index = p ^ r) :
    (zPart Λ).index = p ^ r := by
  rw [← hΛ]
  exact Nat.card_congr (quotZPartEquiv Λ hΛ).toEquiv

/-- `Λ` is determined by `Λ ∩ ℤ²` among subgroups of index `p^r`. -/
theorem zPart_injOn {r : ℕ} {Λ Λ' : AddSubgroup (ℤ_[p] × ℤ_[p])} (hΛ : Λ.index = p ^ r)
    (hΛ' : Λ'.index = p ^ r) (e : zPart Λ = zPart Λ') : Λ = Λ' := by
  have key : ∀ {A B : AddSubgroup (ℤ_[p] × ℤ_[p])}, A.index = p ^ r → B.index = p ^ r →
      zPart A = zPart B → A ≤ B := by
    intro A B hA hB hAB x hx
    obtain ⟨v, y, hxy⟩ := approx_pair (p := p) r x
    have hv : iota p v ∈ A := by
      have h : iota p v = x - (p ^ r) • y := by rw [hxy]; abel
      rw [h]
      exact A.sub_mem hx (pow_smul_mem_of_index hA y)
    have hvB : iota p v ∈ B := by
      have hvz : v ∈ zPart A := hv
      rw [hAB] at hvz
      exact hvz
    rw [hxy]
    exact B.add_mem hvB (pow_smul_mem_of_index hB y)
  exact le_antisymm (key hΛ hΛ' e) (key hΛ' hΛ e.symm)

/-- For an index-`p^r` subgroup, `ℤ_p²/Λ` is cyclic iff `ℤ²/(Λ ∩ ℤ²)` is. -/
theorem isAddCyclic_quot_iff {r : ℕ} {Λ : AddSubgroup (ℤ_[p] × ℤ_[p])} (hΛ : Λ.index = p ^ r) :
    IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ) ↔ IsAddCyclic ((ℤ × ℤ) ⧸ zPart Λ) :=
  ⟨fun _ => isAddCyclic_of_surjective (quotZPartEquiv Λ hΛ).symm.toAddMonoidHom
      (quotZPartEquiv Λ hΛ).symm.surjective,
    fun _ => isAddCyclic_of_surjective (quotZPartEquiv Λ hΛ).toAddMonoidHom
      (quotZPartEquiv Λ hΛ).surjective⟩


/-- Equal subgroups give isomorphic quotients (cyclicity is unchanged). -/
theorem isAddCyclic_quot_congr {G : Type*} [AddCommGroup G] {H K : AddSubgroup G} (h : H = K) :
    IsAddCyclic (G ⧸ H) ↔ IsAddCyclic (G ⧸ K) := by
  subst h
  exact Iff.rfl

/-- For an index-`p^r` subgroup `Λ` with `r ≥ 1`, cyclicity of `ℤ_p²/Λ` is the gcd condition on the
Hermite triple of `Λ ∩ ℤ²`. -/
theorem isAddCyclic_quot_iff_gcd {r : ℕ} {Λ : AddSubgroup (ℤ_[p] × ℤ_[p])}
    (hΛ : Λ.index = p ^ r) {t : ℕ × ℕ × ℕ} (ht : t ∈ hnfData (p ^ r)) (hL : latOf t = zPart Λ) :
    IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ) ↔ Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1 := by
  have hpos : 0 < p ^ r := pow_pos hp.out.pos r
  rw [mem_hnfData hpos] at ht
  have hd : 0 < t.2.2 := Nat.pos_of_ne_zero (by intro h; rw [h, mul_zero] at ht; omega)
  rw [isAddCyclic_quot_iff hΛ, isAddCyclic_quot_congr hL.symm]
  exact LatticeCounts.isAddCyclic_quot_latOf_iff hd

/-- The index-`p^r` subgroups of `ℤ_p²` injectively give Hermite triples of level `p^r`. -/
theorem card_index_le (r : ℕ) (hr : 0 < p ^ r) :
    Nat.card {Λ : AddSubgroup (ℤ_[p] × ℤ_[p]) // Λ.index = p ^ r} ≤ ∑ i ∈ Finset.range (r + 1), p ^ i := by
  classical
  have hnf : ∀ Λ : {Λ : AddSubgroup (ℤ_[p] × ℤ_[p]) // Λ.index = p ^ r},
      ∃ t ∈ hnfData (p ^ r), latOf t = zPart Λ.1 := fun Λ =>
    LatticeCounts.exists_latOf_of_index hr (index_zPart Λ.2)
  let f : {Λ : AddSubgroup (ℤ_[p] × ℤ_[p]) // Λ.index = p ^ r} → {t // t ∈ hnfData (p ^ r)} :=
    fun Λ => ⟨Classical.choose (hnf Λ), (Classical.choose_spec (hnf Λ)).1⟩
  have hf : Function.Injective f := by
    intro Λ Λ' h
    have h' : Classical.choose (hnf Λ) = Classical.choose (hnf Λ') := congrArg Subtype.val h
    have hz : zPart Λ.1 = zPart Λ'.1 := by
      rw [← (Classical.choose_spec (hnf Λ)).2, ← (Classical.choose_spec (hnf Λ')).2, h']
    exact Subtype.ext (zPart_injOn Λ.2 Λ'.2 hz)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard, LatticeCounts.card_hnfData] at this
  exact this

/-- The cyclic index-`p^r` subgroups of `ℤ_p²` inject into the cyclic Hermite triples, so there are
at most `p^r + p^(r-1)` of them (`r ≥ 1`). Equality is the surjectivity obligation. -/
theorem card_cyclic_le {r : ℕ} (hr : 1 ≤ r) :
    Nat.card {Λ : AddSubgroup (ℤ_[p] × ℤ_[p]) // Λ.index = p ^ r ∧
      IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ)} ≤ p ^ r + p ^ (r - 1) := by
  classical
  have hpos : 0 < p ^ r := pow_pos hp.out.pos r
  have hnf : ∀ Λ : {Λ : AddSubgroup (ℤ_[p] × ℤ_[p]) // Λ.index = p ^ r ∧
      IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ)},
      ∃ t ∈ hnfData (p ^ r), latOf t = zPart Λ.1 := fun Λ =>
    LatticeCounts.exists_latOf_of_index hpos (index_zPart Λ.2.1)
  let f : {Λ : AddSubgroup (ℤ_[p] × ℤ_[p]) // Λ.index = p ^ r ∧
      IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ)} → {t // t ∈ cyclicHNF p r} :=
    fun Λ => ⟨Classical.choose (hnf Λ), by
      obtain ⟨ht, hL⟩ := Classical.choose_spec (hnf Λ)
      have hg := (isAddCyclic_quot_iff_gcd (hΛ := Λ.2.1) ht hL).mp Λ.2.2
      unfold cyclicHNF
      exact Finset.mem_filter.mpr ⟨ht, hg⟩⟩
  have hf : Function.Injective f := by
    intro Λ Λ' h
    have h' : Classical.choose (hnf Λ) = Classical.choose (hnf Λ') := congrArg Subtype.val h
    have hz : zPart Λ.1 = zPart Λ'.1 := by
      rw [← (Classical.choose_spec (hnf Λ)).2, ← (Classical.choose_spec (hnf Λ')).2, h']
    exact Subtype.ext (zPart_injOn Λ.2.1 Λ'.2.1 hz)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard, LatticeCounts.card_cyclicHNF hr] at this
  exact this

/-- The subgroup `ℤ_p² ⊆ ℚ_p²`, written as a set of pairs of `p`-adic norm at most one. -/
def Zp2 (p : ℕ) [Fact p.Prime] : Set (ℚ_[p] × ℚ_[p]) :=
  {z | ‖z.1‖ ≤ 1 ∧ ‖z.2‖ ≤ 1}

/-- A translate `c + Z` of a set of measure one has measure one, for any left-invariant measure.
Applied with `Z = ℤ_p²` (`Zp2 p`) and the paper's normalization `μ(ℤ_p²) = 1`, every coset of `ℤ_p²`
in `ℚ_p²` has measure one. Mathlib gives no normalized Haar measure on `ℚ_p²` with `ℤ_p²` as the
normalizing compact, so `μ` and `hn` are hypotheses. -/
theorem coset_measure_one {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    {μ : MeasureTheory.Measure G} [μ.IsAddLeftInvariant] (Z : Set G) (hn : μ Z = 1) (c : G) :
    μ {z | z - c ∈ Z} = 1 := by
  have hset : {z | z - c ∈ Z} = (fun z => -c + z) ⁻¹' Z := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [neg_add_eq_sub, sub_eq_add_neg, add_comm]
  rw [hset, MeasureTheory.measure_preimage_add, hn]

omit hp in
/-- The cyclic and noncyclic Hermite triples partition the triples of level `p^r`. This is the
count-level form of the subtraction in `eq:cyclic-hecke`. -/
theorem card_split {r : ℕ} :
    (LatticeCounts.cyclicHNF p r).card + (LatticeCounts.nonCyclicHNF p r).card =
      (LatticeCounts.hnfData (p ^ r)).card := by
  unfold LatticeCounts.cyclicHNF LatticeCounts.nonCyclicHNF
  exact Finset.card_filter_add_card_filter_not _

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
