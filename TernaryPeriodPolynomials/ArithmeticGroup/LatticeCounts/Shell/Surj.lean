module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Coset

@[expose] public section


/-!
# Every cyclic index-`p^r` lattice is some `Λ_z` with `z` in the shell (O3a)

Formalized by Claude Haiku 5.5.

For `a b : ℤ_p` the form `x ↦ toZModPow r (a x₁ + b x₂)` is `linForm p r a b`. We prove:
* `pairLat_eq_linForm`: if `z = (a/p^r, b/p^r)` then `Λ_z` is the kernel of `linForm p r a b`;
* `isUnit_or_of_linForm_surj`: surjectivity of `linForm` forces a unit coefficient;
* `eq_linForm_of_hom`: every additive map `ℤ_p² → ℤ/p^r` is some `linForm` (so the
  kernel is automatically `ℤ_p`-stable);
* `exists_surj_ker_of_cyclic`: a cyclic quotient of index `p^r` is the kernel of a surjection;
* `exists_pairShell_of_cyclic`: every cyclic additive subgroup of `ℤ_p²` of index `p^r` equals
  `Λ_z` for some `z` in the shell `max(|z₁|_p,|z₂|_p) = p^r`.
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

/-- The form `x ↦ a x₁ + b x₂` on `ℤ_p²`, reduced modulo `p^r`. -/
noncomputable def linForm (p r : ℕ) [Fact p.Prime] (a b : ℤ_[p]) : ℤ_[p] × ℤ_[p] →+ ZMod (p ^ r) where
  toFun x := toZModPow r (a * x.1 + b * x.2)
  map_zero' := by simp
  map_add' := by
    intro x y
    rw [← map_add]
    congr 1
    simp only [Prod.fst_add, Prod.snd_add]
    ring

theorem linForm_apply {p : ℕ} [Fact p.Prime] (r : ℕ) (a b : ℤ_[p]) (x : ℤ_[p] × ℤ_[p]) :
    linForm p r a b x = toZModPow r (a * x.1 + b * x.2) := rfl

/-- `Λ_z` is the kernel of `linForm p r a b` when `a = z₁ p^r` and `b = z₂ p^r`. -/
theorem pairLat_eq_linForm {p : ℕ} [hp : Fact p.Prime] {r : ℕ} {z : ℚ_[p] × ℚ_[p]} {a b : ℤ_[p]}
    (ha : (a : ℚ_[p]) = z.1 * (p : ℚ_[p]) ^ r) (hb : (b : ℚ_[p]) = z.2 * (p : ℚ_[p]) ^ r) :
    (pairLat p z).toAddSubgroup = (linForm p r a b).ker := by
  ext x
  rw [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker, linForm_apply]
  show ‖z.1 * (x.1 : ℚ_[p]) + z.2 * (x.2 : ℚ_[p])‖ ≤ 1 ↔ _
  rw [← RingHom.mem_ker, ker_toZModPow, ← norm_le_pow_iff_mem_span_pow]
  have hpos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by exact_mod_cast hp.out.pos) r
  have hpr : ‖(p : ℚ_[p]) ^ r‖ = ((p : ℝ) ^ r)⁻¹ := by
    rw [norm_pow, Padic.norm_p, inv_pow]
  have hw : ((a * x.1 + b * x.2 : ℤ_[p]) : ℚ_[p]) =
      (p : ℚ_[p]) ^ r * (z.1 * (x.1 : ℚ_[p]) + z.2 * (x.2 : ℚ_[p])) := by
    push_cast
    rw [ha, hb]
    ring
  have hnorm : ‖a * x.1 + b * x.2‖ =
      ((p : ℝ) ^ r)⁻¹ * ‖z.1 * (x.1 : ℚ_[p]) + z.2 * (x.2 : ℚ_[p])‖ := by
    rw [PadicInt.norm_def, hw, norm_mul, hpr]
  rw [hnorm, zpow_neg, zpow_natCast]
  constructor
  · intro h
    exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hpos.le)).trans (mul_one _).le
  · intro h
    exact le_of_mul_le_mul_left (by rw [mul_one]; exact h) (inv_pos.mpr hpos)

/-- Surjectivity of `linForm p r a b` (with `r ≥ 1`) forces a unit coefficient. -/
theorem isUnit_or_of_linForm_surj {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 1 ≤ r)
    {a b : ℤ_[p]} (hs : Function.Surjective (linForm p r a b)) : IsUnit a ∨ IsUnit b := by
  by_contra hcon
  rw [not_or, PadicInt.isUnit_iff, PadicInt.isUnit_iff] at hcon
  obtain ⟨ha, hb⟩ := hcon
  have ha' : ‖a‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one a) ha
  have hb' : ‖b‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one b) hb
  obtain ⟨x, hx⟩ := hs 1
  have hx' : toZModPow r (a * x.1 + b * x.2) = 1 := hx
  have hw : ‖a * x.1 + b * x.2‖ < 1 := by
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans_lt ha'
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans_lt hb'
  have hmem : a * x.1 + b * x.2 - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ r} := by
    rw [← ker_toZModPow, RingHom.mem_ker, map_sub, hx', map_one, sub_self]
  have hw1 : ‖a * x.1 + b * x.2 - 1‖ < 1 := by
    have hle := (norm_le_pow_iff_mem_span_pow (a * x.1 + b * x.2 - 1) r).mpr hmem
    have hlt : (p : ℝ) ^ (-(r : ℤ)) < 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by exact_mod_cast hp.out.one_lt) (by omega))
    exact hle.trans_lt hlt
  have hsum : ‖(1 : ℤ_[p])‖ ≤ max ‖a * x.1 + b * x.2‖ ‖a * x.1 + b * x.2 - 1‖ := by
    have h := IsUltrametricDist.norm_add_le_max (a * x.1 + b * x.2) (-(a * x.1 + b * x.2 - 1))
    rwa [norm_neg, show a * x.1 + b * x.2 + -(a * x.1 + b * x.2 - 1) = 1 by ring] at h
  rw [norm_one] at hsum
  exact absurd hsum (not_le.mpr (max_lt hw hw1))

/-- Every `ℤ_p²`-digit splits as a natural-number digit plus `p^r` times something. -/
theorem decomp_zmod {p : ℕ} [hp : Fact p.Prime] (r : ℕ) (t : ℤ_[p]) :
    ∃ (n : ℕ) (y : ℤ_[p]), t = (n : ℤ_[p]) + (p : ℤ_[p]) ^ r * y := by
  have hmem : t - ((toZModPow r t).val : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ r} := by
    rw [← ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨(toZModPow r t).val, y, by linear_combination -hy⟩

/-- Every `ℤ_p²`-element is a natural combination of the basis plus `p^r` times something. -/
theorem decomp_pair {p : ℕ} [hp : Fact p.Prime] (r : ℕ) (x : ℤ_[p] × ℤ_[p]) :
    ∃ (n1 n2 : ℕ) (y : ℤ_[p] × ℤ_[p]),
      x = n1 • ((1 : ℤ_[p]), (0 : ℤ_[p])) + n2 • ((0 : ℤ_[p]), (1 : ℤ_[p])) + (p ^ r) • y := by
  obtain ⟨n1, y1, h1⟩ := decomp_zmod (p := p) r x.1
  obtain ⟨n2, y2, h2⟩ := decomp_zmod (p := p) r x.2
  refine ⟨n1, n2, (y1, y2), ?_⟩
  ext : 1
  · simp [nsmul_eq_mul]
    linear_combination h1
  · simp [nsmul_eq_mul]
    linear_combination h2

/-- Every additive map `ℤ_p² → ℤ/p^r` is a `linForm`. -/
theorem eq_linForm_of_hom {p : ℕ} [hp : Fact p.Prime] {r : ℕ}
    (φ : ℤ_[p] × ℤ_[p] →+ ZMod (p ^ r)) :
    ∃ a b : ℤ_[p], φ = linForm p r a b := by
  obtain ⟨m1, hm1⟩ := ZMod.intCast_surjective (φ (1, 0))
  obtain ⟨m2, hm2⟩ := ZMod.intCast_surjective (φ (0, 1))
  refine ⟨(m1 : ℤ_[p]), (m2 : ℤ_[p]), AddMonoidHom.ext fun x => ?_⟩
  have h1 : φ (1, 0) = linForm p r (m1 : ℤ_[p]) (m2 : ℤ_[p]) (1, 0) := by
    show φ (1, 0) = toZModPow r ((m1 : ℤ_[p]) * 1 + (m2 : ℤ_[p]) * 0)
    rw [mul_one, mul_zero, add_zero, map_intCast, hm1]
  have h2 : φ (0, 1) = linForm p r (m1 : ℤ_[p]) (m2 : ℤ_[p]) (0, 1) := by
    show φ (0, 1) = toZModPow r ((m1 : ℤ_[p]) * 0 + (m2 : ℤ_[p]) * 1)
    rw [mul_one, mul_zero, zero_add, map_intCast, hm2]
  have hz : ∀ z : ZMod (p ^ r), (p ^ r) • z = 0 := fun z => by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  obtain ⟨n1, n2, y, hx⟩ := decomp_pair (p := p) r x
  rw [hx]
  simp only [map_add, map_nsmul, hz, add_zero, h1, h2]

/-- A cyclic quotient of index `p^r` is the kernel of a surjection onto `ZMod (p^r)`. -/
theorem exists_surj_ker_of_cyclic {p : ℕ} [hp : Fact p.Prime] {G : Type*} [AddCommGroup G]
    {r : ℕ} {L : AddSubgroup G} (hL : L.index = p ^ r) (hc : IsAddCyclic (G ⧸ L)) :
    ∃ φ : G →+ ZMod (p ^ r), Function.Surjective φ ∧ φ.ker = L := by
  have hcard : Nat.card (G ⧸ L) = p ^ r := hL
  have hpos : Nat.card (G ⧸ L) ≠ 0 := by
    rw [hcard]; exact (pow_pos (Fact.out : p.Prime).pos r).ne'
  have : Finite (G ⧸ L) := Nat.finite_of_card_ne_zero hpos
  obtain ⟨g, hg⟩ := (IsAddCyclic.exists_zsmul_surjective :
    ∃ g : G ⧸ L, Function.Surjective (fun n : ℤ => n • g))
  have hord : addOrderOf g ∣ Nat.card (G ⧸ L) := addOrderOf_dvd_natCard g
  rw [hcard] at hord
  have h0 : zmultiplesHom _ g ((p ^ r : ℕ) : ℤ) = 0 := by
    show ((p ^ r : ℕ) : ℤ) • g = 0
    rw [natCast_zsmul]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hord
  let ψ : ZMod (p ^ r) →+ (G ⧸ L) := ZMod.lift (p ^ r) ⟨zmultiplesHom _ g, h0⟩
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨k, hk⟩ := hg z
    refine ⟨(k : ZMod (p ^ r)), ?_⟩
    show ZMod.lift (p ^ r) ⟨zmultiplesHom _ g, h0⟩ (k : ZMod (p ^ r)) = z
    rw [ZMod.lift_coe]
    exact hk
  have hψbij : Function.Bijective ψ :=
    (Nat.bijective_iff_surjective_and_card ψ).mpr ⟨hψsurj, by rw [Nat.card_zmod, hcard]⟩
  let e : ZMod (p ^ r) ≃+ (G ⧸ L) := AddEquiv.ofBijective ψ hψbij
  let φ : G →+ ZMod (p ^ r) := e.symm.toAddMonoidHom.comp (QuotientAddGroup.mk' L)
  have hφsurj : Function.Surjective φ := by
    intro z
    obtain ⟨q, hq⟩ := e.symm.surjective z
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨w, hq⟩
  refine ⟨φ, hφsurj, ?_⟩
  refine AddSubgroup.ext fun w => ?_
  rw [AddMonoidHom.mem_ker]
  show e.symm (QuotientAddGroup.mk w) = 0 ↔ w ∈ L
  rw [map_eq_zero_iff _ e.symm.injective, QuotientAddGroup.eq_zero_iff]

/-- Every cyclic additive subgroup of `ℤ_p²` of index `p^r` (`r ≥ 1`) is `Λ_z` for some `z`
in the shell `max(|z₁|_p,|z₂|_p) = p^r`. -/
theorem exists_pairShell_of_cyclic {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 1 ≤ r)
    {L : AddSubgroup (ℤ_[p] × ℤ_[p])} (hL : L.index = p ^ r)
    (hc : IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ L)) :
    ∃ z ∈ pairShell p r, (pairLat p z).toAddSubgroup = L := by
  obtain ⟨φ, hφs, hker⟩ := exists_surj_ker_of_cyclic (p := p) hL hc
  obtain ⟨a, b, hab⟩ := eq_linForm_of_hom φ
  have hsurj : Function.Surjective (linForm p r a b) := by
    rw [← hab]; exact hφs
  have hunit := isUnit_or_of_linForm_surj hr hsurj
  have hp0 : (p : ℚ_[p]) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hpos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by exact_mod_cast hp.out.pos) r
  have hnorm : ∀ c : ℤ_[p], ‖(c : ℚ_[p]) / (p : ℚ_[p]) ^ r‖ = ‖c‖ * (p : ℝ) ^ r := by
    intro c
    rw [norm_div, norm_pow, Padic.norm_p, inv_pow, div_inv_eq_mul, PadicInt.norm_def]
  have ha : (a : ℚ_[p]) = (a : ℚ_[p]) / (p : ℚ_[p]) ^ r * (p : ℚ_[p]) ^ r :=
    (div_mul_cancel₀ _ hp0).symm
  have hb : (b : ℚ_[p]) = (b : ℚ_[p]) / (p : ℚ_[p]) ^ r * (p : ℚ_[p]) ^ r :=
    (div_mul_cancel₀ _ hp0).symm
  refine ⟨((a : ℚ_[p]) / (p : ℚ_[p]) ^ r, (b : ℚ_[p]) / (p : ℚ_[p]) ^ r), ?_, ?_⟩
  · show max ‖(a : ℚ_[p]) / (p : ℚ_[p]) ^ r‖ ‖(b : ℚ_[p]) / (p : ℚ_[p]) ^ r‖ = (p : ℝ) ^ r
    rw [hnorm a, hnorm b]
    rcases hunit with h | h
    · rw [PadicInt.isUnit_iff.mp h, one_mul]
      exact max_eq_left (mul_le_of_le_one_left hpos.le (PadicInt.norm_le_one b))
    · rw [PadicInt.isUnit_iff.mp h, one_mul]
      exact max_eq_right (mul_le_of_le_one_left hpos.le (PadicInt.norm_le_one a))
  · rw [pairLat_eq_linForm (z := ((a : ℚ_[p]) / (p : ℚ_[p]) ^ r, (b : ℚ_[p]) / (p : ℚ_[p]) ^ r))
      ha hb, ← hab, hker]

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
