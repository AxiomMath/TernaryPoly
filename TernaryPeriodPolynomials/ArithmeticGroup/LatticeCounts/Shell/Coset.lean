module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Dictionary

@[expose] public section


/-!
# The integral shell and its cosets: obligation O3

Formalized by Claude Haiku 5.5.

For `z = (s,t) ∈ ℚ_p²` put `Λ_z = {(u,v) ∈ ℤ_p² : s u + t v ∈ ℤ_p}` (`pairLat`), and let the shell
`max(|s|_p,|t|_p) = p^r` be `pairShell p r`. The paper claims, for `r ≥ 1`:
* `Λ_z` depends only on the `ℤ_p²`-coset of `z` (`pairLat_add_mem_zp2`);
* the shell is a union of `ℤ_p²`-cosets, each contained in the shell
  (`pairShell_add_mem_zp2`, `pairShell_eq_union_cosets`);
* each coset has measure one, under the explicit normalization `μ(ℤ_p²) = 1` (
  `pairShell_coset_measure`);
* `Λ_z` is a ℤ_p-lattice of index `p^r` with cyclic quotient (`pairLat_index`,
  `isAddCyclic_pairLat`), the cyclic one of the paper's "cyclic lattice".

The O3 obligations:
* O3a: each cyclic `Λ` of index `p^r` is some `Λ_z`, `z` in the shell:
  `Padic.exists_pairShell_of_cyclic` (`LatticeCounts/ShellSurj.lean`).
* O3b: the fibre of `z ↦ Λ_z` over a lattice has `(1-p^{-1})p^r` primitive defining pairs mod
  `p^r`, differing by units: `Padic.card_fiber_padic` and
  `Padic.fibre_units_padic` (`LatticeCounts/ShellFibre.lean`).
* O3c: the number of `ℤ_p²`-cosets in the shell is `p^{2r} - p^{2r-2}`: `Padic.card_shellCos`
  (`LatticeCounts/ShellCount.lean`), and the shell measure under `μ(ℤ_p²) = 1`:
  `Padic.shell_measure` and `Padic.shell_measure_rat` (same file).
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- The shell `max(|s|_p,|t|_p) = p^r` of `ℚ_p²`. -/
def pairShell (p r : ℕ) [Fact p.Prime] : Set (ℚ_[p] × ℚ_[p]) :=
  {z | max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ r}

/-- The lattice `Λ_z = {(u,v) ∈ ℤ_p² : s u + t v ∈ ℤ_p}` of `z = (s,t) ∈ ℚ_p²`. -/
def pairLat (p : ℕ) [Fact p.Prime] (z : ℚ_[p] × ℚ_[p]) : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) where
  carrier := {x | ‖z.1 * (x.1 : ℚ_[p]) + z.2 * (x.2 : ℚ_[p])‖ ≤ 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have e : z.1 * ((a + b).1 : ℚ_[p]) + z.2 * ((a + b).2 : ℚ_[p]) =
        (z.1 * (a.1 : ℚ_[p]) + z.2 * (a.2 : ℚ_[p])) +
          (z.1 * (b.1 : ℚ_[p]) + z.2 * (b.2 : ℚ_[p])) := by
      simp only [Prod.fst_add, Prod.snd_add]
      push_cast
      ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero]
    simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have e : z.1 * ((c • x).1 : ℚ_[p]) + z.2 * ((c • x).2 : ℚ_[p]) =
        (c : ℚ_[p]) * (z.1 * (x.1 : ℚ_[p]) + z.2 * (x.2 : ℚ_[p])) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      push_cast
      ring
    rw [e, norm_mul]
    exact (mul_le_mul (PadicInt.norm_le_one c) hx (norm_nonneg _) zero_le_one).trans (by norm_num)

/-- `Zp2 p` is the coset group `ℤ_p²` inside `ℚ_p²`; this is the membership test. -/
theorem mem_Zp2 {w : ℚ_[p] × ℚ_[p]} : w ∈ Zp2 p ↔ ‖w.1‖ ≤ 1 ∧ ‖w.2‖ ≤ 1 :=
  Iff.rfl

theorem norm_add_le_one_iff {A B : ℚ_[p]} (hB : ‖B‖ ≤ 1) : ‖A + B‖ ≤ 1 ↔ ‖A‖ ≤ 1 := by
  constructor
  · intro h
    have h2 := IsUltrametricDist.norm_add_le_max (A + B) (-B)
    rw [norm_neg, show A + B + -B = A by ring] at h2
    exact h2.trans (max_le h hB)
  · intro h
    exact (IsUltrametricDist.norm_add_le_max A B).trans (max_le h hB)

theorem norm_add_eq_of_one_lt {A B : ℚ_[p]} (hB : ‖B‖ ≤ 1) (hA : 1 < ‖A‖) :
    ‖A + B‖ = ‖A‖ := by
  have h1 : ‖A + B‖ ≤ ‖A‖ :=
    (IsUltrametricDist.norm_add_le_max A B).trans (max_le le_rfl (hB.trans hA.le))
  have h2 : ‖A‖ ≤ max ‖A + B‖ ‖B‖ := by
    have h := IsUltrametricDist.norm_add_le_max (A + B) (-B)
    rw [norm_neg, show A + B + -B = A by ring] at h
    exact h
  rcases le_max_iff.mp h2 with h | h
  · exact le_antisymm h1 h
  · exact absurd (h.trans hB) (not_le.mpr hA)

theorem norm_zp2_mul (w : ℚ_[p] × ℚ_[p]) (hw : w ∈ Zp2 p) (x : ℤ_[p] × ℤ_[p]) :
    ‖w.1 * (x.1 : ℚ_[p]) + w.2 * (x.2 : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨h1, h2⟩ := mem_Zp2.mp hw
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_mul h1 (PadicInt.norm_le_one x.1) (norm_nonneg _) zero_le_one).trans (by norm_num)
  · rw [norm_mul]
    exact (mul_le_mul h2 (PadicInt.norm_le_one x.2) (norm_nonneg _) zero_le_one).trans (by norm_num)

/-- `Λ_z` depends only on the `ℤ_p²`-coset of `z`. -/
theorem pairLat_add_mem_zp2 (z w : ℚ_[p] × ℚ_[p]) (hw : w ∈ Zp2 p) :
    pairLat p (z + w) = pairLat p z := by
  ext x
  show ‖(z.1 + w.1) * (x.1 : ℚ_[p]) + (z.2 + w.2) * (x.2 : ℚ_[p])‖ ≤ 1 ↔
    ‖z.1 * (x.1 : ℚ_[p]) + z.2 * (x.2 : ℚ_[p])‖ ≤ 1
  have e : (z.1 + w.1) * (x.1 : ℚ_[p]) + (z.2 + w.2) * (x.2 : ℚ_[p]) =
      (z.1 * (x.1 : ℚ_[p]) + z.2 * (x.2 : ℚ_[p])) +
        (w.1 * (x.1 : ℚ_[p]) + w.2 * (x.2 : ℚ_[p])) := by ring
  rw [e]
  exact norm_add_le_one_iff (norm_zp2_mul w hw x)

/-- The shell is stable under translation by `ℤ_p²` when `r ≥ 1`. -/
theorem pairShell_add_mem_zp2 {r : ℕ} (hr : 1 ≤ r) {z w : ℚ_[p] × ℚ_[p]}
    (hz : z ∈ pairShell p r) (hw : w ∈ Zp2 p) : z + w ∈ pairShell p r := by
  have hM : (1 : ℝ) < (p : ℝ) ^ r :=
    one_lt_pow₀ (by exact_mod_cast hp.out.one_lt) (by omega)
  obtain ⟨hw1, hw2⟩ := mem_Zp2.mp hw
  have hz' : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ r := hz
  show max ‖z.1 + w.1‖ ‖z.2 + w.2‖ = (p : ℝ) ^ r
  rcases le_or_gt ‖z.1‖ 1 with h1 | h1 <;> rcases le_or_gt ‖z.2‖ 1 with h2 | h2
  · have := max_le h1 h2
    rw [hz'] at this
    linarith
  · have e2 : ‖z.2 + w.2‖ = ‖z.2‖ := norm_add_eq_of_one_lt hw2 h2
    have e1 : ‖z.1 + w.1‖ ≤ 1 := (norm_add_le_one_iff hw1).mpr h1
    have hz2 : ‖z.2‖ = (p : ℝ) ^ r := by
      rw [max_eq_right (h1.trans h2.le)] at hz'
      exact hz'
    rw [e2, hz2, max_eq_right (e1.trans hM.le)]
  · have e1 : ‖z.1 + w.1‖ = ‖z.1‖ := norm_add_eq_of_one_lt hw1 h1
    have e2 : ‖z.2 + w.2‖ ≤ 1 := (norm_add_le_one_iff hw2).mpr h2
    have hz1 : ‖z.1‖ = (p : ℝ) ^ r := by
      rw [max_eq_left (h2.trans h1.le)] at hz'
      exact hz'
    rw [e1, hz1, max_eq_left (e2.trans hM.le)]
  · rw [norm_add_eq_of_one_lt hw1 h1, norm_add_eq_of_one_lt hw2 h2]
    exact hz'

/-- The shell is the union of the `ℤ_p²`-cosets of its points. -/
theorem pairShell_eq_union_cosets (r : ℕ) (hr : 1 ≤ r) :
    pairShell p r = ⋃ z ∈ pairShell p r, {y | y - z ∈ Zp2 p} := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · intro hy
    refine ⟨y, hy, ?_⟩
    simp only [sub_self]
    exact ⟨by simp, by simp⟩
  · rintro ⟨z, hz, hy⟩
    have e : z + (y - z) = y := by abel
    have := pairShell_add_mem_zp2 hr hz hy
    rwa [e] at this

/-- Each coset of `ℤ_p²` through a shell point lies in the shell, carries the lattice `Λ_z`, and
has measure one under the normalization `μ(ℤ_p²) = 1`. -/
theorem pairShell_coset_measure {r : ℕ} (hr : 1 ≤ r)
    [MeasurableSpace (ℚ_[p] × ℚ_[p])] [MeasurableAdd (ℚ_[p] × ℚ_[p])]
    {μ : MeasureTheory.Measure (ℚ_[p] × ℚ_[p])} [μ.IsAddLeftInvariant]
    (hn : μ (Zp2 p) = 1) {z : ℚ_[p] × ℚ_[p]} (hz : z ∈ pairShell p r) :
    (∀ y ∈ {y | y - z ∈ Zp2 p}, y ∈ pairShell p r ∧ pairLat p y = pairLat p z) ∧
      μ {y | y - z ∈ Zp2 p} = 1 := by
  refine ⟨fun y hy => ?_, coset_measure_one (Zp2 p) hn z⟩
  have hy' : y - z ∈ Zp2 p := hy
  have e : z + (y - z) = y := by abel
  constructor
  · have := pairShell_add_mem_zp2 hr hz hy'
    rwa [e] at this
  · have := pairLat_add_mem_zp2 z (y - z) hy'
    rwa [e] at this

/-- For `z` in the shell with `r ≥ 1`, `Λ_z` is the kernel of a surjection `ℤ_p² → ℤ/p^r`
given by a `ℤ_p`-linear form with a unit coefficient. -/
theorem pairLat_eq_ker {r : ℕ} {z : ℚ_[p] × ℚ_[p]} (hz : z ∈ pairShell p r) :
    ∃ Φ : ℤ_[p] × ℤ_[p] →+ ZMod (p ^ r), Function.Surjective Φ ∧
      (pairLat p z).toAddSubgroup = Φ.ker := by
  have hz' : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ r := hz
  have hpos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by exact_mod_cast hp.out.pos) r
  have hpr : ‖(p : ℚ_[p]) ^ r‖ = ((p : ℝ) ^ r)⁻¹ := by
    rw [norm_pow, Padic.norm_p, inv_pow]
  have hscale : ∀ u : ℚ_[p], ‖u‖ ≤ (p : ℝ) ^ r → ‖u * (p : ℚ_[p]) ^ r‖ ≤ 1 := by
    intro u hu
    rw [norm_mul, hpr]
    calc ‖u‖ * ((p : ℝ) ^ r)⁻¹ ≤ (p : ℝ) ^ r * ((p : ℝ) ^ r)⁻¹ :=
          mul_le_mul_of_nonneg_right hu (inv_nonneg.mpr hpos.le)
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  have hA : ‖z.1 * (p : ℚ_[p]) ^ r‖ ≤ 1 := hscale _ ((le_max_left _ _).trans hz'.le)
  have hB : ‖z.2 * (p : ℚ_[p]) ^ r‖ ≤ 1 := hscale _ ((le_max_right _ _).trans hz'.le)
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[p], (a : ℚ_[p]) = z.1 * (p : ℚ_[p]) ^ r := ⟨⟨_, hA⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ_[p], (b : ℚ_[p]) = z.2 * (p : ℚ_[p]) ^ r := ⟨⟨_, hB⟩, rfl⟩
  have hunit : IsUnit a ∨ IsUnit b := by
    rcases max_choice ‖z.1‖ ‖z.2‖ with h | h
    · have h1 : ‖z.1‖ = (p : ℝ) ^ r := by rw [← h]; exact hz'
      left
      rw [PadicInt.isUnit_iff, PadicInt.norm_def, ha, norm_mul, hpr, h1,
        mul_inv_cancel₀ hpos.ne']
    · have h1 : ‖z.2‖ = (p : ℝ) ^ r := by rw [← h]; exact hz'
      right
      rw [PadicInt.isUnit_iff, PadicInt.norm_def, hb, norm_mul, hpr, h1,
        mul_inv_cancel₀ hpos.ne']
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℤ_[p] × ℤ_[p] →+ ZMod (p ^ r),
      ∀ x, Φ x = toZModPow r (a * x.1 + b * x.2) :=
    ⟨AddMonoidHom.mk' (fun x => toZModPow r (a * x.1 + b * x.2)) (by
      intro x y
      rw [← map_add]
      congr 1
      simp only [Prod.fst_add, Prod.snd_add]
      ring), fun x => rfl⟩
  have hiff : ∀ x : ℤ_[p] × ℤ_[p], x ∈ pairLat p z ↔ Φ x = 0 := by
    intro x
    show ‖z.1 * (x.1 : ℚ_[p]) + z.2 * (x.2 : ℚ_[p])‖ ≤ 1 ↔ _
    rw [hΦ, ← RingHom.mem_ker, ker_toZModPow, ← norm_le_pow_iff_mem_span_pow]
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
  have hsurj : Function.Surjective Φ := by
    intro k
    have hk : toZModPow r ((k.val : ℕ) : ℤ_[p]) = k := by
      rw [map_natCast, ZMod.natCast_zmod_val]
    rcases hunit with ⟨u, hu⟩ | ⟨u, hu⟩
    · refine ⟨((↑u⁻¹ : ℤ_[p]) * ((k.val : ℕ) : ℤ_[p]), 0), ?_⟩
      rw [hΦ]
      dsimp only
      rw [mul_zero, add_zero, ← mul_assoc, ← hu, Units.mul_inv, one_mul, hk]
    · refine ⟨(0, (↑u⁻¹ : ℤ_[p]) * ((k.val : ℕ) : ℤ_[p])), ?_⟩
      rw [hΦ]
      dsimp only
      rw [mul_zero, zero_add, ← mul_assoc, ← hu, Units.mul_inv, one_mul, hk]
  refine ⟨Φ, hsurj, ?_⟩
  ext x
  rw [Submodule.mem_toAddSubgroup, hiff x, AddMonoidHom.mem_ker]

/-- The index of `Λ_z` is `p^r` for `z` in the shell. -/
theorem pairLat_index {r : ℕ} {z : ℚ_[p] × ℚ_[p]} (hz : z ∈ pairShell p r) :
    (pairLat p z).toAddSubgroup.index = p ^ r := by
  obtain ⟨Φ, hΦ, hk⟩ := pairLat_eq_ker hz
  rw [hk, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hΦ]
  rw [Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_zmod]

/-- `ℤ_p²/Λ_z` is cyclic for `z` in the shell. -/
theorem isAddCyclic_pairLat {r : ℕ} {z : ℚ_[p] × ℚ_[p]} (hz : z ∈ pairShell p r) :
    IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ (pairLat p z).toAddSubgroup) := by
  obtain ⟨Φ, hΦ, hk⟩ := pairLat_eq_ker hz
  rw [hk]
  exact isAddCyclic_of_surjective (QuotientAddGroup.quotientKerEquivOfSurjective Φ hΦ).symm.toAddMonoidHom
    (QuotientAddGroup.quotientKerEquivOfSurjective Φ hΦ).symm.surjective

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
