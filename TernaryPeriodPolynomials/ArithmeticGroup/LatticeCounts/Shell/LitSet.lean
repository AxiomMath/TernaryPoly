module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Count
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LtInj
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LtSurj
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.HermiteCount

@[expose] public section


/-!
# The shell of valuation `r` as a disjoint union of Hermite fibres

Formalized by Claude Haiku 5.5.

The shell `pairShell p r` (`r ≥ 1`) and the lattice map `z ↦ pairLat p z` are invariant under
translation by `ℤ_p²`, which is open. So every invariant set is open, hence measurable. The
shell is the disjoint union, over the cyclic Hermite triples `t` of level `p^r`, of the fibres
`shellFibre p r t = {z ∈ shell | pairLat z = hermLat t}`.
-/

open MeasureTheory

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitSet

open TernaryPeriodPolynomials.Argument.LatticeCounts (cyclicHNF hnfData)
open TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

variable {p : ℕ} [hp : Fact p.Prime]

theorem isOpen_zp2 : IsOpen (Zp2 p) := by
  have e : Zp2 p = Metric.closedBall (0 : ℚ_[p]) 1 ×ˢ Metric.closedBall (0 : ℚ_[p]) 1 := by
    ext z
    simp [Zp2]
  rw [e]
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).prod
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero)

/-- A set invariant under translation by `ℤ_p²` is open. -/
theorem isOpen_of_zp2_inv {S : Set (ℚ_[p] × ℚ_[p])}
    (hS : ∀ z w : ℚ_[p] × ℚ_[p], w ∈ Zp2 p → (z ∈ S ↔ z + w ∈ S)) : IsOpen S := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hT : IsOpen ((fun y => y - z) ⁻¹' Zp2 p) :=
    (isOpen_zp2 (p := p)).preimage (continuous_sub_right z)
  refine Filter.mem_of_superset (hT.mem_nhds ?_) ?_
  · show z - z ∈ Zp2 p
    rw [sub_self]
    exact zp2_zero
  · intro y hy
    have hy' : y - z ∈ Zp2 p := hy
    have := (hS z (y - z) hy').1 hz
    simpa using this

theorem norm_add_zp2_le {N : ℝ} {a w : ℚ_[p]} (hN : 1 < N) (hw : ‖w‖ ≤ 1) (ha : ‖a‖ ≤ N) :
    ‖a + w‖ ≤ N :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (hw.trans hN.le))

theorem norm_add_zp2_eq {N : ℝ} {a w : ℚ_[p]} (hN : 1 < N) (hw : ‖w‖ ≤ 1) (ha : ‖a‖ = N) :
    ‖a + w‖ = N := by
  have hne : ‖a‖ ≠ ‖w‖ := by
    rw [ha]
    exact (lt_of_le_of_lt hw hN).ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, ha, max_eq_left (hw.trans hN.le)]

/-- Translation by `ℤ_p²` preserves the shell of valuation `r ≥ 1`. -/
theorem pairShell_add_zp2 {r : ℕ} (hr : 1 ≤ r) {z w : ℚ_[p] × ℚ_[p]} (hz : z ∈ pairShell p r)
    (hw : w ∈ Zp2 p) : z + w ∈ pairShell p r := by
  have hN : (1 : ℝ) < (p : ℝ) ^ r := one_lt_pow₀ (by exact_mod_cast hp.out.one_lt) (by omega)
  obtain ⟨hw1, hw2⟩ := hw
  have hz' : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ r := hz
  change max ‖z.1 + w.1‖ ‖z.2 + w.2‖ = (p : ℝ) ^ r
  apply le_antisymm
  · exact max_le (norm_add_zp2_le hN hw1 ((le_max_left _ _).trans hz'.le))
      (norm_add_zp2_le hN hw2 ((le_max_right _ _).trans hz'.le))
  · rcases max_choice ‖z.1‖ ‖z.2‖ with h | h
    · have ha : ‖z.1‖ = (p : ℝ) ^ r := h.symm.trans hz'
      exact le_max_of_le_left (norm_add_zp2_eq hN hw1 ha).ge
    · have ha : ‖z.2‖ = (p : ℝ) ^ r := h.symm.trans hz'
      exact le_max_of_le_right (norm_add_zp2_eq hN hw2 ha).ge

theorem pairShell_zp2_iff {r : ℕ} (hr : 1 ≤ r) {z w : ℚ_[p] × ℚ_[p]} (hw : w ∈ Zp2 p) :
    z ∈ pairShell p r ↔ z + w ∈ pairShell p r :=
  ⟨fun hz => pairShell_add_zp2 hr hz hw, fun hz => by
    have := pairShell_add_zp2 hr hz (zp2_neg hw)
    simpa using this⟩

theorem isOpen_pairShell {r : ℕ} (hr : 1 ≤ r) : IsOpen (pairShell p r) :=
  isOpen_of_zp2_inv fun _ _ hw => pairShell_zp2_iff hr hw

/-- The fibre of the Hermite triple `t` in the shell of valuation `r`: the shell points whose
lattice is `hermLat p t`. -/
def shellFibre (p r : ℕ) [Fact p.Prime] (t : ℕ × ℕ × ℕ) : Set (ℚ_[p] × ℚ_[p]) :=
  {z | z ∈ pairShell p r ∧ (pairLat p z).toAddSubgroup = (hermLat p t).toAddSubgroup}

theorem isOpen_shellFibre {r : ℕ} (hr : 1 ≤ r) (t : ℕ × ℕ × ℕ) : IsOpen (shellFibre p r t) := by
  refine isOpen_of_zp2_inv fun z w hw => ?_
  show (z ∈ pairShell p r ∧ (pairLat p z).toAddSubgroup = (hermLat p t).toAddSubgroup) ↔
    (z + w ∈ pairShell p r ∧ (pairLat p (z + w)).toAddSubgroup = (hermLat p t).toAddSubgroup)
  rw [pairLat_add_mem_zp2 z w hw]
  exact and_congr_left' (pairShell_zp2_iff hr hw)

omit hp in
theorem mem_hnfData_of_cyclic {r : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF p r) :
    t ∈ hnfData (p ^ r) :=
  (Finset.mem_filter.mp ht).1

theorem exists_shellFibre {r : ℕ} {z : ℚ_[p] × ℚ_[p]} (hz : z ∈ pairShell p r) :
    ∃ t ∈ cyclicHNF p r, z ∈ shellFibre p r t := by
  obtain ⟨t, ht, heq⟩ := exists_cyclicHNF_hermLat (pairLat_index hz) (isAddCyclic_pairLat hz)
  refine ⟨t, ht, ?_⟩
  unfold shellFibre
  exact ⟨hz, by rw [heq]⟩

theorem shellFibre_unique {r : ℕ} {t t' : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF p r)
    (ht' : t' ∈ cyclicHNF p r) {z : ℚ_[p] × ℚ_[p]} (hz : z ∈ shellFibre p r t)
    (hz' : z ∈ shellFibre p r t') : t = t' := by
  have h1 : (pairLat p z).toAddSubgroup = (hermLat p t).toAddSubgroup := hz.2
  have h2 : (pairLat p z).toAddSubgroup = (hermLat p t').toAddSubgroup := hz'.2
  have heq : hermLat p t = hermLat p t' :=
    (Submodule.toAddSubgroup_inj _ _).1 (h1.symm.trans h2)
  exact hermLat_inj (mem_hnfData_of_cyclic ht) (mem_hnfData_of_cyclic ht') heq

theorem shellFibre_sub {r : ℕ} (t : ℕ × ℕ × ℕ) : shellFibre p r t ⊆ pairShell p r :=
  fun _ hz => hz.1

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitSet
