module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Surjective
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.Functional
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Surj

@[expose] public section


/-!
# The fibre of `z ↦ Λ_z` over a cyclic lattice: obligation O3b

Formalized by Claude Haiku 5.5.

For a residue pair `v = (v₁, v₂) ∈ (ℤ/p^r)²` let `zForm p r v : ℤ_p² →+ ℤ/p^r`,
`x ↦ v₁ x₁ + v₂ x₂` (with `x_i` reduced). Then:
* `ker_zForm_eq_latOfZ`: for primitive `v`, the kernel of `zForm v` is the `ℤ_p`-lattice
  `latOfZ (lamST v)` attached to the integral lattice `lamST v ⊆ ℤ²` (`PadicSurjective`);
* `card_fiber_padic`: for a cyclic `ℤ_p`-lattice `Λ` of index `p^r`, the primitive residue
  pairs `v` with `ker (zForm v) = Λ` number `p^r - p^(r-1) = (1 - p⁻¹) p^r`;
* `fibre_units_padic`: any two such pairs differ by a unit of `ℤ/p^r`.
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

/-- The residue form `x ↦ v₁ x₁ + v₂ x₂` on `ℤ_p²`, with values in `ℤ/p^r`. -/
noncomputable def zForm (p r : ℕ) [Fact p.Prime] (v : ZMod (p ^ r) × ZMod (p ^ r)) :
    ℤ_[p] × ℤ_[p] →+ ZMod (p ^ r) :=
  AddMonoidHom.mk' (fun x => v.1 * toZModPow r x.1 + v.2 * toZModPow r x.2) (fun a b => by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring)

theorem zForm_apply {p : ℕ} [Fact p.Prime] {r : ℕ} (v : ZMod (p ^ r) × ZMod (p ^ r))
    (x : ℤ_[p] × ℤ_[p]) :
    zForm p r v x = v.1 * toZModPow r x.1 + v.2 * toZModPow r x.2 := rfl

/-- The residue form is the linear form `linForm a b` when `a, b` lift the coefficients. -/
theorem zForm_eq_linForm {p : ℕ} [Fact p.Prime] {r : ℕ} {v : ZMod (p ^ r) × ZMod (p ^ r)}
    {a b : ℤ_[p]} (ha : toZModPow r a = v.1) (hb : toZModPow r b = v.2) :
    zForm p r v = linForm p r a b := by
  refine AddMonoidHom.ext fun x => ?_
  rw [zForm_apply, linForm_apply, map_add, map_mul, map_mul, ha, hb]

/-- For a primitive residue pair `v`, the kernel of `zForm v` is the `ℤ_p`-lattice attached to
the integral lattice `lamST v`. -/
theorem ker_zForm_eq_latOfZ {p : ℕ} [hp : Fact p.Prime] {r : ℕ}
    (v : ZMod (p ^ r) × ZMod (p ^ r)) :
    (zForm p r v).ker = (latOfZ p r (lamST p r v.1 v.2)).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup]
  show v.1 * toZModPow r x.1 + v.2 * toZModPow r x.2 = 0 ↔
    redP (p := p) r x ∈ (lamST p r v.1 v.2).map (redZ p r)
  rw [AddSubgroup.mem_map]
  constructor
  · intro h
    obtain ⟨k1, hk1⟩ := ZMod.intCast_surjective (toZModPow r x.1)
    obtain ⟨k2, hk2⟩ := ZMod.intCast_surjective (toZModPow r x.2)
    refine ⟨(k1, k2), ?_, ?_⟩
    · rw [mem_lamST]
      show ((k1 : ℤ) : ZMod (p ^ r)) * v.1 + ((k2 : ℤ) : ZMod (p ^ r)) * v.2 = 0
      rw [hk1, hk2]
      linear_combination h
    · show (((k1 : ℤ) : ZMod (p ^ r)), ((k2 : ℤ) : ZMod (p ^ r))) = redP (p := p) r x
      rw [hk1, hk2]
      rfl
  · rintro ⟨w, hw, hwx⟩
    rw [mem_lamST] at hw
    have e1 : ((w.1 : ℤ) : ZMod (p ^ r)) = toZModPow r x.1 := congrArg Prod.fst hwx
    have e2 : ((w.2 : ℤ) : ZMod (p ^ r)) = toZModPow r x.2 := congrArg Prod.snd hwx
    rw [← e1, ← e2]
    linear_combination hw

/-- The fibre criterion: for a primitive residue pair `v` and a cyclic lattice `Λ` of index
`p^r`, `ker (zForm v) = Λ` iff `lamST v = zPart Λ`. -/
theorem ker_zForm_iff_lamST {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 1 ≤ r)
    {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])} (hΛ : Λ.toAddSubgroup.index = p ^ r)
    (v : PrimPt p r) :
    (zForm p r v.1).ker = Λ.toAddSubgroup ↔ lamST p r v.1.1 v.1.2 = zPart Λ.toAddSubgroup := by
  have hvst : IsUnit v.1.1 ∨ IsUnit v.1.2 := (mem_primPairs p (by omega) _).mp v.2
  have hidx : (lamST p r v.1.1 v.1.2).index = p ^ r := (index_and_cyclic_lamST hvst).1
  rw [ker_zForm_eq_latOfZ]
  constructor
  · intro h
    have h' := congrArg zPart h
    rw [zPart_latOfZ hidx] at h'
    exact h'
  · intro h
    rw [h, latOfZ_zPart hΛ]

/-- **O3b, card.** For a cyclic `ℤ_p`-lattice `Λ` of index `p^r`, the primitive residue pairs
defining it, `ker (zForm v) = Λ`, number `p^r - p^(r-1)`. -/
theorem card_fiber_padic {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 1 ≤ r)
    {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])} (hΛ : Λ.toAddSubgroup.index = p ^ r)
    (hc : IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)) :
    Nat.card {v : PrimPt p r // (zForm p r v.1).ker = Λ.toAddSubgroup} = p ^ r - p ^ (r - 1) := by
  have hr0 : 0 < r := hr
  have hL : (zPart Λ.toAddSubgroup).index = p ^ r := index_zPart hΛ
  have hLc : IsAddCyclic ((ℤ × ℤ) ⧸ zPart Λ.toAddSubgroup) := (isAddCyclic_quot_iff hΛ).mp hc
  exact (Nat.card_congr (Equiv.subtypeEquivRight
    (fun v => ker_zForm_iff_lamST hr hΛ v))).trans (card_fiber_lamST hr0 hL hLc)

/-- **O3b, units.** Two primitive residue pairs defining the same cyclic lattice differ by a
unit of `ℤ/p^r`. -/
theorem fibre_units_padic {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 1 ≤ r)
    {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])} (hΛ : Λ.toAddSubgroup.index = p ^ r)
    (v w : PrimPt p r) (hv : (zForm p r v.1).ker = Λ.toAddSubgroup)
    (hw : (zForm p r w.1).ker = Λ.toAddSubgroup) :
    ∃ u : (ZMod (p ^ r))ˣ, u • v = w := by
  have hlam : lamST p r v.1.1 v.1.2 = lamST p r w.1.1 w.1.2 :=
    ((ker_zForm_iff_lamST hr hΛ v).mp hv).trans ((ker_zForm_iff_lamST hr hΛ w).mp hw).symm
  have hvst : IsUnit v.1.1 ∨ IsUnit v.1.2 := (mem_primPairs p (by omega) _).mp v.2
  have hwst : IsUnit w.1.1 ∨ IsUnit w.1.2 := (mem_primPairs p (by omega) _).mp w.2
  obtain ⟨u, hu, h1, h2⟩ := (lamST_eq_iff hvst hwst).mp hlam
  refine ⟨hu.unit, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change (hu.unit : ZMod (p ^ r)) * v.1.1 = w.1.1
    rw [IsUnit.unit_spec]; exact h1.symm
  · change (hu.unit : ZMod (p ^ r)) * v.1.2 = w.1.2
    rw [IsUnit.unit_spec]; exact h2.symm

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
