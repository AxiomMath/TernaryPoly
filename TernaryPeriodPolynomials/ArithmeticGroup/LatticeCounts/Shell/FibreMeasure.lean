module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Count
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Fibre

@[expose] public section


/-!
# The fibre measure of a cyclic lattice in the shell

Formalized by Claude Haiku 5.5.

For a cyclic `ℤ_p`-lattice `Λ` of index `p^r` (`r ≥ 1`), the set of shell points `z` with
`Λ_z = Λ` has measure `p^r - p^(r-1)` under a left-invariant measure with `μ(ℤ_p²) = 1`.
Route: `Λ_z` is the kernel of the residue form of the primitive pair `shellRes z`
(`pairLat_eq_zForm`); the fibre is a union of `ℤ_p²`-cosets, one for each coset of the shell whose
primitive pair defines `Λ`; the coset count is the fibre count `card_fiber_padic` through the
bijection `shellMap`.
-/

open PadicInt MeasureTheory

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Key identity.** On the shell, `Λ_z` is the kernel of the residue form of the primitive pair
`shellRes z`. -/
theorem pairLat_eq_zForm {r : ℕ} (hr : 1 ≤ r) {z : ℚ_[p] × ℚ_[p]} (hz : z ∈ pairShell p r) :
    (pairLat p z).toAddSubgroup = (zForm p r (shellRes p r hr ⟨z, hz⟩).1).ker := by
  obtain ⟨h1, h2⟩ := norm_scale_of_shell hz
  have ha := scaleZ_coe (p := p) (r := r) h1
  have hb := scaleZ_coe (p := p) (r := r) h2
  rw [pairLat_eq_linForm ha hb,
    zForm_eq_linForm (show toZModPow r (scaleZ p r z.1) = (shellRes p r hr ⟨z, hz⟩).1.1 from rfl)
      (show toZModPow r (scaleZ p r z.2) = (shellRes p r hr ⟨z, hz⟩).1.2 from rfl)]

/-- **Fibre measure.** For a cyclic `ℤ_p`-lattice `Λ` of index `p^r`, the shell points whose
lattice is `Λ` have measure `p^r - p^(r-1)` (`μ(ℤ_p²) = 1`). -/
theorem shell_fibre_measure [MeasurableSpace (ℚ_[p] × ℚ_[p])] [BorelSpace (ℚ_[p] × ℚ_[p])]
    [MeasurableAdd (ℚ_[p] × ℚ_[p])]
    {μ : Measure (ℚ_[p] × ℚ_[p])} [μ.IsAddLeftInvariant] (hn : μ (Zp2 p) = 1)
    {r : ℕ} (hr : 1 ≤ r) {Λ : Submodule ℤ_[p] (ℤ_[p] × ℤ_[p])}
    (hΛ : Λ.toAddSubgroup.index = p ^ r)
    (hc : IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Λ.toAddSubgroup)) :
    μ {z | z ∈ pairShell p r ∧ (pairLat p z).toAddSubgroup = Λ.toAddSubgroup} =
      ((p ^ r - p ^ (r - 1) : ℕ) : ENNReal) := by
  classical
  have hfin : Finite (ShellCos p r) := Finite.of_injective _ (shellMap_bijective hr).1
  have : Fintype (ShellCos p r) := Fintype.ofFinite _
  have hmeas : ∀ q : ShellCos p r, MeasurableSet {y | y - (q.out).1 ∈ Zp2 p} := fun q =>
    (continuous_sub_right _).measurable isClosed_Zp2.measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint fun q : ShellCos p r =>
      {y | y - (q.out).1 ∈ Zp2 p}) := by
    intro q q' hne
    refine Set.disjoint_left.mpr fun y hy hy' => hne ?_
    have h1 : q.out.1 - q'.out.1 ∈ Zp2 p := by
      have := zp2_sub (show y - q'.out.1 ∈ Zp2 p from hy') (show y - q.out.1 ∈ Zp2 p from hy)
      rwa [show y - q'.out.1 - (y - q.out.1) = q.out.1 - q'.out.1 by abel] at this
    calc q = (Quotient.mk (shellSetoid p r) q.out) := (Quotient.out_eq q).symm
      _ = (Quotient.mk (shellSetoid p r) q'.out) := Quotient.sound h1
      _ = q' := Quotient.out_eq q'
  -- The lattice of a coset is the kernel of the residue form of its image under `shellMap`.
  have hK : ∀ q : ShellCos p r,
      (pairLat p q.out.1).toAddSubgroup = (zForm p r (shellMap p r hr q).1).ker := by
    intro q
    have e : shellMap p r hr q = shellRes p r hr q.out := by
      calc shellMap p r hr q = shellMap p r hr (Quotient.mk (shellSetoid p r) q.out) := by
            rw [Quotient.out_eq]
        _ = shellRes p r hr q.out := rfl
    rw [e]
    exact pairLat_eq_zForm hr q.out.2
  have hset : {z | z ∈ pairShell p r ∧ (pairLat p z).toAddSubgroup = Λ.toAddSubgroup} =
      ⋃ q ∈ (Finset.univ.filter
        (fun q : ShellCos p r => (zForm p r (shellMap p r hr q).1).ker = Λ.toAddSubgroup)),
        {y | y - (q.out).1 ∈ Zp2 p} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop]
    constructor
    · rintro ⟨hy, hL⟩
      refine ⟨Quotient.mk (shellSetoid p r) ⟨y, hy⟩, ?_, ?_⟩
      · show (zForm p r (shellRes p r hr ⟨y, hy⟩).1).ker = Λ.toAddSubgroup
        rw [← pairLat_eq_zForm hr hy]
        exact hL
      · exact (shellSetoid p r).iseqv.symm (Quotient.mk_out (s := shellSetoid p r) ⟨y, hy⟩)
    · rintro ⟨q, hq, hy'⟩
      have hy : y ∈ pairShell p r := by
        have := pairShell_add_mem_zp2 hr q.out.2 hy'
        rwa [show q.out.1 + (y - q.out.1) = y by abel] at this
      refine ⟨hy, ?_⟩
      have hpl := ((pairShell_coset_measure hr hn q.out.2).1 y hy').2
      rw [hpl, hK q]
      exact hq
  have hcard : (Finset.univ.filter
      (fun q : ShellCos p r => (zForm p r (shellMap p r hr q).1).ker = Λ.toAddSubgroup)).card =
      p ^ r - p ^ (r - 1) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ (shellMap_bijective hr))
      (fun _ => Iff.rfl))).trans (card_fiber_padic hr hΛ hc)
  rw [hset, measure_biUnion_finset (fun _ _ _ _ hab => hdisj hab) (fun q _ => hmeas q),
    Finset.sum_congr rfl (fun q _ => (pairShell_coset_measure hr hn q.out.2).2),
    Finset.sum_const, nsmul_eq_mul, mul_one, hcard]

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
