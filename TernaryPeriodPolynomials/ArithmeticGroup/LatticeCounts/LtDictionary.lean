module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LtCases
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.CyclicZp
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.PermZp

@[expose] public section


/-!
# The Hermite lattices `L_t` of the cyclic shell: the dictionary

Formalized by Claude Haiku 5.5.

For a Hermite triple `t = (a, b, d)` of level `p^s` the lattice `L_t` is the column span of the
matrix `Mz t = [[a, 0], [b, d]]` in `ℤ_p²`. If `t` is cyclic (`mem_cyclicHNF_iff`), one of
`a, b, d` is a unit, and in each case `L_t` is the kernel of a surjective residue form
`ℤ_p² → ℤ/p^s` (the case lemmas are in `LtCases`). Hence `L_t` has index `p^s` and cyclic
quotient (`hermLat_index_cyclic`).
-/

open PadicInt MeasureTheory
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp
  (Mz mulLin mulLin_apply Mz_det)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeCyclicZp (mem_cyclicHNF_iff)
open TernaryPeriodPolynomials.Argument.LatticeCounts (cyclicHNF hnfData mem_hnfData)

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- The lattice `L_t` of a Hermite triple: the column span of `Mz t` in `ℤ_p²`. -/
noncomputable def hermLat (p : ℕ) [Fact p.Prime] (t : ℕ × ℕ × ℕ) :
    Submodule ℤ_[p] (ℤ_[p] × ℤ_[p]) :=
  LinearMap.range (mulLin (Mz (q := p) t))

/-- **Dictionary.** For a cyclic Hermite triple of level `p^s`, `L_t` is the kernel of a surjective
residue form `ℤ_p² → ℤ/p^s`. -/
theorem hermLat_eq_ker {s : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF p s) :
    ∃ Φ : ℤ_[p] × ℤ_[p] →+ ZMod (p ^ s), Function.Surjective Φ ∧
      (hermLat p t).toAddSubgroup = Φ.ker := by
  have hmem : t ∈ hnfData (p ^ s) := (Finset.mem_filter.mp ht).1
  have hcyc := (mem_cyclicHNF_iff (q := p) (r := s) hp.out t hmem).1 ht
  obtain ⟨-, hdet0, -⟩ := (mem_hnfData (pow_pos hp.out.pos s) t).1 hmem
  have hM01 : (Mz (q := p) t) 0 1 = 0 := by simp [Mz]
  have hdet : (Mz (q := p) t) 0 0 * (Mz (q := p) t) 1 1 = (p : ℤ_[p]) ^ s := by
    have h := Mz_det (q := p) t
    rw [Matrix.det_fin_two, hM01, zero_mul, sub_zero, hdet0, Nat.cast_pow] at h
    exact h
  have hU : IsUnit (Mz (q := p) t 0 0) ∨ IsUnit (Mz (q := p) t 1 0) ∨
      IsUnit (Mz (q := p) t 1 1) := by
    by_contra hcon
    rw [not_or, not_or] at hcon
    obtain ⟨ha, hb, hd⟩ := hcon
    apply hcyc
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using mem_span_of_not_isUnit ha
    · simp [Mz]
    · simpa using mem_span_of_not_isUnit hb
    · simpa using mem_span_of_not_isUnit hd
  rcases hU with ha | hb | hd
  · obtain ⟨ua, hua⟩ := ha
    refine ⟨linForm p s (-(Mz (q := p) t 1 0 * ((ua⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))) 1,
      linForm_surj_snd isUnit_one _, ?_⟩
    ext y
    rw [Submodule.mem_toAddSubgroup, hermLat, LinearMap.mem_range, AddMonoidHom.mem_ker]
    exact range_iff_case_a (Mz (q := p) t) hM01 hdet ua hua y
  · obtain ⟨ub, hub⟩ := hb
    refine ⟨linForm p s (-(Mz (q := p) t 1 0)) (Mz (q := p) t 0 0),
      linForm_surj_fst (show IsUnit (Mz (q := p) t 1 0) from ⟨ub, hub⟩).neg _, ?_⟩
    ext y
    rw [Submodule.mem_toAddSubgroup, hermLat, LinearMap.mem_range, AddMonoidHom.mem_ker]
    exact range_iff_case_b (Mz (q := p) t) hM01 hdet ub hub y
  · obtain ⟨ud, hud⟩ := hd
    refine ⟨linForm p s 1 0, linForm_surj_fst isUnit_one 0, ?_⟩
    ext y
    rw [Submodule.mem_toAddSubgroup, hermLat, LinearMap.mem_range, AddMonoidHom.mem_ker]
    exact range_iff_case_d (Mz (q := p) t) hM01 hdet ud hud y

/-- **Index and cyclicity of `L_t`.** For a cyclic Hermite triple of level `p^s`, `L_t` has index
`p^s` in `ℤ_p²` and `ℤ_p²/L_t` is cyclic. -/
theorem hermLat_index_cyclic {s : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF p s) :
    (hermLat p t).toAddSubgroup.index = p ^ s ∧
      IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ (hermLat p t).toAddSubgroup) := by
  obtain ⟨Φ, hΦ, hk⟩ := hermLat_eq_ker ht
  rw [hk]
  exact index_cyclic_of_surj Φ hΦ

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
