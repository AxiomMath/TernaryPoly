module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.FibreMeasure
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Noncyclic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.PermZp

@[expose] public section


/-!
# Residue-form descriptions of the Hermite lattices

Formalized by Claude Haiku 5.5.

For a matrix `M = [[a, 0], [b, d]]` over `ℤ_p` with `a d = p^s`, the column span of `M` is the
kernel of a surjective residue form `ℤ_p² → ℤ/p^s` whenever one of `a, b, d` is a unit.
-/

open PadicInt MeasureTheory
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp (mulLin mulLin_apply)

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

variable {p : ℕ} [hp : Fact p.Prime]

theorem toZModPow_surj_padic (r : ℕ) : Function.Surjective (toZModPow (p := p) r) := by
  intro z
  exact ⟨((z.val : ℕ) : ℤ_[p]), by rw [map_natCast, ZMod.natCast_zmod_val]⟩

theorem mem_span_of_not_isUnit {x : ℤ_[p]} (h : ¬ IsUnit x) :
    x ∈ Ideal.span {(p : ℤ_[p])} := by
  rw [Ideal.mem_span_singleton]
  rw [PadicInt.isUnit_iff] at h
  have hlt : ‖x‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one x) h
  exact (PadicInt.norm_lt_one_iff_dvd x).mp hlt

theorem linForm_eq_zero_iff (r : ℕ) (α β : ℤ_[p]) (y : ℤ_[p] × ℤ_[p]) :
    linForm p r α β y = 0 ↔ (p : ℤ_[p]) ^ r ∣ α * y.1 + β * y.2 := by
  rw [linForm_apply, ← RingHom.mem_ker, ker_toZModPow, Ideal.mem_span_singleton]

/-- A residue form onto `ℤ/p^r` has kernel of index `p^r` with cyclic quotient. -/
theorem index_cyclic_of_surj {r : ℕ} (Φ : ℤ_[p] × ℤ_[p] →+ ZMod (p ^ r))
    (hΦ : Function.Surjective Φ) :
    Φ.ker.index = p ^ r ∧ IsAddCyclic ((ℤ_[p] × ℤ_[p]) ⧸ Φ.ker) := by
  refine ⟨?_, ?_⟩
  · rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hΦ,
      Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_zmod]
  · exact isAddCyclic_of_surjective
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ hΦ).symm.toAddMonoidHom
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ hΦ).symm.surjective

theorem linForm_surj_fst {r : ℕ} {α : ℤ_[p]} (hα : IsUnit α) (β : ℤ_[p]) :
    Function.Surjective (linForm p r α β) := by
  obtain ⟨u, rfl⟩ := hα
  intro z
  obtain ⟨w, hw⟩ := toZModPow_surj_padic (p := p) r z
  refine ⟨(((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * w, 0), ?_⟩
  rw [linForm_apply, ← hw]
  congr 1
  dsimp only
  rw [mul_zero, add_zero, ← mul_assoc, Units.mul_inv, one_mul]

theorem linForm_surj_snd {r : ℕ} {β : ℤ_[p]} (hβ : IsUnit β) (α : ℤ_[p]) :
    Function.Surjective (linForm p r α β) := by
  obtain ⟨u, rfl⟩ := hβ
  intro z
  obtain ⟨w, hw⟩ := toZModPow_surj_padic (p := p) r z
  refine ⟨(0, ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * w), ?_⟩
  rw [linForm_apply, ← hw]
  congr 1
  dsimp only
  rw [mul_zero, zero_add, ← mul_assoc, Units.mul_inv, one_mul]

/-- Case `d` a unit. -/
theorem range_iff_case_d {s : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hM01 : M 0 1 = 0)
    (hdet : M 0 0 * M 1 1 = (p : ℤ_[p]) ^ s) (ud : ℤ_[p]ˣ) (hud : (ud : ℤ_[p]) = M 1 1)
    (y : ℤ_[p] × ℤ_[p]) :
    (∃ x, mulLin M x = y) ↔ linForm p s 1 0 y = 0 := by
  have hA : M 0 0 = (p : ℤ_[p]) ^ s * ((ud⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [← hdet, ← hud, mul_assoc, Units.mul_inv, mul_one]
  rw [linForm_eq_zero_iff, one_mul, zero_mul, add_zero]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨((ud⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * x.1, ?_⟩
    simp only [mulLin_apply, hM01, zero_mul, add_zero]
    rw [hA]
    ring
  · rintro ⟨c, hc⟩
    refine ⟨((ud : ℤ_[p]) * c, ((ud⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (y.2 - M 1 0 * ((ud : ℤ_[p]) * c))), ?_⟩
    ext : 1
    · simp only [mulLin_apply, hM01, zero_mul, add_zero]
      rw [hc, hA]
      linear_combination ((p : ℤ_[p]) ^ s * c) * Units.inv_mul ud
    · simp only [mulLin_apply]
      rw [← hud]
      linear_combination (y.2 - M 1 0 * ((ud : ℤ_[p]) * c)) * Units.mul_inv ud

/-- Case `a` a unit. -/
theorem range_iff_case_a {s : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hM01 : M 0 1 = 0)
    (hdet : M 0 0 * M 1 1 = (p : ℤ_[p]) ^ s) (ua : ℤ_[p]ˣ) (hua : (ua : ℤ_[p]) = M 0 0)
    (y : ℤ_[p] × ℤ_[p]) :
    (∃ x, mulLin M x = y) ↔
      linForm p s (-(M 1 0 * ((ua⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))) 1 y = 0 := by
  have h : (ua : ℤ_[p]) * M 1 1 = (p : ℤ_[p]) ^ s := by rw [hua]; exact hdet
  have hD : M 1 1 = (p : ℤ_[p]) ^ s * ((ua⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    linear_combination ((ua⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * h - M 1 1 * Units.inv_mul ua
  rw [linForm_eq_zero_iff, one_mul]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨((ua⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * x.2, ?_⟩
    simp only [mulLin_apply, hM01, zero_mul, add_zero]
    rw [← hua, hD]
    linear_combination (-(M 1 0 * x.1)) * Units.inv_mul ua
  · rintro ⟨c, hc⟩
    refine ⟨(((ua⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * y.1, (ua : ℤ_[p]) * c), ?_⟩
    ext : 1
    · simp only [mulLin_apply, hM01, zero_mul, add_zero]
      rw [← hua, ← mul_assoc, Units.mul_inv, one_mul]
    · simp only [mulLin_apply]
      rw [hD]
      linear_combination (-1 : ℤ_[p]) * hc + ((p : ℤ_[p]) ^ s * c) * Units.inv_mul ua

/-- Case `b` a unit. -/
theorem range_iff_case_b {s : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hM01 : M 0 1 = 0)
    (hdet : M 0 0 * M 1 1 = (p : ℤ_[p]) ^ s) (ub : ℤ_[p]ˣ) (hub : (ub : ℤ_[p]) = M 1 0)
    (y : ℤ_[p] × ℤ_[p]) :
    (∃ x, mulLin M x = y) ↔ linForm p s (-(M 1 0)) (M 0 0) y = 0 := by
  have hub' : M 1 0 * ((ub⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    rw [← hub]
    exact Units.mul_inv ub
  rw [linForm_eq_zero_iff]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x.2, ?_⟩
    simp only [mulLin_apply, hM01, zero_mul, add_zero]
    linear_combination x.2 * hdet
  · rintro ⟨c, hc⟩
    refine ⟨(((ub⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (y.2 - M 1 1 * c), c), ?_⟩
    ext : 1
    · simp only [mulLin_apply, hM01, zero_mul, add_zero]
      linear_combination ((ub⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * hc
        - (((ub⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * c) * hdet + y.1 * hub'
    · simp only [mulLin_apply]
      linear_combination (y.2 - M 1 1 * c) * hub'

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
