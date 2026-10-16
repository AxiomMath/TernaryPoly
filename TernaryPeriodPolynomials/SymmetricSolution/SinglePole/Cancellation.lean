module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.LinearForms
public import Mathlib.Tactic.FieldSimp

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SinglePole

/-- The actual polynomial embedding in its actual fraction field. -/
abbrev embed : Poly →+* Frac := algebraMap Poly Frac

theorem embed_injective : Function.Injective embed := IsFractionRing.injective Poly Frac

@[simp] theorem embed_ne_zero {p : Poly} : embed p ≠ 0 ↔ p ≠ 0 :=
  map_ne_zero_iff embed embed_injective

/-- Clearing the common denominator in one summand, with no localization shorthand. -/
theorem fraction_mul_product {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (d p : ι → Poly) (hd : ∀ i ∈ s, d i ≠ 0) (i : ι) (hi : i ∈ s) :
    (embed (p i) / embed (d i)) * embed (∏ j ∈ s, d j) =
      embed (p i * ∏ j ∈ s.erase i, d j) := by
  rw [← Finset.mul_prod_erase s d hi,map_mul,map_mul]
  have hdi : embed (d i) ≠ 0 := embed_ne_zero.mpr (hd i hi)
  field_simp

/-- Equality to a polynomial forces cancellation of each distinct prime denominator. -/
theorem finite_prime_cancellation {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (d p : ι → Poly) (hprime : ∀ i ∈ s, Prime (d i))
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ d i ∣ d j)
    (q : Poly) (h : (∑ i ∈ s, embed (p i) / embed (d i)) = embed q)
    (i : ι) (hi : i ∈ s) : d i ∣ p i := by
  have hd : ∀ j ∈ s, d j ≠ 0 := fun j hj => (hprime j hj).ne_zero
  have he : (∑ j ∈ s, p j * ∏ k ∈ s.erase j, d k) = q * ∏ j ∈ s, d j := by
    apply embed_injective
    rw [map_sum,map_mul]
    have ht := congrArg (fun x : Frac => x * embed (∏ j ∈ s, d j)) h
    rw [Finset.sum_mul] at ht
    convert ht using 1
    apply Finset.sum_congr rfl
    intro j hj
    exact (fraction_mul_product s d p hd j hj).symm
  have htotal : d i ∣ ∑ j ∈ s, p j * ∏ k ∈ s.erase j, d k := by
    rw [he]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem d hi) q
  have hothers : d i ∣ ∑ j ∈ s.erase i, p j * ∏ k ∈ s.erase j, d k := by
    apply Finset.dvd_sum
    intro j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem d (Finset.mem_erase.mpr ⟨hij,hi⟩)) _
  have hterm : d i ∣ p i * ∏ k ∈ s.erase i, d k := by
    have ht := dvd_sub htotal hothers
    rw [← Finset.sum_erase_add s (fun j => p j * ∏ k ∈ s.erase j, d k) hi] at ht
    simpa only [add_sub_cancel_left] using ht
  have hnot : ¬ d i ∣ ∏ k ∈ s.erase i, d k :=
    (hprime i hi).not_dvd_finsetProd fun j hj =>
      hdistinct i hi j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm
  exact ((hprime i hi).dvd_mul.mp hterm).resolve_right hnot

/-- Distinct actual rational hyperplanes have presentation-independent principal parts. -/
theorem normal_denominator_cancellation (s : Finset Normal) (p : Normal → Poly) (q : Poly)
    (h : (∑ H ∈ s, embed (p H) / embed (denominator H)) = embed q)
    (H : Normal) (hH : H ∈ s) : denominator H ∣ p H := by
  classical
  exact finite_prime_cancellation s denominator p (fun J _ => denominator_prime J)
    (fun J _ K _ hJK hd => hJK ((denominator_dvd_iff J K).mp hd)) q h H hH

end TernaryPoly.SinglePole
