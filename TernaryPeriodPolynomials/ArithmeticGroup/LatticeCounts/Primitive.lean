module

public import Mathlib

@[expose] public section


/-!
# Primitive pairs modulo `p^r` and the unit action

Formalized by Claude Haiku 5.5.
Paper: Appendix C,
(primitive defining pairs modulo `p^r`, `(1-p^{-1})p^r` of them per cyclic lattice, differing by units).

A pair `(x, y) ∈ (ℤ/p^r)²` is primitive when it is not the case that `p` divides both `x.val` and `y.val`,
i.e. when it generates a cyclic subgroup of order `p^r`. The group of units `(ℤ/p^r)ˣ` acts on primitive
pairs by scalar multiplication. We prove:

* `primPairs_card`: there are `p^(2r) - p^(2r-2)` primitive pairs;
* `primUnitAction_free`: the action is free;
* `primOrbit_card`: every orbit has `p^r - p^(r-1) = (1 - p⁻¹) p^r` elements;
* `primOrbit_count`: there are `p^r + p^(r-1)` orbits.
-/

namespace TernaryPeriodPolynomials.Argument.LatticeCounts

open Finset

variable (p : ℕ) [Fact p.Prime]

/-- Primitive pairs modulo `p^r`: pairs not both of whose entries are divisible by `p`. -/
def primPairs (r : ℕ) : Finset (ZMod (p ^ r) × ZMod (p ^ r)) :=
  univ.filter fun v => ¬ (p ∣ v.1.val ∧ p ∣ v.2.val)

/-- The primitive pairs, as a type; the carrier of the unit action. -/
abbrev PrimPt (r : ℕ) := {v // v ∈ primPairs p r}

theorem dvd_val_iff_not_isUnit {r : ℕ} (hr : 0 < r) (z : ZMod (p ^ r)) :
    p ∣ z.val ↔ ¬ IsUnit z := by
  have h := ZMod.isUnit_iff_coprime z.val (p ^ r)
  rw [ZMod.natCast_zmod_val] at h
  rw [h, Nat.coprime_pow_right_iff hr, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out), not_not]

theorem mem_primPairs {r : ℕ} (hr : 0 < r) (v : ZMod (p ^ r) × ZMod (p ^ r)) :
    v ∈ primPairs p r ↔ IsUnit v.1 ∨ IsUnit v.2 := by
  simp only [primPairs, mem_filter, mem_univ, true_and, dvd_val_iff_not_isUnit p hr]
  tauto

theorem dvd_val_mul_unit {r : ℕ} (u : (ZMod (p ^ r))ˣ) (x : ZMod (p ^ r)) :
    p ∣ ((u : ZMod (p ^ r)) * x).val ↔ p ∣ x.val := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    rw [Subsingleton.elim ((u : ZMod (p ^ 0)) * x) x]
  · rw [dvd_val_iff_not_isUnit p hr, dvd_val_iff_not_isUnit p hr, IsUnit.mul_iff]
    simp [u.isUnit]

theorem mem_primPairs_smul {r : ℕ} (u : (ZMod (p ^ r))ˣ) (v : ZMod (p ^ r) × ZMod (p ^ r))
    (hv : v ∈ primPairs p r) :
    ((u : ZMod (p ^ r)) * v.1, (u : ZMod (p ^ r)) * v.2) ∈ primPairs p r := by
  simp only [primPairs, mem_filter, mem_univ, true_and, dvd_val_mul_unit] at hv ⊢
  exact hv

/-- The unit group acts on primitive pairs by scalar multiplication. -/
instance primUnitAction (r : ℕ) : MulAction (ZMod (p ^ r))ˣ (PrimPt p r) where
  smul u v := ⟨((u : ZMod (p ^ r)) * v.1.1, (u : ZMod (p ^ r)) * v.1.2),
    mem_primPairs_smul p u v.1 v.2⟩
  one_smul v := by
    apply Subtype.ext
    change (((1 : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) * v.1.1, ((1 : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) * v.1.2) = v.1
    simp
  mul_smul u w v := by
    apply Subtype.ext
    change (((u * w : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) * v.1.1, ((u * w : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) * v.1.2) =
      ((u : ZMod (p ^ r)) * ((w : ZMod (p ^ r)) * v.1.1), (u : ZMod (p ^ r)) * ((w : ZMod (p ^ r)) * v.1.2))
    simp [mul_assoc]

theorem eq_one_of_mul_eq {M : Type*} [Monoid M] (u : Mˣ) {x : M} (hx : IsUnit x)
    (h : (u : M) * x = x) : u = 1 := by
  obtain ⟨w, rfl⟩ := hx
  apply Units.ext
  have h' : (u : M) * w = 1 * w := by rw [one_mul]; exact h
  simpa using (Units.mul_left_inj w).1 h'


theorem card_nonunit {r : ℕ} (hr : 0 < r) :
    (univ.filter fun z : ZMod (p ^ r) => ¬ IsUnit z).card = p ^ (r - 1) := by
  classical
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (ZMod (p ^ r)))) (fun z => IsUnit z)
  have h2 : (univ.filter fun z : ZMod (p ^ r) => IsUnit z).card = (p ^ r).totient := by
    rw [← ZMod.card_units_eq_totient, ← Fintype.card_subtype]
    apply Fintype.card_congr
    exact { toFun := fun z => z.2.unit
            invFun := fun u => ⟨(u : ZMod (p ^ r)), u.isUnit⟩
            left_inv := fun z => Subtype.ext (IsUnit.unit_spec z.2)
            right_inv := fun u => Units.ext rfl }
  rw [Finset.card_univ, ZMod.card, h2, Nat.totient_prime_pow Fact.out hr] at h1
  have hpow : p ^ r = p ^ (r - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hr]
  have key : p ^ r = p ^ (r - 1) * (p - 1) + p ^ (r - 1) := by
    calc p ^ r = p ^ (r - 1) * p := hpow
      _ = p ^ (r - 1) * ((p - 1) + 1) := by rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
      _ = p ^ (r - 1) * (p - 1) + p ^ (r - 1) := by rw [mul_add, mul_one]
  omega

theorem card_primPairs {r : ℕ} (hr : 0 < r) :
    (primPairs p r).card = p ^ (2 * r) - p ^ (2 * r - 2) := by
  classical
  have hset : primPairs p r = univ.filter fun v : ZMod (p ^ r) × ZMod (p ^ r) => IsUnit v.1 ∨ IsUnit v.2 := by
    ext v
    rw [mem_filter, mem_primPairs p hr v]
    simp
  have h := card_filter_add_card_filter_not (s := (univ : Finset (ZMod (p ^ r) × ZMod (p ^ r))))
    (fun v : ZMod (p ^ r) × ZMod (p ^ r) => IsUnit v.1 ∨ IsUnit v.2)
  have hneg : univ.filter (fun v : ZMod (p ^ r) × ZMod (p ^ r) => ¬ (IsUnit v.1 ∨ IsUnit v.2)) =
      (univ.filter fun z : ZMod (p ^ r) => ¬ IsUnit z) ×ˢ (univ.filter fun z : ZMod (p ^ r) => ¬ IsUnit z) := by
    ext v
    simp [not_or]
  rw [Finset.card_univ, Fintype.card_prod] at h
  simp only [ZMod.card] at h
  rw [hneg, card_product, card_nonunit p hr] at h
  rw [hset]
  have e1 : p ^ (2 * r) = p ^ r * p ^ r := by rw [two_mul, pow_add]
  have e2 : p ^ (2 * r - 2) = p ^ (r - 1) * p ^ (r - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e1, e2]
  omega


/-- The unit action on primitive pairs is free (for `r ≥ 1`). -/
theorem primUnitAction_free {r : ℕ} (hr : 0 < r) (u : (ZMod (p ^ r))ˣ) (v : PrimPt p r)
    (h : u • v = v) : u = 1 := by
  have hv := v.2
  rw [mem_primPairs p hr] at hv
  have h1 : (u : ZMod (p ^ r)) * v.1.1 = v.1.1 := congrArg (fun w => w.1.1) h
  have h2 : (u : ZMod (p ^ r)) * v.1.2 = v.1.2 := congrArg (fun w => w.1.2) h
  rcases hv with hx | hy
  · exact eq_one_of_mul_eq u hx h1
  · exact eq_one_of_mul_eq u hy h2

/-- Every orbit of `(ℤ/p^r)ˣ` on primitive pairs has `p^r - p^(r-1)` elements. -/
theorem primOrbit_card {r : ℕ} (hr : 0 < r) (v : PrimPt p r) :
    Nat.card (MulAction.orbit (ZMod (p ^ r))ˣ v) = p ^ r - p ^ (r - 1) := by
  have e : (ZMod (p ^ r))ˣ ≃ MulAction.orbit (ZMod (p ^ r))ˣ v :=
    Equiv.ofBijective (fun u => (⟨u • v, MulAction.mem_orbit v u⟩ : MulAction.orbit (ZMod (p ^ r))ˣ v))
      ⟨by
        intro a b hab
        have hab' : a • v = b • v := congrArg Subtype.val hab
        have hinv : (b⁻¹ * a) • v = v := by
          rw [mul_smul, hab', ← mul_smul, inv_mul_cancel, one_smul]
        exact (inv_mul_eq_one.1 (primUnitAction_free p hr _ _ hinv)).symm,
       by
        rintro ⟨w, hw⟩
        obtain ⟨u, rfl⟩ := (MulAction.mem_orbit_iff).1 hw
        exact ⟨u, rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Fact.out hr]
  have hpow : p ^ r = p ^ (r - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hr]
  rw [hpow, Nat.mul_sub_one]


/-- The number of orbits of `(ℤ/p^r)ˣ` on primitive pairs is `p^r + p^(r-1)`, the number of points of `P¹(ℤ/p^r)`. -/
theorem primOrbit_count {r : ℕ} (hr : 0 < r) :
    Nat.card (MulAction.orbitRel.Quotient (ZMod (p ^ r))ˣ (PrimPt p r)) = p ^ r + p ^ (r - 1) := by
  classical
  let _ : Fintype (MulAction.orbitRel.Quotient (ZMod (p ^ r))ˣ (PrimPt p r)) := Fintype.ofFinite _
  let _ : ∀ v : PrimPt p r, Fintype (MulAction.stabilizer (ZMod (p ^ r))ˣ v) := fun v => Fintype.ofFinite _
  have hcf := MulAction.card_eq_sum_card_group_div_card_stabilizer (ZMod (p ^ r))ˣ (PrimPt p r)
  have hone : ∀ ω : MulAction.orbitRel.Quotient (ZMod (p ^ r))ˣ (PrimPt p r),
      Fintype.card (ZMod (p ^ r))ˣ / Fintype.card (MulAction.stabilizer (ZMod (p ^ r))ˣ ω.out) =
        Fintype.card (ZMod (p ^ r))ˣ := by
    intro ω
    have h1 : Fintype.card (MulAction.stabilizer (ZMod (p ^ r))ˣ ω.out) = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨1, fun g => Subtype.ext (by
        have := MulAction.mem_stabilizer_iff.mp g.2
        simpa using primUnitAction_free p hr _ _ this)⟩
    rw [h1, Nat.div_one]
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hcf
  have hβ : Fintype.card (PrimPt p r) = p ^ (2 * r) - p ^ (2 * r - 2) := by
    rw [Fintype.card_coe, card_primPairs p hr]
  have hG : Fintype.card (ZMod (p ^ r))ˣ = p ^ r - p ^ (r - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Fact.out hr]
    have hpow : p ^ r = p ^ (r - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hr]
    rw [hpow, Nat.mul_sub_one]
  have hq : p ^ (r - 1) < p ^ r := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
  have e1 : p ^ (2 * r) = p ^ r * p ^ r := by rw [two_mul, pow_add]
  have e2 : p ^ (2 * r - 2) = p ^ (r - 1) * p ^ (r - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hβ, hG, e1, e2, Nat.mul_self_sub_mul_self_eq] at hcf
  rw [Nat.card_eq_fintype_card]
  have hpos : 0 < p ^ r - p ^ (r - 1) := by omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← hcf]


/-- The rational form `(1 - p⁻¹) p^r` of the orbit size, as used in the paper. -/
theorem primOrbit_card_rat {r : ℕ} (hr : 0 < r) (v : PrimPt p r) :
    ((Nat.card (MulAction.orbit (ZMod (p ^ r))ˣ v) : ℕ) : ℚ) = (1 - (p : ℚ)⁻¹) * (p : ℚ) ^ r := by
  have hq : p ^ (r - 1) ≤ p ^ r := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  have hpow : (p : ℚ) ^ r = (p : ℚ) ^ (r - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hr]
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rw [primOrbit_card p hr v, Nat.cast_sub hq]
  push_cast
  rw [hpow]
  field_simp


/-- The primitive pairs as a finite type: `Fintype.card = p^(2r) - p^(2r-2)`. -/
theorem card_primPt {r : ℕ} (hr : 0 < r) :
    Fintype.card (PrimPt p r) = p ^ (2 * r) - p ^ (2 * r - 2) := by
  rw [Fintype.card_coe, card_primPairs p hr]

end TernaryPeriodPolynomials.Argument.LatticeCounts
