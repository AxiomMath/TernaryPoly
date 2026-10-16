module

public import Mathlib
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.Cyclic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Primitive

@[expose] public section


/-!
# The lattices `Λ_{s,t}` of primitive pairs modulo `p^r`

Formalized by Claude Haiku 5.5.
Paper: Appendix C,
(`Λ_{s,t}` for a primitive defining pair, `(1 - p⁻¹) p^r` primitive pairs per cyclic lattice,
differing by units).

For `s t : ZMod (p^r)` the functional `(u, v) ↦ u s + v t` on `ℤ²` has kernel
`Λ_{s,t} = {(u, v) : u s + v t = 0}`. We prove:

* `isUnit_or_of_phiST_surjective`: surjectivity of the functional forces `IsUnit s ∨ IsUnit t`;
* `phiST_surjective_of_isUnit`: the converse, so primitive pairs are exactly the surjective ones;
* `index_lamST`, `isAddCyclic_quot_lamST`: for primitive `(s, t)`, `Λ_{s,t}` has index `p^r` and cyclic quotient;
* `exists_lamST_of_cyclic`: every cyclic sublattice of index `p^r` is some `Λ_{s,t}` with `(s, t)` primitive;
* `lamST_eq_iff`: for primitive pairs, `Λ_{s,t} = Λ_{s',t'}` iff `(s', t') = u (s, t)` for a unit `u`;
* `card_fiber_lamST`: the primitive pairs defining a given cyclic lattice form one unit orbit, of size
  `p^r - p^(r-1) = (1 - p⁻¹) p^r`.
-/

namespace TernaryPeriodPolynomials.Argument.LatticeCounts

/-- The functional `(u, v) ↦ u s + v t` from `ℤ²` to `ZMod (p^r)`. -/
def phiST (p r : ℕ) (s t : ZMod (p ^ r)) : (ℤ × ℤ) →+ ZMod (p ^ r) where
  toFun w := (w.1 : ZMod (p ^ r)) * s + (w.2 : ZMod (p ^ r)) * t
  map_zero' := by simp
  map_add' := by
    intro x y
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring

/-- The lattice `Λ_{s,t} = {(u, v) ∈ ℤ² : u s + v t = 0}`. -/
def lamST (p r : ℕ) (s t : ZMod (p ^ r)) : AddSubgroup (ℤ × ℤ) := (phiST p r s t).ker

theorem phiST_apply (p r : ℕ) (s t : ZMod (p ^ r)) (w : ℤ × ℤ) :
    phiST p r s t w = (w.1 : ZMod (p ^ r)) * s + (w.2 : ZMod (p ^ r)) * t := rfl

theorem mem_lamST {p r : ℕ} {s t : ZMod (p ^ r)} (w : ℤ × ℤ) :
    w ∈ lamST p r s t ↔ (w.1 : ZMod (p ^ r)) * s + (w.2 : ZMod (p ^ r)) * t = 0 := Iff.rfl

/-- A unit coordinate makes the functional surjective. -/
theorem phiST_surjective_of_isUnit {p r : ℕ} {s t : ZMod (p ^ r)} (h : IsUnit s ∨ IsUnit t) :
    Function.Surjective (phiST p r s t) := by
  intro z
  rcases h with hs | ht
  · obtain ⟨σ, hσ⟩ := hs.exists_right_inv
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (z * σ)
    refine ⟨((k : ℤ), (0 : ℤ)), ?_⟩
    show (k : ZMod (p ^ r)) * s + ((0 : ℤ) : ZMod (p ^ r)) * t = z
    rw [hk]
    simp only [Int.cast_zero, zero_mul, add_zero]
    linear_combination z * hσ
  · obtain ⟨σ, hσ⟩ := ht.exists_right_inv
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (z * σ)
    refine ⟨((0 : ℤ), (k : ℤ)), ?_⟩
    show ((0 : ℤ) : ZMod (p ^ r)) * s + (k : ZMod (p ^ r)) * t = z
    rw [hk]
    simp only [Int.cast_zero, zero_mul, zero_add]
    linear_combination z * hσ

/-- Surjectivity of the functional forces a unit coordinate, for `r ≥ 1`. -/
theorem isUnit_or_of_phiST_surjective {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r)
    {s t : ZMod (p ^ r)} (hsurj : Function.Surjective (phiST p r s t)) :
    IsUnit s ∨ IsUnit t := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hs, ht⟩ := hcon
  have hdvd : p ∣ p ^ r := dvd_pow_self p hr.ne'
  have hcz : ∀ z : ZMod (p ^ r), ¬ IsUnit z → ZMod.castHom hdvd (ZMod p) z = 0 := by
    intro z hz
    have hv : p ∣ z.val := (dvd_val_iff_not_isUnit p hr z).mpr hz
    have hc : ZMod.castHom hdvd (ZMod p) z = ((z.val : ℕ) : ZMod p) := by
      simp only [ZMod.castHom_apply, ZMod.natCast_val]
    rw [hc, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natCast_dvd_natCast.mpr hv
  obtain ⟨w, hw⟩ := hsurj 1
  have hw' : (w.1 : ZMod (p ^ r)) * s + (w.2 : ZMod (p ^ r)) * t = 1 := hw
  have hc1 := congrArg (ZMod.castHom hdvd (ZMod p)) hw'
  rw [map_add, map_mul, map_mul, hcz s hs, hcz t ht, mul_zero, mul_zero, add_zero, map_one] at hc1
  exact zero_ne_one hc1

/-- The index of `Λ_{s,t}` is `p^r` when the functional is surjective. -/
theorem index_lamST (p r : ℕ) (s t : ZMod (p ^ r)) (hsurj : Function.Surjective (phiST p r s t)) :
    (lamST p r s t).index = p ^ r := by
  unfold lamST
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj,
    Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_zmod]

/-- The quotient by `Λ_{s,t}` is cyclic when the functional is surjective. -/
theorem isAddCyclic_quot_lamST (p r : ℕ) (s t : ZMod (p ^ r))
    (hsurj : Function.Surjective (phiST p r s t)) :
    IsAddCyclic ((ℤ × ℤ) ⧸ lamST p r s t) := by
  let e := QuotientAddGroup.quotientKerEquivOfSurjective (phiST p r s t) hsurj
  exact isAddCyclic_of_surjective e.symm.toAddMonoidHom e.symm.surjective

/-- For a primitive pair `(s, t)` mod `p^r`, `Λ_{s,t}` has index `p^r` and cyclic quotient. -/
theorem index_and_cyclic_lamST {p r : ℕ} [Fact p.Prime] {s t : ZMod (p ^ r)}
    (h : IsUnit s ∨ IsUnit t) :
    (lamST p r s t).index = p ^ r ∧ IsAddCyclic ((ℤ × ℤ) ⧸ lamST p r s t) :=
  ⟨index_lamST p r s t (phiST_surjective_of_isUnit h),
    isAddCyclic_quot_lamST p r s t (phiST_surjective_of_isUnit h)⟩

/-- Every cyclic sublattice of index `p^r` (with `r ≥ 1`) is `Λ_{s,t}` for a primitive pair. -/
theorem exists_lamST_of_cyclic {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r) {L : AddSubgroup (ℤ × ℤ)}
    (hL : L.index = p ^ r) (hc : IsAddCyclic ((ℤ × ℤ) ⧸ L)) :
    ∃ s t : ZMod (p ^ r), (IsUnit s ∨ IsUnit t) ∧ L = lamST p r s t := by
  have hcard : Nat.card ((ℤ × ℤ) ⧸ L) = p ^ r := hL
  have hpos : Nat.card ((ℤ × ℤ) ⧸ L) ≠ 0 := by
    rw [hcard]; exact (pow_pos (Fact.out : p.Prime).pos r).ne'
  have : Finite ((ℤ × ℤ) ⧸ L) := Nat.finite_of_card_ne_zero hpos
  obtain ⟨g, hg⟩ := (IsAddCyclic.exists_zsmul_surjective :
    ∃ g : (ℤ × ℤ) ⧸ L, Function.Surjective (fun n : ℤ => n • g))
  have hord : addOrderOf g ∣ Nat.card ((ℤ × ℤ) ⧸ L) := addOrderOf_dvd_natCard g
  rw [hcard] at hord
  have h0 : zmultiplesHom _ g ((p ^ r : ℕ) : ℤ) = 0 := by
    show ((p ^ r : ℕ) : ℤ) • g = 0
    rw [natCast_zsmul]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hord
  let ψ : ZMod (p ^ r) →+ ((ℤ × ℤ) ⧸ L) := ZMod.lift (p ^ r) ⟨zmultiplesHom _ g, h0⟩
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨k, hk⟩ := hg z
    refine ⟨(k : ZMod (p ^ r)), ?_⟩
    show ZMod.lift (p ^ r) ⟨zmultiplesHom _ g, h0⟩ (k : ZMod (p ^ r)) = z
    rw [ZMod.lift_coe]
    exact hk
  have hψbij : Function.Bijective ψ :=
    (Nat.bijective_iff_surjective_and_card ψ).mpr ⟨hψsurj, by rw [Nat.card_zmod, hcard]⟩
  let e : ZMod (p ^ r) ≃+ ((ℤ × ℤ) ⧸ L) := AddEquiv.ofBijective ψ hψbij
  let φ : (ℤ × ℤ) →+ ZMod (p ^ r) := e.symm.toAddMonoidHom.comp (QuotientAddGroup.mk' L)
  have hφsurj : Function.Surjective φ := by
    intro z
    obtain ⟨q, hq⟩ := e.symm.surjective z
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨w, hq⟩
  have hlin : ∀ w : ℤ × ℤ, φ w = (w.1 : ZMod (p ^ r)) * φ (1, 0) + (w.2 : ZMod (p ^ r)) * φ (0, 1) := by
    intro w
    have hw : w = w.1 • ((1 : ℤ), (0 : ℤ)) + w.2 • ((0 : ℤ), (1 : ℤ)) := by
      ext <;> simp
    have h1 : φ w = w.1 • φ (1, 0) + w.2 • φ (0, 1) := by
      conv_lhs => rw [hw]
      rw [map_add, map_zsmul, map_zsmul]
    rw [h1, zsmul_eq_mul, zsmul_eq_mul]
  have hfun : ∀ w : ℤ × ℤ, phiST p r (φ (1, 0)) (φ (0, 1)) w = φ w := fun w => by
    rw [phiST_apply, hlin w]
  have hmem : ∀ w : ℤ × ℤ, w ∈ lamST p r (φ (1, 0)) (φ (0, 1)) ↔ φ w = 0 := fun w => by
    rw [mem_lamST, ← hlin w]
  have hsurj' : Function.Surjective (phiST p r (φ (1, 0)) (φ (0, 1))) := by
    intro z
    obtain ⟨w, hw⟩ := hφsurj z
    exact ⟨w, by rw [hfun]; exact hw⟩
  refine ⟨φ (1, 0), φ (0, 1), isUnit_or_of_phiST_surjective hr hsurj', ?_⟩
  refine AddSubgroup.ext fun w => ?_
  rw [hmem w]
  show _ ↔ e.symm (QuotientAddGroup.mk w) = 0
  rw [map_eq_zero_iff _ e.symm.injective, QuotientAddGroup.eq_zero_iff]

/-- Two primitive pairs with the same lattice differ by a unit. -/
theorem lamST_eq_iff {p r : ℕ} [Fact p.Prime] {s t s' t' : ZMod (p ^ r)}
    (hst : IsUnit s ∨ IsUnit t) (hst' : IsUnit s' ∨ IsUnit t') :
    lamST p r s t = lamST p r s' t' ↔ ∃ u : ZMod (p ^ r), IsUnit u ∧ s' = u * s ∧ t' = u * t := by
  constructor
  · intro hker
    have hk : ∀ w : ℤ × ℤ, (w.1 : ZMod (p ^ r)) * s + (w.2 : ZMod (p ^ r)) * t = 0 ↔
        (w.1 : ZMod (p ^ r)) * s' + (w.2 : ZMod (p ^ r)) * t' = 0 := fun w => by
      rw [← mem_lamST, ← mem_lamST, hker]
    obtain ⟨w0, hw0⟩ := phiST_surjective_of_isUnit hst 1
    have hw0' : (w0.1 : ZMod (p ^ r)) * s + (w0.2 : ZMod (p ^ r)) * t = 1 := hw0
    have hsm : ∀ (k : ℤ) (x : ℤ × ℤ), k • x = (k * x.1, k * x.2) := by
      intro k x
      ext <;> simp
    set u0 : ZMod (p ^ r) := (w0.1 : ZMod (p ^ r)) * s' + (w0.2 : ZMod (p ^ r)) * t' with hu0def
    have hlin' : ∀ w : ℤ × ℤ, (w.1 : ZMod (p ^ r)) * s' + (w.2 : ZMod (p ^ r)) * t' =
        ((w.1 : ZMod (p ^ r)) * s + (w.2 : ZMod (p ^ r)) * t) * u0 := by
      intro w
      obtain ⟨k, hk1⟩ := ZMod.intCast_surjective
        ((w.1 : ZMod (p ^ r)) * s + (w.2 : ZMod (p ^ r)) * t)
      have e0 : ((w - k • w0).1 : ZMod (p ^ r)) * s + ((w - k • w0).2 : ZMod (p ^ r)) * t = 0 := by
        rw [hsm]
        simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Int.cast_mul]
        linear_combination (-1 : ZMod (p ^ r)) * hk1 - (k : ZMod (p ^ r)) * hw0'
      have e1 := (hk (w - k • w0)).mp e0
      rw [hsm] at e1
      simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Int.cast_mul] at e1
      linear_combination e1 + u0 * hk1
    have hu0 : IsUnit u0 := by
      obtain ⟨w1, hw1⟩ := phiST_surjective_of_isUnit hst' 1
      have hw1' : (w1.1 : ZMod (p ^ r)) * s' + (w1.2 : ZMod (p ^ r)) * t' = 1 := hw1
      have hprod : ((w1.1 : ZMod (p ^ r)) * s + (w1.2 : ZMod (p ^ r)) * t) * u0 = 1 := by
        rw [← hlin' w1]; exact hw1'
      exact isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact hprod⟩
    refine ⟨u0, hu0, ?_, ?_⟩
    · have h := hlin' (1, 0)
      simp only [Int.cast_one, Int.cast_zero, zero_mul, add_zero, one_mul] at h
      linear_combination h
    · have h := hlin' (0, 1)
      simp only [Int.cast_one, Int.cast_zero, zero_mul, one_mul, zero_add] at h
      linear_combination h
  · rintro ⟨u, hu, rfl, rfl⟩
    refine AddSubgroup.ext fun w => ?_
    rw [mem_lamST, mem_lamST]
    have e : (w.1 : ZMod (p ^ r)) * (u * s) + (w.2 : ZMod (p ^ r)) * (u * t)
        = u * ((w.1 : ZMod (p ^ r)) * s + (w.2 : ZMod (p ^ r)) * t) := by ring
    rw [e]
    exact hu.mul_right_eq_zero.symm

/-- The primitive pairs defining a fixed cyclic lattice of index `p^r` form one unit orbit,
of size `p^r - p^(r-1)`. -/
theorem card_fiber_lamST {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r) {L : AddSubgroup (ℤ × ℤ)}
    (hL : L.index = p ^ r) (hc : IsAddCyclic ((ℤ × ℤ) ⧸ L)) :
    Nat.card {v : PrimPt p r // lamST p r v.1.1 v.1.2 = L} = p ^ r - p ^ (r - 1) := by
  obtain ⟨s0, t0, hst0, hL0⟩ := exists_lamST_of_cyclic hr hL hc
  let v0 : PrimPt p r := ⟨(s0, t0), (mem_primPairs p hr _).mpr hst0⟩
  have hv0 : (v0 : ZMod (p ^ r) × ZMod (p ^ r)) = (s0, t0) := rfl
  have key : ∀ v : PrimPt p r, lamST p r v.1.1 v.1.2 = L ↔ v ∈ MulAction.orbit (ZMod (p ^ r))ˣ v0 := by
    intro v
    have hvst : IsUnit v.1.1 ∨ IsUnit v.1.2 := (mem_primPairs p hr _).mp v.2
    constructor
    · intro hv
      have h' : lamST p r s0 t0 = lamST p r v.1.1 v.1.2 := by rw [← hL0, hv]
      obtain ⟨u, hu, h1, h2⟩ := (lamST_eq_iff hst0 hvst).mp h'
      refine MulAction.mem_orbit_iff.mpr ⟨hu.unit, Subtype.ext (Prod.ext ?_ ?_)⟩
      · change ((hu.unit : ZMod (p ^ r)) * s0) = v.1.1
        rw [IsUnit.unit_spec]; exact h1.symm
      · change ((hu.unit : ZMod (p ^ r)) * t0) = v.1.2
        rw [IsUnit.unit_spec]; exact h2.symm
    · intro hv
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hv
      have hunit : IsUnit ((g : ZMod (p ^ r)) * s0) ∨ IsUnit ((g : ZMod (p ^ r)) * t0) :=
        hst0.elim (fun h => Or.inl (g.isUnit.mul h)) (fun h => Or.inr (g.isUnit.mul h))
      rw [← hg, hL0]
      change lamST p r ((g : ZMod (p ^ r)) * s0) ((g : ZMod (p ^ r)) * t0) = lamST p r s0 t0
      exact ((lamST_eq_iff hst0 hunit).mpr ⟨(g : ZMod (p ^ r)), g.isUnit, rfl, rfl⟩).symm
  exact (Nat.card_congr (Equiv.subtypeEquivRight key)).trans (primOrbit_card p hr v0)

/-- Rational form of the fiber count: `(1 - p⁻¹) p^r` primitive defining pairs per cyclic lattice. -/
theorem card_fiber_lamST_rat {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r) {L : AddSubgroup (ℤ × ℤ)}
    (hL : L.index = p ^ r) (hc : IsAddCyclic ((ℤ × ℤ) ⧸ L)) :
    ((Nat.card {v : PrimPt p r // lamST p r v.1.1 v.1.2 = L} : ℕ) : ℚ) = (1 - (p : ℚ)⁻¹) * (p : ℚ) ^ r := by
  have hq : p ^ (r - 1) ≤ p ^ r := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  have hpow : (p : ℚ) ^ r = (p : ℚ) ^ (r - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hr]
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rw [card_fiber_lamST hr hL hc, Nat.cast_sub hq]
  push_cast
  rw [hpow]
  field_simp

end TernaryPeriodPolynomials.Argument.LatticeCounts
