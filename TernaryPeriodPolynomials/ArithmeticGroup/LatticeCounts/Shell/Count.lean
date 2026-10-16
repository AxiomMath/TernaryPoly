module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Coset
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Identity
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Surjective

@[expose] public section


/-!
# The shell cosets, their count, and the shell measure: obligation O3c

Formalized by Claude Haiku 5.5.

* `card_shellCos`: the number of `ℤ_p²`-cosets in the shell `max(|s|_p,|t|_p) = p^r` (for `r ≥ 1`)
  is `p^(2r) - p^(2r-2)`. The bijection sends the coset of `z` to the primitive residue pair
  `redP (p^r z)`; the count is `card_shell_primPt_eq`.
* `shell_measure`: under the normalization `μ(ℤ_p²) = 1` (explicit hypothesis `hn`),
  `μ(shell) = p^(2r) - p^(2r-2)` (a union of `p^(2r) - p^(2r-2)` cosets, each of measure one).
* `shell_measure_rat`: the same value in the rational form `(1 - p⁻²) p^(2r)`.
-/

open PadicInt MeasureTheory

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- The element of `ℤ_p` with value `x`, given `‖x‖ ≤ 1`. -/
def mkZ (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (h : ‖x‖ ≤ 1) : ℤ_[p] := ⟨x, h⟩

theorem mkZ_coe (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (h : ‖x‖ ≤ 1) : (mkZ p x h : ℚ_[p]) = x := rfl

/-- The integral lift of `z · p^r` when it is integral, and `0` otherwise. -/
noncomputable def scaleZ (p r : ℕ) [Fact p.Prime] (z : ℚ_[p]) : ℤ_[p] :=
  if h : ‖z * (p : ℚ_[p]) ^ r‖ ≤ 1 then mkZ p _ h else 0

theorem scaleZ_coe {r : ℕ} {z : ℚ_[p]} (h : ‖z * (p : ℚ_[p]) ^ r‖ ≤ 1) :
    ((scaleZ p r z : ℤ_[p]) : ℚ_[p]) = z * (p : ℚ_[p]) ^ r := by
  unfold scaleZ
  rw [dite_eq_left h, mkZ_coe]

theorem norm_mul_pow_le_one {r : ℕ} {u : ℚ_[p]} (hu : ‖u‖ ≤ (p : ℝ) ^ r) :
    ‖u * (p : ℚ_[p]) ^ r‖ ≤ 1 := by
  have hpos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by exact_mod_cast hp.out.pos) r
  have hpr : ‖(p : ℚ_[p]) ^ r‖ = ((p : ℝ) ^ r)⁻¹ := by
    rw [norm_pow, Padic.norm_p, inv_pow]
  rw [norm_mul, hpr]
  calc ‖u‖ * ((p : ℝ) ^ r)⁻¹ ≤ (p : ℝ) ^ r * ((p : ℝ) ^ r)⁻¹ :=
        mul_le_mul_of_nonneg_right hu (inv_nonneg.mpr hpos.le)
    _ = 1 := mul_inv_cancel₀ hpos.ne'

theorem norm_scale_of_shell {r : ℕ} {z : ℚ_[p] × ℚ_[p]} (hz : z ∈ pairShell p r) :
    ‖z.1 * (p : ℚ_[p]) ^ r‖ ≤ 1 ∧ ‖z.2 * (p : ℚ_[p]) ^ r‖ ≤ 1 := by
  have hz' : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ r := hz
  exact ⟨norm_mul_pow_le_one ((le_max_left _ _).trans hz'.le),
    norm_mul_pow_le_one ((le_max_right _ _).trans hz'.le)⟩

/-- On the shell, one coordinate of `z · p^r` is a unit of `ℤ_p`. -/
theorem shell_scale_unit {r : ℕ} {z : ℚ_[p] × ℚ_[p]} (hz : z ∈ pairShell p r) :
    IsUnit (scaleZ p r z.1) ∨ IsUnit (scaleZ p r z.2) := by
  have hz' : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ r := hz
  have hpos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by exact_mod_cast hp.out.pos) r
  have hpr : ‖(p : ℚ_[p]) ^ r‖ = ((p : ℝ) ^ r)⁻¹ := by
    rw [norm_pow, Padic.norm_p, inv_pow]
  rcases max_choice ‖z.1‖ ‖z.2‖ with h | h
  · left
    have h1 : ‖z.1‖ = (p : ℝ) ^ r := by rw [← h]; exact hz'
    rw [PadicInt.isUnit_iff, PadicInt.norm_def,
      scaleZ_coe (norm_mul_pow_le_one ((le_max_left _ _).trans hz'.le)), norm_mul, hpr, h1,
      mul_inv_cancel₀ hpos.ne']
  · right
    have h1 : ‖z.2‖ = (p : ℝ) ^ r := by rw [← h]; exact hz'
    rw [PadicInt.isUnit_iff, PadicInt.norm_def,
      scaleZ_coe (norm_mul_pow_le_one ((le_max_right _ _).trans hz'.le)), norm_mul, hpr, h1,
      mul_inv_cancel₀ hpos.ne']

/-- Two scaled integral lifts have equal reductions mod `p^r` exactly when their difference
has norm at most one. -/
theorem toZModPow_scale_eq_iff {r : ℕ} {a b : ℚ_[p]} (ha : ‖a * (p : ℚ_[p]) ^ r‖ ≤ 1)
    (hb : ‖b * (p : ℚ_[p]) ^ r‖ ≤ 1) :
    toZModPow r (scaleZ p r a) = toZModPow r (scaleZ p r b) ↔ ‖a - b‖ ≤ 1 := by
  have hpos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by exact_mod_cast hp.out.pos) r
  have hpr : ‖(p : ℚ_[p]) ^ r‖ = ((p : ℝ) ^ r)⁻¹ := by
    rw [norm_pow, Padic.norm_p, inv_pow]
  have hc : ((scaleZ p r a - scaleZ p r b : ℤ_[p]) : ℚ_[p]) = (a - b) * (p : ℚ_[p]) ^ r := by
    rw [PadicInt.coe_sub, scaleZ_coe ha, scaleZ_coe hb]
    ring
  have hn : ‖scaleZ p r a - scaleZ p r b‖ = ‖a - b‖ * ((p : ℝ) ^ r)⁻¹ := by
    rw [PadicInt.norm_def, hc, norm_mul, hpr]
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_toZModPow, ← norm_le_pow_iff_mem_span_pow,
    hn, zpow_neg, zpow_natCast, mul_le_iff_le_one_left (inv_pos.mpr hpos)]

/-- The reduction of the scaled lifts of two shell points agrees exactly on `ℤ_p²`-cosets. -/
theorem redP_scale_eq_iff {r : ℕ} {z w : ℚ_[p] × ℚ_[p]} (hz : z ∈ pairShell p r)
    (hw : w ∈ pairShell p r) :
    redP (p := p) r (scaleZ p r z.1, scaleZ p r z.2) =
        redP (p := p) r (scaleZ p r w.1, scaleZ p r w.2) ↔
      z - w ∈ Zp2 p := by
  obtain ⟨hz1, hz2⟩ := norm_scale_of_shell hz
  obtain ⟨hw1, hw2⟩ := norm_scale_of_shell hw
  have e1 := toZModPow_scale_eq_iff hz1 hw1
  have e2 := toZModPow_scale_eq_iff hz2 hw2
  show (toZModPow r (scaleZ p r z.1), toZModPow r (scaleZ p r z.2)) =
      (toZModPow r (scaleZ p r w.1), toZModPow r (scaleZ p r w.2)) ↔ z - w ∈ Zp2 p
  rw [Prod.mk.injEq, e1, e2]
  exact Iff.rfl

/-- The primitive residue pair attached to a shell point: `redP (p^r z)`. -/
noncomputable def shellRes (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r) (z : pairShell p r) :
    PrimPt p r :=
  ⟨redP (p := p) r (scaleZ p r z.1.1, scaleZ p r z.1.2),
    (mem_primPairs p (by omega) _).mpr (by
      rcases shell_scale_unit z.2 with h | h
      · exact Or.inl (RingHom.isUnit_map _ h)
      · exact Or.inr (RingHom.isUnit_map _ h))⟩

/-! ### The subgroup `ℤ_p²` inside `ℚ_p²` -/

theorem zp2_zero : (0 : ℚ_[p] × ℚ_[p]) ∈ Zp2 p :=
  mem_Zp2.mpr ⟨by simp, by simp⟩

theorem zp2_add {a b : ℚ_[p] × ℚ_[p]} (ha : a ∈ Zp2 p) (hb : b ∈ Zp2 p) :
    a + b ∈ Zp2 p := by
  obtain ⟨a1, a2⟩ := mem_Zp2.mp ha
  obtain ⟨b1, b2⟩ := mem_Zp2.mp hb
  exact mem_Zp2.mpr ⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le a1 b1),
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le a2 b2)⟩

theorem zp2_neg {a : ℚ_[p] × ℚ_[p]} (ha : a ∈ Zp2 p) : -a ∈ Zp2 p := by
  obtain ⟨a1, a2⟩ := mem_Zp2.mp ha
  exact mem_Zp2.mpr ⟨by rw [Prod.fst_neg, norm_neg]; exact a1,
    by rw [Prod.snd_neg, norm_neg]; exact a2⟩

theorem zp2_sub {a b : ℚ_[p] × ℚ_[p]} (ha : a ∈ Zp2 p) (hb : b ∈ Zp2 p) :
    a - b ∈ Zp2 p := by
  rw [sub_eq_add_neg]
  exact zp2_add ha (zp2_neg hb)

theorem isClosed_Zp2 : IsClosed (Zp2 p) := by
  have e : Zp2 p = (Prod.fst ⁻¹' Metric.closedBall (0 : ℚ_[p]) 1) ∩
      (Prod.snd ⁻¹' Metric.closedBall (0 : ℚ_[p]) 1) := by
    ext z
    simp [Zp2]
  rw [e]
  exact (Metric.isClosed_closedBall.preimage continuous_fst).inter
    (Metric.isClosed_closedBall.preimage continuous_snd)

/-- The setoid whose classes are the `ℤ_p²`-cosets of the shell. -/
def shellSetoid (p r : ℕ) [Fact p.Prime] : Setoid (pairShell p r) where
  r a b := a.1 - b.1 ∈ Zp2 p
  iseqv := ⟨fun a => by
      show a.1 - a.1 ∈ Zp2 p
      rw [sub_self]
      exact zp2_zero,
    fun {a b} h => by
      show b.1 - a.1 ∈ Zp2 p
      rw [show b.1 - a.1 = -(a.1 - b.1) by abel]
      exact zp2_neg h,
    fun {a b c} h1 h2 => by
      show a.1 - c.1 ∈ Zp2 p
      rw [show a.1 - c.1 = (a.1 - b.1) + (b.1 - c.1) by abel]
      exact zp2_add h1 h2⟩

/-- The `ℤ_p²`-cosets of the shell. -/
abbrev ShellCos (p r : ℕ) [Fact p.Prime] := Quotient (shellSetoid p r)

theorem shellRes_eq_of_rel {r : ℕ} (hr : 1 ≤ r) {a b : pairShell p r}
    (h : a.1 - b.1 ∈ Zp2 p) : shellRes p r hr a = shellRes p r hr b :=
  Subtype.ext ((redP_scale_eq_iff a.2 b.2).mpr h)

/-- The map from cosets to primitive residue pairs. -/
noncomputable def shellMap (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r) : ShellCos p r → PrimPt p r :=
  Quotient.lift (shellRes p r hr) (fun _ _ h => shellRes_eq_of_rel hr h)

theorem exists_shell_of_primPt {r : ℕ} (hr : 1 ≤ r) (v : PrimPt p r) :
    ∃ z ∈ pairShell p r, redP (p := p) r (scaleZ p r z.1, scaleZ p r z.2) = v.1 := by
  obtain ⟨x, hx⟩ := redP_surjective (p := p) r v.1
  have hne : (p : ℚ_[p]) ^ r ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hpos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by exact_mod_cast hp.out.pos) r
  have hpr : ‖(p : ℚ_[p]) ^ r‖ = ((p : ℝ) ^ r)⁻¹ := by
    rw [norm_pow, Padic.norm_p, inv_pow]
  have hzs : ∀ a : ℤ_[p], (a : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹ * (p : ℚ_[p]) ^ r = a := fun a => by
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
  have hnormeq : ∀ a : ℤ_[p], ‖(a : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹‖ = ‖(a : ℚ_[p])‖ * (p : ℝ) ^ r :=
    fun a => by rw [norm_mul, norm_inv, hpr, inv_inv]
  have hnorm : ∀ a : ℤ_[p], ‖(a : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹‖ ≤ (p : ℝ) ^ r := fun a => by
    rw [hnormeq]
    exact mul_le_of_le_one_left hpos.le (PadicInt.norm_le_one a)
  have e1 : scaleZ p r ((x.1 : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹) = x.1 :=
    Subtype.ext ((scaleZ_coe (norm_mul_pow_le_one (hnorm x.1))).trans (hzs x.1))
  have e2 : scaleZ p r ((x.2 : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹) = x.2 :=
    Subtype.ext ((scaleZ_coe (norm_mul_pow_le_one (hnorm x.2))).trans (hzs x.2))
  have hprim : IsUnit x.1 ∨ IsUnit x.2 := by
    have hv := v.2
    rw [mem_primPairs p (by omega)] at hv
    rcases hv with h | h
    · left
      have h' : IsUnit (toZModPow r x.1) := by
        have h'' := h
        rw [← hx] at h''
        exact h''
      -- a non-unit `x.1 ∈ pℤ_p` reduces to a non-unit mod `p^r`
      by_contra hcon
      have hn1 : ¬ IsUnit x.1 := hcon
      rw [PadicInt.isUnit_iff] at hn1
      have hlt : ‖x.1‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) hn1
      obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd x.1).mp hlt
      rw [hc, map_mul, map_natCast] at h'
      have hpu : IsUnit (p : ZMod (p ^ r)) := isUnit_of_mul_isUnit_left h'
      rw [ZMod.isUnit_iff_coprime] at hpu
      have : p = 1 := Nat.Coprime.eq_one_of_dvd (Nat.coprime_pow_right_iff (by omega) _ _ |>.mp hpu)
        (dvd_refl p)
      exact hp.out.one_lt.ne' this
    · right
      have h' : IsUnit (toZModPow r x.2) := by
        have h'' := h
        rw [← hx] at h''
        exact h''
      by_contra hcon
      have hn1 : ¬ IsUnit x.2 := hcon
      rw [PadicInt.isUnit_iff] at hn1
      have hlt : ‖x.2‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) hn1
      obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd x.2).mp hlt
      rw [hc, map_mul, map_natCast] at h'
      have hpu : IsUnit (p : ZMod (p ^ r)) := isUnit_of_mul_isUnit_left h'
      rw [ZMod.isUnit_iff_coprime] at hpu
      have : p = 1 := Nat.Coprime.eq_one_of_dvd (Nat.coprime_pow_right_iff (by omega) _ _ |>.mp hpu)
        (dvd_refl p)
      exact hp.out.one_lt.ne' this
  have hzmem : ((x.1 : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹, (x.2 : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹) ∈
      pairShell p r := by
    show max ‖(x.1 : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹‖ ‖(x.2 : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹‖ =
      (p : ℝ) ^ r
    rcases hprim with h | h
    · have h1 : ‖(x.1 : ℚ_[p])‖ = 1 := by
        rw [← PadicInt.norm_def]
        exact PadicInt.isUnit_iff.mp h
      rw [hnormeq, hnormeq, h1, one_mul]
      exact max_eq_left (mul_le_of_le_one_left hpos.le (PadicInt.norm_le_one _))
    · have h1 : ‖(x.2 : ℚ_[p])‖ = 1 := by
        rw [← PadicInt.norm_def]
        exact PadicInt.isUnit_iff.mp h
      rw [hnormeq, hnormeq, h1, one_mul]
      exact max_eq_right (mul_le_of_le_one_left hpos.le (PadicInt.norm_le_one _))
  refine ⟨_, hzmem, ?_⟩
  show redP (p := p) r (scaleZ p r ((x.1 : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹),
    scaleZ p r ((x.2 : ℚ_[p]) * ((p : ℚ_[p]) ^ r)⁻¹)) = v.1
  rw [e1, e2, hx]

theorem shellMap_bijective {r : ℕ} (hr : 1 ≤ r) : Function.Bijective (shellMap p r hr) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    exact Quotient.sound ((redP_scale_eq_iff a.2 b.2).mp (congrArg Subtype.val hxy))
  · intro v
    obtain ⟨z, hz, hv⟩ := exists_shell_of_primPt hr v
    exact ⟨(Quotient.mk (shellSetoid p r) ⟨z, hz⟩), Subtype.ext hv⟩

/-- The number of `ℤ_p²`-cosets in the shell is `p^(2r) - p^(2r-2)`. -/
theorem card_shellCos {r : ℕ} (hr : 1 ≤ r) :
    Nat.card (ShellCos p r) = p ^ (2 * r) - p ^ (2 * r - 2) := by
  rw [Nat.card_congr (Equiv.ofBijective _ (shellMap_bijective hr)), card_shell_primPt_eq p hr]

/-- The shell measure under the normalization `μ(ℤ_p²) = 1`: `μ(shell)` is the
number of cosets, `p^(2r) - p^(2r-2)`. -/
theorem shell_measure [MeasurableSpace (ℚ_[p] × ℚ_[p])] [BorelSpace (ℚ_[p] × ℚ_[p])]
    [MeasurableAdd (ℚ_[p] × ℚ_[p])]
    {μ : Measure (ℚ_[p] × ℚ_[p])} [μ.IsAddLeftInvariant] (hn : μ (Zp2 p) = 1)
    {r : ℕ} (hr : 1 ≤ r) :
    μ (pairShell p r) = ((p ^ (2 * r) - p ^ (2 * r - 2) : ℕ) : ENNReal) := by
  have hfin : Finite (ShellCos p r) := Finite.of_injective _ (shellMap_bijective hr).1
  have : Fintype (ShellCos p r) := Fintype.ofFinite _
  have hmeas : ∀ q : ShellCos p r, MeasurableSet {y | y - (q.out).1 ∈ Zp2 p} := fun q =>
    (continuous_sub_right _).measurable isClosed_Zp2.measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint fun q : ShellCos p r => {y | y - (q.out).1 ∈ Zp2 p}) := by
    intro q q' hne
    refine Set.disjoint_left.mpr fun y hy hy' => hne ?_
    have h1 : q.out.1 - q'.out.1 ∈ Zp2 p := by
      have := zp2_sub (show y - q'.out.1 ∈ Zp2 p from hy') (show y - q.out.1 ∈ Zp2 p from hy)
      rwa [show y - q'.out.1 - (y - q.out.1) = q.out.1 - q'.out.1 by abel] at this
    calc q = (Quotient.mk (shellSetoid p r) q.out) := (Quotient.out_eq q).symm
      _ = (Quotient.mk (shellSetoid p r) q'.out) := Quotient.sound h1
      _ = q' := Quotient.out_eq q'
  have hcov : pairShell p r = ⋃ q : ShellCos p r, {y | y - (q.out).1 ∈ Zp2 p} := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hy
      exact ⟨(Quotient.mk (shellSetoid p r) ⟨y, hy⟩), (shellSetoid p r).iseqv.symm (Quotient.mk_out (s := shellSetoid p r) ⟨y, hy⟩)⟩
    · rintro ⟨q, hq⟩
      have := pairShell_add_mem_zp2 hr q.out.2 hq
      rwa [show q.out.1 + (y - q.out.1) = y by abel] at this
  have h1 : ∀ q : ShellCos p r, μ {y | y - (q.out).1 ∈ Zp2 p} = 1 := fun q =>
    (pairShell_coset_measure hr hn q.out.2).2
  rw [hcov, measure_iUnion hdisj hmeas, tsum_fintype,
    Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_shellCos hr]
  simp

/-- The shell measure in the rational form `(1 - p⁻²) p^(2r)`. -/
theorem shell_measure_rat [MeasurableSpace (ℚ_[p] × ℚ_[p])] [BorelSpace (ℚ_[p] × ℚ_[p])]
    [MeasurableAdd (ℚ_[p] × ℚ_[p])]
    {μ : Measure (ℚ_[p] × ℚ_[p])} [μ.IsAddLeftInvariant] (hn : μ (Zp2 p) = 1)
    {r : ℕ} (hr : 1 ≤ r) :
    μ (pairShell p r) = ENNReal.ofReal ((1 - ((p : ℝ) ^ 2)⁻¹) * (p : ℝ) ^ (2 * r)) := by
  rw [shell_measure hn hr, ← ENNReal.ofReal_natCast]
  congr 1
  have hle : p ^ (2 * r - 2) ≤ p ^ (2 * r) := Nat.pow_le_pow_right hp.out.pos (by omega)
  obtain ⟨m, hm⟩ : ∃ m, 2 * r - 2 = m := ⟨_, rfl⟩
  have e : 2 * r = m + 2 := by omega
  rw [hm] at hle ⊢
  rw [e] at hle ⊢
  rw [Nat.cast_sub hle]
  push_cast
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  field_simp
  ring

end TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
