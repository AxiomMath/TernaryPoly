module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.MoveAdd

@[expose] public section





noncomputable section

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open PowerSeries

/-- Shifted-divisibility helper: for `w ≤ d`, `w ∣ d - w ↔ w ∣ d`. -/
theorem dvd_sub_iff_dvd {w d : ℕ} (h : w ≤ d) : w ∣ (d - w) ↔ w ∣ d := by
  have e : w + (d - w) = d := Nat.add_sub_cancel' h
  constructor
  · intro hd; rw [← e]; exact dvd_add (dvd_refl w) hd
  · intro hd; rw [← e] at hd; exact (Nat.dvd_add_right (dvd_refl w)).mp hd

/-- The power series `∑ₙ [w ∣ n] Xⁿ`, i.e. the geometric series in `X^w`. -/
def geom (w : ℕ) : PowerSeries ℤ := PowerSeries.mk fun n => if w ∣ n then (1 : ℤ) else 0

theorem geom_coeff (w n : ℕ) : (PowerSeries.coeff n) (geom w) = if w ∣ n then (1 : ℤ) else 0 :=
  PowerSeries.coeff_mk n _

/-- `geom w` is a one-sided inverse of `1 - X^w` for `w > 0`. -/
theorem one_sub_X_pow_mul_geom {w : ℕ} (hw : 0 < w) :
    (1 - PowerSeries.X ^ w) * geom w = 1 := by
  rw [sub_mul, one_mul]
  apply PowerSeries.ext
  intro d
  rw [map_sub, geom_coeff, PowerSeries.coeff_X_pow_mul' (geom w) w d, geom_coeff,
    PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · have hw' : ¬ (w ≤ 0) := by omega
    simp [hw']
  · have key : w ∣ d ↔ (w ≤ d ∧ w ∣ (d - w)) := by
      constructor
      · intro h1
        exact ⟨Nat.le_of_dvd hd0 h1, (dvd_sub_iff_dvd (Nat.le_of_dvd hd0 h1)).mpr h1⟩
      · rintro ⟨h2, h3⟩
        exact (dvd_sub_iff_dvd h2).mp h3
    by_cases h1 : w ∣ d
    · obtain ⟨h2, h3⟩ := key.mp h1
      simp [h1, h2, h3, hd0.ne']
    · by_cases h2 : w ≤ d
      · have h3 : ¬ w ∣ (d - w) := fun hc => h1 (key.mpr ⟨h2, hc⟩)
        simp [h1, h2, h3, hd0.ne']
      · simp [h1, h2, hd0.ne']

/-- Generic fact: if `D1,D2,D3` individually right-invert `A1,A2,A3`, the products do too. -/
theorem mul_mul_mul_eq_one {D1 D2 D3 A1 A2 A3 : PowerSeries ℤ}
    (h1 : D1 * A1 = 1) (h2 : D2 * A2 = 1) (h3 : D3 * A3 = 1) :
    (D1 * D2 * D3) * (A1 * A2 * A3) = 1 := by
  have e : (D1 * D2 * D3) * (A1 * A2 * A3) = (D1 * A1) * (D2 * A2) * (D3 * A3) := by ring
  rw [e, h1, h2, h3]; ring

/-- Two one-sided inverses of the same element (in a commutative ring) agree with any other
one-sided inverse composed through it: if `D * A = 1` and `D * B' = C` then `A * C = B'`. More
precisely we only need: `D * A = 1` and `D' * B = 1` and `P * D = D'` together give
`A * D' = D * A * D' `... -- see `eq_mul_of_...` below for the actual shape used. -/
theorem geomA_eq_P_mul_geomB {D D' P A B : PowerSeries ℤ}
    (hA : D * A = 1) (hB : D' * B = 1) (hPD : P * D = D') :
    A = P * B := by
  have h1 : A = A * (D' * B) := by rw [hB, mul_one]
  have h2 : D' * B = (P * D) * B := by rw [hPD]
  have h3 : (P * D) * B = P * (D * B) := by ring
  have h4 : A * (D * B) = (A * D) * B := by ring
  have h5 : A * D = D * A := by ring
  calc A = A * (D' * B) := h1
    _ = A * ((P * D) * B) := by rw [h2]
    _ = A * (P * (D * B)) := by rw [h3]
    _ = P * (A * (D * B)) := by ring
    _ = P * ((A * D) * B) := by rw [h4]
    _ = P * ((D * A) * B) := by rw [h5]
    _ = P * (D * A * B) := by ring
    _ = P * (B * (D * A)) := by ring
    _ = P * (B * 1) := by rw [hA]
    _ = P * B := by rw [mul_one]

/-- The 28 weighted degrees (weight 1,2,3 on the three generators `a,b,c`) of
`TernaryPoly.DicksonQuotient.standardMonomial`, in index order; hand-computed from the explicit
monomial list. -/
def stdDeg : Fin 28 → ℕ :=
  ![0,1,2,2,3,3,3,4,4,4,5,5,5,5,6,6,6,6,7,7,7,8,8,8,9,9,10,11]

/-- The Hilbert-series numerator `Σ_m X^{stdDeg m}` (28 terms, with multiplicity). -/
def P : PowerSeries ℤ := ∑ m : Fin 28, PowerSeries.X ^ (stdDeg m)

theorem DA_mul_eq_one :
    ((1 - PowerSeries.X ^ 1) * (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X ^ 3)) *
      (geom 1 * geom 2 * geom 3) = 1 :=
  mul_mul_mul_eq_one (one_sub_X_pow_mul_geom (by norm_num))
    (one_sub_X_pow_mul_geom (by norm_num)) (one_sub_X_pow_mul_geom (by norm_num))

theorem DB_mul_eq_one :
    ((1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6) * (1 - PowerSeries.X ^ 7)) *
      (geom 4 * geom 6 * geom 7) = 1 :=
  mul_mul_mul_eq_one (one_sub_X_pow_mul_geom (by norm_num))
    (one_sub_X_pow_mul_geom (by norm_num)) (one_sub_X_pow_mul_geom (by norm_num))

/-- The key finite Hilbert-series identity, hand-verified coefficient-by-coefficient:
`P(X)·(1-X)(1-X²)(1-X³) = (1-X⁴)(1-X⁶)(1-X⁷)`. -/
theorem P_mul_DA_eq_DB :
    P * ((1 - PowerSeries.X ^ 1) * (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X ^ 3)) =
      (1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6) * (1 - PowerSeries.X ^ 7) := by
  show (∑ _m : Fin 28, PowerSeries.X ^ (stdDeg _m)) * _ = _
  simp [stdDeg, Fin.sum_univ_succ]
  ring

/-- **STEP1 conclusion.** The abstract product-of-geometric-series identity transporting the
28-term Hilbert-series numerator across the two one-sided inverses. -/
theorem geom123_eq_P_mul_geom467 :
    geom 1 * geom 2 * geom 3 = P * (geom 4 * geom 6 * geom 7) :=
  geomA_eq_P_mul_geomB DA_mul_eq_one DB_mul_eq_one P_mul_DA_eq_DB

end TernaryPeriodPolynomials.Argument.CharTwoKernel
