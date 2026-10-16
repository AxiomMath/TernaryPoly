module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldBig

@[expose] public section


/-!
# Absolute convergence of the free-orbit sum of the line radical average, and linearity in `f`

* `QAct.orbit_integrable`: the representative of a free orbit is integrable over `ℝ²`.
* `QAct.orbit_summable`: the family of `ℝ²` integrals over the free orbits is absolutely summable
  (each is bounded by the orbit sum of the summable bound `B` of `Φ` on `[-N, N]²`).
* `lineA1`: the explicit coefficient `∑'_O ∫_{ℝ²} PhiQ(c_O)(N v) dv` of the line-radical average;
  `lineA1_add` and `lineA1_smul` (additive and `ℂ`-homogeneous in the cusp form `f`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set MvPolynomial
open scoped MatrixGroups ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.SeedC3.Psi

section Orbits

variable {N : ℕ} [NeZero N] {Cs : Type} (Q : QAct N Cs)

omit [NeZero N] in
theorem QAct.r0Q_out (o : Quotient Q.orbSetoid) : Q.r0Q o = Q.r0 (Quotient.out o) := by
  have ho : Quotient.mk Q.orbSetoid (Quotient.out o) = o := Quotient.out_eq o
  conv_lhs => rw [← ho]
  rfl

omit [NeZero N] in
/-- The representative of a free orbit is integrable over `ℝ²`. -/
theorem QAct.orbit_integrable (Φ : Cs → (Fin 2 → ℝ) → ℂ)
    (h1 : ∀ ℓ c v, Φ (Q.act ℓ c) v = Φ c ((N : ℝ) • intVec ℓ + v))
    (hc : ∀ c, Continuous (Φ c))
    (hb : ∀ R : ℝ, ∃ B : Cs → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖Φ c v‖ ≤ B c)
    (o : Quotient Q.orbSetoid) (ho : Q.r0Q o ≠ 0) :
    Integrable (fun v : Fin 2 → ℝ => Φ (Quotient.out o) ((N : ℝ) • v)) := by
  rw [QAct.r0Q_out] at ho
  exact (free_orbit_unfold_aux Q Φ h1 hc hb _ ho).1

omit [NeZero N] in
theorem unit_square_bound (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (k : Fin 2) :
    |((N : ℝ) • ![a, b]) k| ≤ N := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  fin_cases k
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast]
    simp
    rw [abs_of_nonneg ha.1]
    exact mul_le_of_le_one_right hN0 ha.2
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast]
    simp
    rw [abs_of_nonneg hb.1]
    exact mul_le_of_le_one_right hN0 hb.2

omit [NeZero N] in
/-- **Absolute convergence of the sum over the free orbits** of the `ℝ²` integrals. -/
theorem QAct.orbit_summable [Countable Cs] (Φ : Cs → (Fin 2 → ℝ) → ℂ)
    (h1 : ∀ ℓ c v, Φ (Q.act ℓ c) v = Φ c ((N : ℝ) • intVec ℓ + v))
    (hc : ∀ c, Continuous (Φ c))
    (hb : ∀ R : ℝ, ∃ B : Cs → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖Φ c v‖ ≤ B c) :
    Summable fun o : {o : Quotient Q.orbSetoid // Q.r0Q o ≠ 0} =>
      ∫ v : Fin 2 → ℝ, Φ (Quotient.out o.1) ((N : ℝ) • v) := by
  classical
  obtain ⟨B, hBs, hBb⟩ := hb (N : ℝ)
  let q : Cs → Quotient Q.orbSetoid := fun c => Quotient.mk Q.orbSetoid c
  have hHB : Summable fun o : Quotient Q.orbSetoid => ∑' c : q ⁻¹' {o}, B c :=
    (hBs.hasSum.tsum_fiberwise q).summable
  have hbound : ∀ o : {o : Quotient Q.orbSetoid // Q.r0Q o ≠ 0},
      ‖∫ v : Fin 2 → ℝ, Φ (Quotient.out o.1) ((N : ℝ) • v)‖ ≤ ∑' c : q ⁻¹' {o.1}, B c := by
    intro o
    set c₀ := Quotient.out o.1 with hc₀
    have hr : Q.r0 c₀ ≠ 0 := by rw [← QAct.r0Q_out]; exact o.2
    have ho : Quotient.mk Q.orbSetoid c₀ = o.1 := Quotient.out_eq o.1
    have hset : q ⁻¹' {o.1} = {c | Q.OrbRel c₀ c} := by
      ext c
      rw [← ho]
      show Quotient.mk Q.orbSetoid c = Quotient.mk Q.orbSetoid c₀ ↔ Q.OrbRel c₀ c
      rw [Quotient.eq]
      exact ⟨fun h => QAct.OrbRel.symm Q h, fun h => QAct.OrbRel.symm Q h⟩
    rw [← free_orbit_unfold Q Φ h1 hc hb c₀ hr]
    have hsum : Summable fun c : {c // Q.OrbRel c₀ c} => B c.1 := hBs.subtype _
    have hin : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
        ‖∑' c : {c // Q.OrbRel c₀ c}, Φ c.1 ((N : ℝ) • ![a, b])‖ ≤ ∑' c : q ⁻¹' {o.1}, B c := by
      intro a b ha hb'
      rw [tsum_congr_set_coe B hset]
      exact tsum_of_norm_bounded hsum.hasSum (fun c => hBb c.1 _ (unit_square_bound a b ha hb'))
    have hout : ∀ a : ℝ, a ∈ Icc (0 : ℝ) 1 →
        ‖∫ b in (0 : ℝ)..1, ∑' c : {c // Q.OrbRel c₀ c}, Φ c.1 ((N : ℝ) • ![a, b])‖ ≤
          ∑' c : q ⁻¹' {o.1}, B c := by
      intro a ha
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (C := ∑' c : q ⁻¹' {o.1}, B c)
        (f := fun b => ∑' c : {c // Q.OrbRel c₀ c}, Φ c.1 ((N : ℝ) • ![a, b]))
        (fun b hb' => hin a b ha (by
          rw [uIoc_of_le zero_le_one] at hb'
          exact ⟨hb'.1.le, hb'.2⟩))
      simpa using this
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := ∑' c : q ⁻¹' {o.1}, B c)
      (f := fun a => ∫ b in (0 : ℝ)..1, ∑' c : {c // Q.OrbRel c₀ c}, Φ c.1 ((N : ℝ) • ![a, b]))
      (fun a ha => hout a (by
        rw [uIoc_of_le zero_le_one] at ha
        exact ⟨ha.1.le, ha.2⟩))
    simpa using this
  exact Summable.of_norm_bounded (hHB.subtype _) hbound

end Orbits

section Linearity

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **The explicit coefficient of the line-radical average**: the sum over the free orbits of the
`ℝ²`-integrals of the orbit representatives. -/
def lineA1 (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (x : Face) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) : ℂ :=
  ∑' o : {o : Quotient (qActGamma N).orbSetoid // (qActGamma N).r0Q o ≠ 0},
    ∫ v : Fin 2 → ℝ, PhiQ N n f x p q m (Quotient.out o.1) ((N : ℝ) • v)

theorem PhiQ_data (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) {x : Face}
    (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    Summable (fun o : {o : Quotient (qActGamma N).orbSetoid // (qActGamma N).r0Q o ≠ 0} =>
      ∫ v : Fin 2 → ℝ, PhiQ N n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) ∧
    ∀ o : {o : Quotient (qActGamma N).orbSetoid // (qActGamma N).r0Q o ≠ 0},
      Integrable (fun v : Fin 2 → ℝ => PhiQ N n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) :=
  ⟨QAct.orbit_summable (qActGamma N) (fun c w => PhiQ N n f x p q m c w)
    (fun ℓ c w => PhiQ_latQ hx p q m ℓ c w)
    (fun c => (PhiQ_continuous_bound N n f hn hx p q m).1 c)
    (fun R => (PhiQ_continuous_bound N n f hn hx p q m).2 R),
   fun o => QAct.orbit_integrable (qActGamma N) (fun c w => PhiQ N n f x p q m c w)
    (fun ℓ c w => PhiQ_latQ hx p q m ℓ c w)
    (fun c => (PhiQ_continuous_bound N n f hn hx p q m).1 c)
    (fun R => (PhiQ_continuous_bound N n f hn hx p q m).2 R) o.1 o.2⟩

/-- **`lineA1` is additive in the cusp form.** -/
theorem lineA1_add (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) {x : Face}
    (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    lineA1 N n (f + g) x p q m = lineA1 N n f x p q m + lineA1 N n g x p q m := by
  obtain ⟨hsf, hif⟩ := PhiQ_data N n f hn hx p q m
  obtain ⟨hsg, hig⟩ := PhiQ_data N n g hn hx p q m
  unfold lineA1
  rw [← hsf.tsum_add hsg]
  refine tsum_congr fun o => ?_
  have : (fun v : Fin 2 → ℝ => PhiQ N n (f + g) x p q m (Quotient.out o.1) ((N : ℝ) • v)) =
      fun v => PhiQ N n f x p q m (Quotient.out o.1) ((N : ℝ) • v) +
        PhiQ N n g x p q m (Quotient.out o.1) ((N : ℝ) • v) := by
    funext v
    exact PhiQ_add N n f g p q m _ _
  rw [this]
  exact integral_add (hif o) (hig o)

/-- **`lineA1` is `ℂ`-homogeneous in the cusp form.** -/
theorem lineA1_smul (a : ℂ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) {x : Face}
    (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    lineA1 N n (a • f) x p q m = a * lineA1 N n f x p q m := by
  unfold lineA1
  rw [← tsum_mul_left]
  refine tsum_congr fun o => ?_
  have : (fun v : Fin 2 → ℝ => PhiQ N n (a • f) x p q m (Quotient.out o.1) ((N : ℝ) • v)) =
      fun v => a * PhiQ N n f x p q m (Quotient.out o.1) ((N : ℝ) • v) := by
    funext v
    exact PhiQ_smul N n f a p q m _ _
  rw [this]
  exact integral_const_mul a _

/-- The headline restated: the coefficient of the line-radical average is `lineA1`. -/
theorem lineAvg_coeff_eq_lineA1 (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) {x : Face}
    (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    (Coef.toPoly (((((lineTwist N n).avInvT
        (lineFaceForm N n (planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))) :
          ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action (rhoQ N n)) :
            Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single p 1, Pi.single q 1])).coeff m = lineA1 N n f x p q m :=
  lineAvg_coeff N n f hn hx p q m

end Linearity

end TernaryPeriodPolynomials.Argument.EisensteinClass
