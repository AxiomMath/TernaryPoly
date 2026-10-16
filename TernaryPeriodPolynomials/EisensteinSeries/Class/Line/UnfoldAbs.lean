module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Abs
public import TernaryPeriodPolynomials.EisensteinSeries.Class.TilingR2

@[expose] public section


/-!
# The two cells of the line radical, abstractly: fixed points vanish, free orbits unfold to `ℝ²`

(rows `Q, I` and
`Q, w₀⁻¹`: "the target root is conjugated into the source binary root ... average zero by cuspidality";
"the target radical intersects the conjugated source parabolic radical trivially, leaving the integral over
`𝔸²`. The integrated radical quotient is compact, so Fubini applies").

`QAct N Cs`: a right action of the lattice `ℤ²` on an index set with an invariant integer `r₀` such that the
action is trivial where `r₀ = 0` and free where `r₀ ≠ 0`. `QAct.total`: for an equivariant, continuous,
locally summably bounded family `Φ` whose integral along one period of a coordinate direction vanishes on
the fixed points, the torus integral of the total sum is the sum over the free orbits of the integral over
`ℝ²` of the orbit representative.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

/-- A right action of the radical lattice `ℤ²` which is trivial on the cell `r₀ = 0` and free on the
cell `r₀ ≠ 0`. -/
structure QAct (N : ℕ) (Cs : Type) where
  act : (Fin 2 → ℤ) → Cs → Cs
  r0 : Cs → ℤ
  act_zero : ∀ c, act 0 c = c
  act_add : ∀ ℓ ℓ' c, act (ℓ + ℓ') c = act ℓ' (act ℓ c)
  r0_act : ∀ ℓ c, r0 (act ℓ c) = r0 c
  fix : ∀ ℓ c, r0 c = 0 → act ℓ c = c
  free : ∀ c, r0 c ≠ 0 → Function.Injective fun ℓ => act ℓ c

namespace QAct

variable {N : ℕ} {Cs : Type} (Q : QAct N Cs)

/-- The orbit relation. -/
def OrbRel (c c' : Cs) : Prop := ∃ ℓ : Fin 2 → ℤ, Q.act ℓ c = c'

theorem OrbRel.refl (c : Cs) : Q.OrbRel c c := ⟨0, Q.act_zero c⟩

theorem OrbRel.symm {c c' : Cs} (h : Q.OrbRel c c') : Q.OrbRel c' c := by
  obtain ⟨ℓ, rfl⟩ := h
  refine ⟨-ℓ, ?_⟩
  rw [← Q.act_add, add_neg_cancel, Q.act_zero]

theorem OrbRel.trans {c c' c'' : Cs} (h : Q.OrbRel c c') (h' : Q.OrbRel c' c'') :
    Q.OrbRel c c'' := by
  obtain ⟨ℓ, rfl⟩ := h
  obtain ⟨ℓ', rfl⟩ := h'
  exact ⟨ℓ + ℓ', by rw [Q.act_add]⟩

/-- The orbit setoid. -/
def orbSetoid : Setoid Cs where
  r := Q.OrbRel
  iseqv := ⟨OrbRel.refl Q, OrbRel.symm Q, OrbRel.trans Q⟩

theorem r0_of_orbRel {c c' : Cs} (h : Q.OrbRel c c') : Q.r0 c' = Q.r0 c := by
  obtain ⟨ℓ, rfl⟩ := h
  exact Q.r0_act ℓ c

/-- The invariant integer of an orbit. -/
def r0Q (o : Quotient Q.orbSetoid) : ℤ :=
  Quotient.lift Q.r0 (fun a b h => (Q.r0_of_orbRel (show Q.OrbRel a b from h)).symm) o

end QAct

section Torus

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- **Row `Q, I`**: if the integral along one period of a coordinate direction vanishes, the torus
integral vanishes. -/
theorem torus_zero_of_axis (F : (Fin 2 → ℝ) → ℂ) (hF : Continuous F) (k : Fin 2)
    (hk : ∀ w : Fin 2 → ℝ, ∫ s in (0 : ℝ)..1, F (w + s • ((N : ℝ) • (Pi.single k 1 : Fin 2 → ℝ))) = 0) :
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, F ((N : ℝ) • ![a, b]) = 0 := by
  fin_cases k
  · -- the closed direction is the first coordinate: swap the order of integration
    have hcont : Continuous (Function.uncurry fun a b : ℝ => F ((N : ℝ) • ![a, b])) :=
      (hF.comp ((show Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) by fun_prop).const_smul (N : ℝ)) : Continuous fun p : ℝ × ℝ => F ((N : ℝ) • ![p.1, p.2]))
    rw [integral_swap_unit _ hcont]
    have : ∀ b : ℝ, ∫ a in (0 : ℝ)..1, F ((N : ℝ) • ![a, b]) = 0 := by
      intro b
      rw [← hk ((N : ℝ) • ![0, b])]
      refine intervalIntegral.integral_congr fun a _ => ?_
      congr 1
      funext i
      fin_cases i <;> simp [mul_comm]
    exact (intervalIntegral.integral_congr fun b _ => this b).trans (by simp)
  · have : ∀ a : ℝ, ∫ b in (0 : ℝ)..1, F ((N : ℝ) • ![a, b]) = 0 := by
      intro a
      rw [← hk ((N : ℝ) • ![a, 0])]
      refine intervalIntegral.integral_congr fun b _ => ?_
      congr 1
      funext i
      fin_cases i <;> simp [mul_comm]
    exact (intervalIntegral.integral_congr fun a _ => this a).trans (by simp)

end Torus

section Orbits

variable {N : ℕ} [NeZero N] {Cs : Type} (Q : QAct N Cs)

omit [NeZero N] in
/-- **Row `Q, w₀⁻¹`**: the orbit representative of a free orbit is integrable over `ℝ²`, and the sum over
the orbit of the torus integral is its integral (unfolding, Fubini). -/
theorem free_orbit_unfold_aux (Φ : Cs → (Fin 2 → ℝ) → ℂ)
    (h1 : ∀ ℓ c v, Φ (Q.act ℓ c) v = Φ c ((N : ℝ) • intVec ℓ + v))
    (hc : ∀ c, Continuous (Φ c))
    (hb : ∀ R : ℝ, ∃ B : Cs → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖Φ c v‖ ≤ B c)
    (c₀ : Cs) (hr : Q.r0 c₀ ≠ 0) :
    Integrable (fun v : Fin 2 → ℝ => Φ c₀ ((N : ℝ) • v)) ∧
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
      ∑' c : {c // Q.OrbRel c₀ c}, Φ c.1 ((N : ℝ) • ![a, b]) = ∫ v : Fin 2 → ℝ, Φ c₀ ((N : ℝ) • v) := by
  obtain ⟨B, hBs, hBb⟩ := hb (N : ℝ)
  let ψ : (Fin 2 → ℤ) → {c // Q.OrbRel c₀ c} := fun ℓ => ⟨Q.act ℓ c₀, ⟨ℓ, rfl⟩⟩
  have hψinj : Function.Injective ψ := fun ℓ ℓ' h => Q.free c₀ hr (congrArg Subtype.val h)
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨c, ℓ, rfl⟩
    exact ⟨ℓ, rfl⟩
  let e : (Fin 2 → ℤ) ≃ {c // Q.OrbRel c₀ c} := Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hvbd : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → ∀ k : Fin 2,
      |((N : ℝ) • ![a, b]) k| ≤ N := by
    intro a b ha hb k
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
  have hsub : ∀ a b : ℝ, ∑' c : {c // Q.OrbRel c₀ c}, Φ c.1 ((N : ℝ) • ![a, b]) =
      ∑' ℓ : Fin 2 → ℤ, Φ (Q.act ℓ c₀) ((N : ℝ) • ![a, b]) := fun a b =>
    (e.tsum_eq (fun c : {c // Q.OrbRel c₀ c} => Φ c.1 ((N : ℝ) • ![a, b]))).symm
  simp_rw [hsub]
  let F : (Fin 2 → ℤ) → ℝ → ℝ → ℂ := fun ℓ a b => Φ (Q.act ℓ c₀) ((N : ℝ) • ![a, b])
  have hFc : ∀ ℓ, Continuous (Function.uncurry (F ℓ)) := by
    intro ℓ
    exact (hc _).comp ((show Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) by
      fun_prop).const_smul (N : ℝ))
  have hBsum : Summable fun ℓ : Fin 2 → ℤ => B (Q.act ℓ c₀) :=
    hBs.comp_injective (fun ℓ ℓ' h => Q.free c₀ hr h)
  have hFB : ∀ ℓ a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → ‖F ℓ a b‖ ≤ B (Q.act ℓ c₀) :=
    fun ℓ a b ha hb => hBb _ _ (hvbd a b ha hb)
  rw [← tsum_iterIntegral F hFc _ hBsum hFB]
  -- the tiling of the plane by the squares `ℓ + [0,1]²`
  have hgc : Continuous fun v : Fin 2 → ℝ => Φ c₀ ((N : ℝ) • v) := (hc c₀).comp (continuous_id.const_smul (N : ℝ))
  have hshift : ∀ (ℓ : Fin 2 → ℤ) (a b : ℝ),
      Φ c₀ ((N : ℝ) • (![(ℓ 0 : ℝ) + a, (ℓ 1 : ℝ) + b] : Fin 2 → ℝ)) = F ℓ a b := by
    intro ℓ a b
    show _ = Φ (Q.act ℓ c₀) _
    rw [h1]
    congr 1
    funext i
    fin_cases i <;> simp [intVec] <;> ring
  obtain ⟨hint, hval⟩ := tiling_pi hgc (fun ℓ => B (Q.act ℓ c₀)) hBsum (fun ℓ a b ha hb => by
    have := hFB ℓ a b ha hb
    rwa [← hshift ℓ a b] at this)
  refine ⟨hint, ?_⟩
  rw [hval]
  refine tsum_congr fun ℓ => ?_
  refine intervalIntegral.integral_congr fun a _ => ?_
  refine intervalIntegral.integral_congr fun b _ => ?_
  exact (hshift ℓ a b).symm

omit [NeZero N] in
/-- **Row `Q, w₀⁻¹`**: the sum over a free orbit of the torus integral is the integral over `ℝ²` of the
orbit representative (unfolding, Fubini). -/
theorem free_orbit_unfold (Φ : Cs → (Fin 2 → ℝ) → ℂ)
    (h1 : ∀ ℓ c v, Φ (Q.act ℓ c) v = Φ c ((N : ℝ) • intVec ℓ + v))
    (hc : ∀ c, Continuous (Φ c))
    (hb : ∀ R : ℝ, ∃ B : Cs → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖Φ c v‖ ≤ B c)
    (c₀ : Cs) (hr : Q.r0 c₀ ≠ 0) :
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
      ∑' c : {c // Q.OrbRel c₀ c}, Φ c.1 ((N : ℝ) • ![a, b]) = ∫ v : Fin 2 → ℝ, Φ c₀ ((N : ℝ) • v) :=
  (free_orbit_unfold_aux Q Φ h1 hc hb c₀ hr).2

/-- **The total averaged coefficient of the line radical**: the torus integral of the sum over all
indices is the sum, over the free orbits, of the `ℝ²` integral of the orbit representative. -/
theorem QAct.total [Countable Cs] (Φ : Cs → (Fin 2 → ℝ) → ℂ)
    (h1 : ∀ ℓ c v, Φ (Q.act ℓ c) v = Φ c ((N : ℝ) • intVec ℓ + v))
    (hc : ∀ c, Continuous (Φ c))
    (hb : ∀ R : ℝ, ∃ B : Cs → ℝ, Summable B ∧ ∀ c v, (∀ i, |v i| ≤ R) → ‖Φ c v‖ ≤ B c)
    (hcl : ∀ c, Q.r0 c = 0 → ∃ k : Fin 2, ∀ w : Fin 2 → ℝ,
      ∫ s in (0 : ℝ)..1, Φ c (w + s • ((N : ℝ) • (Pi.single k 1 : Fin 2 → ℝ))) = 0) :
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, ∑' c, Φ c ((N : ℝ) • ![a, b]) =
      ∑' o : {o : Quotient Q.orbSetoid // Q.r0Q o ≠ 0},
        ∫ v : Fin 2 → ℝ, Φ (Quotient.out o.1) ((N : ℝ) • v) := by
  classical
  obtain ⟨B, hBs, hBb⟩ := hb (N : ℝ)
  let q : Cs → Quotient Q.orbSetoid := fun c => Quotient.mk Q.orbSetoid c
  have hvbd : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → ∀ k : Fin 2,
      |((N : ℝ) • ![a, b]) k| ≤ N := by
    intro a b ha hb k
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
  let G : Quotient Q.orbSetoid → ℝ → ℝ → ℂ := fun o a b =>
    ∑' c : q ⁻¹' {o}, Φ c.1 ((N : ℝ) • ![a, b])
  have hHB : HasSum (fun o : Quotient Q.orbSetoid => ∑' c : q ⁻¹' {o}, B c) (∑' c, B c) :=
    hBs.hasSum.tsum_fiberwise q
  have hfib : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      HasSum (fun o => G o a b) (∑' c, Φ c ((N : ℝ) • ![a, b])) := by
    intro a b ha hb
    have hs : Summable fun c => Φ c ((N : ℝ) • ![a, b]) :=
      Summable.of_norm_bounded hBs (fun c => hBb c _ (hvbd a b ha hb))
    exact hs.hasSum.tsum_fiberwise q
  have hGc : ∀ o, Continuous (Function.uncurry (G o)) := by
    intro o
    have h1' := LatAct.continuous_tsum_set (N := N) Φ hc hb (q ⁻¹' {o})
    exact h1'.comp (show Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) by fun_prop)
  have hGb : ∀ o a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      ‖G o a b‖ ≤ ∑' c : q ⁻¹' {o}, B c := by
    intro o a b ha hb
    exact tsum_of_norm_bounded ((hBs.subtype (q ⁻¹' {o})).hasSum)
      (fun c => hBb c.1 _ (hvbd a b ha hb))
  -- the value of the double integral of one orbit sum
  have hset : ∀ c₀ : Cs, q ⁻¹' {Quotient.mk Q.orbSetoid c₀} = {c | Q.OrbRel c₀ c} := by
    intro c₀
    ext c
    show Quotient.mk Q.orbSetoid c = Quotient.mk Q.orbSetoid c₀ ↔ Q.OrbRel c₀ c
    rw [Quotient.eq]
    exact ⟨fun h => QAct.OrbRel.symm Q h, fun h => QAct.OrbRel.symm Q h⟩
  have hG0 : ∀ o : Quotient Q.orbSetoid, ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, G o a b =
      if Q.r0Q o = 0 then 0 else ∫ v : Fin 2 → ℝ, Φ (Quotient.out o) ((N : ℝ) • v) := by
    intro o
    set c₀ := Quotient.out o with hc₀
    have ho : Quotient.mk Q.orbSetoid c₀ = o := Quotient.out_eq o
    have hset' : q ⁻¹' {o} = {c | Q.OrbRel c₀ c} := by rw [← ho]; exact hset c₀
    have hr0 : Q.r0Q o = Q.r0 c₀ := by rw [← ho]; rfl
    have hGeq : ∀ a b, G o a b = ∑' c : {c // Q.OrbRel c₀ c}, Φ c.1 ((N : ℝ) • ![a, b]) := by
      intro a b
      exact tsum_congr_set_coe (fun c => Φ c ((N : ℝ) • ![a, b])) hset'
    by_cases hr : Q.r0 c₀ = 0
    · rw [hr0, ite_eq_left hr]
      have hG1 : ∀ a b, G o a b = Φ c₀ ((N : ℝ) • ![a, b]) := by
        intro a b
        rw [hGeq]
        rw [tsum_eq_single (⟨c₀, QAct.OrbRel.refl Q c₀⟩ : {c // Q.OrbRel c₀ c})]
        intro c hcne
        exfalso
        obtain ⟨ℓ, hℓ⟩ := c.2
        exact hcne (Subtype.ext (by rw [← hℓ]; exact Q.fix ℓ c₀ hr))
      obtain ⟨k, hk⟩ := hcl c₀ hr
      simp_rw [hG1]
      exact torus_zero_of_axis _ (hc c₀) k hk
    · rw [hr0, ite_eq_right hr]
      simp_rw [hGeq]
      exact free_orbit_unfold Q Φ h1 hc hb c₀ hr
  have hex := tsum_iterIntegral G hGc (fun o => ∑' c : q ⁻¹' {o}, B c) hHB.summable hGb
  calc ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, ∑' c, Φ c ((N : ℝ) • ![a, b])
      = ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, ∑' o, G o a b := by
        refine intervalIntegral.integral_congr fun a ha => ?_
        refine intervalIntegral.integral_congr fun b hb => ?_
        rw [uIcc_of_le zero_le_one] at ha hb
        exact (hfib a b ha hb).tsum_eq.symm
    _ = ∑' o, ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, G o a b := hex.symm
    _ = ∑' o : Quotient Q.orbSetoid, (if Q.r0Q o = 0 then 0 else
          ∫ v : Fin 2 → ℝ, Φ (Quotient.out o) ((N : ℝ) • v)) := tsum_congr hG0
    _ = _ := by
        have hsupp : Function.support (fun o : Quotient Q.orbSetoid =>
            if Q.r0Q o = 0 then (0 : ℂ) else ∫ v : Fin 2 → ℝ, Φ (Quotient.out o) ((N : ℝ) • v)) ⊆
            {o | Q.r0Q o ≠ 0} := by
          intro o ho
          by_contra hcon
          have hz : Q.r0Q o = 0 := not_not.1 hcon
          exact ho (by simp [hz])
        refine (tsum_subtype_eq_of_support_subset hsupp).symm.trans ?_
        refine tsum_congr fun o => ?_
        exact ite_eq_right o.2

end Orbits

end TernaryPeriodPolynomials.Argument.EisensteinClass
