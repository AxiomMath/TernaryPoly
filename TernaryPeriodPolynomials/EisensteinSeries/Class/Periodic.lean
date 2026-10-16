module

public import Mathlib

@[expose] public section


/-!
# Invariance of the unit-square integral of periodic functions under `SL₂(ℤ)`

Paper: "both maps
commute with the lattice-preserving Levi action, which preserves normalized Haar measure": the
Levi block `Γ₂(N) ⊂ SL₂(ℤ)` acts on the torus `ℝ²/Nℤ²` of the radical preserving its normalized
Haar measure.

`sqInt f = ∫₀¹∫₀¹ f(a, b) db da`. For a continuous `ℤ²`-periodic `f` and `A ∈ SL₂(ℤ)` acting
by the real matrix `zAct A`, `sqInt (f ∘ zAct A) = sqInt f` (`sqInt_zAct`). The proof checks the
generators `S`, `T` (Fubini on the unit square, `integral_swap_unit`, and periodicity of the interval
integral) and closes under products and inverses (`SL₂(ℤ) = ⟨S, T⟩`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set intervalIntegral
open scoped MatrixGroups
open ModularGroup

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Swapping iterated interval integrals of a continuous function on the unit square. -/
theorem integral_swap_unit (g : ℝ → ℝ → G) (hg : Continuous (Function.uncurry g)) :
    ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, g a b = ∫ b in (0:ℝ)..1, ∫ a in (0:ℝ)..1, g a b := by
  have hint : Integrable (Function.uncurry g)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have : IntegrableOn (Function.uncurry g) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (volume.prod volume) :=
      hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact this.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simp only [intervalIntegral.integral_of_le zero_le_one]
  exact integral_integral_swap hint

/-- The iterated integral over the unit square. -/
def sqInt (f : (Fin 2 → ℝ) → G) : G := ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, f ![a, b]

/-- The integer translation vector `k ∈ ℤ²` as a real vector. -/
def intVec (k : Fin 2 → ℤ) : Fin 2 → ℝ := fun i => (k i : ℝ)

/-- Periodic with respect to `ℤ²`. -/
def PerZ2 (f : (Fin 2 → ℝ) → G) : Prop := ∀ (v : Fin 2 → ℝ) (k : Fin 2 → ℤ), f (v + intVec k) = f v

/-- The real linear action of an integer matrix. -/
def zAct (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (A.map (Int.castRingHom ℝ)).mulVec v

theorem zAct_add (A : Matrix (Fin 2) (Fin 2) ℤ) (v w : Fin 2 → ℝ) :
    zAct A (v + w) = zAct A v + zAct A w := by
  simp [zAct, Matrix.mulVec_add]

theorem zAct_intVec (A : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin 2 → ℤ) :
    zAct A (intVec k) = intVec (A.mulVec k) := by
  funext i
  simp [zAct, intVec, Matrix.mulVec, dotProduct]

theorem zAct_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℝ) :
    zAct (A * B) v = zAct A (zAct B v) := by
  unfold zAct
  rw [Matrix.map_mul, Matrix.mulVec_mulVec]

theorem zAct_one (v : Fin 2 → ℝ) : zAct 1 v = v := by
  simp [zAct]

theorem continuous_zAct (A : Matrix (Fin 2) (Fin 2) ℤ) : Continuous (zAct A) := by
  unfold zAct
  exact (Matrix.mulVecLin (A.map (Int.castRingHom ℝ))).continuous_of_finiteDimensional

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem PerZ2.comp_zAct {f : (Fin 2 → ℝ) → G} (hf : PerZ2 f) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    PerZ2 (fun v => f (zAct A v)) := by
  intro v k
  simp only [zAct_add, zAct_intVec]
  exact hf _ _

theorem sqInt_zAct_T {f : (Fin 2 → ℝ) → G} (hc : Continuous f) (hp : PerZ2 f) :
    sqInt (fun v => f (zAct (T : Matrix (Fin 2) (Fin 2) ℤ) v)) = sqInt f := by
  have hT : ∀ v : Fin 2 → ℝ, zAct (T : Matrix (Fin 2) (Fin 2) ℤ) v = ![v 0 + v 1, v 1] := by
    intro v; funext i; fin_cases i <;> simp [zAct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  unfold sqInt
  simp only [hT, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcont : Continuous (Function.uncurry fun a b : ℝ => f ![a + b, b]) := by
    refine hc.comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  rw [integral_swap_unit _ hcont]
  have hcont2 : Continuous (Function.uncurry fun a b : ℝ => f ![a, b]) := by
    refine hc.comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  rw [integral_swap_unit _ hcont2]
  refine intervalIntegral.integral_congr fun b _ => ?_
  have hper : Function.Periodic (fun s : ℝ => f ![s, b]) 1 := by
    intro s
    have := hp ![s, b] (fun i => if i = 0 then 1 else 0)
    convert this using 2
    funext i; fin_cases i <;> simp [intVec]
  have := hper.intervalIntegral_add_eq b 0
  simp only [zero_add] at this
  have h2 := intervalIntegral.integral_comp_add_right (fun x => f ![x, b]) (a := 0) (b := 1) b
  simp only [zero_add] at h2
  rw [add_comm 1 b] at h2
  rw [h2]
  exact this

theorem sqInt_zAct_S {f : (Fin 2 → ℝ) → G} (hc : Continuous f) (hp : PerZ2 f) :
    sqInt (fun v => f (zAct (S : Matrix (Fin 2) (Fin 2) ℤ) v)) = sqInt f := by
  have hS : ∀ v : Fin 2 → ℝ, zAct (S : Matrix (Fin 2) (Fin 2) ℤ) v = ![-v 1, v 0] := by
    intro v; funext i; fin_cases i <;> simp [zAct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  unfold sqInt
  simp only [hS, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcont : Continuous (Function.uncurry fun a b : ℝ => f ![-b, a]) := by
    refine hc.comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  rw [integral_swap_unit _ hcont]
  set h : ℝ → G := fun s => ∫ a in (0:ℝ)..1, f ![s, a] with hh
  have hper : Function.Periodic h 1 := by
    intro s
    refine intervalIntegral.integral_congr fun a _ => ?_
    have := hp ![s, a] (fun i => if i = 0 then 1 else 0)
    convert this using 2
    funext i; fin_cases i <;> simp [intVec]
  have h1 : ∫ b in (0:ℝ)..1, ∫ a in (0:ℝ)..1, f ![-b, a] = ∫ b in (0:ℝ)..1, h (-b) := rfl
  rw [h1, intervalIntegral.integral_comp_neg h]
  have := hper.intervalIntegral_add_eq (-1) 0
  rw [show (-1 : ℝ) + 1 = 0 by norm_num, zero_add] at this
  rw [neg_zero]
  exact this

/-- Invariance of the unit-square integral of continuous `ℤ²`-periodic functions. -/
def GoodSL (A : SL(2, ℤ)) : Prop :=
  ∀ f : (Fin 2 → ℝ) → G, Continuous f → PerZ2 f →
    sqInt (fun v => f (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) v)) = sqInt f

/-- **The unit-square integral of a continuous `ℤ²`-periodic function is invariant under
`SL₂(ℤ)`** (generated by `S`, `T`, each handled by Fubini and periodicity). -/
theorem sqInt_zAct (A : SL(2, ℤ)) {f : (Fin 2 → ℝ) → G} (hc : Continuous f) (hp : PerZ2 f) :
    sqInt (fun v => f (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) v)) = sqInt f := by
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {A | GoodSL (G := G) A}
      one_mem' := by
        intro f _ _
        simp [zAct_one]
      mul_mem' := by
        intro A B hA hB f hc hp
        have h1 := hB (fun v => f (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) v))
          (hc.comp (continuous_zAct _)) (hp.comp_zAct _)
        have h2 := hA f hc hp
        have e : (fun v => f (zAct ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) v)) =
            (fun v => (fun w => f (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) w))
              (zAct (B : Matrix (Fin 2) (Fin 2) ℤ) v)) := by
          funext v
          simp only [Matrix.SpecialLinearGroup.coe_mul, zAct_mul]
        rw [e, h1, h2]
      inv_mem' := by
        intro A hA f hc hp
        have h1 := hA (fun v => f (zAct ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) v))
          (hc.comp (continuous_zAct _)) (hp.comp_zAct _)
        have e : (fun v => (fun w => f (zAct ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) w))
            (zAct (A : Matrix (Fin 2) (Fin 2) ℤ) v)) = f := by
          funext v
          simp only [← zAct_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one, zAct_one]
        rw [e] at h1
        exact h1.symm }
  have hST : Subgroup.closure ({S, T} : Set SL(2, ℤ)) ≤ H := by
    rw [Subgroup.closure_le]
    intro B hB
    rcases hB with rfl | rfl
    · exact fun f hc hp => sqInt_zAct_S hc hp
    · exact fun f hc hp => sqInt_zAct_T hc hp
  have hA : A ∈ H := hST (by rw [SpecialLinearGroup.SL2Z_generators]; trivial)
  exact hA f hc hp

end TernaryPeriodPolynomials.Argument.EisensteinClass
