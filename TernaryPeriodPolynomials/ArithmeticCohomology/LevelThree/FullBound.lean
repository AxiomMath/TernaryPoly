module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SharpBounds

@[expose] public section


/-!
# Full first cohomology of the level-three Levi `Γ₁'(3)`

The boundary contribution: a class of `H¹(Γ₁'(3), Sym^m ⊗ det^e)` is parabolic iff its values
`z(T)(1, 0)` and `z(L)(0, 1)` vanish (`(T - 1)V` and `(L - 1)V` are exactly these hyperplanes), and
the reflection `ε = diag(-1, 1)` forces `z(T)(1, 0) = 0` when `e + m` is even and `z(L)(0, 1) = 0`
when `e` is even. Hence (`finrank_level_H1_le_sharp`)

`dim H¹(Γ₁'(3), Sym^m ⊗ det^e) + 1 ≤ ⌊(m + 2)/3⌋ + [e + m odd] + [e odd]`,

i.e. `dim S_{m+2}(Γ₁(3))` plus one Eisenstein dimension for each cusp whose stabilizer has
nonzero cohomology. For the bad-line coefficient (`e = 0`, `m = degree + 1`):
`finrank_binaryArithmetic_H1_le` gives `dim + 1 ≤ ⌊(degree + 3)/3⌋ + [degree even]`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.FullBound

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators LowDegreeParabolic
open TwoGenerator GammaOneThree SymFixed ParabolicBounds ReflectionBound SharpBounds
open GeneralEisenstein Module Matrix MvPolynomial

section Hyperplanes

variable {m : ℕ} (e : ℤ)

theorem evalAt_powerVector_zero : SymFixed.evalAt (m := m) ![1, 0] (powerVector 0 m) = 1 := by
  change eval ![1, 0] ((X 0 : Binary.Poly) ^ m) = 1
  simp

theorem evalAt_powerVector_one : SymFixed.evalAt (m := m) ![0, 1] (powerVector 1 m) = 1 := by
  change eval ![0, 1] ((X 1 : Binary.Poly) ^ m) = 1
  simp

theorem finrank_ker_evalAt (x : Fin 2 → ℂ) (v : Binary.HomogeneousPoly m) (hv : SymFixed.evalAt x v = 1) :
    finrank ℂ (LinearMap.ker (SymFixed.evalAt (m := m) x)) = m := by
  have rank_nullity := LinearMap.finrank_range_add_finrank_ker (SymFixed.evalAt (m := m) x)
  have range_top : LinearMap.range (SymFixed.evalAt (m := m) x) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact ⟨c • v, by rw [map_smul, hv, smul_eq_mul, mul_one]⟩
  rw [range_top, finrank_top, Module.finrank_self, finrank_sym] at rank_nullity
  omega

theorem movedSpace_upper_eq {c : ℂ} (hc : c ≠ 0) :
    movedSpace (m := m) e (upperC c) = LinearMap.ker (SymFixed.evalAt ![1, 0]) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro w hw
    rw [LinearMap.mem_ker]
    exact eval_upper_moved e c w hw
  · have rank_nullity := LinearMap.finrank_range_add_finrank_ker
      (Binary.homogeneousAction m e (upperC c) - 1)
    rw [finrank_sym] at rank_nullity
    change finrank ℂ (movedSpace e (upperC c)) + finrank ℂ (fixedSpace e (upperC c)) = _
      at rank_nullity
    rw [finrank_fixed_upper e hc] at rank_nullity
    rw [finrank_ker_evalAt _ _ evalAt_powerVector_zero]
    omega

theorem eval_lower_moved (c : ℂ) (w : Binary.HomogeneousPoly m)
    (hw : w ∈ movedSpace e (lowerC c)) : eval ![0, 1] w.val = 0 := by
  obtain ⟨v, rfl⟩ := hw
  change eval ![0, 1] ((Binary.homogeneousAction m e (lowerC c) v).val - v.val) = 0
  rw [map_sub, Binary.homogeneousAction_coe, eval_lower]
  simp

theorem movedSpace_lower_eq {c : ℂ} (hc : c ≠ 0) :
    movedSpace (m := m) e (lowerC c) = LinearMap.ker (SymFixed.evalAt ![0, 1]) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro w hw
    rw [LinearMap.mem_ker]
    exact eval_lower_moved e c w hw
  · have rank_nullity := LinearMap.finrank_range_add_finrank_ker
      (Binary.homogeneousAction m e (lowerC c) - 1)
    rw [finrank_sym] at rank_nullity
    change finrank ℂ (movedSpace e (lowerC c)) + finrank ℂ (fixedSpace e (lowerC c)) = _
      at rank_nullity
    rw [finrank_fixed_lower e hc] at rank_nullity
    rw [finrank_ker_evalAt _ _ evalAt_powerVector_one]
    omega

end Hyperplanes

section Values

variable {m : ℕ} (e : ℤ)

theorem rho_inv_cancel {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem ev10_T (v : Binary.HomogeneousPoly m) :
    eval ![1, 0] (levelRep m e (upper 1) v).val = eval ![1, 0] v.val := by
  rw [levelRep_T, Binary.homogeneousAction_coe, eval_upper]
  simp

theorem ev10_T_inv (v : Binary.HomogeneousPoly m) :
    eval ![1, 0] (levelRep m e (upper 1)⁻¹ v).val = eval ![1, 0] v.val := by
  have h := ev10_T e (levelRep m e (upper 1)⁻¹ v)
  rw [rho_inv_cancel] at h
  exact h.symm

theorem ev10_ε (v : Binary.HomogeneousPoly m) :
    eval ![1, 0] (levelRep m e reflection v).val =
      (-1 : ℂ) ^ e * (-1 : ℂ) ^ m * eval ![1, 0] v.val := by
  rw [levelRep_ε, Binary.homogeneousAction_coe, eval_reflection]
  have h := eval_smul_of_homogeneous (isHomogeneous v) (-1) ![1, 0]
  rw [show (-1 : ℂ) • ![(1 : ℂ), 0] = ![-1, 0] by
    funext i; fin_cases i <;> simp] at h
  rw [h, mul_assoc]

theorem ev01_L (v : Binary.HomogeneousPoly m) :
    eval ![0, 1] (levelRep m e (lower 1) v).val = eval ![0, 1] v.val := by
  rw [levelRep_L, Binary.homogeneousAction_coe, eval_lower]
  simp

theorem ev01_L_inv (v : Binary.HomogeneousPoly m) :
    eval ![0, 1] (levelRep m e (lower 1)⁻¹ v).val = eval ![0, 1] v.val := by
  have h := ev01_L e (levelRep m e (lower 1)⁻¹ v)
  rw [rho_inv_cancel] at h
  exact h.symm

theorem ev01_ε (v : Binary.HomogeneousPoly m) :
    eval ![0, 1] (levelRep m e reflection v).val = (-1 : ℂ) ^ e * eval ![0, 1] v.val := by
  rw [levelRep_ε, Binary.homogeneousAction_coe, eval_reflection, neg_zero]

/-- The reflection relation at the cusp `∞`: `(s + 1) z(T)(1,0) = 0`, `s = (-1)^{e+m}`. -/
theorem ev10_cocycle (z : crossedCocycles (levelRep m e)) :
    ((-1 : ℂ) ^ e * (-1 : ℂ) ^ m + 1) * eval ![1, 0] (z.val (upper 1)).val = 0 := by
  set s : ℂ := (-1 : ℂ) ^ e * (-1 : ℂ) ^ m
  have h1 := cocycle_inv z (upper 1)
  have h2 : z.val (reflection * upper 1 * reflection) = z.val reflection +
      levelRep m e reflection (z.val (upper 1)) +
        levelRep m e reflection (levelRep m e (upper 1) (z.val reflection)) := by
    rw [cocycle_mul, cocycle_mul, map_mul, Module.End.mul_apply]
  rw [hεT, h1] at h2
  have hsq := cocycle_mul z reflection reflection
  rw [reflection_mul_self, cocycle_one] at hsq
  have value := congrArg (fun w : Binary.HomogeneousPoly m => eval ![1, 0] w.val) h2
  have valueSq := congrArg (fun w : Binary.HomogeneousPoly m => eval ![1, 0] w.val) hsq
  simp only [Submodule.coe_add, Submodule.coe_neg, map_add, map_neg, ZeroMemClass.coe_zero,
    map_zero] at value valueSq
  rw [ev10_T_inv, ev10_ε, ev10_ε, ev10_T] at value
  rw [ev10_ε] at valueSq
  linear_combination -value + valueSq

/-- The reflection relation at the cusp `0`: `(t + 1) z(L)(0,1) = 0`, `t = (-1)^e`. -/
theorem ev01_cocycle (z : crossedCocycles (levelRep m e)) :
    ((-1 : ℂ) ^ e + 1) * eval ![0, 1] (z.val (lower 1)).val = 0 := by
  set t : ℂ := (-1 : ℂ) ^ e
  have h1 := cocycle_inv z (lower 1)
  have h2 : z.val (reflection * lower 1 * reflection) = z.val reflection +
      levelRep m e reflection (z.val (lower 1)) +
        levelRep m e reflection (levelRep m e (lower 1) (z.val reflection)) := by
    rw [cocycle_mul, cocycle_mul, map_mul, Module.End.mul_apply]
  rw [hεL, h1] at h2
  have hsq := cocycle_mul z reflection reflection
  rw [reflection_mul_self, cocycle_one] at hsq
  have value := congrArg (fun w : Binary.HomogeneousPoly m => eval ![0, 1] w.val) h2
  have valueSq := congrArg (fun w : Binary.HomogeneousPoly m => eval ![0, 1] w.val) hsq
  simp only [Submodule.coe_add, Submodule.coe_neg, map_add, map_neg, ZeroMemClass.coe_zero,
    map_zero] at value valueSq
  rw [ev01_L_inv, ev01_ε, ev01_ε, ev01_L] at value
  rw [ev01_ε] at valueSq
  linear_combination -value + valueSq

end Values

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- Cutting by one functional lowers the dimension by at most one, and not at all if it is zero. -/
theorem finrank_le_inf_ker_add {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (S : Submodule ℂ M) (f : M →ₗ[ℂ] ℂ) (P : Prop) [Decidable P] (hP : P → f = 0) :
    finrank ℂ S ≤ finrank ℂ (S ⊓ LinearMap.ker f : Submodule ℂ M) + if P then 0 else 1 := by
  by_cases hp : P
  · rw [ite_eq_left hp, hP hp, LinearMap.ker_zero, inf_top_eq, add_zero]
  · rw [ite_eq_right hp]
    have sup_inf := Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker f)
    have sup_le := Submodule.finrank_le (S ⊔ LinearMap.ker f)
    have rank_nullity := LinearMap.finrank_range_add_finrank_ker f
    have range_le := Submodule.finrank_le (LinearMap.range f)
    rw [Module.finrank_self] at range_le
    omega

/-- A cocycle is determined by its values on three generators. -/
theorem cocycles_finiteDimensional_three [FiniteDimensional ℂ V] (T L ε : G)
    (gen : Subgroup.closure ({T, L, ε} : Set G) = ⊤) : FiniteDimensional ℂ (crossedCocycles ρ) := by
  let values : crossedCocycles ρ →ₗ[ℂ] V × V × V :=
    (TwoGenerator.evalAt ρ T).prod ((TwoGenerator.evalAt ρ L).prod (TwoGenerator.evalAt ρ ε))
  have injective : Function.Injective values := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    have hT : z.val T = 0 := congrArg Prod.fst hz
    have hL : z.val L = 0 := congrArg (fun p => p.2.1) hz
    have hε : z.val ε = 0 := congrArg (fun p => p.2.2) hz
    apply cocycle_ext_of_closure gen
    intro s hs
    rcases hs with rfl | rfl | rfl
    · exact hT
    · exact hL
    · exact hε
  exact Module.Finite.of_injective values injective

variable {ρ}

/-- **Boundary cut**: if `(T - 1)V = ker φ₁` and `(L - 1)V = ker φ₂`, then
`dim H¹ ≤ dim H¹_par + c₁ + c₂`, where `cᵢ = 0` whenever `φᵢ` kills all cocycle values. -/
theorem finrank_H1_le_parabolic_add [FiniteDimensional ℂ (crossedCocycles ρ)] (T L : G)
    (φ₁ φ₂ : V →ₗ[ℂ] ℂ) (h₁ : moved ρ T = LinearMap.ker φ₁) (h₂ : moved ρ L = LinearMap.ker φ₂)
    (P₁ P₂ : Prop) [Decidable P₁] [Decidable P₂]
    (hP₁ : P₁ → ∀ z : crossedCocycles ρ, φ₁ (z.val T) = 0)
    (hP₂ : P₂ → ∀ z : crossedCocycles ρ, φ₂ (z.val L) = 0) :
    finrank ℂ (CrossedH1 ρ) ≤ finrank ℂ (parabolicH1 ρ T L) +
      (if P₁ then 0 else 1) + (if P₂ then 0 else 1) := by
  let Ψ₁ : crossedCocycles ρ →ₗ[ℂ] ℂ := φ₁.comp (TwoGenerator.evalAt ρ T)
  let Ψ₂ : crossedCocycles ρ →ₗ[ℂ] ℂ := φ₂.comp (TwoGenerator.evalAt ρ L)
  have le₁ : crossedBoundaries ρ ≤ LinearMap.ker Ψ₁ := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    change φ₁ (ρ T v - v) = 0
    rw [← LinearMap.mem_ker, ← h₁]
    exact sub_mem_moved ρ T v
  have le₂ : crossedBoundaries ρ ≤ LinearMap.ker Ψ₂ := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    change φ₂ (ρ L v - v) = 0
    rw [← LinearMap.mem_ker, ← h₂]
    exact sub_mem_moved ρ L v
  let Φ₁ : CrossedH1 ρ →ₗ[ℂ] ℂ := (crossedBoundaries ρ).liftQ Ψ₁ le₁
  let Φ₂ : CrossedH1 ρ →ₗ[ℂ] ℂ := (crossedBoundaries ρ).liftQ Ψ₂ le₂
  have zero₁ : P₁ → Φ₁ = 0 := by
    intro hp
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact hP₁ hp z
  have zero₂ : P₂ → Φ₂ = 0 := by
    intro hp
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact hP₂ hp z
  have kernel : (⊤ : Submodule ℂ (CrossedH1 ρ)) ⊓ LinearMap.ker Φ₁ ⊓ LinearMap.ker Φ₂ ≤
      parabolicH1 ρ T L := by
    rintro x ⟨⟨_, hx₁⟩, hx₂⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hx₁ hx₂
    refine ⟨z, ⟨?_, ?_⟩, rfl⟩
    · rw [h₁, LinearMap.mem_ker]
      exact hx₁
    · rw [h₂, LinearMap.mem_ker]
      exact hx₂
  have step1 := finrank_le_inf_ker_add (⊤ : Submodule ℂ (CrossedH1 ρ)) Φ₁ P₁ zero₁
  have step2 := finrank_le_inf_ker_add ((⊤ : Submodule ℂ (CrossedH1 ρ)) ⊓ LinearMap.ker Φ₁)
    Φ₂ P₂ zero₂
  have step3 := Submodule.finrank_mono kernel
  rw [finrank_top] at step1
  omega

end Abstract

section Main

variable {m : ℕ} (e : ℤ)

theorem neg_one_zpow_mul_pow (n : ℕ) : (-1 : ℂ) ^ e * (-1 : ℂ) ^ n = (-1 : ℂ) ^ (e + n) := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]

theorem moved_T_eq : moved (levelRep m e) (upper 1) = LinearMap.ker (SymFixed.evalAt ![1, 0]) := by
  rw [← movedSpace_upper_eq e one_ne_zero]
  unfold moved
  rw [levelRep_T]

theorem moved_L_eq : moved (levelRep m e) (lower 1) = LinearMap.ker (SymFixed.evalAt ![0, 1]) := by
  rw [← movedSpace_lower_eq e three_ne_zero]
  unfold moved
  rw [levelRep_L]

theorem cusp_infinity_zero (even : Even (e + m)) (z : crossedCocycles (levelRep m e)) :
    SymFixed.evalAt ![1, 0] (z.val (upper 1)) = 0 := by
  have h := ev10_cocycle e z
  rw [neg_one_zpow_mul_pow, even.neg_one_zpow] at h
  have two : (2 : ℂ) * eval ![1, 0] (z.val (upper 1)).val = 0 := by linear_combination h
  exact (mul_eq_zero.mp two).resolve_left two_ne_zero

theorem cusp_zero_zero (even : Even e) (z : crossedCocycles (levelRep m e)) :
    SymFixed.evalAt ![0, 1] (z.val (lower 1)) = 0 := by
  have h := ev01_cocycle e z
  rw [even.neg_one_zpow] at h
  have two : (2 : ℂ) * eval ![0, 1] (z.val (lower 1)).val = 0 := by linear_combination h
  exact (mul_eq_zero.mp two).resolve_left two_ne_zero

/-- **`dim H¹(Γ₁'(3), Sym^m ⊗ det^e) ≤ dim H¹_par + [e + m odd] + [e odd]`**. -/
theorem finrank_level_H1_le_parabolic :
    finrank ℂ (CrossedH1 (levelRep m e)) ≤ finrank ℂ (parabolicH1 (levelRep m e) (upper 1) (lower 1)) +
      (if Even (e + m) then 0 else 1) + (if Even e then 0 else 1) := by
  have := cocycles_finiteDimensional_three (levelRep m e) (upper 1) (lower 1) reflection level_closure
  exact finrank_H1_le_parabolic_add (upper 1) (lower 1) _ _ (moved_T_eq e) (moved_L_eq e)
    (Even (e + m)) (Even e) (fun h => cusp_infinity_zero e h) (fun h => cusp_zero_zero e h)

/-- **Sharp full bound**:
`dim H¹(Γ₁'(3), Sym^m ⊗ det^e) + 1 ≤ ⌊(m + 2)/3⌋ + [e + m odd] + [e odd]` (`m > 0`). -/
theorem finrank_level_H1_le_sharp (positive : 0 < m) :
    finrank ℂ (CrossedH1 (levelRep m e)) + 1 ≤
      (m + 2) / 3 + (if Even (e + m) then 0 else 1) + (if Even e then 0 else 1) := by
  have h := finrank_level_H1_le_parabolic (m := m) e
  have p := finrank_level_parabolicH1_le e positive
  omega

/-- **The bad-line Levi cohomology**:
`dim H¹(Γ₁'(3), Sym^{degree+1}) + 1 ≤ ⌊(degree + 3)/3⌋ + [degree even]`. -/
theorem finrank_binaryArithmetic_H1_le (degree : ℕ) :
    finrank ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) + 1 ≤
      (degree + 3) / 3 + (if Even degree then 1 else 0) := by
  have h := finrank_level_H1_le_sharp (m := degree + 1) 0 (Nat.succ_pos degree)
  change finrank ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) + 1 ≤ _ at h
  have parity : Even ((0 : ℤ) + ((degree + 1 : ℕ) : ℤ)) ↔ ¬ Even degree := by
    rw [zero_add, Int.even_coe_nat, Nat.even_add_one]
  have h0 : Even (0 : ℤ) := ⟨0, rfl⟩
  by_cases hd : Even degree
  · rw [ite_eq_right (by rw [parity]; exact not_not.mpr hd), ite_eq_left h0] at h
    rw [ite_eq_left hd]
    omega
  · rw [ite_eq_left (parity.mpr hd), ite_eq_left h0] at h
    rw [ite_eq_right hd]
    omega

end Main

end TernaryPeriodPolynomials.LevelThree.FullBound
