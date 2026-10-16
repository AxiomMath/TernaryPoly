module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.ParityCriterion
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.BoundaryValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.U3Kernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.EigenLValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.PositiveEta
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.PositiveE4
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.ParityHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Dimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CommonEigenvector

@[expose] public section


/-!
# Eichler–Shimura injectivity for `Γ₁'(3)`

For every `m` and every twist `e`, the parity-projected period map
`levelPeriodMap m e : S_{m+2}(Γ₁(3)) → H¹(Γ₁'(3), Sym^m ⊗ det^e)` is injective
(`levelPeriodMap_injective_levelThree`).

* A form `f` in the kernel has vanishing moments `∫_0^∞ t^(m-j) f(it) dt` for every interior
  position `0 < j < m` with `e + j` even (`moment_eq_zero_of_levelPeriodMap_eq_zero`: the boundary
  values of the period cocycle and the parity criterion).
* The kernel is stable under the Hecke operators `T_p` (`p ≠ 3`) and `U_3`, which commute, so a
  nonzero kernel contains a joint eigenform. Its moment at `p = m - j` is a nonzero multiple of
  `L(f, p + 1)`, which does not vanish for `p + 1 > (m + 2)/2 + 1` (Euler product). The position
  `j = 1` (`e` odd) or `j = 2` (`e` even) works as soon as `m ≥ 5`, resp. `m ≥ 7`
  (`ker_eq_zero_of_large`).
* For `m ≤ 3` there are no cusp forms. For `m = 4`, and for `m = 5, 6` with `e` even, the space of
  cusp forms is a line spanned by a form that is positive on the imaginary axis, so all its moments
  are nonzero (`ker_eq_zero_of_positive`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane MeasureTheory Module
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (binaryRealGammaOneThree)
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke

namespace TernaryPeriodPolynomials.LevelThreeInjective.Main

/-! ### Moments of forms in the kernel -/

/-- **Moments of a form in the kernel.** -/
theorem moment_eq_zero_of_levelPeriodMap_eq_zero {m : ℕ} {e : ℤ} (f : S m)
    (h0 : levelPeriodMap m e f = 0) (j : Fin (m + 1)) (hj0 : j ≠ 0) (hjm : j ≠ Fin.last m)
    (hpar : Even (e + (j.val : ℤ))) :
    Moment.moment (⇑f) (m - j.val) = 0 := by
  obtain ⟨a, b, hT, hL, hcoord⟩ := BoundaryValues.exists_boundary_values m e f
  have h := ParityCriterion.coord_eq_zero_of_levelPeriodMap_eq_zero f a b hT hL h0 j hj0 hjm hpar
  rw [hcoord j] at h
  have hc : ((m.choose j.val : ℕ) : ℂ) * (-Complex.I) ^ (m - j.val) * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)))
      Complex.I_ne_zero
    exact_mod_cast (Nat.choose_pos (Nat.lt_succ_iff.mp j.isLt)).ne'
  exact (mul_eq_zero.mp h).resolve_left hc

/-- A cusp form that is positive on the imaginary axis has nonzero moments. -/
theorem moment_ne_zero_of_pos {k : ℤ} (f : CuspForm binaryRealGammaOneThree k)
    (hpos : ∀ t : ℝ, 0 < t → 0 < (f (ofComplex (Complex.I * t))).re ∧
      (f (ofComplex (Complex.I * t))).im = 0) (p : ℕ) :
    Moment.moment (⇑f) p ≠ 0 := by
  intro h0
  have hint := BoundaryValues.moment_integrable f p
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  have hmom : Moment.moment (⇑f) p =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ p * f (ofComplex (Complex.I * (t : ℂ))) := rfl
  rw [← hmom, h0, Complex.zero_re] at hre
  have hval : ∀ t ∈ Set.Ioi (0 : ℝ), ((t : ℂ) ^ p * f (ofComplex (Complex.I * t))).re =
      t ^ p * (f (ofComplex (Complex.I * t))).re := by
    intro t _
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hreint : IntegrableOn
      (fun t : ℝ => ((t : ℂ) ^ p * f (ofComplex (Complex.I * t))).re) (Set.Ioi 0) :=
    hint.re
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      fun t : ℝ => ((t : ℂ) ^ p * f (ofComplex (Complex.I * t))).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hval t ht]
    exact (mul_pos (pow_pos ht p) (hpos t ht).1).le
  have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support
      (fun t : ℝ => ((t : ℂ) ^ p * f (ofComplex (Complex.I * t))).re) ∩ Set.Ioi 0 := by
    intro t ht
    refine ⟨?_, ht⟩
    rw [Function.mem_support, hval t ht]
    exact (mul_pos (pow_pos ht p) (hpos t ht).1).ne'
  have hmeas : 0 < volume (Function.support
      (fun t : ℝ => ((t : ℂ) ^ p * f (ofComplex (Complex.I * t))).re) ∩ Set.Ioi 0) := by
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  have hposint := (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hreint).mpr hmeas
  rw [hre] at hposint
  exact lt_irrefl 0 hposint

/-! ### Hecke stability of the kernel -/

/-- `T_p` for `p ≠ 3` and `U_3` for `p = 3`. -/
def op (m : ℕ) (p : Nat.Primes) : Module.End ℂ (S m) :=
  if hp : p.val = 3 then levelThreeU3 ((m : ℤ) + 2) else levelThreeHecke ((m : ℤ) + 2) p hp

theorem op_comm (m : ℕ) (p q : Nat.Primes) (g : S m) : op m p (op m q g) = op m q (op m p g) := by
  unfold op
  by_cases hp : p.val = 3 <;> by_cases hq : q.val = 3
  · simp only [dite_eq_left hp, dite_eq_left hq]
  · simp only [dite_eq_left hp, dite_eq_right hq]
    exact (levelThreeHecke_comm_U3 q hq g).symm
  · simp only [dite_eq_right hp, dite_eq_left hq]
    exact levelThreeHecke_comm_U3 p hp g
  · simp only [dite_eq_right hp, dite_eq_right hq]
    exact levelThreeHecke_comm p q hp hq g

theorem tp_mem {m : ℕ} {e : ℤ} (hm : 0 < m) (p : Nat.Primes) (hp : p.val ≠ 3) {g : S m}
    (hg : levelPeriodMap m e g = 0) :
    levelPeriodMap m e (levelThreeHecke ((m : ℤ) + 2) p hp g) = 0 := by
  have h := LevelThreePeriodParityHecke.levelHecke_levelPeriodMap e p hp hm g
  rw [hg, map_zero, map_smul] at h
  have hne : ((p.val : ℂ) ^ (-e)) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast p.property.ne_zero)
  exact (smul_eq_zero.mp h.symm).resolve_left hne

theorem op_mem {m : ℕ} {e : ℤ} (hm : 0 < m) (p : Nat.Primes) {g : S m}
    (hg : levelPeriodMap m e g = 0) : levelPeriodMap m e (op m p g) = 0 := by
  unfold op
  by_cases hp : p.val = 3
  · rw [dite_eq_left hp]
    exact U3Kernel.levelPeriodMap_U3_eq_zero m e hm g hg
  · rw [dite_eq_right hp]
    exact tp_mem hm p hp hg

/-! ### The generic case: Hecke eigenforms and `L`-values -/

/-- **Injectivity in the convergent range.** -/
theorem ker_eq_zero_of_large {m : ℕ} {e : ℤ} (hm : 0 < m) (j : Fin (m + 1)) (hj0 : j ≠ 0)
    (hjm : j ≠ Fin.last m) (hpar : Even (e + (j.val : ℤ)))
    (hbig : (((m : ℤ) + 2 : ℤ) : ℝ) / 2 + 1 < ((m - j.val : ℕ) : ℝ) + 1)
    (f : S m) (hf : levelPeriodMap m e f = 0) : f = 0 := by
  have hfd : FiniteDimensional ℂ (S m) := SturmBound.cuspForm_finiteDimensional ((m : ℤ) + 2)
  by_contra hne
  let K := LinearMap.ker (levelPeriodMap m e)
  have hstable : ∀ (p : Nat.Primes) (g : S m), g ∈ K → op m p g ∈ K := fun p g hg =>
    LinearMap.mem_ker.mpr (op_mem hm p (LinearMap.mem_ker.mp hg))
  have hnt : Nontrivial K := by
    refine nontrivial_of_ne (⟨f, LinearMap.mem_ker.mpr hf⟩ : K) 0 ?_
    intro h
    exact hne (congrArg Subtype.val h)
  let ops : Nat.Primes → Module.End ℂ K := fun p => (op m p).restrict (hstable p)
  have hcomm : ∀ p q, Commute (ops p) (ops q) := by
    intro p q
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    exact op_comm m p q g.val
  obtain ⟨v, eigen, hv0, hv⟩ := commuting_family_exists_eigenvector ops hcomm
  have hval : ∀ p, op m p v.val = eigen p • v.val := fun p => congrArg Subtype.val (hv p)
  have hT : ∀ (p : Nat.Primes) (hp : p.val ≠ 3),
      levelThreeHecke ((m : ℤ) + 2) p hp v.val = eigen p • v.val := by
    intro p hp
    have h := hval p
    unfold op at h
    rw [dite_eq_right hp] at h
    exact h
  have hU : levelThreeU3 ((m : ℤ) + 2) v.val = eigen ⟨3, Nat.prime_three⟩ • v.val := by
    have h := hval ⟨3, Nat.prime_three⟩
    unfold op at h
    rw [dite_eq_left (show (⟨3, Nat.prime_three⟩ : Nat.Primes).val = 3 from rfl)] at h
    exact h
  have hv0' : v.val ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hk : (0 : ℤ) < (m : ℤ) + 2 := by omega
  have hne0 := EigenLValue.moment_ne_zero_of_jointEigen hk v.val hv0' eigen hT hU
    (m - j.val) hbig
  exact hne0 (moment_eq_zero_of_levelPeriodMap_eq_zero v.val (LinearMap.mem_ker.mp v.property)
    j hj0 hjm hpar)

/-! ### Small weights: a positive spanning form -/

/-- **Injectivity when the cusp forms are a line spanned by a positive form.** -/
theorem ker_eq_zero_of_positive {m : ℕ} {e : ℤ} (hdim : finrank ℂ (S m) = 1) (f₀ : S m)
    (hf₀ : f₀ ≠ 0)
    (hpos : ∀ t : ℝ, 0 < t → 0 < (f₀ (ofComplex (Complex.I * t))).re ∧
      (f₀ (ofComplex (Complex.I * t))).im = 0)
    (j : Fin (m + 1)) (hj0 : j ≠ 0) (hjm : j ≠ Fin.last m) (hpar : Even (e + (j.val : ℤ)))
    (f : S m) (hf : levelPeriodMap m e f = 0) : f = 0 := by
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' f₀ hf₀).mp hdim f
  by_cases hc : c = 0
  · rw [hc, zero_smul]
  · exfalso
    rw [map_smul] at hf
    have h0 : levelPeriodMap m e f₀ = 0 := (smul_eq_zero.mp hf).resolve_left hc
    exact moment_ne_zero_of_pos f₀ hpos (m - j.val)
      (moment_eq_zero_of_levelPeriodMap_eq_zero f₀ h0 j hj0 hjm hpar)

theorem finrank_S (m : ℕ) : finrank ℂ (S m) = (m + 2) / 3 - 1 :=
  LevelThreePeriodDimension.finrank_cuspForm_eq' (m := m)

/-! ### The theorem -/

/-- **Eichler–Shimura injectivity for `Γ₁'(3)`.** For every `m` and every twist `e`, the
parity-projected period map `S_{m+2}(Γ₁(3)) → H¹(Γ₁'(3), Sym^m ⊗ det^e)` is injective. -/
theorem levelPeriodMap_injective_levelThree (m : ℕ) (e : ℤ) :
    Function.Injective (levelPeriodMap m e) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  rw [LinearMap.mem_ker] at hf
  have hfd : FiniteDimensional ℂ (S m) := SturmBound.cuspForm_finiteDimensional ((m : ℤ) + 2)
  rcases Nat.lt_or_ge m 4 with hsmall | hm4
  · -- no cusp forms of weight `m + 2 ≤ 5`
    have hzero : finrank ℂ (S m) = 0 := by
      rw [finrank_S]
      omega
    have hsub : Subsingleton (S m) := Module.finrank_zero_iff.mp hzero
    exact Subsingleton.elim f 0
  rcases Int.even_or_odd e with he | he
  · -- even twist: position `j = 2`
    obtain ⟨j, hjv⟩ : ∃ j : Fin (m + 1), j.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
    have hj0 : j ≠ 0 := fun h => by
      have := congrArg Fin.val h
      rw [Fin.val_zero] at this
      omega
    have hjm : j ≠ Fin.last m := fun h => by
      have := congrArg Fin.val h
      rw [Fin.val_last] at this
      omega
    have hpar : Even (e + (j.val : ℤ)) := by
      rw [hjv]
      exact he.add ⟨1, by norm_num⟩
    rcases Nat.lt_or_ge m 7 with hm7 | hm7
    · have hcases : m = 4 ∨ m = 5 ∨ m = 6 := by omega
      rcases hcases with rfl | rfl | rfl
      · obtain ⟨f₀, hf₀, hpos⟩ := PositiveEta.exists_positive_form_four
        exact ker_eq_zero_of_positive ((finrank_S _).trans (by norm_num)) f₀ hf₀ hpos j hj0 hjm
          hpar f hf
      · obtain ⟨f₀, hf₀, hpos⟩ := PositiveE4.exists_positive_form_five
        exact ker_eq_zero_of_positive ((finrank_S _).trans (by norm_num)) f₀ hf₀ hpos j hj0 hjm
          hpar f hf
      · obtain ⟨f₀, hf₀, hpos⟩ := PositiveE4.exists_positive_form_six
        exact ker_eq_zero_of_positive ((finrank_S _).trans (by norm_num)) f₀ hf₀ hpos j hj0 hjm
          hpar f hf
    · refine ker_eq_zero_of_large (by omega) j hj0 hjm hpar ?_ f hf
      rw [hjv, Nat.cast_sub (by omega : 2 ≤ m)]
      push_cast
      have : (7 : ℝ) ≤ m := by exact_mod_cast hm7
      linarith
  · -- odd twist: position `j = 1`
    obtain ⟨j, hjv⟩ : ∃ j : Fin (m + 1), j.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
    have hj0 : j ≠ 0 := fun h => by
      have := congrArg Fin.val h
      rw [Fin.val_zero] at this
      omega
    have hjm : j ≠ Fin.last m := fun h => by
      have := congrArg Fin.val h
      rw [Fin.val_last] at this
      omega
    have hpar : Even (e + (j.val : ℤ)) := by
      rw [hjv, Nat.cast_one]
      exact he.add_one
    rcases Nat.lt_or_ge m 5 with hm5 | hm5
    · have hm : m = 4 := by omega
      subst hm
      obtain ⟨f₀, hf₀, hpos⟩ := PositiveEta.exists_positive_form_four
      exact ker_eq_zero_of_positive ((finrank_S _).trans (by norm_num)) f₀ hf₀ hpos j hj0 hjm
        hpar f hf
    · refine ker_eq_zero_of_large (by omega) j hj0 hjm hpar ?_ f hf
      rw [hjv, Nat.cast_sub (by omega : 1 ≤ m)]
      push_cast
      have : (5 : ℝ) ≤ m := by exact_mod_cast hm5
      linarith

/-- The form needed for the good-plane bound (`GoodPlaneBoundExport`): twist `e = -1`. -/
theorem levelPeriodMap_injective_goodPlane (n : ℕ) :
    Function.Injective (levelPeriodMap (n + 1) (-1)) :=
  levelPeriodMap_injective_levelThree (n + 1) (-1)

/-- The form needed for the bad-line bound (`BadLineUpper`): twist `e = 0`. -/
theorem levelPeriodMap_injective_badLine (n : ℕ) :
    Function.Injective (levelPeriodMap (n + 1) 0) :=
  levelPeriodMap_injective_levelThree (n + 1) 0

end TernaryPeriodPolynomials.LevelThreeInjective.Main
