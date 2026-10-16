/-
  Right-invariance of the finite-coset Hecke translate `translateSource` under
  the *rational* finite congruence level, with NO normaliser hypothesis.

  Key simplification: using clause (c) of `IsSourceCocycle` (real-group
  equivariance) with `h = r_ℝ⁻¹`, the component action `φ(r_ℝ)` and the shifted
  real argument cancel, so each Hecke summand is exactly

    φ(r_ℝ)(c(r_ℝ⁻¹ x)(g · atFinite kf · rationalGroup r))
      = c x (g · atFinite (kf · rationalFinite r)).

  Hence the whole average is the finite double-coset average
  `Σ_r c x (g · atFinite (kf · rationalFinite r))`, which is invariant under
  `kf = rationalFinite γ.val` (`γ : rationalLevel`) by reindexing the double
  coset with the permutation `Helpers.representativeMap`.  This is exactly the
  "rational/finite correspondence ... via actual coset reindexing"; the gap to the full compact `finiteLevel`
  (which is strictly larger than the rational finite part) is separate.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HeckeInvariance
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.AveragedHecke
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.Equivariance

@[expose] public section



open GeneralEisenstein
open GeneralEisenstein.Adelic
open Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.TranslateRationalLevel

variable {n : ℕ} {D : InducingData n} {side : Side}

/-- **Cancellation of the component action and real shift.**  Clause (c) applied
with `r_ℝ⁻¹` turns each Hecke summand into the source value at the finite shift
`kf · rationalFinite r`. -/
theorem translateSource_term_eq {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (r : RationalGL3) (x : Fin 3 → RealGL3) (g : AdelicGL)
    (kf : GeneralLinearGroup (Fin 3) FiniteAdeles) :
    realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
      (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
        (g * atFinite kf * rationalGroup r))
    = c x (g * atFinite (kf * rationalFinite r)) := by
  have harg : (g * atFinite kf * rationalGroup r) *
      atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹) =
      g * atFinite (kf * rationalFinite r) := by
    calc
      (g * atFinite kf * rationalGroup r) *
          atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹)
          = (g * atFinite kf) *
              (rationalGroup r * (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) r))⁻¹) := by
              rw [← HeckeInvariance.atInfinity_inv]; group
      _ = (g * atFinite kf) * atFinite (rationalFinite r) := by
              rw [HeckeInvariance.rationalGroup_mul_atInfinity_inv]
      _ = g * (atFinite kf * atFinite (rationalFinite r)) := by group
      _ = g * atFinite (kf * rationalFinite r) := by
              rw [HeckeInvariance.atFinite_mul]
  have h := hc.2.2.1 ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹) x
    (g * atFinite kf * rationalGroup r)
  rw [h, harg, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

theorem atFinite_one :
    atFinite (1 : GeneralLinearGroup (Fin 3) FiniteAdeles) = (1 : AdelicGL) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  by_cases hij : i = j <;> simp [atFinite, combineGL, pairMatrix, hij]

/-- The average as a finite double-coset sum of source values. -/
theorem translateSource_sum_eq (t : HeckeCorrespondence) {c : SourceCochain n}
    (hc : IsSourceCocycle D side c) (x : Fin 3 → RealGL3) (g : AdelicGL)
    (kf : GeneralLinearGroup (Fin 3) FiniteAdeles) :
    HeckeInvariance.translateSource D t c x (g * atFinite kf) =
      ∑ r ∈ t.representatives, c x (g * atFinite (kf * rationalFinite r)) := by
  rw [HeckeInvariance.translateSource]
  apply Finset.sum_congr rfl
  intro r _
  exact translateSource_term_eq hc r x g kf

/-- **Right-invariance under the rational finite congruence level.**  For
`γ : rationalLevel`, the Hecke translate is invariant under right translation by
`atFinite (rationalFinite γ.val)`. -/
theorem translateSource_ratFinite_invariant (t : HeckeCorrespondence) {c : SourceCochain n}
    (hc : IsSourceCocycle D side c) (x : Fin 3 → RealGL3) (γ : rationalLevel)
    (g : AdelicGL) :
    HeckeInvariance.translateSource D t c x (g * atFinite (rationalFinite γ.val)) =
      HeckeInvariance.translateSource D t c x g := by
  have hone : g * atFinite (1 : GeneralLinearGroup (Fin 3) FiniteAdeles) = g := by
    rw [atFinite_one, mul_one]
  rw [translateSource_sum_eq t hc x g (rationalFinite γ.val)]
  conv_rhs => rw [← hone]
  rw [translateSource_sum_eq t hc x g (1 : GeneralLinearGroup (Fin 3) FiniteAdeles)]
  simp only [one_mul]
  rw [← Finset.sum_coe_sort t.representatives]
  conv_rhs => rw [← Finset.sum_coe_sort t.representatives]
  have hbi : Function.Bijective (Helpers.representativeMap t γ) :=
    ⟨Helpers.representativeMap_injective t γ,
      Finite.surjective_of_injective (Helpers.representativeMap_injective t γ)⟩
  have hsum : (∑ r : t.representatives, c x (g * atFinite (rationalFinite r.val))) =
      ∑ r : t.representatives,
        c x (g * atFinite (rationalFinite γ.val * rationalFinite r.val)) := by
    apply Fintype.sum_bijective (Helpers.representativeMap t γ) hbi
      (fun r : t.representatives => c x (g * atFinite (rationalFinite r.val)))
      (fun r : t.representatives =>
        c x (g * atFinite (rationalFinite γ.val * rationalFinite r.val)))
    intro r
    let tgt : t.representatives := Helpers.representativeMap t γ r
    let δ : rationalLevel :=
      ⟨tgt.val⁻¹ * (γ.val⁻¹ * r.val), Helpers.representativeMap_mem t γ r⟩
    have hδinv_mem : rationalFinite δ.val⁻¹ ∈ finiteLevel :=
      AveragedHecke.rationalFinite_mem_of_rationalLevel (rationalLevel.inv_mem δ.property)
    have hsplit : γ.val * tgt.val = r.val * δ.val⁻¹ := by
      have hd : tgt.val * δ.val = γ.val⁻¹ * r.val := by
        show tgt.val * (tgt.val⁻¹ * (γ.val⁻¹ * r.val)) = γ.val⁻¹ * r.val
        group
      calc γ.val * tgt.val = γ.val * (tgt.val * δ.val) * δ.val⁻¹ := by group
        _ = γ.val * (γ.val⁻¹ * r.val) * δ.val⁻¹ := by rw [hd]
        _ = r.val * δ.val⁻¹ := by group
    have hval : c x (g * atFinite (rationalFinite γ.val * rationalFinite tgt.val)) =
        c x (g * atFinite (rationalFinite r.val)) := by
      have hfin : rationalFinite γ.val * rationalFinite tgt.val =
          rationalFinite r.val * rationalFinite δ.val⁻¹ := by
        rw [← map_mul, hsplit, map_mul]
      rw [hfin, ← HeckeInvariance.atFinite_mul, ← mul_assoc]
      exact AveragedHecke.source_level_invariance hc x
        ⟨rationalFinite δ.val⁻¹, hδinv_mem⟩ (g * atFinite (rationalFinite r.val))
    exact hval.symm
  exact hsum.symm

/-- **Single-element normaliser invariance.**  If `u : finiteLevel` conjugates
every representative's finite part back into `finiteLevel`, then the average is
invariant under right translation by `atFinite u.val`.  This is the direct
`finiteLevel`-Shimura statement (no reindexing needed). -/
theorem translateSource_normalizer_invariant (t : HeckeCorrespondence) {c : SourceCochain n}
    (hc : IsSourceCocycle D side c) (x : Fin 3 → RealGL3) (u : finiteLevel)
    (hu : ∀ r ∈ t.representatives,
      (rationalFinite r)⁻¹ * u.val * rationalFinite r ∈ finiteLevel)
    (g : AdelicGL) :
    HeckeInvariance.translateSource D t c x (g * atFinite u.val) =
      HeckeInvariance.translateSource D t c x g := by
  have hone : g * atFinite (1 : GeneralLinearGroup (Fin 3) FiniteAdeles) = g := by
    rw [atFinite_one, mul_one]
  rw [translateSource_sum_eq t hc x g u.val]
  conv_rhs => rw [← hone]
  rw [translateSource_sum_eq t hc x g (1 : GeneralLinearGroup (Fin 3) FiniteAdeles)]
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro r hr
  have hm : u.val * rationalFinite r =
      rationalFinite r * ((rationalFinite r)⁻¹ * u.val * rationalFinite r) := by group
  rw [hm, ← HeckeInvariance.atFinite_mul, ← mul_assoc]
  exact AveragedHecke.source_level_invariance hc x
    ⟨(rationalFinite r)⁻¹ * u.val * rationalFinite r, hu r hr⟩
    (g * atFinite (rationalFinite r))

/-- **Full `finiteLevel`-invariance from the density/decomposition input.**  If
every `k : finiteLevel` factors as `k = d · u` with `d` in the rational finite
level and `u` conjugating every representative's finite part back into
`finiteLevel` (true by density of the diagonal `ℤ`-points in `∏_p ℤ_p`), then the average is invariant under all of `finiteLevel`. -/
theorem translateSource_finiteLevel_invariant_of_decomposition
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (x : Fin 3 → RealGL3) (g : AdelicGL)
    (hdec : ∀ k : finiteLevel, ∃ d : rationalLevel, ∃ u : finiteLevel,
      k.val = rationalFinite d.val * u.val ∧
      (∀ r ∈ t.representatives,
        (rationalFinite r)⁻¹ * u.val * rationalFinite r ∈ finiteLevel)) :
    ∀ k : finiteLevel,
      HeckeInvariance.translateSource D t c x (g * atFinite k.val) =
        HeckeInvariance.translateSource D t c x g := by
  intro k
  obtain ⟨d, u, hk, hu⟩ := hdec k
  rw [hk, ← HeckeInvariance.atFinite_mul, ← mul_assoc]
  rw [translateSource_normalizer_invariant t hc x u hu
    (g * atFinite (rationalFinite d.val))]
  exact translateSource_ratFinite_invariant t hc x d g

/-- `translateSource` is additive in the source cochain (pointwise). -/
theorem translateSource_add (D : InducingData n) (t : HeckeCorrespondence)
    (c₁ c₂ : SourceCochain n) :
    HeckeInvariance.translateSource D t (c₁ + c₂) =
      HeckeInvariance.translateSource D t c₁ + HeckeInvariance.translateSource D t c₂ := by
  funext x g
  simp only [HeckeInvariance.translateSource, Pi.add_apply, map_add, Finset.sum_add_distrib]

/-- `translateSource` vanishes on the zero source cochain. -/
theorem translateSource_zero (D : InducingData n) (t : HeckeCorrespondence) :
    HeckeInvariance.translateSource D t (0 : SourceCochain n) = 0 := by
  funext x g
  simp only [HeckeInvariance.translateSource, Pi.zero_apply, map_zero, Finset.sum_const_zero]

end TernaryPeriodPolynomials.HeckeTranslate.TranslateRationalLevel

end
