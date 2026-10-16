module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.Limit
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REBadMain

@[expose] public section


/-!
# Normalization of the finite-entry eigenform

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.TwistedSource

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

/-- N1: the weight exceeds six. Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem entry_weight_gt_six {n : ℕ} {D : InducingData n} (S : Entry.SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (_hv : I.vector = S.vector) :
    6 < -2 * I.halfWeight := by
  have hS := S.weight
  have hlarge : (3 : ℤ) < (n : ℤ) := by exact_mod_cast S.large
  rw [hw]
  omega

/-- N4: the classical form of an Eichler input realizes the scalar function exactly.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem classicalFormOfEichlerInput_coe {σ : CuspidalRepresentation} {n : ℕ} (I : EichlerInput σ n) :
    (⇑(classicalFormOfEichlerInput I) : UpperHalfPlane → ℂ) =
      cuspScalarWeightedLinear σ I.halfWeight 1 I.vector := by
  unfold classicalFormOfEichlerInput
  exact cuspClassicalFormMap_coe σ I.halfWeight (eichlerInput_halfWeight_neg I)
    ⟨I.vector, eichlerInput_mem_classical I⟩

/-- The Fourier coefficient at level one equals the `q`-expansion coefficient at width one.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem fourierCoeff_eq_qExpansion_one {k : ℤ} (f : CuspForm levelOne k) (m : ℕ) :
    fourierCoeff f m = (UpperHalfPlane.qExpansion 1 f).coeff m := by
  unfold fourierCoeff
  rw [Subgroup.strictWidthInfty_SL2Z]

/-- N3 (unconditional): the entry value is the `L`-ratio of `S.form` itself.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem value_eq_LRatio {n : ℕ} {D : InducingData n} (S : Entry.SphericalEntryData D) :
    S.value = LSeries (removeEulerCoefficients (fun m => fourierCoeff S.form m) 3)
        (((-2 * S.halfWeight : ℤ) : ℂ) - 2) /
      LSeries (removeEulerCoefficients (fun m => fourierCoeff S.form m) 3)
        (((-2 * S.halfWeight : ℤ) : ℂ) - 1) := by
  unfold Entry.SphericalEntryData.value
  simp only [fourierCoeff_eq_qExpansion_one]

/-- N3 (any representative): for any level-one form with the same underlying function as `S.form`, the
entry value is its `L`-ratio.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem value_eq_LRatio_of_form_eq {n : ℕ} {D : InducingData n} (S : Entry.SphericalEntryData D)
    (h : CuspForm levelOne (-2 * S.halfWeight)) (hform : (⇑h : UpperHalfPlane → ℂ) = ⇑S.form) :
    S.value = LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3)
        (((-2 * S.halfWeight : ℤ) : ℂ) - 2) /
      LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3)
        (((-2 * S.halfWeight : ℤ) : ℂ) - 1) := by
  have hEq : h = S.form := DFunLike.coe_injective hform
  subst hEq
  exact value_eq_LRatio S

/-- Prime Hecke relations are linear: the difference of two forms with the same eigenvalues.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem hecke_relations_sub {w : ℤ} {f₁ f₂ : UpperHalfPlane → ℂ} {μ : Nat.Primes → ℂ}
    (r₁ : HasPrimeHeckeRelations w f₁ μ) (r₂ : HasPrimeHeckeRelations w f₂ μ) :
    HasPrimeHeckeRelations w (f₁ - f₂) μ := by
  intro prime point
  have a := r₁ prime point
  have b := r₂ prime point
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  linear_combination a - b

/-- The Hecke eigenvalue normalization of the classical form: `p^(-h-1) * (p^(h+1) * μ) = μ`.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem zpow_cancel_eigenvalue (p : Nat.Primes) (h : ℤ) (μ : ℂ) :
    (p.val : ℂ) ^ (-h - 1) * ((p.val : ℂ) ^ (h + 1) * μ) = μ := by
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  rw [← mul_assoc, ← zpow_add₀ hp, show -h - 1 + (h + 1) = 0 by ring, zpow_zero, one_mul]

/-- Multiplicity one: two level-one cusp forms with the same prime Hecke eigenvalues are proportional, the
factor being the first coefficient of the first form when the second is normalized.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem fun_eq_smul_of_hecke_relations {k k' : ℤ} (hk : k = k') (g : CuspForm levelOne k)
    (F : CuspForm levelOne k') (μ : Nat.Primes → ℂ) (relations_g : HasPrimeHeckeRelations k ⇑g μ)
    (relations_F : HasPrimeHeckeRelations k' ⇑F μ) (normalized_F : fourierCoeff F 1 = 1) :
    (⇑g : UpperHalfPlane → ℂ) = (UpperHalfPlane.qExpansion 1 g).coeff 1 • ⇑F := by
  subst hk
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  rw [fourierCoeff_eq_qExpansion_one] at normalized_F
  let c : ℂ := (UpperHalfPlane.qExpansion 1 g).coeff 1
  let D : CuspForm levelOne k := g - c • F
  have relations_D : HasPrimeHeckeRelations k ⇑D μ :=
    hecke_relations_sub relations_g (relations_F.smul c)
  have coeff_D : (UpperHalfPlane.qExpansion 1 D).coeff 1 = 0 := by
    have e : (⇑D : UpperHalfPlane → ℂ) = ⇑g - ⇑(c • F) := rfl
    have e2 : (⇑(c • F) : UpperHalfPlane → ℂ) = c • ⇑F := rfl
    rw [e, ModularForm.qExpansion_sub (by norm_num : (0 : ℝ) < 1) period, e2,
      ModularForm.qExpansion_smul (by norm_num : (0 : ℝ) < 1) period]
    simp only [c, map_sub, PowerSeries.coeff_smul, smul_eq_mul, normalized_F, mul_one, sub_self]
  have D_zero : D = 0 := by
    by_contra nonzero
    exact cuspForm_hecke_first_coefficient_ne_zero D period nonzero μ relations_D coeff_D
  have fun_zero : (⇑g : UpperHalfPlane → ℂ) - c • ⇑F = 0 := by
    have := congrArg (fun f : CuspForm levelOne k => (⇑f : UpperHalfPlane → ℂ)) D_zero
    exact this
  exact sub_eq_zero.mp fun_zero

/-- N2' (no new premise): the classical form of the Eichler vector is a scalar multiple of the normalized
eigenform `S.form`, the scalar being its first coefficient.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem classical_eq_smul_form {n : ℕ} {D : InducingData n} (S : Entry.SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) :
    cuspScalarWeightedLinear D.cusp I.halfWeight 1 I.vector =
      fourierCoeff (classicalFormOfEichlerInput I) 1 • (⇑S.form : UpperHalfPlane → ℂ) := by
  have neg := eichlerInput_halfWeight_neg I
  have hol := cuspScalarWeightedRealization_holomorphic D.cusp I.halfWeight I.vector I.vector_spherical
    I.rotation I.holomorphic 1
  have eig : ∀ prime : Nat.Primes, cuspPrimeHeckeSum D.cusp prime I.vector =
      ((prime.val : ℂ) ^ (I.halfWeight + 1) * S.eigenvalues prime) • I.vector := by
    intro prime
    rw [hv, hw]
    exact S.eigen prime
  have key := cuspLevelOneCuspForm_hecke_relations D.cusp I.central_positive I.halfWeight neg I.vector
    I.vector_spherical I.rotation hol
    (fun prime => (prime.val : ℂ) ^ (I.halfWeight + 1) * S.eigenvalues prime) eig
  have eigen_eq : (fun prime : Nat.Primes => (prime.val : ℂ) ^ (-I.halfWeight - 1) *
      ((prime.val : ℂ) ^ (I.halfWeight + 1) * S.eigenvalues prime)) = S.eigenvalues :=
    funext fun prime => zpow_cancel_eigenvalue prime I.halfWeight (S.eigenvalues prime)
  rw [eigen_eq] at key
  have relations_g : HasPrimeHeckeRelations (-2 * I.halfWeight) (⇑(classicalFormOfEichlerInput I))
      S.eigenvalues := by
    have e : (⇑(classicalFormOfEichlerInput I) : UpperHalfPlane → ℂ) =
        ⇑(cuspLevelOneCuspForm_of_holomorphic D.cusp I.halfWeight neg I.vector I.vector_spherical
          I.rotation hol) := by
      rw [classicalFormOfEichlerInput_coe I]
      rfl
    rw [e]
    exact key
  have hk : -2 * I.halfWeight = -2 * S.halfWeight := by rw [hw]
  rw [← classicalFormOfEichlerInput_coe I, fourierCoeff_eq_qExpansion_one]
  exact fun_eq_smul_of_hecke_relations hk (classicalFormOfEichlerInput I) S.form S.eigenvalues relations_g
    S.relations S.normalized

/-- N2' nonvanishing: the first coefficient of the classical form of the Eichler vector is nonzero.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem fourierCoeff_classicalFormOfEichlerInput_one_ne_zero {n : ℕ} {D : InducingData n}
    (S : Entry.SphericalEntryData D) (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight)
    (hv : I.vector = S.vector) : fourierCoeff (classicalFormOfEichlerInput I) 1 ≠ 0 := by
  intro hzero
  have hfun : cuspScalarWeightedLinear D.cusp I.halfWeight 1 I.vector = 0 := by
    rw [classical_eq_smul_form S I hw hv, hzero, zero_smul]
  have hgz : classicalFormOfEichlerInput I = 0 := by
    apply DFunLike.coe_injective
    rw [classicalFormOfEichlerInput_coe I, hfun]
    rfl
  have hinj := cuspClassicalFormMap_injective D.cusp I.central_positive I.halfWeight
    (eichlerInput_halfWeight_neg I)
  have hmem : (⟨I.vector, eichlerInput_mem_classical I⟩ : cuspClassicalVectors D.cusp I.halfWeight) = 0 :=
    hinj (by rw [map_zero]; exact hgz)
  exact I.vector_ne (congrArg Subtype.val hmem)

/-- The Eichler input with the vector rescaled by `c⁻¹`, the halfweight and the rest unchanged.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
def rescaledEichlerInput {σ : CuspidalRepresentation} {n : ℕ} (I : EichlerInput σ n) (c : ℂ) (hc : c ≠ 0) :
    EichlerInput σ n where
  central_positive := I.central_positive
  halfWeight := I.halfWeight
  weight := I.weight
  vector := c⁻¹ • I.vector
  vector_ne := smul_ne_zero (inv_ne_zero hc) I.vector_ne
  vector_spherical := by
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ _ I.vector_spherical
  rotation := fun angle => by
    rw [Submodule.coe_smul, map_smul, I.rotation angle, smul_comm]
  holomorphic := by
    have e : cuspWeightedAffineOrbit σ I.halfWeight (c⁻¹ • I.vector).val =
        fun z => c⁻¹ • cuspWeightedAffineOrbit σ I.halfWeight I.vector.val z := by
      funext z
      unfold cuspWeightedAffineOrbit cuspAffineOrbitVector
      rw [Submodule.coe_smul, map_smul, smul_comm]
    rw [e]
    exact I.holomorphic.const_smul c⁻¹

/-- Transport of a normalized eigenform along an equality of weights.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem transport_normalized {k k' : ℤ} (hk : k = k') (F : CuspForm levelOne k)
    (normalized : fourierCoeff F 1 = 1) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations k (⇑F) eigenvalues) :
    ∃ G : CuspForm levelOne k', (⇑G : UpperHalfPlane → ℂ) = ⇑F ∧ IsNormalizedEigenform G := by
  subst hk
  exact ⟨F, rfl, normalized, eigenvalues, relations⟩

/-- N2' rescaled: with `c` the first coefficient of the classical form, the rescaled Eichler input
`I'` (vector `c⁻¹ • I.vector`) has `S.form` as its normalized eigenform, the conversion being exact.
Formalized by Claude Haiku 5.5, with Claude Opus 5.5. -/
theorem exists_normalized_eigenform_rescaled {n : ℕ} {D : InducingData n} (S : Entry.SphericalEntryData D)
    (I : EichlerInput D.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector) :
    ∃ I' : EichlerInput D.cusp n, I'.halfWeight = I.halfWeight ∧
      I'.vector = (fourierCoeff (classicalFormOfEichlerInput I) 1)⁻¹ • I.vector ∧
      ∃ h : CuspForm levelOne (-2 * I'.halfWeight), IsNormalizedEigenform h ∧
        (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear D.cusp I'.halfWeight 1 I'.vector ∧
        (⇑h : UpperHalfPlane → ℂ) = ⇑S.form := by
  have hc := fourierCoeff_classicalFormOfEichlerInput_one_ne_zero S I hw hv
  have hk : -2 * S.halfWeight = -2 * I.halfWeight := by rw [hw]
  obtain ⟨G, hG, hnorm⟩ := transport_normalized hk S.form S.normalized S.eigenvalues S.relations
  refine ⟨rescaledEichlerInput I (fourierCoeff (classicalFormOfEichlerInput I) 1) hc, rfl, rfl, G, hnorm,
    ?_, hG⟩
  have hform := classical_eq_smul_form S I hw hv
  have final : (⇑S.form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear D.cusp I.halfWeight 1
      ((fourierCoeff (classicalFormOfEichlerInput I) 1)⁻¹ • I.vector) := by
    rw [map_smul, hform, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact hG.trans final

end TernaryPeriodPolynomials.Argument.BoundaryComparison

