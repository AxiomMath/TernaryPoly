module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.ModelComparison

@[expose] public section


/-!
# The negative-determinant component of the model comparison

Formalized by Claude Sonnet 5.5.

For `g_∞` with `det g_∞ < 0` the value `v_h(g_∞, g_f)` of the paper is `F_h(γ g_∞)` for a *rational* `γ ∈ GL₂(ℚ)` with `γ g_f ∈ GL₂(ℤ̂)` and `det γ < 0` (so that `γ g_∞ ∈ GL₂⁺(ℝ)`): two such
`γ` differ by `SL₂(ℤ)`, and the reflection `ε = diag(1,-1)` turns a positive reduction `γ` into the negative reduction `ε γ`.  Here:

* `vhModel_eq_integral`: for any `γ ∈ GL₂(ℚ)` with `γ g_f` integral and `det(γ g_∞) > 0` the model value is `F_h(γ g_∞)` (the argument of `ModelComparison` without the sign condition on `γ`);
* `vhModel_eq_neg`, `vhModel_eq_full`: for `det g_∞ < 0` the model value is `vhValueNeg = F_h(ε γ g_∞)` (independent of the reduction, `vhValueNeg_eq_of_reduction`); `vhValueFull` is `vhValue` on the positive and
  `vhValueNeg` on the negative component.
* **The literal `vhValue` at a negative-determinant `g_∞` is NOT the model value**: `Fh_neg_det`, `literal_neg_formula` show `F_h(x) = (-1)^{k/2} N_k(ε x) h(-conj((ε x)·i))` for `det x < 0`, while the model value
  (`vhModel_neg_formula`) is `N_k(ε x) h((ε x)·i)`; they differ by the sign `(-1)^{k/2}` and the reflection `z ↦ -z̄` of the argument of `h`.
* `Nf_scalGL`, `Fh_scalGL`, `vhValue_scalGL`, `vhValueNeg_scalGL`, `vhValueFull_scalGL`: real scalar matrices `t·1` (`t ≠ 0`; the positive scalars, and the negative one because the weight is even) act trivially.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.RationalIntegral
open TernaryPeriodPolynomials.Argument.LatticeCounts.FhSL2Invariance

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The reflection `diag(1, -1)` over a commutative ring. -/
def reflectionGL (R : Type*) [CommRing R] : GL (Fin 2) R where
  val := !![1, 0; 0, -1]
  inv := !![1, 0; 0, -1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem map_reflectionGL {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    GeneralLinearGroup.map f (reflectionGL R) = reflectionGL S := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectionGL, GeneralLinearGroup.map]

theorem det_reflectionGL (R : Type*) [CommRing R] :
    (GeneralLinearGroup.det (reflectionGL R)).val = -1 := by
  rw [GeneralLinearGroup.val_det_apply]
  simp [reflectionGL, Matrix.det_fin_two]

/-- The reflection as a rational matrix. -/
abbrev reflectionQ : BinaryRationalGL := reflectionGL ℚ

theorem reflectionQ_finite_mem : binaryRationalFinite reflectionQ ∈ binaryIntegralFinite := by
  refine ⟨reflectionGL IntegralAdeles, ?_⟩
  rw [map_reflectionGL]
  exact (map_reflectionGL (algebraMap ℚ FiniteAdeles)).symm

theorem det_reflectionQ_real : (GeneralLinearGroup.det (binaryRationalReal reflectionQ)).val = -1 := by
  unfold binaryRationalReal
  rw [map_reflectionGL, det_reflectionGL]

/-- **The model value at a point with an integral rational reduction `γ` such that `γ g_∞` has positive determinant**: it is `F_h(γ g_∞)`. -/
theorem vhModel_realize_eq_integral (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (gf : BinaryFiniteGL) (γ : BinaryRationalGL)
    (hint : binaryRationalFinite γ * gf ∈ binaryIntegralFinite)
    (hdet : 0 < (GeneralLinearGroup.det (binaryRationalReal γ * gInf)).val) :
    smoothReal σ (σ.π (atFinite gf) I.vector.val) (atInfinity gInf) =
      Fh (-2 * I.halfWeight) ⇑h (binaryRationalReal γ * gInf) := by
  rw [binaryIntegralFinite, MonoidHom.mem_range] at hint
  obtain ⟨k, hk⟩ := hint
  have comm : ∀ f : BinaryFiniteGL, atFinite f * atInfinity gInf = atInfinity gInf * atFinite f :=
    fun f => (atInfinity_commute_atFinite gInf f).eq.symm
  have prod : (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ) *
      atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) γ)) *
      (atInfinity gInf * atFinite gf) =
      atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ * gInf) *
        atFinite (GeneralLinearGroup.map integralEmbedding k) := by
    rw [hk]
    calc (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ) *
          atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) γ)) *
          (atInfinity gInf * atFinite gf)
        = atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ) *
          ((atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) γ) * atInfinity gInf) *
            atFinite gf) := by simp only [mul_assoc]
      _ = atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ) *
          ((atInfinity gInf * atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) γ)) *
            atFinite gf) := by rw [comm]
      _ = (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ) * atInfinity gInf) *
          (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) γ) * atFinite gf) := by
          simp only [mul_assoc]
      _ = atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ * gInf) *
          atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) γ * gf) := by
          rw [atInfinity_mul, atFinite_mul']
  rw [smoothReal_eq_realize σ _ (σ.smooth_stable _ I.vector.val I.vector.property),
    σ.equivariant (atFinite gf) I.vector (atInfinity gInf),
    ← σ.leftRational γ I.vector (atInfinity gInf * atFinite gf),
    binaryRationalMatrix_split γ, prod, realize_mul_integral I _ k]
  exact realize_atInfinity_eq_Fh I h hform _ hdet

/-- **The model value at a negative-determinant archimedean component**: for a rational lattice
reduction `γ` of `g_f` of positive determinant, it is `F_h(ε γ g_∞)` with the reflection `ε = diag(1,-1)`
(the negative reduction `ε γ` of `g_f`; `ε γ g_∞` has positive determinant). -/
theorem vhModel_eq_neg_of_reduction (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hgInf : (GeneralLinearGroup.det gInf).val < 0)
    (gf : BinaryFiniteGL) (L : LatticeReduction gf) :
    smoothReal σ (σ.π (atFinite gf) I.vector.val) (atInfinity gInf) =
      Fh (-2 * I.halfWeight) ⇑h (binaryRationalReal (reflectionQ * L.γ) * gInf) := by
  have hdetR : 0 < (GeneralLinearGroup.det (binaryRationalReal L.γ)).val := by
    have e : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ)).val =
        algebraMap ℚ ℝ (GeneralLinearGroup.det L.γ).val := by
      simp only [GeneralLinearGroup.val_det_apply]
      exact (RingHom.map_det (algebraMap ℚ ℝ) _).symm
    show 0 < (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ)).val
    rw [e, eq_ratCast]
    exact Rat.cast_pos.mpr L.det_pos
  have hdet : 0 < (GeneralLinearGroup.det (binaryRationalReal (reflectionQ * L.γ) * gInf)).val := by
    have e : (GeneralLinearGroup.det (binaryRationalReal (reflectionQ * L.γ) * gInf)).val =
        (-1) * (GeneralLinearGroup.det (binaryRationalReal L.γ)).val * (GeneralLinearGroup.det gInf).val := by
      simp only [map_mul, Units.val_mul, det_reflectionQ_real]
    rw [e]
    nlinarith
  have hint : binaryRationalFinite (reflectionQ * L.γ) * gf ∈ binaryIntegralFinite := by
    rw [map_mul, mul_assoc]
    exact binaryIntegralFinite.mul_mem reflectionQ_finite_mem L.integral
  exact vhModel_realize_eq_integral I h hform gInf gf _ hint hdet

/-- Conjugation of an element of `SL₂(ℤ)` by the reflection `diag(1,-1)`. -/
def reflSL (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![(δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, -(δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      -(δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
    have := δ.2
    rw [Matrix.det_fin_two] at this ⊢
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linarith⟩

theorem reflSL_conj (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ((reflSL δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) =
      (reflectionQ.val : Matrix (Fin 2) (Fin 2) ℚ) * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) *
        (reflectionQ.val : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflSL, reflectionGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem reflectionQ_mul_self : (reflectionQ.val : Matrix (Fin 2) (Fin 2) ℚ) * reflectionQ.val = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectionGL, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The value of `v_h` on the negative-determinant component**: `F_h(ε γ g_∞)` for the chosen positive reduction `γ`. -/
def vhValueNeg (k : ℤ) (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (gf : BinaryFiniteGL) : ℂ :=
  Fh k ⇑h (binaryRationalReal (reflectionQ * (Classical.choice (latticeReductionExists gf)).γ) * gInf)

theorem det_neg_pos (gInf : BinaryRealGL) (hgInf : (GeneralLinearGroup.det gInf).val < 0) (gf : BinaryFiniteGL)
    (L : LatticeReduction gf) :
    0 < (GeneralLinearGroup.det (binaryRationalReal (reflectionQ * L.γ) * gInf)).val := by
  have hdetR : 0 < (GeneralLinearGroup.det (binaryRationalReal L.γ)).val := by
    have e : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ)).val =
        algebraMap ℚ ℝ (GeneralLinearGroup.det L.γ).val := by
      simp only [GeneralLinearGroup.val_det_apply]
      exact (RingHom.map_det (algebraMap ℚ ℝ) _).symm
    show 0 < (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ)).val
    rw [e, eq_ratCast]
    exact Rat.cast_pos.mpr L.det_pos
  have e : (GeneralLinearGroup.det (binaryRationalReal (reflectionQ * L.γ) * gInf)).val =
      (-1) * (GeneralLinearGroup.det (binaryRationalReal L.γ)).val * (GeneralLinearGroup.det gInf).val := by
    simp only [map_mul, Units.val_mul, det_reflectionQ_real]
  rw [e]
  nlinarith

/-- Independence of the reduction on the negative component. -/
theorem vhValueNeg_eq_of_reduction (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (hgInf : (GeneralLinearGroup.det gInf).val < 0) (gf : BinaryFiniteGL)
    (r : LatticeReduction gf) :
    vhValueNeg k h gInf gf = Fh k ⇑h (binaryRationalReal (reflectionQ * r.γ) * gInf) := by
  unfold vhValueNeg
  set c := Classical.choice (latticeReductionExists gf) with hc
  obtain ⟨δ, hδ⟩ := reductions_differ gf c.γ r.γ c.integral r.integral c.det_pos r.det_pos
  have hrel : ((reflectionQ * r.γ).val : Matrix (Fin 2) (Fin 2) ℚ) =
      ((reflSL δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) * (reflectionQ * c.γ).val := by
    rw [Units.val_mul, Units.val_mul, hδ, reflSL_conj]
    calc (reflectionQ.val : Matrix (Fin 2) (Fin 2) ℚ) * ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * c.γ.val)
        = reflectionQ.val * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * (1 * c.γ.val) := by
          rw [one_mul, mul_assoc]
      _ = _ := by
          rw [← reflectionQ_mul_self]
          simp only [Matrix.mul_assoc]
  rw [binaryRationalReal_rel (reflSL δ) hrel, mul_assoc]
  exact (Fh_sl2_mul (h := h) k (reflSL δ) _ (det_neg_pos gInf hgInf gf c)).symm

/-- **Model comparison on the negative-determinant component.** -/
theorem vhModel_eq_neg (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : FinitePlace) (A : GeneralLinearGroup (Fin 2) (p.adicCompletion ℚ))
    (gInf : BinaryRealGL) (hgInf : (GeneralLinearGroup.det gInf).val < 0) :
    smoothReal σ (σ.π (atFinite (ιGL p A)) I.vector.val) (atInfinity gInf) =
      vhValueNeg (-2 * I.halfWeight) h gInf (ιGL p A) := by
  rw [vhValueNeg_eq_of_reduction (-2 * I.halfWeight) h gInf hgInf (ιGL p A)
    (Classical.choice (latticeReductionExists (ιGL p A)))]
  exact vhModel_eq_neg_of_reduction I h hform gInf hgInf (ιGL p A) _

/-- The value `v_h` on all of `GL₂(ℝ) × GL₂(𝔸_f)`: positive determinant by `vhValue`, negative by reflection. -/
def vhValueFull (k : ℤ) (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (gf : BinaryFiniteGL) : ℂ :=
  if 0 < (GeneralLinearGroup.det gInf).val then vhValue k h gInf gf else vhValueNeg k h gInf gf

/-- **The model comparison on both real components.** -/
theorem vhModel_eq_full (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : FinitePlace) (A : GeneralLinearGroup (Fin 2) (p.adicCompletion ℚ)) (gInf : BinaryRealGL) :
    smoothReal σ (σ.π (atFinite (ιGL p A)) I.vector.val) (atInfinity gInf) =
      vhValueFull (-2 * I.halfWeight) h gInf (ιGL p A) := by
  unfold vhValueFull
  by_cases hpos : 0 < (GeneralLinearGroup.det gInf).val
  · rw [ite_eq_left hpos]
    exact vhModel_eq I h hform p A gInf hpos
  · rw [ite_eq_right hpos]
    have hne : (GeneralLinearGroup.det gInf).val ≠ 0 := (GeneralLinearGroup.det gInf).ne_zero
    exact vhModel_eq_neg I h hform p A gInf (lt_of_le_of_ne (not_lt.mp hpos) hne)

/-- The reflection `z ↦ -z̄` of the upper half-plane. -/
def negConj (z : UpperHalfPlane) : UpperHalfPlane :=
  UpperHalfPlane.mk (-(starRingEnd ℂ) (z : ℂ)) (by simpa using z.im_pos)

theorem coe_negConj (z : UpperHalfPlane) : (negConj z : ℂ) = -(starRingEnd ℂ) (z : ℂ) := rfl

theorem reflection_mul_apply (x : BinaryRealGL) (j : Fin 2) :
    ((reflectionGL ℝ * x : BinaryRealGL) : Matrix (Fin 2) (Fin 2) ℝ) 0 j = (x : Matrix (Fin 2) (Fin 2) ℝ) 0 j ∧
    ((reflectionGL ℝ * x : BinaryRealGL) : Matrix (Fin 2) (Fin 2) ℝ) 1 j = -(x : Matrix (Fin 2) (Fin 2) ℝ) 1 j := by
  constructor <;> simp [reflectionGL, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_reflection_mul (x : BinaryRealGL) :
    (GeneralLinearGroup.det (reflectionGL ℝ * x)).val = -(GeneralLinearGroup.det x).val := by
  rw [map_mul, Units.val_mul, det_reflectionGL]
  ring

/-- **The literal `F_h` at a negative-determinant point is a reflected `F_h`.**  For `det x < 0` and
even `k = 2 m`: `F_h(x) = (-1)^m (det εx)^{k/2} (denom εx)^{-k} h(-conj((εx)·i))`, i.e. the literal value
`(det x)^{k/2} (c i + d)^{-k} h(x·i)` differs from the model value `F_h(ε x)` by the sign `(-1)^m` and the
reflection `h(z) ↦ h(-z̄)` of the argument. -/
theorem Fh_neg_det (k m : ℤ) (hk : k = 2 * m) (h : UpperHalfPlane → ℂ) (x : BinaryRealGL)
    (hx : (GeneralLinearGroup.det x).val < 0) :
    Fh k h x = ((-1 : ℂ) ^ m) * (Nf k (reflectionGL ℝ * x) * h (negConj ((reflectionGL ℝ * x) • UpperHalfPlane.I))) := by
  have hpos : 0 < (GeneralLinearGroup.det (reflectionGL ℝ * x)).val := by
    rw [det_reflection_mul]; linarith
  obtain ⟨e00, e10⟩ := reflection_mul_apply x 0
  obtain ⟨e01, e11⟩ := reflection_mul_apply x 1
  have harg : x • UpperHalfPlane.I = negConj ((reflectionGL ℝ * x) • UpperHalfPlane.I) := by
    apply UpperHalfPlane.ext
    rw [coe_negConj, UpperHalfPlane.coe_smul_of_det_pos hpos, UpperHalfPlane.coe_smul,
      UpperHalfPlane.σ, ite_eq_right (not_lt.mpr hx.le)]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, e00, e01, e10, e11]
    have hden : ((-(x.val 1 0) : ℝ) : ℂ) * (UpperHalfPlane.I : ℂ) + ((-(x.val 1 1) : ℝ) : ℂ) =
        -(((x.val 1 0 : ℝ) : ℂ) * (UpperHalfPlane.I : ℂ) + ((x.val 1 1 : ℝ) : ℂ)) := by
      push_cast; ring
    rw [hden, div_neg, map_neg, neg_neg]
    rfl
  have hNf : Nf k x = ((-1 : ℂ) ^ m) * Nf k (reflectionGL ℝ * x) := by
    unfold Nf
    have hkm : ((k : ℤ) : ℂ) / 2 = ((m : ℤ) : ℂ) := by rw [hk]; push_cast; ring
    have hdetx : ((GeneralLinearGroup.det x).val : ℂ) = -(((GeneralLinearGroup.det (reflectionGL ℝ * x)).val : ℝ) : ℂ) := by
      rw [det_reflection_mul]; push_cast; ring
    have hdenom : UpperHalfPlane.denom (reflectionGL ℝ * x) Complex.I = -UpperHalfPlane.denom x Complex.I := by
      simp only [UpperHalfPlane.denom, e10, e11]
      push_cast; ring
    rw [hkm, hdetx, hdenom, Complex.cpow_intCast, Complex.cpow_intCast,
      show -(((GeneralLinearGroup.det (reflectionGL ℝ * x)).val : ℝ) : ℂ) =
        (-1 : ℂ) * (((GeneralLinearGroup.det (reflectionGL ℝ * x)).val : ℝ) : ℂ) by ring,
      mul_zpow]
    have hev : (-UpperHalfPlane.denom x Complex.I) ^ (-k) = UpperHalfPlane.denom x Complex.I ^ (-k) :=
      Even.neg_zpow ⟨-m, by omega⟩ _
    rw [hev]
    ring
  unfold Fh
  rw [harg, hNf]
  ring

/-- The scalar matrix `t · 1` of `GL₂(ℝ)`. -/
def scalGL (t : ℝ) (ht : t ≠ 0) : BinaryRealGL where
  val := t • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  inv := t⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht]

theorem det_scalGL (t : ℝ) (ht : t ≠ 0) : (GeneralLinearGroup.det (scalGL t ht)).val = t ^ 2 := by
  rw [GeneralLinearGroup.val_det_apply]
  simp [scalGL]

theorem scalGL_smul_I (t : ℝ) (ht : t ≠ 0) : scalGL t ht • UpperHalfPlane.I = UpperHalfPlane.I := by
  have hpos : 0 < (GeneralLinearGroup.det (scalGL t ht)).val := by
    rw [det_scalGL]; positivity
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, scalGL]
  simp [Matrix.smul_apply]
  field_simp

/-- **Scalar matrices act trivially on `N_k`** (for even `k = 2 m`, every real scalar `t ≠ 0`). -/
theorem Nf_scalGL (k m : ℤ) (hk : k = 2 * m) (t : ℝ) (ht : t ≠ 0) (g : BinaryRealGL) :
    Nf k (g * scalGL t ht) = Nf k g := by
  unfold Nf
  have hkm : ((k : ℤ) : ℂ) / 2 = ((m : ℤ) : ℂ) := by rw [hk]; push_cast; ring
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hdet : (((GeneralLinearGroup.det (g * scalGL t ht)).val : ℝ) : ℂ) =
      (((GeneralLinearGroup.det g).val : ℝ) : ℂ) * (t : ℂ) ^ 2 := by
    rw [map_mul, Units.val_mul, det_scalGL]; push_cast; ring
  have hden : UpperHalfPlane.denom (g * scalGL t ht) Complex.I = (t : ℂ) * UpperHalfPlane.denom g Complex.I := by
    simp [UpperHalfPlane.denom, scalGL, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e2 : ((t : ℂ) ^ 2) ^ m = (t : ℂ) ^ ((2 : ℤ) * m) := by
    rw [← zpow_natCast, ← _root_.zpow_mul]; simp
  rw [hkm, hdet, hden, Complex.cpow_intCast, Complex.cpow_intCast, mul_zpow, mul_zpow, e2]
  have : ((t : ℂ) ^ ((2 : ℤ) * m)) * (t : ℂ) ^ (-k) = 1 := by
    rw [← zpow_add₀ ht', hk]; simp
  calc _ = (((GeneralLinearGroup.det g).val : ℝ) : ℂ) ^ m * UpperHalfPlane.denom g Complex.I ^ (-k) *
        (((t : ℂ) ^ ((2 : ℤ) * m)) * (t : ℂ) ^ (-k)) := by ring
    _ = _ := by rw [this, mul_one]

theorem Fh_scalGL (k m : ℤ) (hk : k = 2 * m) (h : UpperHalfPlane → ℂ) (t : ℝ) (ht : t ≠ 0) (g : BinaryRealGL) :
    Fh k h (g * scalGL t ht) = Fh k h g := by
  unfold Fh
  rw [mul_smul, scalGL_smul_I, Nf_scalGL k m hk t ht]

/-- **Real scalars act trivially on `v_h`** (the paper's positive scalars; the negative scalar because the weight `k = -2 halfWeight` is even). -/
theorem vhValue_scalGL (k m : ℤ) (hk : k = 2 * m)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (gf : BinaryFiniteGL) (t : ℝ) (ht : t ≠ 0) :
    vhValue k h (gInf * scalGL t ht) gf = vhValue k h gInf gf := by
  unfold vhValue
  rw [← mul_assoc, Fh_scalGL k m hk _ t ht]

theorem vhValueNeg_scalGL (k m : ℤ) (hk : k = 2 * m)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (gf : BinaryFiniteGL) (t : ℝ) (ht : t ≠ 0) :
    vhValueNeg k h (gInf * scalGL t ht) gf = vhValueNeg k h gInf gf := by
  unfold vhValueNeg
  rw [← mul_assoc, Fh_scalGL k m hk _ t ht]

theorem vhValueFull_scalGL (k m : ℤ) (hk : k = 2 * m)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (gf : BinaryFiniteGL) (t : ℝ) (ht : t ≠ 0) :
    vhValueFull k h (gInf * scalGL t ht) gf = vhValueFull k h gInf gf := by
  unfold vhValueFull
  have hs : 0 < (GeneralLinearGroup.det (gInf * scalGL t ht)).val ↔ 0 < (GeneralLinearGroup.det gInf).val := by
    rw [map_mul, Units.val_mul, det_scalGL]
    have : 0 < t ^ 2 := by positivity
    constructor
    · intro h0; exact (mul_pos_iff_of_pos_right this).mp h0
    · intro h0; exact mul_pos h0 this
  by_cases hp : 0 < (GeneralLinearGroup.det gInf).val
  · rw [ite_eq_left (hs.mpr hp), ite_eq_left hp]
    exact vhValue_scalGL k m hk h gInf gf t ht
  · rw [ite_eq_right (fun h' => hp (hs.mp h')), ite_eq_right hp]
    exact vhValueNeg_scalGL k m hk h gInf gf t ht

theorem binaryRationalReal_reflectionQ : binaryRationalReal reflectionQ = reflectionGL ℝ := by
  unfold binaryRationalReal
  exact map_reflectionGL _

theorem det_real_pos (gf : BinaryFiniteGL) (L : LatticeReduction gf) :
    0 < (GeneralLinearGroup.det (binaryRationalReal L.γ)).val := by
  have e : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ)).val =
      algebraMap ℚ ℝ (GeneralLinearGroup.det L.γ).val := by
    simp only [GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (algebraMap ℚ ℝ) _).symm
  show 0 < (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ)).val
  rw [e, eq_ratCast]
  exact Rat.cast_pos.mpr L.det_pos

theorem det_real_mul_neg (gf : BinaryFiniteGL) (L : LatticeReduction gf) (gInf : BinaryRealGL)
    (hgInf : (GeneralLinearGroup.det gInf).val < 0) :
    (GeneralLinearGroup.det (binaryRationalReal L.γ * gInf)).val < 0 := by
  rw [map_mul, Units.val_mul]
  exact mul_neg_of_pos_of_neg (det_real_pos gf L) hgInf

/-- **Model value at a negative-determinant point, as `N_k(ε x) h(z)`** (`x = γ g_∞`, `z = (ε x)·i`). -/
theorem vhModel_neg_formula (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hgInf : (GeneralLinearGroup.det gInf).val < 0)
    (gf : BinaryFiniteGL) (L : LatticeReduction gf) :
    smoothReal σ (σ.π (atFinite gf) I.vector.val) (atInfinity gInf) =
      Nf (-2 * I.halfWeight) (reflectionGL ℝ * (binaryRationalReal L.γ * gInf)) *
        h ((reflectionGL ℝ * (binaryRationalReal L.γ * gInf)) • UpperHalfPlane.I) := by
  rw [vhModel_eq_neg_of_reduction I h hform gInf hgInf gf L]
  unfold Fh
  rw [map_mul, binaryRationalReal_reflectionQ, mul_assoc]

/-- **The literal `F_h` of the same reduction is the reflected expression with the sign `(-1)^{k/2}`.** -/
theorem literal_neg_formula (k m : ℤ) (hk : k = 2 * m) (h : UpperHalfPlane → ℂ) (gInf : BinaryRealGL)
    (hgInf : (GeneralLinearGroup.det gInf).val < 0) (gf : BinaryFiniteGL) (L : LatticeReduction gf) :
    Fh k h (binaryRationalReal L.γ * gInf) =
      ((-1 : ℂ) ^ m) * (Nf k (reflectionGL ℝ * (binaryRationalReal L.γ * gInf)) *
        h (negConj ((reflectionGL ℝ * (binaryRationalReal L.γ * gInf)) • UpperHalfPlane.I))) :=
  Fh_neg_det k m hk h _ (det_real_mul_neg gf L gInf hgInf)

end TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
