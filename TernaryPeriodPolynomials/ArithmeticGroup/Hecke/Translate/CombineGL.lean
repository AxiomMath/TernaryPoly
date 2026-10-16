/-
  Multiplicativity of the adelic-block embedding `combineGL`, the
  archimedean/finite decomposition of `rationalGroup`, and the commutation
  identity that controls the congruence-level behaviour of the Hecke
  translate.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.Helpers

@[expose] public section



open GeneralEisenstein
open Homogeneous Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance

theorem combineGL_mul {m : ℕ}
    (r r' : GeneralLinearGroup (Fin m) ℝ)
    (f f' : GeneralLinearGroup (Fin m) FiniteAdeles) :
    combineGL r f * combineGL r' f' = combineGL (r * r') (f * f') := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · simp only [combineGL, pairMatrix, Matrix.mul_apply, Prod.fst_mul, Prod.fst_sum,
      Units.val_mul]
  · simp only [combineGL, pairMatrix, Matrix.mul_apply, Prod.snd_mul, Prod.snd_sum,
      Units.val_mul]

theorem rationalGroup_eq (r : RationalGL3) :
    rationalGroup r =
      combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
        (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) r) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Prod.ext <;>
    simp only [rationalGroup, GeneralLinearGroup.map_apply, combineGL, pairMatrix,
      rationalAdele, RingHom.prod_apply]

theorem atFinite_eq (k : finiteLevel) :
    atFinite k.val = combineGL 1 k.val := rfl

/-- Right multiplication by the rational adelic matrix conjugates the
congruence level: the finite factor `rationalFinite r` acts by conjugation. -/
theorem atFinite_mul_rationalGroup (k : finiteLevel) (r : RationalGL3) :
    atFinite k.val * rationalGroup r =
      rationalGroup r * atFinite ((rationalFinite r)⁻¹ * k.val * rationalFinite r) := by
  rw [rationalGroup_eq r, atFinite, atFinite, combineGL_mul, combineGL_mul]
  congr 1
  · group
  · simp only [rationalFinite]; group

/-- The congruence-level invariance of the right translate `g ↦ f (g * rationalGroup r)`
holds as soon as every conjugate `r_f⁻¹ k r_f` of `k ∈ finiteLevel` stays in
`finiteLevel` (`r_f = rationalFinite r`). -/
theorem finiteLevel_right_translate (r : RationalGL3) (f : AdelicGL → ℂ)
    (hf : ∀ k : finiteLevel, ∀ g, f (g * atFinite k.val) = f g)
    (hr : ∀ k : finiteLevel, (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel)
    (k : finiteLevel) (g : AdelicGL) :
    f (g * atFinite k.val * rationalGroup r) = f (g * rationalGroup r) := by
  rw [mul_assoc, atFinite_mul_rationalGroup k r, ← mul_assoc]
  exact hf ⟨_, hr k⟩ (g * rationalGroup r)


section Archimedean

/-- `atInfinity` is multiplicative. -/
theorem atInfinity_mul {m : ℕ}
    (a b : GeneralLinearGroup (Fin m) ℝ) :
    atInfinity a * atInfinity b = atInfinity (a * b) := by
  show combineGL a 1 * combineGL b 1 = combineGL (a * b) 1
  rw [combineGL_mul, one_mul]

/-- The archimedean shift and the rational adelic shift differ by conjugation of
the archimedean factor: `atInfinity h · rationalGroup r` equals
`rationalGroup r · atInfinity (map r⁻¹ · h · map r)`. -/
theorem atInfinity_mul_rationalGroup (h : RealGL3) (r : RationalGL3) :
    atInfinity h * rationalGroup r =
      rationalGroup r * atInfinity
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * h *
          GeneralLinearGroup.map (algebraMap ℚ ℝ) r) := by
  rw [rationalGroup_eq r]
  show combineGL h 1 *
      combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
        (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) r) =
    combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
        (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) r) *
      combineGL ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * h *
        GeneralLinearGroup.map (algebraMap ℚ ℝ) r) 1
  rw [combineGL_mul, combineGL_mul]
  congr 1
  · group
  · simp


theorem atFinite_mul {m : ℕ} (a b : GeneralLinearGroup (Fin m) FiniteAdeles) :
    atFinite a * atFinite b = atFinite (a * b) := by
  rw [atFinite, atFinite, atFinite, combineGL_mul, one_mul]


theorem atFinite_comm_atInfinity {m : ℕ}
    (f : GeneralLinearGroup (Fin m) FiniteAdeles) (r : GeneralLinearGroup (Fin m) ℝ) :
    atFinite f * atInfinity r = atInfinity r * atFinite f := by
  show combineGL 1 f * combineGL r 1 = combineGL r 1 * combineGL 1 f
  rw [combineGL_mul, combineGL_mul]
  congr 1 <;> group

end Archimedean


theorem combineGL_inv {m : ℕ}
    (r : GeneralLinearGroup (Fin m) ℝ) (f : GeneralLinearGroup (Fin m) FiniteAdeles) :
    (combineGL r f)⁻¹ = combineGL r⁻¹ f⁻¹ := by
  apply Units.ext
  rfl

theorem atInfinity_inv {m : ℕ} (g : GeneralLinearGroup (Fin m) ℝ) :
    (atInfinity g)⁻¹ = atInfinity g⁻¹ := by
  rw [atInfinity, combineGL_inv, atInfinity, inv_one]

/-- The rational adelic shift, left-multiplied by the inverse archimedean shift, is
the finite-part shift: `rationalGroup r · (atInfinity r_ℝ)⁻¹ = atFinite (r_f)`. -/
theorem rationalGroup_mul_atInfinity_inv (r : RationalGL3) :
    rationalGroup r * (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) r))⁻¹ =
      atFinite (rationalFinite r) := by
  rw [rationalGroup_eq r, atInfinity_inv, atInfinity, combineGL_mul]
  congr 1
  · group
  · rw [mul_one, rationalFinite]

/-- With the adelic variable on the left: `g · rationalGroup r · (atInfinity r_ℝ)⁻¹
= g · atFinite r_f`. -/
theorem mul_rationalGroup_atInfinity_inv (g : AdelicGL) (r : RationalGL3) :
    g * rationalGroup r * (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) r))⁻¹ =
      g * atFinite (rationalFinite r) := by
  rw [mul_assoc, rationalGroup_mul_atInfinity_inv]

end TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance
