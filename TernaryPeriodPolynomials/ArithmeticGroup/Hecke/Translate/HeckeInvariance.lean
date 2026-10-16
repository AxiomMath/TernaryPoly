/-
  Partial formalization toward the associate-pair splitting:
  the finite-coset Hecke action on adelic source cochains.

  `translateSource` is the adelic cochain obtained from a source cochain by the
  literal finite-coset formula of `heckeCochain` after transport across the
  evaluation comparison `Evaluates`.  `evaluates_translate` verifies that the
  transported cochain evaluates the Hecke image of the cohomology class, which
  is the first half of the invariance step.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.Helpers

@[expose] public section



open GeneralEisenstein
open Homogeneous Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance

variable {n : ℕ}

/-- The finite-coset translate of an adelic source cochain. -/
def translateSource (D : InducingData n) (t : HeckeCorrespondence)
    (c : SourceCochain n) : SourceCochain n :=
  fun x g => ∑ r ∈ t.representatives,
    realCoefficientComponent n D.chi
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
      (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
         (g * rationalGroup r))

theorem heckeCochain_apply (D : InducingData n) (side : Side)
    (t : HeckeCorrespondence) (z : MaximalCycles n D.chi side)
    (x : Fin 3 → RationalGL3) (q : RationalGL3) :
    heckeCochain (flagRepresentation (rationalCoefficientComponent n D.chi) side) t
        z.val x (QuotientGroup.mk q) =
      ∑ r ∈ t.representatives,
        rationalCoefficientComponent n D.chi r
          (z.val.val (fun i => r⁻¹ * x i) (QuotientGroup.mk (r⁻¹ * q))) := by
  rw [heckeCochain, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  show (functionRepresentation (rationalCoefficientComponent n D.chi) (Flags side)) r
      (z.val.val (fun i => r⁻¹ * x i)) (QuotientGroup.mk q) = _
  show rationalCoefficientComponent n D.chi r
      (z.val.val (fun i => r⁻¹ * x i) (r⁻¹ • QuotientGroup.mk q)) = _
  congr 1

theorem evaluates_translate (D : InducingData n) (side : Side)
    (t : HeckeCorrespondence)
    {c : SourceCochain n}
    {z : MaximalCycles n D.chi side}
    (heval : Evaluates D side c z)
    {z' : MaximalCycles n D.chi side}
    (hz' : ∀ x, z'.val.val x = heckeCochain
        (flagRepresentation (rationalCoefficientComponent n D.chi) side) t z.val x) :
    Evaluates D side (translateSource D t c) z' := by
  intro x q
  rw [hz', heckeCochain_apply]
  simp only [translateSource]
  apply Finset.sum_congr rfl
  intro r _
  rw [heval (fun i => r⁻¹ * x i) (r⁻¹ * q)]
  have hA : (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ)) (r⁻¹ * x i)) =
      (fun i => ((GeneralLinearGroup.map (algebraMap ℚ ℝ)) r)⁻¹ *
        (GeneralLinearGroup.map (algebraMap ℚ ℝ)) (x i)) := by
    funext i; rw [map_mul, map_inv]
  have hB : rationalGroup (r⁻¹ * q)⁻¹ = rationalGroup q⁻¹ * rationalGroup r := by
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
  rw [hA, hB]
  rfl


section RealCocyclePreservation

open Matrix

/-- The real-variable cocycle equation of an adelic source cochain is preserved
by the finite-coset translate. -/
theorem translateSource_closed (D : InducingData n) (t : HeckeCorrespondence)
    (c : SourceCochain n)
    (hc : ∀ x : Fin 4 → RealGL3, ∀ g,
      c ![x 1, x 2, x 3] g - c ![x 0, x 2, x 3] g +
        c ![x 0, x 1, x 3] g - c ![x 0, x 1, x 2] g = 0) :
    ∀ x : Fin 4 → RealGL3, ∀ g,
      translateSource D t c ![x 1, x 2, x 3] g -
        translateSource D t c ![x 0, x 2, x 3] g +
        translateSource D t c ![x 0, x 1, x 3] g -
        translateSource D t c ![x 0, x 1, x 2] g = 0 := by
  intro x g
  simp only [translateSource]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro r _
  rw [← map_sub, ← map_add, ← map_sub]
  have h := hc (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
    (g * rationalGroup r)
  have key : c ![((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 1),
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 2),
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 3)] (g * rationalGroup r) -
      c ![((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 0),
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 2),
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 3)] (g * rationalGroup r) +
      c ![((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 0),
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 1),
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 3)] (g * rationalGroup r) -
      c ![((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 0),
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 1),
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 2)] (g * rationalGroup r) = 0 := by
    convert h using 2
  have e1 : (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * ![x 1, x 2, x 3] i)
      = ![((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 1),
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 2),
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 3)] := by
    funext i; fin_cases i <;> rfl
  have e2 : (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * ![x 0, x 2, x 3] i)
      = ![((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 0),
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 2),
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 3)] := by
    funext i; fin_cases i <;> rfl
  have e3 : (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * ![x 0, x 1, x 3] i)
      = ![((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 0),
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 1),
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 3)] := by
    funext i; fin_cases i <;> rfl
  have e4 : (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * ![x 0, x 1, x 2] i)
      = ![((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 0),
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 1),
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x 2)] := by
    funext i; fin_cases i <;> rfl
  rw [e1, e2, e3, e4, key, map_zero]

end RealCocyclePreservation

end TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance
