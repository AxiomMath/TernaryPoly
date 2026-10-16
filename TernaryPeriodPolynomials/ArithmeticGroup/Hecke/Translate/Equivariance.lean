/-
  Preservation of the real-variable equivariance condition of a source cochain
  by the finite-coset Hecke translate `translateSource`.

  Together with `HeckeInvariance.translateSource_closed` (preservation of the
  cocycle equation) this carries two of the four source-cocycle conditions
  through the Hecke action, independently of any level-normaliser hypothesis.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HeckeInvariance

@[expose] public section



open GeneralEisenstein
open Homogeneous Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance

variable {n : ℕ}

/-- The real-group equivariance of an adelic source cochain is preserved by the
finite-coset Hecke translate. -/
theorem translateSource_equivariant (D : InducingData n) (t : HeckeCorrespondence)
    (c : SourceCochain n)
    (hc : ∀ h x g, c (fun i => h * x i) g =
      realCoefficientComponent n D.chi h (c x (g * atInfinity h))) :
    ∀ h x g, translateSource D t c (fun i => h * x i) g =
      realCoefficientComponent n D.chi h (translateSource D t c x (g * atInfinity h)) := by
  intro h x g
  simp only [translateSource]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  let rR : RealGL3 := GeneralLinearGroup.map (algebraMap ℚ ℝ) r
  have hcomm : g * rationalGroup r * atInfinity (rR⁻¹ * h) =
      g * atInfinity h * rationalGroup r * atInfinity (rR⁻¹) := by
    calc
      g * rationalGroup r * atInfinity (rR⁻¹ * h)
          = g * rationalGroup r * ((atInfinity rR)⁻¹ * atInfinity h) := by
              rw [← atInfinity_mul, ← atInfinity_inv]
      _ = g * (rationalGroup r * (atInfinity rR)⁻¹) * atInfinity h := by group
      _ = g * atFinite (rationalFinite r) * atInfinity h := by
              rw [rationalGroup_mul_atInfinity_inv]
      _ = g * (atFinite (rationalFinite r) * atInfinity h) := by group
      _ = g * (atInfinity h * atFinite (rationalFinite r)) := by
              rw [atFinite_comm_atInfinity]
      _ = g * atInfinity h * (rationalGroup r * (atInfinity rR)⁻¹) := by
              rw [rationalGroup_mul_atInfinity_inv]; group
      _ = g * atInfinity h * rationalGroup r * atInfinity (rR⁻¹) := by
              rw [atInfinity_inv]; group
  have ha1 : c (fun i => rR⁻¹ * (h * x i)) (g * rationalGroup r)
      = realCoefficientComponent n D.chi (rR⁻¹ * h)
          (c x (g * rationalGroup r * atInfinity (rR⁻¹ * h))) := by
    simpa only [mul_assoc] using hc (rR⁻¹ * h) x (g * rationalGroup r)
  have ha2 : c (fun i => rR⁻¹ * x i) (g * atInfinity h * rationalGroup r)
      = realCoefficientComponent n D.chi (rR⁻¹)
          (c x (g * atInfinity h * rationalGroup r * atInfinity (rR⁻¹))) :=
    hc (rR⁻¹) x (g * atInfinity h * rationalGroup r)
  have ha2' : realCoefficientComponent n D.chi rR
        (c (fun i => rR⁻¹ * x i) (g * atInfinity h * rationalGroup r))
      = c x (g * atInfinity h * rationalGroup r * atInfinity (rR⁻¹)) := by
    rw [ha2, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  change realCoefficientComponent n D.chi rR
      (c (fun i => rR⁻¹ * (h * x i)) (g * rationalGroup r))
    = realCoefficientComponent n D.chi h
        (realCoefficientComponent n D.chi rR
          (c (fun i => rR⁻¹ * x i) (g * atInfinity h * rationalGroup r)))
  calc
    realCoefficientComponent n D.chi rR
        (c (fun i => rR⁻¹ * (h * x i)) (g * rationalGroup r))
        = realCoefficientComponent n D.chi rR
            (realCoefficientComponent n D.chi (rR⁻¹ * h)
              (c x (g * rationalGroup r * atInfinity (rR⁻¹ * h)))) := by rw [ha1]
    _ = realCoefficientComponent n D.chi (rR * (rR⁻¹ * h))
            (c x (g * rationalGroup r * atInfinity (rR⁻¹ * h))) := by
              rw [← Module.End.mul_apply, ← map_mul]
    _ = realCoefficientComponent n D.chi h
            (c x (g * rationalGroup r * atInfinity (rR⁻¹ * h))) := by
              rw [mul_inv_cancel_left]
    _ = realCoefficientComponent n D.chi h
            (c x (g * atInfinity h * rationalGroup r * atInfinity (rR⁻¹))) := by
              rw [hcomm]
    _ = realCoefficientComponent n D.chi h
            (realCoefficientComponent n D.chi rR
              (c (fun i => rR⁻¹ * x i) (g * atInfinity h * rationalGroup r))) := by
              rw [← ha2']

/-- Clauses (c) (real equivariance) and (d) (the cocycle equation) of
`IsSourceCocycle` both pass to the finite-coset Hecke translate, unconditionally
in the level-normaliser data. -/
theorem translateSource_satisfies_equivariance_and_cocycle
    (D : InducingData n) (t : HeckeCorrespondence) {side : Side} (c : SourceCochain n)
    (hc : IsSourceCocycle D side c) :
    (∀ h x g, translateSource D t c (fun i => h * x i) g =
        realCoefficientComponent n D.chi h (translateSource D t c x (g * atInfinity h))) ∧
    (∀ x : Fin 4 → RealGL3, ∀ g,
      translateSource D t c ![x 1, x 2, x 3] g -
        translateSource D t c ![x 0, x 2, x 3] g +
        translateSource D t c ![x 0, x 1, x 3] g -
        translateSource D t c ![x 0, x 1, x 2] g = 0) :=
  ⟨translateSource_equivariant D t c hc.2.2.1,
   translateSource_closed D t c hc.2.2.2⟩

end TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance

end
