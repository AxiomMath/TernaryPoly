/-
  Representative independence of the finite-coset Hecke translate.

  For `γ` in the arithmetic level `Γ = rationalLevel`, replacing a
  representative `r` by `r · γ` does not change the term of the adelic source
  translate.  The proof uses clause (c) of `IsSourceCocycle` (real
  equivariance) and clause (a) (finite-level right invariance), together with
  the identity `rationalGroup γ * atInfinity (map γ)⁻¹ = atFinite (rf γ)`
  and the fact `rf γ ∈ finiteLevel` for `γ ∈ rationalLevel`.

  Consequence: the finite-coset Hecke translate depends only on the classes
  `r Γ`, so a Hecke double coset may be summed with any right-`Γ`-adapted
  representative set without changing the cochain.  This is a concrete step in
  the finite-level Hecke averaging; it does not by itself prove finite-level
  invariance (the sharp condition for that is the `hnorm` of
  `AveragedHecke.translateSource_level_normalizer`).
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.AveragedHecke
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section



open GeneralEisenstein
open Homogeneous Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.RepresentativeInvariance

variable {n : ℕ}

/-- Twisted coefficient action is multiplicative in composition order. -/
theorem realCoefficientComponent_mul_apply (χ : RankOneCharacter)
    (a b : RealGL3) (v : HomogeneousPoly n) :
    realCoefficientComponent n χ (a * b) v =
      realCoefficientComponent n χ a (realCoefficientComponent n χ b v) := by
  rw [map_mul, Module.End.mul_apply]

/-- `rationalGroup γ · atInfinity (map γ)⁻¹ = atFinite (rationalFinite γ)`: the
archimedean inverse cancels the archimedean half of `rationalGroup γ`. -/
theorem rationalGroup_mul_atInfinity_inv (γ : rationalLevel) :
    rationalGroup γ.val *
      atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)⁻¹) =
      atFinite (rationalFinite γ.val) := by
  rw [HeckeInvariance.rationalGroup_eq γ.val]
  show combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)
        (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) γ.val) *
      combineGL ((GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)⁻¹) 1 =
      combineGL 1 (rationalFinite γ.val)
  rw [HeckeInvariance.combineGL_mul, mul_one, mul_inv_cancel]
  rfl

/-- **Term invariance under right-`Γ` multiplication of the representative.**
For `γ ∈ rationalLevel`, the `r`-term and the `r·γ`-term of the adelic source
translate coincide. -/
theorem translateSource_term_invariant (D : InducingData n) (side : Side)
    {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (x : Fin 3 → RealGL3) (g : AdelicGL) (r : RationalGL3) (γ : rationalLevel) :
    realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
        (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
           (g * rationalGroup r)) =
    realCoefficientComponent n D.chi
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (r * γ.val))
        (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) (r * γ.val))⁻¹ * x i)
           (g * rationalGroup (r * γ.val))) := by
  have hmul : GeneralLinearGroup.map (algebraMap ℚ ℝ) (r * γ.val) =
      GeneralLinearGroup.map (algebraMap ℚ ℝ) r *
        GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val := map_mul _ _ _
  have hinv : (GeneralLinearGroup.map (algebraMap ℚ ℝ) (r * γ.val))⁻¹ =
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)⁻¹ *
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ := by
    rw [hmul, _root_.mul_inv_rev]
  have hrg : rationalGroup (r * γ.val) = rationalGroup r * rationalGroup γ.val :=
    map_mul _ _ _
  rw [hinv, hmul, hrg]
  rw [realCoefficientComponent_mul_apply]
  apply congrArg (realCoefficientComponent n D.chi
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) r))
  -- reduce the inner equality
  rw [show (fun i => ((GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)⁻¹ *
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹) * x i) =
      (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)⁻¹ *
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)) from by
    funext i; rw [mul_assoc]]
  rw [hc.2.2.1 ((GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)⁻¹)]
  rw [← realCoefficientComponent_mul_apply, mul_inv_cancel, map_one,
    Module.End.one_apply]
  -- remaining: c y (g · rΓ) = c y ((g · rΓ) · atFinite (rf γ))
  have hfin : g * (rationalGroup r * rationalGroup γ.val) *
        atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)⁻¹) =
      (g * rationalGroup r) * atFinite (rationalFinite γ.val) := by
    rw [mul_assoc, mul_assoc, rationalGroup_mul_atInfinity_inv, ← mul_assoc]
  rw [hfin]
  exact (AveragedHecke.source_level_invariance hc _ 
    ⟨rationalFinite γ.val, AveragedHecke.rationalFinite_mem_of_rationalLevel γ.property⟩ _
    ).symm

/-- General form, for any rational `r` (not only `γ ∈ rationalLevel`). -/
theorem rationalGroup_mul_atInfinity_inv_general (r : RationalGL3) :
    rationalGroup r *
      atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹) =
      atFinite (rationalFinite r) := by
  rw [HeckeInvariance.rationalGroup_eq r]
  show combineGL (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
        (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) r) *
      combineGL ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹) 1 =
      combineGL 1 (rationalFinite r)
  rw [HeckeInvariance.combineGL_mul, mul_one, mul_inv_cancel]
  rfl

/-- The archimedean and finite blocks commute inside the adelic group. -/
theorem atInfinity_atFinite_comm (h : RealGL3) (f : FiniteGL) :
    atInfinity h * atFinite f = atFinite f * atInfinity h := by
  show combineGL h 1 * combineGL 1 f = combineGL 1 f * combineGL h 1
  rw [HeckeInvariance.combineGL_mul, HeckeInvariance.combineGL_mul]
  congr 1
  · simp only [mul_one, one_mul]
  · simp only [mul_one, one_mul]

/-- `atInfinity 1 = 1`. -/
theorem atInfinity_one : atInfinity (1 : RealGL3) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  by_cases hij : i = j <;>
    simp [atInfinity, combineGL, pairMatrix, hij]

/-- Reverse form of clause (c): applying `ρ h` to a value of `c` is evaluating
`c` at the translated tuple and the shifted adelic point. -/
theorem realCoefficientComponent_apply_eq (D : InducingData n) (side : Side)
    {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (h : RealGL3) (x : Fin 3 → RealGL3) (y : AdelicGL) :
    realCoefficientComponent n D.chi h (c x y) =
      c (fun i => h * x i) (y * atInfinity h⁻¹) := by
  have hcl := hc.2.2.1 h x (y * atInfinity h⁻¹)
  rw [hcl]
  apply congrArg (realCoefficientComponent n D.chi h)
  apply congrArg (c x)
  rw [mul_assoc, HeckeInvariance.atInfinity_mul, inv_mul_cancel, atInfinity_one, mul_one]

/-- **Clause (c) is preserved by the finite-coset translate.**  The adelic source
translate is real-equivariant for the same coefficient action. -/
theorem translateSource_real_equivariant (D : InducingData n) (side : Side)
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (h : RealGL3) (x : Fin 3 → RealGL3) (g : AdelicGL) :
    HeckeInvariance.translateSource D t c (fun i => h * x i) g =
      realCoefficientComponent n D.chi h
        (HeckeInvariance.translateSource D t c x (g * atInfinity h)) := by
  simp only [HeckeInvariance.translateSource]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (h * x i)) =
      (fun i => ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * h) * x i) from by
    funext i; rw [mul_assoc]]
  rw [hc.2.2.1 ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * h) x
      (g * rationalGroup r)]
  rw [← realCoefficientComponent_mul_apply,
      show GeneralLinearGroup.map (algebraMap ℚ ℝ) r *
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * h) = h from by group]
  apply congrArg (realCoefficientComponent n D.chi h)
  rw [realCoefficientComponent_apply_eq D side hc (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
        (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
        ((g * atInfinity h) * rationalGroup r)]
  rw [show (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) *
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)) = x from by
    funext i; group]
  apply congrArg (c x)
  have hgroup : g * rationalGroup r *
        atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * h) =
      ((g * atInfinity h) * rationalGroup r) *
        atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹) := by
    have hA : atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * h) =
        atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹) * atInfinity h :=
      (HeckeInvariance.atInfinity_mul _ _).symm
    have hB : rationalGroup r *
        atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹) =
        atFinite (rationalFinite r) := rationalGroup_mul_atInfinity_inv_general r
    have hC : atFinite (rationalFinite r) * atInfinity h =
        atInfinity h * atFinite (rationalFinite r) := (atInfinity_atFinite_comm h _).symm
    calc g * rationalGroup r * atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * h)
        = g * rationalGroup r *
            (atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹) * atInfinity h) := by
          rw [hA]
      _ = g * (rationalGroup r *
            atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹)) * atInfinity h := by
          simp only [mul_assoc]
      _ = g * atFinite (rationalFinite r) * atInfinity h := by rw [hB]
      _ = g * (atFinite (rationalFinite r) * atInfinity h) := by simp only [mul_assoc]
      _ = g * (atInfinity h * atFinite (rationalFinite r)) := by rw [hC]
      _ = g * (atInfinity h * (rationalGroup r *
            atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹))) := by rw [← hB]
      _ = ((g * atInfinity h) * rationalGroup r) *
            atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹) := by
          simp only [mul_assoc]
  exact hgroup

/-- The parabolic unipotent matched to the side. -/
def sideUnipotent : Side → Adeles → Adeles → AdelicGL
  | .plane => planeUnipotent
  | .line => lineUnipotent

/-- **Parabolic-unipotent invariance of the Hecke translate** (a piece of
clause (a) of `IsSourceCocycle`).  It is the termwise transport of the
corresponding clause of the source cocycle `c`. -/
theorem translateSource_unipotent_invariant (D : InducingData n) (side : Side)
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (x : Fin 3 → RealGL3) (g : AdelicGL) (a b : Adeles) :
    HeckeInvariance.translateSource D t c x (sideUnipotent side a b * g) =
      HeckeInvariance.translateSource D t c x g := by
  simp only [HeckeInvariance.translateSource]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply AveragedHecke.poly_ext
  intro m
  rw [mul_assoc]
  cases side with
  | plane => exact (hc.1 _ m).2.2.2.1 a b (g * rationalGroup r)
  | line => exact (hc.1 _ m).2.2.2.1 a b (g * rationalGroup r)

/-- The parabolic Levi matched to the side. -/
def sideLevi : Side → Adelesˣ → AdelicGL
  | .plane => fun t => planeLevi 1 t
  | .line => fun t => lineLevi t 1

/-- The modulus exponent appearing in the Levi-character clause at the
cohomological point. -/
def sideLeviExponent (side : Side) : ℂ :=
  match side with
  | .plane => -2 * inductionExponent .plane cohomologicalPoint
  | .line => 2 * inductionExponent .line cohomologicalPoint

/-- **Levi-character clause of the Hecke translate** (another piece of clause (a)
of `IsSourceCocycle`). -/
theorem translateSource_levi (D : InducingData n) (side : Side)
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (x : Fin 3 → RealGL3) (g : AdelicGL) (u : Adelesˣ) :
    HeckeInvariance.translateSource D t c x (sideLevi side u * g) =
      (D.chi.toMonoidHom u * normPower u (sideLeviExponent side)) •
        HeckeInvariance.translateSource D t c x g := by
  simp only [HeckeInvariance.translateSource]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_assoc]
  have hpoly : c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
        (sideLevi side u * (g * rationalGroup r)) =
      (D.chi.toMonoidHom u * normPower u (sideLeviExponent side)) •
        c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
          (g * rationalGroup r) := by
    apply AveragedHecke.poly_ext
    intro m
    rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    cases side with
    | plane => exact (hc.1 _ m).2.2.2.2.1 u (g * rationalGroup r)
    | line => exact (hc.1 _ m).2.2.2.2.1 u (g * rationalGroup r)
  rw [hpoly, map_smul]

end TernaryPeriodPolynomials.HeckeTranslate.RepresentativeInvariance

end
