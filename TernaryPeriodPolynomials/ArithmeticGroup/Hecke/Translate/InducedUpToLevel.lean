/-
  `IsInduced` with the finite-level-invariance conjunct separated out.

  This lets the finite-coset Hecke translate's coefficient functions be shown
  `IsInduced` from (i) the rational-level double-coset reindexing (their
  finite-level invariance) together with (ii) the level-free part of the
  right-shift closure `IsInducedShift.isInduced_right_shift`.  The latter does
  not use the normaliser hypothesis, so the two pieces give clause (a) of
  `IsSourceCocycle` without `hnorm` once the finite-level invariance of the
  average is available.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HasSmoothCuspLiftClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInducedClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInducedAssembly
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SourceSmoothness
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInducedShift

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.InducedUpToLevel

variable {n : ℕ} {D : InducingData n} {side : Side} {s : ℂ}

/-- `IsInduced D side s f` with the finite-level-invariance conjunct dropped. -/
def IsInducedUpToLevel (D : InducingData n) (side : Side) (s : ℂ)
    (f : AdelicGL → ℂ) : Prop :=
  (∀ g, Smooth (fun x : Fin 1 → RealGL3 => f (g * atInfinity (x 0)))) ∧
  HasSmoothCuspLift D side s (fun (_ : Fin 0 → RealGL3) => f) ∧
  match side with
  | .plane =>
    (∀ a b g, f (planeUnipotent a b * g) = f g) ∧
    (∀ t g, f (planeLevi 1 t * g) =
      D.chi.toMonoidHom t * normPower t (-2*inductionExponent .plane s) * f g) ∧
    (∀ g, (fun A : BinaryAdelicGL =>
      normPower (GeneralLinearGroup.det A) (-(((n:ℂ)+3)/2 + inductionExponent .plane s)) *
        f (planeLevi A 1 * g)) ∈ cuspFunctions D.cusp)
  | .line =>
    (∀ a b g, f (lineUnipotent a b * g) = f g) ∧
    (∀ t g, f (lineLevi t 1 * g) =
      D.chi.toMonoidHom t * normPower t (2*inductionExponent .line s) * f g) ∧
    (∀ g, (fun A : BinaryAdelicGL =>
      normPower (GeneralLinearGroup.det A) (-(((n:ℂ)+3)/2 - inductionExponent .line s)) *
        f (lineLevi 1 A * g)) ∈ cuspFunctions D.cusp)

theorem isInducedUpToLevel_of_isInduced {f : AdelicGL → ℂ} (hf : IsInduced D side s f) :
    IsInducedUpToLevel D side s f :=
  ⟨hf.1, hf.2.2.1, hf.2.2.2⟩

theorem isInduced_of_upToLevel {f : AdelicGL → ℂ} (hu : IsInducedUpToLevel D side s f)
    (hk : ∀ k : finiteLevel, ∀ g, f (g * atFinite k.val) = f g) :
    IsInduced D side s f :=
  ⟨hu.1, hk, hu.2.1, hu.2.2⟩

theorem isInducedUpToLevel_add {f g : AdelicGL → ℂ}
    (hf : IsInducedUpToLevel D side s f) (hg : IsInducedUpToLevel D side s g) :
    IsInducedUpToLevel D side s (fun z => f z + g z) := by
  refine ⟨?_, HasSmoothCuspLiftClosure.hasSmoothCuspLift_add hf.2.1 hg.2.1, ?_⟩
  · intro G
    simpa only [Pi.add_apply] using SmoothClosure.smooth_add (hf.1 G) (hg.1 G)
  · cases side with
    | plane =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        simp only [hf.2.2.1 a b G, hg.2.2.1 a b G]
      · intro t G
        simp only [hf.2.2.2.1 t G, hg.2.2.2.1 t G]
        ring
      · intro G
        have h1 := hf.2.2.2.2 G
        have h2 := hg.2.2.2.2 G
        have he : (fun A : BinaryAdelicGL =>
              normPower (GeneralLinearGroup.det A)
                  (-(((n : ℂ) + 3) / 2 + inductionExponent .plane s)) *
                (fun z => f z + g z) (planeLevi A 1 * G))
            = (fun A : BinaryAdelicGL =>
                normPower (GeneralLinearGroup.det A)
                  (-(((n : ℂ) + 3) / 2 + inductionExponent .plane s)) *
                f (planeLevi A 1 * G)) +
              (fun A : BinaryAdelicGL =>
                normPower (GeneralLinearGroup.det A)
                  (-(((n : ℂ) + 3) / 2 + inductionExponent .plane s)) *
                g (planeLevi A 1 * G)) := by
          funext A; simp only [Pi.add_apply]; ring
        rw [he]; exact Submodule.add_mem _ h1 h2
    | line =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        simp only [hf.2.2.1 a b G, hg.2.2.1 a b G]
      · intro t G
        simp only [hf.2.2.2.1 t G, hg.2.2.2.1 t G]
        ring
      · intro G
        have h1 := hf.2.2.2.2 G
        have h2 := hg.2.2.2.2 G
        have he : (fun A : BinaryAdelicGL =>
              normPower (GeneralLinearGroup.det A)
                  (-(((n : ℂ) + 3) / 2 - inductionExponent .line s)) *
                (fun z => f z + g z) (lineLevi 1 A * G))
            = (fun A : BinaryAdelicGL =>
                normPower (GeneralLinearGroup.det A)
                  (-(((n : ℂ) + 3) / 2 - inductionExponent .line s)) *
                f (lineLevi 1 A * G)) +
              (fun A : BinaryAdelicGL =>
                normPower (GeneralLinearGroup.det A)
                  (-(((n : ℂ) + 3) / 2 - inductionExponent .line s)) *
                g (lineLevi 1 A * G)) := by
          funext A; simp only [Pi.add_apply]; ring
        rw [he]; exact Submodule.add_mem _ h1 h2

theorem isInducedUpToLevel_finset_sum {ι : Type*} (S : Finset ι) (f : ι → AdelicGL → ℂ)
    (h : ∀ i ∈ S, IsInducedUpToLevel D side s (f i)) :
    IsInducedUpToLevel D side s (fun g => ∑ i ∈ S, f i g) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simpa only [Finset.sum_empty] using
      isInducedUpToLevel_of_isInduced
        (IsInducedAssembly.isInduced_zero (D := D) (side := side) (s := s))
  · intro a S ha ih h
    have he : (fun g => ∑ i ∈ insert a S, f i g) = fun g => f a g + ∑ i ∈ S, f i g := by
      funext g; rw [Finset.sum_insert ha]
    rw [he]
    exact isInducedUpToLevel_add (h a (Finset.mem_insert_self a S))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The level-free part of the right-shift closure: right translation by
`rationalGroup r` preserves every `IsInduced` conjunct except finite-level
invariance. -/
theorem isInducedUpToLevel_right_shift (r : RationalGL3) {f : AdelicGL → ℂ}
    (hf : IsInducedUpToLevel D side s f) :
    IsInducedUpToLevel D side s (fun z => f (z * rationalGroup r)) := by
  have hdet : (((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val).det ≠ 0 :=
    GeneralLinearGroup.det_ne_zero _
  have hstep : ∀ x : RealGL3,
      atInfinity x * rationalGroup r =
        rationalGroup r * atInfinity
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x *
            GeneralLinearGroup.map (algebraMap ℚ ℝ) r) :=
    fun x => HeckeInvariance.atInfinity_mul_rationalGroup x r
  refine ⟨?_, ?_, ?_⟩
  · intro G
    have hsrc := hf.1 (G * rationalGroup r)
    have hcomp := SmoothTransport.Smooth.comp_conj
      (F := fun x' : Fin 1 → RealGL3 => f ((G * rationalGroup r) * atInfinity (x' 0)))
      hsrc (((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val) hdet
    refine SmoothClosure.smooth_congr hcomp (fun x₁ => ?_)
    simp only []
    congr 1
    calc G * atInfinity (x₁ 0) * rationalGroup r
        = G * (atInfinity (x₁ 0) * rationalGroup r) := by group
      _ = G * (rationalGroup r * atInfinity
            ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
              GeneralLinearGroup.map (algebraMap ℚ ℝ) r)) := by rw [hstep]
      _ = (G * rationalGroup r) * atInfinity
            (invertibleMatrix ((((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val) * (x₁ 0).val *
              ((((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val)⁻¹))) := by
          rw [← SourceSmoothness.invertibleMatrix_conj_eq r (x₁ 0)]
          group
  · intro a
    obtain ⟨v₀, hv₁, hv₂⟩ := hf.2.1 (a * rationalGroup r)
    refine ⟨fun x₁ : Fin 1 → RealGL3 => v₀ (fun _ : Fin 1 =>
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
          GeneralLinearGroup.map (algebraMap ℚ ℝ) r), ?_, ?_⟩
    · have hcomp := SmoothTransport.Smooth.comp_conj
        (F := fun x' : Fin 1 → RealGL3 => (v₀ x').val) hv₁
        (((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val) hdet
      refine SmoothClosure.smooth_congr hcomp (fun x₁ => ?_)
      simp only []
      refine congrArg (Submodule.subtype D.cusp.smooth) ?_
      refine congrArg v₀ ?_
      funext i
      fin_cases i
      exact (SourceSmoothness.invertibleMatrix_conj_eq r (x₁ 0)).symm
    · intro x₁ A
      show D.cusp.realize (v₀ (fun _ : Fin 1 =>
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
              GeneralLinearGroup.map (algebraMap ℚ ℝ) r)) A =
          normPower (GeneralLinearGroup.det A) (-binaryInductionExponent n side s) *
            f (binaryLevi side A * (a * atInfinity (x₁ 0)) * rationalGroup r)
      rw [hv₂ (fun _ : Fin 1 => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
            GeneralLinearGroup.map (algebraMap ℚ ℝ) r) A]
      simp only []
      congr 1
      congr 1
      calc binaryLevi side A * ((a * rationalGroup r) * atInfinity
              ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
                GeneralLinearGroup.map (algebraMap ℚ ℝ) r))
          = binaryLevi side A * (a * (rationalGroup r * atInfinity
              ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
                GeneralLinearGroup.map (algebraMap ℚ ℝ) r))) := by group
        _ = binaryLevi side A * (a * (atInfinity (x₁ 0) * rationalGroup r)) := by rw [← hstep]
        _ = binaryLevi side A * (a * atInfinity (x₁ 0)) * rationalGroup r := by group
  · cases side with
    | plane =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        show f (planeUnipotent a b * G * rationalGroup r) = f (G * rationalGroup r)
        rw [mul_assoc]; exact hf.2.2.1 a b (G * rationalGroup r)
      · intro t G
        show f (planeLevi 1 t * G * rationalGroup r) =
          D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane s) *
            f (G * rationalGroup r)
        rw [mul_assoc]; exact hf.2.2.2.1 t (G * rationalGroup r)
      · intro G
        simpa only [mul_assoc] using hf.2.2.2.2 (G * rationalGroup r)
    | line =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        show f (lineUnipotent a b * G * rationalGroup r) = f (G * rationalGroup r)
        rw [mul_assoc]; exact hf.2.2.1 a b (G * rationalGroup r)
      · intro t G
        show f (lineLevi t 1 * G * rationalGroup r) =
          D.chi.toMonoidHom t * normPower t (2 * inductionExponent .line s) *
            f (G * rationalGroup r)
        rw [mul_assoc]; exact hf.2.2.2.1 t (G * rationalGroup r)
      · intro G
        simpa only [mul_assoc] using hf.2.2.2.2 (G * rationalGroup r)

end TernaryPeriodPolynomials.HeckeTranslate.InducedUpToLevel

end
