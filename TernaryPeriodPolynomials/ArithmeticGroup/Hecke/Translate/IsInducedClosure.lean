/-
  The set of functions satisfying `IsInduced D side s` is closed under addition
  and ℂ-scalar multiplication.  Together with `Smooth` closure and
  `hasSmoothCuspLift_add/smul`, this makes the Hecke translate's coefficients
  inherit `IsInduced` from the source cocycle by linearity, avoiding an explicit
  transported smooth-vector family.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HasSmoothCuspLiftClosure

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix MvPolynomial
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.IsInducedClosure

variable {n : ℕ} {D : InducingData n} {side : Side} {s : ℂ}

theorem isInduced_add {f g : AdelicGL → ℂ}
    (hf : IsInduced D side s f) (hg : IsInduced D side s g) :
    IsInduced D side s (fun z => f z + g z) := by
  refine ⟨?_, ?_, HasSmoothCuspLiftClosure.hasSmoothCuspLift_add hf.2.2.1 hg.2.2.1, ?_⟩
  · intro G
    simpa only [Pi.add_apply] using SmoothClosure.smooth_add (hf.1 G) (hg.1 G)
  · intro k G
    simp only [hf.2.1 k G, hg.2.1 k G]
  · cases side with
    | plane =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        simp only [hf.2.2.2.1 a b G, hg.2.2.2.1 a b G]
      · intro t G
        simp only [hf.2.2.2.2.1 t G, hg.2.2.2.2.1 t G]
        ring
      · intro G
        have h1 := hf.2.2.2.2.2 G
        have h2 := hg.2.2.2.2.2 G
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
        simp only [hf.2.2.2.1 a b G, hg.2.2.2.1 a b G]
      · intro t G
        simp only [hf.2.2.2.2.1 t G, hg.2.2.2.2.1 t G]
        ring
      · intro G
        have h1 := hf.2.2.2.2.2 G
        have h2 := hg.2.2.2.2.2 G
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

theorem isInduced_smul (c : ℂ) {f : AdelicGL → ℂ}
    (hf : IsInduced D side s f) :
    IsInduced D side s (fun z => c * f z) := by
  refine ⟨?_, ?_, HasSmoothCuspLiftClosure.hasSmoothCuspLift_smul c hf.2.2.1, ?_⟩
  · intro G
    simpa only [smul_eq_mul] using HasSmoothCuspLiftClosure.smooth_smul_complex c (hf.1 G)
  · intro k G
    simp only [hf.2.1 k G]
  · cases side with
    | plane =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        simp only [hf.2.2.2.1 a b G]
      · intro t G
        simp only [hf.2.2.2.2.1 t G]
        ring
      · intro G
        have h1 := hf.2.2.2.2.2 G
        have he : (fun A : BinaryAdelicGL =>
              normPower (GeneralLinearGroup.det A)
                  (-(((n : ℂ) + 3) / 2 + inductionExponent .plane s)) *
                (fun z => c * f z) (planeLevi A 1 * G))
            = c • (fun A : BinaryAdelicGL =>
                normPower (GeneralLinearGroup.det A)
                  (-(((n : ℂ) + 3) / 2 + inductionExponent .plane s)) *
                f (planeLevi A 1 * G)) := by
          funext A; simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [he]; exact Submodule.smul_mem _ c h1
    | line =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        simp only [hf.2.2.2.1 a b G]
      · intro t G
        simp only [hf.2.2.2.2.1 t G]
        ring
      · intro G
        have h1 := hf.2.2.2.2.2 G
        have he : (fun A : BinaryAdelicGL =>
              normPower (GeneralLinearGroup.det A)
                  (-(((n : ℂ) + 3) / 2 - inductionExponent .line s)) *
                (fun z => c * f z) (lineLevi 1 A * G))
            = c • (fun A : BinaryAdelicGL =>
                normPower (GeneralLinearGroup.det A)
                  (-(((n : ℂ) + 3) / 2 - inductionExponent .line s)) *
                f (lineLevi 1 A * G)) := by
          funext A; simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [he]; exact Submodule.smul_mem _ c h1

end TernaryPeriodPolynomials.HeckeTranslate.IsInducedClosure

end
