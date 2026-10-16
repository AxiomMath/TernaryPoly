/-
  `HasSmoothCuspLift` is closed under finite linear combinations.

  This is the structural fact that lets the Hecke translate inherit its
  `HasSmoothCuspLift` clauses from the source cocycle without an explicit
  construction of the transported smooth vector family: a linear combination of
  smooth cusp-vector families realizes the linear combination of the functions,
  by linearity of `D.cusp.realize`.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothClosure

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.HasSmoothCuspLiftClosure

variable {n k : ℕ} {D : InducingData n} {side : Side} {s : ℂ}
variable {f g : (Fin k → RealGL3) → AdelicGL → ℂ}

theorem hasSmoothCuspLift_add
    (hf : HasSmoothCuspLift D side s f) (hg : HasSmoothCuspLift D side s g) :
    HasSmoothCuspLift D side s (fun x z => f x z + g x z) := by
  intro a
  obtain ⟨v, hv1, hv2⟩ := hf a
  obtain ⟨w, hw1, hw2⟩ := hg a
  refine ⟨fun x => v x + w x, ?_, ?_⟩
  · have he : (fun x : Fin (k + 1) → RealGL3 => (v x + w x).val)
        = fun x => (v x).val + (w x).val := by
      funext x; rw [Submodule.coe_add]
    rw [he]
    exact SmoothClosure.smooth_add hv1 hw1
  · intro x A
    rw [map_add, Pi.add_apply, hv2 x A, hw2 x A, mul_add]

theorem smooth_smul_complex {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℂ) {h : (Fin k → RealGL3) → E} (hh : Smooth h) :
    Smooth (fun x => c • h x) := by
  let φ : E →L[ℝ] E :=
    { toLinearMap :=
        { toFun := fun y => c • y
          map_add' := by intro a b; rw [smul_add]
          map_smul' := by intro r a; exact (smul_comm r c a).symm }
      cont := continuous_const_smul c }
  show ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      c • h (fun i => invertibleMatrix (A i))) {A | ∀ i, (A i).det ≠ 0}
  have hh' : ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      h (fun i => invertibleMatrix (A i))) {A | ∀ i, (A i).det ≠ 0} := hh
  exact (φ.contDiff).comp_contDiffOn hh'

theorem hasSmoothCuspLift_smul (c : ℂ)
    (hf : HasSmoothCuspLift D side s f) :
    HasSmoothCuspLift D side s (fun x g => c * f x g) := by
  intro a
  obtain ⟨v, hv1, hv2⟩ := hf a
  refine ⟨fun x => c • v x, ?_, ?_⟩
  · have he : (fun x : Fin (k + 1) → RealGL3 => (c • v x).val)
        = fun x => c • (v x).val := by
      funext x; rw [Submodule.coe_smul]
    rw [he]
    exact smooth_smul_complex c hv1
  · intro x A
    rw [show D.cusp.realize (c • v x) A = c * D.cusp.realize (v x) A from by
      rw [map_smul, Pi.smul_apply, smul_eq_mul]]
    rw [hv2 x A]; ring


theorem hasSmoothCuspLift_zero :
    HasSmoothCuspLift D side s
      (fun (_ : Fin k → RealGL3) (_ : AdelicGL) => (0 : ℂ)) := by
  intro a
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simpa only [Submodule.coe_zero] using SmoothClosure.smooth_zero (k := k + 1) (E := D.cusp.H)
  · intro x A; rw [map_zero]; simp

theorem hasSmoothCuspLift_finset_sum {ι : Type*}
    (S : Finset ι) (F : ι → (Fin k → RealGL3) → AdelicGL → ℂ)
    (h : ∀ i ∈ S, HasSmoothCuspLift D side s (F i)) :
    HasSmoothCuspLift D side s (fun x g => ∑ i ∈ S, F i x g) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simpa only [Finset.sum_empty] using
      (hasSmoothCuspLift_zero (D := D) (side := side) (s := s) (k := k))
  · intro i S hi ih h
    have he : (fun x g => ∑ j ∈ insert i S, F j x g)
        = fun x g => F i x g + (∑ j ∈ S, F j x g) := by
      funext x g; rw [Finset.sum_insert hi]
    rw [he]
    exact hasSmoothCuspLift_add (h i (Finset.mem_insert_self i S))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end TernaryPeriodPolynomials.HeckeTranslate.HasSmoothCuspLiftClosure

end
