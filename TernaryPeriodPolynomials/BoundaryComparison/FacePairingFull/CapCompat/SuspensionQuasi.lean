module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Suspension
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso

@[expose] public section


/-!
# The chain suspension preserves quasi-isomorphisms

`TernaryPoly.BoundaryFaceResolutionComparison.Suspension.map f` is a quasi-isomorphism when `f` is: the suspension has the
same cycles and boundaries, shifted by one (its differential is `-d`), so the shifted short complexes of the two
complexes are related by sign-twisted comparison maps that are quasi-isomorphisms.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits ZeroObject
open TernaryPoly.BoundaryFaceResolutionComparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {C : Type*} [Category* C] [Abelian C]

theorem suspension_map_quasiIso {A B : ChainComplex C ℕ} (f : A ⟶ B) [QuasiIso f] :
    QuasiIso (Suspension.map f) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
    have hA : (Suspension.obj A).ExactAt 0 := by
      rw [HomologicalComplex.exactAt_iff]
      exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
    have hB : (Suspension.obj B).ExactAt 0 := by
      rw [HomologicalComplex.exactAt_iff]
      exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
    exact (quasiIsoAt_iff_exactAt _ _ hA).2 hB
  | succ m =>
    have hf : QuasiIsoAt f m := inferInstance
    cases m with
    | zero =>
      rw [quasiIsoAt_iff' f 1 0 0 (by simp) (by simp)] at hf
      rw [quasiIsoAt_iff' (Suspension.map f) 2 1 0 (by simp) (by simp)]
      let θ : ∀ X : ChainComplex C ℕ, (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 2 1 0).obj
          (Suspension.obj X) ⟶ (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).obj X :=
        fun X => { τ₁ := -𝟙 (X.X 1), τ₂ := 𝟙 (X.X 0), τ₃ := 0
                   comm₁₂ := by
                     change (-𝟙 (X.X 1)) ≫ X.d 1 0 = (-X.d 1 0) ≫ 𝟙 (X.X 0)
                     simp
                   comm₂₃ := by
                     change 𝟙 (X.X 0) ≫ X.d 0 0 = (0 : X.X 0 ⟶ 0) ≫ 0
                     simp }
      have hθ : ∀ X : ChainComplex C ℕ, ShortComplex.QuasiIso (θ X) := fun X => by
        have : Epi (θ X).τ₁ := by
          change Epi (-𝟙 (X.X 1))
          infer_instance
        have : IsIso (θ X).τ₂ := by
          change IsIso (𝟙 (X.X 0))
          infer_instance
        have : Mono (θ X).τ₃ := by
          change Mono (0 : (0 : C) ⟶ X.X 0)
          infer_instance
        exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono _
      have hsq : (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 2 1 0).map (Suspension.map f) ≫
          θ B = θ A ≫ (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map f := by
        refine ShortComplex.Hom.ext ?_ ?_ ?_
        · change f.f 1 ≫ (-𝟙 (B.X 1)) = (-𝟙 (A.X 1)) ≫ f.f 1
          simp
        · change f.f 0 ≫ 𝟙 (B.X 0) = 𝟙 (A.X 0) ≫ f.f 0
          simp
        · exact (isZero_zero C).eq_of_src _ _
      have := hθ A
      have := hθ B
      have h1 : ShortComplex.QuasiIso (θ A ≫ (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map f) :=
        (ShortComplex.quasiIso_iff_comp_left _ _).2 hf
      rw [← hsq] at h1
      exact (ShortComplex.quasiIso_iff_comp_right _ _).1 h1
    | succ m =>
      rw [quasiIsoAt_iff' f (m+2) (m+1) m (by simp) (by simp)] at hf
      rw [quasiIsoAt_iff' (Suspension.map f) (m+3) (m+2) (m+1) (by simp) (by simp)]
      let θ : ∀ X : ChainComplex C ℕ, (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) (m+3) (m+2) (m+1)).obj
          (Suspension.obj X) ⟶ (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) (m+2) (m+1) m).obj X :=
        fun X => { τ₁ := -𝟙 (X.X (m+2)), τ₂ := 𝟙 (X.X (m+1)), τ₃ := -𝟙 (X.X m)
                   comm₁₂ := by
                     change (-𝟙 (X.X (m+2))) ≫ X.d (m+2) (m+1) = (-X.d (m+2) (m+1)) ≫ 𝟙 (X.X (m+1))
                     simp
                   comm₂₃ := by
                     change 𝟙 (X.X (m+1)) ≫ X.d (m+1) m = (-X.d (m+1) m) ≫ (-𝟙 (X.X m))
                     simp }
      have hθ : ∀ X : ChainComplex C ℕ, ShortComplex.QuasiIso (θ X) := fun X => by
        have : Epi (θ X).τ₁ := by
          change Epi (-𝟙 (X.X (m+2)))
          infer_instance
        have : IsIso (θ X).τ₂ := by
          change IsIso (𝟙 (X.X (m+1)))
          infer_instance
        have : Mono (θ X).τ₃ := by
          change Mono (-𝟙 (X.X m))
          infer_instance
        exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono _
      have hsq : (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) (m+3) (m+2) (m+1)).map (Suspension.map f) ≫
          θ B = θ A ≫ (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) (m+2) (m+1) m).map f := by
        refine ShortComplex.Hom.ext ?_ ?_ ?_
        · change f.f (m+2) ≫ (-𝟙 (B.X (m+2))) = (-𝟙 (A.X (m+2))) ≫ f.f (m+2)
          simp
        · change f.f (m+1) ≫ 𝟙 (B.X (m+1)) = 𝟙 (A.X (m+1)) ≫ f.f (m+1)
          simp
        · change f.f m ≫ (-𝟙 (B.X m)) = (-𝟙 (A.X m)) ≫ f.f m
          simp
      have := hθ A
      have := hθ B
      have h1 : ShortComplex.QuasiIso (θ A ≫ (HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) (m+2) (m+1) m).map f) :=
        (ShortComplex.quasiIso_iff_comp_left _ _).2 hf
      rw [← hsq] at h1
      exact (ShortComplex.quasiIso_iff_comp_right _ _).1 h1

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
