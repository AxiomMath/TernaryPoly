module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Pairing

@[expose] public section


/-!
# Cutting the model resolutions along invariant subsets of the label set

Formalized by Claude Sonnet 5.5.

For a `Γ`-invariant subset `S ⊆ Z` the permutation complex `ℚ[V^{•+1} × Z]` of `prodComplex Γ V Z` is split by the idempotent chain map `cutHom S`,
`[x, z] ↦ [x, z]` for `z ∈ S` and `0` otherwise.  It commutes with the differentials and with the maps `prodMapHom` induced by equivariant maps of label
sets (up to preimage).  Applied to the cochains of a line or plane datum it gives the datum of the part supported on `S`.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open GeneralEisenstein
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation (flagLine flagLine_equivariant flagPlane flagPlane_equivariant)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

section Cut

variable (Γ : Type) [Group Γ] (V Z : Type) [MulAction Γ V] [MulAction Γ Z]
  (S : Set Z) (hS : ∀ (γ : Γ) (z : Z), γ • z ∈ S ↔ z ∈ S)

open Classical in
include hS in
/-- The idempotent of `ℚ[V^{k+1} × Z]` keeping the basis elements whose label lies in `S`. -/
def cutHom (k : ℕ) : (prodComplex Γ V Z).X k ⟶ (prodComplex Γ V Z).X k :=
  ofMulActionLift ((Fin (k + 1) → V) × Z) ((prodComplex Γ V Z).X k)
    (fun s => if s.2 ∈ S then (MonoidAlgebra.single s (1 : ℚ) : (prodComplex Γ V Z).X k) else 0)
    (fun γ s => by
      by_cases h : s.2 ∈ S
      · have h' : (γ • s).2 ∈ S := (hS γ s.2).2 h
        have h'' : γ • s.2 ∈ S := h'
        erw [ite_eq_left h'', ite_eq_left h]
        exact (X_ρ_single Γ V Z k γ s 1).symm
      · have h' : ¬ (γ • s).2 ∈ S := fun hh => h ((hS γ s.2).1 hh)
        have h'' : γ • s.2 ∉ S := h'
        erw [ite_eq_right h'', ite_eq_right h, map_zero])

open Classical in
theorem cutHom_single (k : ℕ) (s : (Fin (k + 1) → V) × Z) :
    ((cutHom Γ V Z S hS k).hom (MonoidAlgebra.single s 1)) =
      if s.2 ∈ S then (MonoidAlgebra.single s (1 : ℚ) : (prodComplex Γ V Z).X k) else 0 :=
  ofMulActionLift_single _ _ _ _ s

open Classical in
theorem cutHom_comm_d (k : ℕ) :
    (prodComplex Γ V Z).d (k + 1) k ≫ cutHom Γ V Z S hS k =
      cutHom Γ V Z S hS (k + 1) ≫ (prodComplex Γ V Z).d (k + 1) k := by
  refine hom_ext_single ((Fin (k + 2) → V) × Z) _ (fun y => ?_)
  change (cutHom Γ V Z S hS k).hom (((prodComplex Γ V Z).d (k + 1) k).hom (MonoidAlgebra.single y 1)) =
    ((prodComplex Γ V Z).d (k + 1) k).hom ((cutHom Γ V Z S hS (k + 1)).hom (MonoidAlgebra.single y 1))
  by_cases h : y.2 ∈ S
  · erw [cutHom_single Γ V Z S hS (k + 1) y, ite_eq_left h, d_single Γ V Z k y]
    refine (map_sum _ _ _).trans (Finset.sum_congr rfl (fun i _ => ?_))
    erw [map_zsmul, cutHom_single, ite_eq_left (show (face V Z i y).2 ∈ S from h)]
    rfl
  · erw [cutHom_single Γ V Z S hS (k + 1) y, ite_eq_right h, map_zero, d_single Γ V Z k y]
    refine (map_sum _ _ _).trans (Finset.sum_eq_zero (fun i _ => ?_))
    erw [map_zsmul, cutHom_single, ite_eq_right (show (face V Z i y).2 ∉ S from h)]
    exact smul_zero ((-1 : ℤ) ^ (i : ℕ))

end Cut


section Natural

variable {Γ : Type} [Group Γ] {V Z Z' : Type} [MulAction Γ V] [MulAction Γ Z] [MulAction Γ Z']

theorem preimage_invariant (α : Z → Z') (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) (S' : Set Z')
    (hS' : ∀ (γ : Γ) (z : Z'), γ • z ∈ S' ↔ z ∈ S') :
    ∀ (γ : Γ) (z : Z), γ • z ∈ α ⁻¹' S' ↔ z ∈ α ⁻¹' S' := by
  intro γ z
  change α (γ • z) ∈ S' ↔ α z ∈ S'
  rw [hα]
  exact hS' γ (α z)

open Classical in
/-- The cut of the permutation complex commutes with the maps induced by equivariant maps of label sets (up to preimage). -/
theorem cutHom_natural (α : Z → Z') (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) (S' : Set Z')
    (hS' : ∀ (γ : Γ) (z : Z'), γ • z ∈ S' ↔ z ∈ S') (k : ℕ) :
    cutHom Γ V Z (α ⁻¹' S') (preimage_invariant α hα S' hS') k ≫ (prodMapHom Γ V Z α hα).f k =
      (prodMapHom Γ V Z α hα).f k ≫ cutHom Γ V Z' S' hS' k := by
  refine hom_ext_single ((Fin (k + 1) → V) × Z) _ (fun y => ?_)
  obtain ⟨x, z⟩ := y
  change ((prodMapHom Γ V Z α hα).f k).hom ((cutHom Γ V Z (α ⁻¹' S') (preimage_invariant α hα S' hS') k).hom
      (MonoidAlgebra.single (x, z) 1)) =
    (cutHom Γ V Z' S' hS' k).hom (((prodMapHom Γ V Z α hα).f k).hom (MonoidAlgebra.single (x, z) 1))
  by_cases h : α z ∈ S'
  · erw [cutHom_single, ite_eq_left (show z ∈ α ⁻¹' S' from h), prodMapHom_f_single, cutHom_single, ite_eq_left h]
    rfl
  · erw [cutHom_single, ite_eq_right (show z ∉ α ⁻¹' S' from h), map_zero, prodMapHom_f_single, cutHom_single, ite_eq_right h]
    rfl

end Natural

end TernaryPeriodPolynomials.Argument.GammaNStokes
