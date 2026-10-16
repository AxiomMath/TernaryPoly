module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.DiagCup
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CupProduct

@[expose] public section


/-!
# The model diagonal in bidegrees `(1,2)` and `(2,1)` is the inhomogeneous cup product

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (S : Subgroup Γ) (v₀ : V) (z : Z)
  (hz : ∀ s : S, (s : Γ) • z = z) {W W' : Rep.{0} ℚ Γ} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ))

/-- The pairing `W × W' → ℚ` of a morphism `π : W ⊗ W' ⟶ 𝟙`. -/
def pairOf : W →ₗ[ℚ] W' →ₗ[ℚ] ℚ := (TensorProduct.mk ℚ W W').compr₂ π.hom.toLinearMap

/-- `π` is invariant: the pairing is invariant under the group. -/
theorem pairOf_inv (g : Γ) (a : W) (b : W') : pairOf π (W.ρ g a) (W'.ρ g b) = pairOf π a b := by
  have h := Rep.hom_comm_apply π g (a ⊗ₜ[ℚ] b)
  simpa [pairOf] using h

include hz in
/-- **The model diagonal in bidegree `(1,2)` on a bar simplex is the inhomogeneous cup product** `cup12` of the bar cochains. -/
theorem diag12_bar (f : (prodComplex Γ V Z).X 1 ⟶ W) (g : (prodComplex Γ V Z).X 2 ⟶ W') (x : Fin 3 → S) :
    (nerveDelta Γ V Z 1 2 3 rfl ≫ (f ⊗ₘ g) ≫ π).hom (MonoidAlgebra.single (barSimplex S v₀ z x) 1) =
      cup12 ((W'.ρ).comp S.subtype) (pairOf π) (fun s : S => barCochain S v₀ z f (fun _ : Fin 1 => s))
        (fun s t : S => barCochain S v₀ z g (fun j : Fin 2 => if j = 0 then s else t)) (x 0) (x 1) (x 2) := by
  refine (diag_pair_bar S v₀ z hz π 1 2 f g x).trans ?_
  have e1 : (fun j : Fin 1 => x ⟨j.1, by omega⟩) = fun _ => x 0 := by
    funext j; fin_cases j; rfl
  have e2 : (Fin.partialProd x ⟨1, by omega⟩ : S) = x 0 := by
    have h := pp_succ x 0 (by omega)
    have h0 : Fin.partialProd x ⟨0, by omega⟩ = 1 := Fin.partialProd_zero x
    rw [h0, one_mul] at h
    exact h
  have e3 : (fun j : Fin 2 => x ⟨1 + j.1, by omega⟩) = fun j => if j = 0 then x 1 else x 2 := by
    funext j; fin_cases j <;> rfl
  rw [e1, e2, e3]
  rfl

include hz in
/-- … in bidegree `(2,1)` it is the product `cup21`. -/
theorem diag21_bar (f : (prodComplex Γ V Z).X 2 ⟶ W) (g : (prodComplex Γ V Z).X 1 ⟶ W') (x : Fin 3 → S) :
    (nerveDelta Γ V Z 2 1 3 rfl ≫ (f ⊗ₘ g) ≫ π).hom (MonoidAlgebra.single (barSimplex S v₀ z x) 1) =
      cup21 ((W'.ρ).comp S.subtype) (pairOf π)
        (fun s t : S => barCochain S v₀ z f (fun j : Fin 2 => if j = 0 then s else t))
        (fun s : S => barCochain S v₀ z g (fun _ : Fin 1 => s)) (x 0) (x 1) (x 2) := by
  refine (diag_pair_bar S v₀ z hz π 2 1 f g x).trans ?_
  have e1 : (fun j : Fin 2 => x ⟨j.1, by omega⟩) = fun j => if j = 0 then x 0 else x 1 := by
    funext j; fin_cases j <;> rfl
  have e2 : (Fin.partialProd x ⟨2, by omega⟩ : S) = x 0 * x 1 := by
    have h1 := pp_succ x 1 (by omega)
    have h0 := pp_succ x 0 (by omega)
    have h00 : Fin.partialProd x ⟨0, by omega⟩ = 1 := Fin.partialProd_zero x
    rw [h00, one_mul] at h0
    rw [h0] at h1
    exact h1
  have e3 : (fun j : Fin 1 => x ⟨2 + j.1, by omega⟩) = fun _ => x 2 := by
    funext j; fin_cases j; rfl
  rw [e1, e2, e3]
  rfl

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
