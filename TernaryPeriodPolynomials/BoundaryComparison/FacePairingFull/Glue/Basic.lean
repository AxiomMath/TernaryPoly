module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Lift

@[expose] public section


/-!
# Coordinates of the Rep-level pairing: evaluation of diagonals on basis simplices

* `rHom r : Wℂ ⟶ 𝟙_` is the equivariant map `ℂ → ℚ` given by a `ℚ`-linear functional `r`;
* `delta_pair_single`: `(Δ_{p,q} ≫ (f ⊗ g) ≫ π)` evaluated on the basis simplex `(x; z)` is `π (f(front) ⊗ g(back))`;
* `vertexHom`: the Rep-level `ℚ`-valued 3-cochain attached to an invariant scalar 3-cochain `γ` on the labels `X` and a
  functional `r`, with `vertexHom_d` (its coboundary evaluated on a basis simplex is `r (dγ)`);
* faces of simplices as `![x 0, …]`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction

/-- The equivariant map from the trivial complex representation to the trivial rational one given by `r`. -/
def rHom (r : ℂ →ₗ[ℚ] ℚ) : Wℂ ⟶ 𝟙_ (Rep.{0} ℚ Γ6) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ r (fun g x => by simp))

theorem rHom_apply (r : ℂ →ₗ[ℚ] ℚ) (x : ℂ) : (rHom r).hom x = r x := rfl

theorem hom4_apply {X : Rep.{0} ℚ Γ6} (A B C D : X ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (t : X) :
    (A + B - C + D).hom t = A.hom t + B.hom t - C.hom t + D.hom t := rfl

section Faces

theorem front_1 (x : Fin 4 → RationalGL3) (h : 1 ≤ 3) : x ∘ frontIdx 1 3 h = ![x 0, x 1] := by
  funext j; fin_cases j <;> rfl

theorem back_1 (x : Fin 4 → RationalGL3) (h : 1 + 2 = 3) : x ∘ backIdx 1 2 3 h = ![x 1, x 2, x 3] := by
  funext j; fin_cases j <;> rfl

theorem front_2 (x : Fin 4 → RationalGL3) (h : 2 ≤ 3) : x ∘ frontIdx 2 3 h = ![x 0, x 1, x 2] := by
  funext j; fin_cases j <;> rfl

theorem back_2 (x : Fin 4 → RationalGL3) (h : 2 + 1 = 3) : x ∘ backIdx 2 1 3 h = ![x 2, x 3] := by
  funext j; fin_cases j <;> rfl

theorem front_3 (x : Fin 5 → RationalGL3) (h : 2 ≤ 4) : x ∘ frontIdx 2 4 h = ![x 0, x 1, x 2] := by
  funext j; fin_cases j <;> rfl

theorem back_3 (x : Fin 5 → RationalGL3) (h : 2 + 2 = 4) : x ∘ backIdx 2 2 4 h = ![x 2, x 3, x 4] := by
  funext j; fin_cases j <;> rfl

end Faces

section Delta

variable {V Z : Type} [MulAction Γ6 V] [MulAction Γ6 Z]

/-- The diagonal followed by a pairing of two cochains, on a basis simplex. -/
theorem delta_pair_single {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (p q n : ℕ)
    (h : p + q = n) (f : (prodComplex Γ6 V Z).X p ⟶ W) (g : (prodComplex Γ6 V Z).X q ⟶ W')
    (s : (Fin (n + 1) → V) × Z) :
    (nerveDelta Γ6 V Z p q n h ≫ (f ⊗ₘ g) ≫ π).hom (MonoidAlgebra.single s 1) =
      π.hom (f.hom (MonoidAlgebra.single (frontFace V Z p n (by omega) s) 1) ⊗ₜ[ℚ]
        g.hom (MonoidAlgebra.single (backFace V Z p q n h s) 1)) := by
  change π.hom ((f ⊗ₘ g).hom ((nerveDelta Γ6 V Z p q n h).hom (MonoidAlgebra.single s 1))) = _
  rw [nerveDelta_single]
  exact congrArg π.hom (tensorHom_tmul' f g _ _)

end Delta

section Vertex

variable {X Z : Type} [MulAction RationalGL3 X] [MulAction Γ6 Z] (ψ : X ≃ Z)
  (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x)

/-- The Rep-level `ℚ`-valued 3-cochain attached to an invariant scalar 3-cochain `γ` of the labels `X`. -/
def vertexHom (r : ℂ →ₗ[ℚ] ℚ) (γ : (Fin 4 → RationalGL3) → X → ℂ)
    (hγ : γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial X) 3) :
    (prodComplex Γ6 RationalGL3 Z).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6) :=
  toHom ψ hψ 3 ⟨γ, cochains_mono _ N6_le_rationalLevel 3 hγ⟩ ≫ rHom r

theorem vertexHom_single (r : ℂ →ₗ[ℚ] ℚ) (γ : (Fin 4 → RationalGL3) → X → ℂ)
    (hγ : γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial X) 3)
    (x : Fin 4 → RationalGL3) (z : Z) :
    (vertexHom ψ hψ r γ hγ).hom (MonoidAlgebra.single (x, z) 1) = r (γ x (ψ.symm z)) := by
  change (rHom r).hom ((toHom ψ hψ 3 ⟨γ, cochains_mono _ N6_le_rationalLevel 3 hγ⟩).hom _) = _
  rw [rHom_apply]
  exact congrArg r (toHom_val ψ hψ 3 ⟨γ, cochains_mono _ N6_le_rationalLevel 3 hγ⟩ x z)

theorem vertexHom_d_single (r : ℂ →ₗ[ℚ] ℚ) (γ : (Fin 4 → RationalGL3) → X → ℂ)
    (hγ : γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial X) 3)
    (x : Fin 5 → RationalGL3) (z : Z) :
    ((prodComplex Γ6 RationalGL3 Z).d 4 3 ≫ vertexHom ψ hψ r γ hγ).hom (MonoidAlgebra.single (x, z) 1) =
      r (differentialThreeRaw γ x (ψ.symm z)) := by
  change (rHom r).hom ((((prodComplex Γ6 RationalGL3 Z).d 4 3) ≫
    toHom ψ hψ 3 ⟨γ, cochains_mono _ N6_le_rationalLevel 3 hγ⟩).hom _) = _
  rw [rHom_apply]
  exact congrArg r (homFun_d_toHom_three ψ hψ ⟨γ, cochains_mono _ N6_le_rationalLevel 3 hγ⟩ x z)

end Vertex

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
