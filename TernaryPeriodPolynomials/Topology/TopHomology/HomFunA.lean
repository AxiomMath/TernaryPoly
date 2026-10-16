module

public import TernaryPeriodPolynomials.Topology.TopHomology.FreeNerve

@[expose] public section


/-!
# Morphisms out of the model resolutions into a general representation

The functions `homFun` of `TopHomology.FreeNerve` attached to a morphism `c : prodComplex ⟶ A` into a
*trivial* representation are generalized to an arbitrary rational representation `A`: `homFunA c` is the
equivariant function `y ↦ c(y)`, and the differential and the chain maps of `prodComplex` act on it by
the alternating sum of faces (`homFunA_comp_d`) and by precomposition (`homFunA_comp_map`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.TopHomology

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] {A : Rep.{0} ℚ Γ}

/-- The function `y ↦ c(y)` attached to a morphism out of the model resolution into `A`. -/
def homFunA {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ A) : (Fin (k + 1) → V) × Z → A :=
  fun y => c.hom (MonoidAlgebra.single y 1)

theorem homFunA_equivariant {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ A) (γ : Γ)
    (y : (Fin (k + 1) → V) × Z) : homFunA c (γ • y) = A.ρ γ (homFunA c y) :=
  (homFunEquiv ((Fin (k + 1) → V) × Z) A c).2 γ y

theorem homFunA_injective {k : ℕ} {c c' : (prodComplex Γ V Z).X k ⟶ A}
    (h : homFunA c = homFunA c') : c = c' :=
  hom_ext_single ((Fin (k + 1) → V) × Z) A (fun y => congrFun h y)

/-- The morphism attached to an equivariant function. -/
def homOfFunA {k : ℕ} (F : (Fin (k + 1) → V) × Z → A)
    (hF : ∀ (γ : Γ) y, F (γ • y) = A.ρ γ (F y)) : (prodComplex Γ V Z).X k ⟶ A :=
  ofMulActionLift ((Fin (k + 1) → V) × Z) A F hF

theorem homFunA_homOfFunA {k : ℕ} (F : (Fin (k + 1) → V) × Z → A)
    (hF : ∀ (γ : Γ) y, F (γ • y) = A.ρ γ (F y)) : homFunA (homOfFunA F hF) = F := by
  funext y
  exact ofMulActionLift_single ((Fin (k + 1) → V) × Z) A F hF y

theorem homOfFunA_homFunA {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ A) :
    homOfFunA (homFunA c) (homFunA_equivariant c) = c :=
  homFunA_injective (homFunA_homOfFunA _ _)

theorem homFunA_add {k : ℕ} (c c' : (prodComplex Γ V Z).X k ⟶ A) :
    homFunA (c + c') = homFunA c + homFunA c' := rfl

theorem homFunA_smul {k : ℕ} (r : ℚ) (c : (prodComplex Γ V Z).X k ⟶ A) :
    homFunA (r • c) = r • homFunA c := rfl

theorem homFunA_comp_d {k : ℕ} (c : (prodComplex Γ V Z).X k ⟶ A)
    (y : (Fin (k + 2) → V) × Z) :
    homFunA ((prodComplex Γ V Z).d (k + 1) k ≫ c) y =
      ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • homFunA c (face V Z i y) := by
  have h := prodComplex_d_comp_eq Γ V Z k c
  change ((prodComplex Γ V Z).d (k + 1) k ≫ c).hom (MonoidAlgebra.single y 1) = _
  rw [h]
  erw [Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [Rep.zsmul_hom]
  exact congrArg (fun w => ((-1 : ℤ) ^ (i : ℕ)) • c.hom w) (delta_single Γ V Z k i y)

theorem homFunA_comp_map {Z' : Type} [MulAction Γ Z'] (α : Z → Z')
    (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) {k : ℕ}
    (c : (prodComplex Γ V Z').X k ⟶ A) (x : Fin (k + 1) → V) (z : Z) :
    homFunA ((prodMapHom Γ V Z α hα).f k ≫ c) (x, z) = homFunA c (x, α z) := by
  change c.hom (((prodMapHom Γ V Z α hα).f k).hom (MonoidAlgebra.single (x, z) 1)) = _
  rw [prodMapHom_f_single]
  rfl

end TernaryPeriodPolynomials.Argument.TopHomology
