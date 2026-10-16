module

public import TernaryPeriodPolynomials.Topology.TopHomology.HomFunA
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Inv

@[expose] public section


/-!
# The model cochains of `Γ(6)` with coefficients as morphisms out of the model resolutions

For a complex representation `ρ` of `GL₃(ℚ)` on a space `V` with a compatible rational structure, and a
`GL₃(ℚ)`-set `X` equivariantly in bijection with a `Γ(6)`-set `Z` (`ψ : X ≃ Z`), the homogeneous cochains
`cochains N6 (functionRepresentation ρ X) k` of the model are the same as the morphisms
`ℚ[V^{k+1} × Z] ⟶ ρ|_{Γ(6)}` of rational representations of `Γ(6)` out of the permutation modules of the
model resolution (`modelHomEquiv`), compatibly with the differentials (`homFunA_comp_d`).  This generalizes
`ModelInv`, which treats the scalar trivial coefficient system.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.LevelTransfer

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

section Coeff

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

/-- The restriction of a complex representation of `GL₃(ℚ)` to `Γ(6)`, as a rational representation. -/
def coeffRepr : Representation ℚ Γ6 V where
  toFun γ := (ρ (iotaQ γ)).restrictScalars ℚ
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp

/-- The rational representation of `Γ(6)` underlying `ρ|_{Γ(6)}`. -/
def coeffRep : Rep.{0} ℚ Γ6 := Rep.of (coeffRepr ρ)

theorem coeffRep_apply (γ : Γ6) (v : V) : (coeffRep ρ).ρ γ v = ρ (iotaQ γ) v := rfl

end Coeff

section Model

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)
  {X Z : Type} [MulAction RationalGL3 X] [MulAction Γ6 Z] (ψ : X ≃ Z)
  (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x)

/-- The function attached to a model cochain. -/
def modelFun {k : ℕ} (f : cochains N6 (functionRepresentation ρ X) k) :
    (Fin (k + 1) → RationalGL3) × Z → V :=
  fun y => f.1 y.1 (ψ.symm y.2)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
include hψ in
theorem modelFun_equivariant {k : ℕ} (f : cochains N6 (functionRepresentation ρ X) k) (γ : Γ6)
    (y : (Fin (k + 1) → RationalGL3) × Z) :
    modelFun ρ ψ f (γ • y) = ρ (iotaQ γ) (modelFun ρ ψ f y) := by
  have h1 := congrFun (f.2 ⟨iotaQ γ, iotaQ_mem γ⟩ y.1) (ψ.symm (γ • y.2))
  change f.1 (fun i => iotaQ γ * y.1 i) (ψ.symm (γ • y.2)) = ρ (iotaQ γ) (f.1 y.1 (ψ.symm y.2))
  rw [h1]
  change ((functionRepresentation ρ X) (iotaQ γ) (f.1 y.1)) (ψ.symm (γ • y.2)) = _
  simp only [functionRepresentation, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [symm_smul ψ hψ, inv_smul_smul]

/-- The morphism out of the model resolution attached to a model cochain. -/
def modelHomOf {k : ℕ} (f : cochains N6 (functionRepresentation ρ X) k) :
    (prodComplex Γ6 RationalGL3 Z).X k ⟶ coeffRep ρ :=
  homOfFunA (A := coeffRep ρ) (modelFun ρ ψ f) (fun γ y => modelFun_equivariant ρ ψ hψ f γ y)

/-- The model cochain attached to a morphism out of the model resolution. -/
def cochainOfHom {k : ℕ} (c : (prodComplex Γ6 RationalGL3 Z).X k ⟶ coeffRep ρ) :
    cochains N6 (functionRepresentation ρ X) k :=
  ⟨fun x e => homFunA c (x, ψ e), by
    intro n x
    funext e
    obtain ⟨γ, hγ⟩ := exists_iotaQ_eq n.2
    have h := homFunA_equivariant c γ (x, ψ ((n.val)⁻¹ • e))
    have h1 : γ • ψ ((n.val)⁻¹ • e) = ψ e := by
      rw [← hψ, hγ, smul_inv_smul]
    have h2 : (γ • (x, ψ ((n.val)⁻¹ • e)) : (Fin (k + 1) → RationalGL3) × Z) =
        (fun i => n.val * x i, ψ e) := by
      refine Prod.ext ?_ h1
      funext i
      change iotaQ γ * x i = n.val * x i
      rw [hγ]
    rw [h2] at h
    change homFunA c (fun i => n.val * x i, ψ e) = ρ n.val (homFunA c (x, ψ ((n.val)⁻¹ • e)))
    rw [h]
    rw [← hγ]
    rfl⟩

theorem homFunA_modelHomOf {k : ℕ} (f : cochains N6 (functionRepresentation ρ X) k) :
    homFunA (modelHomOf ρ ψ hψ f) = modelFun ρ ψ f :=
  homFunA_homOfFunA _ _

theorem modelHomOf_cochainOfHom {k : ℕ} (c : (prodComplex Γ6 RationalGL3 Z).X k ⟶ coeffRep ρ) :
    modelHomOf ρ ψ hψ (cochainOfHom ρ ψ hψ c) = c := by
  apply homFunA_injective
  rw [homFunA_modelHomOf]
  funext y
  change homFunA c (y.1, ψ (ψ.symm y.2)) = homFunA c y
  rw [Equiv.apply_symm_apply]

theorem cochainOfHom_modelHomOf {k : ℕ} (f : cochains N6 (functionRepresentation ρ X) k) :
    cochainOfHom ρ ψ hψ (modelHomOf ρ ψ hψ f) = f := by
  apply Subtype.ext
  funext x e
  change homFunA (modelHomOf ρ ψ hψ f) (x, ψ e) = f.1 x e
  rw [homFunA_modelHomOf]
  change f.1 x (ψ.symm (ψ e)) = f.1 x e
  rw [Equiv.symm_apply_apply]

theorem modelHomOf_add {k : ℕ} (f g : cochains N6 (functionRepresentation ρ X) k) :
    modelHomOf ρ ψ hψ (f + g) = modelHomOf ρ ψ hψ f + modelHomOf ρ ψ hψ g := by
  apply homFunA_injective
  rw [homFunA_add, homFunA_modelHomOf, homFunA_modelHomOf, homFunA_modelHomOf]
  rfl

theorem modelHomOf_smul {k : ℕ} (r : ℚ) (f : cochains N6 (functionRepresentation ρ X) k) :
    modelHomOf ρ ψ hψ (r • f) = r • modelHomOf ρ ψ hψ f := by
  apply homFunA_injective
  rw [homFunA_smul, homFunA_modelHomOf, homFunA_modelHomOf]
  rfl

omit [MulAction Γ6 Z] in
/-- The faces `0, 1, 2` of a two-simplex. -/
theorem face_two (y : (Fin 3 → RationalGL3) × Z) :
    (face RationalGL3 Z (0 : Fin 3) y = (![y.1 1, y.1 2], y.2)) ∧
    (face RationalGL3 Z (1 : Fin 3) y = (![y.1 0, y.1 2], y.2)) ∧
    (face RationalGL3 Z (2 : Fin 3) y = (![y.1 0, y.1 1], y.2)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · refine Prod.ext ?_ rfl
    funext j
    fin_cases j <;> rfl

theorem modelHomOf_differentialOne (f : cochains N6 (functionRepresentation ρ X) 1)
    (y : (Fin 3 → RationalGL3) × Z) :
    homFunA ((prodComplex Γ6 RationalGL3 Z).d 2 1 ≫ modelHomOf ρ ψ hψ f) y =
      modelFun ρ ψ (differentialOne N6 (functionRepresentation ρ X) f) y := by
  rw [homFunA_comp_d]
  simp only [homFunA_modelHomOf]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.univ_eq_empty,
    Finset.sum_empty]
  obtain ⟨h0, h1, h2⟩ := face_two (Z := Z) y
  simp only [Fin.succ_zero_eq_one, Fin.val_zero, Fin.val_one, Fin.succ_one_eq_two,
    pow_zero, pow_one, Fin.val_two, add_zero]
  rw [h0, h1, h2]
  change (1 : ℤ) • f.1 ![y.1 1, y.1 2] (ψ.symm y.2) +
      ((-1 : ℤ) • f.1 ![y.1 0, y.1 2] (ψ.symm y.2) +
        (-1 : ℤ) ^ 2 • f.1 ![y.1 0, y.1 1] (ψ.symm y.2)) =
    f.1 ![y.1 1, y.1 2] (ψ.symm y.2) - f.1 ![y.1 0, y.1 2] (ψ.symm y.2) +
      f.1 ![y.1 0, y.1 1] (ψ.symm y.2)
  norm_num
  abel

omit [MulAction Γ6 Z] in
/-- The faces of a three-simplex. -/
theorem face_three (y : (Fin 4 → RationalGL3) × Z) :
    (face RationalGL3 Z (0 : Fin 4) y = (![y.1 1, y.1 2, y.1 3], y.2)) ∧
    (face RationalGL3 Z (1 : Fin 4) y = (![y.1 0, y.1 2, y.1 3], y.2)) ∧
    (face RationalGL3 Z (2 : Fin 4) y = (![y.1 0, y.1 1, y.1 3], y.2)) ∧
    (face RationalGL3 Z (3 : Fin 4) y = (![y.1 0, y.1 1, y.1 2], y.2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · refine Prod.ext ?_ rfl
    funext j
    fin_cases j <;> rfl

theorem modelHomOf_differentialTwo (f : cochains N6 (functionRepresentation ρ X) 2)
    (y : (Fin 4 → RationalGL3) × Z) :
    homFunA ((prodComplex Γ6 RationalGL3 Z).d 3 2 ≫ modelHomOf ρ ψ hψ f) y =
      differentialTwo N6 (functionRepresentation ρ X) f y.1 (ψ.symm y.2) := by
  rw [homFunA_comp_d]
  simp only [homFunA_modelHomOf]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Finset.univ_eq_empty, Finset.sum_empty]
  obtain ⟨h0, h1, h2, h3⟩ := face_three (Z := Z) y
  have e3 : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
  simp only [Fin.succ_zero_eq_one, Fin.val_zero, Fin.val_one, Fin.succ_one_eq_two,
    pow_zero, pow_one, Fin.val_two, add_zero, e3]
  rw [h0, h1, h2, h3]
  change (1 : ℤ) • f.1 ![y.1 1, y.1 2, y.1 3] (ψ.symm y.2) +
      ((-1 : ℤ) • f.1 ![y.1 0, y.1 2, y.1 3] (ψ.symm y.2) +
        ((-1 : ℤ) ^ 2 • f.1 ![y.1 0, y.1 1, y.1 3] (ψ.symm y.2) +
          (-1 : ℤ) ^ 3 • f.1 ![y.1 0, y.1 1, y.1 2] (ψ.symm y.2))) =
    f.1 ![y.1 1, y.1 2, y.1 3] (ψ.symm y.2) - f.1 ![y.1 0, y.1 2, y.1 3] (ψ.symm y.2) +
      f.1 ![y.1 0, y.1 1, y.1 3] (ψ.symm y.2) - f.1 ![y.1 0, y.1 1, y.1 2] (ψ.symm y.2)
  norm_num
  abel

end Model

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
