module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.HomModel
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cls
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallCochains

@[expose] public section


/-!
# The model `H²` is the cohomology of the Hom complex of the model resolution

For a `GL₃(ℚ)`-set `X` equivariantly in bijection with a `Γ(6)`-set `Z`, `homK ρ Z` is the cochain complex
`Hom_{Γ(6)}(ℚ[V^{•+1} × Z], ρ|_{Γ(6)})` of rational vector spaces.  The class `modelCls` of a model
cocycle is injective on cohomology and onto: `H²(N6, Fun(X, ρ))` of the homogeneous-cochain model is
`H²(homK ρ Z)` (`modelClsEquiv`), the cohomology of `∂M` in the case of the line and plane faces.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.LevelTransfer

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

section

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)
  {X Z : Type} [MulAction RationalGL3 X] [MulAction Γ6 Z] (ψ : X ≃ Z)
  (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x)

/-- The Hom complex of the model resolution `ℚ[V^{•+1} × Z]` into `ρ|_{Γ(6)}`. -/
abbrev homK : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  TernaryPoly.EquivariantSingularSmall.homCochains (prodComplex Γ6 RationalGL3 Z) (coeffRep ρ)

theorem homK_d_hom (i j : ℕ) (φ : (prodComplex Γ6 RationalGL3 Z).X i ⟶ coeffRep ρ) :
    ((homK ρ (Z := Z)).d i j).hom φ = (prodComplex Γ6 RationalGL3 Z).d j i ≫ φ := rfl

/-- The model differential of a cocycle composes to zero on the Hom side. -/
theorem modelHomOf_cocycle (c : cocycles N6 (functionRepresentation ρ X)) :
    (((homK ρ (Z := Z)).d 2 3).hom (modelHomOf ρ ψ hψ c.val)) = 0 := by
  rw [homK_d_hom]
  apply homFunA_injective
  funext y
  rw [modelHomOf_differentialTwo]
  have h : differentialTwo N6 (functionRepresentation ρ X) c.val = 0 := c.property
  rw [h]
  rfl

/-- The class in `H²(homK)` of a model cocycle. -/
def modelCls (c : cocycles N6 (functionRepresentation ρ X)) : (homK ρ (Z := Z)).homology 2 :=
  cls2 _ (modelHomOf ρ ψ hψ c.val) (modelHomOf_cocycle ρ ψ hψ c)

theorem modelCls_add (c c' : cocycles N6 (functionRepresentation ρ X)) :
    modelCls ρ ψ hψ (c + c') = modelCls ρ ψ hψ c + modelCls ρ ψ hψ c' := by
  unfold modelCls
  have hsum : ((homK ρ (Z := Z)).d 2 3).hom (modelHomOf ρ ψ hψ c.val + modelHomOf ρ ψ hψ c'.val) = 0 := by
    have := modelHomOf_cocycle ρ ψ hψ (c + c')
    rw [show (c + c').val = c.val + c'.val from rfl, modelHomOf_add] at this
    exact this
  rw [← cls2_add _ _ _ (modelHomOf_cocycle ρ ψ hψ c) (modelHomOf_cocycle ρ ψ hψ c') hsum]
  exact cls2_congr _ _ _ (modelHomOf_add ρ ψ hψ c.val c'.val)

theorem modelCls_smul (r : ℚ) (c : cocycles N6 (functionRepresentation ρ X)) :
    modelCls ρ ψ hψ (r • c) = r • modelCls ρ ψ hψ c := by
  unfold modelCls
  have hsm : ((homK ρ (Z := Z)).d 2 3).hom (r • modelHomOf ρ ψ hψ c.val) = 0 := by
    have := modelHomOf_cocycle ρ ψ hψ (r • c)
    rw [show (r • c).val = r • c.val from rfl, modelHomOf_smul] at this
    exact this
  rw [← cls2_smul _ r _ (modelHomOf_cocycle ρ ψ hψ c) hsm]
  exact cls2_congr _ _ _ (modelHomOf_smul ρ ψ hψ r c.val)

theorem modelHomOf_injective {k : ℕ} {f g : cochains N6 (functionRepresentation ρ X) k}
    (h : modelHomOf ρ ψ hψ f = modelHomOf ρ ψ hψ g) : f = g := by
  have := congrArg (cochainOfHom ρ ψ hψ) h
  rwa [cochainOfHom_modelHomOf, cochainOfHom_modelHomOf] at this

theorem modelHomOf_differentialOne' (f : cochains N6 (functionRepresentation ρ X) 1) :
    modelHomOf ρ ψ hψ (differentialOne N6 (functionRepresentation ρ X) f) =
      (prodComplex Γ6 RationalGL3 Z).d 2 1 ≫ modelHomOf ρ ψ hψ f := by
  apply homFunA_injective
  funext y
  rw [homFunA_modelHomOf, modelHomOf_differentialOne]

/-- A model cocycle has zero class iff it is a coboundary. -/
theorem modelCls_eq_zero_iff (c : cocycles N6 (functionRepresentation ρ X)) :
    modelCls ρ ψ hψ c = 0 ↔ c ∈ LinearMap.range (boundaryMap N6 (functionRepresentation ρ X)) := by
  refine (cls2_eq_zero_iff _ _ _).trans ?_
  constructor
  · rintro ⟨b, hb⟩
    let b' : (prodComplex Γ6 RationalGL3 Z).X 1 ⟶ coeffRep ρ := b
    have hb' : (prodComplex Γ6 RationalGL3 Z).d 2 1 ≫ b' = modelHomOf ρ ψ hψ c.val := hb
    refine ⟨cochainOfHom ρ ψ hψ b', ?_⟩
    apply Subtype.ext
    apply modelHomOf_injective ρ ψ hψ
    change modelHomOf ρ ψ hψ (differentialOne N6 (functionRepresentation ρ X)
      (cochainOfHom ρ ψ hψ b')) = _
    rw [modelHomOf_differentialOne', modelHomOf_cochainOfHom, hb']
  · rintro ⟨f, hf⟩
    refine ⟨modelHomOf ρ ψ hψ f, ?_⟩
    change (prodComplex Γ6 RationalGL3 Z).d 2 1 ≫ modelHomOf ρ ψ hψ f = modelHomOf ρ ψ hψ c.val
    rw [← modelHomOf_differentialOne']
    have := congrArg (fun t : cocycles N6 (functionRepresentation ρ X) => t.val) hf
    change differentialOne N6 (functionRepresentation ρ X) f = c.val at this
    rw [this]

/-- Every class of `H²(homK)` is the class of a model cocycle. -/
theorem modelCls_surjective (x : (homK ρ (Z := Z)).homology 2) :
    ∃ c : cocycles N6 (functionRepresentation ρ X), modelCls ρ ψ hψ c = x := by
  obtain ⟨a, ha, rfl⟩ := exists_cls2 _ x
  let a' : (prodComplex Γ6 RationalGL3 Z).X 2 ⟶ coeffRep ρ := a
  have ha' : (prodComplex Γ6 RationalGL3 Z).d 3 2 ≫ a' = 0 := ha
  have ha2 : (prodComplex Γ6 RationalGL3 Z).d 3 2 ≫ modelHomOf ρ ψ hψ (cochainOfHom ρ ψ hψ a') = 0 := by
    rw [modelHomOf_cochainOfHom]
    exact ha'
  have hc : differentialTwo N6 (functionRepresentation ρ X) (cochainOfHom ρ ψ hψ a') = 0 := by
    funext z
    funext e
    have h1 := congrArg (fun m => homFunA m (z, ψ e)) ha2
    simp only [modelHomOf_differentialTwo] at h1
    rw [Equiv.symm_apply_apply] at h1
    exact h1
  refine ⟨⟨cochainOfHom ρ ψ hψ a', hc⟩, ?_⟩
  unfold modelCls
  exact cls2_congr _ _ _ (modelHomOf_cochainOfHom ρ ψ hψ a')

theorem modelCls_eq_of_sub_mem (c c' : cocycles N6 (functionRepresentation ρ X))
    (h : c - c' ∈ LinearMap.range (boundaryMap N6 (functionRepresentation ρ X))) :
    modelCls ρ ψ hψ c = modelCls ρ ψ hψ c' := by
  have h0 := (modelCls_eq_zero_iff ρ ψ hψ (c - c')).2 h
  have h1 : c = (c - c') + c' := by abel
  calc modelCls ρ ψ hψ c = modelCls ρ ψ hψ ((c - c') + c') := congrArg _ h1
    _ = modelCls ρ ψ hψ (c - c') + modelCls ρ ψ hψ c' := modelCls_add ρ ψ hψ _ _
    _ = modelCls ρ ψ hψ c' := by rw [h0, zero_add]

/-- The class in `H²(homK)` of a class of the cochain model of `N6`. -/
def modelClsH2 : H2 N6 (functionRepresentation ρ X) → (homK ρ (Z := Z)).homology 2 :=
  Quotient.lift (modelCls ρ ψ hψ) (fun c c' h =>
    modelCls_eq_of_sub_mem ρ ψ hψ c c' ((Submodule.quotientRel_def _).1 h))

theorem modelClsH2_classOf (c : cocycles N6 (functionRepresentation ρ X)) :
    modelClsH2 ρ ψ hψ (classOf N6 (functionRepresentation ρ X) c) = modelCls ρ ψ hψ c := rfl

theorem modelClsH2_injective : Function.Injective (modelClsH2 ρ ψ hψ (Z := Z)) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨c', rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have h : modelCls ρ ψ hψ c = modelCls ρ ψ hψ c' := hab
  have h0 : modelCls ρ ψ hψ (c - c') = 0 := by
    have : c - c' + c' = c := by abel
    have h2 := modelCls_add ρ ψ hψ (c - c') c'
    rw [this, h] at h2
    simpa using h2.symm
  exact (Submodule.Quotient.eq _).2 ((modelCls_eq_zero_iff ρ ψ hψ (c - c')).1 h0)

theorem modelClsH2_surjective : Function.Surjective (modelClsH2 ρ ψ hψ (Z := Z)) := by
  intro x
  obtain ⟨c, rfl⟩ := modelCls_surjective ρ ψ hψ x
  exact ⟨classOf N6 (functionRepresentation ρ X) c, rfl⟩

end

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
