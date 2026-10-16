module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.CapSystem
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

@[expose] public section


/-!
# Tensor carriers

If `K ⊆ D.X m` are the carriers of a cell basis and `W` is a representation, the subspaces
`W ⊗ K ⊆ W ⊗ D.X m` are carriers for the tensor complex `W ◁ D`; they stay acyclic because `W` is flat over `ℚ`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory TensorProduct
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

/-- The tensor complex `W ◁ D`. -/
abbrev tensorComplex (W : Rep.{0} ℚ Γ) (D : ChainComplex (Rep.{0} ℚ Γ) ℕ) : ChainComplex (Rep.{0} ℚ Γ) ℕ :=
  ((tensorLeft W).mapHomologicalComplex (ComplexShape.down ℕ)).obj D

example (W : Rep.{0} ℚ Γ) (D : ChainComplex (Rep.{0} ℚ Γ) ℕ) (m : ℕ) :
    (tensorComplex W D).X m = (W ⊗ D.X m) := rfl

example (W : Rep.{0} ℚ Γ) (D : ChainComplex (Rep.{0} ℚ Γ) ℕ) (m : ℕ) :
    (tensorComplex W D).d (m+1) m = (W ◁ D.d (m+1) m) := rfl

/-- The tensor carrier `W ⊗ K` of a subspace `K`. -/
def tensorK (W : Rep.{0} ℚ Γ) {X : Rep.{0} ℚ Γ} (K : Submodule ℚ X) : Submodule ℚ (W ⊗ X : Rep.{0} ℚ Γ) :=
  LinearMap.range (LinearMap.lTensor W K.subtype)

theorem tmul_mem_tensorK (W : Rep.{0} ℚ Γ) {X : Rep.{0} ℚ Γ} {K : Submodule ℚ X} (w : W) {x : X}
    (hx : x ∈ K) : (w ⊗ₜ[ℚ] x : (W ⊗ X : Rep.{0} ℚ Γ)) ∈ tensorK W K :=
  ⟨w ⊗ₜ[ℚ] (⟨x, hx⟩ : K), rfl⟩

theorem tensorK_eq_span (W : Rep.{0} ℚ Γ) {X : Rep.{0} ℚ Γ} (K : Submodule ℚ X) :
    tensorK W K = Submodule.span ℚ {t | ∃ (w : W) (x : X), x ∈ K ∧ t = (w ⊗ₜ[ℚ] x : (W ⊗ X : Rep.{0} ℚ Γ))} := by
  apply le_antisymm
  · rintro t ⟨u, rfl⟩
    induction u using TensorProduct.inductionOn with
    | tmul w x => exact Submodule.subset_span ⟨w, x, x.2, rfl⟩
    | add u v hu hv =>
      rw [map_add]
      exact Submodule.add_mem _ hu hv
  · rw [Submodule.span_le]
    rintro t ⟨w, x, hx, rfl⟩
    exact tmul_mem_tensorK W w hx

theorem tensorK_mono (W : Rep.{0} ℚ Γ) {X : Rep.{0} ℚ Γ} {K K' : Submodule ℚ X} (h : K ≤ K') :
    tensorK W K ≤ tensorK W K' := by
  rw [tensorK_eq_span, Submodule.span_le]
  rintro t ⟨w, x, hx, rfl⟩
  exact tmul_mem_tensorK W w (h hx)

theorem tensorK_map (W : Rep.{0} ℚ Γ) {X : Rep.{0} ℚ Γ} (K : Submodule ℚ X) (γ : Γ) :
    tensorK W (K.map (X.ρ γ)) = (tensorK W K).map ((W ⊗ X : Rep.{0} ℚ Γ).ρ γ) := by
  rw [tensorK_eq_span, tensorK_eq_span, Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨w, x, ⟨x', hx', rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨(W.ρ γ⁻¹ w ⊗ₜ[ℚ] x' : (W ⊗ X : Rep.{0} ℚ Γ)),
      ⟨W.ρ γ⁻¹ w, x', hx', rfl⟩, ?_⟩
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul]
    have : W.ρ γ (W.ρ γ⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [this]
  · rw [Submodule.span_le]
    rintro t ⟨t', ⟨w, x, hx, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨W.ρ γ w, X.ρ γ x, ⟨x, hx, rfl⟩, ?_⟩
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul]

theorem whiskerLeft_hom_apply (W : Rep.{0} ℚ Γ) {X Y : Rep.{0} ℚ Γ} (f : X ⟶ Y) (x : (W ⊗ X : Rep.{0} ℚ Γ)) :
    (W ◁ f).hom x = LinearMap.lTensor W f.hom.toLinearMap x := rfl

variable {C : ChainComplex (Rep.{0} ℚ Γ) ℕ} {B : CellBasis C} {D : ChainComplex (Rep.{0} ℚ Γ) ℕ}

/-- Tensoring carriers with a representation. -/
def CarrierData.tensor (𝒦 : CarrierData B D) (W : Rep.{0} ℚ Γ) : CarrierData B (tensorComplex W D) where
  K n s m := tensorK W (𝒦.K n s m)
  K_smul n γ s m := by
    rw [𝒦.K_smul]
    exact tensorK_map W _ γ
  K_face n s := by
    refine Submodule.span_mono ?_ (𝒦.K_face n s)
    rintro x ⟨t, ht, rfl⟩
    exact ⟨t, fun m => tensorK_mono W (ht m), rfl⟩

/-- Subcomplex condition for carriers. -/
def CarrierData.IsSubcomplex (𝒦 : CarrierData B D) : Prop :=
  ∀ n (s : B.S n) m, ∀ x ∈ 𝒦.K n s (m+1), (D.d (m+1) m).hom x ∈ 𝒦.K n s m

theorem CarrierData.Acyclic.tensor {𝒦 : CarrierData B D} (hsub : 𝒦.IsSubcomplex) {A : Rep.{0} ℚ Γ}
    {aug : D.X 0 ⟶ A} (hac : 𝒦.Acyclic aug) (W : Rep.{0} ℚ Γ) :
    (𝒦.tensor W).Acyclic (W ◁ aug : (tensorComplex W D).X 0 ⟶ (W ⊗ A : Rep.{0} ℚ Γ)) := by
  refine ⟨?_, ?_, ?_⟩
  · change W ◁ D.d 1 0 ≫ W ◁ aug = 0
    rw [← MonoidalCategory.whiskerLeft_comp, hac.aug_d, MonoidalPreadditive.whiskerLeft_zero]
  · intro n s y hy hy0
    obtain ⟨y', rfl⟩ := hy
    let d1 : 𝒦.K n s 1 →ₗ[ℚ] 𝒦.K n s 0 :=
      ((D.d 1 0).hom.toLinearMap).restrict (fun x hx => hsub n s 0 x hx)
    let a0 : 𝒦.K n s 0 →ₗ[ℚ] A := aug.hom.toLinearMap ∘ₗ (𝒦.K n s 0).subtype
    have hex : Function.Exact d1 a0 := by
      intro z
      constructor
      · intro hz
        obtain ⟨x, hx, hxd⟩ := hac.acyc0 n s z.1 z.2 hz
        exact ⟨⟨x, hx⟩, Subtype.ext hxd⟩
      · rintro ⟨x, rfl⟩
        have h := hac.aug_d
        change (D.d 1 0 ≫ aug).hom x.1 = 0
        rw [h]
        rfl
    have hflat := Module.Flat.lTensor_exact W hex
    have h0 : LinearMap.lTensor W a0 y' = 0 := by
      have : LinearMap.lTensor W a0 y' = LinearMap.lTensor W aug.hom.toLinearMap
          (LinearMap.lTensor W (𝒦.K n s 0).subtype y') := by
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      rw [this]
      exact hy0
    obtain ⟨x', hx'⟩ := (hflat y').mp h0
    have hcomm2 : (D.d 1 0).hom.toLinearMap ∘ₗ (𝒦.K n s 1).subtype =
        (𝒦.K n s 0).subtype ∘ₗ d1 := by
      ext x; rfl
    refine ⟨LinearMap.lTensor W (𝒦.K n s 1).subtype x', ⟨x', rfl⟩, ?_⟩
    change LinearMap.lTensor W (D.d 1 0).hom.toLinearMap
      (LinearMap.lTensor W (𝒦.K n s 1).subtype x') = LinearMap.lTensor W (𝒦.K n s 0).subtype y'
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomm2, LinearMap.lTensor_comp,
      LinearMap.comp_apply, hx']
  · intro n s m y hy hy0
    obtain ⟨y', rfl⟩ := hy
    let d1 : 𝒦.K n s (m+2) →ₗ[ℚ] 𝒦.K n s (m+1) :=
      ((D.d (m+2) (m+1)).hom.toLinearMap).restrict (fun x hx => hsub n s (m+1) x hx)
    let d0 : 𝒦.K n s (m+1) →ₗ[ℚ] 𝒦.K n s m :=
      ((D.d (m+1) m).hom.toLinearMap).restrict (fun x hx => hsub n s m x hx)
    have hex : Function.Exact d1 d0 := by
      intro z
      constructor
      · intro hz
        have hz' : (D.d (m+1) m).hom z.1 = 0 := congrArg Subtype.val hz
        obtain ⟨x, hx, hxd⟩ := hac.acyc n s m z.1 z.2 hz'
        exact ⟨⟨x, hx⟩, Subtype.ext hxd⟩
      · rintro ⟨x, rfl⟩
        apply Subtype.ext
        have h := D.d_comp_d (m+2) (m+1) m
        change ((D.d (m+2) (m+1) ≫ D.d (m+1) m).hom x.1) = 0
        rw [h]
        rfl
    have hflat := Module.Flat.lTensor_exact W hex
    have hcomm : (D.d (m+1) m).hom.toLinearMap ∘ₗ (𝒦.K n s (m+1)).subtype =
        (𝒦.K n s m).subtype ∘ₗ d0 := by
      ext x; rfl
    have hinj : Function.Injective (LinearMap.lTensor W (𝒦.K n s m).subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
    have h0 : LinearMap.lTensor W d0 y' = 0 := by
      apply hinj
      rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← hcomm, LinearMap.lTensor_comp,
        LinearMap.comp_apply]
      exact hy0
    obtain ⟨x', hx'⟩ := (hflat y').mp h0
    have hcomm2 : (D.d (m+2) (m+1)).hom.toLinearMap ∘ₗ (𝒦.K n s (m+2)).subtype =
        (𝒦.K n s (m+1)).subtype ∘ₗ d1 := by
      ext x; rfl
    refine ⟨LinearMap.lTensor W (𝒦.K n s (m+2)).subtype x', ⟨x', rfl⟩, ?_⟩
    change LinearMap.lTensor W (D.d (m+2) (m+1)).hom.toLinearMap
      (LinearMap.lTensor W (𝒦.K n s (m+2)).subtype x') = LinearMap.lTensor W (𝒦.K n s (m+1)).subtype y'
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomm2, LinearMap.lTensor_comp,
      LinearMap.comp_apply, hx']

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
