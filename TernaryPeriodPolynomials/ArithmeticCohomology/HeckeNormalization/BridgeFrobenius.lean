module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.FareyNeighbours

@[expose] public section


/-!
# Frobenius duality for the dual Farey tree (L1, Farey side)

Formalized by Claude Sonnet 5.5.  Supports the Hecke bridge B1 (Appendix B, Lemma B.1,
`HomologyHomBridge`).

For a `ℚ`-representation `M` of `Γ = GL₂(ℤ)` and a `Γ`-set `X` all of whose stabilizers are finite,
* `frobFun`, `frobEquiv`: the Frobenius map `(M ⊗ ℚ[X])_Γ → (X → M)`, `[m ⊗ y] ↦ (x ↦ ∑_{γ y = x} γ m)`, a linear isomorphism
  onto the equivariant functions `EqFun X M = Hom_Γ(ℚ[X], M)` when `Γ` acts transitively (`evalAt` of `PermEval` at every point,
  moved by `evalAt_base_smul'`);
* `frobE`, `frobT`: the instances `X = OTE` (oriented edges) and `X = Tri` (triangles) of the dual Farey tree;
* `frobE_sigC`, `frobT_dW`: under `frobE`/`frobT` the swap `sigC` is `F ↦ F ∘ swap` and the boundary `dW` is
  `(∂†F)(t) = ∑_{q ending at t} F q - ∑_{q leaving t} F q`;
* `H1Fun M` and `h1Fun : H₁(Γ, M) ≃ₗ H1Fun M` (Mathlib's `groupHomology`): equivariant antisymmetric functions `F` on oriented
  edges with `∑_{q leaving t} F q = 0` at every triangle; `h1Fun_p0` says `(h1Fun x) p₀ = edge2 M x`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open CategoryTheory Representation Rep TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.BinaryDuality
open TernaryPeriodPolynomials.Argument.HeckeDuality
open scoped Classical MonoidAlgebra

section Generic

variable {Γ : Type} [Group Γ] {X : Type} [MulAction Γ X]

theorem transp_base_smul' (g : Γ) (x₀ y : X) :
    transp (Γ := Γ) (g • x₀) y = (fun δ => g * δ) '' transp x₀ y := by
  ext γ
  simp only [transp, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h
    refine ⟨g⁻¹ * γ, ?_, mul_inv_cancel_left g γ⟩
    rw [mul_smul, h, inv_smul_smul]
  · rintro ⟨δ, hδ, rfl⟩
    rw [mul_smul, hδ]

/-- Moving the base point by `g` multiplies the norm sum by `g`. -/
theorem normAt_base_smul' (g : Γ) {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀))
    (hx' : Finite (MulAction.stabilizer Γ (g • x₀))) (M : Rep ℚ Γ) (y : X) (m : M) :
    normAt hx' M y m = M.ρ g (normAt hx₀ M y m) := by
  unfold normAt
  have hset : (transp_finite hx' y).toFinset = (transp_finite hx₀ y).toFinset.image (fun δ => g * δ) := by
    ext γ
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, transp_base_smul', Set.mem_image]
  rw [hset, LinearMap.sum_apply, LinearMap.sum_apply, map_sum,
    Finset.sum_image (fun a _ b _ h => mul_left_cancel h)]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [map_mul]; rfl

theorem evalAt_base_smul' (g : Γ) {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀))
    (hx' : Finite (MulAction.stabilizer Γ (g • x₀))) (M : Rep ℚ Γ)
    (w : Coinvariants ((M.ρ).tprod (Rep.ofMulAction ℚ Γ X).ρ)) :
    evalAt hx' M w = M.ρ g (evalAt hx₀ M w) := by
  obtain ⟨t, rfl⟩ := Coinvariants.mk_surjective _ w
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul m c =>
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, map_add, ha, hb, map_add, map_add]
    | single y r =>
      rw [evalAt_mk, evalAt_mk, evalTen_tmul_single, evalTen_tmul_single, normAt_base_smul' g hx₀ hx',
        map_smul]

variable (M : Rep ℚ Γ) (X)

/-- The `Γ`-equivariant functions `X → M` (that is, `Hom_Γ(ℚ[X], M)`). -/
def EqFun : Submodule ℚ (X → M) where
  carrier := {F | ∀ (γ : Γ) (x : X), F (γ • x) = M.ρ γ (F x)}
  add_mem' := fun {a b} ha hb γ x => by simp [ha γ x, hb γ x]
  zero_mem' := fun γ x => by simp
  smul_mem' := fun c {a} ha γ x => by simp [ha γ x]

variable {X}

theorem mem_EqFun {F : X → M} : F ∈ EqFun (Γ := Γ) X M ↔ ∀ (γ : Γ) (x : X), F (γ • x) = M.ρ γ (F x) := Iff.rfl

variable (hX : ∀ x : X, Finite (MulAction.stabilizer Γ x))

/-- **The Frobenius map** `(M ⊗ ℚ[X])_Γ → (X → M)`, `[m ⊗ y] ↦ (x ↦ ∑_{γ y = x} γ m)`. -/
def frobFun : Coinvariants ((M.ρ).tprod (Rep.ofMulAction ℚ Γ X).ρ) →ₗ[ℚ] (X → M) :=
  LinearMap.pi fun x => evalAt (hX x) M

theorem frobFun_apply (w : Coinvariants ((M.ρ).tprod (Rep.ofMulAction ℚ Γ X).ρ)) (x : X) :
    frobFun M hX w x = evalAt (hX x) M w := rfl

theorem frobFun_mem (w : Coinvariants ((M.ρ).tprod (Rep.ofMulAction ℚ Γ X).ρ)) :
    frobFun M hX w ∈ EqFun (Γ := Γ) X M := fun γ x =>
  evalAt_base_smul' γ (hX x) (hX (γ • x)) M w

theorem frobFun_mk (m : M) (y x : X) (r : ℚ) :
    frobFun M hX (Coinvariants.mk _ (m ⊗ₜ MonoidAlgebra.single y r)) x = r • normAt (hX x) M y m := by
  rw [frobFun_apply, evalAt_mk, evalTen_tmul_single]

variable {x₀ : X} (htr : ∀ y : X, ∃ γ : Γ, γ • x₀ = y)

include htr in
theorem frobFun_injective : Function.Injective (frobFun M hX) := by
  intro a b h
  apply evalAt_injective (hX x₀) M htr
  exact congrFun h x₀

include htr in
theorem frobFun_range : LinearMap.range (frobFun M hX) = EqFun (Γ := Γ) X M := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact frobFun_mem M hX w
  · intro F hF
    have hinv : ∀ s : MulAction.stabilizer Γ x₀, M.ρ s (F x₀) = F x₀ := by
      intro s
      rw [← hF s x₀, MulAction.mem_stabilizer_iff.mp s.2]
    obtain ⟨w, hw⟩ := (mem_range_evalAt (hX x₀) M htr (F x₀)).mpr hinv
    refine ⟨w, funext fun x => ?_⟩
    obtain ⟨γ, rfl⟩ := htr x
    rw [frobFun_apply, evalAt_base_smul' γ (hX x₀) (hX (γ • x₀)) M w, hw, hF γ x₀]

/-- **L1 (Frobenius duality).**  For a transitive `Γ`-set with finite stabilizers, `(M ⊗ ℚ[X])_Γ ≃ Hom_Γ(ℚ[X], M)`. -/
def frobEquiv : Coinvariants ((M.ρ).tprod (Rep.ofMulAction ℚ Γ X).ρ) ≃ₗ[ℚ] EqFun (Γ := Γ) X M :=
  LinearEquiv.ofBijective
    ((frobFun M hX).codRestrict (EqFun (Γ := Γ) X M) (frobFun_mem M hX))
    ⟨fun a b h => frobFun_injective M hX htr (congrArg Subtype.val h),
     fun F => by
      have : (F : X → M) ∈ LinearMap.range (frobFun M hX) := by rw [frobFun_range M hX htr]; exact F.2
      obtain ⟨w, hw⟩ := this
      exact ⟨w, Subtype.ext hw⟩⟩

theorem frobEquiv_apply (w : Coinvariants ((M.ρ).tprod (Rep.ofMulAction ℚ Γ X).ρ)) :
    ((frobEquiv M hX htr w : EqFun (Γ := Γ) X M) : X → M) = frobFun M hX w := rfl

end Generic


/-- Two linear maps out of `(M ⊗ ℚ[X])_Γ` agreeing on the generators `[m ⊗ y]` are equal. -/
theorem ct_ext {Γ : Type} [Group Γ] {X : Type} [MulAction Γ X] {M : Rep ℚ Γ} {N : Type} [AddCommGroup N] [Module ℚ N]
    (L1 L2 : Coinvariants ((M.ρ).tprod (Rep.ofMulAction ℚ Γ X).ρ) →ₗ[ℚ] N)
    (h : ∀ (m : M) (y : X) (r : ℚ), L1 (Coinvariants.mk _ (m ⊗ₜ MonoidAlgebra.single y r)) =
      L2 (Coinvariants.mk _ (m ⊗ₜ MonoidAlgebra.single y r))) : L1 = L2 := by
  refine Coinvariants.hom_ext (TensorProduct.ext' fun m c => ?_)
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [LinearMap.comp_apply, TensorProduct.tmul_add, map_add] at ha hb ⊢; rw [ha, hb]
  | single y r => exact h m y r

section Fiber

variable {Γ : Type} [Group Γ] {X Y : Type} [MulAction Γ X] [MulAction Γ Y]

/-- Sum of the norm sums over a fibre of an equivariant map. -/
theorem sum_fiber_normAt (φ : X → Y) (hφ : ∀ (γ : Γ) (x : X), φ (γ • x) = γ • φ x)
    (hX : ∀ x : X, Finite (MulAction.stabilizer Γ x)) (hY : ∀ y : Y, Finite (MulAction.stabilizer Γ y))
    (M : Rep ℚ Γ) (y : Y) (A : Finset X) (hA : ∀ e, e ∈ A ↔ φ e = y) (x : X) (m : M) :
    ∑ e ∈ A, normAt (hX e) M x m = normAt (hY y) M (φ x) m := by
  unfold normAt
  simp only [LinearMap.sum_apply]
  have hmaps : ∀ γ ∈ (transp_finite (hY y) (φ x)).toFinset, γ • x ∈ A := by
    intro γ hγ
    rw [Set.Finite.mem_toFinset] at hγ
    rw [hA, hφ]
    exact hγ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun e he => ?_
  refine Finset.sum_congr ?_ fun γ _ => rfl
  ext γ
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, transp, Set.mem_ofPred_eq]
  constructor
  · rintro h
    refine ⟨?_, h⟩
    have h2 := (hA e).mp he
    rw [← h, hφ] at h2
    exact h2
  · rintro ⟨_, h⟩
    exact h

end Fiber

section Farey

variable (M : Rep ℚ IntegralGL)

theorem hOTE : ∀ e : OTE, Finite (MulAction.stabilizer IntegralGL e) := fun e => ote_stabilizer_finite e

theorem hTri : ∀ t : Tri, Finite (MulAction.stabilizer IntegralGL t) := fun t => tri_stabilizer_finite t

/-- Frobenius for oriented edges: `(M ⊗ PE)_Γ ≃ Hom_Γ(ℚ[OTE], M)`. -/
def frobE : CT M PE ≃ₗ[ℚ] EqFun (Γ := IntegralGL) OTE M := frobEquiv M hOTE ote_htr

/-- Frobenius for triangles. -/
def frobT : CT M P0 ≃ₗ[ℚ] EqFun (Γ := IntegralGL) Tri M := frobEquiv M hTri tri_htr

theorem frobE_apply (w : CT M PE) (e : OTE) : (frobE M w : OTE → M) e = evalAt (ote_stabilizer_finite e) M w := rfl

theorem frobT_apply (w : CT M P0) (t : Tri) : (frobT M w : Tri → M) t = evalAt (tri_stabilizer_finite t) M w := rfl

theorem frobE_p0 (w : CT M PE) : (frobE M w : OTE → M) p0 = evalP M w := rfl

theorem normAt_swap (e y : OTE) (m : M) :
    normAt (ote_stabilizer_finite e) M y.swap m = normAt (ote_stabilizer_finite e.swap) M y m := by
  unfold normAt
  have hset : (transp_finite (ote_stabilizer_finite e) y.swap).toFinset =
      (transp_finite (ote_stabilizer_finite e.swap) y).toFinset := by
    ext γ
    simp only [Set.Finite.mem_toFinset, transp, Set.mem_ofPred_eq]
    constructor
    · intro h
      have := congrArg OTE.swap h
      rwa [← OTE.swap_smul, OTE.swap_swap] at this
    · intro h
      have := congrArg OTE.swap h
      rw [OTE.swap_smul, OTE.swap_swap] at this
      exact this
  rw [hset]

/-- The swap involution on the Frobenius side. -/
theorem frobE_sigC (w : CT M PE) (e : OTE) :
    (frobE M ((sigC M).hom w) : OTE → M) e = (frobE M w : OTE → M) e.swap := by
  rw [frobE_apply, frobE_apply]
  obtain ⟨t, rfl⟩ := Coinvariants.mk_surjective _ w
  induction t using TensorProduct.inductionOn with
  | add a b ha hb =>
    have h1 : (sigC M).hom (Coinvariants.mk _ (a + b)) = (sigC M).hom (Coinvariants.mk _ a) + (sigC M).hom (Coinvariants.mk _ b) := by
      rw [map_add, map_add]
    rw [h1, map_add, map_add, map_add, ha, hb]
  | tmul m c =>
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      have h1 : (sigC M).hom (Coinvariants.mk _ (m ⊗ₜ (a + b))) = (sigC M).hom (Coinvariants.mk _ (m ⊗ₜ a)) +
          (sigC M).hom (Coinvariants.mk _ (m ⊗ₜ b)) := by
        rw [TensorProduct.tmul_add, map_add, map_add]
      rw [h1, map_add, TensorProduct.tmul_add, map_add, map_add, ha, hb]
    | single y r =>
      have h1 : (sigC M).hom (Coinvariants.mk _ (m ⊗ₜ MonoidAlgebra.single y r)) =
          Coinvariants.mk _ (m ⊗ₜ MonoidAlgebra.single y.swap r) := by
        change Coinvariants.mk _ (m ⊗ₜ swapMap.hom (MonoidAlgebra.single y r)) = _
        rw [swapMap_single]
      rw [h1]
      have a1 := (evalAt_mk (ote_stabilizer_finite e) M m (MonoidAlgebra.single y.swap r)).trans
        (evalTen_tmul_single (ote_stabilizer_finite e) M m y.swap r)
      have a2 := (evalAt_mk (ote_stabilizer_finite e.swap) M m (MonoidAlgebra.single y r)).trans
        (evalTen_tmul_single (ote_stabilizer_finite e.swap) M m y r)
      refine a1.trans (Eq.trans ?_ a2.symm)
      rw [normAt_swap]

/-- Oriented edges ending at a triangle. -/
def inE (t : Tri) : Finset OTE := (nbF t).image OTE.swap

theorem mem_inE {t : Tri} {q : OTE} : q ∈ inE t ↔ q.1.2 = t := by
  unfold inE
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_nbF] at ha
    exact ha
  · intro h
    exact ⟨q.swap, mem_nbF.mpr h, OTE.swap_swap q⟩

theorem dW_mk (m : M) (e : OTE) (r : ℚ) :
    (dW M).hom (Coinvariants.mk (M.ρ.tprod (Rep.ofMulAction ℚ IntegralGL OTE).ρ) (m ⊗ₜ MonoidAlgebra.single e r)) =
      Coinvariants.mk (M.ρ.tprod (Rep.ofMulAction ℚ IntegralGL Tri).ρ)
        (m ⊗ₜ (MonoidAlgebra.single e.1.2 r - MonoidAlgebra.single e.1.1 r)) := by
  change Coinvariants.mk _ (m ⊗ₜ dTilde.hom (MonoidAlgebra.single e r)) = _
  rw [dTilde_single]
  rfl

/-- **`dC` on the Frobenius side**: `(∂†F)(t) = ∑_{q ending at t} F(q) - ∑_{q leaving t} F(q)`. -/
theorem frobT_dW (w : CT M PE) (t : Tri) :
    (frobT M ((dW M).hom w) : Tri → M) t =
      ∑ q ∈ inE t, (frobE M w : OTE → M) q - ∑ q ∈ nbF t, (frobE M w : OTE → M) q := by
  rw [frobT_apply]
  simp only [frobE_apply]
  have key : (evalAt (tri_stabilizer_finite t) M).comp (dW M).hom =
      (∑ q ∈ inE t, evalAt (ote_stabilizer_finite q) M) - ∑ q ∈ nbF t, evalAt (ote_stabilizer_finite q) M := by
    apply ct_ext
    intro m e r
    have hs := sum_fiber_normAt (Γ := IntegralGL) (fun q : OTE => q.1.2) (fun _ _ => rfl) ote_stabilizer_finite
      tri_stabilizer_finite M t (inE t) (fun q => mem_inE) e m
    have hf := sum_fiber_normAt (Γ := IntegralGL) (fun q : OTE => q.1.1) (fun _ _ => rfl) ote_stabilizer_finite
      tri_stabilizer_finite M t (nbF t) (fun q => mem_nbF) e m
    have ev : ∀ (x : OTE) (hx : Finite (MulAction.stabilizer IntegralGL x)) (c : MonoidAlgebra ℚ OTE),
        evalAt hx M (Coinvariants.mk _ (m ⊗ₜ c)) = evalTen hx M (m ⊗ₜ c) := fun x hx c => evalAt_mk hx M m c
    have evT : ∀ (x : Tri) (hx : Finite (MulAction.stabilizer IntegralGL x)) (c : MonoidAlgebra ℚ Tri),
        evalAt hx M (Coinvariants.mk _ (m ⊗ₜ c)) = evalTen hx M (m ⊗ₜ c) := fun x hx c => evalAt_mk hx M m c
    have step1 : evalAt (tri_stabilizer_finite t) M ((dW M).hom
        (Coinvariants.mk (M.ρ.tprod (Rep.ofMulAction ℚ IntegralGL OTE).ρ) (m ⊗ₜ MonoidAlgebra.single e r))) =
        evalTen (tri_stabilizer_finite t) M
          (m ⊗ₜ (MonoidAlgebra.single e.1.2 r - MonoidAlgebra.single e.1.1 r)) := by
      rw [dW_mk]
      exact evT _ _ _
    rw [LinearMap.comp_apply]
    refine step1.trans ?_
    rw [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.sum_apply]
    simp only [ev]
    rw [TensorProduct.tmul_sub, map_sub, evalTen_tmul_single, evalTen_tmul_single]
    simp only [evalTen_tmul_single, ← Finset.smul_sum]
    rw [hs, hf]
  have := LinearMap.congr_fun key w
  simpa [LinearMap.sub_apply, LinearMap.sum_apply] using this

/-- Antisymmetry gives `∑_{q ending at t} F q = -∑_{q leaving t} F q`. -/
theorem sum_inE_of_anti (F : OTE → M) (hF : ∀ e : OTE, F e.swap = -F e) (t : Tri) :
    ∑ q ∈ inE t, F q = -∑ q ∈ nbF t, F q := by
  unfold inE
  rw [Finset.sum_image (fun a _ b _ h => by simpa using congrArg OTE.swap h)]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => hF a

/-- **The period functions** `H₁`-side target: `Γ`-equivariant, antisymmetric functions `F` on oriented edges with
`∑_{q leaving t} F q = 0` at every triangle `t`. -/
def H1Fun : Submodule ℚ (EqFun (Γ := IntegralGL) OTE M) where
  carrier := {F | (∀ e : OTE, (F : OTE → M) e.swap = -(F : OTE → M) e) ∧
    ∀ t : Tri, ∑ q ∈ nbF t, (F : OTE → M) q = 0}
  add_mem' := fun {a b} ha hb => by
    refine ⟨fun e => ?_, fun t => ?_⟩
    · have h1 := ha.1 e
      have h2 := hb.1 e
      simp only [Submodule.coe_add, Pi.add_apply]
      rw [h1, h2]
      abel
    · simp [Finset.sum_add_distrib, ha.2 t, hb.2 t]
  zero_mem' := ⟨fun e => by simp, fun t => by simp⟩
  smul_mem' := fun c {a} ha => by
    refine ⟨fun e => ?_, fun t => ?_⟩
    · have h1 := ha.1 e
      simp only [Submodule.coe_smul, Pi.smul_apply]
      rw [h1, smul_neg]
    · simp [← Finset.smul_sum, ha.2 t]

theorem mem_H1Fun {F : EqFun (Γ := IntegralGL) OTE M} :
    F ∈ H1Fun M ↔ (∀ e : OTE, (F : OTE → M) e.swap = -(F : OTE → M) e) ∧
      ∀ t : Tri, ∑ q ∈ nbF t, (F : OTE → M) q = 0 := Iff.rfl

/-- A chain `w ∈ (M ⊗ PE)_Γ` is antisymmetric and a cycle iff its Frobenius function lies in `H1Fun`. -/
theorem frobE_mem_H1Fun_iff (w : CT M PE) :
    frobE M w ∈ H1Fun M ↔ (sigC M).hom w = -w ∧ (dW M).hom w = 0 := by
  constructor
  · rintro ⟨hanti, hvert⟩
    have h1 : (sigC M).hom w = -w := by
      apply (frobE M).injective
      apply Subtype.ext
      funext e
      rw [map_neg]
      change (frobE M ((sigC M).hom w) : OTE → M) e = -(frobE M w : OTE → M) e
      rw [frobE_sigC]
      exact hanti e
    refine ⟨h1, ?_⟩
    apply (frobT M).injective
    apply Subtype.ext
    funext t
    rw [map_zero]
    change (frobT M ((dW M).hom w) : Tri → M) t = 0
    rw [frobT_dW, sum_inE_of_anti M _ hanti, hvert t]
    simp
  · rintro ⟨h1, h2⟩
    have hanti : ∀ e : OTE, (frobE M w : OTE → M) e.swap = -(frobE M w : OTE → M) e := by
      intro e
      rw [← frobE_sigC, h1, map_neg]
      rfl
    refine ⟨hanti, fun t => ?_⟩
    have h3 := frobT_dW M w t
    rw [h2, map_zero] at h3
    rw [sum_inE_of_anti M _ hanti] at h3
    change (0 : M) = _ at h3
    have h4 : (2 : ℚ) • ∑ q ∈ nbF t, (frobE M w : OTE → M) q = 0 := by
      rw [two_smul]
      calc (∑ q ∈ nbF t, (frobE M w : OTE → M) q) + ∑ q ∈ nbF t, (frobE M w : OTE → M) q
          = -(-(∑ q ∈ nbF t, (frobE M w : OTE → M) q) - ∑ q ∈ nbF t, (frobE M w : OTE → M) q) := by abel
        _ = 0 := by rw [← h3]; simp
    exact (smul_eq_zero.mp h4).resolve_left (by norm_num)

/-- The cycle map `H₁(Γ, M) → Hom_Γ(ℚ[OTE], M)`: the Frobenius function of the Farey cycle. -/
def h1Raw : groupHomology M 1 →ₗ[ℚ] EqFun (Γ := IntegralGL) OTE M :=
  (frobE M).toLinearMap ∘ₗ (inclC M).hom ∘ₗ (LinearMap.ker (dC M).hom).subtype ∘ₗ (H1Iso M).hom.hom

theorem h1Raw_p0 (x : groupHomology M 1) : (h1Raw M x : OTE → M) p0 = edge2 M x := rfl

theorem h1Raw_mem (x : groupHomology M 1) : h1Raw M x ∈ H1Fun M := by
  set z := (H1Iso M).hom.hom x with hz
  have hcyc : (dW M).hom ((inclC M).hom (z : CT M P1)) = 0 := by
    have := z.2
    rw [LinearMap.mem_ker] at this
    have e := congrArg (fun f : CT M P1 ⟶ CT M P0 => f.hom (z : CT M P1)) (dC_eq M)
    exact e.symm.trans this
  have hanti : (sigC M).hom ((inclC M).hom (z : CT M P1)) = -(inclC M).hom (z : CT M P1) := by
    have := congrArg (fun f => f.hom (z : CT M P1)) (inclC_sigC M)
    simpa using this
  exact (frobE_mem_H1Fun_iff M _).mpr ⟨hanti, hcyc⟩

theorem h1Raw_injective : Function.Injective (h1Raw M) := by
  intro x y h
  have h1 := (frobE M).injective h
  have h2 := inclC_injective M h1
  have h3 := Subtype.ext h2
  exact (ModuleCat.mono_iff_injective (H1Iso M).hom).mp inferInstance h3

theorem h1Raw_surjective {F : EqFun (Γ := IntegralGL) OTE M} (hF : F ∈ H1Fun M) :
    ∃ x, h1Raw M x = F := by
  obtain ⟨hsig, hdW⟩ := (frobE_mem_H1Fun_iff M ((frobE M).symm F)).mp (by simpa using hF)
  set w := (frobE M).symm F with hw
  set z0 : CT M P1 := (retrC M).hom w with hz0
  have hinc : (inclC M).hom z0 = w := by
    have := congrArg (fun f => f.hom w) (retrC_inclC M)
    simp only [ModuleCat.hom_comp] at this
    change (inclC M).hom ((retrC M).hom w) = _ at this
    rw [this]
    have h2 : ((1 / 2 : ℚ) • (𝟙 (CT M PE) - sigC M)).hom w = (1 / 2 : ℚ) • (w - (sigC M).hom w) := rfl
    rw [h2, hsig]
    module
  have hker : z0 ∈ LinearMap.ker (dC M).hom := by
    rw [LinearMap.mem_ker]
    have e := congrArg (fun f : CT M P1 ⟶ CT M P0 => f.hom z0) (dC_eq M)
    exact e.trans (by simp only [ModuleCat.hom_comp, LinearMap.comp_apply]; change (dW M).hom ((inclC M).hom z0) = 0; rw [hinc]; exact hdW)
  refine ⟨(H1Iso M).inv.hom ⟨z0, hker⟩, ?_⟩
  have hinv : (H1Iso M).hom.hom ((H1Iso M).inv.hom ⟨z0, hker⟩) = ⟨z0, hker⟩ :=
    Iso.inv_hom_id_apply (H1Iso M) _
  change (frobE M) ((inclC M).hom ((H1Iso M).hom.hom ((H1Iso M).inv.hom ⟨z0, hker⟩))) = F
  rw [hinv]
  change (frobE M) ((inclC M).hom z0) = F
  rw [hinc, hw]
  simp

/-- **L1 for `H₁(GL₂(ℤ), M)`.**  `H₁(Γ, M)` (Mathlib group homology) is linearly isomorphic to the space `H1Fun M`
of equivariant antisymmetric functions on oriented dual-tree edges with zero outgoing sum at every triangle,
by the Frobenius map `(M ⊗ P)_Γ ≃ Hom_Γ(P, M)` on the Farey cycles. -/
def h1Fun : groupHomology M 1 ≃ₗ[ℚ] H1Fun M :=
  LinearEquiv.ofBijective ((h1Raw M).codRestrict (H1Fun M) (h1Raw_mem M))
    ⟨fun a b h => by
      have h' := congrArg Subtype.val h
      rw [LinearMap.codRestrict_apply, LinearMap.codRestrict_apply] at h'
      exact h1Raw_injective M h',
     fun F => by
      obtain ⟨x, hx⟩ := h1Raw_surjective M F.2
      exact ⟨x, Subtype.ext hx⟩⟩

/-- Evaluation of the period function at the standard oriented edge is the standard-edge coefficient. -/
theorem h1Fun_p0 (x : groupHomology M 1) : ((h1Fun M x : H1Fun M) : EqFun (Γ := IntegralGL) OTE M).1 p0 = edge2 M x := rfl

end Farey

end TernaryPeriodPolynomials.Argument.HeckeNormalization
