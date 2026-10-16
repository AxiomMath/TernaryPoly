module

public import TernaryPeriodPolynomials.Topology.TopHomology.FreeNerve
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Diagonal

@[expose] public section



/-!
# The Alexander-Whitney diagonal of the resolutions `ℚ[V^{•+1} × Z]`, at the level of representations

For the resolution `prodComplex Γ V Z : [n] ↦ ℚ[V^{n+1} × Z]` of rational `Γ`-representations (Mathlib's standard
resolution with an extra permutation factor; the resolutions `resFlag`, `resLine`, `resPlane` of the cone `coneR`),
`nerveDelta p q n h : X n ⟶ X p ⊗ X q` (`h : p + q = n`, diagonal action on the tensor product) is the Alexander-Whitney
diagonal `(x; z) ↦ (x ∘ front; z) ⊗ (x ∘ back; z)`, `front` the first `p + 1` and `back` the last `q + 1` vertices.

* `nerveDelta_d` (Leibniz): `d ≫ Δ_{p,q} = Δ_{p+1,q} ≫ (d ▷ X q) + (-1)^p • (Δ_{p,q+1} ≫ (X p ◁ d))`, from the
  combinatorial `ModelDiagonal.core_identity`.
* `nerveEps : X 0 ⟶ 1`, `nerveEps_comp_d : d₁₀ ≫ ε = 0`, and the counit laws `nerveDelta_counit_left`
  (`Δ_{0,q} ≫ (ε ▷ X q) ≫ λ = 𝟙`) and `nerveDelta_counit_right`.
* `nerveDelta_natural`: for an equivariant map `α : Z → Z'` the chain map `prodMapHom α` (the incidence maps
  `flagLineHom`, `flagPlaneHom` of the model cone) commutes strictly with the diagonals.

The front factor is the one a cochain evaluates (`cap_b = (b ⊗ 1) ∘ Δ`), the back factor is the output.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

section

variable (Γ : Type) [Group Γ] (V Z : Type) [MulAction Γ V] [MulAction Γ Z]

/-- The front and back faces of a simplex `V^{n+1} × Z`. -/
def frontFace (p n : ℕ) (h : p ≤ n) (s : (Fin (n + 1) → V) × Z) : (Fin (p + 1) → V) × Z :=
  (s.1 ∘ frontIdx p n h, s.2)

def backFace (p q n : ℕ) (h : p + q = n) (s : (Fin (n + 1) → V) × Z) : (Fin (q + 1) → V) × Z :=
  (s.1 ∘ backIdx p q n h, s.2)

theorem frontFace_smul (p n : ℕ) (h : p ≤ n) (γ : Γ) (s : (Fin (n + 1) → V) × Z) :
    frontFace V Z p n h (γ • s) = γ • frontFace V Z p n h s := rfl

theorem backFace_smul (p q n : ℕ) (h : p + q = n) (γ : Γ) (s : (Fin (n + 1) → V) × Z) :
    backFace V Z p q n h (γ • s) = γ • backFace V Z p q n h s := rfl

theorem tensor_ρ_tmul {Γ : Type} [Group Γ] (A B : Rep.{0} ℚ Γ) (g : Γ) (a : A) (b : B) :
    (A ⊗ B).ρ g (a ⊗ₜ[ℚ] b) = (A.ρ g a) ⊗ₜ[ℚ] (B.ρ g b) := by
  simp

theorem X_ρ_single (k : ℕ) (γ : Γ) (y : (Fin (k + 1) → V) × Z) (r : ℚ) :
    ((prodComplex Γ V Z).X k).ρ γ (MonoidAlgebra.single y r) = MonoidAlgebra.single (γ • y) r :=
  Representation.ofMulAction_single γ y r

/-- The Alexander-Whitney diagonal of the resolution `ℚ[V^{•+1} × Z]`, in bidegree `(p, q)`. -/
def nerveDelta (p q n : ℕ) (h : p + q = n) :
    (prodComplex Γ V Z).X n ⟶ (prodComplex Γ V Z).X p ⊗ (prodComplex Γ V Z).X q :=
  ofMulActionLift ((Fin (n + 1) → V) × Z) ((prodComplex Γ V Z).X p ⊗ (prodComplex Γ V Z).X q)
    (fun s => (MonoidAlgebra.single (frontFace V Z p n (by omega) s) (1 : ℚ) :
        (prodComplex Γ V Z).X p) ⊗ₜ[ℚ]
      (MonoidAlgebra.single (backFace V Z p q n h s) (1 : ℚ) : (prodComplex Γ V Z).X q))
    (fun γ s => by
      have h1 := X_ρ_single Γ V Z p γ (frontFace V Z p n (by omega) s) 1
      have h2 := X_ρ_single Γ V Z q γ (backFace V Z p q n h s) 1
      exact (congrArg₂ (fun a b => a ⊗ₜ[ℚ] b) h1.symm h2.symm).trans
        (tensor_ρ_tmul ((prodComplex Γ V Z).X p) ((prodComplex Γ V Z).X q) γ _ _).symm)

theorem nerveDelta_single (p q n : ℕ) (h : p + q = n) (s : (Fin (n + 1) → V) × Z) :
    (nerveDelta Γ V Z p q n h).hom (MonoidAlgebra.single s 1) =
      (MonoidAlgebra.single (frontFace V Z p n (by omega) s) (1 : ℚ) : (prodComplex Γ V Z).X p) ⊗ₜ[ℚ]
      (MonoidAlgebra.single (backFace V Z p q n h s) (1 : ℚ) : (prodComplex Γ V Z).X q) :=
  ofMulActionLift_single _ _ _ _ s

theorem d_single (k : ℕ) (y : (Fin (k + 2) → V) × Z) :
    ((prodComplex Γ V Z).d (k + 1) k).hom (MonoidAlgebra.single y 1) =
      ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • (MonoidAlgebra.single (face V Z i y) (1 : ℚ) :
        (prodComplex Γ V Z).X k) := by
  have h := prodComplex_d_comp_eq Γ V Z k (𝟙 ((prodComplex Γ V Z).X k))
  have h' : ((prodComplex Γ V Z).d (k + 1) k).hom (MonoidAlgebra.single y 1) =
      ((prodComplex Γ V Z).d (k + 1) k ≫ 𝟙 ((prodComplex Γ V Z).X k)).hom
        (MonoidAlgebra.single y 1) := rfl
  rw [h', h]
  erw [Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [Rep.zsmul_hom]
  exact congrArg (fun w => ((-1 : ℤ) ^ (i : ℕ)) • w) (delta_single Γ V Z k i y)

theorem whiskerRight_tmul' {Γ : Type} [Group Γ] {A A' : Rep.{0} ℚ Γ} (f : A ⟶ A') (B : Rep.{0} ℚ Γ)
    (a : A) (b : B) : (f ▷ B).hom (a ⊗ₜ[ℚ] b) = f.hom a ⊗ₜ[ℚ] b := by simp

theorem whiskerLeft_tmul' {Γ : Type} [Group Γ] (A : Rep.{0} ℚ Γ) {B B' : Rep.{0} ℚ Γ} (f : B ⟶ B')
    (a : A) (b : B) : (A ◁ f).hom (a ⊗ₜ[ℚ] b) = a ⊗ₜ[ℚ] f.hom b := by simp

/-- **Leibniz rule for the diagonal of the resolution**: `Δ_{p,q} ∘ d = (d ⊗ 1) Δ_{p+1,q} + (-1)^p (1 ⊗ d) Δ_{p,q+1}`. -/
theorem nerveDelta_d (p q n : ℕ) (h : p + q = n) :
    (prodComplex Γ V Z).d (n + 1) n ≫ nerveDelta Γ V Z p q n h =
      nerveDelta Γ V Z (p + 1) q (n + 1) (by omega) ≫
          ((prodComplex Γ V Z).d (p + 1) p ▷ (prodComplex Γ V Z).X q) +
        ((-1 : ℤ) ^ p) • (nerveDelta Γ V Z p (q + 1) (n + 1) (by omega) ≫
          ((prodComplex Γ V Z).X p ◁ (prodComplex Γ V Z).d (q + 1) q)) := by
  subst h
  refine hom_ext_single ((Fin (p + q + 1 + 1) → V) × Z) _ (fun y => ?_)
  obtain ⟨x, z⟩ := y
  have core := core_identity (V := V) (A := ↑((prodComplex Γ V Z).X p ⊗ (prodComplex Γ V Z).X q)) p q
    (fun u v => (MonoidAlgebra.single (u, z) (1 : ℚ) : (prodComplex Γ V Z).X p) ⊗ₜ[ℚ]
      (MonoidAlgebra.single (v, z) (1 : ℚ) : (prodComplex Γ V Z).X q)) x
  have hL : ((prodComplex Γ V Z).d (p + q + 1) (p + q) ≫ nerveDelta Γ V Z p q (p + q) rfl).hom
      (MonoidAlgebra.single (x, z) 1) = ∑ i : Fin (p + q + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((MonoidAlgebra.single ((x ∘ i.succAbove) ∘ frontIdx p (p + q) (by omega), z) (1 : ℚ) :
          (prodComplex Γ V Z).X p) ⊗ₜ[ℚ]
        (MonoidAlgebra.single ((x ∘ i.succAbove) ∘ backIdx p q (p + q) rfl, z) (1 : ℚ) :
          (prodComplex Γ V Z).X q)) := by
    change (nerveDelta Γ V Z p q (p + q) rfl).hom (((prodComplex Γ V Z).d (p + q + 1) (p + q)).hom
      (MonoidAlgebra.single (x, z) 1)) = _
    rw [d_single]
    refine (map_sum _ _ _).trans (Finset.sum_congr rfl (fun i _ => ?_))
    refine (map_zsmul _ _ _).trans ?_
    exact congrArg (fun w => ((-1 : ℤ) ^ (i : ℕ)) • w) (nerveDelta_single Γ V Z p q (p + q) rfl _)
  have hR1 : ((nerveDelta Γ V Z (p + 1) q (p + q + 1) (by omega) ≫
          ((prodComplex Γ V Z).d (p + 1) p ▷ (prodComplex Γ V Z).X q)).hom (MonoidAlgebra.single (x, z) 1)) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((MonoidAlgebra.single ((x ∘ frontIdx (p + 1) (p + q + 1) (by omega)) ∘ i.succAbove, z) (1 : ℚ) :
          (prodComplex Γ V Z).X p) ⊗ₜ[ℚ]
        (MonoidAlgebra.single (x ∘ backIdx (p + 1) q (p + q + 1) (by omega), z) (1 : ℚ) :
          (prodComplex Γ V Z).X q)) := by
    have e0 := congrArg ((prodComplex Γ V Z).d (p + 1) p ▷ (prodComplex Γ V Z).X q).hom
      (nerveDelta_single Γ V Z (p + 1) q (p + q + 1) (by omega) (x, z))
    refine e0.trans ((whiskerRight_tmul' _ _ _ _).trans ?_)
    refine (congrArg (fun w => w ⊗ₜ[ℚ] _) (d_single Γ V Z p _)).trans ?_
    exact (TensorProduct.sum_tmul _ _ _).trans (Finset.sum_congr rfl fun i _ =>
      (TensorProduct.smul_tmul' _ _ _))
  have hR2 : ((nerveDelta Γ V Z p (q + 1) (p + q + 1) (by omega) ≫
          ((prodComplex Γ V Z).X p ◁ (prodComplex Γ V Z).d (q + 1) q)).hom (MonoidAlgebra.single (x, z) 1)) =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
        ((MonoidAlgebra.single (x ∘ frontIdx p (p + q + 1) (by omega), z) (1 : ℚ) :
          (prodComplex Γ V Z).X p) ⊗ₜ[ℚ]
        (MonoidAlgebra.single ((x ∘ backIdx p (q + 1) (p + q + 1) (by omega)) ∘ j.succAbove, z) (1 : ℚ) :
          (prodComplex Γ V Z).X q)) := by
    have e0 := congrArg ((prodComplex Γ V Z).X p ◁ (prodComplex Γ V Z).d (q + 1) q).hom
      (nerveDelta_single Γ V Z p (q + 1) (p + q + 1) (by omega) (x, z))
    refine e0.trans ((whiskerLeft_tmul' _ _ _ _).trans ?_)
    refine (congrArg (fun w => _ ⊗ₜ[ℚ] w) (d_single Γ V Z q _)).trans ?_
    exact (TensorProduct.tmul_sum _ _ _).trans (Finset.sum_congr rfl fun i _ =>
      (map_zsmul (TensorProduct.mk ℚ _ _ _) _ _))
  refine hL.trans (core.trans ?_)
  exact congrArg₂ (fun a b => a + b) hR1.symm (congrArg (fun w => ((-1 : ℤ) ^ p) • w) hR2.symm)

/-- The augmentation `ℚ[V × Z] ⟶ 1` of the resolution to the trivial representation. -/
def nerveEps : (prodComplex Γ V Z).X 0 ⟶ 𝟙_ (Rep.{0} ℚ Γ) :=
  ofMulActionLift ((Fin (0 + 1) → V) × Z) (𝟙_ (Rep.{0} ℚ Γ)) (fun _ => ((1 : ℚ) : 𝟙_ (Rep.{0} ℚ Γ)))
    (fun _ _ => rfl)

theorem nerveEps_single (s : (Fin (0 + 1) → V) × Z) :
    (nerveEps Γ V Z).hom (MonoidAlgebra.single s 1) = ((1 : ℚ) : 𝟙_ (Rep.{0} ℚ Γ)) :=
  ofMulActionLift_single _ _ _ _ s

/-- The augmentation kills the boundary of one-simplices. -/
theorem nerveEps_comp_d : (prodComplex Γ V Z).d 1 0 ≫ nerveEps Γ V Z = 0 := by
  refine hom_ext_single ((Fin (1 + 1) → V) × Z) _ (fun y => ?_)
  have h : ((prodComplex Γ V Z).d 1 0 ≫ nerveEps Γ V Z).hom (MonoidAlgebra.single y 1) =
      (nerveEps Γ V Z).hom (((prodComplex Γ V Z).d (0 + 1) 0).hom (MonoidAlgebra.single y 1)) := rfl
  refine h.trans ?_
  rw [d_single]
  refine (map_sum _ _ _).trans ?_
  have hi : ∀ i : Fin (0 + 2), (nerveEps Γ V Z).hom (((-1 : ℤ) ^ (i : ℕ)) •
      (MonoidAlgebra.single (face V Z i y) (1 : ℚ) : (prodComplex Γ V Z).X 0)) =
      ((-1 : ℤ) ^ (i : ℕ)) • ((1 : ℚ) : 𝟙_ (Rep.{0} ℚ Γ)) := fun i =>
    (map_zsmul _ _ _).trans (congrArg (fun w => ((-1 : ℤ) ^ (i : ℕ)) • w) (nerveEps_single Γ V Z _))
  rw [Finset.sum_congr rfl (fun i _ => hi i), Fin.sum_univ_two]
  simp
  rfl

theorem leftUnitor_tmul' {Γ : Type} [Group Γ] (X : Rep.{0} ℚ Γ) (r : ℚ) (x : X) :
    (λ_ X).hom.hom ((r : (𝟙_ (Rep.{0} ℚ Γ))) ⊗ₜ[ℚ] x) = r • x := by simp

theorem rightUnitor_tmul' {Γ : Type} [Group Γ] (X : Rep.{0} ℚ Γ) (r : ℚ) (x : X) :
    (ρ_ X).hom.hom (x ⊗ₜ[ℚ] (r : (𝟙_ (Rep.{0} ℚ Γ)))) = r • x := by simp

theorem tensorHom_tmul' {Γ : Type} [Group Γ] {A B A' B' : Rep.{0} ℚ Γ} (f : A ⟶ A') (g : B ⟶ B')
    (a : A) (b : B) : (f ⊗ₘ g).hom (a ⊗ₜ[ℚ] b) = f.hom a ⊗ₜ[ℚ] g.hom b := by simp

theorem backFace_zero (q : ℕ) (s : (Fin (q + 1) → V) × Z) :
    backFace V Z 0 q q (zero_add q) s = s := by
  refine Prod.ext ?_ rfl
  funext j
  exact congrArg s.1 (Fin.ext (by simp [backIdx]))

theorem frontFace_self (p : ℕ) (s : (Fin (p + 1) → V) × Z) :
    frontFace V Z p p le_rfl s = s := by
  refine Prod.ext ?_ rfl
  funext j
  simp only [frontFace, frontIdx, Function.comp]

/-- Left counit: `(ε ⊗ 1) Δ_{0,q} = λ⁻¹`. -/
theorem nerveDelta_counit_left (q : ℕ) :
    nerveDelta Γ V Z 0 q q (zero_add q) ≫ (nerveEps Γ V Z ▷ (prodComplex Γ V Z).X q) ≫
      (λ_ ((prodComplex Γ V Z).X q)).hom = 𝟙 ((prodComplex Γ V Z).X q) := by
  refine hom_ext_single ((Fin (q + 1) → V) × Z) _ (fun y => ?_)
  have e0 := congrArg (nerveEps Γ V Z ▷ (prodComplex Γ V Z).X q).hom
    (nerveDelta_single Γ V Z 0 q q (zero_add q) y)
  have e1 := (e0.trans (whiskerRight_tmul' _ _ _ _)).trans
    (congrArg (fun w => w ⊗ₜ[ℚ] _) (nerveEps_single Γ V Z _))
  have e2 := congrArg (λ_ ((prodComplex Γ V Z).X q)).hom.hom e1
  have e3 : ((nerveDelta Γ V Z 0 q q (zero_add q) ≫ (nerveEps Γ V Z ▷ (prodComplex Γ V Z).X q) ≫
      (λ_ ((prodComplex Γ V Z).X q)).hom).hom (MonoidAlgebra.single y 1)) =
      (λ_ ((prodComplex Γ V Z).X q)).hom.hom
        ((nerveEps Γ V Z ▷ (prodComplex Γ V Z).X q).hom
          ((nerveDelta Γ V Z 0 q q (zero_add q)).hom (MonoidAlgebra.single y 1))) := rfl
  refine e3.trans (e2.trans ?_)
  have e4 : (backFace V Z 0 q q (zero_add q) y) = y := backFace_zero V Z q y
  rw [e4]
  exact (leftUnitor_tmul' _ _ _).trans (one_smul ℚ _)

/-- Right counit: `(1 ⊗ ε) Δ_{p,0} = ρ⁻¹`. -/
theorem nerveDelta_counit_right (p : ℕ) :
    nerveDelta Γ V Z p 0 p (add_zero p) ≫ ((prodComplex Γ V Z).X p ◁ nerveEps Γ V Z) ≫
      (ρ_ ((prodComplex Γ V Z).X p)).hom = 𝟙 ((prodComplex Γ V Z).X p) := by
  refine hom_ext_single ((Fin (p + 1) → V) × Z) _ (fun y => ?_)
  have e0 := congrArg ((prodComplex Γ V Z).X p ◁ nerveEps Γ V Z).hom
    (nerveDelta_single Γ V Z p 0 p (add_zero p) y)
  have e1 := (e0.trans (whiskerLeft_tmul' _ _ _ _)).trans
    (congrArg (fun w => _ ⊗ₜ[ℚ] w) (nerveEps_single Γ V Z _))
  have e2 := congrArg (ρ_ ((prodComplex Γ V Z).X p)).hom.hom e1
  have e3 : ((nerveDelta Γ V Z p 0 p (add_zero p) ≫ ((prodComplex Γ V Z).X p ◁ nerveEps Γ V Z) ≫
      (ρ_ ((prodComplex Γ V Z).X p)).hom).hom (MonoidAlgebra.single y 1)) =
      (ρ_ ((prodComplex Γ V Z).X p)).hom.hom
        (((prodComplex Γ V Z).X p ◁ nerveEps Γ V Z).hom
          ((nerveDelta Γ V Z p 0 p (add_zero p)).hom (MonoidAlgebra.single y 1))) := rfl
  refine e3.trans (e2.trans ?_)
  have e4 : (frontFace V Z p p (by omega) y) = y := frontFace_self V Z p y
  rw [e4]
  exact (rightUnitor_tmul' _ _ _).trans (one_smul ℚ _)

/-- Naturality of the diagonal in the permutation factor `Z`. -/
theorem nerveDelta_natural {Z' : Type} [MulAction Γ Z'] (α : Z → Z')
    (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) (p q n : ℕ) (h : p + q = n) :
    (prodMapHom Γ V Z α hα).f n ≫ nerveDelta Γ V Z' p q n h =
      nerveDelta Γ V Z p q n h ≫ ((prodMapHom Γ V Z α hα).f p ⊗ₘ (prodMapHom Γ V Z α hα).f q) := by
  refine hom_ext_single ((Fin (n + 1) → V) × Z) _ (fun y => ?_)
  obtain ⟨x, z⟩ := y
  have e1 : ((prodMapHom Γ V Z α hα).f n ≫ nerveDelta Γ V Z' p q n h).hom (MonoidAlgebra.single (x, z) 1) =
      (nerveDelta Γ V Z' p q n h).hom ((prodMapHom Γ V Z α hα).f n |>.hom (MonoidAlgebra.single (x, z) 1)) :=
    rfl
  refine e1.trans ?_
  rw [prodMapHom_f_single]
  have e2 : (nerveDelta Γ V Z p q n h ≫ ((prodMapHom Γ V Z α hα).f p ⊗ₘ (prodMapHom Γ V Z α hα).f q)).hom
      (MonoidAlgebra.single (x, z) 1) =
      ((prodMapHom Γ V Z α hα).f p ⊗ₘ (prodMapHom Γ V Z α hα).f q).hom
        ((nerveDelta Γ V Z p q n h).hom (MonoidAlgebra.single (x, z) 1)) := rfl
  refine Eq.trans ?_ e2.symm
  refine (nerveDelta_single Γ V Z' p q n h (x, α z)).trans ?_
  refine Eq.trans ?_ (congrArg ((prodMapHom Γ V Z α hα).f p ⊗ₘ (prodMapHom Γ V Z α hα).f q).hom
    (nerveDelta_single Γ V Z p q n h (x, z))).symm
  refine Eq.trans ?_ (tensorHom_tmul' _ _ _ _).symm
  exact congrArg₂ (fun a b => a ⊗ₜ[ℚ] b) (prodMapHom_f_single Γ V Z α hα p _ z).symm
    (prodMapHom_f_single Γ V Z α hα q _ z).symm

end

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
