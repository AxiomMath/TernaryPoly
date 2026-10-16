module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Local
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CupProduct

@[expose] public section


/-!
# Bar-level translation of the nerve differentials

Formalized by Claude Sonnet 5.5.

* `barCochain_d`: the bar cochain of `d ≫ θ` is the inhomogeneous differential of the bar cochain of `θ`;
* `bar_dd1`, `bar_dd3T`: the explicit forms `dd1`, `dd3T` of the differentials of bar cochains of degrees one and three;
* `diag22_bar`: the model diagonal in bidegree `(2,2)` on a bar simplex is `cup22`;
* `barCochain_restrict_hom`: bar cochains are compatible with the inclusion of a smaller group fixing the same point.
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.EquivariantSingularSmall

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

section Formulas

open groupCohomology

variable {G : Type} [Group G] (A : Rep.{0} ℚ G)

theorem dOne_general_apply (f : (Fin 1 → G) → A) (g : Fin 2 → G) :
    (inhomogeneousCochains.d A 1).hom f g =
      A.ρ (g 0) (f ![g 1]) - f ![g 0 * g 1] + f ![g 0] := by
  have h0 : Fin.contractNth 0 (fun x1 x2 : G => x1 * x2) g = ![g 0 * g 1] := by
    ext i; fin_cases i; simp [Fin.contractNth]
  have h1 : (fun i : Fin 1 => g i.succ) = ![g 1] := by
    ext i; fin_cases i; simp
  have h2 : Fin.contractNth 1 (fun x1 x2 : G => x1 * x2) g = ![g 0] := by
    ext i; fin_cases i; simp [Fin.contractNth]
  simp [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_succ, h0, h1, h2]
  abel

theorem dThree_general_apply (f : (Fin 3 → G) → A) (g : Fin 4 → G) :
    (inhomogeneousCochains.d A 3).hom f g =
      A.ρ (g 0) (f ![g 1, g 2, g 3]) - f ![g 0 * g 1, g 2, g 3] + f ![g 0, g 1 * g 2, g 3] -
        f ![g 0, g 1, g 2 * g 3] + f ![g 0, g 1, g 2] := by
  have h0 : Fin.contractNth 0 (fun x1 x2 : G => x1 * x2) g = ![g 0 * g 1, g 2, g 3] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h1 : Fin.contractNth 1 (fun x1 x2 : G => x1 * x2) g = ![g 0, g 1 * g 2, g 3] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h2 : Fin.contractNth 2 (fun x1 x2 : G => x1 * x2) g = ![g 0, g 1, g 2 * g 3] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  have h3 : (fun i : Fin 3 => g i.succ) = ![g 1, g 2, g 3] := by
    ext i; fin_cases i <;> simp
  have h4 : Fin.contractNth 3 (fun x1 x2 : G => x1 * x2) g = ![g 0, g 1, g 2] := by
    ext i; fin_cases i <;> simp [Fin.contractNth]
  simp [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_succ, h0, h1, h2, h3, h4]
  norm_num
  abel

end Formulas

section Bar

open groupCohomology

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (T : Subgroup Γ) (W : Rep.{0} ℚ Γ)
  (v₀ : V) (z : Z) (hz : ∀ g : T, g • z = z)

include hz in
/-- **The bar cochain of `d ≫ θ` is the inhomogeneous differential of the bar cochain of `θ`.** -/
theorem barCochain_d {k : ℕ} (θ : (prodComplex Γ V Z).X k ⟶ W) :
    (inhomogeneousCochains.d (Rep.res T.subtype W) k).hom (fun x => barCochain T v₀ z θ x) =
      fun x => barCochain T v₀ z ((prodComplex Γ V Z).d (k + 1) k ≫ θ) x := by
  let Φ := stabCoord T W v₀ z hz ≫ (inhomogeneousCochainsIso (Rep.res T.subtype W)).inv
  have hc := congrArg (fun φ => φ.hom θ) (Φ.comm k (k + 1))
  have e1 : ((Φ.f k).hom θ) = fun x => barCochain T v₀ z θ x := by
    funext x
    exact stabCoord_inhom_apply T W v₀ z hz θ x
  have e3 : ((homCochains (prodComplex Γ V Z) W).d k (k + 1)).hom θ = (prodComplex Γ V Z).d (k + 1) k ≫ θ := by
    rfl
  have e2 : ((Φ.f (k + 1)).hom ((homCochains (prodComplex Γ V Z) W).d k (k + 1) |>.hom θ)) =
      fun x => barCochain T v₀ z ((prodComplex Γ V Z).d (k + 1) k ≫ θ) x := by
    rw [e3]
    funext x
    exact stabCoord_inhom_apply T W v₀ z hz (k := k + 1) ((prodComplex Γ V Z).d (k + 1) k ≫ θ) x
  rw [← e2, ← e1]
  have hd : (inhomogeneousCochains (Rep.res T.subtype W)).d k (k + 1) = inhomogeneousCochains.d (Rep.res T.subtype W) k := by
    simp [inhomogeneousCochains, CochainComplex.of_d]
  rw [hd] at hc
  exact hc

include hz in
/-- The explicit form of the differential of a bar cochain of degree one. -/
theorem bar_dd1 (θ : (prodComplex Γ V Z).X 1 ⟶ W) (s t : T) :
    dd1 ((W.ρ).comp T.subtype) (fun s : T => barCochain T v₀ z θ (fun _ : Fin 1 => s)) s t =
      barCochain T v₀ z ((prodComplex Γ V Z).d 2 1 ≫ θ) (fun j : Fin 2 => if j = 0 then s else t) := by
  have h := congrFun (barCochain_d T W v₀ z hz θ) ![s, t]
  rw [dOne_general_apply] at h
  have e1 : (![s, t] : Fin 2 → T) = fun j : Fin 2 => if j = 0 then s else t := by
    funext j; fin_cases j <;> rfl
  have e2 : ∀ x : T, (![x] : Fin 1 → T) = fun _ => x := by
    intro x; funext j; fin_cases j; rfl
  rw [e1] at h
  simp only [e2] at h
  simpa [dd1, e1, e2] using h

include hz in
/-- The explicit form of the differential of a bar cochain of degree three with trivial coefficients. -/
theorem bar_dd3T (θ : (prodComplex Γ V Z).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ)) (a b c d : T) :
    dd3T (fun a b c : T => barCochain T v₀ z θ ![a, b, c]) a b c d =
      barCochain T v₀ z ((prodComplex Γ V Z).d 4 3 ≫ θ) ![a, b, c, d] := by
  have h := congrFun (barCochain_d T (𝟙_ (Rep.{0} ℚ Γ)) v₀ z hz θ) ![a, b, c, d]
  rw [dThree_general_apply] at h
  have hr : ∀ (g : T) (x : ℚ), ((MonoidHom.comp (𝟙_ (Rep.{0} ℚ Γ)).ρ T.subtype) g) x = x := fun _ _ => rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, hr, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h
  simp only [dd3T]
  exact h

section Diag22

variable (hz : ∀ s : T, (s : Γ) • z = z) {W' W'' : Rep.{0} ℚ Γ} (π : W' ⊗ W'' ⟶ 𝟙_ (Rep.{0} ℚ Γ))

include hz in
/-- **The model diagonal in bidegree `(2,2)` on a bar simplex is `cup22`.** -/
theorem diag22_bar (f : (prodComplex Γ V Z).X 2 ⟶ W') (g : (prodComplex Γ V Z).X 2 ⟶ W'') (x : Fin 4 → T) :
    (nerveDelta Γ V Z 2 2 4 rfl ≫ (f ⊗ₘ g) ≫ π).hom (MonoidAlgebra.single (barSimplex T v₀ z x) 1) =
      cup22 ((W''.ρ).comp T.subtype) (pairOf π)
        (fun s t : T => barCochain T v₀ z f (fun j : Fin 2 => if j = 0 then s else t))
        (fun s t : T => barCochain T v₀ z g (fun j : Fin 2 => if j = 0 then s else t)) (x 0) (x 1) (x 2) (x 3) := by
  refine (diag_pair_bar T v₀ z hz π 2 2 f g x).trans ?_
  have e1 : (fun j : Fin 2 => x ⟨j.1, by omega⟩) = fun j => if j = 0 then x 0 else x 1 := by
    funext j; fin_cases j <;> rfl
  have e2 : (Fin.partialProd x ⟨2, by omega⟩ : T) = x 0 * x 1 := by
    have h1 := pp_succ x 1 (by omega)
    have h0 := pp_succ x 0 (by omega)
    have h00 : Fin.partialProd x ⟨0, by omega⟩ = 1 := Fin.partialProd_zero x
    rw [h00, one_mul] at h0
    rw [h0] at h1
    exact h1
  have e3 : (fun j : Fin 2 => x ⟨2 + j.1, by omega⟩) = fun j => if j = 0 then x 2 else x 3 := by
    funext j; fin_cases j <;> rfl
  rw [e1, e2, e3]
  rfl

end Diag22

section Restrict

/-- **Bar cochains are compatible with an inclusion of groups fixing the same data.** -/
theorem barCochain_restrict_hom (H : Subgroup Γ) (ι : H →* T) (hι : ∀ h : H, ((ι h : T) : Γ) = (h : Γ))
    {k : ℕ} (θ : (prodComplex Γ V Z).X k ⟶ W) (x : Fin k → H) :
    barCochain H v₀ z θ x = barCochain T v₀ z θ (fun i => ι (x i)) := by
  have hpp : ∀ i : Fin (k + 1), (((Fin.partialProd x i : H)) : Γ) = (((Fin.partialProd (fun j => ι (x j)) i : T)) : Γ) := by
    intro i
    induction' i using Fin.induction with i ih
    · simp [Fin.partialProd_zero]
    · rw [Fin.partialProd_succ, Fin.partialProd_succ, Subgroup.coe_mul, Subgroup.coe_mul, ih, hι]
  have hs : barSimplex H v₀ z x = barSimplex T v₀ z (fun i => ι (x i)) := by
    refine Prod.ext ?_ rfl
    funext i
    exact congrArg (fun g : Γ => g • v₀) (hpp i)
  unfold barCochain
  rw [hs]

end Restrict

end Bar

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
