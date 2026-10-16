module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.M3Def
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitPairing

@[expose] public section


open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.EquivariantSingularSmall TernaryPoly.BoundaryFaceResolutionComparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull

/-!
# Support of the flag classes (M3a(i-a))

Formalized by Claude Sonnet 5.5.

If a line (plane) datum `d` is supported on a `Γ(6)`-invariant set of lines (planes) `S` and the primitive `γ` of `d.z ∪ e.z` vanishes off `S`, then the flag class
`lineFlagClass`/`planeFlagClass` vanishes at every flag orbit whose line (plane) is not in `S` (`lineFlagClass_eq_zero_of_not_mem`, `planeFlagClass_eq_zero_of_not_mem`; the
proof only uses `d.w` (resp. `d.z`) and `γ` and the explicit bar form `lineFlag_faceCoord`/`planeFlag_faceCoord`).  Cutting commutes with the diagonal (`cutHom_nerveDelta`), so the
cut `γ' = cut_S ∘ γ` of any primitive is again a primitive (`cutγ_line_primitive`, `cutγ_plane_primitive`) vanishing off `S` (`cutγ_*_vanishes`); then the sum of the coordinates over all flag
orbits is the sum over the flag orbits over `S` (`lineFlag_sum_eq_filter`, `planeFlag_sum_eq_filter`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))

/-- **Support (lines)**: if the datum `d` is supported on `S` and the primitive `γ` vanishes off `S`, the flag class vanishes at every flag orbit whose line is not in `S`. -/
theorem lineFlagClass_eq_zero_of_not_mem (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Line) (hd : d.IsOn S)
    (hγS : ∀ (u : Fin 4 → RationalGL3) (ℓ : Line), ℓ ∉ S → γ.hom (MonoidAlgebra.single (u, ℓ) 1) = 0)
    (o : labelOrbits Γ6 Flag) (ho : flagLineOf o.out ∉ S) :
    lineFlagClass π d e γ hγ o = 0 := by
  obtain ⟨hdd, hcoh⟩ := lineFlag_faceCoord π o.out (fun g => g.2) d.w e.z γ (lineFlagCochain_cocycle π d e γ hγ)
  unfold lineFlagClass
  rw [hcoh]
  have hf0 : ∀ x : Fin 3 → MulAction.stabilizer Γ6 o.out,
      cup12 ((W'.ρ).comp (MulAction.stabilizer Γ6 o.out).subtype) (pairOf π)
        (fun s : MulAction.stabilizer Γ6 o.out => barCochain (MulAction.stabilizer Γ6 o.out) (1 : RationalGL3) o.out d.w
          (fun _ : Fin 1 => s))
        (fun s t : MulAction.stabilizer Γ6 o.out => barCochain (MulAction.stabilizer Γ6 o.out) (1 : RationalGL3)
          (SymmetricSpaceBoundaryFaceAugmentation.flagLine o.out) e.z (fun j : Fin 2 => if j = 0 then s else t))
        (x 0) (x 1) (x 2) -
      barCochain (MulAction.stabilizer Γ6 o.out) (1 : RationalGL3)
        (SymmetricSpaceBoundaryFaceAugmentation.flagLine o.out) γ x = 0 := by
    intro x
    have h1 : ∀ s : MulAction.stabilizer Γ6 o.out, barCochain (MulAction.stabilizer Γ6 o.out) (1 : RationalGL3) o.out d.w
        (fun _ : Fin 1 => s) = 0 := fun s => hd.2 _ _ ho
    have h2 : barCochain (MulAction.stabilizer Γ6 o.out) (1 : RationalGL3)
        (SymmetricSpaceBoundaryFaceAugmentation.flagLine o.out) γ x = 0 := hγS _ _ ho
    simp only [h1, h2, cup12, map_zero, LinearMap.zero_apply, sub_zero]
  have hi : Function.Injective (groupCohomology.iCocycles
      (Rep.res (MulAction.stabilizer Γ6 o.out).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hz : groupCohomology.cocyclesMk _ hdd = 0 := by
    apply hi
    rw [groupCohomology.iCocycles_mk, map_zero]
    funext x
    exact hf0 x
  rw [hz, map_zero]



/-- **Support (planes)**: if the datum `d` is supported on the set of planes `S` and the primitive `γ` vanishes off `S`, the flag class vanishes at every flag orbit whose plane is not in `S`. -/
theorem planeFlagClass_eq_zero_of_not_mem (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Plane) (hd : d.IsOn S)
    (hγS : ∀ (u : Fin 4 → RationalGL3) (P : Plane), P ∉ S → γ.hom (MonoidAlgebra.single (u, P) 1) = 0)
    (o : labelOrbits Γ6 Flag) (ho : flagPlaneOf o.out ∉ S) :
    planeFlagClass π d e γ hγ o = 0 := by
  obtain ⟨hdd, hcoh⟩ := planeFlag_faceCoord π o.out (fun g => g.2) d.z e.w γ (planeFlagCochain_cocycle π d e γ hγ)
  unfold planeFlagClass
  rw [hcoh]
  have hf0 : ∀ x : Fin 3 → MulAction.stabilizer Γ6 o.out,
      cup21 ((W'.ρ).comp (MulAction.stabilizer Γ6 o.out).subtype) (pairOf π)
        (fun s t : MulAction.stabilizer Γ6 o.out => barCochain (MulAction.stabilizer Γ6 o.out) (1 : RationalGL3)
          (SymmetricSpaceBoundaryFaceAugmentation.flagPlane o.out) d.z (fun j : Fin 2 => if j = 0 then s else t))
        (fun s : MulAction.stabilizer Γ6 o.out => barCochain (MulAction.stabilizer Γ6 o.out) (1 : RationalGL3) o.out (-e.w)
          (fun _ : Fin 1 => s))
        (x 0) (x 1) (x 2) +
      barCochain (MulAction.stabilizer Γ6 o.out) (1 : RationalGL3)
        (SymmetricSpaceBoundaryFaceAugmentation.flagPlane o.out) γ x = 0 := by
    intro x
    have h1 : ∀ s t : MulAction.stabilizer Γ6 o.out, barCochain (MulAction.stabilizer Γ6 o.out) (1 : RationalGL3)
        (SymmetricSpaceBoundaryFaceAugmentation.flagPlane o.out) d.z (fun j : Fin 2 => if j = 0 then s else t) = 0 :=
      fun s t => hd.1 _ _ ho
    have h2 : barCochain (MulAction.stabilizer Γ6 o.out) (1 : RationalGL3)
        (SymmetricSpaceBoundaryFaceAugmentation.flagPlane o.out) γ x = 0 := hγS _ _ ho
    simp only [h1, h2, cup21, map_zero, LinearMap.zero_apply, add_zero]
  have hi : Function.Injective (groupCohomology.iCocycles
      (Rep.res (MulAction.stabilizer Γ6 o.out).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hz : groupCohomology.cocyclesMk _ hdd = 0 := by
    apply hi
    rw [groupCohomology.iCocycles_mk, map_zero]
    funext x
    exact hf0 x
  rw [hz, map_zero]



section Cut

open Classical in
theorem cutHom_nerveDelta {Z : Type} [MulAction Γ6 Z] (S : Set Z) (hS : ∀ (γ : Γ6) (z : Z), γ • z ∈ S ↔ z ∈ S)
    (p q n : ℕ) (h : p + q = n) :
    cutHom Γ6 RationalGL3 Z S hS n ≫ nerveDelta Γ6 RationalGL3 Z p q n h =
      nerveDelta Γ6 RationalGL3 Z p q n h ≫ (cutHom Γ6 RationalGL3 Z S hS p ⊗ₘ cutHom Γ6 RationalGL3 Z S hS q) := by
  refine hom_ext_single ((Fin (n + 1) → RationalGL3) × Z) _ (fun y => ?_)
  obtain ⟨x, z⟩ := y
  have e1 : (cutHom Γ6 RationalGL3 Z S hS n ≫ nerveDelta Γ6 RationalGL3 Z p q n h).hom (MonoidAlgebra.single (x, z) 1) =
      (nerveDelta Γ6 RationalGL3 Z p q n h).hom ((cutHom Γ6 RationalGL3 Z S hS n).hom (MonoidAlgebra.single (x, z) 1)) := rfl
  have e2 : (nerveDelta Γ6 RationalGL3 Z p q n h ≫ (cutHom Γ6 RationalGL3 Z S hS p ⊗ₘ cutHom Γ6 RationalGL3 Z S hS q)).hom
      (MonoidAlgebra.single (x, z) 1) =
      (cutHom Γ6 RationalGL3 Z S hS p ⊗ₘ cutHom Γ6 RationalGL3 Z S hS q).hom
        ((nerveDelta Γ6 RationalGL3 Z p q n h).hom (MonoidAlgebra.single (x, z) 1)) := rfl
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [nerveDelta_single]
  have hf : (frontFace RationalGL3 Z p n (by omega) (x, z)).2 = z := rfl
  have hb : (backFace RationalGL3 Z p q n h (x, z)).2 = z := rfl
  refine Eq.trans ?_ (tensorHom_tmul' _ _ _ _).symm
  have a1 := cutHom_single Γ6 RationalGL3 Z S hS n (x, z)
  have a2 := cutHom_single Γ6 RationalGL3 Z S hS p (frontFace RationalGL3 Z p n (by omega) (x, z))
  have a3 := cutHom_single Γ6 RationalGL3 Z S hS q (backFace RationalGL3 Z p q n h (x, z))
  by_cases hz : z ∈ S
  · rw [hf] at a2
    rw [hb] at a3
    erw [a1, a2, a3, ite_eq_left hz, ite_eq_left hz, ite_eq_left hz, nerveDelta_single]
    rfl
  · rw [hf] at a2
    rw [hb] at a3
    erw [a1, a2, a3, ite_eq_right hz, ite_eq_right hz, ite_eq_right hz, map_zero]
    exact (TensorProduct.zero_tmul _ _).symm




open Classical in
/-- **Cutting a primitive preserves the primitive property** (lines): if `d`, `e` are supported on the `Γ(6)`-invariant set `S` and `γ` is a primitive of `d.z ∪ e.z`, then
so is `γ' = cut_S ∘ γ`; and `γ'` vanishes off `S` (`cutγ_line_vanishes`). -/
theorem cutγ_line_primitive (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S) (hd : d.IsOn S) (he : e.IsOn S) :
    (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ (cutHom Γ6 RationalGL3 Line S hS 3 ≫ γ) =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π := by
  rw [← Category.assoc, cutHom_comm_d, Category.assoc, hγ]
  have hΔ := cutHom_nerveDelta (Z := Line) S hS 2 2 4 rfl
  change cutHom Γ6 RationalGL3 Line S hS 4 ≫ nerveDelta Γ6 RationalGL3 Line 2 2 4 rfl ≫ _ = _
  rw [← Category.assoc, hΔ, Category.assoc, ← Category.assoc (cutHom Γ6 RationalGL3 Line S hS 2 ⊗ₘ _),
    tensorHom_comp_tensorHom, LineDatum.cut_z_of_isOn S hS d hd, LineDatum.cut_z_of_isOn S hS e he]
  rfl

theorem cutγ_line_vanishes (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S) :
    ∀ (u : Fin 4 → RationalGL3) (ℓ : Line), ℓ ∉ S →
      (cutHom Γ6 RationalGL3 Line S hS 3 ≫ γ).hom (MonoidAlgebra.single (u, ℓ) 1) = 0 := by
  intro u ℓ hℓ
  change γ.hom ((cutHom Γ6 RationalGL3 Line S hS 3).hom (MonoidAlgebra.single (u, ℓ) 1)) = 0
  erw [cutHom_single, ite_eq_right hℓ, map_zero]



open Classical in
/-- **Cutting a primitive preserves the primitive property** (planes): if `d`, `e` are supported on the `Γ(6)`-invariant set `S` and `γ` is a primitive of `d.z ∪ e.z`, then
so is `γ' = cut_S ∘ γ`; and `γ'` vanishes off `S` (`cutγ_plane_vanishes`). -/
theorem cutγ_plane_primitive (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S) (hd : d.IsOn S) (he : e.IsOn S) :
    (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ (cutHom Γ6 RationalGL3 Plane S hS 3 ≫ γ) =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π := by
  rw [← Category.assoc, cutHom_comm_d, Category.assoc, hγ]
  have hΔ := cutHom_nerveDelta (Z := Plane) S hS 2 2 4 rfl
  change cutHom Γ6 RationalGL3 Plane S hS 4 ≫ nerveDelta Γ6 RationalGL3 Plane 2 2 4 rfl ≫ _ = _
  rw [← Category.assoc, hΔ, Category.assoc, ← Category.assoc (cutHom Γ6 RationalGL3 Plane S hS 2 ⊗ₘ _),
    tensorHom_comp_tensorHom, PlaneDatum.cut_z_of_isOn S hS d hd, PlaneDatum.cut_z_of_isOn S hS e he]
  rfl

theorem cutγ_plane_vanishes (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S) :
    ∀ (u : Fin 4 → RationalGL3) (P : Plane), P ∉ S →
      (cutHom Γ6 RationalGL3 Plane S hS 3 ≫ γ).hom (MonoidAlgebra.single (u, P) 1) = 0 := by
  intro u P hP
  change γ.hom ((cutHom Γ6 RationalGL3 Plane S hS 3).hom (MonoidAlgebra.single (u, P) 1)) = 0
  erw [cutHom_single, ite_eq_right hP, map_zero]



end Cut

section Sums

open Classical in
/-- **Support of the flag sum (lines)**: for the cut primitive `γ'` of `γ`, the sum of the coordinates of the flag classes is the sum over the flag orbits lying over `S`. -/
theorem lineFlag_sum_eq_filter (E : FlagEval) (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S) (hd : d.IsOn S) (he : e.IsOn S) :
    ∑ o, E.lam o (lineFlagClass π d e (cutHom Γ6 RationalGL3 Line S hS 3 ≫ γ) (cutγ_line_primitive π d e γ hγ S hS hd he) o) =
      ∑ o ∈ Finset.univ.filter (fun o : labelOrbits Γ6 Flag => flagLineOf o.out ∈ S),
        E.lam o (lineFlagClass π d e (cutHom Γ6 RationalGL3 Line S hS 3 ≫ γ) (cutγ_line_primitive π d e γ hγ S hS hd he) o) := by
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) (fun o _ ho => ?_)
  have hno : flagLineOf o.out ∉ S := fun h => ho (by simpa using h)
  rw [lineFlagClass_eq_zero_of_not_mem π d e _ _ S hd (cutγ_line_vanishes _ S hS) o hno, map_zero]

open Classical in
/-- **Support of the flag sum (planes).** -/
theorem planeFlag_sum_eq_filter (E : FlagEval) (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S) (hd : d.IsOn S) (he : e.IsOn S) :
    ∑ o, E.lam o (planeFlagClass π d e (cutHom Γ6 RationalGL3 Plane S hS 3 ≫ γ) (cutγ_plane_primitive π d e γ hγ S hS hd he) o) =
      ∑ o ∈ Finset.univ.filter (fun o : labelOrbits Γ6 Flag => flagPlaneOf o.out ∈ S),
        E.lam o (planeFlagClass π d e (cutHom Γ6 RationalGL3 Plane S hS 3 ≫ γ) (cutγ_plane_primitive π d e γ hγ S hS hd he) o) := by
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) (fun o _ ho => ?_)
  have hno : flagPlaneOf o.out ∉ S := fun h => ho (by simpa using h)
  rw [planeFlagClass_eq_zero_of_not_mem π d e _ _ S hd (cutγ_plane_vanishes _ S hS) o hno, map_zero]

end Sums

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
