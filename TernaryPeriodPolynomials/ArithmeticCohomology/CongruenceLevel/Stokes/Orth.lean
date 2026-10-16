module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cut

@[expose] public section


/-!
# Orthogonality of cochains with disjoint supports in the cone pairing

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open GeneralEisenstein
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section Support

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] {W W' T : Rep.{0} ℚ Γ}

/-- **Cup products of cochains with disjoint label supports vanish.** -/
theorem nerveDelta_pair_zero (p q n : ℕ) (h : p + q = n) (π : W ⊗ W' ⟶ T) (S : Set Z)
    (X : (prodComplex Γ V Z).X p ⟶ W) (Y : (prodComplex Γ V Z).X q ⟶ W')
    (hX : ∀ (u : Fin (p + 1) → V) (z : Z), z ∉ S → X.hom (MonoidAlgebra.single (u, z) 1) = 0)
    (hY : ∀ (u : Fin (q + 1) → V) (z : Z), z ∈ S → Y.hom (MonoidAlgebra.single (u, z) 1) = 0) :
    nerveDelta Γ V Z p q n h ≫ (X ⊗ₘ Y) ≫ π = 0 := by
  refine hom_ext_single ((Fin (n + 1) → V) × Z) _ (fun s => ?_)
  change π.hom ((X ⊗ₘ Y).hom ((nerveDelta Γ V Z p q n h).hom (MonoidAlgebra.single s 1))) = 0
  rw [nerveDelta_single]
  erw [tensorHom_hom_tmul]
  by_cases hs : s.2 ∈ S
  · have e : Y.hom (MonoidAlgebra.single (backFace V Z p q n h s) 1) = 0 := hY _ s.2 hs
    erw [e, TensorProduct.tmul_zero, map_zero]
  · have e : X.hom (MonoidAlgebra.single (frontFace V Z p n (by omega) s) 1) = 0 := hX _ s.2 hs
    erw [e, TensorProduct.zero_tmul, map_zero]

end Support


section Coords

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (v : coneR.X 4)
  (X : coneR.X 2 ⟶ W) (Y : coneR.X 2 ⟶ W')

/-- **The cone pairing in coordinates**: the corner terms on `v_A`, the line pairing on `v_L` and the plane pairing on `v_P`. -/
theorem conePair_coords :
    conePair π v X Y =
      ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫
          ((modelPush.iA 1 ≫ X) ⊗ₘ (flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ Y)) ≫ π +
        (nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫
          ((flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ X) ⊗ₘ (modelPush.iA 1 ≫ Y)) ≫ π).hom ((modelPush.pA 3).hom v) +
      ((nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫
          ((modelPush.iL 2 ≫ X) ⊗ₘ (modelPush.iL 2 ≫ Y)) ≫ π).hom ((modelPush.pL 3).hom v) +
      ((nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫
          ((modelPush.iP 2 ≫ X) ⊗ₘ (modelPush.iP 2 ≫ Y)) ≫ π).hom ((modelPush.pP 3).hom v) := by
  have hdec := modelPush.decomp_succ 3 v
  generalize (modelPush.pA 3).hom v = x at hdec ⊢
  generalize (modelPush.pL 3).hom v = l at hdec ⊢
  generalize (modelPush.pP 3).hom v = p at hdec ⊢
  subst hdec
  have hA : (modelPush.iA 3 ≫ modelDiagSystem.Δ 2 2 4 rfl ≫ (X ⊗ₘ Y) ≫ π).hom x = _ :=
    congrArg (fun m => m.hom x) (modelPush.iA_pair (nerveDiagSystem Γ6 RationalGL3 Flag)
      (nerveDiagSystem Γ6 RationalGL3 Line) (nerveDiagSystem Γ6 RationalGL3 Plane) π X Y)
  have hL : (modelPush.iL 4 ≫ modelDiagSystem.Δ 2 2 4 rfl ≫ (X ⊗ₘ Y) ≫ π).hom l = _ :=
    congrArg (fun m => m.hom l) (modelPush.iL_pair (nerveDiagSystem Γ6 RationalGL3 Flag)
      (nerveDiagSystem Γ6 RationalGL3 Line) (nerveDiagSystem Γ6 RationalGL3 Plane) π X Y)
  have hP : (modelPush.iP 4 ≫ modelDiagSystem.Δ 2 2 4 rfl ≫ (X ⊗ₘ Y) ≫ π).hom p = _ :=
    congrArg (fun m => m.hom p) (modelPush.iP_pair (nerveDiagSystem Γ6 RationalGL3 Flag)
      (nerveDiagSystem Γ6 RationalGL3 Line) (nerveDiagSystem Γ6 RationalGL3 Plane) π X Y)
  unfold conePair
  rw [map_add, map_add]
  erw [hA, hL, hP]

end Coords


/-- The line of a complete flag. -/
abbrev flagLineOf : Flag → Line := TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine
/-- The plane of a complete flag. -/
abbrev flagPlaneOf : Flag → Plane := TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane

section OrthLine

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (v : coneR.X 4)

theorem flagLineHom_cochain_single (z : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W') (u : Fin 3 → RationalGL3)
    (F : Flag) :
    (flagLineHom.hom.f 2 ≫ z).hom (MonoidAlgebra.single (u, F) 1) = z.hom (MonoidAlgebra.single (u, flagLineOf F) 1) := by
  change z.hom ((flagLineHom.hom.f 2).hom (MonoidAlgebra.single (u, F) 1)) = _
  rw [flagLineHom, prodMapHom_f_single]
  rfl

/-- **Line cochains supported on disjoint sets of lines are orthogonal** (corner terms included, for primitives supported on the flags over the
first set). -/
theorem conePair_lineCone_orth (S : Set Line) (w : A.X 1 ⟶ W)
    (z : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W) (w' : A.X 1 ⟶ W')
    (z' : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W')
    (hz : ∀ (u : Fin 3 → RationalGL3) (ℓ : Line), ℓ ∉ S → z.hom (MonoidAlgebra.single (u, ℓ) 1) = 0)
    (hz' : ∀ (u : Fin 3 → RationalGL3) (ℓ : Line), ℓ ∈ S → z'.hom (MonoidAlgebra.single (u, ℓ) 1) = 0)
    (hw : ∀ (u : Fin 2 → RationalGL3) (F : Flag), flagLineOf F ∉ S → w.hom (MonoidAlgebra.single (u, F) 1) = 0) :
    conePair π v (lineCone w z) (lineCone w' z') = 0 := by
  rw [conePair_coords]
  simp only [lineCone_corner, lineCone_line, lineCone_plane, comp_zero, PushCone.zero_tensorHom',
    PushCone.tensorHom_zero', zero_comp]
  have h1 : (nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫ (w ⊗ₘ (flagLineHom.hom.f 2 ≫ z')) ≫ π = 0 :=
    nerveDelta_pair_zero 1 2 3 rfl π (flagLineOf ⁻¹' S) w (flagLineHom.hom.f 2 ≫ z')
      (fun u F hF => hw u F hF)
      (fun u F hF => by
        rw [flagLineHom_cochain_single]
        exact hz' _ _ hF)
  have h3 : (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (z ⊗ₘ z') ≫ π = 0 :=
    nerveDelta_pair_zero 2 2 4 rfl π S z z' hz hz'
  rw [h1, h3]
  simp

end OrthLine


section OrthPlane

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (v : coneR.X 4)

theorem flagPlaneHom_cochain_single (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) (u : Fin 3 → RationalGL3)
    (F : Flag) :
    (flagPlaneHom.hom.f 2 ≫ z).hom (MonoidAlgebra.single (u, F) 1) = z.hom (MonoidAlgebra.single (u, flagPlaneOf F) 1) := by
  change z.hom ((flagPlaneHom.hom.f 2).hom (MonoidAlgebra.single (u, F) 1)) = _
  rw [flagPlaneHom, prodMapHom_f_single]
  rfl

/-- **Plane cochains supported on disjoint sets of planes are orthogonal.** -/
theorem conePair_planeCone_orth (S : Set Plane) (w : A.X 1 ⟶ W)
    (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) (w' : A.X 1 ⟶ W')
    (z' : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W')
    (hz : ∀ (u : Fin 3 → RationalGL3) (P : Plane), P ∉ S → z.hom (MonoidAlgebra.single (u, P) 1) = 0)
    (hz' : ∀ (u : Fin 3 → RationalGL3) (P : Plane), P ∈ S → z'.hom (MonoidAlgebra.single (u, P) 1) = 0)
    (hw' : ∀ (u : Fin 2 → RationalGL3) (F : Flag), flagPlaneOf F ∈ S → w'.hom (MonoidAlgebra.single (u, F) 1) = 0) :
    conePair π v (planeCone w z) (planeCone w' z') = 0 := by
  rw [conePair_coords]
  simp only [planeCone_corner, planeCone_line, planeCone_plane, comp_zero, PushCone.tensorHom_zero',
    zero_comp]
  have h2 : (nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫ ((flagPlaneHom.hom.f 2 ≫ z) ⊗ₘ (-w')) ≫ π = 0 :=
    nerveDelta_pair_zero 2 1 3 rfl π (flagPlaneOf ⁻¹' S) (flagPlaneHom.hom.f 2 ≫ z) (-w')
      (fun u F hF => by
        rw [flagPlaneHom_cochain_single]
        exact hz _ _ hF)
      (fun u F hF => by
        have := hw' u F hF
        change -(w'.hom (MonoidAlgebra.single (u, F) 1)) = 0
        rw [this, neg_zero])
  have h3 : (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (z ⊗ₘ z') ≫ π = 0 :=
    nerveDelta_pair_zero 2 2 4 rfl π S z z' hz hz'
  rw [h2, h3]
  simp

end OrthPlane


section Cells

variable {W W' : Rep.{0} ℚ Γ6}

/-- The cut of a line datum to the lines of `S` (and the flags over them). -/
def LineDatum.cut (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S) (d : LineDatum W) :
    LineDatum W where
  z := cutHom Γ6 RationalGL3 Line S hS 2 ≫ d.z
  hz := by
    rw [← Category.assoc, cutHom_comm_d, Category.assoc, d.hz, comp_zero]
  w := cutHom Γ6 RationalGL3 Flag (flagLineOf ⁻¹' S)
    (preimage_invariant flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant S hS) 1 ≫ d.w
  hw := by
    rw [← Category.assoc, cutHom_comm_d, Category.assoc, d.hw, ← Category.assoc, ← Category.assoc]
    congr 1
    exact cutHom_natural flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant S hS 2

/-- The cut of a plane datum to the planes of `S`. -/
def PlaneDatum.cut (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S) (d : PlaneDatum W) :
    PlaneDatum W where
  z := cutHom Γ6 RationalGL3 Plane S hS 2 ≫ d.z
  hz := by
    rw [← Category.assoc, cutHom_comm_d, Category.assoc, d.hz, comp_zero]
  w := cutHom Γ6 RationalGL3 Flag (flagPlaneOf ⁻¹' S)
    (preimage_invariant flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant S hS) 1 ≫ d.w
  hw := by
    rw [← Category.assoc, cutHom_comm_d, Category.assoc, d.hw, ← Category.assoc, ← Category.assoc]
    congr 1
    exact cutHom_natural flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant S hS 2

end Cells


section Partition

variable {ι : Type} [Fintype ι]

open Classical in
/-- The cuts along the cells of a partition of the label set add up to the identity. -/
theorem cutHom_sum {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z]
    (S : ι → Set Z) (hS : ∀ (i : ι) (γ : Γ) (z : Z), γ • z ∈ S i ↔ z ∈ S i)
    (hpart : ∀ z : Z, ∃! i, z ∈ S i) (k : ℕ) :
    (∑ i, cutHom Γ V Z (S i) (hS i) k : (prodComplex Γ V Z).X k ⟶ (prodComplex Γ V Z).X k) = 𝟙 _ := by
  refine hom_ext_single ((Fin (k + 1) → V) × Z) _ (fun s => ?_)
  obtain ⟨i₀, hi₀, huniq⟩ := hpart s.2
  change (Rep.Hom.hom (∑ i, cutHom Γ V Z (S i) (hS i) k : (prodComplex Γ V Z).X k ⟶ (prodComplex Γ V Z).X k))
    (MonoidAlgebra.single s 1) = MonoidAlgebra.single s 1
  erw [Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
  rw [Finset.sum_eq_single i₀]
  · erw [cutHom_single, ite_eq_left hi₀]
    rfl
  · intro j _ hj
    erw [cutHom_single, ite_eq_right (fun hh => hj (huniq j hh))]
    rfl
  · intro h
    exact absurd (Finset.mem_univ i₀) h

end Partition


section Sums

variable {W W' : Rep.{0} ℚ Γ6} {ι : Type}

theorem lineCone_zero :
    lineCone (0 : A.X 1 ⟶ W) (0 : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W) = 0 := by
  unfold lineCone
  rw [show ((0 : A.X 1 ⟶ W), (0 : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W),
    (0 : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W)) = 0 from rfl, map_zero]

theorem planeCone_zero :
    planeCone (0 : A.X 1 ⟶ W) (0 : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) = 0 := by
  unfold planeCone
  rw [show (-(0 : A.X 1 ⟶ W), (0 : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W),
    (0 : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W)) = 0 from by
      refine Prod.ext (neg_zero) rfl, map_zero]

theorem lineCone_sum (s : Finset ι) (w : ι → (A.X 1 ⟶ W))
    (z : ι → ((prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W)) :
    lineCone (∑ i ∈ s, w i) (∑ i ∈ s, z i) = ∑ i ∈ s, lineCone (w i) (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lineCone_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, lineCone_add, ih]

theorem planeCone_sum (s : Finset ι) (w : ι → (A.X 1 ⟶ W))
    (z : ι → ((prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W)) :
    planeCone (∑ i ∈ s, w i) (∑ i ∈ s, z i) = ∑ i ∈ s, planeCone (w i) (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using planeCone_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, planeCone_add, ih]

variable (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (v : coneR.X 4)

theorem conePair_zero_left (Y : coneR.X 2 ⟶ W') : conePair π v 0 Y = 0 := by
  unfold conePair
  rw [PushCone.zero_tensorHom', zero_comp, comp_zero]
  rfl

theorem conePair_zero_right (X : coneR.X 2 ⟶ W) : conePair π v X 0 = 0 := by
  unfold conePair
  rw [PushCone.tensorHom_zero', zero_comp, comp_zero]
  rfl

end Sums


section Decomp

variable {W W' : Rep.{0} ℚ Γ6} {ι : Type} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (v : coneR.X 4)

theorem conePair_sum_left (s : Finset ι) (X : ι → (coneR.X 2 ⟶ W)) (Y : coneR.X 2 ⟶ W') :
    conePair π v (∑ i ∈ s, X i) Y = ∑ i ∈ s, conePair π v (X i) Y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using conePair_zero_left π v Y
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, conePair_add_left, ih]

theorem conePair_sum_right (s : Finset ι) (X : coneR.X 2 ⟶ W) (Y : ι → (coneR.X 2 ⟶ W')) :
    conePair π v X (∑ i ∈ s, Y i) = ∑ i ∈ s, conePair π v X (Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using conePair_zero_right π v X
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, conePair_add_right, ih]

open Classical in
theorem LineDatum.cut_z_single (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S)
    (d : LineDatum W) (u : Fin 3 → RationalGL3) (ℓ : Line) :
    (d.cut S hS).z.hom (MonoidAlgebra.single (u, ℓ) 1) =
      if ℓ ∈ S then d.z.hom (MonoidAlgebra.single (u, ℓ) 1) else 0 := by
  change d.z.hom ((cutHom Γ6 RationalGL3 Line S hS 2).hom (MonoidAlgebra.single (u, ℓ) 1)) = _
  erw [cutHom_single]
  by_cases h : ℓ ∈ S
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    exact map_zero _

open Classical in
theorem LineDatum.cut_w_single (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S)
    (d : LineDatum W) (u : Fin 2 → RationalGL3) (F : Flag) :
    (d.cut S hS).w.hom (MonoidAlgebra.single (u, F) 1) =
      if flagLineOf F ∈ S then d.w.hom (MonoidAlgebra.single (u, F) 1) else 0 := by
  change d.w.hom ((cutHom Γ6 RationalGL3 Flag (flagLineOf ⁻¹' S) _ 1).hom (MonoidAlgebra.single (u, F) 1)) = _
  erw [cutHom_single]
  by_cases h : flagLineOf F ∈ S
  · rw [ite_eq_left (show F ∈ flagLineOf ⁻¹' S from h), ite_eq_left h]
  · rw [ite_eq_right (show F ∉ flagLineOf ⁻¹' S from h), ite_eq_right h]
    exact map_zero _

variable [Fintype ι]

theorem LineDatum.cone_eq_sum (S : ι → Set Line) (hS : ∀ (i : ι) (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S i ↔ ℓ ∈ S i)
    (hpart : ∀ ℓ : Line, ∃! i, ℓ ∈ S i) (d : LineDatum W) :
    d.cone = ∑ i, (d.cut (S i) (hS i)).cone := by
  have hF := cutHom_sum (Γ := Γ6) (V := RationalGL3) (Z := Flag) (fun i => flagLineOf ⁻¹' S i)
    (fun i => preimage_invariant flagLineOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant (S i) (hS i))
    (fun F => hpart (flagLineOf F)) 1
  have hL := cutHom_sum (Γ := Γ6) (V := RationalGL3) (Z := Line) S hS hpart 2
  unfold LineDatum.cone
  simp only [LineDatum.cut]
  rw [← lineCone_sum, ← Preadditive.sum_comp, ← Preadditive.sum_comp, hF, hL, Category.id_comp, Category.id_comp]


theorem LineDatum.pair_cut_orth (S₁ S₂ : Set Line) (h1 : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S₁ ↔ ℓ ∈ S₁)
    (h2 : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S₂ ↔ ℓ ∈ S₂) (hdisj : Disjoint S₁ S₂) (d : LineDatum W)
    (e : LineDatum W') :
    conePair π v (d.cut S₁ h1).cone (e.cut S₂ h2).cone = 0 := by
  classical
  refine conePair_lineCone_orth π v S₁ _ _ _ _ (fun u ℓ hℓ => ?_) (fun u ℓ hℓ => ?_) (fun u F hF => ?_)
  · rw [LineDatum.cut_z_single, ite_eq_right hℓ]
  · rw [LineDatum.cut_z_single, ite_eq_right (Set.disjoint_left.mp hdisj hℓ)]
  · rw [LineDatum.cut_w_single, ite_eq_right hF]

theorem LineDatum.pair_eq_sum (S : ι → Set Line) (hS : ∀ (i : ι) (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S i ↔ ℓ ∈ S i)
    (hpart : ∀ ℓ : Line, ∃! i, ℓ ∈ S i) (d : LineDatum W) (e : LineDatum W') :
    conePair π v d.cone e.cone =
      ∑ i, conePair π v (d.cut (S i) (hS i)).cone (e.cut (S i) (hS i)).cone := by
  classical
  rw [LineDatum.cone_eq_sum S hS hpart d, LineDatum.cone_eq_sum S hS hpart e, conePair_sum_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [conePair_sum_right, Finset.sum_eq_single i]
  · intro j _ hji
    exact LineDatum.pair_cut_orth π v (S i) (S j) (hS i) (hS j)
      (Set.disjoint_left.2 (fun ℓ hi hj => hji ((hpart ℓ).unique hj hi))) d e
  · intro h
    exact absurd (Finset.mem_univ i) h

open Classical in
theorem PlaneDatum.cut_z_single (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S)
    (d : PlaneDatum W) (u : Fin 3 → RationalGL3) (P : Plane) :
    (d.cut S hS).z.hom (MonoidAlgebra.single (u, P) 1) =
      if P ∈ S then d.z.hom (MonoidAlgebra.single (u, P) 1) else 0 := by
  change d.z.hom ((cutHom Γ6 RationalGL3 Plane S hS 2).hom (MonoidAlgebra.single (u, P) 1)) = _
  erw [cutHom_single]
  by_cases h : P ∈ S
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    exact map_zero _

open Classical in
theorem PlaneDatum.cut_w_single (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S)
    (d : PlaneDatum W) (u : Fin 2 → RationalGL3) (F : Flag) :
    (d.cut S hS).w.hom (MonoidAlgebra.single (u, F) 1) =
      if flagPlaneOf F ∈ S then d.w.hom (MonoidAlgebra.single (u, F) 1) else 0 := by
  change d.w.hom ((cutHom Γ6 RationalGL3 Flag (flagPlaneOf ⁻¹' S) _ 1).hom (MonoidAlgebra.single (u, F) 1)) = _
  erw [cutHom_single]
  by_cases h : flagPlaneOf F ∈ S
  · rw [ite_eq_left (show F ∈ flagPlaneOf ⁻¹' S from h), ite_eq_left h]
  · rw [ite_eq_right (show F ∉ flagPlaneOf ⁻¹' S from h), ite_eq_right h]
    exact map_zero _

theorem PlaneDatum.cone_eq_sum (S : ι → Set Plane) (hS : ∀ (i : ι) (γ : Γ6) (P : Plane), γ • P ∈ S i ↔ P ∈ S i)
    (hpart : ∀ P : Plane, ∃! i, P ∈ S i) (d : PlaneDatum W) :
    d.cone = ∑ i, (d.cut (S i) (hS i)).cone := by
  have hF := cutHom_sum (Γ := Γ6) (V := RationalGL3) (Z := Flag) (fun i => flagPlaneOf ⁻¹' S i)
    (fun i => preimage_invariant flagPlaneOf
      TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant (S i) (hS i))
    (fun F => hpart (flagPlaneOf F)) 1
  have hL := cutHom_sum (Γ := Γ6) (V := RationalGL3) (Z := Plane) S hS hpart 2
  unfold PlaneDatum.cone
  simp only [PlaneDatum.cut]
  rw [← planeCone_sum, ← Preadditive.sum_comp, ← Preadditive.sum_comp, hF, hL, Category.id_comp, Category.id_comp]

theorem PlaneDatum.pair_cut_orth (S₁ S₂ : Set Plane) (h1 : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S₁ ↔ P ∈ S₁)
    (h2 : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S₂ ↔ P ∈ S₂) (hdisj : Disjoint S₁ S₂) (d : PlaneDatum W)
    (e : PlaneDatum W') :
    conePair π v (d.cut S₁ h1).cone (e.cut S₂ h2).cone = 0 := by
  classical
  refine conePair_planeCone_orth π v S₁ _ _ _ _ (fun u P hP => ?_) (fun u P hP => ?_) (fun u F hF => ?_)
  · rw [PlaneDatum.cut_z_single, ite_eq_right hP]
  · rw [PlaneDatum.cut_z_single, ite_eq_right (Set.disjoint_left.mp hdisj hP)]
  · rw [PlaneDatum.cut_w_single, ite_eq_right (Set.disjoint_left.mp hdisj hF)]

theorem PlaneDatum.pair_eq_sum (S : ι → Set Plane) (hS : ∀ (i : ι) (γ : Γ6) (P : Plane), γ • P ∈ S i ↔ P ∈ S i)
    (hpart : ∀ P : Plane, ∃! i, P ∈ S i) (d : PlaneDatum W) (e : PlaneDatum W') :
    conePair π v d.cone e.cone =
      ∑ i, conePair π v (d.cut (S i) (hS i)).cone (e.cut (S i) (hS i)).cone := by
  classical
  rw [PlaneDatum.cone_eq_sum S hS hpart d, PlaneDatum.cone_eq_sum S hS hpart e, conePair_sum_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [conePair_sum_right, Finset.sum_eq_single i]
  · intro j _ hji
    exact PlaneDatum.pair_cut_orth π v (S i) (S j) (hS i) (hS j)
      (Set.disjoint_left.2 (fun P hi hj => hji ((hpart P).unique hj hi))) d e
  · intro h
    exact absurd (Finset.mem_univ i) h

end Decomp

end TernaryPeriodPolynomials.Argument.GammaNStokes
