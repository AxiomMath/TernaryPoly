module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Stokes
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.GeoFace

@[expose] public section


/-!
# Lemma `ar:lem:stokes` at level `Γ(6)`, in cone form, for every coefficient system

Formalized by Claude Sonnet 5.5.

Everything here is generic in the coefficient system `V : Rep ℚ Γ(6)` (no `E_n`, no duality data, no level group `K†`, no model face pairings):

* `lineCone w z = (w, z, 0)`, `planeCone w z = (-w, 0, z)`: the cone cochains of a line (plane) cochain `z` with flag primitive `w`; cocycle criteria
  `lineCone_cocycle`, `planeCone_cocycle`;
* `conePair π v X Y = π ∘ (X ⊗ Y) ∘ Δ_{2,2}(v)`, the cone pairing of two degree-two cone cochains on a chain `v` of the model cone;
* `cone_cross_zero`: a cone cocycle without line component is orthogonal to a cone cocycle without plane component (the two corner terms of
  `PushCone.pair_cycle` are minus the coboundary of `X_A ⌣ Y_A`; this is the cochain form of the vanishing of corner contributions);
  `conePair_linePlane_zero`: line-type against plane-type;
* `exists_stokes_cycle`: **geometric Stokes**, for a suitable coinvariant cycle `Ω` of the model cone, the cone pairing of the restrictions
  `coneToPt^* f`, `coneToPt^* f'` of two global cocycles of `Γ(6)` (coefficients `V`, `V^*`) vanishes (from `facePairing_comparison`, the canonical
  identification of `Ψ` and `geoPairingBoundary_restriction`, for every rational representation `V`);
* `coneToPt_eq_lift`: the restriction of a global cocycle is the sum of its line lift and its plane lift;
* **`cone_stokes`**: for global cocycles with edge-exact (zero flag) restrictions the cone pairing of the line lifts plus that of the plane lifts is `0`.
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

abbrev SA : DiagSystem (prodComplex Γ6 RationalGL3 Flag) := nerveDiagSystem Γ6 RationalGL3 Flag
abbrev A : ChainComplex (Rep.{0} ℚ Γ6) ℕ := prodComplex Γ6 RationalGL3 Flag

theorem neg_tensorHom' {W X Y Z : Rep.{0} ℚ Γ6} (f : W ⟶ X) (g : Y ⟶ Z) : (-f) ⊗ₘ g = -(f ⊗ₘ g) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← MonoidalPreadditive.add_tensor, neg_add_cancel, MonoidalPreadditive.zero_tensor]

theorem aux_neg {M : Type*} [AddCommGroup M] {X Y : M} (h : 0 = -X + 0 - Y) : X = -Y := by
  have h3 : X + Y = 0 := by
    calc X + Y = -(-X + 0 - Y) := by abel
      _ = 0 := by rw [← h, neg_zero]
  exact eq_neg_of_add_eq_zero_left h3

theorem aux_pos {M : Type*} [AddCommGroup M] {X Y : M} (h : 0 = -X + Y - 0) : X = Y := by
  have h3 : X - Y = 0 := by
    calc X - Y = -(-X + Y - 0) := by abel
      _ = 0 := by rw [← h, neg_zero]
  exact sub_eq_zero.mp h3


/-- **Orthogonality of a cone cocycle without line component to a cone cocycle without plane component.** The cone pairing of two
degree-two cone cocycles `bt`, `at'` with `iL ≫ bt = 0` and `iP ≫ at' = 0` vanishes on every coinvariant cycle of the model cone: by
`PushCone.pair_cycle` it reduces to the two corner terms, which are minus the coboundary of `bt_A ⌣ at'_A` on the flag resolution. -/
theorem cone_cross_zero {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (bt : coneR.X 2 ⟶ W) (at' : coneR.X 2 ⟶ W')
    (hbt : coneR.d 3 2 ≫ bt = 0) (hat : coneR.d 3 2 ≫ at' = 0)
    (hbL : modelPush.iL 2 ≫ bt = 0) (hatP : modelPush.iP 2 ≫ at' = 0)
    (v : coneR.X 4) (hv : IsCoinvCycle v) :
    ((modelDiagSystem.Δ 2 2 4 rfl) ≫ (bt ⊗ₘ at') ≫ π).hom v = 0 := by
  have hL : (resLine.complex).d 4 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫
        ((modelPush.iL 2 ≫ bt) ⊗ₘ (modelPush.iL 2 ≫ at')) ≫ π := by
    rw [hbL, PushCone.zero_tensorHom', zero_comp, comp_zero]
    simp
  have hP : (resPlane.complex).d 4 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫
        ((modelPush.iP 2 ≫ bt) ⊗ₘ (modelPush.iP 2 ≫ at')) ≫ π := by
    rw [hatP, PushCone.tensorHom_zero', zero_comp, comp_zero]
    simp
  have key := modelPush.pair_cycle SA (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) bt at' π v hv 0 0 hL hP
  refine Eq.trans key ?_
  have hdb : modelPush.iA 2 ≫ coneR.d 3 2 ≫ bt = 0 := by rw [hbt, comp_zero]
  have hda : modelPush.iA 2 ≫ coneR.d 3 2 ≫ at' = 0 := by rw [hat, comp_zero]
  have hrb : A.d 2 1 ≫ modelPush.iA 1 ≫ bt = -(flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ bt) := by
    have h := modelPush.dA 1
    have h2 := congrArg (fun m => m ≫ bt) h
    simp only [Category.assoc, Preadditive.add_comp, Preadditive.sub_comp, Preadditive.neg_comp] at h2
    rw [hbt, comp_zero, hbL, comp_zero] at h2
    exact aux_neg h2
  have hra : A.d 2 1 ≫ modelPush.iA 1 ≫ at' = flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ at' := by
    have h := modelPush.dA 1
    have h2 := congrArg (fun m => m ≫ at') h
    simp only [Category.assoc, Preadditive.add_comp, Preadditive.sub_comp, Preadditive.neg_comp] at h2
    rw [hat, comp_zero, hatP, comp_zero] at h2
    exact aux_pos h2
  have hleib := SA.leibniz 1 1 2 rfl
  have hθ : A.d 3 2 ≫ (SA.Δ 1 1 2 rfl ≫ ((modelPush.iA 1 ≫ bt) ⊗ₘ (modelPush.iA 1 ≫ at')) ≫ π) =
      -(SA.Δ 1 2 3 rfl ≫ ((modelPush.iA 1 ≫ bt) ⊗ₘ (flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ at')) ≫ π +
        SA.Δ 2 1 3 rfl ≫ ((flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ bt) ⊗ₘ (modelPush.iA 1 ≫ at')) ≫ π) := by
    rw [← Category.assoc, hleib]
    simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]
    rw [← tensorHom_id, ← id_tensorHom]
    rw [← Category.assoc (A.d (1 + 1) 1 ⊗ₘ 𝟙 (A.X 1)), tensorHom_comp_tensorHom,
      ← Category.assoc (𝟙 (A.X 1) ⊗ₘ A.d (1 + 1) 1), tensorHom_comp_tensorHom]
    rw [Category.id_comp]
    have hrb' : A.d (1 + 1) 1 ≫ modelPush.iA 1 ≫ bt = -(flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ bt) := hrb
    have hra' : A.d (1 + 1) 1 ≫ modelPush.iA 1 ≫ at' = flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ at' := hra
    rw [hrb', hra', neg_tensorHom']
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, Int.reducePow, neg_smul, one_smul, Category.id_comp, Nat.reduceAdd]
    abel
  set θ0 := SA.Δ 1 1 2 rfl ≫ ((modelPush.iA 1 ≫ bt) ⊗ₘ (modelPush.iA 1 ≫ at')) ≫ π with hθ0
  have hsum : (SA.Δ 1 2 3 rfl ≫ ((modelPush.iA 1 ≫ bt) ⊗ₘ (flagLineHom.hom.f 2 ≫ modelPush.iL 2 ≫ at')) ≫ π +
        SA.Δ 2 1 3 rfl ≫ ((flagPlaneHom.hom.f 2 ≫ modelPush.iP 2 ≫ bt) ⊗ₘ (modelPush.iA 1 ≫ at')) ≫ π) =
      -(A.d 3 2 ≫ θ0) := by
    rw [hθ, neg_neg]
  rw [comp_zero, comp_zero, sub_zero, add_zero, hsum]
  have hcyc := hv (modelPush.pA 2 ≫ θ0)
  have hpd := modelPush.pA_d 2 v
  have e1 : (modelPush.pA 2 ≫ θ0).hom ((coneR.d 4 3).hom v) = θ0.hom ((modelPush.pA 2).hom ((coneR.d 4 3).hom v)) := rfl
  rw [e1] at hcyc
  have hpd' : (modelPush.pA 2).hom ((coneR.d 4 3).hom v) = -(A.d 3 2).hom ((modelPush.pA 3).hom v) := hpd
  rw [hpd', map_neg, neg_eq_zero] at hcyc
  have e2 : (Rep.Hom.hom (-(A.d 3 2 ≫ θ0))) ((Rep.Hom.hom (modelPush.pA 3)) v) =
      -θ0.hom ((A.d 3 2).hom ((modelPush.pA 3).hom v)) := rfl
  rw [e2, hcyc, neg_zero]

section Lifts

variable {W : Rep.{0} ℚ Γ6}

/-- The cone cochain `(w, z, 0)` of a line cochain `z` with a flag primitive `w`. -/
def lineCone (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W) : coneR.X 2 ⟶ W :=
  (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1).symm (w, z, 0)

/-- The cone cochain `(-w, 0, z)` of a plane cochain `z` with a flag primitive `w`. -/
def planeCone (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) : coneR.X 2 ⟶ W :=
  (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1).symm (-w, 0, z)

theorem coneCoords (c : coneR.X 2 ⟶ W) :
    signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1 c =
      (modelPush.iA 1 ≫ c, modelPush.iL 2 ≫ c, modelPush.iP 2 ≫ c) :=
  signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom W 1 c

theorem lineCone_corner (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W) :
    modelPush.iA 1 ≫ lineCone w z = w := by
  have h := coneCoords (lineCone w z)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1 (lineCone w z) = (w, z, 0) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg Prod.fst h).symm

theorem lineCone_line (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W) :
    modelPush.iL 2 ≫ lineCone w z = z := by
  have h := coneCoords (lineCone w z)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1 (lineCone w z) = (w, z, 0) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun p => p.2.1) h).symm

theorem lineCone_plane (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W) :
    modelPush.iP 2 ≫ lineCone w z = 0 := by
  have h := coneCoords (lineCone w z)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1 (lineCone w z) = (w, z, 0) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun p => p.2.2) h).symm

theorem planeCone_corner (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) :
    modelPush.iA 1 ≫ planeCone w z = -w := by
  have h := coneCoords (planeCone w z)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1 (planeCone w z) = (-w, 0, z) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg Prod.fst h).symm

theorem planeCone_line (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) :
    modelPush.iL 2 ≫ planeCone w z = 0 := by
  have h := coneCoords (planeCone w z)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1 (planeCone w z) = (-w, 0, z) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun p => p.2.1) h).symm

theorem planeCone_plane (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) :
    modelPush.iP 2 ≫ planeCone w z = z := by
  have h := coneCoords (planeCone w z)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1 (planeCone w z) = (-w, 0, z) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun p => p.2.2) h).symm

theorem lineCone_cocycle (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W)
    (hz : (prodComplex Γ6 RationalGL3 Line).d 3 2 ≫ z = 0)
    (hw : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ z) : coneR.d 3 2 ≫ lineCone w z = 0 := by
  apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 2).injective
  rw [cone_coboundary_coordinates]
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1 (lineCone w z) = (w, z, 0) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change -(A.d 2 1 ≫ w) + flagLineHom.hom.f 2 ≫ z -
      flagPlaneHom.hom.f 2 ≫ (0 : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) = 0
    rw [hw, comp_zero]
    abel
  · exact hz
  · exact comp_zero

theorem planeCone_cocycle (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W)
    (hz : (prodComplex Γ6 RationalGL3 Plane).d 3 2 ≫ z = 0)
    (hw : A.d 2 1 ≫ w = flagPlaneHom.hom.f 2 ≫ z) : coneR.d 3 2 ≫ planeCone w z = 0 := by
  apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 2).injective
  rw [cone_coboundary_coordinates]
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W 1 (planeCone w z) = (-w, 0, z) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change -(A.d 2 1 ≫ (-w)) + flagLineHom.hom.f 2 ≫ (0 : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W) -
      flagPlaneHom.hom.f 2 ≫ z = 0
    rw [Preadditive.comp_neg, hw, comp_zero]
    abel
  · exact comp_zero
  · exact hz

end Lifts

section Pairing

/-- The cone pairing of two degree-two cone cochains on a chain `v` of the model cone: `π ∘ (X ⊗ Y) ∘ Δ_{2,2}`. -/
def conePair {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (v : coneR.X 4)
    (X : coneR.X 2 ⟶ W) (Y : coneR.X 2 ⟶ W') : (𝟙_ (Rep.{0} ℚ Γ6) : Type) :=
  ((modelDiagSystem.Δ 2 2 4 rfl) ≫ (X ⊗ₘ Y) ≫ π).hom v

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (v : coneR.X 4)

theorem conePair_add_left (X X' : coneR.X 2 ⟶ W) (Y : coneR.X 2 ⟶ W') :
    conePair π v (X + X') Y = conePair π v X Y + conePair π v X' Y := by
  unfold conePair
  rw [MonoidalPreadditive.add_tensor, Preadditive.add_comp, Preadditive.comp_add]
  rfl

theorem conePair_add_right (X : coneR.X 2 ⟶ W) (Y Y' : coneR.X 2 ⟶ W') :
    conePair π v X (Y + Y') = conePair π v X Y + conePair π v X Y' := by
  unfold conePair
  rw [MonoidalPreadditive.tensor_add, Preadditive.add_comp, Preadditive.comp_add]
  rfl

/-- **Orthogonality of line-type and plane-type cone cochains** (line-type `X`, i.e. no plane component, against plane-type `Y`): all four
terms of `PushCone.pair_cycle` vanish. -/
theorem conePair_linePlane_zero (X : coneR.X 2 ⟶ W) (Y : coneR.X 2 ⟶ W')
    (hX : modelPush.iP 2 ≫ X = 0) (hY : modelPush.iL 2 ≫ Y = 0) (hv : IsCoinvCycle v) :
    conePair π v X Y = 0 := by
  have hL : (resLine.complex).d 4 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫
        ((modelPush.iL 2 ≫ X) ⊗ₘ (modelPush.iL 2 ≫ Y)) ≫ π := by
    rw [hY, PushCone.tensorHom_zero', zero_comp, comp_zero]
    simp
  have hP : (resPlane.complex).d 4 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫
        ((modelPush.iP 2 ≫ X) ⊗ₘ (modelPush.iP 2 ≫ Y)) ≫ π := by
    rw [hX, PushCone.zero_tensorHom', zero_comp, comp_zero]
    simp
  have key := modelPush.pair_cycle SA (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) X Y π v hv 0 0 hL hP
  unfold conePair
  refine Eq.trans key ?_
  rw [hY, hX]
  simp [PushCone.tensorHom_zero', PushCone.zero_tensorHom']

end Pairing

section Stokes

open TernaryPoly.SingularLocalDuality (dualRepresentation)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

/-- **Geometric Stokes in cone form, for every coefficient system of `Γ(6)`.**  There is a coinvariant cycle `Ω` of the model cone such that
the cone pairing of the restrictions `coneToPt^* f`, `coneToPt^* f'` of two global degree-two cocycles of `Γ(6)` with coefficients `V`, `V^*`
vanishes. -/
theorem exists_stokes_cycle : ∃ Ω : coneR.X 4, IsCoinvCycle Ω ∧
    ∀ {V : Rep.{0} ℚ Γ6} (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ V)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
      (f' : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ dualRepresentation V)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f' = 0),
      conePair (evalRep V) Ω (coneToPt.f 2 ≫ f) (coneToPt.f 2 ≫ f') = 0 := by
  obtain ⟨Ω, Ψ, κ, c₀, hcyc, hcar, hq, haug, hκ, hc₀, pairGeo, htr⟩ := exists_pairGeo
  refine ⟨Ω, hcyc, fun {V} f hf f' hf' => ?_⟩
  have hB : coneR.d 3 2 ≫ coneToPt.f 2 ≫ f = 0 := by
    rw [← Category.assoc, ← coneToPt.comm 3 2, Category.assoc, hf, comp_zero]
  have hA : coneR.d 3 2 ≫ coneToPt.f 2 ≫ f' = 0 := by
    rw [← Category.assoc, ← coneToPt.comm 3 2, Category.assoc, hf', comp_zero]
  obtain ⟨β, hβ, hPB⟩ := exists_pullsBackTo hq _ hB
  obtain ⟨α, hα, hPA⟩ := exists_pullsBackTo hq _ hA
  have hpair := pairGeo _ _ β hβ α hα hA hPB hPA
  obtain ⟨η, hη⟩ := hPB
  obtain ⟨η', hη'⟩ := hPA
  have hβcls := cochainClass_eq_restrictedClass hq haug f hf β hβ η hη
  have hαcls := cochainClass_eq_restrictedClass hq haug f' hf' α hα η' hη'
  have hgeo : geoOf V α hα β hβ = 0 := by
    unfold geoOf
    rw [hβcls, hαcls]
    exact geoPairing_restrictedClass_zero V _ _
  have h0 : conePair (evalRep V) Ω (coneToPt.f 2 ≫ f) (coneToPt.f 2 ≫ f') = κ * geoOf V α hα β hβ := hpair
  rw [h0, hgeo, mul_zero]

variable {V : Rep.{0} ℚ Γ6}

theorem plane_edge_of_line_edge (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ V) (w : A.X 1 ⟶ V)
    (hw : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f) :
    A.d 2 1 ≫ w = flagPlaneHom.hom.f 2 ≫ (ptMap Plane).f 2 ≫ f := by
  have h := congrArg (fun m => m.f 2 ≫ f) line_plane_ptMap
  simp only [HomologicalComplex.comp_f, Category.assoc] at h
  rw [hw]
  exact h

/-- **A global cocycle with edge-exact face restrictions is the sum of its line lift and its plane lift** (zero corner component):
`coneToPt^* f = (w, f_L, 0) + (-w, 0, f_P)`. -/
theorem coneToPt_eq_lift (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ V) (w : A.X 1 ⟶ V) :
    coneToPt.f 2 ≫ f = lineCone w ((ptMap Line).f 2 ≫ f) + planeCone w ((ptMap Plane).f 2 ≫ f) := by
  apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom V 1).injective
  rw [coneCoords, map_add, coneCoords, coneCoords]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change modelPush.iA 1 ≫ coneToPt.f 2 ≫ f = modelPush.iA 1 ≫ lineCone w _ + modelPush.iA 1 ≫ planeCone w _
    rw [coneToPt_corner, lineCone_corner, planeCone_corner]
    abel
  · change modelPush.iL 2 ≫ coneToPt.f 2 ≫ f = modelPush.iL 2 ≫ lineCone w _ + modelPush.iL 2 ≫ planeCone w _
    rw [← Category.assoc, coneToPt_line, lineCone_line, planeCone_line, add_zero]
  · change modelPush.iP 2 ≫ coneToPt.f 2 ≫ f = modelPush.iP 2 ≫ lineCone w _ + modelPush.iP 2 ≫ planeCone w _
    rw [← Category.assoc, coneToPt_plane, lineCone_plane, planeCone_plane, zero_add]

/-- **Lemma `ar:lem:stokes` at level `Γ(6)`, in cone form, for every coefficient system `V`.**  For global cocycles `f` (coefficients `V`) and
`f'` (coefficients `V^*`) of `Γ(6)` whose restrictions to the complete flags are the coboundaries of `w`, `w'`, the cone pairing of the line lifts
`(w, f_L, 0)`, `(w', f'_L, 0)` plus that of the plane lifts `(-w, 0, f_P)`, `(-w', 0, f'_P)` vanishes (the cross terms vanish). -/
theorem cone_stokes : ∃ Ω : coneR.X 4, IsCoinvCycle Ω ∧
    ∀ {V : Rep.{0} ℚ Γ6} (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ V)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
      (f' : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ dualRepresentation V)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f' = 0)
      (w : A.X 1 ⟶ V) (_ : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f)
      (w' : A.X 1 ⟶ dualRepresentation V) (_ : A.d 2 1 ≫ w' = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f'),
      conePair (evalRep V) Ω (lineCone w ((ptMap Line).f 2 ≫ f)) (lineCone w' ((ptMap Line).f 2 ≫ f')) +
        conePair (evalRep V) Ω (planeCone w ((ptMap Plane).f 2 ≫ f))
          (planeCone w' ((ptMap Plane).f 2 ≫ f')) = 0 := by
  obtain ⟨Ω, hΩ, H⟩ := exists_stokes_cycle
  refine ⟨Ω, hΩ, fun {V} f hf f' hf' w hw w' hw' => ?_⟩
  have h0 := H f hf f' hf'
  rw [coneToPt_eq_lift f w, coneToPt_eq_lift f' w', conePair_add_left, conePair_add_right,
    conePair_add_right] at h0
  have hLP : conePair (evalRep V) Ω (lineCone w ((ptMap Line).f 2 ≫ f))
      (planeCone w' ((ptMap Plane).f 2 ≫ f')) = 0 :=
    conePair_linePlane_zero _ _ _ _ (lineCone_plane _ _) (planeCone_line _ _) hΩ
  have hf1 : (prodComplex Γ6 RationalGL3 Line).d 3 2 ≫ (ptMap Line).f 2 ≫ f = 0 := by
    rw [← Category.assoc, ← (ptMap Line).comm 3 2, Category.assoc, hf, comp_zero]
  have hf2 : (prodComplex Γ6 RationalGL3 Plane).d 3 2 ≫ (ptMap Plane).f 2 ≫ f = 0 := by
    rw [← Category.assoc, ← (ptMap Plane).comm 3 2, Category.assoc, hf, comp_zero]
  have hf1' : (prodComplex Γ6 RationalGL3 Line).d 3 2 ≫ (ptMap Line).f 2 ≫ f' = 0 := by
    rw [← Category.assoc, ← (ptMap Line).comm 3 2, Category.assoc, hf', comp_zero]
  have hf2' : (prodComplex Γ6 RationalGL3 Plane).d 3 2 ≫ (ptMap Plane).f 2 ≫ f' = 0 := by
    rw [← Category.assoc, ← (ptMap Plane).comm 3 2, Category.assoc, hf', comp_zero]
  have hPL : conePair (evalRep V) Ω (planeCone w ((ptMap Plane).f 2 ≫ f))
      (lineCone w' ((ptMap Line).f 2 ≫ f')) = 0 :=
    cone_cross_zero _ _ _
      (planeCone_cocycle _ _ hf2 (plane_edge_of_line_edge f w hw))
      (lineCone_cocycle _ _ hf1' hw')
      (planeCone_line _ _) (lineCone_plane _ _) Ω hΩ
  rw [hLP, hPL] at h0
  simpa using h0

end Stokes

end TernaryPeriodPolynomials.Argument.GammaNStokes
