module

public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalAction
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallCochains

@[expose] public section



/-!
# Twisting by conjugation, and the conjugation action on Hom cochains

For a normal subgroup `H ≤ G` and `k ∈ G`, restriction along `h ↦ k⁻¹ h k` twists an `H`-representation
(`twistRep`, `twistC` for complexes). A compatible `G`-action (`GAct`, `GActC`) makes the action of `k` a
morphism from the twist (`actRep`, `actC`). For `ψ : twist_k X ⟶ W` the reindexing `ρ_W(k)⁻¹ ∘ ψ` is
`H`-equivariant on `X` (`sigmaHom`, an isomorphism of Hom cochain complexes `sigmaIso`).
`homPullback_actC_sigma`: pulling back along `actC` and reindexing is the conjugation action
`hcAct` of `k⁻¹`; `homPullback_eq_hcAct`: the same for any chain map of the form `Θ.hom ≫ actC A k` after
the reindexing `XiIso`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory

section Twist

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal]

/-- Conjugation `h ↦ k⁻¹ h k` of a normal subgroup. -/
def cjH (k : G) : ↥H →* ↥H := (MulAut.conjNormal (H := H) k⁻¹).toMonoidHom

variable {H}

@[simp] theorem cjH_val (k : G) (h : ↥H) : (cjH H k h).1 = k⁻¹ * h.1 * k := by simp [cjH]

theorem conjElt_cjH (k : G) (h : ↥H) : conjElt H k (cjH H k h) = h :=
  Subtype.ext (by simp [mul_assoc])

theorem cjH_conjElt (k : G) (h : ↥H) : cjH H k (conjElt H k h) = h :=
  Subtype.ext (by simp [mul_assoc])

/-- An `H`-representation restricted along `h ↦ k⁻¹ h k`. -/
def twistRep (k : G) (X : Rep.{0} ℚ ↥H) : Rep.{0} ℚ ↥H := (Rep.resFunctor (cjH H k)).obj X

/-- The action of `k` is an `H`-map from the twisted representation. -/
def actRep {X : Rep.{0} ℚ ↥H} (A : GAct H X) (k : G) : twistRep k X ⟶ X :=
  Rep.ofHom ⟨A.ρ k, fun h => LinearMap.ext fun x => by
    change A.ρ k (X.ρ (cjH H k h) x) = X.ρ h (A.ρ k x)
    rw [A.conj, conjElt_cjH]⟩

/-- The twist of a complex of `H`-representations. -/
def twistC (k : G) (D : ChainComplex (Rep.{0} ℚ ↥H) ℕ) : ChainComplex (Rep.{0} ℚ ↥H) ℕ :=
  ((Rep.resFunctor (cjH H k)).mapHomologicalComplex (ComplexShape.down ℕ)).obj D

/-- The action of `k` as a chain map from the twisted complex. -/
def actC {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D) (k : G) : twistC k D ⟶ D where
  f n := actRep (A.act n) k
  comm' i j _ := by
    apply rep_hom_ext'
    intro x
    exact A.comm k i j x

variable {W : Rep.{0} ℚ ↥H}

/-- Reindexing of `H`-homomorphisms out of the twisted representation: `ψ ↦ ρ_W(k)⁻¹ ∘ ψ`. -/
def sigmaHom {X : Rep.{0} ℚ ↥H} (B : GAct H W) (k : G) (ψ : twistRep k X ⟶ W) : X ⟶ W :=
  Rep.ofHom ⟨(B.ρ k⁻¹).comp ψ.hom.toLinearMap, fun h => LinearMap.ext fun x => by
    have h2 : ψ.hom (X.ρ (cjH H k (conjElt H k h)) x) = W.ρ (conjElt H k h) (ψ.hom x) :=
      Rep.hom_comm_apply ψ (conjElt H k h) x
    rw [cjH_conjElt] at h2
    change B.ρ k⁻¹ (ψ.hom (X.ρ h x)) = W.ρ h (B.ρ k⁻¹ (ψ.hom x))
    rw [h2, B.conj]
    congr 2
    exact Subtype.ext (by simp [conjElt, mul_assoc])⟩

/-- The inverse reindexing `φ ↦ ρ_W(k) ∘ φ`. -/
def sigmaInv {X : Rep.{0} ℚ ↥H} (B : GAct H W) (k : G) (φ : X ⟶ W) : twistRep k X ⟶ W :=
  Rep.ofHom ⟨(B.ρ k).comp φ.hom.toLinearMap, fun h => LinearMap.ext fun x => by
    change B.ρ k (φ.hom (X.ρ (cjH H k h) x)) = W.ρ h (B.ρ k (φ.hom x))
    rw [Rep.hom_comm_apply φ, B.conj, conjElt_cjH]⟩

/-- `sigmaHom` as a linear map. -/
def sigmaL {X : Rep.{0} ℚ ↥H} (B : GAct H W) (k : G) : (twistRep k X ⟶ W) →ₗ[ℚ] (X ⟶ W) where
  toFun := sigmaHom B k
  map_add' ψ ψ' := by
    apply rep_hom_ext'
    intro x
    change B.ρ k⁻¹ (ψ.hom x + ψ'.hom x) = _
    rw [map_add]; rfl
  map_smul' c ψ := by
    apply rep_hom_ext'
    intro x
    change B.ρ k⁻¹ (c • ψ.hom x) = _
    rw [map_smul]; rfl

/-- `sigmaInv` as a linear map. -/
def sigmaInvL {X : Rep.{0} ℚ ↥H} (B : GAct H W) (k : G) : (X ⟶ W) →ₗ[ℚ] (twistRep k X ⟶ W) where
  toFun := sigmaInv B k
  map_add' φ φ' := by
    apply rep_hom_ext'
    intro x
    change B.ρ k (φ.hom x + φ'.hom x) = _
    rw [map_add]; rfl
  map_smul' c φ := by
    apply rep_hom_ext'
    intro x
    change B.ρ k (c • φ.hom x) = _
    rw [map_smul]; rfl

theorem sigmaHom_inv {X : Rep.{0} ℚ ↥H} (B : GAct H W) (k : G) (φ : X ⟶ W) :
    sigmaHom B k (sigmaInv B k φ) = φ := by
  apply rep_hom_ext'
  intro x
  change B.ρ k⁻¹ (B.ρ k (φ.hom x)) = φ.hom x
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem sigmaInv_hom {X : Rep.{0} ℚ ↥H} (B : GAct H W) (k : G) (ψ : twistRep k X ⟶ W) :
    sigmaInv B k (sigmaHom B k ψ) = ψ := by
  apply rep_hom_ext'
  intro x
  change B.ρ k (B.ρ k⁻¹ (ψ.hom x)) = ψ.hom x
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

/-- The reindexing of Hom cochains of the twisted complex, as a cochain isomorphism. -/
def sigmaIso {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (B : GAct H W) (k : G) :
    (twistC k D).linearYonedaObj ℚ W ≅ D.linearYonedaObj ℚ W :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => LinearEquiv.toModuleIso
      { sigmaL B k with
        invFun := sigmaInv B k
        left_inv := sigmaInv_hom B k
        right_inv := sigmaHom_inv B k })
    (fun i j _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ψ
      apply rep_hom_ext'
      intro x
      rfl)

/-- **Pullback along the action of `k` followed by the reindexing is the conjugation by `k⁻¹`.** -/
theorem homPullback_actC_sigma {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D) (B : GAct H W)
    (k : G) :
    TernaryPoly.EquivariantSingularSmall.homPullback (actC A k) W ≫ (sigmaIso (D := D) B k).hom =
      hcAct A B k⁻¹ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply rep_hom_ext'
  intro x
  change B.ρ k⁻¹ (φ.hom ((A.act n).ρ k x)) = B.ρ k⁻¹ (φ.hom ((A.act n).ρ k⁻¹⁻¹ x))
  rw [inv_inv]

end Twist


section Xi

variable {G : Type} [Group G] {H : Subgroup G} [H.Normal]
  {W : Rep.{0} ℚ ↥H} {R' R : ChainComplex (Rep.{0} ℚ ↥H) ℕ}

omit [H.Normal] in
theorem homPullback_id' (C : ChainComplex (Rep.{0} ℚ ↥H) ℕ) (W : Rep.{0} ℚ ↥H) :
    TernaryPoly.EquivariantSingularSmall.homPullback (𝟙 C) W = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rfl

/-- The reindexing isomorphism of Hom cochains `Hom_H(R', W) ≅ Hom_H(R, W)` attached to an
identification `Θ : R' ≅ twist_k R`: pull back along `Θ⁻¹`, then apply `ψ ↦ ρ_W(k)⁻¹ ∘ ψ`. -/
def XiIso (B : GAct H W) (k : G) (Θ : R' ≅ twistC k R) :
    R'.linearYonedaObj ℚ W ≅ R.linearYonedaObj ℚ W where
  hom := TernaryPoly.EquivariantSingularSmall.homPullback Θ.inv W ≫ (sigmaIso B k).hom
  inv := (sigmaIso B k).inv ≫ TernaryPoly.EquivariantSingularSmall.homPullback Θ.hom W
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc ((sigmaIso B k).hom), Iso.hom_inv_id, Category.id_comp,
      ← TernaryPoly.EquivariantSingularSmall.homPullback_comp, Iso.hom_inv_id,
      homPullback_id']
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc (TernaryPoly.EquivariantSingularSmall.homPullback Θ.hom W),
      ← TernaryPoly.EquivariantSingularSmall.homPullback_comp, Iso.inv_hom_id, homPullback_id',
      Category.id_comp, Iso.inv_hom_id]

/-- **Agreement of a pullback with the conjugation action up to reindexing.** If a chain map
`Φ : R' ⟶ R` is the composite of an identification `Θ : R' ≅ twist_k R` with the action of `k`, then
pulling back along `Φ` and applying the reindexing `XiIso` is the conjugation action `hcAct` of
`k⁻¹`. -/
theorem homPullback_eq_hcAct (A : GActC R) (B : GAct H W) (k : G) (Θ : R' ≅ twistC k R)
    (Φ : R' ⟶ R) (hΦ : Φ = Θ.hom ≫ actC A k) :
    TernaryPoly.EquivariantSingularSmall.homPullback Φ W ≫ (XiIso B k Θ).hom = hcAct A B k⁻¹ := by
  rw [← homPullback_actC_sigma A B k, hΦ, TernaryPoly.EquivariantSingularSmall.homPullback_comp]
  change _ ≫ TernaryPoly.EquivariantSingularSmall.homPullback Θ.hom W ≫
    TernaryPoly.EquivariantSingularSmall.homPullback Θ.inv W ≫ (sigmaIso B k).hom = _
  rw [← Category.assoc (TernaryPoly.EquivariantSingularSmall.homPullback Θ.hom W),
    ← TernaryPoly.EquivariantSingularSmall.homPullback_comp, Iso.inv_hom_id, homPullback_id',
    Category.id_comp]

end Xi


section ActIso

variable {G : Type} [Group G] {H : Subgroup G} [H.Normal]

/-- The inverse of the action of `k`: the action of `k⁻¹` into the twisted representation. -/
def actRepInv {X : Rep.{0} ℚ ↥H} (A : GAct H X) (k : G) : X ⟶ twistRep k X :=
  Rep.ofHom ⟨A.ρ k⁻¹, fun h => LinearMap.ext fun x => by
    change A.ρ k⁻¹ (X.ρ h x) = X.ρ (cjH H k h) (A.ρ k⁻¹ x)
    rw [A.conj]
    rfl⟩

/-- The inverse chain map of `actC`. -/
def actCInv {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D) (k : G) : D ⟶ twistC k D where
  f n := actRepInv (A.act n) k
  comm' i j _ := by
    apply rep_hom_ext'
    intro x
    exact A.comm k⁻¹ i j x

/-- The action of `k` is an isomorphism from the twisted complex. -/
instance actC_isIso {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} (A : GActC D) (k : G) :
    IsIso (actC A k) :=
  ⟨⟨actCInv A k, by
      apply HomologicalComplex.hom_ext
      intro n
      apply rep_hom_ext'
      intro x
      exact LinearMap.congr_fun (show (A.act n).ρ k⁻¹ * (A.act n).ρ k = 1 by
        rw [← map_mul, inv_mul_cancel, map_one]) x, by
      apply HomologicalComplex.hom_ext
      intro n
      apply rep_hom_ext'
      intro x
      exact LinearMap.congr_fun (show (A.act n).ρ k * (A.act n).ρ k⁻¹ = 1 by
        rw [← map_mul, mul_inv_cancel, map_one]) x⟩⟩

end ActIso

end TernaryPeriodPolynomials.Argument.GroupHomology
