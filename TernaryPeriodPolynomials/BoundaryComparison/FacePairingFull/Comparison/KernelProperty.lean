module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Setup
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Comparison
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.LevelAveraging
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceQuotient
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Corner
public import TernaryPeriodPolynomials.Topology.TopHomology.CoinvariantCycle

@[expose] public section


/-!
# The kernel property: a vanishing evaluation on the fundamental chain forces boundary exactness

For a lift `v` of a degree-four cycle of the coinvariants of the model cone `coneR` that spans the cycles
modulo boundaries (`CoinvariantCycle.exists_fundamental_cycle`), the finite rational chain
`cornerChain v` (the corner component of `v`) has the following property
(`boundaryExactAt_of_cornerChain`): a closed `N6`-invariant edge three-cochain `f` whose
evaluation `evalOmega (cornerChain v) f = Σ_y Ω(y) f(y)` vanishes is boundary exact at `N6`.  The proof
translates `f` into the corner cocycle `coneCocycle f` of the cone (`toHom`, via the identification of the
model cochains with the invariant functions on `V^{k+1} × Z`, `ModelInv`), applies the universal
coefficient property of `ω` (`cocycles vanishing on ω are coboundaries`) and reads the resulting
cone coboundary with `ConeCorner.corner_coboundary` as an edge coboundary plus pullbacks of closed line and
plane three-cochains.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.BoundaryFaceResolutionComparison HomologicalComplex
open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

/-- The corner cochain is the corner projection followed by the corner component. -/
theorem cornerCochain_eq {F L P : ChainComplex (Rep.{0} ℚ Γ6) ℕ} (a : F ⟶ L) (b : F ⟶ P)
    (W : Rep.{0} ℚ Γ6) (n : ℕ) (e : F.X n ⟶ W) :
    cornerCochain a b W n e =
      homotopyCofiber.fstX (signedArrow a b) (n + 1) n (downSucc n) ≫ e := by
  apply (signedConeHomSucc a b W n).injective
  rw [cornerCochain_coords, signedConeHomSucc_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [signedCornerInclusion]
  · simp [signedLineInclusion]
  · simp [signedPlaneInclusion]

section Faces

variable {V Z : Type} {W : Type} [AddCommGroup W]

theorem sum_face_three (G : (Fin 3 → V) × Z → W) (x : Fin 4 → V) (z : Z) :
    ∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • G (face V Z i (x, z)) =
      G (![x 1, x 2, x 3], z) - G (![x 0, x 2, x 3], z) + G (![x 0, x 1, x 3], z) -
        G (![x 0, x 1, x 2], z) := by
  have e0 : face V Z (0 : Fin 4) (x, z) = (![x 1, x 2, x 3], z) :=
    Prod.ext (funext fun j => by fin_cases j <;> rfl) rfl
  have e1 : face V Z (1 : Fin 4) (x, z) = (![x 0, x 2, x 3], z) :=
    Prod.ext (funext fun j => by fin_cases j <;> rfl) rfl
  have e2 : face V Z (2 : Fin 4) (x, z) = (![x 0, x 1, x 3], z) :=
    Prod.ext (funext fun j => by fin_cases j <;> rfl) rfl
  have e3 : face V Z (3 : Fin 4) (x, z) = (![x 0, x 1, x 2], z) :=
    Prod.ext (funext fun j => by fin_cases j <;> rfl) rfl
  have c0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have c1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have c2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have c3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [Fin.sum_univ_four, e0, e1, e2, e3, c0, c1, c2, c3]
  norm_num
  abel

theorem sum_face_four (G : (Fin 4 → V) × Z → W) (x : Fin 5 → V) (z : Z) :
    ∑ i : Fin 5, ((-1 : ℤ) ^ (i : ℕ)) • G (face V Z i (x, z)) =
      G (![x 1, x 2, x 3, x 4], z) - G (![x 0, x 2, x 3, x 4], z) + G (![x 0, x 1, x 3, x 4], z) -
        G (![x 0, x 1, x 2, x 4], z) + G (![x 0, x 1, x 2, x 3], z) := by
  have e0 : face V Z (0 : Fin 5) (x, z) = (![x 1, x 2, x 3, x 4], z) :=
    Prod.ext (funext fun j => by fin_cases j <;> rfl) rfl
  have e1 : face V Z (1 : Fin 5) (x, z) = (![x 0, x 2, x 3, x 4], z) :=
    Prod.ext (funext fun j => by fin_cases j <;> rfl) rfl
  have e2 : face V Z (2 : Fin 5) (x, z) = (![x 0, x 1, x 3, x 4], z) :=
    Prod.ext (funext fun j => by fin_cases j <;> rfl) rfl
  have e3 : face V Z (3 : Fin 5) (x, z) = (![x 0, x 1, x 2, x 4], z) :=
    Prod.ext (funext fun j => by fin_cases j <;> rfl) rfl
  have e4 : face V Z (4 : Fin 5) (x, z) = (![x 0, x 1, x 2, x 3], z) :=
    Prod.ext (funext fun j => by fin_cases j <;> rfl) rfl
  have c0 : ((0 : Fin 5) : ℕ) = 0 := rfl
  have c1 : ((1 : Fin 5) : ℕ) = 1 := rfl
  have c2 : ((2 : Fin 5) : ℕ) = 2 := rfl
  have c3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have c4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  rw [Fin.sum_univ_five, e0, e1, e2, e3, e4, c0, c1, c2, c3, c4]
  norm_num
  abel

end Faces

section Translate

variable {X Z : Type} [MulAction RationalGL3 X] [MulAction Γ6 Z] (ψ : X ≃ Z)
  (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x)

/-- The morphism out of `ℚ[V^{k+1} × Z]` attached to a model cochain. -/
def toHom (k : ℕ) (f : cochains N6 (functionRepresentation scalarTrivial X) k) :
    (prodComplex Γ6 RationalGL3 Z).X k ⟶ Rep.trivial ℚ Γ6 ℂ :=
  homOfFun (modelToInv ψ hψ k f).1 (modelToInv ψ hψ k f).2

theorem homFun_toHom (k : ℕ) (f : cochains N6 (functionRepresentation scalarTrivial X) k) :
    homFun (toHom ψ hψ k f) = (modelToInv ψ hψ k f).1 :=
  homFun_homOfFun _ _

/-- The model cochain attached to a morphism out of `ℚ[V^{k+1} × Z]`. -/
def ofHom (k : ℕ) (c : (prodComplex Γ6 RationalGL3 Z).X k ⟶ Rep.trivial ℚ Γ6 ℂ) :
    cochains N6 (functionRepresentation scalarTrivial X) k :=
  invToModel ψ hψ k ⟨homFun c, homFun_invariant c⟩

theorem ofHom_val (k : ℕ) (c : (prodComplex Γ6 RationalGL3 Z).X k ⟶ Rep.trivial ℚ Γ6 ℂ)
    (x : Fin (k + 1) → RationalGL3) (e : X) : (ofHom ψ hψ k c).1 x e = homFun c (x, ψ e) := rfl

theorem toHom_ofHom (k : ℕ) (c : (prodComplex Γ6 RationalGL3 Z).X k ⟶ Rep.trivial ℚ Γ6 ℂ) :
    toHom ψ hψ k (ofHom ψ hψ k c) = c := by
  apply homFun_injective
  rw [homFun_toHom]
  exact congrArg Subtype.val (modelToInv_invToModel ψ hψ k ⟨homFun c, homFun_invariant c⟩)

theorem toHom_val (k : ℕ) (f : cochains N6 (functionRepresentation scalarTrivial X) k)
    (x : Fin (k + 1) → RationalGL3) (z : Z) : homFun (toHom ψ hψ k f) (x, z) = f.1 x (ψ.symm z) := by
  rw [homFun_toHom]
  rfl

/-- The differential of an edge two-cochain matches the cone differential. -/
theorem homFun_d_toHom_two (f : cochains N6 (functionRepresentation scalarTrivial X) 2)
    (x : Fin 4 → RationalGL3) (z : Z) :
    homFun ((prodComplex Γ6 RationalGL3 Z).d 3 2 ≫ toHom ψ hψ 2 f) (x, z) =
      differentialTwo N6 (functionRepresentation scalarTrivial X) f x (ψ.symm z) := by
  rw [homFun_comp_d, sum_face_three]
  simp only [homFun_toHom]
  rfl

theorem homFun_d_toHom_three (f : cochains N6 (functionRepresentation scalarTrivial X) 3)
    (x : Fin 5 → RationalGL3) (z : Z) :
    homFun ((prodComplex Γ6 RationalGL3 Z).d 4 3 ≫ toHom ψ hψ 3 f) (x, z) =
      differentialThreeRaw f.1 x (ψ.symm z) := by
  rw [homFun_comp_d, sum_face_four]
  simp only [homFun_toHom]
  rfl

end Translate

/-! ### Evaluation on a finite chain -/

/-- Evaluation of a function on a finite rational chain. -/
def evalChain {Y : Type} (v : MonoidAlgebra ℚ Y) : (Y → ℂ) →ₗ[ℂ] ℂ where
  toFun F := Finsupp.linearCombination ℚ F v.coeff
  map_add' F G := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Pi.add_apply, smul_add,
      Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Pi.smul_apply, RingHom.id_apply,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun y _ => smul_comm _ _ _

theorem hom_eq_evalChain {Y : Type} [MulAction Γ6 Y] (c : Rep.ofMulAction ℚ Γ6 Y ⟶ Rep.trivial ℚ Γ6 ℂ)
    (v : MonoidAlgebra ℚ Y) :
    c.hom v = evalChain v (fun y => c.hom (MonoidAlgebra.single y 1)) := by
  have key : c.hom.toLinearMap = liftMap Y (Rep.trivial ℚ Γ6 ℂ) (fun y => c.hom (MonoidAlgebra.single y 1)) := by
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
    change c.hom (MonoidAlgebra.single x 1) = liftMap Y (Rep.trivial ℚ Γ6 ℂ) _ (MonoidAlgebra.single x 1)
    rw [liftMap_single, one_smul]
  exact LinearMap.congr_fun key v

/-- The evaluation functional of a chain `Ω` on complete-flag cochains. -/
def evalOmega (Ω : MonoidAlgebra ℚ ((Fin 4 → RationalGL3) × Flag)) :
    ((Fin 4 → RationalGL3) → Edges → ℂ) →ₗ[ℂ] ℂ where
  toFun f := evalChain Ω (fun y => f y.1 (psiEdge.symm y.2))
  map_add' f g := by
    rw [← map_add]
    rfl
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]
    rfl

section Main

/-- The trivial complex coefficients. -/
abbrev Wℂ : Rep.{0} ℚ Γ6 := Rep.trivial ℚ Γ6 ℂ

theorem closed_ofHom {X Z : Type} [MulAction RationalGL3 X] [MulAction Γ6 Z] (ψ : X ≃ Z)
    (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x)
    (c : (prodComplex Γ6 RationalGL3 Z).X 3 ⟶ Wℂ)
    (hc : (prodComplex Γ6 RationalGL3 Z).d 4 3 ≫ c = 0) (x : Fin 5 → RationalGL3) :
    differentialThreeRaw (ofHom ψ hψ 3 c).1 x = 0 := by
  funext e
  have h := homFun_d_toHom_three ψ hψ (ofHom ψ hψ 3 c) x (ψ e)
  rw [toHom_ofHom, hc, Equiv.symm_apply_apply] at h
  exact h.symm

/-- The corner component of a degree-four chain of the model cone. -/
def cornerChain (v : coneR.X 4) : MonoidAlgebra ℚ ((Fin 4 → RationalGL3) × Flag) :=
  (homotopyCofiber.fstX (signedArrow flagLineHom.hom flagPlaneHom.hom) (3 + 1) 3
    (downSucc 3)).hom v

/-- The model cochain of a closed edge three-cochain. -/
def edgeHom (f : closedEdgeCochains N6) : (prodComplex Γ6 RationalGL3 Flag).X 3 ⟶ Wℂ :=
  toHom psiEdge psiEdge_smul 3 ⟨f.1, f.2.1⟩

theorem edgeHom_closed (f : closedEdgeCochains N6) :
    (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ edgeHom f = 0 := by
  apply homFun_injective
  funext y
  obtain ⟨x, z⟩ := y
  have h1 := homFun_d_toHom_three psiEdge psiEdge_smul ⟨f.1, f.2.1⟩ x z
  refine h1.trans ?_
  exact congrFun (f.2.2 x) (psiEdge.symm z)

/-- The corner cocycle of the cone attached to a closed edge three-cochain. -/
def coneCocycle (f : closedEdgeCochains N6) : coneR.X 4 ⟶ Wℂ :=
  cornerCochain flagLineHom.hom flagPlaneHom.hom Wℂ 3 (edgeHom f)

theorem coneCocycle_closed (f : closedEdgeCochains N6) : coneR.d 5 4 ≫ coneCocycle f = 0 := by
  apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom Wℂ 4).injective
  have h := cone_coboundary_coordinates flagLineHom.hom flagPlaneHom.hom Wℂ 3 (coneCocycle f)
  rw [coneCocycle, cornerCochain_coords] at h
  rw [coneCocycle, h, map_zero]
  simp [edgeHom_closed f]

theorem coinvHom_coneCocycle (f : closedEdgeCochains N6) (v : coneR.X 4) :
    coinvHom (coneR.X 4) ℂ (coneCocycle f) (Representation.Coinvariants.mk (coneR.X 4).ρ v) =
      evalOmega (cornerChain v) f.1 := by
  have h1 : coinvHom (coneR.X 4) ℂ (coneCocycle f) (Representation.Coinvariants.mk (coneR.X 4).ρ v) =
      (coneCocycle f).hom v := rfl
  rw [h1, coneCocycle, cornerCochain_eq]
  refine (hom_eq_evalChain (Y := (Fin (3 + 1) → RationalGL3) × Flag) (edgeHom f) _).trans ?_
  change evalChain (cornerChain v) _ = evalChain (cornerChain v) _
  congr 1
  funext y
  exact (toHom_val psiEdge psiEdge_smul 3 ⟨f.1, f.2.1⟩ y.1 y.2)

/-- **The kernel property of the corner chain of a spanning cycle.** -/
theorem boundaryExactAt_of_cornerChain (v : coneR.X 4)
    (hspan : ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (c : coneR.X 4 ⟶ Rep.trivial ℚ Γ6 W),
      coneR.d 5 4 ≫ c = 0 →
      coinvHom (coneR.X 4) W c (Representation.Coinvariants.mk (coneR.X 4).ρ v) = 0 →
      ∃ η : coneR.X 3 ⟶ Rep.trivial ℚ Γ6 W, c = coneR.d 4 3 ≫ η)
    (f : closedEdgeCochains N6) (hev : evalOmega (cornerChain v) f.1 = 0) :
    BoundaryExactAt N6 f.1 := by
  obtain ⟨η, hη⟩ := hspan ℂ (coneCocycle f) (coneCocycle_closed f)
    ((coinvHom_coneCocycle f v).trans hev)
  obtain ⟨e', l', p', hl', hp', he⟩ :=
    corner_coboundary flagLineHom.hom flagPlaneHom.hom Wℂ 2 (edgeHom f) η hη.symm
  let E := ofHom psiEdge psiEdge_smul 2 e'
  let L := ofHom psiLine psiLine_smul 3 l'
  let P := ofHom psiPlane psiPlane_smul 3 p'
  have hLc : ∀ x, differentialThreeRaw L.1 x = 0 := closed_ofHom psiLine psiLine_smul l' hl'
  have hPc : ∀ x, differentialThreeRaw P.1 x = 0 := closed_ofHom psiPlane psiPlane_smul p' hp'
  refine ⟨-E, -P.1, -L.1, (-P).2, (-L).2, ?_, ?_, ?_⟩
  · intro x
    funext e
    have h0 := congrFun (hPc x) e
    simp only [differentialThreeRaw, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at h0 ⊢
    linear_combination -h0
  · intro x
    funext e
    have h0 := congrFun (hLc x) e
    simp only [differentialThreeRaw, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at h0 ⊢
    linear_combination -h0
  · intro x e
    have h1 : f.1 x e = homFun (edgeHom f) (x, psiEdge e) := by
      have := toHom_val psiEdge psiEdge_smul 3 ⟨f.1, f.2.1⟩ x (psiEdge e)
      rw [Equiv.symm_apply_apply] at this
      exact this.symm
    have h2 := congrArg (fun m => homFun m (x, psiEdge e)) he
    simp only [homFun_sub, homFun_add, homFun_neg, Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at h2
    have h3 : homFun (resFlag.complex.d 3 2 ≫ e') (x, psiEdge e) =
        differentialTwo N6 (functionRepresentation scalarTrivial Edges) E x e := by
      have := homFun_d_toHom_two psiEdge psiEdge_smul E x (psiEdge e)
      rw [toHom_ofHom, Equiv.symm_apply_apply] at this
      exact this
    have h4 : homFun (flagLineHom.hom.f 3 ≫ l') (x, psiEdge e) = L.1 x (endpoint .line e) := by
      rw [homFun_comp_map]
      exact congrArg (fun F => homFun l' (x, F)) (psiEdge_line e)
    have h5 : homFun (flagPlaneHom.hom.f 3 ≫ p') (x, psiEdge e) = P.1 x (endpoint .plane e) := by
      rw [homFun_comp_map]
      exact congrArg (fun F => homFun p' (x, F)) (psiEdge_plane e)
    rw [h1, h2, h3, h4, h5, map_neg]
    simp only [Pi.neg_apply]
    ring

end Main

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
