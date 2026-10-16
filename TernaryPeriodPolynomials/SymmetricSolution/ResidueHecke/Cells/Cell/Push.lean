module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Face.Reduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellSurjective
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CoeffAtT0
public import TernaryPeriodPolynomials.GroupCohomology.Homology.BarMaps
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalDescent

@[expose] public section


/-!
# Lemma B.1: the cellular push-forward represents `ι_*`

Formalized by Claude Sonnet 5.5.

Let `j : H →* Γ`, `V : Rep ℚ H`, `W : Rep ℚ Γ`, `φ : V ⟶ Res_j W`.  For a complex `P` of `Γ`-representations the
map `[v ⊗ x] ↦ [φ v ⊗ x]` is a chain map `(V ⊗ Res_j P)_H ⟶ (W ⊗ P)_Γ` (`pushT`, `pushC`, natural in `P`).
It is compatible with the bar resolutions along `j` (`chains_push_comm`), and for any projective resolution `R` of
`ℚ` over `Γ` whose restriction to `H` is a projective resolution (`resRes`) and any augmentation compatible chain map
`c : R ⟶ Q` to a second projective resolution `Q` with a comparison `κ : bar(Γ) ⟶ Q`, the two induced maps on homology
agree (`key_homology`): the proof compares the two maps `bar(H) ⟶ Res_j Q` by the uniqueness of lifts up to homotopy
(`keyHomotopy`).

For `Γ = Γ(6)`, `H = P_N`, `R` the cell resolution of `Lemma33.Retract` this gives

* `cellPush V W φ : cellCoinvPN V ⟶ cellCoinv W`, `[v ⊗ C] ↦ [φ v ⊗ C]` (`cellPush_f_mk`), where `cellCoinvPN V` is the
  cellular complex `(Res cells ⊗ V)_{P_N}` of the restricted resolution `cellResPN`;
* `cellPush_comparison`: `H_m(cellPush) ≫ cellGroupHomologyMap W m = (groupHomologyIso V m cellResPN).inv ≫
  groupHomology.map jPN φ m`;
* `iotaStar_eq_cellPush` and `exists_cell_cycle`: every `ι_* w` is `cellGroupHomologyMap` of the class of the pushed
  cell cycle `cellPush ζ` for a cycle `ζ` of `cellCoinvPN V` representing `w`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory Finsupp Rep
open scoped MonoidAlgebra Classical

section Generic

variable {H Γ : Type} [Group H] [Group Γ] (j : H →* Γ)

/-- The comparison `(V ⊗ Res_j X)_H → (W ⊗ X)_Γ` -/
def pushT (V : Rep.{0} ℚ H) (W : Rep.{0} ℚ Γ) (φ : V ⟶ Rep.res j W) (X : Rep.{0} ℚ Γ) :
    ((coinvariantsTensor ℚ H).obj V).obj (Rep.res j X) ⟶ ((coinvariantsTensor ℚ Γ).obj W).obj X :=
  ModuleCat.ofHom
    (Representation.Coinvariants.lift (V.ρ.tprod (Rep.res j X).ρ)
      (Representation.Coinvariants.mk (W.ρ.tprod X.ρ) ∘ₗ TensorProduct.map φ.hom.toLinearMap LinearMap.id)
      (fun h => by
        refine TensorProduct.ext' fun v x => ?_
        have hc : φ.hom (V.ρ h v) = W.ρ (j h) (φ.hom v) := Rep.hom_comm_apply φ h v
        change Representation.Coinvariants.mk (W.ρ.tprod X.ρ)
            (TensorProduct.map φ.hom.toLinearMap LinearMap.id (V.ρ h v ⊗ₜ[ℚ] X.ρ (j h) x)) = _
        rw [TensorProduct.map_tmul]
        have := Representation.Coinvariants.mk_self_apply (W.ρ.tprod X.ρ) (j h) (φ.hom v ⊗ₜ[ℚ] x)
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply] at this ⊢
        refine Eq.trans ?_ this
        change _ = Representation.Coinvariants.mk (W.ρ.tprod X.ρ) (W.ρ (j h) (φ.hom v) ⊗ₜ[ℚ] X.ρ (j h) x)
        rw [← hc]
        rfl))

theorem pushT_mk (V : Rep.{0} ℚ H) (W : Rep.{0} ℚ Γ) (φ : V ⟶ Rep.res j W) (X : Rep.{0} ℚ Γ)
    (v : V) (x : X) :
    (pushT j V W φ X).hom (Representation.Coinvariants.mk (V.ρ.tprod (Rep.res j X).ρ) (v ⊗ₜ[ℚ] x)) =
      Representation.Coinvariants.mk (W.ρ.tprod X.ρ) (φ.hom v ⊗ₜ[ℚ] x) := rfl

theorem pushT_natural (V : Rep.{0} ℚ H) (W : Rep.{0} ℚ Γ) (φ : V ⟶ Rep.res j W) {X Y : Rep.{0} ℚ Γ}
    (f : X ⟶ Y) :
    ((coinvariantsTensor ℚ H).obj V).map ((resFunctor j).map f) ≫ pushT j V W φ Y =
      pushT j V W φ X ≫ ((coinvariantsTensor ℚ Γ).obj W).map f := by
  refine ModuleCat.hom_ext (Representation.Coinvariants.hom_ext ?_)
  refine TensorProduct.ext' fun v x => ?_
  rfl

/-- chain-level push -/
def pushC (V : Rep.{0} ℚ H) (W : Rep.{0} ℚ Γ) (φ : V ⟶ Rep.res j W) (P : ChainComplex (Rep.{0} ℚ Γ) ℕ) :
    (((resFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj P).coinvariantsTensorObj V ⟶
      P.coinvariantsTensorObj W where
  f n := pushT j V W φ (P.X n)
  comm' i k _ := by
    simp only [Functor.mapHomologicalComplex_obj_d]
    exact (pushT_natural j V W φ (P.d i k)).symm

theorem pushC_f (V : Rep.{0} ℚ H) (W : Rep.{0} ℚ Γ) (φ : V ⟶ Rep.res j W) (P : ChainComplex (Rep.{0} ℚ Γ) ℕ)
    (n : ℕ) : (pushC j V W φ P).f n = pushT j V W φ (P.X n) := rfl

theorem pushC_natural (V : Rep.{0} ℚ H) (W : Rep.{0} ℚ Γ) (φ : V ⟶ Rep.res j W)
    {P Q : ChainComplex (Rep.{0} ℚ Γ) ℕ} (f : P ⟶ Q) :
    (((coinvariantsTensor ℚ H).obj V).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((resFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).map f) ≫ pushC j V W φ Q =
      pushC j V W φ P ≫ (((coinvariantsTensor ℚ Γ).obj W).mapHomologicalComplex (ComplexShape.down ℕ)).map f := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact pushT_natural j V W φ (f.f n)

theorem chains_push_apply (V : Rep.{0} ℚ H) (W : Rep.{0} ℚ Γ) (φ : V ⟶ Rep.res j W) (n : ℕ)
    (x : Fin n → H) (a : V) :
    ((groupHomology.inhomogeneousChainsIso W).hom.f n).hom (((groupHomology.chainsMap j φ).f n).hom (single x a)) =
      ((pushC j V W φ (barComplex ℚ Γ)).f n).hom
        ((((coinvariantsTensor ℚ H).obj V).map ((barMap (k := ℚ) j).f n)).hom
          (((groupHomology.inhomogeneousChainsIso V).hom.f n).hom (single x a))) := by
  have eL : ((groupHomology.chainsMap j φ).f n).hom (single x a) = single (j ∘ x) (φ.hom a) := by
    have := groupHomology.chainsMap_f_single j φ n x a
    simpa using this
  rw [eL]
  have e1 := inhomIso_hom_f_single W n (j ∘ x) (φ.hom a)
  have e5 := inhomIso_hom_f_single V n x a
  have e2 := coinvTensor_map_mk V ((barMap (k := ℚ) j).f n) a
    (single x (MonoidAlgebra.single (1 : H) (1 : ℚ)))
  have e3 : ((barMap (k := ℚ) j).f n).hom (single x (MonoidAlgebra.single (1 : H) (1 : ℚ))) =
      single (j ∘ x) (MonoidAlgebra.single (1 : Γ) (1 : ℚ)) := by
    change (barTerm (k := ℚ) j n).hom _ = _
    rw [barTerm_single, map_one]
  rw [e1, e5, e2, e3]
  rfl

theorem chains_push_comm (V : Rep.{0} ℚ H) (W : Rep.{0} ℚ Γ) (φ : V ⟶ Rep.res j W) :
    groupHomology.chainsMap j φ ≫ (groupHomology.inhomogeneousChainsIso W).hom =
      (groupHomology.inhomogeneousChainsIso V).hom ≫
        (((coinvariantsTensor ℚ H).obj V).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (barMap (k := ℚ) j) ≫ pushC j V W φ (barComplex ℚ Γ) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  exact chains_push_apply j V W φ n x a

theorem barMap_pi_gen :
    (barMap (k := ℚ) j).f 0 ≫ (resFunctor j).map ((barResolution ℚ Γ).π.f 0) =
      (barResolution ℚ H).π.f 0 := by
  refine free_ext _ _ _ _ _ fun x => ?_
  have h2 := barPi_f_zero (k := ℚ) (G := H) x 1 1
  have h3 := barPi_f_zero (k := ℚ) (G := Γ) (fun i => j (x i)) 1 1
  refine Eq.trans ?_ h2.symm
  have key : ((resFunctor j).map ((barResolution ℚ Γ).π.f 0)).hom
      ((barTerm (k := ℚ) j 0).hom (single x (MonoidAlgebra.single 1 1))) =
      ((barResolution ℚ Γ).π.f 0).hom (single (fun i => j (x i)) (MonoidAlgebra.single 1 1)) := by
    rw [barTerm_single, map_one]
    rfl
  exact key.trans h3

/-- Restriction of a projective resolution along `j`, assuming the restricted terms are projective. -/
def resRes (P : ProjectiveResolution (Rep.trivial ℚ Γ ℚ))
    (hP : ∀ n, Projective ((resFunctor.{0} j).obj (P.complex.X n))) :
    ProjectiveResolution ((resFunctor.{0} j).obj (Rep.trivial ℚ Γ ℚ)) where
  complex := ((resFunctor.{0} j).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  projective := hP
  π := ((resFunctor.{0} j).mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex (resFunctor.{0} j) (ComplexShape.down ℕ) 0).hom.app _
  quasiIso := inferInstance

theorem toSingle₀_ext {C : Type*} [Category C] [Abelian C] {K : ChainComplex C ℕ} {X : C}
    {f g : K ⟶ (ChainComplex.single₀ C).obj X} (h : f.f 0 = g.f 0) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero => exact h
  | succ i => exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero i)).eq_of_tgt _ _

section Key

variable (R : ProjectiveResolution (Rep.trivial ℚ Γ ℚ))
  (hR : ∀ n, Projective ((resFunctor.{0} j).obj (R.complex.X n)))
  (Q : ProjectiveResolution (Rep.trivial ℚ Γ ℚ)) (c : R.complex ⟶ Q.complex)
  (hc : c ≫ Q.π = R.π ≫ (ChainComplex.single₀ _).map (𝟙 _))
  (κ : barComplex ℚ Γ ⟶ Q.complex)
  (hκ : κ ≫ Q.π = (barResolution ℚ Γ).π ≫ (ChainComplex.single₀ _).map (𝟙 _))
  (α : barComplex ℚ H ⟶ ((resFunctor.{0} (k := ℚ) j).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
  (hα : α ≫ (resRes j R hR).π = (barResolution ℚ H).π ≫ (ChainComplex.single₀ _).map (𝟙 _))

/-- The H-level homotopy between the two comparisons `bar(H) → Res_j Q`. -/
def keyHomotopy :
    Homotopy
      (α ≫ ((resFunctor.{0} (k := ℚ) j).mapHomologicalComplex (ComplexShape.down ℕ)).map c)
      (barMap (k := ℚ) j ≫ ((resFunctor.{0} (k := ℚ) j).mapHomologicalComplex (ComplexShape.down ℕ)).map κ) := by
  let γ : barComplex ℚ Γ ⟶ R.complex := ProjectiveResolution.lift (𝟙 (Rep.trivial ℚ Γ ℚ)) (barResolution ℚ Γ) R
  have hγ : γ ≫ R.π = (barResolution ℚ Γ).π ≫ (ChainComplex.single₀ _).map (𝟙 _) :=
    ProjectiveResolution.lift_commutes _ _ _
  have h1 : Homotopy α
      (barMap (k := ℚ) j ≫ ((resFunctor.{0} (k := ℚ) j).mapHomologicalComplex (ComplexShape.down ℕ)).map γ) := by
    refine ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial ℚ H ℚ)) (P := barResolution ℚ H)
      (Q := resRes j R hR) _ _ hα ?_
    refine toSingle₀_ext ?_
    have e0 : ((resRes j R hR).π).f 0 = (resFunctor.{0} j).map (R.π.f 0) := by
      simp [resRes]
      exact (congrArg (fun m => (resFunctor.{0} j).map (R.π.f 0) ≫ m)
        ((resFunctor.{0} j).map_id (Rep.trivial ℚ Γ ℚ))).trans (Category.comp_id _)
    have e1 := barMap_pi_gen j
    have e2 := congrArg (fun m => m.f 0) hγ
    simp only [HomologicalComplex.comp_f] at e2 ⊢
    rw [(ChainComplex.single₀ _).map_id, HomologicalComplex.id_f, Category.comp_id] at e2 ⊢
    change (barMap (k := ℚ) j).f 0 ≫ (resFunctor.{0} j).map (γ.f 0) ≫ (resFunctor.{0} j).map (R.π.f 0) = _
    refine Eq.trans (congrArg (fun m => (barMap (k := ℚ) j).f 0 ≫ m)
      ((Functor.map_comp (resFunctor.{0} j) (γ.f 0) (R.π.f 0)).symm.trans
        (congrArg (resFunctor.{0} j).map e2))) e1
  have h2 : Homotopy (γ ≫ c) κ := by
    refine ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial ℚ Γ ℚ)) (P := barResolution ℚ Γ) (Q := Q) _ _ ?_ hκ
    erw [Category.assoc, hc, ← Category.assoc, hγ, Category.assoc]
    simp
  let Rj := (resFunctor.{0} (k := ℚ) j).mapHomologicalComplex (ComplexShape.down ℕ)
  have h3 := h1.compRight (Rj.map c)
  have h4 : (barMap (k := ℚ) j ≫ Rj.map γ) ≫ Rj.map c = barMap (k := ℚ) j ≫ Rj.map (γ ≫ c) := by
    rw [Category.assoc]
    exact congrArg (fun m => barMap (k := ℚ) j ≫ m) (Rj.map_comp γ c).symm
  have h5 : Homotopy (barMap (k := ℚ) j ≫ Rj.map (γ ≫ c)) (barMap (k := ℚ) j ≫ Rj.map κ) :=
    ((resFunctor.{0} (k := ℚ) j).mapHomotopy h2).compLeft (barMap (k := ℚ) j)
  exact h3.trans ((Homotopy.ofEq h4).trans h5)

include hR hc hκ hα in
theorem key_homology (V : Rep.{0} ℚ H) (W : Rep.{0} ℚ Γ) (φ : V ⟶ Rep.res j W) (n : ℕ) :
    HomologicalComplex.homologyMap (groupHomology.chainsMap j φ ≫
      (groupHomology.inhomogeneousChainsIso W).hom ≫
      (((coinvariantsTensor ℚ Γ).obj W).mapHomologicalComplex (ComplexShape.down ℕ)).map κ) n =
    HomologicalComplex.homologyMap ((groupHomology.inhomogeneousChainsIso V).hom ≫
      (((coinvariantsTensor ℚ H).obj V).mapHomologicalComplex (ComplexShape.down ℕ)).map α ≫
      pushC j V W φ R.complex ≫
      (((coinvariantsTensor ℚ Γ).obj W).mapHomologicalComplex (ComplexShape.down ℕ)).map c) n := by
  let G := (coinvariantsTensor ℚ H).obj V
  let FV := G.mapHomologicalComplex (ComplexShape.down ℕ)
  let Rj := (resFunctor.{0} (k := ℚ) j).mapHomologicalComplex (ComplexShape.down ℕ)
  have eL : groupHomology.chainsMap j φ ≫ (groupHomology.inhomogeneousChainsIso W).hom ≫
      (((coinvariantsTensor ℚ Γ).obj W).mapHomologicalComplex (ComplexShape.down ℕ)).map κ =
      (groupHomology.inhomogeneousChainsIso V).hom ≫ FV.map (barMap (k := ℚ) j ≫ Rj.map κ) ≫
        pushC j V W φ Q.complex := by
    rw [← Category.assoc, chains_push_comm j V W φ, Functor.map_comp]
    simp only [Category.assoc]
    rw [pushC_natural j V W φ κ]
  have eR : (groupHomology.inhomogeneousChainsIso V).hom ≫ FV.map α ≫
      pushC j V W φ R.complex ≫
      (((coinvariantsTensor ℚ Γ).obj W).mapHomologicalComplex (ComplexShape.down ℕ)).map c =
      (groupHomology.inhomogeneousChainsIso V).hom ≫ FV.map (α ≫ Rj.map c) ≫
        pushC j V W φ Q.complex := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [pushC_natural j V W φ c]
  rw [eL, eR]
  have hh := ((G.mapHomotopy (keyHomotopy j R hR Q c hc κ hκ α hα)).compRight
    (pushC j V W φ Q.complex)).compLeft (groupHomology.inhomogeneousChainsIso V).hom
  exact (hh.homologyMap_eq n).symm

end Key

theorem res_perm_projective (hj : Function.Injective j) (X : Type) [MulAction Γ X] [IsCancelSMul Γ X] :
    Projective (Rep.res j (Rep.ofMulAction ℚ Γ X)) := by
  let _ : MulAction H X := MulAction.compHom X j
  have _ : IsCancelSMul H X :=
    { left_cancel' := fun a _ _ h => MulAction.injective (j a) h
      right_cancel' := fun a b x h => hj (IsCancelSMul.right_cancel (j a) (j b) x h) }
  exact (inferInstance : Projective (Rep.ofMulAction ℚ H X))

end Generic
end TernaryPeriodPolynomials.Argument.GroupHomology

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Rep TernaryPoly TernaryPoly.SingularLocalHomology TernaryPoly.EquivariantSingularResolution
  TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open scoped Classical

/-- The classical decidable equality used by Mathlib's group homology comparison for `Γ(6)`. -/
local instance (priority := high) decEqSix : DecidableEq principalSix := fun a b => Classical.propDecidable (a = b)

/-- The classical decidable equality for `P_N`. -/
local instance (priority := high) decEqPN : DecidableEq PN := fun a b => Classical.propDecidable (a = b)

theorem jPN_injective : Function.Injective jPN :=
  fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x : principalSix => x.1) h))

theorem cellRes_projective (n : ℕ) :
    Projective ((resFunctor.{0} jPN).obj (cellResolution.complex.X n)) :=
  res_perm_projective jPN jPN_injective (Graded n)

/-- The cell resolution restricted to `P_N`. -/
def cellResPN : ProjectiveResolution ((resFunctor.{0} jPN).obj (Rep.trivial ℚ principalSix ℚ)) :=
  resRes jPN cellResolution cellRes_projective

theorem cellGroupHomologyMap_eq (W : Rep.{0} ℚ principalSix) (m : ℕ) :
    cellGroupHomologyMap W m =
      HomologicalComplex.homologyMap (cellCoinvMap W) m ≫
        (groupCoinvariantHomologyIso principalSix (TopCat.of TernaryPoly.SymmetricSpaceRationalGluing.Glued) W m).inv := by
  unfold cellGroupHomologyMap cellToBordified
  have h1 : (bordifiedGroupLocalHomologyIso W m).inv =
      HomologicalComplex.homologyMap (bordifiedChainIso W).inv m ≫
        (groupCoinvariantHomologyIso principalSix (TopCat.of TernaryPoly.SymmetricSpaceRationalGluing.Glued) W m).inv := rfl
  rw [h1, HomologicalComplex.homologyMap_comp, Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (bordifiedChainIso W).hom m), ← HomologicalComplex.homologyMap_comp,
    Iso.hom_inv_id, HomologicalComplex.homologyMap_id, Category.id_comp]

/-- The cellular complex of `P_N` with coefficients in `V`: `(Res cells ⊗ V)_{P_N}`. -/
abbrev cellCoinvPN (V : Rep.{0} ℚ PN) : ChainComplex (ModuleCat ℚ) ℕ :=
  cellResPN.complex.coinvariantsTensorObj V

/-- The cellular push-forward `[v ⊗ C] ↦ [φ v ⊗ C]`. -/
def cellPush (V : Rep.{0} ℚ PN) (W : Rep.{0} ℚ principalSix) (φ : V ⟶ Rep.res jPN W) :
    cellCoinvPN V ⟶ cellCoinv W :=
  pushC jPN V W φ cellPermComplex

theorem cellPush_f_mk (V : Rep.{0} ℚ PN) (W : Rep.{0} ℚ principalSix) (φ : V ⟶ Rep.res jPN W) (n : ℕ)
    (v : V) (x : cellRep n) :
    ((cellPush V W φ).f n).hom (Representation.Coinvariants.mk (V.ρ.tprod (Rep.res jPN (cellRep n)).ρ) (v ⊗ₜ[ℚ] x)) =
      Representation.Coinvariants.mk (W.ρ.tprod (cellRep n).ρ) (φ.hom v ⊗ₜ[ℚ] x) := rfl

abbrev glued6 : TopCat := TopCat.of TernaryPoly.SymmetricSpaceRationalGluing.Glued

/-- The singular chains of the bordification as a resolution. -/
abbrev singRes : ProjectiveResolution (Rep.trivial ℚ principalSix ℚ) :=
  projectiveResolution principalSix glued6

/-- The bar-to-singular comparison. -/
def cellκ : barComplex ℚ principalSix ⟶ equivariantChains principalSix glued6 :=
  (resolutionHomotopyEquiv principalSix glued6).inv

theorem cellκ_aug : cellκ ≫ singRes.π =
    (barResolution ℚ principalSix).π ≫ (ChainComplex.single₀ _).map (𝟙 _) := by
  rw [(ChainComplex.single₀ _).map_id, Category.comp_id]
  exact resolutionInverse_augmentation (G := principalSix) (E := glued6)

theorem cellChainMap_aug' : cellChainMap ≫ singRes.π =
    cellResolution.π ≫ (ChainComplex.single₀ _).map (𝟙 _) := by
  rw [(ChainComplex.single₀ _).map_id, Category.comp_id]
  exact cellChainMap_aug

/-- The comparison from the bar resolution of `P_N` to the restricted cell resolution. -/
def cellα : barComplex ℚ PN ⟶ ((resFunctor.{0} (k := ℚ) jPN).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      cellResolution.complex :=
  ProjectiveResolution.lift (𝟙 (Rep.trivial ℚ PN ℚ)) (barResolution ℚ PN) cellResPN

theorem cellα_aug : cellα ≫ cellResPN.π =
    (barResolution ℚ PN).π ≫ (ChainComplex.single₀ _).map (𝟙 _) :=
  ProjectiveResolution.lift_commutes _ _ _

theorem comparison_hom_eq (W : Rep.{0} ℚ principalSix) (m : ℕ) :
    (groupCoinvariantHomologyIso principalSix glued6 W m).hom =
      HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso W).hom m ≫
        HomologicalComplex.homologyMap
          ((((coinvariantsTensor ℚ principalSix).obj W).mapHomologicalComplex (ComplexShape.down ℕ)).map
            cellκ) m := by
  have h1 : (groupCoinvariantHomologyIso principalSix glued6 W m).hom =
      HomologicalComplex.homologyMap (comparisonMap principalSix glued6 W) m := rfl
  have h2 : comparisonMap principalSix glued6 W = (groupHomology.inhomogeneousChainsIso W).hom ≫
      ((((coinvariantsTensor ℚ principalSix).obj W).mapHomologicalComplex (ComplexShape.down ℕ)).map
            cellκ) := rfl
  rw [h1, h2, HomologicalComplex.homologyMap_comp]

theorem cell_key (V : Rep.{0} ℚ PN) (W : Rep.{0} ℚ principalSix) (φ : V ⟶ Rep.res jPN W) (m : ℕ) :
    groupHomology.map jPN φ m ≫ (groupCoinvariantHomologyIso principalSix glued6 W m).hom =
      (HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso V).hom m ≫
        HomologicalComplex.homologyMap
          ((((coinvariantsTensor ℚ PN).obj V).mapHomologicalComplex (ComplexShape.down ℕ)).map cellα) m) ≫
      HomologicalComplex.homologyMap (cellPush V W φ) m ≫ HomologicalComplex.homologyMap (cellCoinvMap W) m := by
  have K := key_homology jPN cellResolution cellRes_projective singRes cellChainMap cellChainMap_aug'
    cellκ cellκ_aug cellα cellα_aug V W φ m
  simp only [HomologicalComplex.homologyMap_comp] at K
  rw [comparison_hom_eq]
  exact K.trans (by simp only [Category.assoc]; rfl)

theorem cellPush_comparison (V : Rep.{0} ℚ PN) (W : Rep.{0} ℚ principalSix) (φ : V ⟶ Rep.res jPN W) (m : ℕ) :
    HomologicalComplex.homologyMap (cellPush V W φ) m ≫ cellGroupHomologyMap W m =
      (groupHomologyIso V m cellResPN).inv ≫ groupHomology.map jPN φ m := by
  have comm : cellα.f 0 ≫ cellResPN.π.f 0 = (barResolution ℚ PN).π.f 0 := by
    have h := congrArg (fun t => t.f 0) cellα_aug
    simp only [HomologicalComplex.comp_f] at h
    rw [(ChainComplex.single₀ _).map_id, HomologicalComplex.id_f, Category.comp_id] at h
    exact h
  have h1 := groupHomologyIso_hom_comp (k := ℚ) (G := PN) V m (P := barResolution ℚ PN) (Q := cellResPN) cellα comm
  rw [groupHomologyIso_bar_hom] at h1
  have hK : groupHomology.map jPN φ m ≫ (groupCoinvariantHomologyIso principalSix glued6 W m).hom =
      (groupHomologyIso V m cellResPN).hom ≫ HomologicalComplex.homologyMap (cellPush V W φ) m ≫
        HomologicalComplex.homologyMap (cellCoinvMap W) m := by
    rw [← h1]
    exact cell_key V W φ m
  rw [cellGroupHomologyMap_eq]
  calc _ = (groupHomologyIso V m cellResPN).inv ≫ ((groupHomologyIso V m cellResPN).hom ≫
        HomologicalComplex.homologyMap (cellPush V W φ) m ≫ HomologicalComplex.homologyMap (cellCoinvMap W) m) ≫
          (groupCoinvariantHomologyIso principalSix glued6 W m).inv := by
        simp
    _ = _ := by
        rw [← hK]
        simp

/-- The homology class of a degree-three cycle. -/
def cycleClass (C : ChainComplex (ModuleCat.{0} ℚ) ℕ) (z : C.X 3) (hz : (C.d 3 2).hom z = 0) : C.homology 3 :=
  C.homologyπ 3 (C.cyclesMk z 2 next_three hz)

theorem cellClass_eq_cycleClass (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
    (hz : ((cellCoinv W).d 3 2).hom z = 0) : cellClass W z hz = cycleClass (cellCoinv W) z hz := rfl

theorem exists_cycleClass (C : ChainComplex (ModuleCat.{0} ℚ) ℕ) (y : C.homology 3) :
    ∃ (z : C.X 3) (hz : (C.d 3 2).hom z = 0), cycleClass C z hz = y := by
  obtain ⟨c, rfl⟩ := ((ModuleCat.epi_iff_surjective (C.homologyπ 3)).mp inferInstance) y
  have hz : (C.d 3 2).hom ((C.iCycles 3).hom c) = 0 := by
    have h := C.iCycles_d 3 2
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, h]
    simp
  refine ⟨(C.iCycles 3).hom c, hz, ?_⟩
  unfold cycleClass
  congr 1
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map (C.iCycles 3)) :=
    (Preadditive.mono_iff_injective (C.iCycles 3)).1 inferInstance
  apply inj
  exact HomologicalComplex.i_cyclesMk C ((C.iCycles 3).hom c) 2 next_three hz

theorem homologyMap_cycleClass {C D : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : C ⟶ D) (z : C.X 3)
    (hz : (C.d 3 2).hom z = 0) (hz' : (D.d 3 2).hom ((f.f 3).hom z) = 0) :
    (HomologicalComplex.homologyMap f 3).hom (cycleClass C z hz) = cycleClass D ((f.f 3).hom z) hz' := by
  unfold cycleClass
  have h1 := HomologicalComplex.homologyπ_naturality f 3
  have h2 := congrArg (fun t => t.hom (C.cyclesMk z 2 next_three hz)) h1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [h2]
  congr 1
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map (D.iCycles 3)) :=
    (Preadditive.mono_iff_injective (D.iCycles 3)).1 inferInstance
  apply inj
  have h3 := congrArg (fun t => t.hom (C.cyclesMk z 2 next_three hz)) (HomologicalComplex.cyclesMap_i f 3)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h3
  refine h3.trans ?_
  refine Eq.trans ?_ (HomologicalComplex.i_cyclesMk D ((f.f 3).hom z) 2 next_three hz').symm
  exact congrArg (f.f 3).hom (HomologicalComplex.i_cyclesMk C z 2 next_three hz)

theorem iotaStar_eq_cellPush (n : ℕ) (w : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    iotaStar n w =
      (cellGroupHomologyMap (Rep.res principalSix.subtype (ResRep n)) 3).hom
        ((HomologicalComplex.homologyMap
          (cellPush (Rep.res PN.subtype (FibRep n)) (Rep.res principalSix.subtype (ResRep n)) (lofN n)) 3).hom
          ((groupHomologyIso (Rep.res PN.subtype (FibRep n)) 3 cellResPN).hom.hom w)) := by
  have h := cellPush_comparison (Rep.res PN.subtype (FibRep n)) (Rep.res principalSix.subtype (ResRep n))
    (lofN n) 3
  have h2 := congrArg (fun t => t.hom ((groupHomologyIso (Rep.res PN.subtype (FibRep n)) 3 cellResPN).hom.hom w)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  refine Eq.trans ?_ h2.symm
  have h3 := congrArg (fun t => t.hom w) (Iso.hom_inv_id (groupHomologyIso (Rep.res PN.subtype (FibRep n)) 3 cellResPN))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h3
  rw [h3]
  rfl

theorem exists_cell_cycle (n : ℕ) (w : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    ∃ (ζ : (cellCoinvPN (Rep.res PN.subtype (FibRep n))).X 3)
      (_ : ((cellCoinvPN (Rep.res PN.subtype (FibRep n))).d 3 2).hom ζ = 0)
      (hz : ((cellCoinv (Rep.res principalSix.subtype (ResRep n))).d 3 2).hom
        (((cellPush (Rep.res PN.subtype (FibRep n)) (Rep.res principalSix.subtype (ResRep n)) (lofN n)).f 3).hom ζ) = 0),
      iotaStar n w = (cellGroupHomologyMap (Rep.res principalSix.subtype (ResRep n)) 3).hom
        (cellClass (Rep.res principalSix.subtype (ResRep n))
          (((cellPush (Rep.res PN.subtype (FibRep n)) (Rep.res principalSix.subtype (ResRep n)) (lofN n)).f 3).hom ζ) hz) := by
  obtain ⟨ζ, hζ, hcl⟩ := exists_cycleClass (cellCoinvPN (Rep.res PN.subtype (FibRep n)))
    ((groupHomologyIso (Rep.res PN.subtype (FibRep n)) 3 cellResPN).hom.hom w)
  have hz : ((cellCoinv (Rep.res principalSix.subtype (ResRep n))).d 3 2).hom
      (((cellPush (Rep.res PN.subtype (FibRep n)) (Rep.res principalSix.subtype (ResRep n)) (lofN n)).f 3).hom ζ) = 0 := by
    have hc := congrArg (fun t => t.hom ζ)
      ((cellPush (Rep.res PN.subtype (FibRep n)) (Rep.res principalSix.subtype (ResRep n)) (lofN n)).comm 3 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    rw [hc, hζ, map_zero]
  refine ⟨ζ, hζ, hz, ?_⟩
  rw [iotaStar_eq_cellPush, ← hcl, cellClass_eq_cycleClass,
    homologyMap_cycleClass _ ζ hζ hz]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
