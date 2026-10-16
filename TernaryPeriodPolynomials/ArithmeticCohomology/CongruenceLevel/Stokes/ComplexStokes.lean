module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.Stokes

@[expose] public section


/-!
# The complex-valued cone pairing and Stokes with the literal complex dual

Formalized by Claude Sonnet 5.5.

`ConeStokes` is stated for rational representations `V` of `Γ(6)` and the rational dual `dualRepresentation V`, pairing into `ℚ`.  The coefficient module of the
paper is complex: `E` is a complex representation and `E^*` its complex-linear dual (contragredient).  Here:

* `qRep ρ`: the rational representation underlying a complex representation `ρ` of `Γ(6)`;
* `evalC ρ : qRep ρ ⊗ qRep ρ.dual ⟶ trivial ℂ`: the evaluation `v ⊗ f ↦ f v` of `E` against the complex dual `E^*`;
* `dualEmb r : qRep ρ.dual ⟶ dualRepresentation (qRep ρ)`, `f ↦ r ∘ f`, for a rational-linear functional `r : ℂ → ℚ`, and `rHom r : trivial ℂ ⟶ 𝟙`,
  with `dualEmb_eval : (𝟙 ⊗ dualEmb r) ≫ evalRep = evalC ≫ rHom r`;
* `conePairC`: the complex-valued cone pairing, with `r (conePairC ..) = conePair ..`;
* `cone_stokes_complex`: Stokes for a complex coefficient module and its literal complex dual.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.SingularLocalDuality (dualRepresentation dualValue)
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open GeneralEisenstein
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section NaturalLifts

variable {W W' : Rep.{0} ℚ Γ6}

theorem lineCone_comp (g : W ⟶ W') (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W) :
    lineCone w z ≫ g = lineCone (w ≫ g) (z ≫ g) := by
  apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W' 1).injective
  rw [coneCoords, coneCoords]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change modelPush.iA 1 ≫ lineCone w z ≫ g = modelPush.iA 1 ≫ lineCone (w ≫ g) (z ≫ g)
    rw [← Category.assoc, lineCone_corner, lineCone_corner]
  · change modelPush.iL 2 ≫ lineCone w z ≫ g = modelPush.iL 2 ≫ lineCone (w ≫ g) (z ≫ g)
    rw [← Category.assoc, lineCone_line, lineCone_line]
  · change modelPush.iP 2 ≫ lineCone w z ≫ g = modelPush.iP 2 ≫ lineCone (w ≫ g) (z ≫ g)
    rw [← Category.assoc, lineCone_plane, lineCone_plane, zero_comp]

theorem planeCone_comp (g : W ⟶ W') (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W) :
    planeCone w z ≫ g = planeCone (w ≫ g) (z ≫ g) := by
  apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom W' 1).injective
  rw [coneCoords, coneCoords]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change modelPush.iA 1 ≫ planeCone w z ≫ g = modelPush.iA 1 ≫ planeCone (w ≫ g) (z ≫ g)
    rw [← Category.assoc, planeCone_corner, planeCone_corner, Preadditive.neg_comp]
  · change modelPush.iL 2 ≫ planeCone w z ≫ g = modelPush.iL 2 ≫ planeCone (w ≫ g) (z ≫ g)
    rw [← Category.assoc, planeCone_line, planeCone_line, zero_comp]
  · change modelPush.iP 2 ≫ planeCone w z ≫ g = modelPush.iP 2 ≫ planeCone (w ≫ g) (z ≫ g)
    rw [← Category.assoc, planeCone_plane, planeCone_plane]

end NaturalLifts

section Complex

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  {G : Type} [Group G] (ι : Γ6 →* G) (ρ : Representation ℂ G V)

/-- The rational representation of `Γ(6)` underlying the restriction along `ι : Γ(6) → G` of a complex representation of `G`. -/
def qRepr : Representation ℚ Γ6 V where
  toFun γ := (ρ (ι γ)).restrictScalars ℚ
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

/-- The rational representation of `Γ(6)` underlying a complex representation of `G` (along `ι`), as an object of `Rep ℚ Γ(6)`. -/
def qRep : Rep.{0} ℚ Γ6 := Rep.of (qRepr ι ρ)

/-- The ℚ-bilinear evaluation of the complex dual on `V`. -/
def evalBilinC : V →ₗ[ℚ] Module.Dual ℂ V →ₗ[ℚ] ℂ :=
  LinearMap.mk₂ ℚ (fun v f => f v) (fun v v' f => map_add f v v')
    (fun q v f => by
      change f (q • v) = q • f v
      rw [← algebraMap_smul ℂ q v, map_smul, algebraMap_smul])
    (fun v f f' => rfl)
    (fun q v f => rfl)

/-- The evaluation of `E` against its complex-linear dual `E^*`, with values in the trivial module `ℂ`. -/
def evalC : qRep ι ρ ⊗ qRep ι ρ.dual ⟶ Rep.trivial ℚ Γ6 ℂ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ (Representation.trivial ℚ Γ6 ℂ)
    (TensorProduct.lift (evalBilinC (V := V)))
    (fun g x => by
      have key : ∀ (f : Module.Dual ℂ V) (v : V), (ρ.dual (ι g) f) (ρ (ι g) v) = f v := by
        intro f v
        have h : (ρ.dual (ι g) f) (ρ (ι g) v) = f (ρ (ι g)⁻¹ (ρ (ι g) v)) := rfl
        rw [h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul v f => exact key f v))

/-- A rational-linear functional on `ℂ` as a morphism from the trivial module `ℂ` to the trivial module `ℚ`. -/
def rHom (r : ℂ →ₗ[ℚ] ℚ) : Rep.trivial ℚ Γ6 ℂ ⟶ 𝟙_ (Rep.{0} ℚ Γ6) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ (Representation.trivial ℚ Γ6 ℚ) r
    (fun _ _ => rfl))

/-- `f ↦ r ∘ f`, the embedding of the complex dual into the rational dual determined by a rational functional `r` on `ℂ`. -/
def dualEmbLin (r : ℂ →ₗ[ℚ] ℚ) : Module.Dual ℂ V →ₗ[ℚ] Module.Dual ℚ V where
  toFun f := r ∘ₗ f.restrictScalars ℚ
  map_add' f f' := by ext v; simp
  map_smul' q f := by ext v; simp

/-- The embedding `E^* ↪ (E_ℚ)^*` given by a rational functional `r` on `ℂ`, as a morphism of `Γ(6)`-modules. -/
def dualEmb (r : ℂ →ₗ[ℚ] ℚ) : qRep ι ρ.dual ⟶ dualRepresentation (qRep ι ρ) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (dualEmbLin (V := V) r)
    (fun g f => by
      apply LinearMap.ext
      intro v
      change r ((ρ.dual (ι g) f) v) = r (f (ρ (ι g⁻¹) v))
      rw [map_inv]
      rfl))

theorem dualEmb_eval (r : ℂ →ₗ[ℚ] ℚ) :
    (𝟙 (qRep ι ρ) ⊗ₘ dualEmb ι ρ r) ≫ evalRep (qRep ι ρ) = evalC ι ρ ≫ rHom r := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro v f
  change (evalRep (qRep ι ρ)).hom (((𝟙 (qRep ι ρ) ⊗ₘ dualEmb ι ρ r)).hom (v ⊗ₜ[ℚ] f)) =
    r ((show Module.Dual ℂ V from f) v)
  rw [tensorHom_hom_tmul, evalRep_tmul]
  rfl

end Complex

section ConePairC

variable {W W' : Rep.{0} ℚ Γ6}

/-- The complex-valued cone pairing of two degree-two cone cochains on a chain `v` of the model cone. -/
def conePairC (π : W ⊗ W' ⟶ Rep.trivial ℚ Γ6 ℂ) (v : coneR.X 4)
    (X : coneR.X 2 ⟶ W) (Y : coneR.X 2 ⟶ W') : ℂ :=
  ((modelDiagSystem.Δ 2 2 4 rfl) ≫ (X ⊗ₘ Y) ≫ π).hom v

theorem rHom_conePairC (r : ℂ →ₗ[ℚ] ℚ) (π : W ⊗ W' ⟶ Rep.trivial ℚ Γ6 ℂ) (v : coneR.X 4)
    (X : coneR.X 2 ⟶ W) (Y : coneR.X 2 ⟶ W') :
    r (conePairC π v X Y) = conePair (π ≫ rHom r) v X Y := rfl

theorem conePairC_add_left (π : W ⊗ W' ⟶ Rep.trivial ℚ Γ6 ℂ) (v : coneR.X 4)
    (X X' : coneR.X 2 ⟶ W) (Y : coneR.X 2 ⟶ W') :
    conePairC π v (X + X') Y = conePairC π v X Y + conePairC π v X' Y := by
  unfold conePairC
  rw [MonoidalPreadditive.add_tensor, Preadditive.add_comp, Preadditive.comp_add]
  rfl

theorem conePairC_add_right (π : W ⊗ W' ⟶ Rep.trivial ℚ Γ6 ℂ) (v : coneR.X 4)
    (X : coneR.X 2 ⟶ W) (Y Y' : coneR.X 2 ⟶ W') :
    conePairC π v X (Y + Y') = conePairC π v X Y + conePairC π v X Y' := by
  unfold conePairC
  rw [MonoidalPreadditive.tensor_add, Preadditive.add_comp, Preadditive.comp_add]
  rfl

/-- A complex number is zero if every rational-linear functional vanishes on it. -/
theorem eq_zero_of_forall_rat_functional {z : ℂ} (h : ∀ r : ℂ →ₗ[ℚ] ℚ, r z = 0) : z = 0 :=
  (Module.forall_dual_apply_eq_zero_iff ℚ z).mp h

end ConePairC

section StokesC

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  {G : Type} [Group G] (ι : Γ6 →* G) (ρ : Representation ℂ G V)

theorem conePair_dualEmb (r : ℂ →ₗ[ℚ] ℚ) (Ω : coneR.X 4) (X : coneR.X 2 ⟶ qRep ι ρ)
    (Y : coneR.X 2 ⟶ qRep ι ρ.dual) :
    conePair (evalRep (qRep ι ρ)) Ω X (Y ≫ dualEmb ι ρ r) = r (conePairC (evalC ι ρ) Ω X Y) := by
  rw [rHom_conePairC, ← dualEmb_eval]
  unfold conePair
  have h : X ⊗ₘ (Y ≫ dualEmb ι ρ r) = (X ⊗ₘ Y) ≫ (𝟙 (qRep ι ρ) ⊗ₘ dualEmb ι ρ r) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  rw [h]
  simp only [Category.assoc]

/-- **Lemma `ar:lem:stokes` at level `Γ(6)`, in cone form, for a complex coefficient module and its literal complex dual.** -/
theorem cone_stokes_complex : ∃ Ω : coneR.X 4, IsCoinvCycle Ω ∧
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
      {G : Type} [Group G] (ι : Γ6 →* G) (ρ : Representation ℂ G V)
      (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ qRep ι ρ)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
      (f' : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ qRep ι ρ.dual)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f' = 0)
      (w : A.X 1 ⟶ qRep ι ρ) (_ : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f)
      (w' : A.X 1 ⟶ qRep ι ρ.dual) (_ : A.d 2 1 ≫ w' = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f'),
      conePairC (evalC ι ρ) Ω (lineCone w ((ptMap Line).f 2 ≫ f)) (lineCone w' ((ptMap Line).f 2 ≫ f')) +
        conePairC (evalC ι ρ) Ω (planeCone w ((ptMap Plane).f 2 ≫ f))
          (planeCone w' ((ptMap Plane).f 2 ≫ f')) = 0 := by
  obtain ⟨Ω, hΩ, H⟩ := cone_stokes
  refine ⟨Ω, hΩ, fun {V} _ _ _ _ {G} _ ι ρ f hf f' hf' w hw w' hw' => ?_⟩
  apply eq_zero_of_forall_rat_functional
  intro r
  have h := H (V := qRep ι ρ) f hf (f' ≫ dualEmb ι ρ r) (by rw [← Category.assoc, hf', zero_comp]) w hw
    (w' ≫ dualEmb ι ρ r) (by rw [← Category.assoc, hw']; simp only [Category.assoc])
  have e1 : lineCone (w' ≫ dualEmb ι ρ r) ((ptMap Line).f 2 ≫ f' ≫ dualEmb ι ρ r) =
      lineCone w' ((ptMap Line).f 2 ≫ f') ≫ dualEmb ι ρ r := by
    rw [lineCone_comp, Category.assoc]
  have e2 : planeCone (w' ≫ dualEmb ι ρ r) ((ptMap Plane).f 2 ≫ f' ≫ dualEmb ι ρ r) =
      planeCone w' ((ptMap Plane).f 2 ≫ f') ≫ dualEmb ι ρ r := by
    rw [planeCone_comp, Category.assoc]
  rw [e1, e2, conePair_dualEmb, conePair_dualEmb] at h
  rw [map_add]
  exact h

end StokesC

end TernaryPeriodPolynomials.Argument.GammaNStokes
