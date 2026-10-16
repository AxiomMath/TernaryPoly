module

public import TernaryPeriodPolynomials.Topology.Rational.Homology.Dual
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Homology
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Representatives
public import TernaryPeriodPolynomials.Topology.SingularLocal.DualityDetection
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapAlgebra
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Generators
public import TernaryPeriodPolynomials.Topology.SingularHomology.BarycentricSubdivisionHomotopyOperator
public import TernaryPeriodPolynomials.Topology.SingularHomology.CupProduct

@[expose] public section


/-!
# Representative-level evaluation of the Kronecker pairing

Formalized by Claude Sonnet 5.5.

* `ucS`, `ucS_apply`, `ucS_pi`: the universal coefficient isomorphism of a short complex of modules, built from
  `RationalHomologyDual` (opposite short complex, `dualFunctor`), evaluates a dual cycle on a cycle (using the
  compatibility `op_homologyπ_homologyOpIso` of Mathlib's `homologyOpIso` with `homologyπ`);
* **`uc_cochainClass_chainClass` (2a)**: for a chain complex `K` and genuine cycles `x` of `dualCochains K`, `z` of `K`:
  `UC (cochainClass x) (chainClass z) = x z`;
* **`homologyPairing_cochainClass_chainClass` (2b)**: the geometric pairing of `TernaryPoly.SingularLocalDuality`:
  `homologyPairing (cochainClass x) (chainClass z) = degreeDuality x z`;
* **`degreeDuality_degreeEquiv` / `degreeDuality_degreeEquiv_mk` (2c)**: for `a : chainRep G E b ⟶ dualRepresentation W`
  the pairing of the cochain `homVertexEquiv a` with `degreeEquiv (mk ζ)` is `TensorProduct.lift B ζ`,
  `B v s = (a s)(v)`;
* **`singularChainMap_surjective` (2d)**: pushing singular chains forward along a quotient covering is onto (every
  base simplex lifts; the map is split by the choice of lifts).
-/

open CategoryTheory Limits
open TernaryPoly.RationalHomologyDual
open TernaryPoly.SingularLocalCap.Homology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KroneckerRep

theorem piF {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (S : ShortComplex C) [S.HasHomology] [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  have h1 := ShortComplex.LeftHomologyData.mapHomologyIso_eq S.leftHomologyData F
  have h2 := ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom (S.map F) (S.leftHomologyData.map F)
  have h3 := ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom S S.leftHomologyData
  have e : (S.mapHomologyIso F).hom = (S.leftHomologyData.map F).homologyIso.hom ≫
      F.map S.leftHomologyData.homologyIso.inv := congrArg Iso.hom h1
  have hid : S.leftHomologyData.cyclesIso.hom = 𝟙 _ := by
    simp [ShortComplex.LeftHomologyData.cyclesIso]
    rfl
  have h3' : S.homologyπ ≫ S.leftHomologyData.homologyIso.hom = S.leftHomologyData.π :=
    h3.trans (by rw [hid]; exact Category.id_comp _)
  have h4 : S.leftHomologyData.π ≫ S.leftHomologyData.homologyIso.inv = S.homologyπ :=
    (Iso.comp_inv_eq _).2 h3'.symm
  have h5 : (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      ((S.leftHomologyData.map F).cyclesIso.hom ≫ F.map S.leftHomologyData.π) ≫
        F.map S.leftHomologyData.homologyIso.inv := by
    rw [e]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun m => m ≫ F.map S.leftHomologyData.homologyIso.inv) h2)
  refine h5.trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m => (S.leftHomologyData.map F).cyclesIso.hom ≫ m)
    ((F.map_comp S.leftHomologyData.π S.leftHomologyData.homologyIso.inv).symm.trans
      (congrArg F.map h4)))

theorem op_homologyπ_homologyOpIso {C : Type*} [Category C] [Abelian C] (S : ShortComplex C) [S.HasHomology] :
    S.op.homologyπ ≫ S.homologyOpIso.hom = S.cyclesOpIso.hom ≫ S.homologyι.op := by
  dsimp only [ShortComplex.homologyOpIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [ShortComplex.homologyπ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h := ShortComplex.LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom S.rightHomologyData.op
  refine (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ S.rightHomologyIso.symm.op.hom) h).trans ?_)
  exact Category.assoc _ _ _

/-- The universal coefficient isomorphism of a short complex of modules. -/
def ucS (S : ShortComplex (ModuleCat.{0} ℚ)) : (S.op.map dualFunctor).homology ≅ dualFunctor.obj (Opposite.op S.homology) :=
  (S.op.mapHomologyIso dualFunctor) ≪≫ dualFunctor.mapIso S.homologyOpIso

theorem ucS_pi (S : ShortComplex (ModuleCat.{0} ℚ)) (wφ : (S.op.map dualFunctor).cycles) (wc : S.cycles) :
    (show Module.Dual ℚ S.homology from (ucS S).hom.hom ((S.op.map dualFunctor).homologyπ.hom wφ))
        (S.homologyπ.hom wc) =
      (show Module.Dual ℚ S.X₂ from (S.op.map dualFunctor).iCycles.hom wφ) (S.iCycles.hom wc) := by
  have hpi := congrArg (fun t => t.hom wφ) (piF dualFunctor S.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hpi
  have hmap : ∀ {A B : (ModuleCat.{0} ℚ)ᵒᵖ} (f : A ⟶ B) (l : Module.Dual ℚ A.unop) (x : B.unop),
      (show Module.Dual ℚ B.unop from (dualFunctor.map f).hom l) x = l (f.unop.hom x) := fun f l x => rfl
  have h1 : (show Module.Dual ℚ S.homology from (ucS S).hom.hom ((S.op.map dualFunctor).homologyπ.hom wφ))
        (S.homologyπ.hom wc) =
      (show Module.Dual ℚ S.op.cycles.unop from (S.op.mapCyclesIso dualFunctor).hom.hom wφ)
        ((S.op.homologyπ ≫ S.homologyOpIso.hom).unop.hom (S.homologyπ.hom wc)) := by
    change (show Module.Dual ℚ S.homology from (dualFunctor.map S.homologyOpIso.hom).hom
      ((S.op.mapHomologyIso dualFunctor).hom.hom ((S.op.map dualFunctor).homologyπ.hom wφ))) (S.homologyπ.hom wc) = _
    rw [hpi]
    rfl
  have h2 := op_homologyπ_homologyOpIso S
  have h3 : (S.op.homologyπ ≫ S.homologyOpIso.hom).unop.hom (S.homologyπ.hom wc) =
      S.cyclesOpIso.hom.unop.hom (S.pOpcycles.hom (S.iCycles.hom wc)) := by
    rw [h2]
    have := congrArg (fun t => t.hom wc) S.homology_π_ι
    exact congrArg (fun y => S.cyclesOpIso.hom.unop.hom y) this
  have e0 : S.op.iCycles = S.cyclesOpIso.hom ≫ S.pOpcycles.op := (Iso.inv_comp_eq _).1 S.cyclesOpIso_inv_op_iCycles
  have e1 : S.pOpcycles ≫ S.cyclesOpIso.hom.unop = S.op.iCycles.unop := by
    rw [e0]; rfl
  have h4 : S.cyclesOpIso.hom.unop.hom (S.pOpcycles.hom (S.iCycles.hom wc)) =
      S.op.iCycles.unop.hom (S.iCycles.hom wc) := congrArg (fun t => t.hom (S.iCycles.hom wc)) e1
  have h5 : (dualFunctor.map S.op.iCycles).hom ((S.op.mapCyclesIso dualFunctor).hom.hom wφ) =
      (S.op.map dualFunctor).iCycles.hom wφ := by
    have := congrArg (fun t => t.hom wφ) (ShortComplex.mapCyclesIso_hom_iCycles (S := S.op) dualFunctor)
    exact this
  rw [h1, h3, h4]
  have h6 := hmap S.op.iCycles ((S.op.mapCyclesIso dualFunctor).hom.hom wφ) (S.iCycles.hom wc)
  refine h6.symm.trans ?_
  rw [h5]
  rfl

theorem ucS_apply (S : ShortComplex (ModuleCat.{0} ℚ)) (φ : Cycles (S.op.map dualFunctor)) (c : Cycles S) :
    (show Module.Dual ℚ S.homology from (ucS S).hom.hom (cycleClass (S.op.map dualFunctor) φ)) (cycleClass S c) =
      (show Module.Dual ℚ S.X₂ from φ.val) c.val := by
  have hcls : ∀ (T : ShortComplex (ModuleCat.{0} ℚ)) (z : Cycles T),
      cycleClass T z = T.homologyπ.hom (T.moduleCatCyclesIso.inv.hom z) := by
    intro T z
    have := congrArg (fun t => t.hom z) T.moduleCatCyclesIso_inv_π
    exact this.symm
  have hiφ : (S.op.map dualFunctor).iCycles.hom ((S.op.map dualFunctor).moduleCatCyclesIso.inv.hom φ) = φ.val := by
    have := congrArg (fun t => t.hom φ) (S.op.map dualFunctor).moduleCatCyclesIso_inv_iCycles
    exact this
  have hic : S.iCycles.hom (S.moduleCatCyclesIso.inv.hom c) = c.val := by
    have := congrArg (fun t => t.hom c) S.moduleCatCyclesIso_inv_iCycles
    exact this
  rw [hcls, hcls]
  refine (ucS_pi S _ _).trans ?_
  rw [hiφ, hic]

open TernaryPoly.SingularLocalCap.Descent in
theorem uc_eq_ucS (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) :
    universalCoefficientIso K n = ucS (K.sc n) := rfl

open TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCap.Descent in
/-- **(2a)** The universal coefficient isomorphism evaluates the cochain cycle on the chain cycle. -/
theorem uc_cochainClass_chainClass (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (x : Cycles ((dualCochains K).sc' (n-1) n (n+1))) (z : Cycles (K.sc' (n+1) n (n-1))) :
    (show Module.Dual ℚ (K.homology n) from
        (universalCoefficientIso K n).hom.hom (cochainClass (dualCochains K) n x)) (chainClass K n z) =
      (show Module.Dual ℚ (K.X n) from x.val) z.val := by
  have hcls : ∀ (T : ShortComplex (ModuleCat.{0} ℚ)) (z : Cycles T),
      TernaryPoly.SingularLocalCap.Homology.cycleClass T z = T.homologyπ.hom (T.moduleCatCyclesIso.inv.hom z) := by
    intro T z
    have := congrArg (fun t => t.hom z) T.moduleCatCyclesIso_inv_π
    exact this.symm
  have hx : cochainClass (dualCochains K) n x = ((dualCochains K).homologyπ n).hom
      (((dualCochains K).cyclesIsoSc' (n-1) n (n+1) (up_prev _) (up_next _)).inv.hom
        (((dualCochains K).sc' (n-1) n (n+1)).moduleCatCyclesIso.inv.hom x)) := by
    unfold cochainClass
    rw [hcls]
    have := congrArg (fun t => t.hom (((dualCochains K).sc' (n-1) n (n+1)).moduleCatCyclesIso.inv.hom x))
      ((dualCochains K).π_homologyIsoSc'_inv (n-1) n (n+1) (up_prev _) (up_next _))
    exact this
  have hz : chainClass K n z = (K.homologyπ n).hom
      ((K.cyclesIsoSc' (n+1) n (n-1) (down_prev _) (down_next _)).inv.hom
        ((K.sc' (n+1) n (n-1)).moduleCatCyclesIso.inv.hom z)) := by
    unfold chainClass
    rw [hcls]
    have := congrArg (fun t => t.hom ((K.sc' (n+1) n (n-1)).moduleCatCyclesIso.inv.hom z))
      (K.π_homologyIsoSc'_inv (n+1) n (n-1) (down_prev _) (down_next _))
    exact this
  rw [hx, hz]
  set u := ((dualCochains K).cyclesIsoSc' (n-1) n (n+1) (up_prev _) (up_next _)).inv.hom
    (((dualCochains K).sc' (n-1) n (n+1)).moduleCatCyclesIso.inv.hom x) with hu
  set v := (K.cyclesIsoSc' (n+1) n (n-1) (down_prev _) (down_next _)).inv.hom
    ((K.sc' (n+1) n (n-1)).moduleCatCyclesIso.inv.hom z) with hv
  have hiu : ((dualCochains K).iCycles n).hom u = x.val := by
    have h1 := congrArg (fun t => t.hom (((dualCochains K).sc' (n-1) n (n+1)).moduleCatCyclesIso.inv.hom x))
      ((dualCochains K).cyclesIsoSc'_inv_iCycles (n-1) n (n+1) (up_prev _) (up_next _))
    have h2 := congrArg (fun t => t.hom x) ((dualCochains K).sc' (n-1) n (n+1)).moduleCatCyclesIso_inv_iCycles
    exact h1.trans h2
  have hiv : (K.iCycles n).hom v = z.val := by
    have h1 := congrArg (fun t => t.hom ((K.sc' (n+1) n (n-1)).moduleCatCyclesIso.inv.hom z))
      (K.cyclesIsoSc'_inv_iCycles (n+1) n (n-1) (down_prev _) (down_next _))
    have h2 := congrArg (fun t => t.hom z) (K.sc' (n+1) n (n-1)).moduleCatCyclesIso_inv_iCycles
    exact h1.trans h2
  have key := ucS_pi (K.sc n) u v
  change (show Module.Dual ℚ (K.homology n) from (ucS (K.sc n)).hom.hom
    ((((dualCochains K).sc n).homologyπ).hom u)) ((K.sc n).homologyπ.hom v) = _
  refine key.trans ?_
  change (show Module.Dual ℚ (K.X n) from ((dualCochains K).iCycles n).hom u) ((K.iCycles n).hom v) = _
  rw [hiu, hiv]

section Local

open TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCap.Descent TernaryPoly.SingularLocalDuality
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalCompactCap.Algebra
open scoped Classical

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

/-- **(2b)** The geometric pairing evaluates the dual cochain on the chain. -/
theorem homologyPairing_cochainClass_chainClass (n : ℕ)
    (x : Cycles ((localCochains p hp (dualRepresentation V)).sc' (n-1) n (n+1)))
    (z : Cycles ((localChains p hp V).sc' (n+1) n (n-1))) :
    homologyPairing p hp V n (cochainClass _ n x) (chainClass _ n z) = degreeDuality p hp V n x.val z.val := by
  let f := (cochainDuality p hp V).hom
  have hy : ((localChains p hp V).sc' (n+1) n (n-1)).X₂ = (localChains p hp V).X n := rfl
  let y : Cycles ((TernaryPoly.RationalHomologyDual.dualCochains (localChains p hp V)).sc' (n-1) n (n+1)) :=
    ⟨f.f n x.val, by
      have h := congrArg (fun t => t.hom x.val) (f.comm n (n+1))
      have hx : ((localCochains p hp (dualRepresentation V)).d n (n+1)).hom x.val = 0 := x.property
      change ((TernaryPoly.RationalHomologyDual.dualCochains (localChains p hp V)).d n (n+1)).hom (f.f n x.val) = 0
      have h' : ((TernaryPoly.RationalHomologyDual.dualCochains (localChains p hp V)).d n (n+1)).hom (f.f n x.val) =
          (f.f (n+1)).hom (((localCochains p hp (dualRepresentation V)).d n (n+1)).hom x.val) := by
        exact h
      rw [h', hx, map_zero]⟩
  have h1 : HomologicalComplex.homologyMap f n (cochainClass _ n x) = cochainClass _ n y :=
    cochainClass_natural f n x y rfl
  have h2 := uc_cochainClass_chainClass (localChains p hp V) n y z
  change (show Module.Dual ℚ ((localChains p hp V).homology n) from
      (TernaryPoly.RationalHomologyDual.universalCoefficientIso (localChains p hp V) n).hom.hom
        (HomologicalComplex.homologyMap f n (cochainClass _ n x))) (chainClass _ n z) = _
  rw [h1]
  exact h2

end Local


section Coinv

open TernaryPoly TernaryPoly.SingularLocalDuality TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalHomology
  TernaryPoly.EquivariantSingularResolution TernaryPoly.CoveringSingularOrbits TernaryPoly.FreeActionLinearization
  TernaryPoly.SingularLocalCap.Descent
open scoped Classical TensorProduct

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (W : Rep.{0} ℚ G) (b : ℕ)
  (a : chainRep G E b ⟶ dualRepresentation W)

/-- The pairing `W × chainRep → ℚ` given by `a`. -/
def pairB : W →ₗ[ℚ] (chainRep G E b) →ₗ[ℚ] ℚ :=
  LinearMap.flip (show (chainRep G E b) →ₗ[ℚ] Module.Dual ℚ W from a.hom.toLinearMap)

theorem pairB_apply (w : W) (s : chainRep G E b) : pairB W b a w s = dualValue (a.hom s) w := rfl

theorem pairB_invariant (g : G) (w : W) (s : chainRep G E b) :
    pairB W b a (W.ρ g w) ((chainRep G E b).ρ g s) = pairB W b a w s := by
  rw [pairB_apply, pairB_apply]
  have h : a.hom ((chainRep G E b).ρ g s) = (dualRepresentation W).ρ g (a.hom s) := Rep.hom_comm_apply a g s
  rw [h, dualRepresentation_apply]
  have : g⁻¹ • (W.ρ g w) = w := by
    change W.ρ g⁻¹ (W.ρ g w) = w
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  rw [this]

/-- The functional on coinvariant chains induced by the pairing. -/
def pairLam : (coinvariantChains G E W).X b →ₗ[ℚ] ℚ :=
  Representation.Coinvariants.lift (W.ρ.tprod (chainRep G E b).ρ) (TensorProduct.lift (pairB W b a)) (fun g => by
    refine TensorProduct.ext' fun w s => ?_
    change TensorProduct.lift (pairB W b a) (W.ρ g w ⊗ₜ[ℚ] (chainRep G E b).ρ g s) =
      TensorProduct.lift (pairB W b a) (w ⊗ₜ[ℚ] s)
    rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul]
    exact pairB_invariant W b a g w s)

variable [IsCancelSMul G E]

theorem pairing_single (σ : SingularSimplex B b)
    (c : FiberCoefficient p hp W (atVertex σ)) (τ : Lifts p σ) :
    degreeDuality p hp W b (homVertexEquiv p hp (dualRepresentation W) b a) (DFinsupp.single σ c) =
      pairLam W b a ((degreeEquiv p hp W b).symm (DFinsupp.single σ c)) := by
  rw [degreeDuality_single_at p hp W b _ σ c (liftVertexEquiv p hp σ τ),
    degreeEquiv_symm_single_lift p hp W b τ c, homVertexEquiv_lift p hp (dualRepresentation W) b a τ]
  rfl

/-- **(2c)** The geometric pairing of the dual cochain with the coinvariant chain is the induced functional. -/
theorem degreeDuality_degreeEquiv (c : (coinvariantChains G E W).X b) :
    degreeDuality p hp W b (homVertexEquiv p hp (dualRepresentation W) b a) (degreeEquiv p hp W b c) =
      pairLam W b a c := by
  have h : (degreeDuality p hp W b (homVertexEquiv p hp (dualRepresentation W) b a)) =
      (pairLam W b a) ∘ₗ (degreeEquiv p hp W b).symm.toLinearMap := by
    apply DFinsupp.lhom_ext
    intro σ cc
    obtain ⟨τ, hτ⟩ := (chosenLift p hp b σ)
    exact pairing_single p hp W b a σ cc ⟨τ, hτ⟩
  have := LinearMap.congr_fun h (degreeEquiv p hp W b c)
  simpa using this

/-- **(2c)**, on a representative of the coinvariant class. -/
theorem degreeDuality_degreeEquiv_mk (ζ : W ⊗[ℚ] chainRep G E b) :
    degreeDuality p hp W b (homVertexEquiv p hp (dualRepresentation W) b a)
      (degreeEquiv p hp W b (Representation.Coinvariants.mk (W.ρ.tprod (chainRep G E b).ρ) ζ)) =
      TensorProduct.lift (pairB W b a) ζ := by
  exact degreeDuality_degreeEquiv p hp W b a (Representation.Coinvariants.mk (W.ρ.tprod (chainRep G E b).ρ) ζ)

end Coinv



section Surj

open TernaryPoly TernaryPoly.SingularLocalHomology TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open scoped Classical

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)

omit [IsCancelSMul G E] in
include hp in
/-- **(2d)** Pushing singular chains of a quotient covering forward is surjective. -/
theorem singularChainMap_surjective (n : ℕ) : Function.Surjective (singularChainMap ℚ p n).hom := by
  let s : singularSimplices B n → singularSimplices E n := fun σ => (chosenLift p hp n σ).val
  have hs : ∀ σ, pushSimplex p n (s σ) = σ := fun σ => (chosenLift p hp n σ).property
  let ιE : ∀ τ : singularSimplices E n, ModuleCat.of ℚ ℚ ⟶ singularChainGroup ℚ E n := fun τ =>
    Sigma.ι (fun _ : singularSimplices E n => ModuleCat.of ℚ ℚ) τ
  let g : singularChainGroup ℚ B n ⟶ singularChainGroup ℚ E n := Limits.Sigma.desc (fun σ => ιE (s σ))
  have hg : g ≫ singularChainMap ℚ p n = 𝟙 _ := by
    refine Limits.Sigma.hom_ext _ _ (fun σ => ?_)
    have h1 : Sigma.ι (fun _ : singularSimplices B n => ModuleCat.of ℚ ℚ) σ ≫ g = ιE (s σ) :=
      Limits.Sigma.ι_comp_desc _ σ
    refine ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ singularChainMap ℚ p n) h1)).trans ?_
    refine (chainmap_generator (R := ℚ) p n (s σ)).trans ?_
    exact (congrArg (fun τ => Sigma.ι (fun _ : singularSimplices B n => ModuleCat.of ℚ ℚ) τ) (hs σ)).trans
      (Category.comp_id _).symm
  intro y
  exact ⟨g.hom y, congrArg (fun t => t.hom y) hg⟩

end Surj


end TernaryPeriodPolynomials.Argument.KroneckerRep
