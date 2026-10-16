module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Descent

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap.Descent
open CategoryTheory Homology

variable (C : CochainComplex (ModuleCat.{0} ℚ) ℕ)
  (K L : ChainComplex (ModuleCat.{0} ℚ) ℕ)
  (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b)
  (hβ : Leibniz C K L β)

/-- The descended actual homology operation agrees with the concrete cap on every pair of cycle representatives. -/
theorem homologySC_cycleClass (a b : ℕ) (x : Cycles (C.sc' (a-1) a (a+1)))
    (c : Cycles (K.sc' (a+b+1) (a+b) (a+b-1))) :
    homologySC C K L β hβ a b (cycleClass _ x) (cycleClass _ c) =
      cycleClass _ (⟨β a b x.val c.val,cycles C K L β hβ a b x c⟩ :
        Cycles (L.sc' (b+1) b (b-1))) := by
  unfold homologySC induced
  exact descend_cycleClass _ _ _ _ _ _ x c

/-- A genuine cochain cycle represents its actual cohomology class. -/
def cochainClass (a : ℕ) (x : Cycles (C.sc' (a-1) a (a+1))) : C.homology a :=
  (C.homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).inv (cycleClass _ x)

/-- A genuine chain cycle represents its actual homology class. -/
def chainClass (n : ℕ) (x : Cycles (K.sc' (n+1) n (n-1))) : K.homology n :=
  (K.homologyIsoSc' (n+1) n (n-1) (down_prev _) (down_next _)).inv (cycleClass _ x)

/-- Exact representative formula for the operation on the actual full-complex homology objects. -/
theorem homology_representatives (a b : ℕ) (x : Cycles (C.sc' (a-1) a (a+1)))
    (c : Cycles (K.sc' (a+b+1) (a+b) (a+b-1))) :
    homology C K L β hβ a b (cochainClass C a x) (chainClass K (a+b) c) =
      chainClass L b ⟨β a b x.val c.val,cycles C K L β hβ a b x c⟩ := by
  unfold homology cochainClass chainClass
  erw [LinearMap.compr₂_apply,LinearMap.comp_apply,LinearMap.compl₂_apply]
  have hx : (C.homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).hom
      ((C.homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).inv (cycleClass _ x)) = cycleClass _ x :=
    congrArg (fun f => f (cycleClass _ x))
      (C.homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).inv_hom_id
  have hc : (K.homologyIsoSc' (a+b+1) (a+b) (a+b-1) (down_prev _) (down_next _)).hom
      ((K.homologyIsoSc' (a+b+1) (a+b) (a+b-1) (down_prev _) (down_next _)).inv (cycleClass _ c)) = cycleClass _ c :=
    congrArg (fun f => f (cycleClass _ c))
      (K.homologyIsoSc' (a+b+1) (a+b) (a+b-1) (down_prev _) (down_next _)).inv_hom_id
  erw [hx,hc,homologySC_cycleClass]

end TernaryPoly.SingularLocalCap.Descent
