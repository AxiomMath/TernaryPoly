module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionChainDiagram
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex
open SingularLocalCap SingularLocalCap.Homology SingularLocalCompactCap.Algebra

/-- The actual image of a genuine chain cycle under an actual chain map. -/
def mapChainCycle {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) (k : ℕ)
    (c : Cycles (K.sc' (k+1) k (k-1))) : Cycles (L.sc' (k+1) k (k-1)) :=
  ⟨f.f k c.val, by
    have h := congrArg (fun g => g c.val) (f.comm k (k-1))
    change L.d k (k-1) (f.f k c.val) = f.f (k-1) (K.d k (k-1) c.val) at h
    exact h.trans (by erw [c.property,map_zero]; rfl)⟩

/-- The actual homology class of an image cycle is the actual homology image. -/
theorem chainClass_map {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) (k : ℕ)
    (c : Cycles (K.sc' (k+1) k (k-1))) :
    homologyMap f k (Descent.chainClass K k c) = Descent.chainClass L k (mapChainCycle f k c) :=
  chainClass_natural f k c (mapChainCycle f k c) rfl

/-- Vanishing of the actual class of a genuine cycle is equivalent to being the actual
boundary of a genuine chain in the next degree. -/
theorem chainClass_zero_iff (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (k : ℕ)
    (c : Cycles (K.sc' (k+1) k (k-1))) :
    Descent.chainClass K k c = 0 ↔ ∃ b : K.X (k+1), K.d (k+1) k b = c.val := by
  let S := K.sc' (k+1) k (k-1)
  let e := S.moduleCatHomologyIso.symm ≪≫
    (K.homologyIsoSc' (k+1) k (k-1) (down_prev _) (down_next _)).symm
  constructor
  · intro h
    have hq : (Boundaries S).mkQ c = 0 := by
      apply e.toLinearEquiv.injective
      exact h.trans (map_zero _).symm
    obtain ⟨b,hb⟩ := (Submodule.Quotient.mk_eq_zero (Boundaries S)).mp hq
    exact ⟨b,congrArg Subtype.val hb⟩
  · rintro ⟨b,hb⟩
    have hq : (Boundaries S).mkQ c = 0 :=
      (Submodule.Quotient.mk_eq_zero (Boundaries S)).mpr ⟨b,Subtype.ext hb⟩
    change e.hom ((Boundaries S).mkQ c) = 0
    exact (congrArg e.hom hq).trans (map_zero _)

/-- A cycle represented by an injective actual chain inclusion lifts to a genuine cycle. -/
def liftChainCycle {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L)
    (hf : ∀ k, Function.Injective (f.f k)) (k : ℕ)
    (c : Cycles (L.sc' (k+1) k (k-1))) (x : K.X k) (hx : f.f k x = c.val) :
    Cycles (K.sc' (k+1) k (k-1)) :=
  ⟨x, by
    apply hf (k-1)
    have h := congrArg (fun g => g x) (f.comm k (k-1))
    change L.d k (k-1) (f.f k x) = f.f (k-1) (K.d k (k-1) x) at h
    exact h.symm.trans ((congrArg (L.d k (k-1)) hx).trans
      (c.property.trans (map_zero _).symm))⟩

end TernaryPoly.SingularLocalOpenUnion
