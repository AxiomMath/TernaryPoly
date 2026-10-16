module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVPairing

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory HomologicalComplex
open SingularLocalCap SingularLocalCompactCap.Algebra

/-- A literal commuting square of actual bilinear Leibniz pairings induces the corresponding
square on actual homology, with no dimension or finiteness restriction. -/
theorem pairing_homology_natural {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L M N : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : C ⟶ D) (g : K ⟶ L) (h : M ⟶ N)
    (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] M.X b)
    (γ : ∀ a b, D.X a →ₗ[ℚ] L.X (a+b) →ₗ[ℚ] N.X b)
    (hβ : Descent.Leibniz C K M β) (hγ : Descent.Leibniz D L N γ)
    (hn : ∀ a b x c, h.f b (β a b x c) = γ a b (f.f a x) (g.f (a+b) c))
    (a b : ℕ) (x : C.homology a) (c : K.homology (a+b)) :
    homologyMap h b (Descent.homology C K M β hβ a b x c) =
      Descent.homology D L N γ hγ a b (homologyMap f a x) (homologyMap g (a+b) c) := by
  obtain ⟨x,rfl⟩ := cochainClass_surjective C a x
  obtain ⟨c,rfl⟩ := chainClass_surjective K (a+b) c
  let y : Homology.Cycles (D.sc' (a-1) a (a+1)) :=
    ⟨f.f a x.val,(congrArg (fun h => h x.val) (f.comm a (a+1))).trans
      ((congrArg (f.f (a+1)) x.property).trans (map_zero _))⟩
  let d : Homology.Cycles (L.sc' (a+b+1) (a+b) (a+b-1)) :=
    ⟨g.f (a+b) c.val,(congrArg (fun h => h c.val) (g.comm (a+b) (a+b-1))).trans
      ((congrArg (g.f (a+b-1)) c.property).trans (map_zero _))⟩
  rw [cochainClass_natural f a x y rfl,chainClass_natural g (a+b) c d rfl,
    Descent.homology_representatives,Descent.homology_representatives]
  apply chainClass_natural h b
  exact (hn a b x.val c.val).symm

end TernaryPoly.SingularLocalCompactCapMV
