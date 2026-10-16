module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVSign
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex
open SingularLocalCap SingularLocalCompactCap.Algebra

/-- Pull a genuine cap pairing back through actual cochain and scalar-chain maps. -/
def pullPairing {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : C ⟶ D) (g : K ⟶ L)
    (β : ∀ a b, D.X a →ₗ[ℚ] L.X (a+b) →ₗ[ℚ] M.X b) (a b : ℕ) :
    C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] M.X b :=
  ((β a b).compl₂ (g.f (a+b)).hom).comp (f.f a).hom

/-- The exact Leibniz convention survives actual cochain and scalar-chain pullbacks. -/
theorem pullPairing_leibniz {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : C ⟶ D) (g : K ⟶ L)
    (β : ∀ a b, D.X a →ₗ[ℚ] L.X (a+b) →ₗ[ℚ] M.X b)
    (hβ : Descent.Leibniz D L M β) : Descent.Leibniz C K M (pullPairing f g β) := by
  intro a b x c
  change β a b (f.f a x) (g.f (a+b) (K.d (a+b+1) (a+b) c)) =
    β (a+1) b (f.f (a+1) (C.d a (a+1) x))
      (g.f (a+1+b) ((Descent.castLeft K a b).hom c)) +
        (-1 : ℤ)^a • M.d (b+1) b (β a (b+1) (f.f a x) (g.f (a+b+1) c))
  have hg := congrArg (fun h => h c) (g.comm (a+b+1) (a+b))
  have hf := congrArg (fun h => h x) (f.comm a (a+1))
  have ht := congrArg (fun h => h c) (XIsoOfEq_hom_naturality g (show a+b+1 = a+1+b by omega))
  change L.d (a+b+1) (a+b) (g.f (a+b+1) c) = g.f (a+b) (K.d (a+b+1) (a+b) c) at hg
  change D.d a (a+1) (f.f a x) = f.f (a+1) (C.d a (a+1) x) at hf
  change (Descent.castLeft L a b).hom (g.f (a+b+1) c) =
    g.f (a+1+b) ((Descent.castLeft K a b).hom c) at ht
  rw [← hg,hβ,← hf,← ht]

/-- Actual pullback of a cap pairing induces the expected pairing of homology images. -/
theorem pullPairing_homology {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : C ⟶ D) (g : K ⟶ L)
    (β : ∀ a b, D.X a →ₗ[ℚ] L.X (a+b) →ₗ[ℚ] M.X b)
    (hβ : Descent.Leibniz D L M β) (a b : ℕ) (x : C.homology a) (c : K.homology (a+b)) :
    Descent.homology C K M (pullPairing f g β) (pullPairing_leibniz f g β hβ) a b x c =
      Descent.homology D L M β hβ a b (homologyMap f a x) (homologyMap g (a+b) c) := by
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
  rfl

end TernaryPoly.SingularLocalCompactCapMV
