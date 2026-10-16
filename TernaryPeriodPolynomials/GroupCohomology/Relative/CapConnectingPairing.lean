module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.CapConnectingAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeCapConnecting
open CategoryTheory Limits HomologicalComplex
open SingularLocalCap SingularLocalCompactCap.Algebra SingularLocalCompactCapMV

/-- The scalar and cohomology connecting maps obey the cap identity with net positive sign.
The Koszul factor multiplies an actual boundary, which vanishes in homology. -/
theorem connecting_pairing
    (S : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℕ)) (hS : S.ShortExact)
    (T : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ)) (hT : T.ShortExact)
    {M L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (j : M ⟶ L)
    (β₁ : ∀ a b, S.X₁.X a →ₗ[ℚ] T.X₃.X (a+b) →ₗ[ℚ] L.X b)
    (β₂ : ∀ a b, S.X₂.X a →ₗ[ℚ] T.X₂.X (a+b) →ₗ[ℚ] L.X b)
    (β₃ : ∀ a b, S.X₃.X a →ₗ[ℚ] T.X₁.X (a+b) →ₗ[ℚ] M.X b)
    (hβ₁ : Descent.Leibniz S.X₁ T.X₃ L β₁)
    (hβ₂ : Descent.Leibniz S.X₂ T.X₂ L β₂)
    (hβ₃ : Descent.Leibniz S.X₃ T.X₁ M β₃)
    (hf : ∀ a b x c, β₁ a b x (T.g.f (a+b) c) = β₂ a b (S.f.f a x) c)
    (hg : ∀ a b x c, j.f b (β₃ a b (S.g.f a x) c) = β₂ a b x (T.f.f (a+b) c))
    (a b : ℕ) (x : S.X₃.homology a)
    (c : Homology.Cycles (T.X₃.sc' (a+b+2) (a+b+1) (a+b))) :
    homologyMap j b
      (Descent.homology S.X₃ T.X₁ M β₃ hβ₃ a b x
        (hT.δ (a+b+1) (a+b) rfl (Descent.chainClass T.X₃ (a+b+1) c))) =
      Descent.homology S.X₁ T.X₃ L β₁ hβ₁ (a+1) b
        (hS.δ a (a+1) rfl x)
        (Descent.chainClass T.X₃ (a+1+b) (castChainCycle T.X₃ (by omega) c)) := by
  obtain ⟨x₃,rfl⟩ := cochainClass_surjective S.X₃ a x
  obtain ⟨x₂,x₁,hx₂,hx₁⟩ := cochainConnecting_lifts S hS a x₃
  obtain ⟨c₂,c₁,hc₂,hc₁⟩ := chainConnecting_lifts T hT (a+b) c
  let c' := castChainCycle T.X₃ (show a+b+1 = a+1+b by omega) c
  let z₃ : Homology.Cycles (M.sc' (b+1) b (b-1)) :=
    ⟨β₃ a b x₃.val c₁.val,Descent.cycles _ _ _ _ hβ₃ a b x₃ c₁⟩
  let z₁ : Homology.Cycles (L.sc' (b+1) b (b-1)) :=
    ⟨β₁ (a+1) b x₁.val c'.val,Descent.cycles _ _ _ _ hβ₁ (a+1) b x₁ c'⟩
  let z₂ : Homology.Cycles (L.sc' (b+1) b (b-1)) :=
    ⟨j.f b z₃.val,(congrArg (fun f => f z₃.val) (j.comm b (b-1))).trans
      ((congrArg (j.f (b-1)) z₃.property).trans (map_zero _))⟩
  have hz₂ : z₂.val = β₂ a b x₂ (T.X₂.d (a+b+1) (a+b) c₂) := by
    change j.f b (β₃ a b x₃.val c₁.val) = _
    rw [← hx₂]
    erw [hg,hc₁]
  have hz₁ : z₁.val = β₂ (a+1) b (S.X₂.d a (a+1) x₂)
      ((Descent.castLeft T.X₂ a b).hom c₂) := by
    change β₁ (a+1) b x₁.val c'.val = _
    have ht : c'.val = T.g.f (a+1+b) ((Descent.castLeft T.X₂ a b).hom c₂) := by
      rw [castChainCycle_val]
      rw [← hc₂]
      exact castLeft_map T.g a b c₂
    rw [ht]
    erw [hf,hx₁]
  have hu : L.d (b+1) b ((-1 : ℤ)^a • β₂ a (b+1) x₂ c₂) = z₂.val - z₁.val := by
    rw [map_zsmul,hz₂,hz₁,hβ₂]
    exact (add_sub_cancel_left _ _).symm
  erw [cochainConnecting_representatives S hS a x₃ x₂ x₁ hx₂ hx₁,
    chainConnecting_representatives T hT (a+b) c c₂ c₁ hc₂ hc₁,
    Descent.homology_representatives S.X₃ T.X₁ M β₃ hβ₃ a b x₃ c₁,
    Descent.homology_representatives S.X₁ T.X₃ L β₁ hβ₁ (a+1) b x₁ c']
  exact (chainClass_natural j b z₃ z₂ rfl).trans
    (chainClass_eq_of_boundary L b z₂ z₁ _ hu)

/-- The connecting cap square holds for every actual scalar homology class, with canonical
transport between the equal total degrees on its two sides. -/
theorem connecting_pairing_homology
    (S : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℕ)) (hS : S.ShortExact)
    (T : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ)) (hT : T.ShortExact)
    {M L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (j : M ⟶ L)
    (β₁ : ∀ a b, S.X₁.X a →ₗ[ℚ] T.X₃.X (a+b) →ₗ[ℚ] L.X b)
    (β₂ : ∀ a b, S.X₂.X a →ₗ[ℚ] T.X₂.X (a+b) →ₗ[ℚ] L.X b)
    (β₃ : ∀ a b, S.X₃.X a →ₗ[ℚ] T.X₁.X (a+b) →ₗ[ℚ] M.X b)
    (hβ₁ : Descent.Leibniz S.X₁ T.X₃ L β₁)
    (hβ₂ : Descent.Leibniz S.X₂ T.X₂ L β₂)
    (hβ₃ : Descent.Leibniz S.X₃ T.X₁ M β₃)
    (hf : ∀ a b x c, β₁ a b x (T.g.f (a+b) c) = β₂ a b (S.f.f a x) c)
    (hg : ∀ a b x c, j.f b (β₃ a b (S.g.f a x) c) = β₂ a b x (T.f.f (a+b) c))
    (a b : ℕ) (x : S.X₃.homology a)
    (c : T.X₃.homology (a+b+1)) :
    homologyMap j b
      (Descent.homology S.X₃ T.X₁ M β₃ hβ₃ a b x
        (hT.δ (a+b+1) (a+b) rfl c)) =
      Descent.homology S.X₁ T.X₃ L β₁ hβ₁ (a+1) b
        (hS.δ a (a+1) rfl x)
        (eqToHom (congrArg (fun i => T.X₃.homology i) (show a+b+1 = a+1+b by omega)) c) := by
  obtain ⟨c,rfl⟩ := chainClass_surjective T.X₃ (a+b+1) c
  rw [← cast_cycle_class]
  exact connecting_pairing S hS T hT j β₁ β₂ β₃ hβ₁ hβ₂ hβ₃ hf hg a b x c

end TernaryPoly.RelativeCapConnecting
