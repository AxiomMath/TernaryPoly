module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVConnectingClasses

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex
open SingularLocalCap SingularLocalCompactCap.Algebra

/-- Reindex an actual chain cycle through an equality of degrees. -/
def castChainCycle (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) {n m : ℕ} (h : n = m)
    (c : Homology.Cycles (K.sc' (n+1) n (n-1))) : Homology.Cycles (K.sc' (m+1) m (m-1)) := by
  subst m
  exact c

/-- The reindexed cycle has the canonical degree-isomorphism value. -/
theorem castChainCycle_val (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) {n m : ℕ} (h : n = m)
    (c : Homology.Cycles (K.sc' (n+1) n (n-1))) :
    (castChainCycle K h c).val = (K.XIsoOfEq h).hom c.val := by
  subst m
  rfl

/-- Integer scaling of a literal chain cycle induces the same scaling of its actual homology class. -/
theorem chainClass_zsmul (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) (r : ℤ)
    (c : Homology.Cycles (K.sc' (n+1) n (n-1))) :
    Descent.chainClass K n (r • c) = r • Descent.chainClass K n c := by
  simp only [Descent.chainClass,map_zsmul]

/-- A genuine cochain short exact sequence provides a lift of each cocycle and of its differential. -/
theorem cochainConnecting_lifts
    (S : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℕ)) (hS : S.ShortExact) (a : ℕ)
    (x₃ : Homology.Cycles (S.X₃.sc' (a-1) a (a+1))) :
    ∃ x₂ : S.X₂.X a, ∃ x₁ : Homology.Cycles (S.X₁.sc' a (a+1) (a+2)),
      S.g.f a x₂ = x₃.val ∧ S.f.f (a+1) x₁.val = S.X₂.d a (a+1) x₂ := by
  have := hS.epi_g
  have := hS.mono_f
  obtain ⟨x₂,h₂⟩ := (ModuleCat.epi_iff_surjective (S.g.f a)).mp inferInstance x₃.val
  have hd : S.g.f (a+1) (S.X₂.d a (a+1) x₂) = 0 := by
    have hc := congrArg (fun f => f x₂) (S.g.comm a (a+1))
    exact hc.symm.trans ((congrArg (S.X₃.d a (a+1)) h₂).trans x₃.property)
  have hs := (shortExact_iff_degreewise_shortExact S).mp hS (a+1)
  obtain ⟨x₁,h₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp hs.exact (S.X₂.d a (a+1) x₂) hd
  have hc : S.X₁.d (a+1) (a+2) x₁ = 0 := by
    apply (ModuleCat.mono_iff_injective (S.f.f (a+2))).mp inferInstance
    rw [map_zero]
    have he := congrArg (fun f => f x₁) (S.f.comm (a+1) (a+2))
    exact he.symm.trans ((congrArg (S.X₂.d (a+1) (a+2)) h₁).trans
      (congrArg (fun f => f x₂) (S.X₂.d_comp_d a (a+1) (a+2))))
  exact ⟨x₂,⟨x₁,hc⟩,h₂,h₁⟩

/-- The two genuine signed Mayer–Vietoris connecting morphisms commute with compatible cap
pairings with the sign forced by the Leibniz rule: (-1)^(a+1). -/
theorem connecting_pairing
    (S : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℕ)) (hS : S.ShortExact)
    (T : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ)) (hT : T.ShortExact)
    (K : ChainComplex (ModuleCat.{0} ℚ) ℕ)
    (β₁ : ∀ a b, S.X₁.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] T.X₁.X b)
    (β₂ : ∀ a b, S.X₂.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] T.X₂.X b)
    (β₃ : ∀ a b, S.X₃.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] T.X₃.X b)
    (hβ₁ : Descent.Leibniz S.X₁ K T.X₁ β₁)
    (hβ₂ : Descent.Leibniz S.X₂ K T.X₂ β₂)
    (hβ₃ : Descent.Leibniz S.X₃ K T.X₃ β₃)
    (hf : ∀ a b x c, T.f.f b (β₁ a b x c) = β₂ a b (S.f.f a x) c)
    (hg : ∀ a b x c, T.g.f b (β₂ a b x c) = β₃ a b (S.g.f a x) c)
    (a b : ℕ) (x : S.X₃.homology a)
    (c : Homology.Cycles (K.sc' (a+b+2) (a+b+1) (a+b))) :
    hT.δ (b+1) b rfl
      (Descent.homology S.X₃ K T.X₃ β₃ hβ₃ a (b+1) x (Descent.chainClass K (a+b+1) c)) =
        (-1 : ℤ)^(a+1) • Descent.homology S.X₁ K T.X₁ β₁ hβ₁ (a+1) b
          (hS.δ a (a+1) rfl x)
          (Descent.chainClass K (a+1+b) (castChainCycle K (by omega) c)) := by
  obtain ⟨x₃,rfl⟩ := cochainClass_surjective S.X₃ a x
  obtain ⟨x₂,x₁,h₂,h₁⟩ := cochainConnecting_lifts S hS a x₃
  let c' := castChainCycle K (show a+b+1 = a+1+b by omega) c
  let z₃ : Homology.Cycles (T.X₃.sc' (b+2) (b+1) b) :=
    ⟨β₃ a (b+1) x₃.val c.val,Descent.cycles _ _ _ _ hβ₃ a (b+1) x₃ c⟩
  let z₁ : Homology.Cycles (T.X₁.sc' (b+1) b (b-1)) :=
    ⟨β₁ (a+1) b x₁.val c'.val,Descent.cycles _ _ _ _ hβ₁ (a+1) b x₁ c'⟩
  have h₂' : T.g.f (b+1) (β₂ a (b+1) x₂ c.val) = z₃.val := by
    exact (hg a (b+1) x₂ c.val).trans
      (congrArg (fun y : S.X₃.X a => β₃ a (b+1) y c.val) h₂)
  have h₁' : T.f.f b (((-1 : ℤ)^(a+1) • z₁).val) =
      T.X₂.d (b+1) b (β₂ a (b+1) x₂ c.val) := by
    change T.f.f b ((-1 : ℤ)^(a+1) • β₁ (a+1) b x₁.val c'.val) = _
    rw [map_zsmul]
    erw [hf (a+1) b x₁.val c'.val,h₁]
    have hc : K.d (a+b+1) (a+b) c.val = 0 := c.property
    have ht : c'.val = (Descent.castLeft K a b).hom c.val := castChainCycle_val K _ c
    rw [ht]
    exact (cap_boundary_sign S.X₂ K T.X₂ β₂ hβ₂ a b x₂ c.val hc).symm
  erw [cochainConnecting_representatives S hS a x₃ x₂ x₁ h₂ h₁,
    Descent.homology_representatives S.X₃ K T.X₃ β₃ hβ₃ a (b+1) x₃ c,
    Descent.homology_representatives S.X₁ K T.X₁ β₁ hβ₁ (a+1) b x₁ c']
  exact (chainConnecting_representatives T hT b z₃ (β₂ a (b+1) x₂ c.val)
    ((-1 : ℤ)^(a+1) • z₁) h₂' h₁').trans (chainClass_zsmul T.X₁ b _ z₁)

end TernaryPoly.SingularLocalCompactCapMV
