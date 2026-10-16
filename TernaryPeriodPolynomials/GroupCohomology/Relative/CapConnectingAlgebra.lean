module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVConnectingPairing

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeCapConnecting
open CategoryTheory Limits HomologicalComplex
open SingularLocalCap SingularLocalCompactCap.Algebra SingularLocalCompactCapMV

/-- A genuine chain short exact sequence lifts a relative cycle and its differential. -/
theorem chainConnecting_lifts
    (S : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ)) (hS : S.ShortExact) (n : ℕ)
    (c₃ : Homology.Cycles (S.X₃.sc' (n+2) (n+1) n)) :
    ∃ c₂ : S.X₂.X (n+1), ∃ c₁ : Homology.Cycles (S.X₁.sc' (n+1) n (n-1)),
      S.g.f (n+1) c₂ = c₃.val ∧ S.f.f n c₁.val = S.X₂.d (n+1) n c₂ := by
  have := hS.epi_g
  have := hS.mono_f
  obtain ⟨c₂,h₂⟩ := (ModuleCat.epi_iff_surjective (S.g.f (n+1))).mp inferInstance c₃.val
  have hd : S.g.f n (S.X₂.d (n+1) n c₂) = 0 := by
    have hc := congrArg (fun f => f c₂) (S.g.comm (n+1) n)
    exact hc.symm.trans ((congrArg (S.X₃.d (n+1) n) h₂).trans c₃.property)
  have hs := (shortExact_iff_degreewise_shortExact S).mp hS n
  obtain ⟨c₁,h₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp hs.exact (S.X₂.d (n+1) n c₂) hd
  have hc : S.X₁.d n (n-1) c₁ = 0 := by
    apply (ModuleCat.mono_iff_injective (S.f.f (n-1))).mp inferInstance
    rw [map_zero]
    have he := congrArg (fun f => f c₁) (S.f.comm n (n-1))
    exact he.symm.trans ((congrArg (S.X₂.d n (n-1)) h₁).trans
      (congrArg (fun f => f c₂) (S.X₂.d_comp_d (n+1) n (n-1))))
  exact ⟨c₂,⟨c₁,hc⟩,h₂,h₁⟩

/-- Two actual cycles with an explicit boundary difference represent the same homology class. -/
theorem chainClass_eq_of_boundary (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (x y : Homology.Cycles (K.sc' (n+1) n (n-1))) (u : K.X (n+1))
    (hu : K.d (n+1) n u = x.val - y.val) :
    Descent.chainClass K n x = Descent.chainClass K n y := by
  apply (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  rw [Descent.chainClass,Descent.chainClass,represented_opcycles,represented_opcycles]
  rw [← sub_eq_zero]
  erw [← map_sub,← hu]
  exact congrArg (fun f => f u) (K.d_pOpcycles (n+1) n)

/-- Degree transport of a cycle gives precisely the canonical equality map on homology. -/
theorem cast_cycle_class (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) {n m : ℕ} (h : n = m)
    (c : Homology.Cycles (K.sc' (n+1) n (n-1))) :
    Descent.chainClass K m (castChainCycle K h c) =
      eqToHom (congrArg (fun i => K.homology i) h) (Descent.chainClass K n c) := by
  subst m
  rfl

end TernaryPoly.RelativeCapConnecting
