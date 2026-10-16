module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Degrees

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap
open CategoryTheory
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open Homology

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [IsCancelSMul G E] (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

/-- Actual cochains and their adjacent differentials in degree a. -/
abbrev cochainSC (a : ℕ) := (localCochains p hp V).sc' (a-1) a (a+1)

/-- Actual local chains and their adjacent differentials in degree b. -/
abbrev localChainSC (b : ℕ) := (localChains p hp V).sc' (b+1) b (b-1)

/-- Actual scalar chains and their adjacent differentials in degree n. -/
abbrev scalarChainSC (n : ℕ) := (scalarChains B).sc' (n+1) n (n-1)

omit [IsCancelSMul G E] in
/-- The outgoing local-cochain map is the actual geometric differential. -/
theorem cochainSC_g (a : ℕ) : (cochainSC p hp V a).g.hom = differential p hp V a := by
  simp [cochainSC, localCochains, CochainComplex.of_d]
  rfl

/-- The incoming local-chain map is the actual geometric boundary. -/
theorem localChainSC_f (b : ℕ) : (localChainSC p hp V b).f.hom = boundary p hp V b := by
  simp [localChainSC, localChains, ChainComplex.of_d]
  rfl

/-- The positive-degree outgoing local-chain map is the actual geometric boundary. -/
theorem localChainSC_g_succ (b : ℕ) : (localChainSC p hp V (b+1)).g.hom = boundary p hp V b := by
  simp [localChainSC, localChains, ChainComplex.of_d]
  rfl

omit [IsCancelSMul G E] in
/-- The incoming positive-degree local-cochain map is the actual geometric differential. -/
theorem cochainSC_f_succ (a : ℕ) : (cochainSC p hp V (a+1)).f.hom = differential p hp V a := by
  simp [cochainSC, localCochains, CochainComplex.of_d]
  rfl

/-- A genuine cocycle capped with a genuine scalar cycle is a genuine local cycle. -/
theorem cap_cycles (a b : ℕ) (φ : Cycles (cochainSC p hp V a))
    (c : Cycles (scalarChainSC (B := B) (a+b))) :
    (localChainSC p hp V b).g (cap p hp V a b φ.val c.val) = 0 := by
  have hφ : differential p hp V a φ.val = 0 := by
    have h := φ.property
    change (cochainSC p hp V a).g.hom φ.val = 0 at h
    rwa [cochainSC_g] at h
  cases b with
  | zero =>
    change (localChains p hp V).d 0 0 _ = 0
    rw [(localChains p hp V).shape _ _ (by simp)]
    rfl
  | succ b =>
    change (localChainSC p hp V (b+1)).g.hom _ = 0
    erw [localChainSC_g_succ]
    have hc : (singularBoundary ℚ B (a+b)).hom c.val = 0 := by
      have hh := c.property
      change (scalarChains B).d (a+b+1) (a+b+1-1) c.val = 0 at hh
      have he : a+b+1-1 = a+b := Nat.add_sub_cancel _ _
      have hd := congrArg (fun f => f c.val) ((scalarChains B).d_comp_XIsoOfEq_hom he (a+b+1))
      erw [← hd]
      change ((scalarChains B).XIsoOfEq he).hom ((scalarChains B).d (a+b+1) (a+b+1-1) c.val) = 0
      rw [hh, map_zero]
    erw [boundary_cap p hp V a b φ.val c.val, hc, hφ, map_zero]
    change (-1 : ℤ)^a • (0 - capLinear p hp V (a+1) b 0 (scalarCastLeft B a b c.val)) = 0
    rw [map_zero]
    simp

/-- Capping a scalar boundary with a cocycle is a local boundary with the proved Koszul sign. -/
theorem cap_scalar_boundary (a b : ℕ) (φ : Cycles (cochainSC p hp V a))
    (c : (scalarChainSC (B := B) (a+b)).X₁) :
    ∃ u : (localChainSC p hp V b).X₁,
      (localChainSC p hp V b).f u = cap p hp V a b φ.val ((scalarChainSC (B := B) (a+b)).f c) := by
  refine ⟨(-1 : ℤ)^a • cap p hp V a (b+1) φ.val c, ?_⟩
  have hφ : differential p hp V a φ.val = 0 := by
    have h := φ.property
    change (cochainSC p hp V a).g.hom φ.val = 0 at h
    rwa [cochainSC_g] at h
  change (localChainSC p hp V b).f.hom _ = cap p hp V a b φ.val ((singularBoundary ℚ B (a+b)).hom c)
  erw [localChainSC_f]
  erw [map_zsmul, cap_leibniz p hp V a b φ.val c, hφ]
  change _ = capLinear p hp V (a+1) b 0 (scalarCastLeft B a b c) + _
  rw [map_zero]
  simp
  rfl

/-- Capping a cochain boundary with a scalar cycle is an actual local boundary. -/
theorem cap_cochain_boundary (a b : ℕ) (ψ : (cochainSC p hp V a).X₁)
    (c : Cycles (scalarChainSC (B := B) (a+b))) :
    ∃ u : (localChainSC p hp V b).X₁,
      (localChainSC p hp V b).f u = cap p hp V a b ((cochainSC p hp V a).f ψ) c.val := by
  cases a with
  | zero =>
    refine ⟨0, ?_⟩
    change (localChains p hp V).d (b+1) b 0 =
      capLinear p hp V 0 b ((localCochains p hp V).d 0 0 ψ) c.val
    rw [(localCochains p hp V).shape _ _ (by simp)]
    erw [map_zero]
    change 0 = capLinear p hp V 0 b 0 c.val
    rw [map_zero]
    rfl
  | succ a =>
    let c' := scalarCastRight B a b c.val
    have hc : (singularBoundary ℚ B (a+b)).hom c' = 0 :=
      scalarCastRight_cycle B a b c.val c.property
    have h := cap_leibniz p hp V a b ψ c'
    rw [hc, map_zero] at h
    erw [scalarCastLeft_right B a b c.val] at h
    refine ⟨-((-1 : ℤ)^a • cap p hp V a (b+1) ψ c'), ?_⟩
    change (localChainSC p hp V b).f.hom _ = cap p hp V (a+1) b ((cochainSC p hp V (a+1)).f.hom ψ) c.val
    erw [localChainSC_f, cochainSC_f_succ]
    erw [map_neg, map_zsmul]
    exact eq_neg_iff_add_eq_zero.mpr h.symm |>.symm

/-- The actual cap pairing on homology of the adjacent singular short complexes. -/
def absoluteSC (a b : ℕ) :
    (cochainSC p hp V a).homology →ₗ[ℚ]
      (scalarChainSC (B := B) (a+b)).homology →ₗ[ℚ] (localChainSC p hp V b).homology :=
  induced _ _ _ (capLinear p hp V a b)
    (cap_cycles p hp V a b) (cap_cochain_boundary p hp V a b) (cap_scalar_boundary p hp V a b)

/-- The genuine absolute cap product on actual local cohomology and scalar singular homology. -/
def absolute (a b : ℕ) :
    (localCochains p hp V).homology a →ₗ[ℚ]
      (scalarChains B).homology (a+b) →ₗ[ℚ] (localChains p hp V).homology b :=
  (((absoluteSC p hp V a b).compl₂
      ((scalarChains B).homologyIsoSc' (a+b+1) (a+b) (a+b-1) (down_prev _) (down_next _)).hom.hom).comp
      ((localCochains p hp V).homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).hom.hom).compr₂
      ((localChains p hp V).homologyIsoSc' (b+1) b (b-1) (down_prev _) (down_next _)).inv.hom

end TernaryPoly.SingularLocalCap
