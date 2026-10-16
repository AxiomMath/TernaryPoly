module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.SupportLemma
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.LocalRelation
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Representatives
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapAlgebra
public import TernaryPeriodPolynomials.Topology.Rational.Compact.NeighborhoodAlgebra
public import TernaryPeriodPolynomials.Topology.Rational.Compact.NeighborhoodRelative

@[expose] public section


/-!
# Representatives of the Poincaré dual of a coinvariant cycle

For a manifold base `B` with a quotient covering `p : E ⟶ B` (rational representation `V`) and a
degree-three cycle `z` of the coinvariant singular chains, `exists_dual` produces a compact support
`K₀`, a cocycle `φ` of the geometric local cochains, vanishing on simplices subordinate to `K₀ᶜ`, such
that for every larger compact `K` and every chain `c` of `B` representing the fundamental class at `K`
(`IsFundRep`), `deg⁻¹ (cap φ c) - z` is a coboundary of the coinvariant chains.  `exists_fundRep` gives
such `c`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly TernaryPoly.RationalManifoldCompact
  TernaryPoly.SingularLocalSupport TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCompactDuality TernaryPoly.RationalLocalOrientation
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap.Descent TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.CoveringSingularOrbits
  TernaryPoly.FreeActionLinearization TernaryPoly.EquivariantSingularResolution
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

section Algebra

variable (K : ChainComplex (ModuleCat.{0} ℚ) ℕ)

/-- Every homology class is the class of a cycle. -/
theorem exists_chainClass (n : ℕ) (h : K.homology n) :
    ∃ x : Cycles (K.sc' (n+1) n (n-1)), Descent.chainClass K n x = h := by
  obtain ⟨x, hx⟩ := TernaryPoly.SingularLocalCompactCap.Algebra.cycleClass_surjective
    (K.sc' (n+1) n (n-1)) ((K.homologyIsoSc' (n+1) n (n-1) (down_prev _) (down_next _)).hom h)
  refine ⟨x, ?_⟩
  unfold Descent.chainClass
  rw [hx]
  exact congrArg (fun f => f h)
    (K.homologyIsoSc' (n+1) n (n-1) (down_prev _) (down_next _)).hom_inv_id

/-- Cycles with the same class differ by a boundary. -/
theorem exists_boundary_of_chainClass_eq (n : ℕ) (x x' : Cycles (K.sc' (n+1) n (n-1)))
    (h : Descent.chainClass K n x = Descent.chainClass K n x') :
    ∃ b : K.X (n+1), K.d (n+1) n b = x.val - x'.val := by
  have hx := TernaryPoly.SingularLocalCompactCap.Algebra.represented_opcycles K (n+1) n (n-1)
    (down_prev _) (down_next _) x
  have hx' := TernaryPoly.SingularLocalCompactCap.Algebra.represented_opcycles K (n+1) n (n-1)
    (down_prev _) (down_next _) x'
  have h1 : K.pOpcycles n x.val = K.pOpcycles n x'.val := by
    rw [← hx, ← hx']
    exact congrArg _ h
  let a : K.X n := x.val
  let a' : K.X n := x'.val
  have hxd : K.d n (n-1) a = 0 := x.property
  have hxd' : K.d n (n-1) a' = 0 := x'.property
  have hd : K.d n (n-1) (a - a') = 0 := by rw [map_sub, hxd, hxd', sub_zero]
  have h0 : TernaryPoly.RationalCompactNeighborhood.cycleClass K n (a - a') hd = 0 := by
    apply (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
    rw [TernaryPoly.RationalCompactNeighborhood.cycleClass_opcycles, map_sub]
    change K.pOpcycles n x.val - K.pOpcycles n x'.val = (K.homologyι n) 0
    rw [h1, sub_self, map_zero]
  exact (TernaryPoly.RationalCompactNeighborhood.cycleClass_eq_zero_iff K n _ hd).mp h0

end Algebra

section Dual

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [SecondCountableTopology B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)

/-- Every homology class is dual to a compactly supported cohomology class supported in a compact. -/
theorem exists_dual_class (a b : ℕ) (hab : a + b = n + 2)
    (zc : (coveringLocalChains p V).homology b) :
    ∃ (K : Compacts B) (y : (supportCochains p V (K : Set B)).homology a),
      compactCapMap p V n e o a b hab (compactClassMap p V K a y) = zc := by
  let _ : IsCancelSMul G E := hp.out.isCancelSMul
  have hiso := manifold_compactCap_isIso p V n e o a b hab
  obtain ⟨K, y, hy⟩ := Concrete.colimit_exists_rep (compactCohomologyDiagram p V a)
    (inv (compactCapMap p V n e o a b hab) zc)
  refine ⟨K, y, ?_⟩
  have h1 : compactClassMap p V K a y = inv (compactCapMap p V n e o a b hab) zc := hy
  rw [h1]
  exact congrArg (fun f => f zc) (IsIso.inv_hom_id (compactCapMap p V n e o a b hab))

end Dual

section Main

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [SecondCountableTopology B] [ChartedSpace H B]
  (e : H ≃ₜ EuclideanSpace ℝ (Fin (3+2))) (o : Orientation (3+2) B)

omit hp [ContinuousConstSMul G E] in
/-- A chain of `B` represents the compact fundamental class at the support `K`. -/
def IsFundRep {B : TopCat.{0}} {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
    (e : H ≃ₜ EuclideanSpace ℝ (Fin (3+2))) (o : Orientation (3+2) B)
    (K : Compacts B) (c : singularChainGroup ℚ B (2+3)) : Prop :=
  ∃ h : (supportChains (K : Set B)).d (2+3) (2+3-1)
      ((cokernel.π (RationalRelativeSingular.inclusion (K : Set B)ᶜ)).f (2+3) c) = 0,
    Descent.chainClass (supportChains (K : Set B)) (2+3)
      ⟨(cokernel.π (RationalRelativeSingular.inclusion (K : Set B)ᶜ)).f (2+3) c, h⟩ =
      capFundamentalClass 3 e o K 2 3 rfl

omit hp [ContinuousConstSMul G E] [SecondCountableTopology B] in
/-- Every compact support has a chain representing its fundamental class, with boundary over `Kᶜ`. -/
theorem exists_fundRep (K : Compacts B) :
    ∃ c : singularChainGroup ℚ B (2+3), IsFundRep e o K c ∧
      (singularBoundary ℚ B (2+3-1)).hom c ∈ subChainSubmodule ℚ B (K : Set B)ᶜ (2+3-1) := by
  obtain ⟨x, hx⟩ := exists_chainClass (supportChains (K : Set B)) (2+3)
    (capFundamentalClass 3 e o K 2 3 rfl)
  obtain ⟨c, hc⟩ := SingularLocalCap.RelativeAlgebra.projection_surjective
    (RationalRelativeSingular.inclusion (K : Set B)ᶜ) (2+3) x.val
  have hcyc : (supportChains (K : Set B)).d (2+3) (2+3-1)
      ((cokernel.π (RationalRelativeSingular.inclusion (K : Set B)ᶜ)).f (2+3) c) = 0 := by
    rw [hc]; exact x.property
  refine ⟨c, ⟨hcyc, ?_⟩, ?_⟩
  · rw [← hx]
    congr 1
    exact Subtype.ext hc
  · have hd := ConcreteCategory.congr_hom
      ((cokernel.π (RationalRelativeSingular.inclusion (K : Set B)ᶜ)).comm (2+3) (2+3-1)) c
    have h0 : (cokernel.π (RationalRelativeSingular.inclusion (K : Set B)ᶜ)).f (2+3-1)
        ((singularBoundary ℚ B (2+3-1)).hom c) = 0 := by
      refine Eq.trans ?_ hcyc
      exact hd.symm
    obtain ⟨b, hb⟩ := (SingularLocalCap.RelativeAlgebra.projection_zero_iff
      (RationalRelativeSingular.inclusion (K : Set B)ᶜ) (2+3-1) _).mp h0
    rw [← hb]
    exact singularChainMap_sInclusion_mem _ _ b

omit hp [ContinuousConstSMul G E] [SecondCountableTopology B] [T2Space B] in
theorem localChains_d_apply [ContinuousConstSMul G E] [IsCancelSMul G E]
    (hp' : IsQuotientCoveringMap p G) (n : ℕ) (x : VertexChain p hp' V (n+1)) :
    (localChains p hp' V).d (n+1) n x = boundary p hp' V n x := by
  simp only [localChains, ChainComplex.of_d]
  rfl

omit [SecondCountableTopology B] [T2Space B] in
theorem localCochains_d_apply (n : ℕ) (x : VertexCochain p hp.out V n) :
    (localCochains p hp.out V).d n (n+1) x = differential p hp.out V n x := by
  simp only [localCochains, CochainComplex.of_d]
  rfl

omit [SecondCountableTopology B] [T2Space B] in
/-- The inclusion of cochains supported in `K` is a cochain map: cocycles stay cocycles. -/
theorem supportInclusion_differential (K : Set B) (x : (supportCochains p V K).X 2)
    (hx : (supportCochains p V K).d 2 3 x = 0) :
    differential p hp.out V 2 ((supportInclusion p V K).f 2 x) = 0 := by
  have h2 : (localCochains p hp.out V).d 2 3 ((supportInclusion p V K).f 2 x) =
      (supportInclusion p V K).f 3 ((supportCochains p V K).d 2 3 x) :=
    ConcreteCategory.congr_hom ((supportInclusion p V K).comm 2 3) x
  rw [hx, map_zero] at h2
  exact (localCochains_d_apply p V 2 ((supportInclusion p V K).f 2 x)).symm.trans h2

omit [SecondCountableTopology B] [T2Space B] in
/-- A cochain supported in `K` vanishes on the simplices subordinate to `Kᶜ`. -/
theorem supportInclusion_vanish (K : Set B) (x : (supportCochains p V K).X 2) :
    ∀ σ : SingularSimplex B 2, IsSubordinate Kᶜ σ → ((supportInclusion p V K).f 2 x) σ = 0 := by
  intro σ hσ
  have hk : (localRestriction p Kᶜ V).f 2 ((supportInclusion p V K).f 2 x) = 0 := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun F => F.f 2) (kernel.condition (localRestriction p Kᶜ V))) x
    exact h
  obtain ⟨τ, hτ⟩ := exists_pushSimplex_of_subordinate (Kᶜ) 2 hσ
  have := (localRestriction_zero_iff p V Kᶜ 2 _).mp hk τ
  rw [← hτ]
  exact this

omit [T2Space B] [SecondCountableTopology B] in
/-- A coinvariant cycle is a cycle of the geometric local chains. -/
theorem degreeEquiv_cycle [IsCancelSMul G E] (z : (coinvariantChains G E V).X 3)
    (hz : (coinvariantChains G E V).d 3 2 z = 0) :
    (localChains p hp.out V).d 3 2 (degreeEquiv p hp.out V 3 z) = 0 := by
  have h := LinearMap.congr_fun (degreeEquiv_symm_boundary p hp.out V 2)
    (degreeEquiv p hp.out V 3 z)
  have h2 : (degreeEquiv p hp.out V 2).symm
      (boundary p hp.out V 2 (degreeEquiv p hp.out V 3 z)) = 0 := by
    change (degreeEquiv p hp.out V 2).symm
        (boundary p hp.out V 2 (degreeEquiv p hp.out V 3 z)) =
      (coinvariantChains G E V).d 3 2 ((degreeEquiv p hp.out V 3).symm
        (degreeEquiv p hp.out V 3 z)) at h
    rw [h, LinearEquiv.symm_apply_apply, hz]
  have h3 := (degreeEquiv p hp.out V 2).symm.injective (h2.trans (map_zero _).symm)
  rw [localChains_d_apply p V hp.out 2]
  exact h3

omit [SecondCountableTopology B] in
/-- **The dual of a cycle, from a cocycle representative of a dual class.**  Suppose the compact-support
class `y₁` supported in `K₁` caps (against the fundamental class) to the class of the coinvariant cycle
`z`, and `φ₁` is a cocycle representing `y₁`.  Then `φ₁` is a cocycle of the geometric local cochains
vanishing off `K₁`, and for every larger compact `K` and every chain `c` representing the fundamental
class at `K`, the cap of `φ₁` with `c` is homologous to `z` in the coinvariant chains. -/
theorem dual_of_rep [IsCancelSMul G E] (z : (coinvariantChains G E V).X 3)
    (hz : (coinvariantChains G E V).d 3 2 z = 0) (K₁ : Compacts B)
    (y₁ : (supportCochains p V (K₁ : Set B)).homology 2)
    (hy₁ : compactCapMap p V 3 e o 2 3 rfl (compactClassMap p V K₁ 2 y₁) =
      chainClass (localChains p hp.out V) 3
        (⟨degreeEquiv p hp.out V 3 z, degreeEquiv_cycle p V z hz⟩ :
          Cycles ((localChains p hp.out V).sc' (3+1) 3 (3-1))))
    (φ₁ : Cycles ((supportCochains p V (K₁ : Set B)).sc' (2-1) 2 (2+1)))
    (hφ₁ : cochainClass (supportCochains p V (K₁ : Set B)) 2 φ₁ = y₁) :
      differential p hp.out V 2 ((supportInclusion p V (K₁ : Set B)).f 2 φ₁.val) = 0 ∧
      (∀ σ : SingularSimplex B 2, IsSubordinate (K₁ : Set B)ᶜ σ →
        ((supportInclusion p V (K₁ : Set B)).f 2 φ₁.val) σ = 0) ∧
      ∀ (K : Compacts B), K₁ ≤ K → ∀ c : singularChainGroup ℚ B (2+3), IsFundRep e o K c →
        ∃ v : (coinvariantChains G E V).X 4,
          (coinvariantChains G E V).d 4 3 v =
            (degreeEquiv p hp.out V 3).symm
              (cap p hp.out V 2 3 ((supportInclusion p V (K₁ : Set B)).f 2 φ₁.val) c) - z := by
  have hzl := degreeEquiv_cycle p V z hz
  let zx : Cycles ((localChains p hp.out V).sc' (3+1) 3 (3-1)) :=
    ⟨degreeEquiv p hp.out V 3 z, hzl⟩
  refine ⟨?_, ?_, ?_⟩
  · exact supportInclusion_differential p V _ _ φ₁.property
  · exact supportInclusion_vanish p V _ _
  · intro K hK c hc
    obtain ⟨hcyc, hcls⟩ := hc
    let φK : Cycles ((supportCochains p V (K : Set B)).sc' (2-1) 2 (2+1)) :=
      ⟨(supportMap p V (K₁ : Set B) (K : Set B) hK).f 2 φ₁.val, by
        have h : ((supportCochains p V (K : Set B)).d 2 3)
            ((supportMap p V (K₁ : Set B) (K : Set B) hK).f 2 φ₁.val) =
            (supportMap p V (K₁ : Set B) (K : Set B) hK).f 3
              ((supportCochains p V (K₁ : Set B)).d 2 3 φ₁.val) :=
          ConcreteCategory.congr_hom ((supportMap p V (K₁ : Set B) (K : Set B) hK).comm 2 3) φ₁.val
        have h0 : (supportCochains p V (K₁ : Set B)).d 2 3 φ₁.val = 0 := φ₁.property
        change ((supportCochains p V (K : Set B)).d 2 3) _ = 0
        rw [h, h0, map_zero]⟩
    have hφK : φK.val = (supportMap p V (K₁ : Set B) (K : Set B) hK).f 2 φ₁.val := rfl
    have hnat : homologyMap (supportMap p V (K₁ : Set B) (K : Set B) hK) 2 y₁ =
        cochainClass (supportCochains p V (K : Set B)) 2 φK := by
      rw [← hφ₁]
      exact TernaryPoly.SingularLocalCompactCap.Algebra.represented_natural
        (supportMap p V (K₁ : Set B) (K : Set B) hK) (2-1) 2 (2+1) (up_prev _) (up_next _) φ₁ φK rfl
    have hcap1 : compactCapAt p V 3 e o K 2 3 rfl
        (cochainClass (supportCochains p V (K : Set B)) 2 φK) =
        chainClass (localChains p hp.out V) 3 zx := by
      rw [← hnat]
      have h1 := ConcreteCategory.congr_hom
        (compactCapAt_enlargement p V 3 e o K₁ K hK 2 3 rfl) y₁
      have h2 : compactCapAt p V 3 e o K 2 3 rfl
          (homologyMap (supportMap p V (K₁ : Set B) (K : Set B) hK) 2 y₁) =
          compactCapAt p V 3 e o K₁ 2 3 rfl y₁ := h1
      rw [h2, ← compactCapMap_classMap p V 3 e o K₁ 2 3 rfl]
      exact hy₁
    have hrep := supportCapHomology_representatives p V (K : Set B) 2 3 φK
      ⟨(cokernel.π (RationalRelativeSingular.inclusion (K : Set B)ᶜ)).f (2+3) c, hcyc⟩
    have hcap2 : chainClass (localChains p hp.out V) 3
        (⟨supportCap p V (K : Set B) 2 3 φK.val
          ((cokernel.π (RationalRelativeSingular.inclusion (K : Set B)ᶜ)).f (2+3) c),
          Descent.cycles _ _ _ _ (supportCap_leibniz p V (K : Set B)) 2 3 φK
            ⟨(cokernel.π (RationalRelativeSingular.inclusion (K : Set B)ᶜ)).f (2+3) c, hcyc⟩⟩ :
          Cycles ((localChains p hp.out V).sc' (3+1) 3 (3-1))) =
        chainClass (localChains p hp.out V) 3 zx := by
      rw [← hrep, ← hcap1]
      change _ = supportCapHomology p V (K : Set B) 2 3
        (cochainClass (supportCochains p V (K : Set B)) 2 φK)
        (capFundamentalClass 3 e o K 2 3 rfl)
      rw [← hcls]
    obtain ⟨b, hb⟩ := exists_boundary_of_chainClass_eq (localChains p hp.out V) 3 _ _ hcap2
    have h3 : supportCap p V (K : Set B) 2 3 φK.val
        ((cokernel.π (RationalRelativeSingular.inclusion (K : Set B)ᶜ)).f (2+3) c) =
        cap p hp.out V 2 3 ((supportInclusion p V (K₁ : Set B)).f 2 φ₁.val) c := by
      have hsp := supportCap_projection p V (K : Set B) 2 3
        (φK.val : (supportCochains p V (K : Set B)).X 2) c
      refine hsp.trans ?_
      have hh := congrArg (fun F => F.f 2) (supportMap_inclusion p V (K₁ : Set B) (K : Set B) hK)
      have := ConcreteCategory.congr_hom hh φ₁.val
      have h4 : (supportInclusion p V (K : Set B)).f 2 φK.val =
          (supportInclusion p V (K₁ : Set B)).f 2 φ₁.val := by rw [hφK]; exact this
      rw [h4]
    have hb' : boundary p hp.out V 3 b =
        cap p hp.out V 2 3 ((supportInclusion p V (K₁ : Set B)).f 2 φ₁.val) c -
          degreeEquiv p hp.out V 3 z := by
      rw [← localChains_d_apply p V hp.out 3 b]
      exact hb.trans
        (congrArg (fun w => w - (degreeEquiv p hp.out V 3 z : (localChains p hp.out V).X 3)) h3)
    refine ⟨(degreeEquiv p hp.out V 4).symm b, ?_⟩
    have h1 := LinearMap.congr_fun (degreeEquiv_symm_boundary p hp.out V 3) b
    change (degreeEquiv p hp.out V 3).symm (boundary p hp.out V 3 b) =
      (coinvariantChains G E V).d 4 3 ((degreeEquiv p hp.out V 4).symm b) at h1
    rw [← h1, hb', map_sub, LinearEquiv.symm_apply_apply]


omit [SecondCountableTopology B] in
/-- **The dual of a cycle, from a dual class.**  Suppose the compact-support class `y₁` supported in `K₁`
caps (against the fundamental class) to the class of the coinvariant cycle `z`.  Then a cocycle
representative `φ` of `y₁` satisfies: for every larger compact `K` and every chain `c` representing the
fundamental class at `K`, the cap of `φ` with `c` is homologous to `z` in the coinvariant chains. -/
theorem dual_of_class [IsCancelSMul G E] (z : (coinvariantChains G E V).X 3)
    (hz : (coinvariantChains G E V).d 3 2 z = 0) (K₁ : Compacts B)
    (y₁ : (supportCochains p V (K₁ : Set B)).homology 2)
    (hy₁ : compactCapMap p V 3 e o 2 3 rfl (compactClassMap p V K₁ 2 y₁) =
      chainClass (localChains p hp.out V) 3
        (⟨degreeEquiv p hp.out V 3 z, degreeEquiv_cycle p V z hz⟩ :
          Cycles ((localChains p hp.out V).sc' (3+1) 3 (3-1)))) :
    ∃ φ₁ : Cycles ((supportCochains p V (K₁ : Set B)).sc' (2-1) 2 (2+1)),
      cochainClass (supportCochains p V (K₁ : Set B)) 2 φ₁ = y₁ ∧
      differential p hp.out V 2 ((supportInclusion p V (K₁ : Set B)).f 2 φ₁.val) = 0 ∧
      (∀ σ : SingularSimplex B 2, IsSubordinate (K₁ : Set B)ᶜ σ →
        ((supportInclusion p V (K₁ : Set B)).f 2 φ₁.val) σ = 0) ∧
      ∀ (K : Compacts B), K₁ ≤ K → ∀ c : singularChainGroup ℚ B (2+3), IsFundRep e o K c →
        ∃ v : (coinvariantChains G E V).X 4,
          (coinvariantChains G E V).d 4 3 v =
            (degreeEquiv p hp.out V 3).symm
              (cap p hp.out V 2 3 ((supportInclusion p V (K₁ : Set B)).f 2 φ₁.val) c) - z := by
  obtain ⟨φ₁, hφ₁⟩ := TernaryPoly.SingularLocalCompactCap.Algebra.cochainClass_surjective
    (supportCochains p V (K₁ : Set B)) 2 y₁
  exact ⟨φ₁, hφ₁, dual_of_rep p V e o z hz K₁ y₁ hy₁ φ₁ hφ₁⟩

end Main

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
