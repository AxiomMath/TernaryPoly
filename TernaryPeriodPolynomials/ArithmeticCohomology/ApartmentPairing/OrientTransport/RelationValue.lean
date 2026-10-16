module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.LocalRelationBox
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.LocalizeDec
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.CYPoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.PointClass

@[expose] public section


/-!
# The value of the local relation scalar

`local_relation_value` is `Locality.local_relation` with the additional output of the value of the scalar `r` in terms of the
staircase constant `d₅`: for the pulled-back Thom cochain `θ_X = θ₁ ∘ (δ⁻¹ ρ f)_#` of the chart (`f = s ≫ psi`),
`d₅ · r · θ_X(a) = lamPos · lam2`.  The hypotheses are those of `local_relation` together with: the identification of `y` with
the pulled-back Thom cochain `y₁ ∘ g_#` of radius `η` over the chart, the geometry of the chart in the product coordinates
`psi`, and the orientation data (the local class of `c` at the base point is the orientation generator of `B`, which is the
pushforward of the library orientation of the symmetric space).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open CategoryTheory Limits TernaryPoly TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap TernaryPoly.EquivariantSingularResolution
  TopologicalSpace TernaryPoly.RationalLocalMap TernaryPoly.RationalLocalOrientation
  TernaryPoly.RationalSingularAugmentation TernaryPoly.ContractibleSingularHomology
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open TernaryPoly.SymmetricSpacePositive TernaryPoly.EuclideanLocalHomology

variable {G : Type} [Group G] {B : TopCat.{0}} [T1Space B] [MulAction G (TopCat.of Space)]
  [ContinuousConstSMul G (TopCat.of Space)] [IsCancelSMul G (TopCat.of Space)]
  (p : TopCat.of Space ⟶ B) (hp : IsQuotientCoveringMap p G)


/-- **The local relation with the value of `r`.** -/
theorem local_relation_value
    (UT UA UB : Set B) (hUT : IsOpen UT) (hUA : IsOpen UA) (hUB : IsOpen UB)
    (hcov : UT ∪ UA ∪ UB = Set.univ)
    (y : singularChainGroup ℚ (TopCat.of Space) 3 →ₗ[ℚ] ℚ)
    (hy : ∀ e, y ((singularBoundary ℚ (TopCat.of Space) 3).hom e) = 0)
    (hfin : ∀ τ : SingularSimplex (TopCat.of Space) 3,
      {g : G | y (chainGenerator ℚ (TopCat.of Space) 3 (g • τ)) ≠ 0}.Finite)
    {Z : Set (TopCat.of Space)}
    (hyZ : ∀ τ : SingularSimplex (TopCat.of Space) 3, IsSubordinate Zᶜ τ →
      y (chainGenerator ℚ (TopCat.of Space) 3 τ) = 0)
    (hUBZ : p ⁻¹' UB ⊆ Zᶜ)
    (c : singularChainGroup ℚ B 5) (hc : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B UA 4)
    (s : TopCat.of UT ⟶ TopCat.of Space) (hs : s ≫ p = sInclusion UT)
    (hone : ∀ (ρ : SingularSimplex (TopCat.of UT) 3) (g : G), g ≠ 1 →
      y (chainGenerator ℚ (TopCat.of Space) 3 (g • pushSimplex s 3 ρ)) = 0)
    (a : singularChainGroup ℚ (TopCat.of UT) 2)
    (hspan : ∀ z : singularChainGroup ℚ (TopCat.of UT) 2,
      (singularBoundary ℚ (TopCat.of UT) 1).hom z ∈
        subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 1 →
      ∃ (q : ℚ) (f : singularChainGroup ℚ (TopCat.of UT) 3),
        z - q • a - (singularBoundary ℚ (TopCat.of UT) 2).hom f ∈
          subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 2)
    -- the Thom data
    (y₁ : (chains R3).X 3 →ₗ[ℚ] ℚ) (θ₁ : (chains R2).X 2 →ₗ[ℚ] ℚ) (T : UnitThom y₁ θ₁)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (g : TopCat.of Space ⟶ TopCat.of R3) (hyform : y = y₁.comp (singularChainMap ℚ g 3).hom)
    (hgs : ∀ u : UT, g.hom (s.hom u) = η⁻¹ • piE (psi (s.hom u)))
    (hA : ∀ u : UT, (u : B) ∈ UA → δ < ‖rhoE (psi (s.hom u))‖)
    (hBη : ∀ u : UT, (u : B) ∈ UB → η < ‖piE (psi (s.hom u))‖)
    -- the orientation data
    (hpB : IsLocalHomeomorph p.hom) (oB : ∀ b : B, (RationalLocalChartHomology.localChains b).homology 5)
    (hgen : ∀ S : Space, oB (p.hom S) =
      localHomeomorphMap p.hom hpB S 5 (SymmetricSpaceLocalOrientation.localGenerator S))
    (Tt : Opens Space) (p0 : Space) (hp0 : p0 ∈ Tt) (hiso : IsolatesFiber p.hom p0 Tt)
    (hom : TopCat.of UT ⟶ TopCat.of Tt) (hhom : hom ≫ TtInc Tt = s)
    (hb0A : p.hom p0 ∉ UA) (hb0B : p.hom p0 ∉ UB) (hpsi0 : psi p0 = 0)
    (hcb : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B ({p.hom p0}ᶜ : Set B) 4)
    (hc0 : rcls (X := B) ({p.hom p0}ᶜ : Set B) 4 c hcb = oB (p.hom p0)) :
    ∃ r : ℚ,
      (∀ (V : Rep.{0} ℚ G) (φ : VertexCochain p hp V 2) (_ : differential p hp V 2 φ = 0)
        (_ : ∀ σ : SingularSimplex B 2, IsSubordinate UA σ → φ σ = 0),
        Yco V y hfin ((degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ c)) =
          r • (chainDesc fun σ : SingularSimplex (TopCat.of UT) 2 =>
            vertexToFunction p hp φ (pushSimplex s 2 σ)) a) ∧
      d5 * r * (θ₁.comp (singularChainMap ℚ ((s ≫ psiHom) ≫ rhoEHom ≫ scale2 δ⁻¹) 2).hom) a =
        lamPos * lam2 := by
  obtain ⟨cY, ⟨cA, hcA, cB, hcB, u, hdec⟩, ⟨aY, haY, bY, hbY, hbd⟩, hid⟩ :=
    localize_pairing_dec p hp UT UA UB hUT hUA hUB hcov y hy hfin hyZ hUBZ c hc s hs
  set Wset : Set (TopCat.of UT) := (Subtype.val ⁻¹' UA)ᶜ with hW
  set Zs : Set (TopCat.of UT) := s ⁻¹' Z with hZs
  have hWc : Wsetᶜ = Subtype.val ⁻¹' UA := by rw [hW, compl_compl]
  have hps : ∀ u : UT, p (s u) = (u : B) := by
    intro u
    have h := ConcreteCategory.congr_hom hs u
    exact h
  have hZB : (Subtype.val ⁻¹' UB : Set (TopCat.of UT)) ⊆ Zsᶜ := by
    intro u hu hz
    have : p (s u) ∈ UB := by rw [hps]; exact hu
    exact hUBZ this hz
  have hy' : ∀ e, (y.comp (singularChainMap ℚ s 3).hom)
      ((singularBoundary ℚ (TopCat.of UT) 3).hom e) = 0 := by
    intro e
    rw [LinearMap.comp_apply]
    have h1 := singularChainMap_boundary_apply ℚ s 3 e
    have h2 : (singularChainMap ℚ s 3).hom ((singularBoundary ℚ (TopCat.of UT) 3).hom e) =
        (singularBoundary ℚ (TopCat.of Space) 3).hom ((singularChainMap ℚ s 4).hom e) := h1.symm
    rw [h2]; exact hy _
  have hyv : ∀ τ : SingularSimplex (TopCat.of UT) 3, IsSubordinate Zsᶜ τ →
      (y.comp (singularChainMap ℚ s 3).hom) (chainGenerator ℚ (TopCat.of UT) 3 τ) = 0 := by
    intro τ hτ
    rw [LinearMap.comp_apply, singularChainMap_generator]
    apply hyZ
    rw [isSubordinate_pushSimplex_iff]
    exact hτ
  have hcc : (singularBoundary ℚ (TopCat.of UT) 4).hom cY ∈
      subChainSubmodule ℚ (TopCat.of UT) Wsetᶜ 4 ⊔ subChainSubmodule ℚ (TopCat.of UT) Zsᶜ 4 := by
    rw [hbd, hWc]
    exact Submodule.add_mem_sup haY (subChainSubmodule_mono hZB 4 hbY)
  obtain ⟨r, hr⟩ := cross_relation (TopCat.of UT) Wset Zs (y.comp (singularChainMap ℚ s 3).hom)
    hy' hyv a cY hcc (by rw [hWc]; exact hspan)
  refine ⟨r, ?_, ?_⟩
  · intro V φ hφd hφA
    rw [hid V φ hφd hφA, Yco_capE_pushforward V s (vertexToFunction p hp φ) y hfin hone cY]
    apply hr (ModuleCat.of ℚ V) (chainDesc fun σ : SingularSimplex (TopCat.of UT) 2 =>
        vertexToFunction p hp φ (pushSimplex s 2 σ))
    · intro τ hτ
      rw [chainDesc_generator]
      rw [hWc] at hτ
      exact cochainY_vanish p hp V s hs φ hφA τ hτ
    · exact fun e => cochainY_cocycle p hp V s φ hφd e
  · set f : TopCat.of UT ⟶ TopCat.of (EuclideanSpace ℝ (Fin 5)) := s ≫ psiHom with hf
    -- the explicit form of the chart cochains
    have hgs' : s ≫ g = f ≫ piEHom ≫ scale3 η⁻¹ := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro u
      exact hgs u
    have hyX : y.comp (singularChainMap ℚ s 3).hom =
        y₁.comp (singularChainMap ℚ (f ≫ piEHom ≫ scale3 η⁻¹) 3).hom := by
      rw [hyform, ← hgs', singularChainMap_comp]
      rfl
    set θX : singularChainGroup ℚ (TopCat.of UT) 2 →ₗ[ℚ] ℚ :=
      θ₁.comp (singularChainMap ℚ (f ≫ rhoEHom ≫ scale2 δ⁻¹) 2).hom with hθX
    have hθv : ∀ τ : SingularSimplex (TopCat.of UT) 2, IsSubordinate Wsetᶜ τ →
        θX (chainGenerator ℚ (TopCat.of UT) 2 τ) = 0 := by
      intro τ hτ
      rw [hθX, LinearMap.comp_apply, singularChainMap_generator]
      apply T.t_vanish
      rw [isSubordinate_pushSimplex_iff]
      refine hτ.mono ?_
      intro v hv
      rw [hWc] at hv
      have h1 := hA v hv
      change 1 < ‖δ⁻¹ • rhoE (psi (s.hom v))‖
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, inv_mul_eq_div, lt_div_iff₀ hδ]
      linarith
    have hθc : ∀ e, θX ((singularBoundary ℚ (TopCat.of UT) 2).hom e) = 0 := by
      intro e
      rw [hθX, LinearMap.comp_apply]
      have h1 := singularChainMap_boundary_apply ℚ (f ≫ rhoEHom ≫ scale2 δ⁻¹) 2 e
      have h2 : (singularChainMap ℚ (f ≫ rhoEHom ≫ scale2 δ⁻¹) 2).hom
          ((singularBoundary ℚ (TopCat.of UT) 2).hom e) =
          (singularBoundary ℚ (TopCat.of R2) 2).hom
            ((singularChainMap ℚ (f ≫ rhoEHom ≫ scale2 δ⁻¹) 3).hom e) := h1.symm
      rw [h2]
      exact T.t_cocycle _
    have hval := hr (ModuleCat.of ℚ ℚ) θX hθv hθc
    have hcc' : (singularBoundary ℚ (TopCat.of UT) 4).hom cY ∈
        subChainSubmodule ℚ (TopCat.of UT) (f.hom ⁻¹' {x : EuclideanSpace ℝ (Fin 5) | δ < ‖rhoE x‖}) 4 ⊔
          subChainSubmodule ℚ (TopCat.of UT) (f.hom ⁻¹' {x : EuclideanSpace ℝ (Fin 5) | η < ‖piE x‖}) 4 := by
      rw [hbd]
      refine Submodule.add_mem_sup (subChainSubmodule_mono ?_ 4 haY) (subChainSubmodule_mono ?_ 4 hbY)
      · intro v hv; exact hA v hv
      · intro v hv; exact hBη v hv
    have hA0 : {x : EuclideanSpace ℝ (Fin 5) | δ < ‖rhoE x‖} ⊆ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) := by
      intro x hx hx0
      have : δ < ‖rhoE x‖ := hx
      rw [Set.mem_singleton_iff.mp hx0, map_zero, norm_zero] at this
      linarith
    have hB0 : {x : EuclideanSpace ℝ (Fin 5) | η < ‖piE x‖} ⊆ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) := by
      intro x hx hx0
      have : η < ‖piE x‖ := hx
      rw [Set.mem_singleton_iff.mp hx0, map_zero, norm_zero] at this
      linarith
    have h0 : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom
        ((singularChainMap ℚ f (4 + 1)).hom cY) ∈
        subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4 := by
      have h1 := singularChainMap_boundary_apply ℚ f 4 cY
      rw [h1]
      obtain ⟨a', ha', b', hb', hab⟩ := Submodule.mem_sup.mp hcc'
      rw [← hab, map_add]
      exact Submodule.add_mem _
        (subChainSubmodule_mono hA0 4 (singularChainMap_mem_sub f _ 4 ha'))
        (subChainSubmodule_mono hB0 4 (singularChainMap_mem_sub f _ 4 hb'))
    have hE : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom
        ((singularChainMap ℚ (s ≫ psiHom) (4 + 1)).hom cY) ∈
        subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({psi p0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4 := by
      rw [hpsi0]; exact h0
    have key := cY_pointClass p hpB oB hgen Tt p0 hp0 hiso (sInclusion UT) s hs hom hhom UA UB hb0A hb0B
      c cY cA cB hcA hcB u hdec aY bY haY hbY hbd hcb hc0 hE
    have hpt : rcls (X := TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4
        ((singularChainMap ℚ f (4 + 1)).hom cY) h0 = localGenerator 3 0 := by
      have shift : ∀ z : EuclideanSpace ℝ (Fin 5), psi p0 = z →
          ∀ h : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom
            ((singularChainMap ℚ f (4 + 1)).hom cY) ∈
            subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({z}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4,
          rcls (X := TopCat.of (EuclideanSpace ℝ (Fin 5))) ({z}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4
            ((singularChainMap ℚ f (4 + 1)).hom cY) h = localGenerator 3 z := by
        intro z hz
        subst hz
        intro h
        exact key
      exact shift 0 hpsi0 h0
    have hfinal := chart_scaled_pt T (X := TopCat.of UT) f hη hδ cY hcc' h0 hpt
    rw [← hyX, hval] at hfinal
    rw [← hfinal, smul_eq_mul, mul_assoc]


/-- **The local relation on a product chart, with the value of `r`.**  The box version of `local_relation_value`: the chart
`UT` is homeomorphic to the coordinate box by `e`, which is the product chart `psi` composed with the section `s`, and the slab
complement is the support `UA`. -/
theorem local_relation_box_value
    (UT UA UB : Set B) (hUT : IsOpen UT) (hUA : IsOpen UA) (hUB : IsOpen UB)
    (hcov : UT ∪ UA ∪ UB = Set.univ)
    (y : singularChainGroup ℚ (TopCat.of Space) 3 →ₗ[ℚ] ℚ)
    (hy : ∀ e, y ((singularBoundary ℚ (TopCat.of Space) 3).hom e) = 0)
    (hfin : ∀ τ : SingularSimplex (TopCat.of Space) 3,
      {g : G | y (chainGenerator ℚ (TopCat.of Space) 3 (g • τ)) ≠ 0}.Finite)
    {Z : Set (TopCat.of Space)}
    (hyZ : ∀ τ : SingularSimplex (TopCat.of Space) 3, IsSubordinate Zᶜ τ →
      y (chainGenerator ℚ (TopCat.of Space) 3 τ) = 0)
    (hUBZ : p ⁻¹' UB ⊆ Zᶜ)
    (c : singularChainGroup ℚ B 5) (hc : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B UA 4)
    (s : TopCat.of UT ⟶ TopCat.of Space) (hs : s ≫ p = sInclusion UT)
    (hone : ∀ (ρ : SingularSimplex (TopCat.of UT) 3) (g : G), g ≠ 1 →
      y (chainGenerator ℚ (TopCat.of Space) 3 (g • pushSimplex s 3 ρ)) = 0)
    (ε R δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R)
    (e : TopCat.of UT ≃ₜ boxSet ε R)
    (hW : (Subtype.val ⁻¹' UA : Set UT)ᶜ = {u | ‖((e u : R3 × R2)).2‖ ≤ δ})
    (he : ∀ u : UT, ((e u : boxSet ε R) : R3 × R2) = coordHomeo (s.hom u))
    (a : singularChainGroup ℚ (TopCat.of UT) 2)
    (ha : (singularBoundary ℚ (TopCat.of UT) 1).hom a ∈
      subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 1)
    (haB : a ∉ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 2 ⊔
      LinearMap.range (singularBoundary ℚ (TopCat.of UT) 2).hom)
    (y₁ : (chains R3).X 3 →ₗ[ℚ] ℚ) (θ₁ : (chains R2).X 2 →ₗ[ℚ] ℚ) (T : UnitThom y₁ θ₁)
    {η : ℝ} (hη : 0 < η)
    (g : TopCat.of Space ⟶ TopCat.of R3) (hyform : y = y₁.comp (singularChainMap ℚ g 3).hom)
    (hgs : ∀ u : UT, g.hom (s.hom u) = η⁻¹ • piE (psi (s.hom u)))
    (hBη : ∀ u : UT, (u : B) ∈ UB → η < ‖piE (psi (s.hom u))‖)
    (hpB : IsLocalHomeomorph p.hom) (oB : ∀ b : B, (RationalLocalChartHomology.localChains b).homology 5)
    (hgen : ∀ S : Space, oB (p.hom S) =
      localHomeomorphMap p.hom hpB S 5 (SymmetricSpaceLocalOrientation.localGenerator S))
    (Tt : Opens Space) (p0 : Space) (hp0 : p0 ∈ Tt) (hiso : IsolatesFiber p.hom p0 Tt)
    (hom : TopCat.of UT ⟶ TopCat.of Tt) (hhom : hom ≫ TtInc Tt = s)
    (hb0A : p.hom p0 ∉ UA) (hb0B : p.hom p0 ∉ UB) (hpsi0 : psi p0 = 0)
    (hcb : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B ({p.hom p0}ᶜ : Set B) 4)
    (hc0 : rcls (X := B) ({p.hom p0}ᶜ : Set B) 4 c hcb = oB (p.hom p0)) :
    ∃ r : ℚ,
      (∀ (V : Rep.{0} ℚ G) (φ : VertexCochain p hp V 2) (_ : differential p hp V 2 φ = 0)
        (_ : ∀ σ : SingularSimplex B 2, IsSubordinate UA σ → φ σ = 0),
        Yco V y hfin ((degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ c)) =
          r • (chainDesc fun σ : SingularSimplex (TopCat.of UT) 2 =>
            vertexToFunction p hp φ (pushSimplex s 2 σ)) a) ∧
      d5 * r * (θ₁.comp (singularChainMap ℚ ((s ≫ psiHom) ≫ rhoEHom ≫ scale2 δ⁻¹) 2).hom) a =
        lamPos * lam2 := by
  refine local_relation_value p hp UT UA UB hUT hUA hUB hcov y hy hfin hyZ hUBZ c hc s hs hone a
    (hspan_of_box ε R δ hε hδ hδR e hW a ha haB) y₁ θ₁ T hη hδ g hyform hgs ?_ hBη hpB oB hgen Tt p0 hp0 hiso
    hom hhom hb0A hb0B hpsi0 hcb hc0
  intro u hu
  by_contra hnot
  have hle : ‖((e u : boxSet ε R) : R3 × R2).2‖ ≤ δ := by
    have : ‖rhoE (psi (s.hom u))‖ ≤ δ := not_lt.mp hnot
    have h1 : rhoE (psi (s.hom u)) = (coordHomeo (s.hom u)).2 := rhoE_prodEL _
    rw [he u]
    rw [h1] at this
    exact this
  have : u ∈ ((Subtype.val ⁻¹' UA : Set UT)ᶜ) := by
    rw [hW]; exact hle
  exact this hu

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
