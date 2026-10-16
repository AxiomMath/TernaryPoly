module

public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapConnectingCore

@[expose] public section


/-!
# `K`-equivariance of the duality `Θ = S3 ∘ S2⁻¹ ∘ S1`, piece (ii)(a): the fundamental class

Any `k ∈ GL₃(ℤ)` acts on the rational gluing `Glued` (`integralAction`) and, because `Γ(6)` is normal
in `GL₃(ℤ)`, descends to a homeomorphism `f̄_k` of the compact bordification
`BordifiedOrbit = Γ(6)\Glued` (`fbar`). It preserves the boundary and the open interior
(`fbar_mem_interior_iff`, `psi`), and acts on the interior `Γ(6)\𝒳` as the quotient of the
real matrix action `S ↦ k S kᵀ`.

* `psi_generator`: `f̄_k` preserves the arithmetic interior orientation `interiorOrientation`
  (literal local homology generators). The library already shows that every real `GL₃` action
  preserves the local generators of the covering (`all_actionLocalMap_generator`); this is descended
  through the covering projection (`abar_generator`) and transported to the interior subtype by a
  generic conjugation lemma (`pullbackGenerator_preserved`).
* `fundamentalClass_fbar`: the induced map `fbarRel k` of the relative chains of the boundary pair
  fixes the relative fundamental class (by `fundamentalClass_unique`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.DualityEquivariance

open TernaryPoly TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SymmetricSpaceArithmeticProper TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpaceRelativeFundamental
  TernaryPoly.RationalLocalMap TernaryPoly.RationalLocalChartHomology
  TernaryPoly.RationalLocalOrientation TernaryPoly.RationalRelativeSingular CategoryTheory
  HomologicalComplex


/-- Conjugation by any integral matrix preserves the principal congruence subgroup. -/
theorem conj_mem_principalSix (k : IntegralGL) {g : IntegralGL} (hg : g ∈ principalSix) :
    k * g * k⁻¹ ∈ principalSix :=
  (principal_normal 6).conj_mem g hg k

theorem orbitRel_integral (k : IntegralGL) {x y : Glued}
    (h : MulAction.orbitRel principalSix Glued x y) :
    MulAction.orbitRel principalSix Glued (integralAction k x) (integralAction k y) := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨⟨k * g.1 * k⁻¹, conj_mem_principalSix k g.2⟩, ?_⟩
  change (k * g.1 * k⁻¹) • integralAction k y = integralAction k (g.1 • y)
  change (k * g.1 * k⁻¹) • (k • y) = k • (g.1 • y)
  rw [mul_smul, mul_smul, inv_smul_smul]

/-- The induced map of the bordification `Γ(6)\Glued` by the normalizing element `k`. -/
def fbarFun (k : IntegralGL) : BordifiedOrbit → BordifiedOrbit :=
  Quotient.map (integralAction k) (fun _ _ h => orbitRel_integral k h)

theorem fbarFun_projection (k : IntegralGL) (x : Glued) :
    fbarFun k (projection principalSix x) = projection principalSix (integralAction k x) := rfl

theorem fbarFun_continuous (k : IntegralGL) : Continuous (fbarFun k) := by
  rw [(projection_openQuotient principalSix).isQuotientMap.continuous_iff]
  have : fbarFun k ∘ projection principalSix = projection principalSix ∘ integralAction k := rfl
  rw [this]
  exact (projection_continuous principalSix).comp (continuous_leftAction _)

theorem fbarFun_mul (k l : IntegralGL) (x : BordifiedOrbit) :
    fbarFun k (fbarFun l x) = fbarFun (k * l) x := by
  induction x using Quotient.inductionOn with | _ x => ?_
  change projection principalSix (integralAction k (integralAction l x)) =
    projection principalSix (integralAction (k * l) x)
  congr 1
  change k • (l • x) = (k * l) • x
  rw [mul_smul]

theorem fbarFun_one (x : BordifiedOrbit) : fbarFun 1 x = x := by
  induction x using Quotient.inductionOn with | _ x => ?_
  change projection principalSix ((1 : IntegralGL) • x) = projection principalSix x
  rw [one_smul]

/-- The homeomorphism of the bordification induced by `k`, with inverse induced by `k⁻¹`. -/
def fbar (k : IntegralGL) : BordifiedOrbit ≃ₜ BordifiedOrbit where
  toFun := fbarFun k
  invFun := fbarFun k⁻¹
  left_inv x := by rw [fbarFun_mul, inv_mul_cancel, fbarFun_one]
  right_inv x := by rw [fbarFun_mul, mul_inv_cancel, fbarFun_one]
  continuous_toFun := fbarFun_continuous k
  continuous_invFun := fbarFun_continuous k⁻¹

@[simp] theorem fbar_apply (k : IntegralGL) (x : BordifiedOrbit) : fbar k x = fbarFun k x := rfl

theorem fbar_projection (k : IntegralGL) (x : Glued) :
    fbar k (projection principalSix x) = projection principalSix (integralAction k x) := rfl

theorem fbar_embedding (k : IntegralGL) (S : Space) :
    fbar k (interiorProjection principalSix S) =
      interiorProjection principalSix (act (realIntegral k) S) := by
  change projection principalSix (integralAction k (embedding S)) = _
  rw [integralAction_embedding]
  rfl

open TernaryPoly.SymmetricSpaceCovering in
theorem fbar_mem_interior (k : IntegralGL) {x : BordifiedOrbit}
    (hx : x ∈ (boundary principalSix)ᶜ) : fbar k x ∈ (boundary principalSix)ᶜ := by
  rw [TernaryPoly.SymmetricSpaceRelativeFundamental.boundary_compl_eq_range] at hx ⊢
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨S, rfl⟩ := quotientProjection_surjective o
  refine ⟨quotientProjection (act (realIntegral k) S), ?_⟩
  rw [arithmeticEmbedding_projection, arithmeticEmbedding_projection, fbar_embedding]

theorem fbar_mem_interior_iff (k : IntegralGL) (x : BordifiedOrbit) :
    fbar k x ∈ (boundary principalSix)ᶜ ↔ x ∈ (boundary principalSix)ᶜ := by
  refine ⟨fun h => ?_, fbar_mem_interior k⟩
  have := fbar_mem_interior k⁻¹ h
  change fbarFun k⁻¹ (fbarFun k x) ∈ _ at this
  rwa [fbarFun_mul, inv_mul_cancel, fbarFun_one] at this

/-- The homeomorphism of the open interior induced by `k`. -/
def psi (k : IntegralGL) : ↥(boundary principalSix)ᶜ ≃ₜ ↥(boundary principalSix)ᶜ :=
  (fbar k).subtype (fun x => (fbar_mem_interior_iff k x).symm)

@[simp] theorem psi_val (k : IntegralGL) (x : ↥(boundary principalSix)ᶜ) :
    (psi k x).val = fbar k x.val := rfl

theorem fbar_mem_boundary (k : IntegralGL) {x : BordifiedOrbit} (hx : x ∈ boundary principalSix) :
    fbar k x ∈ boundary principalSix := by
  by_contra h
  exact (fbar_mem_interior_iff k x).1 h hx



section Local

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Degree-`k` local homology map of a homeomorphism at a point. -/
abbrev Lhom (e : X ≃ₜ Y) (x : X) (k : ℕ) :
    (localChains x).homology k ⟶ (localChains (e x)).homology k :=
  homologyMap (homeomorphLocalIso e x).hom k

theorem Lhom_trans (e₁ : X ≃ₜ Y) (e₂ : Y ≃ₜ Z) (x : X) (k : ℕ) :
    Lhom (e₁.trans e₂) x k = Lhom e₁ x k ≫ Lhom e₂ (e₁ x) k := by
  unfold Lhom homeomorphLocalIso
  rw [relativeHomeomorphIso_hom, relativeHomeomorphIso_hom, relativeHomeomorphIso_hom,
    ← homologyMap_comp]
  exact congrArg (fun f => homologyMap f k)
    (RationalRelativeSingular.relativeMap_comp e₁.toHomotopyEquiv.toFun e₂.toHomotopyEquiv.toFun
      _ _ _ _ _).symm

/-- The local map of a homeomorphism is an isomorphism. -/
instance Lhom_isIso [T1Space X] (e : X ≃ₜ Y) (x : X) (k : ℕ) : IsIso (Lhom e x k) :=
  inferInstanceAs (IsIso (homologyMap (homeomorphLocalIso e x).hom k))

/-- A family of local classes that is invariant under the conjugate `α` of `ψ` by `e` gives a
pulled-back family invariant under `ψ`. -/
theorem pullbackGenerator_preserved [T1Space X] (e : X ≃ₜ Y) (ψ : X ≃ₜ X) (k : ℕ)
    (o : ∀ y : Y, (localChains y).homology k)
    (ho : ∀ y, Lhom (e.symm.trans (ψ.trans e)) y k (o y) = o ((e.symm.trans (ψ.trans e)) y))
    (x : X) :
    Lhom ψ x k (pullbackGenerator e k o x) = pullbackGenerator e k o (ψ x) := by
  set α : Y ≃ₜ Y := e.symm.trans (ψ.trans e) with hα
  set P := pullbackGenerator e k o x with hP
  have hP' : Lhom e x k P = o (e x) := by
    have : (pointHomologyIso e x k).hom ((pointHomologyIso e x k).inv (o (e x))) = o (e x) := by
      change ((pointHomologyIso e x k).inv ≫ (pointHomologyIso e x k).hom) (o (e x)) = _
      rw [(pointHomologyIso e x k).inv_hom_id]; rfl
    exact this
  have hcomp : ψ.trans e = e.trans α := by
    ext z
    simp [hα]
  have hS : Lhom (e.trans α) x k P = o ((e.trans α) x) := by
    rw [Lhom_trans]
    change Lhom α (e x) k (Lhom e x k P) = o (α (e x))
    rw [hP']
    exact ho (e x)
  rw [← hcomp] at hS
  rw [Lhom_trans] at hS
  change Lhom e (ψ x) k (Lhom ψ x k P) = o (e (ψ x)) at hS
  have hQ : Lhom e (ψ x) k (pullbackGenerator e k o (ψ x)) = o (e (ψ x)) := by
    have : (pointHomologyIso e (ψ x) k).hom ((pointHomologyIso e (ψ x) k).inv (o (e (ψ x)))) =
        o (e (ψ x)) := by
      change ((pointHomologyIso e (ψ x) k).inv ≫ (pointHomologyIso e (ψ x) k).hom)
        (o (e (ψ x))) = _
      rw [(pointHomologyIso e (ψ x) k).inv_hom_id]; rfl
    exact this
  have hinj : Function.Injective (Lhom e (ψ x) k) := by
    have : Mono (Lhom e (ψ x) k) := inferInstance
    exact (ModuleCat.mono_iff_injective _).mp this
  exact hinj (hS.trans hQ.symm)

end Local



theorem arithmeticEmbedding_interiorHomeomorph (x : ↥(boundary principalSix)ᶜ) :
    arithmeticEmbedding (interiorHomeomorph x) = x.val := by
  unfold interiorHomeomorph
  simp only [Homeomorph.trans_apply]
  have := (arithmeticEmbedding_isOpenEmbedding.isEmbedding.toHomeomorph).apply_symm_apply
    ((Homeomorph.setCongr boundary_compl_eq_range) x)
  exact congrArg Subtype.val this


theorem interiorHomeomorph_eq {o : OrbitSpace} {x : ↥(boundary principalSix)ᶜ}
    (h : arithmeticEmbedding o = x.val) : interiorHomeomorph x = o :=
  arithmeticEmbedding_isOpenEmbedding.injective
    ((arithmeticEmbedding_interiorHomeomorph x).trans h.symm)

/-- The homeomorphism of the orbit space induced by `k`. -/
def abar (k : IntegralGL) : OrbitSpace ≃ₜ OrbitSpace :=
  interiorHomeomorph.symm.trans ((psi k).trans interiorHomeomorph)

theorem abar_projection (k : IntegralGL) (S : Space) :
    abar k (quotientProjection S) = quotientProjection (act (realIntegral k) S) := by
  set x : ↥(boundary principalSix)ᶜ := interiorHomeomorph.symm (quotientProjection S) with hx
  have h1 : arithmeticEmbedding (quotientProjection S) = x.val := by
    have := arithmeticEmbedding_interiorHomeomorph x
    rw [hx, Homeomorph.apply_symm_apply] at this
    exact this
  change interiorHomeomorph (psi k x) = _
  apply interiorHomeomorph_eq
  change arithmeticEmbedding (quotientProjection (act (realIntegral k) S)) = fbar k x.val
  rw [← h1, arithmeticEmbedding_projection, arithmeticEmbedding_projection, fbar_embedding]

section Orient

open TernaryPoly.SymmetricSpaceQuotientOrientation

/-- The covering projection, as a local homeomorphism, intertwines the lifted action with `abar`. -/
theorem abar_generator (k : IntegralGL) (y : OrbitSpace) :
    Lhom (abar k) y 5 (SymmetricSpaceQuotientOrientation.localGenerator y) =
      SymmetricSpaceQuotientOrientation.localGenerator (abar k y) := by
  obtain ⟨S, rfl⟩ := quotientProjection_surjective y
  set g : RealGL := realIntegral k with hg
  set a : Space ≃ₜ Space := actionHomeomorph g with ha
  let Pr : C(Space, OrbitSpace) := SymmetricSpaceQuotientOrientation.projection
  have hPr : IsLocalHomeomorph Pr := SymmetricSpaceQuotientOrientation.projection_localHomeomorph
  let A : C(Space, Space) := ⟨a, a.continuous⟩
  let B : C(OrbitSpace, OrbitSpace) := ⟨abar k, (abar k).continuous⟩
  have hA : IsLocalHomeomorph A := a.isLocalHomeomorph
  have hB : IsLocalHomeomorph B := (abar k).isLocalHomeomorph
  -- the two composites agree
  have hcomp : B.comp Pr = Pr.comp A := by
    ext S'
    exact abar_projection k S'
  -- the statement for an arbitrary map with this common value
  let genS : ∀ S' : Space, (localChains S').homology 5 :=
    fun S' => SymmetricSpaceLocalOrientation.localGenerator S'
  have key : ∀ (f : C(Space, OrbitSpace)) (hf : IsLocalHomeomorph f),
      f = Pr.comp A →
      (localHomeomorphMap f hf S 5) (genS S) =
        SymmetricSpaceQuotientOrientation.localGenerator (f S) := by
    intro f hf hfe
    subst hfe
    rw [← localHomeomorphMap_comp A Pr hA hPr S 5]
    have h1 : (localHomeomorphMap A hA S 5) (genS S) = genS (A S) := by
      have h0 : localHomeomorphMap A hA S 5 = Lhom a S 5 := localHomeomorphMap_homeomorph a S 5
      have h2 := SymmetricSpaceLocalOrientation.all_actionLocalMap_generator g S
      rw [h0]
      exact h2
    change (localHomeomorphMap Pr hPr (A S) 5) ((localHomeomorphMap A hA S 5) (genS S)) = _
    rw [h1]
    exact SymmetricSpaceQuotientOrientation.localGenerator_projection (A S)
  have hk := key (B.comp Pr) (hB.comp hPr) hcomp
  rw [← localHomeomorphMap_comp Pr B hPr hB S 5] at hk
  have hk2 : (localHomeomorphMap B hB (Pr S) 5)
      ((localHomeomorphMap Pr hPr S 5) (genS S)) = _ := hk
  rw [SymmetricSpaceQuotientOrientation.localGenerator_projection S] at hk2
  have hB' : localHomeomorphMap B hB (Pr S) 5 = Lhom (abar k) (quotientProjection S) 5 :=
    localHomeomorphMap_homeomorph (abar k) (quotientProjection S) 5
  rw [hB'] at hk2
  exact hk2

/-- **`ψ_k` preserves the arithmetic interior orientation.** -/
theorem psi_generator (k : IntegralGL) (x : ↥(boundary principalSix)ᶜ) :
    Lhom (psi k) x 5 (interiorOrientation.generator x) = interiorOrientation.generator (psi k x) :=
  pullbackGenerator_preserved interiorHomeomorph (psi k) 5
    SymmetricSpaceQuotientOrientation.localGenerator (fun y => abar_generator k y) x

end Orient

open TernaryPoly.RationalCompactBoundary TernaryPoly.RationalRelativeExcision

/-- The map of relative chains of the boundary pair induced by `f̄_k`. -/
def fbarRel (k : IntegralGL) :
    relativeChains (boundary principalSix) ⟶ relativeChains (boundary principalSix) :=
  relativeMap ⟨fbar k, (fbar k).continuous⟩ (boundary principalSix) (boundary principalSix)
    (fun _ hx => fbar_mem_boundary k hx)

theorem relativeMap_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (h : f = g) (S : Set X) (T : Set Y) (hf : Set.MapsTo f S T) (hg : Set.MapsTo g S T) :
    relativeMap f S T hf = relativeMap g S T hg := by
  subst h; rfl

theorem fbarRel_point (k : IntegralGL) (x : BordifiedOrbit) (hx : x ∉ boundary principalSix)
    (hy : fbar k x ∉ boundary principalSix) :
    fbarRel k ≫ boundaryPointMap (boundary principalSix) (fbar k x) hy =
      boundaryPointMap (boundary principalSix) x hx ≫ (homeomorphLocalIso (fbar k) x).hom := by
  unfold fbarRel boundaryPointMap homeomorphLocalIso
  rw [relativeHomeomorphIso_hom]
  let F : C(BordifiedOrbit, BordifiedOrbit) := ⟨fbar k, (fbar k).continuous⟩
  let I : C(BordifiedOrbit, BordifiedOrbit) := ContinuousMap.id BordifiedOrbit
  let F' : C(BordifiedOrbit, BordifiedOrbit) := (fbar k).toHomotopyEquiv.toFun
  exact (RationalRelativeSingular.relativeMap_comp F I _ _ _ _ _).trans
    ((relativeMap_congr (f := I.comp F) (g := F'.comp I) (ContinuousMap.ext fun _ => rfl)
      _ _ _ _).trans (RationalRelativeSingular.relativeMap_comp I F' _ _ _ _ _).symm)

theorem fbarRel_excision (k : IntegralGL) (x : ↥(boundary principalSix)ᶜ) :
    pointExcisionMap x.val (boundary principalSix)ᶜ x.property ≫
        (homeomorphLocalIso (fbar k) x.val).hom =
      (homeomorphLocalIso (psi k) x).hom ≫
        pointExcisionMap (fbar k x.val) (boundary principalSix)ᶜ (psi k x).property := by
  have e1 := pointExcisionMap_eq_relativeMap x.val (boundary principalSix)ᶜ x.property
  have e2 := pointExcisionMap_eq_relativeMap (fbar k x.val) (boundary principalSix)ᶜ
    (psi k x).property
  unfold homeomorphLocalIso
  rw [relativeHomeomorphIso_hom, relativeHomeomorphIso_hom]
  refine (congrArg (· ≫ _) e1).trans ?_
  refine Eq.trans ?_ (congrArg (_ ≫ ·) e2).symm
  let V : C(↥(boundary principalSix)ᶜ, BordifiedOrbit) := ⟨Subtype.val, continuous_subtype_val⟩
  let F' : C(BordifiedOrbit, BordifiedOrbit) := (fbar k).toHomotopyEquiv.toFun
  let Ψ : C(↥(boundary principalSix)ᶜ, ↥(boundary principalSix)ᶜ) := (psi k).toHomotopyEquiv.toFun
  exact (RationalRelativeSingular.relativeMap_comp V F' _ _ _ _ _).trans
    ((relativeMap_congr (f := F'.comp V) (g := V.comp Ψ) (ContinuousMap.ext fun _ => rfl)
      _ _ _ _).trans (RationalRelativeSingular.relativeMap_comp Ψ V _ _ _ _ _).symm)

/-- **The relative fundamental class is invariant under `f̄_k`.** -/
theorem fundamentalClass_fbar (k : IntegralGL) :
    homologyMap (fbarRel k) 5 fundamentalClass = fundamentalClass := by
  apply fundamentalClass_unique
  intro y hy
  obtain ⟨x, rfl⟩ : ∃ x, fbar k x = y := ⟨(fbar k).symm y, (fbar k).apply_symm_apply y⟩
  have hx : x ∉ boundary principalSix := fun h => hy (fbar_mem_boundary k h)
  have hxc : x ∈ (boundary principalSix)ᶜ := hx
  have A : (homologyMap (boundaryPointMap (boundary principalSix) (fbar k x) hy) 5)
        ((homologyMap (fbarRel k) 5) fundamentalClass) =
      Lhom (fbar k) x 5 ((homologyMap (boundaryPointMap (boundary principalSix) x hx) 5)
        fundamentalClass) := by
    have h := congrArg (fun f : relativeChains (boundary principalSix) ⟶ localChains (fbar k x) =>
      ConcreteCategory.hom (homologyMap f 5) fundamentalClass) (fbarRel_point k x hx hy)
    simp only [homologyMap_comp] at h
    exact h
  rw [A, fundamentalClass_at_point x hx]
  have e := congrArg (fun f : localChains (⟨x, hxc⟩ : ↥(boundary principalSix)ᶜ) ⟶ localChains (fbar k x) =>
      homologyMap f 5) (fbarRel_excision k ⟨x, hxc⟩)
  have e1 := homologyMap_comp (pointExcisionMap x (boundary principalSix)ᶜ hxc)
    (homeomorphLocalIso (fbar k) x).hom 5
  have e2 := homologyMap_comp (homeomorphLocalIso (psi k) ⟨x, hxc⟩).hom
    (pointExcisionMap (fbar k x) (boundary principalSix)ᶜ (psi k ⟨x, hxc⟩).property) 5
  have e' : homologyMap (pointExcisionMap x (boundary principalSix)ᶜ hxc) 5 ≫
      homologyMap (homeomorphLocalIso (fbar k) x).hom 5 =
      homologyMap (homeomorphLocalIso (psi k) ⟨x, hxc⟩).hom 5 ≫
      homologyMap (pointExcisionMap (fbar k x) (boundary principalSix)ᶜ
        (psi k ⟨x, hxc⟩).property) 5 := by
    exact e1.symm.trans (e.trans e2)
  have C := psi_generator k ⟨x, hxc⟩
  have B' : Lhom (fbar k) x 5 ((homologyMap (pointExcisionMap x (boundary principalSix)ᶜ hxc) 5)
      (interiorOrientation.generator ⟨x, hxc⟩)) =
      (homologyMap (pointExcisionMap (fbar k x) (boundary principalSix)ᶜ
        (psi k ⟨x, hxc⟩).property) 5) (Lhom (psi k) ⟨x, hxc⟩ 5
          (interiorOrientation.generator ⟨x, hxc⟩)) :=
    congrArg (fun φ : (relativeChains ({(⟨x, hxc⟩ : ↥(boundary principalSix)ᶜ)}ᶜ :
      Set ↥(boundary principalSix)ᶜ)).homology 5 ⟶ (localChains (fbar k x)).homology 5 =>
      ConcreteCategory.hom φ (interiorOrientation.generator ⟨x, hxc⟩)) e'
  rw [B', C]
  rfl

end TernaryPeriodPolynomials.Argument.DualityEquivariance
