module

public import Mathlib

@[expose] public section


/-!
# Exactness of `N ↦ (N ⊗ X)_Q` for a projective `X`

Formalized by Claude Sonnet 5.5.

For a group `Q` and `X : Rep ℚ Q`, `FX X` is the functor `N ↦ (N ⊗ X)_Q` to `ModuleCat ℚ` (tensor, then coinvariants).
We prove that it preserves short exact sequences when `X` is projective (`FX_shortExact`), hence preserves homology
(`FX_preservesHomology`).  The proof: for the free representation `Rep.free ℚ Q α` the functor is `N ↦ (α →₀ N)`
(`Rep.coinvariantsTensorFreeLEquiv`), which is exact; a projective `X` is a retract of a free representation
(`epiFree`), and a retract of a functor preserving short exact sequences preserves them (`shortExact_of_retract`).
The functoriality in `X` is `FXmap`, and the braiding gives `brNat : (A ⊗ -)_Q ≅ FX A`.
-/

open CategoryTheory MonoidalCategory Representation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

variable {Q : Type} [Group Q]

/-- `N ↦ (N ⊗ X)_Q`. -/
abbrev FX (X : Rep.{0} ℚ Q) : Rep.{0} ℚ Q ⥤ ModuleCat ℚ :=
  tensorRight X ⋙ Rep.coinvariantsFunctor ℚ Q

theorem FX_map_mk {X N N' : Rep.{0} ℚ Q} (f : N ⟶ N') (n : N) (x : X) :
    ((FX X).map f).hom (Coinvariants.mk (N.ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)) =
      Coinvariants.mk (N'.ρ.tprod X.ρ) (f.hom n ⊗ₜ[ℚ] x) := rfl

/-- Functoriality in `X`. -/
def FXmap {X Y : Rep.{0} ℚ Q} (φ : X ⟶ Y) : FX X ⟶ FX Y where
  app N := (Rep.coinvariantsFunctor ℚ Q).map (N ◁ φ)
  naturality N N' f := by
    change (Rep.coinvariantsFunctor ℚ Q).map (f ▷ X) ≫ (Rep.coinvariantsFunctor ℚ Q).map (N' ◁ φ) =
      (Rep.coinvariantsFunctor ℚ Q).map (N ◁ φ) ≫ (Rep.coinvariantsFunctor ℚ Q).map (f ▷ Y)
    rw [← Functor.map_comp, ← Functor.map_comp, ← whisker_exchange]

theorem FXmap_mk {X Y N : Rep.{0} ℚ Q} (φ : X ⟶ Y) (n : N) (x : X) :
    ((FXmap φ).app N).hom (Coinvariants.mk (N.ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x)) =
      Coinvariants.mk (N.ρ.tprod Y.ρ) (n ⊗ₜ[ℚ] φ.hom x) := rfl

theorem FXmap_id (X : Rep.{0} ℚ Q) (N : Rep.{0} ℚ Q) : (FXmap (𝟙 X)).app N = 𝟙 _ := by
  change (Rep.coinvariantsFunctor ℚ Q).map (N ◁ 𝟙 X) = _
  rw [MonoidalCategory.whiskerLeft_id]
  exact CategoryTheory.Functor.map_id _ _

theorem FXmap_comp {X Y Z : Rep.{0} ℚ Q} (φ : X ⟶ Y) (ψ : Y ⟶ Z) (N : Rep.{0} ℚ Q) :
    (FXmap (φ ≫ ψ)).app N = (FXmap φ).app N ≫ (FXmap ψ).app N := by
  change (Rep.coinvariantsFunctor ℚ Q).map (N ◁ (φ ≫ ψ)) = _
  rw [MonoidalCategory.whiskerLeft_comp, Functor.map_comp]
  rfl

theorem FXmap_zero {X Y : Rep.{0} ℚ Q} (N : Rep.{0} ℚ Q) : (FXmap (0 : X ⟶ Y)).app N = 0 := by
  change (Rep.coinvariantsFunctor ℚ Q).map (N ◁ (0 : X ⟶ Y)) = 0
  rw [MonoidalPreadditive.whiskerLeft_zero]
  exact CategoryTheory.Functor.map_zero _ _ _

/-- The braiding identifies `(A ⊗ N)_Q` with `(N ⊗ A)_Q`, naturally in `N`. -/
def brNat (A : Rep.{0} ℚ Q) : (Rep.coinvariantsTensor ℚ Q).obj A ≅ FX A :=
  NatIso.ofComponents (fun P => (Rep.coinvariantsFunctor ℚ Q).mapIso (β_ A P))
    (fun {P P'} f => by
      change (Rep.coinvariantsFunctor ℚ Q).map (A ◁ f) ≫ (Rep.coinvariantsFunctor ℚ Q).map (β_ A P').hom =
        (Rep.coinvariantsFunctor ℚ Q).map (β_ A P).hom ≫ (Rep.coinvariantsFunctor ℚ Q).map (f ▷ A)
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact BraidedCategory.braiding_naturality_right A f)


section Free

variable (α : Type) [DecidableEq α]

/-- The finsupp functor on `ModuleCat ℚ`. -/
def finsuppFunctor : ModuleCat ℚ ⥤ ModuleCat ℚ where
  obj M := ModuleCat.of ℚ (α →₀ M)
  map f := ModuleCat.ofHom (Finsupp.mapRange.linearMap f.hom)

theorem coinvFree_natural {N N' : Rep.{0} ℚ Q} (f : N ⟶ N')
    (x : ((FX (Rep.free ℚ Q α)).obj N)) :
    Rep.coinvariantsTensorFreeLEquiv N' α (((FX (Rep.free ℚ Q α)).map f).hom x) =
      Finsupp.mapRange.linearMap f.hom.toLinearMap (Rep.coinvariantsTensorFreeLEquiv N α x) := by
  have key : (Rep.coinvariantsTensorFreeLEquiv N' α).toLinearMap ∘ₗ
        ((FX (Rep.free ℚ Q α)).map f).hom =
      Finsupp.mapRange.linearMap f.hom.toLinearMap ∘ₗ (Rep.coinvariantsTensorFreeLEquiv N α).toLinearMap := by
    refine Coinvariants.hom_ext (TensorProduct.ext (LinearMap.ext fun a => Finsupp.lhom_ext' fun i =>
      MonoidAlgebra.lhom_ext' fun g => LinearMap.ext fun r => ?_))
    simp [Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single]
    rw [Rep.hom_comm_apply]
  exact LinearMap.congr_fun key x

/-- Short exactness of `N ↦ (N ⊗ free α)_Q`. -/
theorem FX_free_shortExact (S : ShortComplex (Rep.{0} ℚ Q)) (hS : S.ShortExact) :
    (S.map (FX (Rep.free ℚ Q α))).ShortExact := by
  have hf : Function.Injective S.f.hom := (Rep.mono_iff_injective S.f).1 hS.mono_f
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective S.g).1 hS.epi_g
  have hex : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
    (hS.exact.map (forget₂ (Rep.{0} ℚ Q) (ModuleCat ℚ))).moduleCat_range_eq_ker
  have hker : LinearMap.ker S.f.hom.toLinearMap = ⊥ := LinearMap.ker_eq_bot.2 hf
  let e : ∀ N : Rep.{0} ℚ Q, ((FX (Rep.free ℚ Q α)).obj N) ≃ₗ[ℚ] (α →₀ N) :=
    fun N => Rep.coinvariantsTensorFreeLEquiv N α
  have hnat : ∀ {N N' : Rep.{0} ℚ Q} (h : N ⟶ N') (x : ((FX (Rep.free ℚ Q α)).obj N)),
      e N' (((FX (Rep.free ℚ Q α)).map h).hom x) =
        Finsupp.mapRange.linearMap h.hom.toLinearMap (e N x) := fun h x => coinvFree_natural α h x
  have hinj : Function.Injective (((FX (Rep.free ℚ Q α)).map S.f).hom) := by
    intro x y hxy
    have h1 : e S.X₂ (((FX (Rep.free ℚ Q α)).map S.f).hom x) =
        e S.X₂ (((FX (Rep.free ℚ Q α)).map S.f).hom y) := congrArg (e S.X₂) hxy
    rw [hnat, hnat] at h1
    apply (e S.X₁).injective
    simp only [Finsupp.mapRange.linearMap_apply] at h1
    exact Finsupp.mapRange_injective _ (map_zero _) hf h1
  have hsurj : Function.Surjective (((FX (Rep.free ℚ Q α)).map S.g).hom) := by
    intro z
    obtain ⟨w, hw⟩ := Finsupp.mapRange_surjective _ (map_zero _) hg (e S.X₃ z)
    refine ⟨(e S.X₂).symm w, (e S.X₃).injective ?_⟩
    rw [hnat]
    simpa [Finsupp.mapRange.linearMap_apply] using hw
  have hmono : Mono ((S.map (FX (Rep.free ℚ Q α))).f) := by
    change Mono ((FX (Rep.free ℚ Q α)).map S.f)
    rw [ModuleCat.mono_iff_injective]
    exact hinj
  have hepi : Epi ((S.map (FX (Rep.free ℚ Q α))).g) := by
    change Epi ((FX (Rep.free ℚ Q α)).map S.g)
    rw [ModuleCat.epi_iff_surjective]
    exact hsurj
  have hexact : (S.map (FX (Rep.free ℚ Q α))).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    show ∀ x : (FX (Rep.free ℚ Q α)).obj S.X₂, ((FX (Rep.free ℚ Q α)).map S.g).hom x = 0 →
      ∃ x₁ : (FX (Rep.free ℚ Q α)).obj S.X₁, ((FX (Rep.free ℚ Q α)).map S.f).hom x₁ = x
    intro x hx
    have h0 : Finsupp.mapRange.linearMap S.g.hom.toLinearMap (e S.X₂ x) = 0 := by
      rw [← hnat, hx, map_zero]
    have hmem : e S.X₂ x ∈ LinearMap.range (Finsupp.mapRange.linearMap (α := α) S.f.hom.toLinearMap) := by
      rw [Finsupp.range_mapRange_linearMap _ hker, hex]
      have : e S.X₂ x ∈ LinearMap.ker (Finsupp.mapRange.linearMap (α := α) S.g.hom.toLinearMap) := h0
      rw [Finsupp.ker_mapRange] at this
      exact this
    obtain ⟨w, hw⟩ := hmem
    refine ⟨(e S.X₁).symm w, (e S.X₂).injective ?_⟩
    rw [hnat]
    simpa using hw
  exact { exact := hexact, mono_f := hmono, epi_g := hepi }

end Free

section Retract

variable {F G : Rep.{0} ℚ Q ⥤ ModuleCat ℚ} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

/-- A retract of a functor preserving short exact sequences preserves short exact sequences. -/
theorem shortExact_of_retract (i : F ⟶ G) (r : G ⟶ F) (h : ∀ N, i.app N ≫ r.app N = 𝟙 _)
    (hG : ∀ S : ShortComplex (Rep.{0} ℚ Q), S.ShortExact → (S.map G).ShortExact)
    (S : ShortComplex (Rep.{0} ℚ Q)) (hS : S.ShortExact) : (S.map F).ShortExact := by
  have hri : ∀ N (x : F.obj N), (r.app N).hom ((i.app N).hom x) = x := fun N x =>
    congrArg (fun φ => φ.hom x) (h N)
  have hinjG : Function.Injective (G.map S.f).hom :=
    (ModuleCat.mono_iff_injective _).1 (hG S hS).mono_f
  have hsurjG : Function.Surjective (G.map S.g).hom :=
    (ModuleCat.epi_iff_surjective _).1 (hG S hS).epi_g
  have hexG := (ShortComplex.moduleCat_exact_iff _).1 (hG S hS).exact
  have nat_i : ∀ {N N' : Rep.{0} ℚ Q} (f : N ⟶ N') (x : F.obj N),
      (i.app N').hom ((F.map f).hom x) = (G.map f).hom ((i.app N).hom x) := fun f x =>
    congrArg (fun φ => φ.hom x) (i.naturality f)
  have nat_r : ∀ {N N' : Rep.{0} ℚ Q} (f : N ⟶ N') (x : G.obj N),
      (r.app N').hom ((G.map f).hom x) = (F.map f).hom ((r.app N).hom x) := fun f x =>
    congrArg (fun φ => φ.hom x) (r.naturality f)
  have hinj : Function.Injective (F.map S.f).hom := by
    intro x y hxy
    have h1 : (G.map S.f).hom ((i.app S.X₁).hom x) = (G.map S.f).hom ((i.app S.X₁).hom y) := by
      rw [← nat_i, ← nat_i, hxy]
    have := hinjG h1
    rw [← hri _ x, ← hri _ y, this]
  have hsurj : Function.Surjective (F.map S.g).hom := by
    intro z
    obtain ⟨w, hw⟩ := hsurjG ((i.app S.X₃).hom z)
    refine ⟨(r.app S.X₂).hom w, ?_⟩
    rw [← nat_r, hw, hri]
  have hmono : Mono ((S.map F).f) := by
    change Mono (F.map S.f)
    rw [ModuleCat.mono_iff_injective]
    exact hinj
  have hepi : Epi ((S.map F).g) := by
    change Epi (F.map S.g)
    rw [ModuleCat.epi_iff_surjective]
    exact hsurj
  have hexact : (S.map F).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    show ∀ x : F.obj S.X₂, (F.map S.g).hom x = 0 → ∃ x₁ : F.obj S.X₁, (F.map S.f).hom x₁ = x
    intro x hx
    have h0 : (G.map S.g).hom ((i.app S.X₂).hom x) = 0 := by
      rw [← nat_i, hx, map_zero]
    obtain ⟨w, hw⟩ := hexG _ h0
    replace hw : (G.map S.f).hom w = (i.app S.X₂).hom x := hw
    refine ⟨(r.app S.X₁).hom w, ?_⟩
    have : (F.map S.f).hom ((r.app S.X₁).hom w) = (r.app S.X₂).hom ((G.map S.f).hom w) :=
      (nat_r S.f w).symm
    rw [this, hw, hri]
  exact { exact := hexact, mono_f := hmono, epi_g := hepi }

end Retract

section Projective

open Classical in
/-- The canonical epimorphism from the free representation on the underlying set of `X`. -/
def epiFree (X : Rep.{0} ℚ Q) : Rep.free ℚ Q (↑X : Type) ⟶ X :=
  Rep.ofHom (Representation.freeLift X.ρ (fun x : X => x))

theorem epiFree_epi (X : Rep.{0} ℚ Q) : Epi (epiFree X) := by
  classical
  rw [Rep.epi_iff_surjective]
  intro x
  refine ⟨Finsupp.single x (MonoidAlgebra.single (1 : Q) (1 : ℚ)), ?_⟩
  simp [epiFree, Representation.freeLift_single_single]

/-- For a projective `X`, the functor `N ↦ (N ⊗ X)_Q` preserves short exact sequences. -/
theorem FX_shortExact (X : Rep.{0} ℚ Q) [Projective X] (S : ShortComplex (Rep.{0} ℚ Q))
    (hS : S.ShortExact) : (S.map (FX X)).ShortExact := by
  classical
  have := epiFree_epi X
  let s : X ⟶ Rep.free ℚ Q (↑X : Type) := Projective.factorThru (𝟙 X) (epiFree X)
  have hs : s ≫ epiFree X = 𝟙 X := Projective.factorThru_comp _ _
  refine shortExact_of_retract (FXmap s) (FXmap (epiFree X)) ?_
    (fun S hS => FX_free_shortExact _ S hS) S hS
  intro N
  rw [← FXmap_comp, hs, FXmap_id]

theorem FX_preservesHomology (X : Rep.{0} ℚ Q) [Projective X] : (FX X).PreservesHomology :=
  ((Functor.exact_tfae (FX X)).out 1 3).1 (fun S hS => FX_shortExact X S hS)

end Projective

end TernaryPeriodPolynomials.Argument.HochschildSerre
