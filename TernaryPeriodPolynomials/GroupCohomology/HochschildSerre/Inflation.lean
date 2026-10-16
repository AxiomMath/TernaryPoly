module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Exactness
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyEdge

@[expose] public section


/-!
# Inflation of the dual Farey tree and of the functor `(N ⊗ X)_Q`

Formalized by Claude Sonnet 5.5.

For a surjective homomorphism `π : Q →* Γ` and `Γ`-representations `N, X`, the coinvariants `(res N ⊗ res X)_Q` and
`(N ⊗ X)_Γ` coincide (`inflEquiv`, natural in `X` and `N`: `inflEquiv_nat`), hence the kernels of `(N ⊗ φ)_Q` and
`(N ⊗ φ)_Γ` are isomorphic (`kerInflEquiv`).  If `ker π` is finite, the inflation of the dual Farey tree
(`Revision/Proofs/BinaryDuality`) is a short exact sequence `0 → res P1 → res P0 → 1 → 0` of projective `Q`-representations
(`sesQ_shortExact`, `projective_res_P0`, `projective_res_P1`; stabilizers in `Q` are preimages of the finite stabilizers in
`GL₂(ℤ)`, `res_ofMulAction_projective`).  Finally `kerNatEquiv` moves the kernel of a natural transformation along an
isomorphism of the argument.
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

section Inflation

variable {Q Γ : Type} [Group Q] [Group Γ] (π : Q →* Γ)

/-- `(res W)_Q → W_Γ`. -/
def coinvResTo (W : Rep.{0} ℚ Γ) : Coinvariants (Rep.res π W).ρ →ₗ[ℚ] Coinvariants W.ρ :=
  Coinvariants.lift _ (Coinvariants.mk W.ρ) (fun q => LinearMap.ext fun v =>
    Coinvariants.mk_self_apply W.ρ (π q) v)

/-- `W_Γ → (res W)_Q` for a surjective `π`. -/
def coinvResFrom (hπ : Function.Surjective π) (W : Rep.{0} ℚ Γ) :
    Coinvariants W.ρ →ₗ[ℚ] Coinvariants (Rep.res π W).ρ :=
  Coinvariants.lift W.ρ (Coinvariants.mk (Rep.res π W).ρ) (fun g => by
    obtain ⟨q, rfl⟩ := hπ g
    exact LinearMap.ext fun v => Coinvariants.mk_self_apply (Rep.res π W).ρ q v)

def coinvResEquiv (hπ : Function.Surjective π) (W : Rep.{0} ℚ Γ) :
    Coinvariants (Rep.res π W).ρ ≃ₗ[ℚ] Coinvariants W.ρ :=
  LinearEquiv.ofLinearMap (coinvResTo π W) (coinvResFrom π hπ W)
    (Coinvariants.hom_ext (LinearMap.ext fun _ => rfl))
    (Coinvariants.hom_ext (LinearMap.ext fun _ => rfl))

theorem coinvResEquiv_mk (hπ : Function.Surjective π) (W : Rep.{0} ℚ Γ) (v : W) :
    coinvResEquiv π hπ W (Coinvariants.mk (Rep.res π W).ρ v) = Coinvariants.mk W.ρ v := rfl

/-- `(res N ⊗ res X)_Q ≃ (N ⊗ X)_Γ`. -/
def inflEquiv (hπ : Function.Surjective π) (N X : Rep.{0} ℚ Γ) :
    ((FX (Rep.res π X)).obj (Rep.res π N)) ≃ₗ[ℚ] (FX X).obj N :=
  coinvResEquiv π hπ (N ⊗ X)

theorem inflEquiv_mk (hπ : Function.Surjective π) (N X : Rep.{0} ℚ Γ) (n : N) (x : X) :
    inflEquiv π hπ N X (Coinvariants.mk _ (n ⊗ₜ[ℚ] x)) = Coinvariants.mk (N.ρ.tprod X.ρ) (n ⊗ₜ[ℚ] x) := rfl

theorem inflEquiv_nat (hπ : Function.Surjective π) {X Y : Rep.{0} ℚ Γ} (φ : X ⟶ Y) (N : Rep.{0} ℚ Γ)
    (x : (FX (Rep.res π X)).obj (Rep.res π N)) :
    inflEquiv π hπ N Y (((FXmap (Rep.resMap π φ)).app (Rep.res π N)).hom x) =
      ((FXmap φ).app N).hom (inflEquiv π hπ N X x) := by
  induction x using Coinvariants.induction_on with
  | h v =>
    induction v using TensorProduct.inductionOn with
    | tmul n x => rfl
    | add u w hu hw =>
      simp only [map_add, hu, hw]

/-- The kernel of `(N ⊗ φ)_Q` after inflation is the kernel of `(N ⊗ φ)_Γ`. -/
def kerInflEquiv (hπ : Function.Surjective π) {X Y : Rep.{0} ℚ Γ} (φ : X ⟶ Y) (N : Rep.{0} ℚ Γ) :
    LinearMap.ker ((FXmap (Rep.resMap π φ)).app (Rep.res π N)).hom ≃ₗ[ℚ]
      LinearMap.ker ((FXmap φ).app N).hom :=
  LinearEquiv.ofSubmodules (inflEquiv π hπ N X) _ _ (by
    refine Submodule.ext fun y => ?_
    rw [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [LinearMap.mem_ker] at hx
      have h := inflEquiv_nat π hπ φ N x
      change ((FXmap φ).app N).hom (inflEquiv π hπ N X x) = 0
      rw [← h, hx, map_zero]
    · intro hy
      refine ⟨(inflEquiv π hπ N X).symm y, ?_, (inflEquiv π hπ N X).apply_symm_apply y⟩
      rw [LinearMap.mem_ker]
      apply (inflEquiv π hπ N Y).injective
      rw [inflEquiv_nat π hπ φ N, map_zero]
      have : ((FXmap φ).app N).hom ((inflEquiv π hπ N X) ((inflEquiv π hπ N X).symm y)) = 0 := by
        rw [(inflEquiv π hπ N X).apply_symm_apply]; exact hy
      exact this)

end Inflation

/-- The kernel of a natural transformation's component is invariant under isomorphism of the argument. -/
def kerNatEquiv {C : Type*} [Category C] {F G : C ⥤ ModuleCat ℚ} (τ : F ⟶ G) {M M' : C}
    (e : M ≅ M') :
    LinearMap.ker (τ.app M).hom ≃ₗ[ℚ] LinearMap.ker (τ.app M').hom :=
  LinearEquiv.ofSubmodules (F.mapIso e).toLinearEquiv _ _ (by
    have hnat : ∀ x : F.obj M, (τ.app M').hom ((F.map e.hom).hom x) =
        (G.map e.hom).hom ((τ.app M).hom x) := fun x =>
      congrArg (fun φ => φ.hom x) (τ.naturality e.hom)
    refine Submodule.ext fun y => ?_
    rw [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [LinearMap.mem_ker] at hx
      change (τ.app M').hom ((F.map e.hom).hom x) = 0
      rw [hnat, hx, map_zero]
    · intro hy
      refine ⟨(F.mapIso e).toLinearEquiv.symm y, ?_, (F.mapIso e).toLinearEquiv.apply_symm_apply y⟩
      rw [LinearMap.mem_ker]
      have h2 : (τ.app M').hom ((F.map e.hom).hom ((F.mapIso e).toLinearEquiv.symm y)) = 0 := by
        have : (F.map e.hom).hom ((F.mapIso e).toLinearEquiv.symm y) = y :=
          (F.mapIso e).toLinearEquiv.apply_symm_apply y
        rw [this]; exact hy
      rw [hnat] at h2
      have hinj : Function.Injective (G.map e.hom).hom :=
        (G.mapIso e).toLinearEquiv.injective
      apply hinj
      rw [h2, map_zero])

section FareyInflation

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.BinaryDuality
  TernaryPoly.RankTwoAugmentedFrames

variable {Q : Type} [Group Q] (π : Q →* IntegralGL)

theorem preimage_fibre_finite (hker : (π.ker : Set Q).Finite) (b : IntegralGL) : (π ⁻¹' {b}).Finite := by
  by_cases h : ∃ q0, π q0 = b
  · obtain ⟨q0, hq0⟩ := h
    refine (hker.image (fun k => q0 * k)).subset ?_
    intro q hq
    refine ⟨q0⁻¹ * q, ?_, by simp⟩
    change π (q0⁻¹ * q) = 1
    have : π q = b := hq
    rw [map_mul, map_inv, hq0, this]; simp
  · convert Set.finite_empty
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun hq => h ⟨q, hq⟩

theorem res_ofMulAction_projective (hker : (π.ker : Set Q).Finite) {X : Type} [MulAction IntegralGL X]
    (hfin : ∀ x : X, Finite (MulAction.stabilizer IntegralGL x)) :
    Projective (Rep.res π (Rep.ofMulAction ℚ IntegralGL X)) := by
  let _ : MulAction Q X := MulAction.compHom X π
  have e : Rep.res π (Rep.ofMulAction ℚ IntegralGL X) = Rep.ofMulAction ℚ Q X := rfl
  rw [e]
  apply ofMulAction_projective
  intro x
  have h1 : ((MulAction.stabilizer IntegralGL x : Set IntegralGL)).Finite := Set.toFinite _
  have h2 : (π ⁻¹' (MulAction.stabilizer IntegralGL x : Set IntegralGL)).Finite :=
    h1.preimage' (fun b _ => preimage_fibre_finite π hker b)
  have h3 : ((MulAction.stabilizer Q x : Set Q)).Finite := by
    refine h2.subset ?_
    intro q hq
    change π q • x = x
    exact hq
  exact h3.to_subtype

theorem projective_res_P0 (hker : (π.ker : Set Q).Finite) : Projective (Rep.res π P0) :=
  res_ofMulAction_projective π hker tri_stabilizer_finite

theorem projective_res_PE (hker : (π.ker : Set Q).Finite) : Projective (Rep.res π PE) :=
  res_ofMulAction_projective π hker ote_stabilizer_finite

theorem projective_res_P1 (hker : (π.ker : Set Q).Finite) : Projective (Rep.res π P1) := by
  have := projective_res_PE π hker
  exact (⟨(Rep.resFunctor π).map inclP1, (Rep.resFunctor π).map retrP1, by
    rw [← CategoryTheory.Functor.map_comp, inclP1_retrP1, CategoryTheory.Functor.map_id]⟩ :
      Retract (Rep.res π P1) (Rep.res π PE)).projective

/-- The augmentation of the inflated dual Farey tree. -/
def epsQ : Rep.res π P0 ⟶ Rep.trivial ℚ Q ℚ := Rep.resMap π epsMap

theorem resD1_epsQ : Rep.resMap π d1 ≫ epsQ π = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  exact eps_d1 a

/-- The inflated dual Farey tree is a short exact sequence of `Q`-representations. -/
theorem sesQ_shortExact :
    (ShortComplex.mk (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)).ShortExact where
  exact := (forget₂ _ (ModuleCat ℚ)).reflects_exact_of_faithful _ <| by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    ext c
    change c ∈ LinearMap.range d1.hom.toLinearMap ↔ c ∈ LinearMap.ker epsMap.hom.toLinearMap
    constructor
    · rintro ⟨a, rfl⟩
      exact eps_d1 a
    · intro hc
      exact exists_d1_preimage c hc
  mono_f := by
    rw [Rep.mono_iff_injective]
    exact d1_injective
  epi_g := by
    rw [Rep.epi_iff_surjective]
    exact epsMap_surjective

end FareyInflation

end TernaryPeriodPolynomials.Argument.HochschildSerre
