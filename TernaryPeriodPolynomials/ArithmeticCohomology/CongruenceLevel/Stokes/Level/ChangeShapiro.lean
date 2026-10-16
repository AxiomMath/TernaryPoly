module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Bridge
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EdgeNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ConjRestriction
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic.Group

@[expose] public section


/-!
# Shapiro–Mackey for `Fun(G/Δ, E)` in the homogeneous model, and the coordinates of the induced class at the cosets

Formalized by Claude Sonnet 5.5.

For a group `G`, a subgroup `Δ` and a representation `ρ` of `G` on `E`, `permRep ρ Δ` is the `G`-module `Fun(G/Δ, E)` with
`(s·f)(x) = ρ(s) f(s⁻¹x)` (the coinduced module of the finite quotient).  In the homogeneous model of `GeneralEisenstein.Homogeneous` induction
is explicit: for a `Δ`-equivariant function `f` on `(k+1)`-tuples, `indFun f g (uΔ) = ρ(u) f(u⁻¹ g)` is `G`-equivariant (`indFun_equivariant`),
independent of the representative `u` (`indFun_eq`), commutes with the differentials (`indL_rd1`, `indL_rd2`), and has base coordinate `f`
(`evL_indL`, `indL_evL`).  `indZ_mem`: `(a, b) ↦ indFun f ![1, a, a b]` is a Mathlib 2-cocycle of `G` with coefficients `Fun(G/Δ, E)`.

`exists_ind_class` (the Mackey formula): every class `c ∈ H²(Δ, E)` (Mathlib) is the base coordinate of a class `c_V ∈ H²(G, Fun(G/Δ, E))` such that for
every subgroup `K` and `u` with `u⁻¹ K u ≤ Δ` the `uΔ`-coordinate of `res_K c_V` is the pull-back of `c` along `k ↦ u⁻¹ k u` twisted by `ρ(u)`
(`coordH`, `kappa`).  Proof: the two cocycles differ by the prism coboundary of `Bridge.bridge_conj`.
-/

open CategoryTheory GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

section Ind

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E)
  (Δ : Subgroup G)

/-- `Fun(G/Δ, E)` with `(s · f)(x) = ρ(s) f(s⁻¹ x)`: the coinduced module `Coind_Δ^G E` of the finite quotient (`Δ` normal). -/
def permRep : Representation ℂ G ((G ⧸ Δ) → E) where
  toFun s :=
    { toFun := fun f x => ρ s (f (s⁻¹ • x))
      map_add' := fun f g => by funext x; simp
      map_smul' := fun a f => by funext x; simp }
  map_one' := by
    ext f x
    simp
  map_mul' s t := by
    ext f x
    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, mul_inv_rev, map_mul]
    rw [mul_smul]

theorem permRep_apply (s : G) (f : (G ⧸ Δ) → E) (x : G ⧸ Δ) : permRep ρ Δ s f x = ρ s (f (s⁻¹ • x)) := rfl

/-- The induced cochain at a coset `x`, computed with a chosen representative `x.out`. -/
def indFun {k : ℕ} (f : (Fin (k + 1) → G) → E) (g : Fin (k + 1) → G) : (G ⧸ Δ) → E :=
  fun x => ρ (Quotient.out x) (f (fun i => (Quotient.out x)⁻¹ * g i))

theorem indFun_eq {k : ℕ} {f : (Fin (k + 1) → G) → E} (hf : ∀ (γ : Δ) (y : Fin (k + 1) → G), f (fun i => γ.val * y i) = ρ γ.val (f y))
    (g : Fin (k + 1) → G) (u : G) :
    indFun ρ Δ f g (u : G ⧸ Δ) = ρ u (f (fun i => u⁻¹ * g i)) := by
  have hu : ((Quotient.out (u : G ⧸ Δ) : G) : G ⧸ Δ) = (u : G ⧸ Δ) := Quotient.out_eq' _
  obtain ⟨δ, hδ⟩ : ∃ δ : Δ, (Quotient.out (u : G ⧸ Δ) : G) = u * δ.val := by
    have := Δ.inv_mem (QuotientGroup.eq.mp hu)
    exact ⟨⟨u⁻¹ * Quotient.out (u : G ⧸ Δ), by simpa using this⟩, by simp⟩
  unfold indFun
  rw [hδ]
  have e : (fun i => (u * δ.val)⁻¹ * g i) = fun i => δ.val⁻¹ * (u⁻¹ * g i) := by
    funext i; group
  rw [e, hf ⟨δ.val⁻¹, Δ.inv_mem δ.2⟩ _, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (ρ δ.val), ← map_mul]
  simp

theorem smul_mk_quot (s u : G) : s • (u : G ⧸ Δ) = ((s * u : G) : G ⧸ Δ) := rfl

theorem indFun_equivariant {k : ℕ} {f : (Fin (k + 1) → G) → E}
    (hf : ∀ (γ : Δ) (y : Fin (k + 1) → G), f (fun i => γ.val * y i) = ρ γ.val (f y))
    (s : G) (g : Fin (k + 1) → G) :
    indFun ρ Δ f (fun i => s * g i) = permRep ρ Δ s (indFun ρ Δ f g) := by
  funext x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  rw [permRep_apply, smul_mk_quot, indFun_eq ρ Δ hf g (s⁻¹ * u), indFun_eq ρ Δ hf (fun i => s * g i) u]
  rw [← Module.End.mul_apply, ← map_mul]
  have e : (fun i => (s⁻¹ * u)⁻¹ * g i) = fun i => u⁻¹ * (s * g i) := by funext i; group
  rw [e]
  congr 2
  group

theorem indFun_cochain {k : ℕ} {f : (Fin (k + 1) → G) → E}
    (hf : ∀ (γ : Δ) (y : Fin (k + 1) → G), f (fun i => γ.val * y i) = ρ γ.val (f y)) (Γ : Subgroup G) :
    ∀ (γ : Γ) (y : Fin (k + 1) → G), indFun ρ Δ f (fun i => γ.val * y i) = permRep ρ Δ γ.val (indFun ρ Δ f y) :=
  fun γ y => indFun_equivariant ρ Δ hf γ.val y

/-- The induction of raw functions, linear in `f`. -/
def indL {k : ℕ} : FunSpace G E k →ₗ[ℂ] FunSpace G ((G ⧸ Δ) → E) k where
  toFun f := indFun ρ Δ f
  map_add' f g := by funext y x; simp [indFun]
  map_smul' a f := by funext y x; simp [indFun]

theorem indL_apply {k : ℕ} (f : FunSpace G E k) (g : Fin (k + 1) → G) (x : G ⧸ Δ) :
    indL ρ Δ f g x = ρ (Quotient.out x) (f (fun i => (Quotient.out x)⁻¹ * g i)) := rfl

theorem indL_rd1 (f : FunSpace G E 1) : indL ρ Δ (rd1 f) = rd1 (indL ρ Δ f) := by
  funext g x
  have h : ∀ (c : G) (a b : Fin 3), (fun i : Fin 2 => c * (![g a, g b] : Fin 2 → G) i) = ![c * g a, c * g b] := by
    intro c a b; funext i; fin_cases i <;> rfl
  simp only [indL_apply, rd1, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.sub_apply, map_add, map_sub, h]

theorem indL_rd2 (f : FunSpace G E 2) : indL ρ Δ (rd2 f) = rd2 (indL ρ Δ f) := by
  funext g x
  have h : ∀ (c : G) (a b d : Fin 4), (fun i : Fin 3 => c * (![g a, g b, g d] : Fin 3 → G) i) =
      ![c * g a, c * g b, c * g d] := by
    intro c a b d; funext i; fin_cases i <;> rfl
  simp only [indL_apply, rd2, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.sub_apply, map_add, map_sub, h]

/-- Evaluation at the base coset. -/
def evL {k : ℕ} : FunSpace G ((G ⧸ Δ) → E) k →ₗ[ℂ] FunSpace G E k where
  toFun F g := F g ((1 : G) : G ⧸ Δ)
  map_add' F H := by funext g; simp
  map_smul' a F := by funext g; simp

theorem evL_indL {k : ℕ} {f : FunSpace G E k} (hf : IsEq ρ Δ f) : evL Δ (indL ρ Δ f) = f := by
  funext g
  change indFun ρ Δ f g ((1 : G) : G ⧸ Δ) = f g
  rw [indFun_eq ρ Δ (fun γ y => hf γ.1 γ.2 y) g 1]
  simp

theorem indL_evL {k : ℕ} {F : FunSpace G ((G ⧸ Δ) → E) k} (hF : IsEq (permRep ρ Δ) ⊤ F) :
    indL ρ Δ (evL Δ F) = F := by
  funext g x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  have hf : ∀ (γ : Δ) (y : Fin (k + 1) → G), evL Δ F (fun i => γ.val * y i) = ρ γ.val (evL Δ F y) := by
    intro γ y
    change F (fun i => γ.val * y i) ((1 : G) : G ⧸ Δ) = ρ γ.val (F y ((1 : G) : G ⧸ Δ))
    rw [hF γ.val (Subgroup.mem_top _) y, permRep_apply]
    congr 2
    have : γ.val⁻¹ • ((1 : G) : G ⧸ Δ) = ((1 : G) : G ⧸ Δ) := by
      rw [smul_mk_quot, mul_one]
      exact QuotientGroup.eq.mpr (by simp)
    rw [this]
  change indFun ρ Δ (evL Δ F) g (u : G ⧸ Δ) = F g (u : G ⧸ Δ)
  rw [indFun_eq ρ Δ hf g u]
  have := hF u (Subgroup.mem_top _) (fun i => u⁻¹ * g i)
  have e : (fun i => u * (u⁻¹ * g i)) = g := by funext i; group
  rw [e] at this
  rw [this, permRep_apply]
  have hu : u⁻¹ • (u : G ⧸ Δ) = ((1 : G) : G ⧸ Δ) := by rw [smul_mk_quot, inv_mul_cancel]
  rw [hu]
  rfl

theorem isEq_indL {k : ℕ} {f : FunSpace G E k} (hf : IsEq ρ Δ f) (Γ : Subgroup G) :
    IsEq (permRep ρ Δ) Γ (indL ρ Δ f) :=
  fun γ _ x => indFun_equivariant ρ Δ (fun δ y => hf δ.1 δ.2 y) γ x

/-- **The induced Mathlib 2-cocycle**: `(a, b) ↦ (x ↦ ρ(u) f(u⁻¹, u⁻¹a, u⁻¹ab))` for `x = uΔ`, from a `Δ`-equivariant homogeneous 2-cocycle `f`. -/
def indZ (f : FunSpace G E 2) : G × G → ((G ⧸ Δ) → E) := fun p => indL ρ Δ f ![1, p.1, p.1 * p.2]

theorem indZ_mem {f : FunSpace G E 2} (hf : IsEq ρ Δ f) (hz : rd2 f = 0) :
    indZ ρ Δ f ∈ groupCohomology.cocycles₂ (Rep.of (permRep ρ Δ)) := by
  rw [groupCohomology.mem_cocycles₂_iff]
  intro g h j
  have hF : IsEq (permRep ρ Δ) ⊤ (indL ρ Δ f) := isEq_indL ρ Δ hf ⊤
  have h0 : rd2 (indL ρ Δ f) = 0 := by rw [← indL_rd2, hz, map_zero]
  have e0 := congrFun h0 ![1, g, g * h, g * h * j]
  have e1 : (permRep ρ Δ) g (indL ρ Δ f ![1, h, h * j]) = indL ρ Δ f ![g, g * h, g * h * j] := by
    have := hF g (Subgroup.mem_top _) ![1, h, h * j]
    have et : (fun i => g * (![1, h, h * j] : Fin 3 → G) i) = ![g, g * h, g * h * j] := by
      funext i; fin_cases i <;> simp [mul_assoc]
    rw [et] at this
    exact this.symm
  change indL ρ Δ f ![1, g * h, g * h * j] + indL ρ Δ f ![1, g, g * h] =
    (permRep ρ Δ) g (indL ρ Δ f ![1, h, h * j]) + indL ρ Δ f ![1, g, g * (h * j)]
  rw [e1, ← mul_assoc g h j]
  simp only [rd2, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at e0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at e0
  linear_combination (norm := module) -e0

end Ind

section Mackey

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ : Subgroup G)

/-- The conjugate subgroup `uΔu⁻¹`. -/
def Δconj (u : G) : Subgroup G where
  carrier := {y | u⁻¹ * y * u ∈ Δ}
  mul_mem' := fun {a b} ha hb => by
    have : u⁻¹ * (a * b) * u = (u⁻¹ * a * u) * (u⁻¹ * b * u) := by group
    show u⁻¹ * (a * b) * u ∈ Δ
    rw [this]; exact Δ.mul_mem ha hb
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    have : u⁻¹ * a⁻¹ * u = (u⁻¹ * a * u)⁻¹ := by group
    show u⁻¹ * a⁻¹ * u ∈ Δ
    rw [this]; exact Δ.inv_mem ha

theorem isConj_Δconj (u : G) : IsConj Δ (Δconj Δ u) u := fun _ => Iff.rfl

/-- The coordinate of a function on `G ⧸ Δ` at the coset `uΔ`. -/
def evAt (u : G) : ((G ⧸ Δ) → E) →ₗ[ℂ] E := LinearMap.proj (R := ℂ) (φ := fun _ : G ⧸ Δ => E) (u : G ⧸ Δ)

theorem evAt_hT (K : Subgroup G) (u : G) (hu : ∀ k ∈ K, u⁻¹ * k * u ∈ Δ) (k : K)
    (v : Rep.res K.subtype (Rep.of (permRep ρ Δ))) :
    evAt Δ u ((Rep.res K.subtype (Rep.of (permRep ρ Δ))).ρ ((MonoidHom.id K) k) v) =
      (Rep.of (ρ.comp K.subtype)).ρ k (evAt Δ u v) := by
  change permRep ρ Δ k.val v (u : G ⧸ Δ) = ρ k.val (v (u : G ⧸ Δ))
  rw [permRep_apply]
  congr 2
  rw [smul_mk_quot]
  exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hu k.val k.2)

/-- The coordinate map on `H²` at the coset `uΔ`, for a subgroup `K` fixing it. -/
def coordH (K : Subgroup G) (u : G) (hu : ∀ k ∈ K, u⁻¹ * k * u ∈ Δ) :
    groupCohomology.H2 (Rep.res K.subtype (Rep.of (permRep ρ Δ))) →ₗ[ℂ] groupCohomology.H2 (Rep.of (ρ.comp K.subtype)) :=
  EdgeNat.h2Map (MonoidHom.id K) (Rep.res K.subtype (Rep.of (permRep ρ Δ))) (Rep.of (ρ.comp K.subtype)) (evAt Δ u)
    (evAt_hT ρ Δ K u hu)

/-- The conjugation `K → Δ`, `k ↦ u⁻¹ k u`. -/
def kappa (K : Subgroup G) (u : G) (hu : ∀ k ∈ K, u⁻¹ * k * u ∈ Δ) : K →* Δ where
  toFun k := ⟨u⁻¹ * k.val * u, hu k.val k.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

theorem kappa_hT (K : Subgroup G) (u : G) (hu : ∀ k ∈ K, u⁻¹ * k * u ∈ Δ) (k : K)
    (v : Rep.of (ρ.comp Δ.subtype)) :
    (ρ u) ((Rep.of (ρ.comp Δ.subtype)).ρ (kappa Δ K u hu k) v) = (Rep.of (ρ.comp K.subtype)).ρ k (ρ u v) := by
  change ρ u (ρ (u⁻¹ * k.val * u) v) = ρ k.val (ρ u v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

/-- Functoriality: pulling back along `κ_u` after pushing forward along the conjugation is restriction to `K ≤ uΔu⁻¹`. -/
theorem kappa_conj (K : Subgroup G) (u : G) (hu : ∀ k ∈ K, u⁻¹ * k * u ∈ Δ)
    (hK : K ≤ Δconj Δ u) (Y : groupCohomology.H2 (Rep.of (ρ.comp (Δconj Δ u).subtype))) :
    EdgeNat.h2Map (kappa Δ K u hu) (Rep.of (ρ.comp Δ.subtype)) (Rep.of (ρ.comp K.subtype)) (ρ u) (kappa_hT ρ Δ K u hu)
        ((groupCohomology.map (conjHom u (isConj_Δconj Δ u)) (conjRep ρ u (isConj_Δconj Δ u)) 2).hom Y) =
      (groupCohomology.map (Subgroup.inclusion hK) (resRep ρ hK) 2).hom Y := by
  obtain ⟨Z, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π (Rep.of (ρ.comp (Δconj Δ u).subtype)))).mp
    inferInstance Y
  rw [groupCohomology.H2π_comp_map_apply, EdgeNat.h2Map_π, groupCohomology.H2π_comp_map_apply]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  change ρ u (ρ u⁻¹ (Z.1 (conjHom u (isConj_Δconj Δ u) (kappa Δ K u hu a), conjHom u (isConj_Δconj Δ u) (kappa Δ K u hu b)))) =
    Z.1 (Subgroup.inclusion hK a, Subgroup.inclusion hK b)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have e : ∀ x : K, conjHom u (isConj_Δconj Δ u) (kappa Δ K u hu x) = Subgroup.inclusion hK x := fun x =>
    Subtype.ext (by change u * (u⁻¹ * x.val * u) * u⁻¹ = x.val; group)
  rw [e a, e b]

/-- **Shapiro–Mackey (Mathlib form).**  Every class `c` of `H²(Δ, E)` is the base coordinate of a class `c_V` of `H²(G, Fun(G/Δ, E))` whose
restriction to any subgroup `K` fixing the coset `uΔ` has `uΔ`-coordinate the pull-back of `c` along `k ↦ u⁻¹ k u` (twisted by `ρ(u)`). -/
theorem exists_ind_class (c : groupCohomology.H2 (Rep.of (ρ.comp Δ.subtype))) :
    ∃ cV : groupCohomology.H2 (Rep.of (permRep ρ Δ)), ∀ (K : Subgroup G) (u : G) (hu : ∀ k ∈ K, u⁻¹ * k * u ∈ Δ),
      coordH ρ Δ K u hu (twoCohomologyRestriction K.subtype (Rep.of (permRep ρ Δ)) cV) =
        EdgeNat.h2Map (kappa Δ K u hu) (Rep.of (ρ.comp Δ.subtype)) (Rep.of (ρ.comp K.subtype)) (ρ u)
          (kappa_hT ρ Δ K u hu) c := by
  obtain ⟨x, rfl⟩ := (bridge ρ Δ).surjective c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hf : IsEq ρ Δ z.val.val := (mem_cochains_iff ρ Δ 2 _).mp z.val.2
  have hz : rd2 z.val.val = 0 := by
    have h := z.property
    change differentialTwo Δ ρ z.val = 0 at h
    rw [differentialTwo_eq] at h
    exact h
  refine ⟨groupCohomology.H2π (Rep.of (permRep ρ Δ)) ⟨indZ ρ Δ z.val.val, indZ_mem ρ Δ hf hz⟩, ?_⟩
  intro K u hu
  have hK : K ≤ Δconj Δ u := fun k hk => hu k hk
  rw [← bridge_conj ρ u (isConj_Δconj Δ u) (Submodule.Quotient.mk z), kappa_conj ρ Δ K u hu hK, bridge_res ρ hK]
  have h0 : actH2Conj ρ u (isConj_Δconj Δ u) (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (actCocycleConj ρ u (isConj_Δconj Δ u) z) := rfl
  rw [h0]
  have h1 : resH2 ρ hK (Submodule.Quotient.mk (actCocycleConj ρ u (isConj_Δconj Δ u) z)) =
      Submodule.Quotient.mk (cocyclesRes ρ hK (actCocycleConj ρ u (isConj_Δconj Δ u) z)) := rfl
  rw [h1, bridge_mk]
  unfold coordH
  rw [twoCohomologyRestriction_apply, EdgeNat.h2Map_π]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  refine Eq.trans ?_ (bridgeCocycle_apply ρ K _ a b).symm
  change evAt Δ u (indL ρ Δ z.val.val ![1, a.val, (a * b).val]) = actFun ρ u z.val.val ![1, a.val, (a * b).val]
  change indFun ρ Δ z.val.val ![1, a.val, (a * b).val] (u : G ⧸ Δ) = _
  rw [indFun_eq ρ Δ (fun γ y => hf γ.1 γ.2 y)]
  rfl

end Mackey

section Injective

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ : Subgroup G)

theorem base_fixed (δ : G) (hδ : δ ∈ Δ) : δ⁻¹ • ((1 : G) : G ⧸ Δ) = ((1 : G) : G ⧸ Δ) := by
  rw [smul_mk_quot, mul_one]
  exact QuotientGroup.eq.mpr (by simpa using hδ)

/-- The base coordinate of a Mathlib class: restriction to `Δ` and evaluation at the base coset. -/
def PhiH : groupCohomology.H2 (Rep.of (permRep ρ Δ)) →ₗ[ℂ] groupCohomology.H2 (Rep.of (ρ.comp Δ.subtype)) :=
  (coordH ρ Δ Δ 1 (fun k hk => by simpa using hk)).comp
    (twoCohomologyRestriction Δ.subtype (Rep.of (permRep ρ Δ)))

variable {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V)

/-- The homogeneous cochain of a Mathlib 2-cocycle: `(g₀, g₁, g₂) ↦ σ(g₀) Z(g₀⁻¹ g₁, g₁⁻¹ g₂)`. -/
def homOf (Z : G × G → V) : FunSpace G V 2 := fun g => σ (g 0) (Z ((g 0)⁻¹ * g 1, (g 1)⁻¹ * g 2))

theorem homOf_equivariant (Z : G × G → V) (s : G) (g : Fin 3 → G) :
    homOf σ Z (fun i => s * g i) = σ s (homOf σ Z g) := by
  unfold homOf
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  simp [mul_assoc]

theorem homOf_rd2 {Z : G × G → V} (hZ : Z ∈ groupCohomology.cocycles₂ (Rep.of σ)) : rd2 (homOf σ Z) = 0 := by
  funext x
  rw [groupCohomology.mem_cocycles₂_iff] at hZ
  obtain ⟨g, hg⟩ : ∃ g, x 1 = x 0 * g := ⟨(x 0)⁻¹ * x 1, by group⟩
  obtain ⟨h, hh⟩ : ∃ h, x 2 = x 0 * g * h := ⟨g⁻¹ * (x 0)⁻¹ * x 2, by group⟩
  obtain ⟨j, hj⟩ : ∃ j, x 3 = x 0 * g * h * j := ⟨h⁻¹ * g⁻¹ * (x 0)⁻¹ * x 3, by group⟩
  have key := hZ g h j
  have key2 := congrArg (σ (x 0)) key
  simp only [map_add] at key2
  have e1 : (x 0)⁻¹ * (x 0 * g) = g := by group
  have e2 : (x 0 * g)⁻¹ * (x 0 * g * h) = h := by group
  have e3 : (x 0 * g * h)⁻¹ * (x 0 * g * h * j) = j := by group
  have e4 : (x 0)⁻¹ * (x 0 * g * h) = g * h := by group
  have e5 : (x 0 * g)⁻¹ * (x 0 * g * h * j) = h * j := by group
  have e6 : (x 0 * g * h)⁻¹ * (x 0 * g * h * j) = j := by group
  have e7 : (x 0)⁻¹ * (x 0 * g * h * j) = g * h * j := by group
  simp only [rd2, LinearMap.coe_mk, AddHom.coe_mk, homOf, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Pi.zero_apply, hg, hh, hj, e1, e2, e3, e4, e5, map_mul,
    Module.End.mul_apply] at key2 ⊢
  linear_combination (norm := module) -key2

theorem evL_isEq {k : ℕ} {F : FunSpace G ((G ⧸ Δ) → E) k} (hF : IsEq (permRep ρ Δ) ⊤ F) : IsEq ρ Δ (evL Δ F) := by
  intro δ hδ y
  change F (fun i => δ * y i) ((1 : G) : G ⧸ Δ) = ρ δ (F y ((1 : G) : G ⧸ Δ))
  rw [hF δ (Subgroup.mem_top _) y, permRep_apply, base_fixed Δ δ hδ]

theorem evL_rd2 (F : FunSpace G ((G ⧸ Δ) → E) 2) : evL Δ (rd2 F) = rd2 (evL Δ F) := by
  funext g
  rfl

/-- **Shapiro by evaluation is injective** (and, by `exists_ind_class`, surjective): `H²(G, Fun(G/Δ, E)) ≅ H²(Δ, E)`. -/
theorem PhiH_injective : Function.Injective (PhiH ρ Δ) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨Z, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π (Rep.of (permRep ρ Δ)))).mp inferInstance y
  have hZ := Z.2
  set F : FunSpace G ((G ⧸ Δ) → E) 2 := homOf (permRep ρ Δ) Z.1 with hFdef
  have hFeq : IsEq (permRep ρ Δ) ⊤ F := fun γ _ x => homOf_equivariant (permRep ρ Δ) Z.1 γ x
  have hFrd : rd2 F = 0 := homOf_rd2 (permRep ρ Δ) hZ
  have hfeq : IsEq ρ Δ (evL Δ F) := evL_isEq ρ Δ hFeq
  have hfrd : rd2 (evL Δ F) = 0 := by rw [← evL_rd2, hFrd]; rfl
  let zf : cocycles Δ ρ := ⟨⟨evL Δ F, (mem_cochains_iff ρ Δ 2 _).mpr hfeq⟩, by
    change differentialTwo Δ ρ _ = 0
    rw [differentialTwo_eq]; exact hfrd⟩
  have hbr : bridge ρ Δ (Submodule.Quotient.mk zf) = 0 := by
    rw [bridge_mk]
    have hy' : PhiH ρ Δ (groupCohomology.H2π (Rep.of (permRep ρ Δ)) Z) = 0 := hy
    unfold PhiH coordH at hy'
    rw [LinearMap.comp_apply, twoCohomologyRestriction_apply, EdgeNat.h2Map_π] at hy'
    rw [← hy']
    congr 1
    apply Subtype.ext
    funext p
    obtain ⟨a, b⟩ := p
    refine Eq.trans (bridgeCocycle_apply ρ Δ zf a b) ?_
    change evL Δ F ![1, a.val, (a * b).val] = _
    change F ![1, a.val, (a * b).val] ((1 : G) : G ⧸ Δ) = _
    have : F ![1, a.val, (a * b).val] = Z.1 (a.val, b.val) := by
      change (permRep ρ Δ) 1 (Z.1 ((1 : G)⁻¹ * a.val, (a.val)⁻¹ * (a * b).val)) = _
      simp
    rw [this]
    rfl
  have h0 : Submodule.Quotient.mk zf = (0 : H2 Δ ρ) := (bridge ρ Δ).injective (by rw [hbr, map_zero])
  rw [Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨c1, hc1⟩ := h0
  have hc1' : rd1 c1.val = evL Δ F := by
    have := congrArg (fun t : cocycles Δ ρ => t.val.val) hc1
    exact this
  have hFind : F = indL ρ Δ (evL Δ F) := (indL_evL ρ Δ hFeq).symm
  have hH : IsEq (permRep ρ Δ) ⊤ (indL ρ Δ c1.val) := isEq_indL ρ Δ ((mem_cochains_iff ρ Δ 1 _).mp c1.2) ⊤
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun a => indL ρ Δ c1.val ![1, a], ?_⟩
  funext p
  obtain ⟨a, b⟩ := p
  rw [groupCohomology.d₁₂_hom_apply]
  have e1 : F ![1, a, a * b] = indL ρ Δ (rd1 c1.val) ![1, a, a * b] := by rw [hc1', ← hFind]
  have e2 : F ![1, a, a * b] = Z.1 (a, b) := by
    change (permRep ρ Δ) 1 (Z.1 ((1 : G)⁻¹ * a, a⁻¹ * (a * b))) = _
    simp
  rw [indL_rd1] at e1
  have e3 : indL ρ Δ c1.val ![a, a * b] = (permRep ρ Δ) a (indL ρ Δ c1.val ![1, b]) := by
    have := hH a (Subgroup.mem_top _) ![1, b]
    have et : (fun i => a * (![1, b] : Fin 2 → G) i) = ![a, a * b] := by
      funext i; fin_cases i <;> simp
    rw [et] at this
    exact this
  simp only [rd1, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val] at e1
  change ((permRep ρ Δ) a) (indL ρ Δ c1.val ![1, b]) - indL ρ Δ c1.val ![1, a * b] + indL ρ Δ c1.val ![1, a] = Z.1 (a, b)
  rw [← e3, ← e2, e1]

theorem h2Map_kappa_one (c : groupCohomology.H2 (Rep.of (ρ.comp Δ.subtype))) :
    EdgeNat.h2Map (kappa Δ Δ 1 (fun k hk => by simpa using hk)) (Rep.of (ρ.comp Δ.subtype)) (Rep.of (ρ.comp Δ.subtype))
      (ρ 1) (kappa_hT ρ Δ Δ 1 (fun k hk => by simpa using hk)) c = c := by
  obtain ⟨Z, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π (Rep.of (ρ.comp Δ.subtype)))).mp
    inferInstance c
  rw [EdgeNat.h2Map_π]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  change ρ 1 (Z.1 (kappa Δ Δ 1 _ a, kappa Δ Δ 1 _ b)) = Z.1 (a, b)
  have e : ∀ x : Δ, kappa Δ Δ 1 (fun k hk => by simpa using hk) x = x := fun x => Subtype.ext (by
    change (1 : G)⁻¹ * x.val * 1 = x.val; simp)
  rw [e a, e b, map_one]
  rfl

/-- **Shapiro by evaluation is bijective**: `H²(G, Fun(G/Δ, E)) ≅ H²(Δ, E)` (Mathlib group cohomology). -/
theorem PhiH_bijective : Function.Bijective (PhiH ρ Δ) := by
  refine ⟨PhiH_injective ρ Δ, fun c => ?_⟩
  obtain ⟨cV, hcV⟩ := exists_ind_class ρ Δ c
  refine ⟨cV, ?_⟩
  have := hcV Δ 1 (fun k hk => by simpa using hk)
  exact this.trans (h2Map_kappa_one ρ Δ c)

end Injective

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
