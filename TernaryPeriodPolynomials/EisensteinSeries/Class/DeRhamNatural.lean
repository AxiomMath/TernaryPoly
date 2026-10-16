module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagMain
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section


/-!
# Naturality of the de Rham class of the zig-zag (obligation OB4)

Paper: Appendix C,
(the class of `ℰ_P(ω_h)` in `H²(Γ, E)`, and its restriction to the boundary model `e(R)` along
`i_{R,t}`, which "realizes the group restriction").

`SeedC3.ZigZag.deRhamClass` sends a closed equivariant `F`-valued 2-form on a convex open set to
`H²(G, F)`. This file proves that it is natural: if `φ : s → t` is a smooth map of open sets which
is equivariant along a group homomorphism `α : G → G'` (`φ ∘ g = α(g) ∘ φ`), and the coefficient
representations are related by `ρ g = ρ' (α g)`, then the pullback `φ^* ω` is a closed `ρ`-equivariant
form and

  `deRhamClass (φ^* ω) = H²(α) (deRhamClass ω)`

(`deRhamClass_natural`), where `H²(α)` is `groupCohomology.map α` along the identity of the
coefficient module. Special cases are the restriction to a subgroup (`α` an inclusion; the
equivariant map `i_{R,t}` of the boundary model) and the change of coordinates (`α = id`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothSingularComparison
open scoped ContDiff Topology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set D} {t : Set E} {G G' : Type} [Group G] [Group G']

/-! ### Two small calculus lemmas -/

theorem pullRaw_congr_at' {n : ℕ} (f : D → E) {W₁ W₂ : RawForm E F n} {x : D}
    (h : W₁ (f x) = W₂ (f x)) : pullRaw f W₁ x = pullRaw f W₂ x := by
  simp [pullRaw, h]

theorem diffAt_of_contDiffOn (hs : IsOpen s) {φ : D → E} (hφ : ContDiffOn ℝ ∞ φ s) {x : D}
    (hx : x ∈ s) : DifferentiableAt ℝ φ x :=
  ((hφ x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)

section Pullback

variable [FiniteDimensional ℝ D]

/-! ### The pullback of chart forms along a smooth map `D → E` -/

/-- The pullback of chart forms on `t ⊂ E` along a smooth map `φ : D → E` mapping `s ⊂ D` into `t`. -/
def pullBack (hs : IsOpen s) {φ : D → E} (hφ : ContDiffOn ℝ ∞ φ s) (hmaps : Set.MapsTo φ s t)
    (n : ℕ) : Form (F := F) t n →ₗ[ℝ] Form (F := F) s n where
  toFun w := restrictForm (F := F) s (pullRaw φ (w : RawForm E F n))
    (pullRaw_smooth hs hφ (Form.smooth w) hmaps)
  map_add' w η := by
    apply Form.ext
    intro x hx
    simp only [AddMemClass.coe_add, Pi.add_apply, restrictForm_apply (F := F) _ _ hx]
    ext v
    simp [pullRaw]
  map_smul' c w := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply (F := F) _ _ hx, SetLike.val_smul, RingHom.id_apply,
      Pi.smul_apply]
    ext v
    simp [pullRaw]

theorem pullBack_apply (hs : IsOpen s) {φ : D → E} (hφ : ContDiffOn ℝ ∞ φ s)
    (hmaps : Set.MapsTo φ s t) {n : ℕ} (w : Form (F := F) t n) {x : D} (hx : x ∈ s) :
    (pullBack hs hφ hmaps n w : RawForm D F n) x = pullRaw φ (w : RawForm E F n) x :=
  restrictForm_apply (pullRaw φ (w : RawForm E F n))
    (pullRaw_smooth hs hφ (Form.smooth w) hmaps) hx

/-- The pullback commutes with the exterior derivative. -/
theorem d_pullBack (hs : IsOpen s) (ht : IsOpen t) {φ : D → E} (hφ : ContDiffOn ℝ ∞ φ s)
    (hmaps : Set.MapsTo φ s t) {n : ℕ} (w : Form (F := F) t n) :
    d hs n (pullBack hs hφ hmaps n w) = pullBack hs hφ hmaps (n + 1) (d ht n w) := by
  apply Form.ext
  intro x hx
  rw [d_apply hs _ hx, pullBack_apply hs hφ hmaps _ hx]
  have heq : (pullBack hs hφ hmaps n w : RawForm D F n) =ᶠ[𝓝 x]
      pullRaw φ (w : RawForm E F n) := by
    filter_upwards [hs.mem_nhds hx] with y hy using pullBack_apply hs hφ hmaps w hy
  rw [heq.extDeriv_eq]
  have hfx : φ x ∈ t := hmaps hx
  rw [extDeriv_pullRaw ((hφ x hx).contDiffAt (hs.mem_nhds hx))
    ((((Form.smooth w) _ hfx).contDiffAt (ht.mem_nhds hfx)).differentiableAt (by simp))]
  apply pullRaw_congr_at'
  rw [d_apply ht w hfx]

/-- The pullback commutes with the coefficient twist. -/
theorem pullBack_twForm (hs : IsOpen s) {φ : D → E} (hφ : ContDiffOn ℝ ∞ φ s)
    (hmaps : Set.MapsTo φ s t) (L : F →L[ℝ] F) {n : ℕ} (w : Form (F := F) t n) :
    pullBack hs hφ hmaps n (twForm L n w) = twForm L n (pullBack hs hφ hmaps n w) := by
  apply Form.ext
  intro x hx
  rw [pullBack_apply hs hφ hmaps _ hx, twForm_apply, pullBack_apply hs hφ hmaps _ hx]
  exact congrFun (coefficientRaw_pullRaw L φ (w : RawForm E F n)) x

/-- The pullback of a constant is the constant. -/
theorem pullBack_constant (hs : IsOpen s) {φ : D → E} (hφ : ContDiffOn ℝ ∞ φ s)
    (hmaps : Set.MapsTo φ s t) (c : F) :
    pullBack hs hφ hmaps 0 (constant t c) = constant s c := by
  apply Form.ext
  intro x hx
  have hfx : φ x ∈ t := hmaps hx
  have hW : (constant t c : RawForm E F 0) (φ x) = zeroEquiv c := ofFunction_apply _ _ hfx
  rw [pullBack_apply hs hφ hmaps _ hx]
  have hx' : (constant s c : RawForm D F 0) x = zeroEquiv c := ofFunction_apply _ _ hx
  rw [hx']
  ext v
  simp only [pullRaw, ContinuousAlternatingMap.compContinuousLinearMap_apply, hW]
  simp [zeroEquiv]

variable [FiniteDimensional ℝ E]

/-- **Equivariance of the pullback**: pulling back along `φ` intertwines the actions of `g` and
`α g` when `φ ∘ g = α g ∘ φ` on `s`. -/
theorem pullBack_pullForm (hs : IsOpen s) (ht : IsOpen t) (A : Action G s) (B : Action G' t)
    (α : G →* G') {φ : D → E} (hφ : ContDiffOn ℝ ∞ φ s) (hmaps : Set.MapsTo φ s t)
    (hequiv : ∀ g, ∀ x ∈ s, φ (A.act g x) = B.act (α g) (φ x)) (g : G) {n : ℕ}
    (w : Form (F := F) t n) :
    pullBack hs hφ hmaps n (pullForm ht B (α g) n w) =
      pullForm hs A g n (pullBack hs hφ hmaps n w) := by
  apply Form.ext
  intro x hx
  have hfx : φ x ∈ t := hmaps hx
  have hax : A.act g x ∈ s := A.mapsTo g hx
  rw [pullBack_apply hs hφ hmaps _ hx, pullForm_apply hs A g _ hx]
  rw [pullRaw_congr_at' φ (W₂ := pullRaw (B.act (α g)) (w : RawForm E F n))
    (pullForm_apply ht B (α g) w hfx)]
  rw [pullRaw_congr_at' (A.act g) (W₂ := pullRaw φ (w : RawForm E F n))
    (pullBack_apply hs hφ hmaps w hax)]
  rw [pullRaw_comp _ (diffAt_act B ht (α g) hfx) (diffAt_of_contDiffOn hs hφ hx),
    pullRaw_comp _ (diffAt_of_contDiffOn hs hφ hax) (diffAt_act A hs g hx)]
  apply pullRaw_eventuallyEq
  filter_upwards [hs.mem_nhds hx] with y hy
  exact (hequiv g y hy).symm

end Pullback

/-! ### Equivariant maps and the pullback of invariant closed forms -/

section Natural

variable [FiniteDimensional ℝ D] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompleteSpace F]

/-- A smooth map `φ : s → t` which is equivariant along `α : G → G'`: `φ (g x) = α(g) (φ x)`. -/
structure EquivMap (hs : IsOpen s) (ht : IsOpen t) (A : Action G s) (B : Action G' t)
    (α : G →* G') where
  /-- The underlying map of ambient spaces. -/
  φ : D → E
  smooth : ContDiffOn ℝ ∞ φ s
  mapsTo : Set.MapsTo φ s t
  equiv : ∀ g, ∀ x ∈ s, φ (A.act g x) = B.act (α g) (φ x)

variable {hs : IsOpen s} {ht : IsOpen t} {A : Action G s} {B : Action G' t} {α : G →* G'}

omit [CompleteSpace F] in
theorem repCLM_eq_of_hom {ρ : Representation ℝ G F} {ρ' : Representation ℝ G' F}
    (hρ : ∀ g, ρ g = ρ' (α g)) (g : G) : repCLM ρ g = repCLM ρ' (α g) := by
  ext v
  simp [repCLM, hρ g]

/-- **The pullback of an invariant closed form** along an equivariant map is an invariant closed
form for the pulled-back coefficient representation. -/
def pullInv (Φ : EquivMap hs ht A B α) {ρ : Representation ℝ G F} {ρ' : Representation ℝ G' F}
    (hρ : ∀ g, ρ g = ρ' (α g)) (om : invClosed ht B ρ') : invClosed hs A ρ :=
  ⟨pullBack hs Φ.smooth Φ.mapsTo 2 om.1, by
    rw [d_pullBack hs ht Φ.smooth Φ.mapsTo, om.2.1, map_zero], fun g => by
    rw [← pullBack_pullForm hs ht A B α Φ.smooth Φ.mapsTo Φ.equiv, om.2.2 (α g),
      pullBack_twForm hs Φ.smooth Φ.mapsTo, repCLM_eq_of_hom hρ g]⟩

/-- The pullback of a zig-zag datum of `om` is a zig-zag datum of `φ^* om`. -/
def pullDatum (Φ : EquivMap hs ht A B α) {ρ : Representation ℝ G F} {ρ' : Representation ℝ G' F}
    (hρ : ∀ g, ρ g = ρ' (α g)) (om : invClosed ht B ρ')
    (Dt : Datum (d ht 0) (d ht 1) (fun g => pullForm ht B g 1)
      (fun g => twForm (repCLM ρ' g) 1) (om : Form (F := F) t 2)) :
    Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1) (fun g => twForm (repCLM ρ g) 1)
      (pullInv Φ hρ om : Form (F := F) s 2) where
  η := pullBack hs Φ.smooth Φ.mapsTo 1 Dt.η
  θ g := pullBack hs Φ.smooth Φ.mapsTo 0 (Dt.θ (α g))
  dη := by
    change d hs 1 _ = pullBack hs Φ.smooth Φ.mapsTo 2 om.1
    rw [d_pullBack hs ht Φ.smooth Φ.mapsTo, Dt.dη]
  dθ g := by
    rw [d_pullBack hs ht Φ.smooth Φ.mapsTo, Dt.dθ (α g), map_sub,
      pullBack_pullForm hs ht A B α Φ.smooth Φ.mapsTo Φ.equiv,
      pullBack_twForm hs Φ.smooth Φ.mapsTo, repCLM_eq_of_hom hρ g]

/-- The identity of the coefficient module as a morphism `Res_α ρ' ⟶ ρ` of representations. -/
def resMor (α : G →* G') (ρ : Representation ℝ G F) (ρ' : Representation ℝ G' F)
    (hρ : ∀ g, ρ g = ρ' (α g)) : Rep.res α (Rep.of ρ') ⟶ Rep.of ρ :=
  Rep.ofHom ⟨LinearMap.id, fun g => by
    ext v
    simp [hρ g]⟩

/-- The zig-zag cochain of the pulled-back datum is the pullback of the cochain along `α`. -/
theorem cochain_pullDatum (Φ : EquivMap hs ht A B α) (hc : Convex ℝ s) (hne : s.Nonempty)
    (hc' : Convex ℝ t) (hne' : t.Nonempty)
    {ρ : Representation ℝ G F} {ρ' : Representation ℝ G' F} (hρ : ∀ g, ρ g = ρ' (α g))
    (om : invClosed ht B ρ')
    (Dt : Datum (d ht 0) (d ht 1) (fun g => pullForm ht B g 1)
      (fun g => twForm (repCLM ρ' g) 1) (om : Form (F := F) t 2)) (g h : G) :
    cochain (laws hs hc hne A ρ) (pullDatum Φ hρ om Dt) g h =
      cochain (laws ht hc' hne' B ρ') Dt (α g) (α h) := by
  apply (laws hs hc hne A ρ).c_injective
  rw [c_cochain (laws hs hc hne A ρ) (pullDatum Φ hρ om Dt) g h]
  have e := c_cochain (laws ht hc' hne' B ρ') Dt (α g) (α h)
  have hX : deRhamConstant s (cochain (laws ht hc' hne' B ρ') Dt (α g) (α h)) =
      pullBack hs Φ.smooth Φ.mapsTo 0
        (deRhamConstant t (cochain (laws ht hc' hne' B ρ') Dt (α g) (α h))) :=
    (pullBack_constant hs Φ.smooth Φ.mapsTo _).symm
  rw [hX, e, map_sub, map_add]
  show pullForm hs A h 0 (pullBack hs Φ.smooth Φ.mapsTo 0 (Dt.θ (α g))) +
      twForm (repCLM ρ g) 0 (pullBack hs Φ.smooth Φ.mapsTo 0 (Dt.θ (α h))) -
      pullBack hs Φ.smooth Φ.mapsTo 0 (Dt.θ (α (g * h))) = _
  rw [← pullBack_pullForm hs ht A B α Φ.smooth Φ.mapsTo Φ.equiv,
    ← pullBack_twForm hs Φ.smooth Φ.mapsTo, repCLM_eq_of_hom hρ g, map_mul]

/-- **Naturality of the de Rham class** (OB4). For a smooth map `φ : s → t` equivariant along
`α : G → G'`, and coefficient representations with `ρ g = ρ' (α g)`, the class of the pullback
`φ^* ω ∈ invClosed hs A ρ` is the image of the class of `ω` under `H²(α) = groupCohomology.map α`. -/
theorem deRhamClass_natural (Φ : EquivMap hs ht A B α) (hc : Convex ℝ s) (hne : s.Nonempty)
    (hc' : Convex ℝ t) (hne' : t.Nonempty)
    {ρ : Representation ℝ G F} {ρ' : Representation ℝ G' F} (hρ : ∀ g, ρ g = ρ' (α g))
    (om : invClosed ht B ρ') :
    deRhamClass hs hc hne A ρ (pullInv Φ hρ om) =
      (groupCohomology.map α (resMor α ρ ρ' hρ) 2).hom (deRhamClass ht hc' hne' B ρ' om) := by
  obtain ⟨Dt⟩ := exists_datum_deRham ht hc' hne' B ρ' om
  rw [deRhamClass_eq hs hc hne A ρ _ (pullDatum Φ hρ om Dt),
    deRhamClass_eq ht hc' hne' B ρ' om Dt]
  unfold zigzagClass
  rw [groupCohomology.H2π_comp_map_apply α (resMor α ρ ρ' hρ)]
  congr 1
  apply Subtype.ext
  funext p
  change cochain (laws hs hc hne A ρ) (pullDatum Φ hρ om Dt) p.1 p.2 = _
  rw [cochain_pullDatum Φ hc hne hc' hne' hρ om Dt]
  rfl

end Natural

end TernaryPeriodPolynomials.Argument.EisensteinClass
