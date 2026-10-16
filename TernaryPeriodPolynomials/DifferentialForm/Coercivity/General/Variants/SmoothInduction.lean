module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Singular.DeckLink
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.CoveringSingular

@[expose] public section


/-!
# Smooth Shapiro lemma and descent to finite-index subgroups of the cover

For a finite-index admissible subgroup `H` of the cover `gamma0 = Γ(6)` and a real
representation `T` of `GL₃(ℝ)`, the induced representation `indReal T hle` of the deck group on
`FDeck/H → F` (`(g w)(q) = T(g) w(g⁻¹ q)`) is smoothly exact in degree one
(`compactExact_induced`) as soon as `T` has the *primitive property* over `H` (every closed smooth
`H`-equivariant two-form of compact projected support has a smooth `H`-equivariant primitive).  The
primitive property of the five coefficient systems over every admissible `H` is the Tier B theorem
(`primitive_real`, `primitive_dual`, `primitive_complex`, `primitive_complex_dual`, `primitive_lit`).

The primitive of the induced form is assembled from the `r`-translates `r ⋆ η'` of a primitive `η'` of
its base component, where `g ⋆ ω = T(g) · (g⁻¹)^* ω` (`star`).  Together with the rational Shapiro
lemma of `Singular/DeckLink` this gives `singularVanish_of_primitive`: the actual singular
compact-to-ordinary map of `H` with coefficients `V|_H` vanishes in degree two, for every rational deck
system `V` whose real scalar extension is equivariantly isomorphic to `T`.

Formalized by Claude Sonnet 5.5.
-/

open TopologicalSpace CategoryTheory

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
open scoped ContDiff

section InducedRep

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (T : Representation ℝ RealGL F) {H : Subgroup RealGL} (hle : H ≤ gamma0)

/-- The finite set of cosets of `H` in the deck group. -/
abbrev QD : Type := FDeck ⧸ (toDeck hle).range

/-- The induced real representation of the deck group on `(FDeck/H → F)`:
`(g w)(q) = T(g) w(g⁻¹ q)`. -/
def indReal : Representation ℝ FDeck (QD hle → F) where
  toFun g :=
    { toFun := fun w q => T (deckMat g) (w (g⁻¹ • q))
      map_add' := fun w w' => by funext q; simp
      map_smul' := fun c w => by funext q; simp }
  map_one' := by
    apply LinearMap.ext
    intro w
    funext q
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    funext q
    change T (deckMat (g * h)) (w ((g * h)⁻¹ • q)) =
      T (deckMat g) (T (deckMat h) (w (h⁻¹ • g⁻¹ • q)))
    rw [mul_inv_rev, mul_smul, map_mul deckMat, map_mul T, Module.End.mul_apply]

theorem indReal_apply (g : FDeck) (w : QD hle → F) (q : QD hle) :
    indReal T hle g w q = T (deckMat g) (w (g⁻¹ • q)) := rfl

/-- The coordinate projection `W → F`. -/
def projL (q : QD hle) : (QD hle → F) →L[ℝ] F := ContinuousLinearMap.proj q

/-- The inclusion `F → W` at a coordinate. -/
def injL [DecidableEq (QD hle)] (q : QD hle) : F →L[ℝ] (QD hle → F) :=
  ContinuousLinearMap.single ℝ (fun _ : QD hle => F) q

theorem projL_injL_self [DecidableEq (QD hle)] (q : QD hle) (v : F) :
    projL hle q (injL hle q v) = v := by
  simp [projL, injL]

theorem projL_injL_ne [DecidableEq (QD hle)] {q q' : QD hle} (h : q ≠ q') (v : F) : projL hle q (injL hle q' v) = 0 := by
  simp [projL, injL, h.symm]

theorem sum_injL_projL [Fintype (QD hle)] [DecidableEq (QD hle)] (w : QD hle → F) : ∑ q, injL hle q (projL hle q w) = w := by
  funext q'
  simp [projL, injL, Finset.sum_apply]

theorem projL_indReal (g : FDeck) (q : QD hle) (w : QD hle → F) :
    projL hle q (indReal T hle g w) = T (deckMat g) (projL hle (g⁻¹ • q) w) := rfl

end InducedRep


section Star

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (T : Representation ℝ RealGL F)

/-- Raw `k`-forms on the positive coordinates with values in `F`. -/
abbrev RawFm (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) : Type :=
  Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F

/-- The twisted pullback `g ⋆ om = T(g) · (g⁻¹)^* om`, the action of `GL₃(ℝ)` on form-valued sections
corresponding to `f ↦ g · f(g⁻¹ ·)`. -/
def star (g : RealGL) {k : ℕ} (om : RawFm F k) : RawFm F k :=
  coefficientRaw (T g).toContinuousLinearMap (pullRaw (coordinateAction g⁻¹) om)

theorem star_apply (g : RealGL) {k : ℕ} (om : RawFm F k) (x : Coordinates) :
    star T g om x = coefficientFormMap (T g).toContinuousLinearMap k
      (pullRaw (coordinateAction g⁻¹) om x) := rfl

theorem coordinateAction_comp_eventuallyEq (g h : RealGL) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    (coordinateAction g ∘ coordinateAction h) =ᶠ[nhds x] coordinateAction (g * h) := by
  filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
  exact (coordinateAction_mul g h hy).symm

theorem star_mul (g h : RealGL) {k : ℕ} (om : RawFm F k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    star T g (star T h om) x = star T (g * h) om x := by
  have h1 : pullRaw (coordinateAction g⁻¹) (coefficientRaw (T h).toContinuousLinearMap
      (pullRaw (coordinateAction h⁻¹) om)) x =
      coefficientFormMap (T h).toContinuousLinearMap k
        (pullRaw (coordinateAction (h⁻¹ * g⁻¹)) om x) := by
    rw [← coefficientRaw_pullRaw]
    change coefficientFormMap (T h).toContinuousLinearMap k
      (pullRaw (coordinateAction g⁻¹) (pullRaw (coordinateAction h⁻¹) om) x) = _
    rw [pullRaw_comp om (differentiableAt_coordinateAction h⁻¹
        (coordinateAction_mem g⁻¹ x hx)) (differentiableAt_coordinateAction g⁻¹ hx),
      pullRaw_eventuallyEq om (coordinateAction_comp_eventuallyEq h⁻¹ g⁻¹ hx)]
  unfold star
  change coefficientFormMap (T g).toContinuousLinearMap k (pullRaw (coordinateAction g⁻¹)
    (coefficientRaw (T h).toContinuousLinearMap (pullRaw (coordinateAction h⁻¹) om)) x) =
    coefficientFormMap (T (g * h)).toContinuousLinearMap k (pullRaw (coordinateAction (g * h)⁻¹) om x)
  rw [h1, cFM_comp, mul_inv_rev, map_mul]
  rfl


theorem star_one {k : ℕ} (om : RawFm F k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    star T 1 om x = om x := by
  have h1 : pullRaw (coordinateAction (1 : RealGL)⁻¹) om x = om x := by
    rw [inv_one]
    have : coordinateAction (1 : RealGL) =ᶠ[nhds x] id := by
      filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
      exact coordinateAction_one hy
    rw [pullRaw_eventuallyEq om this, pullRaw_id]
  rw [star_apply, h1, map_one]
  exact cFM_id k _

theorem star_of_equivariant {Γ : Subgroup RealGL} {k : ℕ} (om : RawFm F k)
    (hom : ∀ γ : Γ, ∀ x ∈ positiveCoordinates,
      pullRaw (coordinateAction (γ : RealGL)) om x =
        coefficientFormMap (T (γ : RealGL)).toContinuousLinearMap k (om x))
    (γ : Γ) {x : Coordinates} (hx : x ∈ positiveCoordinates) : star T (γ : RealGL) om x = om x := by
  rw [star_apply]
  have := hom γ⁻¹ x hx
  rw [Subgroup.coe_inv] at this
  rw [this, cFM_comp]
  have e : (T (γ : RealGL)).toContinuousLinearMap.comp (T (γ : RealGL)⁻¹).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ F := by
    apply ContinuousLinearMap.ext
    intro v
    change T (γ : RealGL) (T (γ : RealGL)⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [e, cFM_id]

theorem star_smooth (g : RealGL) {k : ℕ} {om : RawFm F k} (hom : ContDiffOn ℝ ∞ om positiveCoordinates) :
    ContDiffOn ℝ ∞ (star T g om) positiveCoordinates :=
  coefficientRaw_smooth _ (pullRaw_smooth isOpen_positiveCoordinates (contDiffOn_coordinateAction g⁻¹)
    hom (fun x hx => coordinateAction_mem g⁻¹ x hx))

theorem star_extDeriv (g : RealGL) {k : ℕ} {om : RawFm F k} (hom : ContDiffOn ℝ ∞ om positiveCoordinates)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    extDeriv (star T g om) x = star T g (extDeriv om) x := by
  have hd : DifferentiableAt ℝ (pullRaw (coordinateAction g⁻¹) om) x :=
    (((pullRaw_smooth isOpen_positiveCoordinates (contDiffOn_coordinateAction g⁻¹) hom
      (fun x hx => coordinateAction_mem g⁻¹ x hx)) x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have hw : DifferentiableAt ℝ om (coordinateAction g⁻¹ x) :=
    ((hom _ (coordinateAction_mem g⁻¹ x hx)).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds (coordinateAction_mem g⁻¹ x hx))).differentiableAt
      (by simp)
  have hcd : ContDiffAt ℝ ∞ (coordinateAction g⁻¹) x :=
    (contDiffOn_coordinateAction g⁻¹ x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)
  unfold star
  rw [extDeriv_coefficientRaw _ hd, extDeriv_pullRaw hcd hw]
  rfl

end Star


section Assemble

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (T : Representation ℝ RealGL F) {H : Subgroup RealGL} (hle : H ≤ gamma0)

theorem star_congr_on (g : RealGL) {k : ℕ} {om om' : RawFm F k}
    (h : ∀ y ∈ positiveCoordinates, om y = om' y) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    star T g om x = star T g om' x := by
  rw [star_apply, star_apply]
  unfold pullRaw
  rw [h _ (coordinateAction_mem g⁻¹ x hx)]

theorem deckMat_toDeck (h : H) : deckMat (toDeck hle h) = (h : RealGL) := by
  have : toGamma (toDeck hle h) = Subgroup.inclusion hle h := by
    change deckEquiv (deckEquiv.symm (Subgroup.inclusion hle h)) = _
    exact deckEquiv.apply_symm_apply _
  exact congrArg Subtype.val this

open Classical in
/-- The induced family of forms: the `q`-component is `r ⋆ η'` for a representative `r` of `q`. -/
def psiQ (η' : RawFm F 1) (q : QD hle) : RawFm F 1 := fun x =>
  if x ∈ positiveCoordinates then star T (deckMat (Quotient.out q)) η' x else 0

variable {T}

theorem psiQ_eq {η' : RawFm F 1}
    (hη' : ∀ h : H, ∀ x ∈ positiveCoordinates,
      pullRaw (coordinateAction (h : RealGL)) η' x =
        coefficientFormMap (T (h : RealGL)).toContinuousLinearMap 1 (η' x))
    (r : FDeck) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    psiQ T hle η' (QuotientGroup.mk r : QD hle) x = star T (deckMat r) η' x := by
  unfold psiQ
  rw [ite_eq_left hx]
  have hq : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk r : QD hle)) : QD hle) =
      QuotientGroup.mk r := Quotient.out_eq' _
  obtain ⟨h, hh⟩ := QuotientGroup.eq.mp hq
  have hout : Quotient.out (QuotientGroup.mk r : QD hle) = r * (toDeck hle h)⁻¹ := by
    rw [hh]; group
  have hm : deckMat (r * (toDeck hle h)⁻¹) = deckMat r * ((h⁻¹ : H) : RealGL) := by
    rw [map_mul, ← map_inv, deckMat_toDeck hle (h⁻¹)]
  rw [hout, hm, ← star_mul T _ _ η' hx]
  exact star_congr_on T _ (fun y hy => star_of_equivariant T η' hη' h⁻¹ hy) hx


omit [FiniteDimensional ℝ F] in
theorem pullRaw_congr_on {D E' : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {k : ℕ} (f : D → E') (w w' : E' → E' [⋀^Fin k]→L[ℝ] F)
    {x : D} (h : w (f x) = w' (f x)) : pullRaw f w x = pullRaw f w' x := by
  unfold pullRaw
  rw [h]

section PiForm

variable [Fintype (QD hle)]

open Classical in
/-- The `W`-valued form assembled from the induced family. -/
def etaW (η' : RawFm F 1) : RawFm (QD hle → F) 1 := fun x =>
  ∑ q, coefficientFormMap (injL hle q) 1 (psiQ T hle η' q x)

omit [FiniteDimensional ℝ F] in
/-- Two `(FDeck/H → F)`-valued alternating maps agree iff all their coordinates do. -/
theorem ext_projL {k : ℕ} {A B : Coordinates [⋀^Fin k]→L[ℝ] (QD hle → F)}
    (h : ∀ q, coefficientFormMap (projL hle q) k A = coefficientFormMap (projL hle q) k B) :
    A = B := by
  apply ContinuousAlternatingMap.ext
  intro v
  funext q
  exact congrArg (fun u : Coordinates [⋀^Fin k]→L[ℝ] F => u v) (h q)

open Classical in
theorem cFM_projL_etaW (η' : RawFm F 1) (q : QD hle) (x : Coordinates) :
    coefficientFormMap (projL hle q) 1 (etaW (T := T) hle η' x) = psiQ T hle η' q x := by
  unfold etaW
  rw [map_sum]
  rw [Finset.sum_eq_single q]
  · rw [cFM_comp]
    have : (projL hle q).comp (injL hle q) = ContinuousLinearMap.id ℝ F := by
      apply ContinuousLinearMap.ext
      intro v
      exact projL_injL_self hle q v
    rw [this, cFM_id]
  · intro q' _ hne
    rw [cFM_comp]
    have : (projL hle q).comp (injL hle q') = (0 : F →L[ℝ] F) := by
      apply ContinuousLinearMap.ext
      intro v
      exact projL_injL_ne hle (Ne.symm hne) v
    rw [this]
    exact ContinuousAlternatingMap.ext fun v => by simp [coefficientFormMap]
  · intro hq
    exact absurd (Finset.mem_univ q) hq

end PiForm

omit [FiniteDimensional ℝ F] in
theorem extDeriv_congr_eventually {k : ℕ} {w w' : RawFm F k} {x : Coordinates}
    (h : w =ᶠ[nhds x] w') : extDeriv w x = extDeriv w' x := by
  unfold extDeriv
  rw [h.fderiv_eq (𝕜 := ℝ)]

theorem pullRaw_star (G S : RealGL) {k : ℕ} (om : RawFm F k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    pullRaw (coordinateAction G) (star T S om) x =
      coefficientFormMap (T G).toContinuousLinearMap k (star T (G⁻¹ * S) om x) := by
  have h1 : pullRaw (coordinateAction G) (coefficientRaw (T S).toContinuousLinearMap
      (pullRaw (coordinateAction S⁻¹) om)) x =
      coefficientFormMap (T S).toContinuousLinearMap k
        (pullRaw (coordinateAction (S⁻¹ * G)) om x) := by
    rw [pullRaw_coefficientRaw]
    congr 1
    rw [pullRaw_comp om (differentiableAt_coordinateAction S⁻¹
        (coordinateAction_mem G x hx)) (differentiableAt_coordinateAction G hx),
      pullRaw_eventuallyEq om (coordinateAction_comp_eventuallyEq S⁻¹ G hx)]
  unfold star
  change pullRaw (coordinateAction G) (coefficientRaw (T S).toContinuousLinearMap
      (pullRaw (coordinateAction S⁻¹) om)) x =
    coefficientFormMap (T G).toContinuousLinearMap k (coefficientFormMap
      (T (G⁻¹ * S)).toContinuousLinearMap k (pullRaw (coordinateAction (G⁻¹ * S)⁻¹) om x))
  have e : (T G).toContinuousLinearMap.comp (T (G⁻¹ * S)).toContinuousLinearMap =
      (T S).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    change T G (T (G⁻¹ * S) v) = T S v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  rw [h1, cFM_comp, mul_inv_rev, inv_inv, e]


section Main

omit [FiniteDimensional ℝ F] in
theorem smul_mk (g r : FDeck) : g • (QuotientGroup.mk r : QD hle) = QuotientGroup.mk (g * r) := rfl

omit [FiniteDimensional ℝ F] in
theorem toDeck_inv_smul_base (h : H) :
    (toDeck hle h)⁻¹ • (QuotientGroup.mk 1 : QD hle) = QuotientGroup.mk 1 := by
  rw [smul_mk, mul_one]
  apply QuotientGroup.eq.mpr
  exact ⟨h, by simp⟩

theorem deckMap_eq (g : FDeck) : deckMap g = coordinateAction (deckMat g) := rfl

variable [Fintype (QD hle)]

/-- The primitive property of the coefficient system `T` over the subgroup `H`: every closed
smooth `H`-equivariant two-form with compact projected support has a smooth `H`-equivariant primitive. -/
def PrimitiveProperty (T : Representation ℝ RealGL F) (H : Subgroup RealGL) : Prop :=
  ∀ ζ : RawFm F 2, ContDiffOn ℝ ∞ ζ positiveCoordinates → (∀ x ∉ positiveCoordinates, ζ x = 0) →
    (∀ h : H, ∀ x ∈ positiveCoordinates, pullRaw (coordinateAction (h : RealGL)) ζ x =
      coefficientFormMap (T (h : RealGL)).toContinuousLinearMap 2 (ζ x)) →
    IsCompact (projSupport H ζ) → (∀ x ∈ positiveCoordinates, extDeriv ζ x = 0) →
    ∃ η : RawFm F 1, ContDiffOn ℝ ∞ η positiveCoordinates ∧ (∀ x ∉ positiveCoordinates, η x = 0) ∧
      (∀ h : H, ∀ x ∈ positiveCoordinates, pullRaw (coordinateAction (h : RealGL)) η x =
        coefficientFormMap (T (h : RealGL)).toContinuousLinearMap 1 (η x)) ∧
      ∀ x ∈ positiveCoordinates, extDeriv η x = ζ x


omit [Fintype (QD hle)] in
include hle in
/-- Compactness of the projected support descends to a finite-index subgroup. -/
theorem isCompact_projSupport_of_le [Finite (gamma0 ⧸ H.subgroupOf gamma0)] (hH : Admissible H)
    {M M' : Type*} [Zero M] [Zero M'] {w : Coordinates → M} {w' : Coordinates → M'}
    (hw : IsCompact (projSupport gamma0 w)) (hsub : Function.support w' ⊆ Function.support w) :
    IsCompact (projSupport H w') := by
  have hP : IsCompact (orbitMap hle ⁻¹' projSupport gamma0 w) :=
    isCompact_preimage_orbitMap hle admissible_principalSixInKReal hw
  have := hH.t2
  refine hP.of_isClosed_subset isClosed_closure ?_
  apply closure_minimal _ (hP.isClosed)
  rintro _ ⟨x, hx, rfl⟩
  exact subset_closure ⟨x, hsub hx, rfl⟩

section EtaProps

/-- Equivariance hypothesis of a one-form for the subgroup `H`. -/
def HEqv (T : Representation ℝ RealGL F) (H : Subgroup RealGL) {k : ℕ} (w : RawFm F k) : Prop :=
  ∀ h : H, ∀ x ∈ positiveCoordinates, pullRaw (coordinateAction (h : RealGL)) w x =
    coefficientFormMap (T (h : RealGL)).toContinuousLinearMap k (w x)

open Classical in
theorem etaW_comp (et : RawFm F 1) (q : QD hle) :
    coefficientRaw (projL hle q) (etaW (T := T) hle et) = psiQ T hle et q :=
  funext fun x => cFM_projL_etaW hle et q x

open Classical in
theorem etaW_smooth {et : RawFm F 1} (hets : ContDiffOn ℝ ∞ et positiveCoordinates)
    (hete : HEqv T H et) : ContDiffOn ℝ ∞ (etaW (T := T) hle et) positiveCoordinates := by
  have hpsis : ∀ q, ContDiffOn ℝ ∞ (psiQ T hle et q) positiveCoordinates := by
    intro q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    exact (star_smooth T (deckMat r) hets).congr (fun x hx => psiQ_eq hle hete r hx)
  have := ContDiffOn.sum (s := Finset.univ)
    (f := fun q x => coefficientFormMap (injL hle q) 1 (psiQ T hle et q x))
    (fun q _ => coefficientRaw_smooth (injL hle q) (hpsis q))
  exact this

open Classical in
theorem etaW_zero (et : RawFm F 1) {x : Coordinates} (hx : x ∉ positiveCoordinates) :
    etaW (T := T) hle et x = 0 := by
  change ∑ q, coefficientFormMap (injL hle q) 1 (psiQ T hle et q x) = 0
  apply Finset.sum_eq_zero
  intro q _
  have : psiQ T hle et q x = 0 := by
    unfold psiQ
    rw [ite_eq_right hx]
  rw [this, map_zero]

open Classical in
theorem etaW_equivariant {et : RawFm F 1} (hete : HEqv T H et) (g : FDeck) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    pullRaw (coordinateAction (deckMat g)) (etaW (T := T) hle et) x =
      coefficientFormMap (indReal T hle g).toContinuousLinearMap 1 (etaW (T := T) hle et x) := by
  apply ext_projL hle
  intro q
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← pullRaw_coefficientRaw, etaW_comp, cFM_comp]
  have e2 : (projL hle (QuotientGroup.mk r)).comp (indReal T hle g).toContinuousLinearMap =
      (T (deckMat g)).toContinuousLinearMap.comp (projL hle (QuotientGroup.mk (g⁻¹ * r))) := by
    apply ContinuousLinearMap.ext
    intro w
    change projL hle (QuotientGroup.mk r) (indReal T hle g w) =
      T (deckMat g) (projL hle (QuotientGroup.mk (g⁻¹ * r)) w)
    rw [projL_indReal, smul_mk]
  rw [e2, ← cFM_comp]
  change _ = coefficientFormMap (T (deckMat g)).toContinuousLinearMap 1
    (coefficientRaw (projL hle (QuotientGroup.mk (g⁻¹ * r))) (etaW (T := T) hle et) x)
  rw [etaW_comp]
  calc pullRaw (coordinateAction (deckMat g)) (psiQ T hle et (QuotientGroup.mk r)) x
      = pullRaw (coordinateAction (deckMat g)) (star T (deckMat r) et) x :=
        pullRaw_congr_on _ _ _ (psiQ_eq hle hete r (coordinateAction_mem _ x hx))
    _ = coefficientFormMap (T (deckMat g)).toContinuousLinearMap 1
          (star T ((deckMat g)⁻¹ * deckMat r) et x) := pullRaw_star _ _ et hx
    _ = _ := by rw [psiQ_eq hle hete (g⁻¹ * r) hx, map_mul, map_inv]

/-- The `r`-th component of an `indReal`-equivariant form is the `r`-translate of the base one. -/
theorem component_eq {om : RawFm (QD hle → F) 2}
    (home : ∀ (g : FDeck) (x : Coordinates), x ∈ positiveCoordinates →
      pullRaw (coordinateAction (deckMat g)) om x =
        coefficientFormMap (indReal T hle g).toContinuousLinearMap 2 (om x))
    (r : FDeck) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coefficientFormMap (projL hle (QuotientGroup.mk r)) 2 (om x) =
      star T (deckMat r) (coefficientRaw (projL hle (QuotientGroup.mk 1)) om) x := by
  have e1 := home r⁻¹ x hx
  have e2 := congrArg (coefficientFormMap (projL hle (QuotientGroup.mk 1)) 2) e1
  rw [← pullRaw_coefficientRaw, cFM_comp] at e2
  have e3 : (projL hle (QuotientGroup.mk 1)).comp (indReal T hle r⁻¹).toContinuousLinearMap =
      (T (deckMat r)⁻¹).toContinuousLinearMap.comp (projL hle (QuotientGroup.mk r)) := by
    apply ContinuousLinearMap.ext
    intro w
    change projL hle (QuotientGroup.mk 1) (indReal T hle r⁻¹ w) =
      T (deckMat r)⁻¹ (projL hle (QuotientGroup.mk r) w)
    rw [projL_indReal, inv_inv, smul_mk, mul_one, map_inv]
  rw [e3, ← cFM_comp, map_inv] at e2
  rw [star_apply, e2, cFM_comp]
  have e4 : (T (deckMat r)).toContinuousLinearMap.comp (T (deckMat r)⁻¹).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ F := by
    apply ContinuousLinearMap.ext
    intro v
    change T (deckMat r) (T (deckMat r)⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [e4, cFM_id]

open Classical in
theorem etaW_extDeriv {om : RawFm (QD hle → F) 2}
    (home : ∀ (g : FDeck) (x : Coordinates), x ∈ positiveCoordinates →
      pullRaw (coordinateAction (deckMat g)) om x =
        coefficientFormMap (indReal T hle g).toContinuousLinearMap 2 (om x))
    {et : RawFm F 1} (hets : ContDiffOn ℝ ∞ et positiveCoordinates) (hete : HEqv T H et)
    (hetd : ∀ x ∈ positiveCoordinates, extDeriv et x =
      coefficientRaw (projL hle (QuotientGroup.mk 1)) om x)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    extDeriv (etaW (T := T) hle et) x = om x := by
  apply ext_projL hle
  intro q
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
  have hd1 : DifferentiableAt ℝ (etaW (T := T) hle et) x :=
    ((etaW_smooth hle hets hete x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  rw [component_eq hle home r hx]
  change coefficientFormMap (projL hle (QuotientGroup.mk r)) 2
    (extDeriv (etaW (T := T) hle et) x) = _
  rw [← extDeriv_coefficientRaw _ hd1, etaW_comp]
  rw [extDeriv_congr_eventually (w' := star T (deckMat r) et)
    (Filter.eventuallyEq_of_mem (isOpen_positiveCoordinates.mem_nhds hx)
      (fun y hy => psiQ_eq hle hete r hy)),
    star_extDeriv T _ hets hx]
  exact star_congr_on T _ hetd hx

end EtaProps

/-- The base component of a closed equivariant compactly supported two-form has a primitive. -/
theorem base_primitive [Finite (gamma0 ⧸ H.subgroupOf gamma0)] (hH : Admissible H)
    (hP : PrimitiveProperty T H) {om : RawFm (QD hle → F) 2}
    (homs : ContDiffOn ℝ ∞ om positiveCoordinates) (homo : ∀ x ∉ positiveCoordinates, om x = 0)
    (home : ∀ (g : FDeck) (x : Coordinates), x ∈ positiveCoordinates →
      pullRaw (coordinateAction (deckMat g)) om x =
        coefficientFormMap (indReal T hle g).toContinuousLinearMap 2 (om x))
    (homc : IsCompact (projSupport gamma0 om))
    (homd : ∀ x ∈ positiveCoordinates, extDeriv om x = 0) :
    ∃ et : RawFm F 1, ContDiffOn ℝ ∞ et positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, et x = 0) ∧ HEqv T H et ∧
      ∀ x ∈ positiveCoordinates, extDeriv et x =
        coefficientRaw (projL hle (QuotientGroup.mk 1)) om x := by
  have hdiff : ∀ x ∈ positiveCoordinates, DifferentiableAt ℝ om x := fun x hx =>
    ((homs x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  refine hP (coefficientRaw (projL hle (QuotientGroup.mk 1)) om)
    (coefficientRaw_smooth _ homs) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coefficientRaw, homo x hx, map_zero]
  · intro h x hx
    have e1 := home (toDeck hle h) x hx
    rw [deckMat_toDeck hle h] at e1
    rw [pullRaw_coefficientRaw, e1, cFM_comp]
    have e2 : (projL hle (QuotientGroup.mk 1)).comp (indReal T hle (toDeck hle h)).toContinuousLinearMap =
        (T (h : RealGL)).toContinuousLinearMap.comp (projL hle (QuotientGroup.mk 1)) := by
      apply ContinuousLinearMap.ext
      intro w
      change projL hle (QuotientGroup.mk 1) (indReal T hle (toDeck hle h) w) =
        T (h : RealGL) (projL hle (QuotientGroup.mk 1) w)
      rw [projL_indReal, deckMat_toDeck hle h, toDeck_inv_smul_base]
    rw [e2, ← cFM_comp]
    rfl
  · refine isCompact_projSupport_of_le hle hH homc ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by
      change coefficientFormMap (projL hle (QuotientGroup.mk 1)) 2 (om x) = 0
      rw [h0, map_zero])
  · intro x hx
    rw [extDeriv_coefficientRaw _ (hdiff x hx), homd x hx, map_zero]

open Classical in
/-- **Smooth Shapiro lemma.**  If `T` has the primitive property on the finite-index subgroup `H` of
the cover, the induced representation `indReal T hle` of the deck group is smoothly exact in
degree one: compactly supported closed equivariant two-forms are exact. -/
theorem compactExact_induced [Finite (gamma0 ⧸ H.subgroupOf gamma0)] (hH : Admissible H)
    (hP : PrimitiveProperty T H) : CompactExactInDegree (indReal T hle) 1 := by
  intro a ha
  have homs : ContDiffOn ℝ ∞ (a.val.val.val : RawFm (QD hle → F) 2) positiveCoordinates := by
    simpa only [liftedDomain_univ] using Form.smooth a.val.val
  have homo : ∀ x ∉ positiveCoordinates, (a.val.val.val : RawFm (QD hle → F) 2) x = 0 :=
    fun x hx => Form.outside a.val.val (by simpa only [liftedDomain_univ] using hx)
  have home : ∀ (g : FDeck) (x : Coordinates), x ∈ positiveCoordinates →
      pullRaw (coordinateAction (deckMat g)) (a.val.val.val : RawFm (QD hle → F) 2) x =
        coefficientFormMap (indReal T hle g).toContinuousLinearMap 2
          ((a.val.val.val : RawFm (QD hle → F) 2) x) := fun g x hx =>
    a.val.property g x (by simpa only [liftedDomain_univ] using hx)
  have homc : IsCompact (projSupport gamma0 (a.val.val.val : RawFm (QD hle → F) 2)) :=
    (coveringCompact_iff _).mp a.property.1
  have homd : ∀ x ∈ positiveCoordinates, extDeriv (a.val.val.val : RawFm (QD hle → F) 2) x = 0 := by
    intro x hx
    have hx' : x ∈ liftedDomain (Set.univ : Set FOrbit) := by simpa using hx
    have h1 := congrArg (fun b : CompactSupportForm (indReal T hle) Set.univ (1 + 1 + 1) =>
      (b.val.val.val : RawFm (QD hle → F) 3) x) ha
    rw [compactDifferential_coe, differential_coe] at h1
    exact (d_apply (liftedDomain_isOpen isOpen_univ) a.val.val hx').symm.trans h1
  obtain ⟨et, hets, heto, hete, hetd⟩ := base_primitive hle hH hP homs homo home homc homd
  have hs' : ContDiffOn ℝ ∞ (etaW (T := T) hle et) (liftedDomain (Set.univ : Set FOrbit)) := by
    simpa only [liftedDomain_univ] using etaW_smooth hle hets hete
  have ho' : ∀ x ∉ liftedDomain (Set.univ : Set FOrbit), etaW (T := T) hle et x = 0 := fun x hx =>
    etaW_zero hle et (by simpa only [liftedDomain_univ] using hx)
  refine ⟨⟨⟨etaW (T := T) hle et, hs', ho'⟩, fun g x hx =>
    etaW_equivariant hle hete g (by simpa only [liftedDomain_univ] using hx)⟩, ?_⟩
  apply Subtype.ext
  apply Form.ext
  intro x hx
  have hx' : x ∈ positiveCoordinates := by simpa using hx
  rw [differential_coe]
  exact (d_apply (liftedDomain_isOpen isOpen_univ)
    (⟨etaW (T := T) hle et, hs', ho'⟩ : Form (F := QD hle → F) _ 1) hx).trans
    (etaW_extDeriv hle home hets hete hetd hx')

end Main

end Assemble


section IndModel

open TernaryPoly.SmoothSingularGlobal

variable {G H : Type} [Group G] [Group H] (φ : H →* G) [Fintype (G ⧸ φ.range)]
  (V : Rep.{0} ℚ G) {F : Type} [AddCommGroup F] [Module ℝ F]

open Classical in
/-- The real scalar extension of the induced system is the induced real system. -/
def indRealEquiv (ε : realRep V ≃ₗ[ℝ] F) : realRep (indRep φ V) ≃ₗ[ℝ] ((G ⧸ φ.range) → F) :=
  (TensorProduct.piRight ℚ ℝ ℝ (fun _ : G ⧸ φ.range => V)).trans
    (LinearEquiv.piCongrRight fun _ => ε)

open Classical in
theorem indRealEquiv_tmul (ε : realRep V ≃ₗ[ℝ] F) (r : ℝ) (w : (G ⧸ φ.range) → V)
    (q : G ⧸ φ.range) :
    indRealEquiv φ V ε (r ⊗ₜ[ℚ] w) q = ε (r ⊗ₜ[ℚ] w q) := by
  simp [indRealEquiv, TensorProduct.piRight_apply]

open Classical in
theorem indRealEquiv_equivariant (σ : Representation ℝ G F) (ε : realRep V ≃ₗ[ℝ] F)
    (hε : ∀ g z, ε ((realRep V).ρ g z) = σ g (ε z)) (g : G) (z : realRep (indRep φ V))
    (q : G ⧸ φ.range) :
    indRealEquiv φ V ε ((realRep (indRep φ V)).ρ g z) q =
      σ g (indRealEquiv φ V ε z (g⁻¹ • q)) := by
  induction z using TensorProduct.inductionOn with
  | tmul r w =>
    change indRealEquiv φ V ε (realAction (indRep φ V) g (r ⊗ₜ[ℚ] w)) q = _
    rw [realAction_tmul, indRealEquiv_tmul, indRealEquiv_tmul]
    exact hε g (r ⊗ₜ[ℚ] w (g⁻¹ • q))
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]

end IndModel

section Descent

open scoped TensorProduct
open TernaryPoly.SmoothSingularGlobal

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (T : Representation ℝ RealGL F) {H : Subgroup RealGL} (hle : H ≤ gamma0)

/-- **Vanishing for a finite-index subgroup of the cover.**  If the rational deck system `V` has
real scalar extension equivariantly isomorphic to the real representation `T`, and `T` has the primitive
property over the admissible finite-index subgroup `H`, then the actual singular compact-to-ordinary
map of `H` with the restricted coefficients `V|_H` vanishes in degree two. -/
theorem singularVanish_of_primitive [Finite (gamma0 ⧸ H.subgroupOf gamma0)] (hH : Admissible H)
    (V : Rep.{0} ℚ FDeck) [FiniteDimensional ℚ V] (ε : realRep V ≃ₗ[ℝ] F)
    (hε : ∀ g z, ε ((realRep V).ρ g z) = deckRep T g (ε z)) (hP : PrimitiveProperty T H) :
    SingularVanish H hH (Rep.res (toDeck hle) V) := by
  have : Finite (FDeck ⧸ (toDeck hle).range) := finite_deck_quotient hle
  have : Fintype (FDeck ⧸ (toDeck hle).range) := Fintype.ofFinite _
  refine singularVanish_of_deck_ind hle hH V ?_
  exact compactForget_zero_of_equiv (indRep (toDeck hle) V) (indReal T hle)
    (indRealEquiv (toDeck hle) V ε)
    (fun g z => funext fun q => indRealEquiv_equivariant (toDeck hle) V (deckRep T) ε hε g z q)
    (compactExact_induced hle hH hP)

end Descent


section Primitives

open TernaryPoly.SmoothCoveringDeRham

variable {n : ℕ} {H : Subgroup RealGL}

theorem primitive_real (hH : Admissible H) (hn : 0 < n) : PrimitiveProperty (Treal n) H := by
  intro ζ hs ho he hc hd
  let ζ' : CForm H n 2 := ⟨⟨ζ, hs, ho⟩, he, hc⟩
  have hd' : CForm.d H n 2 ζ' = 0 := by
    apply CForm.ext
    intro x hx
    rw [CForm.d_apply ζ' hx]
    exact hd x hx
  exact Admissible.closed_compact_exact hH hn ζ' hd'

theorem primitive_dual (hH : Admissible H) (hn : 0 < n) : PrimitiveProperty (Tdual n) H := by
  intro ζ hs ho he hc hd
  let ζ' : DForm H n 2 := ⟨⟨ζ, hs, ho⟩, he, hc⟩
  have hd' : dualD hH n 2 ζ' = 0 := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    exact (dualD_apply hH ζ' hx).trans (hd x hx)
  exact Admissible.closed_compact_exact_dual hH hn ζ' hd'

theorem primitive_complex (hH : Admissible H) (hn : 0 < n) : PrimitiveProperty (Tcx n) H := by
  intro ζ hs ho he hc hd
  let ζ' : CFormCx H n 2 := ⟨⟨ζ, hs, ho⟩, he, hc⟩
  have hd' : CFormCx.d H n 2 ζ' = 0 := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    exact (CFormCx.d_apply ζ' hx).trans (hd x hx)
  exact Admissible.closed_compact_exact_complex hH hn ζ' hd'

theorem primitive_complex_dual (hH : Admissible H) (hn : 0 < n) :
    PrimitiveProperty (Tcxd n) H := by
  intro ζ hs ho he hc hd
  let ζ' : CFormCxD H n 2 := ⟨⟨ζ, hs, ho⟩, he, hc⟩
  have hd' : CFormCxD.d hH n 2 ζ' = 0 := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    exact (CFormCxD.d_apply hH ζ' hx).trans (hd x hx)
  exact Admissible.closed_compact_exact_complex_dual hH hn ζ' hd'

theorem primitive_lit (hH : Admissible H) (hn : 0 < n) : PrimitiveProperty (Tlit n) H := by
  intro ζ hs ho he hc hd
  let ζ' : LitForm H n 2 := ⟨⟨ζ, hs, ho⟩, he, hc⟩
  have hd' : LitForm.d hH n 2 ζ' = 0 := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    exact (LitForm.d_apply hH ζ' hx).trans (hd x hx)
  exact Admissible.closed_compact_exact_lit hH hn ζ' hd'

end Primitives

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
