module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.Frozen
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactExactHomology

@[expose] public section


/-!
# The covering de Rham complex and generic equivariant form spaces

For a real representation `T` of `GL₃(ℝ)` on a finite dimensional space `F`, the representation
`deckRep T` of the fixed deck group `DeckGroup = principalSixInK` is `T ∘ deckMatrix`.  The actual
spaces of compactly supported equivariant smooth forms of the covering complex of
`TernaryPoly.SmoothCoveringDeRham` (`CompactSupportForm (deckRep T) univ k`, with
`compactDifferential`) are linearly isomorphic (`coveringEquiv`) to the generic space `RepForm T k` of
smooth `gamma0`-equivariant forms with compact projected support, with the same underlying
functions, and the isomorphism commutes with the exterior derivative (`coveringEquiv_d`).  For the
real polynomial coefficients this is `frozenEquiv`; here the coefficient representation is arbitrary.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set Topology TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialCoefficientMetric
open scoped TernaryPoly.SymmetricSpaceRiemannian Pointwise ContDiff

section Bridge

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The matrix of a deck transformation, as a monoid homomorphism into `GL₃(ℝ)`. -/
abbrev deckMat : FDeck →* RealGL := TernaryPoly.PolynomialCoefficientMetric.deckMatrix

/-- The deck group representation induced by a representation of `GL₃(ℝ)`. -/
def deckRep (T : Representation ℝ RealGL F) : Representation ℝ FDeck F := T.comp deckMat

theorem toGamma_coe (g : FDeck) : ((toGamma g : gamma0) : RealGL) = deckMat g := rfl

/-- Equivariance of a form for the representation `T` restricted to `gamma0`. -/
def RepEqv (T : Representation ℝ RealGL F) (k : ℕ)
    (w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F) : Prop :=
  ∀ (γ : gamma0) (x : Coordinates), x ∈ positiveCoordinates →
    pullRaw (coordinateAction (γ : RealGL)) w x =
      coefficientFormMap (T (γ : RealGL)).toContinuousLinearMap k (w x)

theorem repEqv_zero (T : Representation ℝ RealGL F) (k : ℕ) : RepEqv T k 0 := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simp [pullRaw, coefficientFormMap]

theorem RepEqv.add {T : Representation ℝ RealGL F} {k : ℕ}
    {w z : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F} (hw : RepEqv T k w) (hz : RepEqv T k z) :
    RepEqv T k (w + z) := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simpa [pullRaw, coefficientFormMap] using
    congrArg (fun z : Coordinates [⋀^Fin k]→L[ℝ] F => z v)
      (congrArg₂ (· + ·) (hw g x hx) (hz g x hx))

theorem RepEqv.smul {T : Representation ℝ RealGL F} {k : ℕ} (c : ℝ)
    {w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F} (hw : RepEqv T k w) :
    RepEqv T k (c • w) := by
  intro g x hx
  apply ContinuousAlternatingMap.ext
  intro v
  simpa [pullRaw, coefficientFormMap] using
    congrArg (fun z : Coordinates [⋀^Fin k]→L[ℝ] F => z v) (congrArg (c • ·) (hw g x hx))

variable (T : Representation ℝ RealGL F) (k : ℕ)

/-- Smooth `gamma0`-equivariant `k`-forms for `T` with compact closed projected support. -/
def RepForm : Submodule ℝ (Form (F := F) positiveCoordinates k) where
  carrier := {w | RepEqv T k (w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F) ∧
    IsCompact (projSupport gamma0 (w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F))}
  zero_mem' := ⟨repEqv_zero T k, by simp [projSupport]⟩
  add_mem' := by
    rintro w z ⟨hw, hwc⟩ ⟨hz, hzc⟩
    refine ⟨hw.add hz, (hwc.union hzc).of_isClosed_subset isClosed_closure ?_⟩
    unfold projSupport
    rw [← closure_union, ← image_union]
    exact closure_mono (image_mono (Function.support_add _ _))
  smul_mem' := by
    rintro c w ⟨hw, hwc⟩
    refine ⟨hw.smul c, hwc.of_isClosed_subset isClosed_closure ?_⟩
    unfold projSupport
    exact closure_mono (image_mono (Function.support_const_smul_subset c _))


/-- The underlying function of an `RepForm`. -/
abbrev RepForm.fn {T : Representation ℝ RealGL F} {k : ℕ} (w : RepForm T k) :
    Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F :=
  ((w : Form (F := F) positiveCoordinates k) : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F)

@[ext] theorem RepForm.ext {T : Representation ℝ RealGL F} {k : ℕ} {w z : RepForm T k}
    (h : ∀ x ∈ positiveCoordinates, RepForm.fn w x = RepForm.fn z x) : w = z :=
  Subtype.ext (Form.ext h)

theorem coveringEquivariant_iff (w : Coordinates → Coordinates [⋀^Fin k]→L[ℝ] F) :
    TernaryPoly.SmoothCoveringDeRham.IsEquivariant (deckRep T) (Set.univ : Set FOrbit) w ↔
      RepEqv T k w := by
  constructor
  · intro h γ x hx
    obtain ⟨g, rfl⟩ := toGamma_surjective γ
    exact h g x (by simpa using hx)
  · intro h g x hx
    exact h (toGamma g) x (by simpa using hx)

theorem projSupport_eq_image' {M : Type*} [Zero M] (w : Coordinates → M) :
    projSupport gamma0 w = orbitHomeo '' closure (coordinateProjection '' Function.support w) := by
  rw [orbitHomeo.image_closure, projSupport, image_image]
  rfl

theorem coveringCompact_iff {M : Type*} [Zero M] (w : Coordinates → M) :
    IsCompact (closure (coordinateProjection '' Function.support w)) ↔
      IsCompact (projSupport gamma0 w) := by
  rw [projSupport_eq_image']
  constructor
  · exact fun h => h.image orbitHomeo.continuous
  · intro h
    have := h.image orbitHomeo.symm.continuous
    rwa [image_image, show (fun x => orbitHomeo.symm (orbitHomeo x)) = id from
      funext orbitHomeo.symm_apply_apply, image_id] at this

/-- Compactly supported forms of the covering complex to generic equivariant forms. -/
def coveringTo : CompactSupportForm (deckRep T) univ k →ₗ[ℝ] RepForm T k where
  toFun a := ⟨⟨a.val.val.val, by simpa only [liftedDomain_univ] using Form.smooth a.val.val,
      fun x hx => Form.outside a.val.val (by simpa only [liftedDomain_univ] using hx)⟩,
    (coveringEquivariant_iff T k _).mp a.val.property, (coveringCompact_iff _).mp a.property.1⟩
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

/-- Generic equivariant forms to compactly supported forms of the covering complex. -/
def coveringFrom : RepForm T k →ₗ[ℝ] CompactSupportForm (deckRep T) univ k where
  toFun w :=
    have hs : ContDiffOn ℝ ∞ (RepForm.fn w) (liftedDomain (Set.univ : Set FOrbit)) := by
      simpa only [liftedDomain_univ] using Form.smooth (w : Form (F := F) positiveCoordinates k)
    have ho : ∀ x ∉ liftedDomain (Set.univ : Set FOrbit), RepForm.fn w x = 0 := by
      intro x hx
      exact Form.outside (w : Form (F := F) positiveCoordinates k)
        (by simpa only [liftedDomain_univ] using hx)
    ⟨⟨⟨RepForm.fn w, hs, ho⟩, (coveringEquivariant_iff T k _).mpr w.2.1⟩,
      (coveringCompact_iff _).mpr w.2.2, Set.subset_univ _⟩
  map_add' _ _ := Subtype.ext (Subtype.ext (Subtype.ext rfl))
  map_smul' _ _ := Subtype.ext (Subtype.ext (Subtype.ext rfl))

/-- **The covering de Rham complex in degree `k` is the generic equivariant form space.** -/
def coveringEquiv : CompactSupportForm (deckRep T) univ k ≃ₗ[ℝ] RepForm T k :=
  LinearEquiv.ofLinearMap (coveringTo T k) (coveringFrom T k)
    (LinearMap.ext fun _ => Subtype.ext (Subtype.ext rfl))
    (LinearMap.ext fun _ => Subtype.ext (Subtype.ext (Subtype.ext rfl)))

theorem coveringEquiv_fn (a : CompactSupportForm (deckRep T) univ k) :
    RepForm.fn (coveringEquiv T k a) = a.val.val.val := rfl

/-- The exterior differential of the covering complex is the pointwise exterior derivative. -/
theorem coveringEquiv_d (a : CompactSupportForm (deckRep T) univ k) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    RepForm.fn (coveringEquiv T (k + 1) (compactDifferential (deckRep T) isOpen_univ k a)) x =
      extDeriv (RepForm.fn (coveringEquiv T k a)) x := by
  have hx' : x ∈ liftedDomain (Set.univ : Set FOrbit) := by simpa using hx
  exact TernaryPoly.SmoothLocalDeRham.d_apply
    (liftedDomain_isOpen isOpen_univ) a.val.val hx'

/-- **Smooth exactness from the generic form statement.**  If every closed generic equivariant
two-form of compact support has a smooth equivariant primitive, the covering complex is exact in
the sense of `CompactExactInDegree`. -/
theorem compactExact_of_repForm
    (H : ∀ ζ : RepForm T 2, (∀ x ∈ positiveCoordinates, extDeriv (RepForm.fn ζ) x = 0) →
      ∃ η : Coordinates → Coordinates [⋀^Fin 1]→L[ℝ] F, ContDiffOn ℝ ∞ η positiveCoordinates ∧
        (∀ x ∉ positiveCoordinates, η x = 0) ∧ RepEqv T 1 η ∧
        ∀ x ∈ positiveCoordinates, extDeriv η x = RepForm.fn ζ x) :
    CompactExactInDegree (deckRep T) 1 := by
  intro a ha
  have hclosed : ∀ x ∈ positiveCoordinates, extDeriv (RepForm.fn (coveringEquiv T 2 a)) x = 0 := by
    intro x hx
    rw [← coveringEquiv_d T 2 a hx, ha]
    rfl
  obtain ⟨η, hs, ho, he, hd⟩ := H (coveringEquiv T 2 a) hclosed
  have hs' : ContDiffOn ℝ ∞ η (liftedDomain (Set.univ : Set FOrbit)) := by
    simpa only [liftedDomain_univ] using hs
  have ho' : ∀ x ∉ liftedDomain (Set.univ : Set FOrbit), η x = 0 := by
    intro x hx
    exact ho x (by simpa only [liftedDomain_univ] using hx)
  refine ⟨⟨⟨η, hs', ho'⟩, (coveringEquivariant_iff T 1 _).mpr he⟩, ?_⟩
  apply Subtype.ext
  apply Form.ext
  intro x hx
  have hx' : x ∈ positiveCoordinates := by simpa using hx
  rw [differential_coe]
  exact (d_apply (liftedDomain_isOpen isOpen_univ) (⟨η, hs', ho'⟩ : Form (F := F) _ 1) hx).trans
    ((hd x hx').trans rfl)

end Bridge

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
