module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.CoveringBridge
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.LiteralForms
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimGlobal
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimCoeff

@[expose] public section


/-!
# Smooth exactness of the covering complex for the five coefficient systems

For the fixed deck group `DeckGroup = principalSixInK` (the cover `gamma0 = principalSixInKReal`),
`CompactExactInDegree (deckRep T) 1` -- every closed compactly supported smooth equivariant two-form of
the covering complex has a smooth equivariant primitive -- is proved from the Tier B theorems of
`TierB/PrimGlobal` and `TierB/PrimCoeff`, through the identification `coveringEquiv` of the covering
complex with the generic equivariant form spaces, for the representations

* `Treal n` -- the real polynomial coefficients (`CForm`),
* `Tdual n` -- the Cartan-twisted dual coefficients (`DForm`),
* `Tcx n` -- the complexification `Sym^n ℂ³` as a real representation (`CFormCx`),
* `Tcxd n` -- the complexified dual (`CFormCxD`),
* `Tlit n` -- the literal `ℂ`-linear dual `StrongDual ℂ (Sym^n ℂ³)` with the contragredient action
  (`LitForm`).

No input from the theorem `positive_degree_compact_smooth_exact` is used: these results rest
on the Γ-free coordinate weak-regularity package of the original library through `Admissible.closed_compact_exact`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set Topology TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialCoefficientMetric
open scoped TernaryPoly.SymmetricSpaceRiemannian Pointwise ContDiff

/-! ### The five coefficient systems -/

section Systems

variable {n : ℕ}

/-- The real polynomial coefficients `Sym^n`. -/
abbrev Treal (n : ℕ) : Representation ℝ RealGL (Coefficients n) := realHomogeneousAction n

/-- The dual (Cartan-twisted) real coefficients. -/
abbrev Tdual (n : ℕ) : Representation ℝ RealGL (Coefficients n) := (Treal n).comp thetaHom

/-- The complexified coefficients `Sym^n ℂ³` as a real representation. -/
abbrev Tcx (n : ℕ) : Representation ℝ RealGL (ComplexCoefficients n) := complexRepresentation n

/-- The complexified dual coefficients. -/
abbrev Tcxd (n : ℕ) : Representation ℝ RealGL (ComplexCoefficients n) := (complexRepresentation n).comp thetaHom

theorem compactExact_real (hn : 0 < n) : CompactExactInDegree (deckRep (Treal n)) 1 := by
  refine compactExact_of_repForm (Treal n) (fun ζ hζ => ?_)
  let ζ' : CForm gamma0 n 2 := ⟨ζ.1, ζ.2⟩
  have hd : CForm.d gamma0 n 2 ζ' = 0 := by
    apply CForm.ext
    intro x hx
    rw [CForm.d_apply ζ' hx]
    exact hζ x hx
  exact Admissible.closed_compact_exact admissible_principalSixInKReal hn ζ' hd

theorem compactExact_dual (hn : 0 < n) : CompactExactInDegree (deckRep (Tdual n)) 1 := by
  refine compactExact_of_repForm (Tdual n) (fun ζ hζ => ?_)
  let ζ' : DForm gamma0 n 2 := ⟨ζ.1, ζ.2⟩
  have hd : dualD admissible_principalSixInKReal n 2 ζ' = 0 := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    exact (dualD_apply admissible_principalSixInKReal ζ' hx).trans (hζ x hx)
  exact Admissible.closed_compact_exact_dual admissible_principalSixInKReal hn ζ' hd

theorem compactExact_complex (hn : 0 < n) : CompactExactInDegree (deckRep (Tcx n)) 1 := by
  refine compactExact_of_repForm (Tcx n) (fun ζ hζ => ?_)
  let ζ' : CFormCx gamma0 n 2 := ⟨ζ.1, ζ.2⟩
  have hd : CFormCx.d gamma0 n 2 ζ' = 0 := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    exact (CFormCx.d_apply ζ' hx).trans (hζ x hx)
  exact Admissible.closed_compact_exact_complex admissible_principalSixInKReal hn ζ' hd

theorem compactExact_complex_dual (hn : 0 < n) : CompactExactInDegree (deckRep (Tcxd n)) 1 := by
  refine compactExact_of_repForm (Tcxd n) (fun ζ hζ => ?_)
  let ζ' : CFormCxD gamma0 n 2 := ⟨ζ.1, ζ.2⟩
  have hd : CFormCxD.d admissible_principalSixInKReal n 2 ζ' = 0 := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    exact (CFormCxD.d_apply admissible_principalSixInKReal ζ' hx).trans (hζ x hx)
  exact Admissible.closed_compact_exact_complex_dual admissible_principalSixInKReal hn ζ' hd

theorem litRep_eq_conj (g : RealGL) (x : LitCoeff n) :
    litRep n g x = litPhi n (Tcxd n g ((litPhi n).symm x)) := by
  have h := litPhi_equivariant n g ((litPhi n).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The contragredient action on the literal dual `StrongDual ℂ (Sym^n ℂ³)`, as a real
representation of `GL₃(ℝ)`. -/
def Tlit (n : ℕ) : Representation ℝ RealGL (LitCoeff n) where
  toFun g := (litRep n g : LitCoeff n →ₗ[ℝ] LitCoeff n)
  map_one' := by
    apply LinearMap.ext
    intro x
    change litRep n 1 x = x
    rw [litRep_eq_conj, map_one]
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change litRep n (g * h) x = litRep n g (litRep n h x)
    rw [litRep_eq_conj, litRep_eq_conj, litRep_eq_conj, map_mul, Module.End.mul_apply,
      LinearEquiv.symm_apply_apply]

theorem compactExact_lit (hn : 0 < n) : CompactExactInDegree (deckRep (Tlit n)) 1 := by
  refine compactExact_of_repForm (Tlit n) (fun ζ hζ => ?_)
  let ζ' : LitForm gamma0 n 2 := ⟨ζ.1, ζ.2⟩
  have hd : LitForm.d admissible_principalSixInKReal n 2 ζ' = 0 := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    exact (LitForm.d_apply admissible_principalSixInKReal ζ' hx).trans (hζ x hx)
  exact Admissible.closed_compact_exact_lit admissible_principalSixInKReal hn ζ' hd

end Systems


/-! ### The dictionary of forms -/

section Dictionary

variable (n k : ℕ)

/-- Real forms: the covering complex of `Treal n` is `CForm gamma0 n`. -/
def coveringReal : CompactSupportForm (deckRep (Treal n)) univ k ≃ₗ[ℝ] CForm gamma0 n k :=
  coveringEquiv (Treal n) k

/-- Dual forms. -/
def coveringDual : CompactSupportForm (deckRep (Tdual n)) univ k ≃ₗ[ℝ] DForm gamma0 n k :=
  coveringEquiv (Tdual n) k

/-- Complex forms. -/
def coveringCx : CompactSupportForm (deckRep (Tcx n)) univ k ≃ₗ[ℝ] CFormCx gamma0 n k :=
  coveringEquiv (Tcx n) k

/-- Complex dual forms. -/
def coveringCxD : CompactSupportForm (deckRep (Tcxd n)) univ k ≃ₗ[ℝ] CFormCxD gamma0 n k :=
  coveringEquiv (Tcxd n) k

/-- Literal dual-valued forms. -/
def coveringLit : CompactSupportForm (deckRep (Tlit n)) univ k ≃ₗ[ℝ] LitForm gamma0 n k :=
  coveringEquiv (Tlit n) k

variable {n k}

theorem coveringReal_d (a : CompactSupportForm (deckRep (Treal n)) univ k) :
    coveringReal n (k + 1) (compactDifferential (deckRep (Treal n)) isOpen_univ k a) =
      CForm.d gamma0 n k (coveringReal n k a) := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  exact (coveringEquiv_d (Treal n) k a hx).trans (CForm.d_apply (coveringReal n k a) hx).symm

theorem coveringDual_d (a : CompactSupportForm (deckRep (Tdual n)) univ k) :
    coveringDual n (k + 1) (compactDifferential (deckRep (Tdual n)) isOpen_univ k a) =
      dualD admissible_principalSixInKReal n k (coveringDual n k a) := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  exact (coveringEquiv_d (Tdual n) k a hx).trans
    (dualD_apply admissible_principalSixInKReal (coveringDual n k a) hx).symm

theorem coveringCx_d (a : CompactSupportForm (deckRep (Tcx n)) univ k) :
    coveringCx n (k + 1) (compactDifferential (deckRep (Tcx n)) isOpen_univ k a) =
      CFormCx.d gamma0 n k (coveringCx n k a) := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  exact (coveringEquiv_d (Tcx n) k a hx).trans (CFormCx.d_apply (coveringCx n k a) hx).symm

theorem coveringCxD_d (a : CompactSupportForm (deckRep (Tcxd n)) univ k) :
    coveringCxD n (k + 1) (compactDifferential (deckRep (Tcxd n)) isOpen_univ k a) =
      CFormCxD.d admissible_principalSixInKReal n k (coveringCxD n k a) := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  exact (coveringEquiv_d (Tcxd n) k a hx).trans
    (CFormCxD.d_apply admissible_principalSixInKReal (coveringCxD n k a) hx).symm

theorem coveringLit_d (a : CompactSupportForm (deckRep (Tlit n)) univ k) :
    coveringLit n (k + 1) (compactDifferential (deckRep (Tlit n)) isOpen_univ k a) =
      LitForm.d admissible_principalSixInKReal n k (coveringLit n k a) := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  exact (coveringEquiv_d (Tlit n) k a hx).trans
    (LitForm.d_apply admissible_principalSixInKReal (coveringLit n k a) hx).symm

end Dictionary

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
