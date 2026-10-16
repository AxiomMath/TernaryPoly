module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.PLeftKernel
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.LinearSelection
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Model

@[expose] public section



/-!
# Graph containment (`ar:prop:graph`) in the boundary-building cochain model

Paper (Appendix C.4): *Let `n ≥ 4`. If a global degree-two class with coefficients `E` has only mixed cuspidal
maximal-face restrictions `(ξ_P, ξ_Q)` and zero flag restrictions, then `ξ_Q = T ξ_P`.* The proof pairs the class with
the dual series `𝓔_Q^∨(η)` in the Stokes lemma, pairs `𝓔_P(ξ_P)` with the same dual class, subtracts the two relations
and uses the perfect line pairing; no invertibility or adjoint normalization of `T^∨` is used.

In the model:

* `EdgeExactGlobal c` is "zero flag restrictions" (`r_B c = 0`): the restriction of `c` to the complete flags is the
  coboundary of an edge primitive (such a class automatically has inner maximal restrictions,
  `innerBoundary_restriction_of_exact`).
* `exists_constant_term_map`: the constant-term map `T` of `ar:eq:constantterms` as one linear map, chosen from the
  `constant_terms` (the paper's `T ξ = r_Q 𝓔_P(ξ)` is the line restriction of such a class).
* `graph_containment_pair`: two classes with zero flag restrictions and equal plane restriction have equal line
  restriction. The two Stokes relations are `facePairingP_global_eq_facePairing_global` for the pairs
  `(c, c')` and `(c₁, c')`, where `c'` ranges over classes `𝓔_P(a')` with `r_P c' = a'` arbitrary; `c' ∘ φ`
  is the dual series class `𝓔_Q^∨(η)` for `η = toLineStar a'` (`DualJ.Pullback`: the transport along `φ` is the
  `ȷ`-pullback of the construction for `ȷ(Γ)`), and `face_pairing_stokes` is literally the Stokes lemma for the cup product
  `c ⌣ (c' ∘ φ)`. The final step is the perfectness of the line pairing (`facePairing_left_nondegenerate`, zero
  left kernel, all `n`).
* `graph_containment`: for the map `T` every class with zero flag restrictions has `ξ_Q = T ξ_P`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.GraphPieces.BoundaryExactness
open TernaryPeriodPolynomials.Argument.Classification

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

variable {n : ℕ}

/-- A global cocycle has zero restriction to every complete flag (`r_B c = 0`): its restriction to
the edges is the coboundary of an edge primitive. -/
def EdgeExactGlobal
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) : Prop :=
  ∃ w : EdgeCochains n trivialCharacter 1, ∀ x e, c.val.val x = differentialOneRaw w.val x e

theorem EdgeExactGlobal.sub
    {c c₁ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hc : EdgeExactGlobal c) (hc₁ : EdgeExactGlobal c₁) : EdgeExactGlobal (c - c₁) := by
  obtain ⟨w, hw⟩ := hc
  obtain ⟨w₁, hw₁⟩ := hc₁
  refine ⟨w - w₁, fun x e => ?_⟩
  change c.val.val x - c₁.val.val x = _
  rw [hw x e, hw₁ x e]
  simp only [differentialOneRaw, Submodule.coe_sub, Pi.sub_apply, Pi.add_apply]
  abel

/-- **Graph containment (`ar:prop:graph`), the two-class form.** Let `n ≥ 4`. Two global classes with
zero flag restrictions and the same plane restriction have the same line restriction. This is the
proposition's content: the line restriction `ξ_Q` of a class with zero flag restrictions is determined
by its plane restriction `ξ_P` (and equals `T ξ_P` for the constant-term map `T`, `graph_containment`).

The proof is the paper's: Stokes (`facePairingP_global_eq_facePairing_global`) against a class
`c'` whose plane restriction is an arbitrary inner plane class (the dual series of the paper, see
`graph_containment_dual`), twice, subtracted; then the perfect line pairing
(`facePairing_left_nondegenerate`). -/
theorem graph_containment_pair (hn : 4 ≤ n)
    (c c₁ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : EdgeExactGlobal c) (hc₁ : EdgeExactGlobal c₁)
    (hP : (globalCoordinates n trivialCharacter c).1 = (globalCoordinates n trivialCharacter c₁).1) :
    (globalCoordinates n trivialCharacter c).2 = (globalCoordinates n trivialCharacter c₁).2 := by
  have hsubex := hc.sub hc₁
  rcases hsubex with ⟨wd, hwd⟩
  have hlin : ∀ d : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      globalCoordinates n trivialCharacter d =
        Dual.globalCoordinatesRepLinear (rationalCoefficientComponent n trivialCharacter) d :=
    fun d => rfl
  have hsub : globalCoordinates n trivialCharacter (c - c₁) =
      globalCoordinates n trivialCharacter c - globalCoordinates n trivialCharacter c₁ := by
    rw [hlin, hlin, hlin, map_sub]
  have hd1 : (globalCoordinates n trivialCharacter (c - c₁)).1 = 0 := by
    rw [hsub]
    exact sub_eq_zero.mpr hP
  have hdi : InnerBoundary n trivialCharacter .line
      (globalCoordinates n trivialCharacter (c - c₁)).2 :=
    innerBoundary_restriction_of_exact (c - c₁) wd hwd .line
  let η : innerClasses n .line := ⟨_, hdi⟩
  have hη : η = 0 := by
    apply facePairing_left_nondegenerate n η
    intro a'
    have ha' : InnerBoundary n trivialCharacter .plane a'.val := a'.property
    have hct := TernaryPeriodPolynomials.constant_terms n hn a'.val ha'
    rcases hct with ⟨c', hc1', hc2'⟩
    have hep := exists_edgePrimitive_of_line_inner c' hc2'
    rcases hep with ⟨w', hw'⟩
    have hst := facePairingP_eq_facePairing_of_restrictions (c - c₁) c' wd w' hwd hw'
      0 ⟨_, hc2'⟩ η a' hd1.symm rfl rfl hc1'.symm
    rw [← hst]
    simp
  have h2 : (globalCoordinates n trivialCharacter (c - c₁)).2 = 0 := congrArg Subtype.val hη
  rw [hsub] at h2
  exact sub_eq_zero.mp h2

/-- **The constant-term map `T` (`ar:eq:constantterms`), as a linear map.** For `n ≥ 4` there is a
linear map `T` from the plane stratum cohomology to the line stratum cohomology such that every inner
plane class `ξ` is the plane restriction of a global class with zero flag restrictions whose line
restriction is `T ξ`. (As for `T^∨`, nothing is assumed about invertibility or an adjoint normalization;
that `T` is the line restriction of *every* such class is `graph_containment`.) -/
theorem exists_constant_term_map (hn : 4 ≤ n) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
        ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
          EdgeExactGlobal c ∧ globalCoordinates n trivialCharacter c = (ξ, T ξ) := by
  let ρ := rationalCoefficientComponent n trivialCharacter
  let coords : cocycles rationalLevel ρ →ₗ[ℂ] StratumH2 n trivialCharacter .line ×
      StratumH2 n trivialCharacter .plane :=
    (LinearMap.prod (LinearMap.snd ℂ _ _) (LinearMap.fst ℂ _ _)).comp
      (Dual.globalCoordinatesRepLinear ρ)
  obtain ⟨T, hT⟩ := Dual.exists_linear_selection coords
    (Dual.innerClassesRep ρ .plane) (Dual.innerClassesRep ρ .line) (fun ξ hξ => by
      obtain ⟨c, hc1, hc2⟩ := TernaryPeriodPolynomials.constant_terms n hn ξ hξ
      exact ⟨c, hc2, hc1⟩)
  refine ⟨T, fun ξ hξ => ?_⟩
  obtain ⟨_, c, hc⟩ := hT ξ hξ
  have hc' : globalCoordinates n trivialCharacter c = (ξ, T ξ) := by
    have h1 := congrArg Prod.snd hc
    have h2 := congrArg Prod.fst hc
    exact Prod.ext h1 h2
  refine ⟨c, ?_, hc'⟩
  have hline : InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 := by
    rw [hc']
    exact (hT ξ hξ).1
  exact exists_edgePrimitive_of_line_inner c hline

/-- **Graph containment (`ar:prop:graph`).** Let `n ≥ 4`. For the constant-term map `T`, a global class
with zero flag restrictions has line restriction `ξ_Q = T ξ_P`, `ξ_P` its plane restriction. -/
theorem graph_containment (hn : 4 ≤ n) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      (∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
        ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
          EdgeExactGlobal c ∧ globalCoordinates n trivialCharacter c = (ξ, T ξ)) ∧
      ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        EdgeExactGlobal c →
          (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1 := by
  obtain ⟨T, hT⟩ := exists_constant_term_map hn
  refine ⟨T, hT, fun c hc => ?_⟩
  obtain ⟨w, hw⟩ := hc
  have hξ : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 :=
    innerBoundary_restriction_of_exact c w hw .plane
  obtain ⟨c₁, hc₁, hc₁'⟩ := hT _ hξ
  have := graph_containment_pair hn c c₁ ⟨w, hw⟩ hc₁ (by rw [hc₁'])
  rw [this, hc₁']

end TernaryPeriodPolynomials.Argument.FacePairingFull
