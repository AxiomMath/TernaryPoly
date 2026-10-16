module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StokesPairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingNondegenerate
public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction.EndpointPull
public import TernaryPeriodPolynomials.BoundaryComparison.ConstantTerms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.GraphPieces.BoundaryExactness
open TernaryPeriodPolynomials.Argument.Classification

/-!
# The left kernel of `⟨ , ⟩_P` and the constant-term map (conditional intermediate)

By Stokes (`facePairingP_global_eq_facePairing_global`), perfectness of `⟨ , ⟩_Q` (all `n`) and the
constant-term theorem (`n ≥ 4`), an inner plane class pairing to zero with every inner line class under
`⟨ , ⟩_P` is the plane restriction of a global class with inner restrictions and ZERO line restriction
(`facePairingP_left_kernel_eq_global`). Hence `⟨ , ⟩_P` has zero left kernel as soon as the constant-term
map is injective (`facePairingP_left_nondegenerate_of_injective`, a labelled CONDITIONAL result: the
hypothesis is the functional-equation content and is not proved here).

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

variable {n : ℕ}

/-- If the line coordinate of a global cocycle is inner, the cocycle is exact on complete flags. -/
theorem exists_edgePrimitive_of_line_inner
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (h : InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2) :
    ∃ w : EdgeCochains n trivialCharacter 1,
      ∀ x e, c.val.val x = differentialOneRaw w.val x e := by
  have h0 := endpointPullH2_eq_zero_of_innerBoundary n trivialCharacter .line _ h
  have h1 : endpointPullH2 n trivialCharacter .line
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
        (restrictionCocycle n trivialCharacter .line c)) = 0 := h0
  rw [endpointPullH2_realizes] at h1
  have hobtain1 := (Submodule.Quotient.mk_eq_zero _).mp h1
  obtain ⟨u, hu⟩ := hobtain1
  refine ⟨u, fun x e => ?_⟩
  have := congrArg (fun m => m.val.val x e) hu
  exact this.symm


/-- Stokes for arbitrary subtype representatives of the restrictions. -/
theorem facePairingP_eq_facePairing_of_restrictions
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w w' : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (hw' : ∀ x e, c'.val.val x = differentialOneRaw w'.val x e)
    (a : innerClasses n .plane) (b' : innerClasses n .line)
    (η : innerClasses n .line) (a' : innerClasses n .plane)
    (ha : a.val = (globalCoordinates n trivialCharacter c).1)
    (hb : b'.val = (globalCoordinates n trivialCharacter c').2)
    (hη : η.val = (globalCoordinates n trivialCharacter c).2)
    (ha' : a'.val = (globalCoordinates n trivialCharacter c').1) :
    Plane.facePairingP n a b' = facePairing n η a' := by
  obtain ⟨av, pa⟩ := a
  obtain ⟨bv, pb⟩ := b'
  obtain ⟨ηv, pη⟩ := η
  obtain ⟨av', pa'⟩ := a'
  change av = _ at ha
  change bv = _ at hb
  change ηv = _ at hη
  change av' = _ at ha'
  subst ha hb hη ha'
  exact facePairingP_global_eq_facePairing_global c c' w w' hw hw'

/-- **Left kernel of `⟨,⟩_P` lies in the kernel of the constant-term map (`n ≥ 4`).** If an inner
plane class pairs to zero with every inner line class under `⟨,⟩_P`, it is the plane restriction
of a global class whose line restriction is zero (and whose restrictions are inner). -/
theorem facePairingP_left_kernel_eq_global (hn : 4 ≤ n) (ξ : innerClasses n .plane)
    (h : ∀ b : innerClasses n .line, Plane.facePairingP n ξ b = 0) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      (globalCoordinates n trivialCharacter c).1 = ξ.val ∧
      (globalCoordinates n trivialCharacter c).2 = 0 := by
  have hξi : InnerBoundary n trivialCharacter .plane ξ.val := ξ.property
  have hobtain2 := TernaryPeriodPolynomials.constant_terms n hn ξ.val hξi
  obtain ⟨c, hc1, hc2⟩ := hobtain2
  refine ⟨c, hc1, ?_⟩
  have hobtain3 := exists_edgePrimitive_of_line_inner c hc2
  obtain ⟨w, hw⟩ := hobtain3
  obtain ⟨η, hηdef⟩ : ∃ η : innerClasses n .line,
      η.val = (globalCoordinates n trivialCharacter c).2 := ⟨⟨_, hc2⟩, rfl⟩
  have hη : η = 0 := by
    apply facePairing_left_nondegenerate n η
    intro ξ'
    have hξi' : InnerBoundary n trivialCharacter .plane ξ'.val := ξ'.property
    have hobtain4 := TernaryPeriodPolynomials.constant_terms n hn ξ'.val hξi'
    obtain ⟨c', hc1', hc2'⟩ := hobtain4
    have hobtain5 := exists_edgePrimitive_of_line_inner c' hc2'
    obtain ⟨w', hw'⟩ := hobtain5
    have hst := facePairingP_eq_facePairing_of_restrictions c c' w w' hw hw' ξ
      ⟨_, hc2'⟩ η ξ' hc1.symm rfl hηdef hc1'.symm
    rw [← hst]
    exact h _
  rw [← hηdef, hη]
  rfl

/-- **`⟨,⟩_P` has zero left kernel if the constant-term map is injective (`n ≥ 4`).** The hypothesis
`hT` says that a global class with inner restrictions and zero line restriction has zero plane
restriction (injectivity of `T`, the functional-equation content). -/
theorem facePairingP_left_nondegenerate_of_injective (hn : 4 ≤ n)
    (hT : ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 →
      (globalCoordinates n trivialCharacter c).2 = 0 →
        (globalCoordinates n trivialCharacter c).1 = 0)
    (ξ : innerClasses n .plane)
    (h : ∀ b : innerClasses n .line, Plane.facePairingP n ξ b = 0) : ξ = 0 := by
  have hobtain6 := facePairingP_left_kernel_eq_global hn ξ h
  obtain ⟨c, hc1, hc2⟩ := hobtain6
  have hξi : InnerBoundary n trivialCharacter .plane ξ.val := ξ.property
  exact Subtype.ext (hc1.symm.trans (hT c (hc1 ▸ hξi) hc2))

end TernaryPeriodPolynomials.Argument.FacePairingFull
