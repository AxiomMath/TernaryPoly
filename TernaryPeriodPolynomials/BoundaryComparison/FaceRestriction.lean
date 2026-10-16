module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Isotropy
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar
public import TernaryPeriodPolynomials.BoundaryComparison.FaceRestriction.Cocycles

@[expose] public section


/-! Target: Lemma C.2 (`ar:lem:stokes`) of the paper, in the project's
boundary-building cochain model. The dual coefficient system `E*` is represented, as in
`TernaryPeriodPolynomials.Duality`, by `E` composed with the level-preserving involution
`dualInvolution` and the invariant apolar pairing `dualPairing`. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Lemma C.2 (Stokes).** Let `a = [c]` be a global class with zero restriction to every
complete flag (edge primitive `w`) and `b = [c']` any global class of the dual system. For any
primitives `γ_P`, `γ_Q` of the cup product `c ⌣ c'^φ` on plane and line flags, the face
pairings are the boundary classes of the edge cochains `w ⌣ c'^φ - γ_R ∘ endpoint`; their
signed sum `⟨r_P a, r_P b⟩_P + ⟨r_Q a, r_Q b⟩_Q` is exact in the boundary building. -/
theorem face_pairing_stokes (n : ℕ)
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (γP : (Fin 4 → RationalGL3) → Flags .plane → ℂ)
    (hγP : γP ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3)
    (hdγP : ∀ x P, differentialThreeRaw γP x P =
      dualPairing n (c.val.val ![x 0, x 1, x 2])
        (c'.val.val ![dualInvolution (x 2), dualInvolution (x 3), dualInvolution (x 4)]))
    (γQ : (Fin 4 → RationalGL3) → Flags .line → ℂ)
    (hγQ : γQ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3)
    (hdγQ : ∀ x F, differentialThreeRaw γQ x F =
      dualPairing n (c.val.val ![x 0, x 1, x 2])
        (c'.val.val ![dualInvolution (x 2), dualInvolution (x 3), dualInvolution (x 4)])) :
    BoundaryExact (fun x e =>
      (dualPairing n (w.val ![x 0, x 1] e)
          (c'.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]) -
        γP x (endpoint .plane e)) -
      (dualPairing n (w.val ![x 0, x 1] e)
          (c'.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]) -
        γQ x (endpoint .line e))) := by
  exact TernaryPeriodPolynomials.Argument.Classification.face_pairing_stokes
    n c c' w hw γP hγP hdγP γQ hγQ hdγQ

end TernaryPeriodPolynomials
