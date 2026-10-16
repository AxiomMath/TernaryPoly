module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel

@[expose] public section


/-!
# Transport of cochains along the level-preserving involution

`dualInvolution` (`φ(g) = a (g⁻¹)ᵀ a⁻¹`) preserves the arithmetic level and swaps the line and
plane parabolics up to the long Weyl element (`dualFlag`, `dualPlaneFlag`, `dualEdge`). Given a
representation `ρ` of `GL₃(ℚ)` and `ρ' = ρ ∘ φ` (the dual coefficient system `E*`, up to the
fixed change of coordinates of the paper), pulling a cochain back along `φ` and along a
`φ`-equivariant map of flag varieties `m : X' → X` is a linear map
`cochains Γ (functionRepresentation ρ X) k → cochains Γ (functionRepresentation ρ' X') k`
(`transportCochains`) commuting with the differentials. It is the cochain-level form of the
paper's "apply the construction to `ȷ(Γ)` and pull back".

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem phi_vec2 (a b : RationalGL3) :
    (fun i => dualInvolution ((![a, b] : Fin 2 → RationalGL3) i)) =
      ![dualInvolution a, dualInvolution b] := by
  funext i
  fin_cases i <;> rfl

theorem phi_vec3 (a b c : RationalGL3) :
    (fun i => dualInvolution ((![a, b, c] : Fin 3 → RationalGL3) i)) =
      ![dualInvolution a, dualInvolution b, dualInvolution c] := by
  funext i
  fin_cases i <;> rfl

theorem phi_vec4 (a b c d : RationalGL3) :
    (fun i => dualInvolution ((![a, b, c, d] : Fin 4 → RationalGL3) i)) =
      ![dualInvolution a, dualInvolution b, dualInvolution c, dualInvolution d] := by
  funext i
  fin_cases i <;> rfl

section Transport

variable {X X' : Type} [MulAction RationalGL3 X] [MulAction RationalGL3 X']
  (ρ ρ' : Representation ℂ RationalGL3 V) (hρ : ∀ g, ρ' g = ρ (dualInvolution g))
  (m : X' → X) (hm : ∀ (g : RationalGL3) F, m (g • F) = dualInvolution g • m F)

/-- Pullback of a cochain along `φ` on the vertices and along `m` on the flags. -/
def transportCochains (k : ℕ) :
    cochains rationalLevel (functionRepresentation ρ X) k →ₗ[ℂ]
      cochains rationalLevel (functionRepresentation ρ' X') k where
  toFun f := ⟨fun x F' => f.val (fun i => dualInvolution (x i)) (m F'), by
    intro γ x
    funext F'
    have hlevel : dualInvolution γ.val ∈ rationalLevel := dualInvolution_mem_rationalLevel γ.property
    have hf := congrFun (f.property ⟨dualInvolution γ.val, hlevel⟩
      (fun i => dualInvolution (x i))) (m F')
    have hv : (fun i => dualInvolution (γ.val * x i)) =
        fun i => dualInvolution γ.val * dualInvolution (x i) := by
      funext i
      exact map_mul dualInvolution _ _
    change f.val (fun i => dualInvolution (γ.val * x i)) (m F') =
      ρ' γ.val (f.val (fun i => dualInvolution (x i)) (m (γ.val⁻¹ • F')))
    rw [hv, hρ γ.val, hm, map_inv]
    exact hf⟩
  map_add' f g := rfl
  map_smul' c f := rfl

theorem transportCochains_differentialOne
    (f : cochains rationalLevel (functionRepresentation ρ X) 1) :
    transportCochains ρ ρ' hρ m hm 2 (differentialOne rationalLevel (functionRepresentation ρ X) f) =
      differentialOne rationalLevel (functionRepresentation ρ' X')
        (transportCochains ρ ρ' hρ m hm 1 f) := by
  apply Subtype.ext
  funext x F'
  change f.val ![dualInvolution (x 1), dualInvolution (x 2)] (m F') -
      f.val ![dualInvolution (x 0), dualInvolution (x 2)] (m F') +
      f.val ![dualInvolution (x 0), dualInvolution (x 1)] (m F') =
    f.val (fun i => dualInvolution (![x 1, x 2] i)) (m F') -
      f.val (fun i => dualInvolution (![x 0, x 2] i)) (m F') +
      f.val (fun i => dualInvolution (![x 0, x 1] i)) (m F')
  rw [phi_vec2, phi_vec2, phi_vec2]

/-- The transport of a two-cocycle is a two-cocycle. -/
def transportCocycles :
    cocycles rationalLevel (functionRepresentation ρ X) →ₗ[ℂ]
      cocycles rationalLevel (functionRepresentation ρ' X') where
  toFun f := ⟨transportCochains ρ ρ' hρ m hm 2 f.val, by
    funext x F'
    have h := congrFun (congrFun f.property (fun i => dualInvolution (x i))) (m F')
    change f.val.val (fun i => dualInvolution ((![x 1, x 2, x 3] : Fin 3 → RationalGL3) i)) (m F') -
        f.val.val (fun i => dualInvolution ((![x 0, x 2, x 3] : Fin 3 → RationalGL3) i)) (m F') +
        f.val.val (fun i => dualInvolution ((![x 0, x 1, x 3] : Fin 3 → RationalGL3) i)) (m F') -
        f.val.val (fun i => dualInvolution ((![x 0, x 1, x 2] : Fin 3 → RationalGL3) i)) (m F') = 0
    rw [phi_vec3, phi_vec3, phi_vec3, phi_vec3]
    exact h⟩
  map_add' f g := rfl
  map_smul' c f := rfl

theorem transportCocycles_boundaryMap (f : cochains rationalLevel (functionRepresentation ρ X) 1) :
    transportCocycles ρ ρ' hρ m hm
        (boundaryMap rationalLevel (functionRepresentation ρ X) f) =
      boundaryMap rationalLevel (functionRepresentation ρ' X')
        (transportCochains ρ ρ' hρ m hm 1 f) :=
  Subtype.ext (transportCochains_differentialOne ρ ρ' hρ m hm f)

end Transport

end TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
