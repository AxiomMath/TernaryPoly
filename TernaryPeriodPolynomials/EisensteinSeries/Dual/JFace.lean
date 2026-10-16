module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.JExt
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalFacePairing
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EdgeNaturalityIso

@[expose] public section


open CategoryTheory groupCohomology
open scoped MatrixGroups

/-!
# `ȷ` as a morphism of the face extensions, and the transport of `H²`

Formalized by Claude Sonnet 5.5.

For a cusp `h` the line group `Γ_{h⁻¹Qh}` (`lineFaceExt N h`, `lineFaceSplitting N h`) and the plane group `Γ_{ȷ(h)⁻¹Pȷ(h)}` (`faceExt N (ȷ h)`,
`faceSplitting N (ȷ h)`) are conjugates of the standard extensions, and `ȷ` is a morphism of split extensions over `(τ, σ)` (`faceJ_inl`, `faceJ_split`).  With the coefficient comparison
`T = dualIso : E → E*` (`faceJ_hT`), the transport `EdgeNat.h2Map` of `H²` is `toLiteral ∘ facePullC` (`h2Map_faceJ`), bijective (`h2Map_faceJ_bijective`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinClass

/-- Generic: the transport of `H²` along `α` with coefficient comparison `T` is `mapId T` after the restriction `map α` (identity coefficients). -/
theorem h2Map_eq_mapId_comp {G₁ G₂ : Type} [Group G₁] [Group G₂] {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] (α : G₂ →* G₁) (ρ₁ : Representation ℂ G₁ V₁) (ρ₃ : Representation ℂ G₂ V₁)
    (hρ₃ : ∀ g, ρ₃ g = ρ₁ (α g)) (ρ₂ : Representation ℂ G₂ V₂) (T : V₁ →ₗ[ℂ] V₂)
    (hT : ∀ g v, T (ρ₁ (α g) v) = ρ₂ g (T v)) (hT' : ∀ g v, T (ρ₃ g v) = ρ₂ g (T v))
    (x : groupCohomology.H2 (Rep.of ρ₁)) :
    EdgeNat.h2Map α (Rep.of ρ₁) (Rep.of ρ₂) T hT x =
      mapId ρ₃ ρ₂ T hT' ((groupCohomology.map α (resMorK α ρ₃ ρ₁ hρ₃) 2).hom x) := by
  induction x using groupCohomology.H2_induction_on with
  | h z =>
    rw [EdgeNat.h2Map_π]
    unfold mapId
    rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply]
    congr 1

variable (N : ℕ) [NeZero N] (n : ℕ) (h : SL(3, ℤ))

/-- The restriction of `ȷ` to a homomorphism `Γ_{h⁻¹Qh} → Γ_{ȷ(h)⁻¹Pȷ(h)}`. -/
abbrev faceJ : gammaNQAt N h →* gammaNPAt N (jmath h) := jRestr (gammaNQAt N h) (gammaNPAt N (jmath h)) (jmath_Q_to_P h)

omit [NeZero N] in
theorem faceJ_bijective : Function.Bijective (faceJ N h) :=
  (jEquivFace (S := gammaNQAt N h) (S' := gammaNPAt N (jmath h)) (fun _ => jmath_mem_gammaNPAt_iff)).bijective

theorem faceJ_inl (r : RadicalLattice) :
    faceJ N h ((lineFaceExt N h).inl r) = (faceExt N (jmath h)).inl (tauRad r) := by
  apply Subtype.ext
  change jmath (h⁻¹ * (radEltQ N r) * h) = (jmath h)⁻¹ * radElt N (tauRad r) * jmath h
  rw [jmath_mul, jmath_mul, jmath_inv, jmath_radEltQ]

theorem faceJ_split (m : ↥(CongruenceSubgroup.Gamma N)) :
    faceJ N h (lineFaceSplitting N h m) = faceSplitting N (jmath h) (sigmaGamma N m) := by
  apply Subtype.ext
  change jmath (h⁻¹ * (blockDiagQ m.1) * h) = (jmath h)⁻¹ * blockDiag (sigmaSL m.1) * jmath h
  rw [jmath_mul, jmath_mul, jmath_inv, jmath_blockDiagQ]

/-- The coefficient comparison `T = dualIso : E → E*` from the plane face of `ȷ(h)` to the (literal dual) line face of `h`. -/
abbrev faceJT : (faceRep N (jmath h) n) →ₗ[ℂ] (lineFaceRepLit N n h) := (dualIso n).toLinearMap

omit [NeZero N] in
theorem faceJ_hT (g : gammaNQAt N h) (v : faceRep N (jmath h) n) :
    faceJT N n h ((faceRep N (jmath h) n).ρ (faceJ N h g) v) = (lineFaceRepLit N n h).ρ g (faceJT N n h v) :=
  dualIso_equivariant_G N n (Subgroup.inclusion (gammaNQAt_le_N N h) g) v

omit [NeZero N] in
/-- **The transport of `H²` along `ȷ` is `toLiteral ∘ facePullC`.** -/
theorem h2Map_faceJ (x : groupCohomology.H2 (faceRep N (jmath h) n)) :
    EdgeNat.h2Map (faceJ N h) (faceRep N (jmath h) n) (lineFaceRepLit N n h) (faceJT N n h) (faceJ_hT N n h) x =
      toLiteral (gammaNQAt N h) (gammaNQAt_le_N N h) n
        (facePullC (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n x) :=
  h2Map_eq_mapId_comp (faceJ N h) (faceRep N (jmath h) n).ρ ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))
    (fun _ => rfl) (lineFaceRepLit N n h).ρ (faceJT N n h) (faceJ_hT N n h)
    (fun s v => dualIso_equivariant_G N n (Subgroup.inclusion (gammaNQAt_le_N N h) s) v) x

omit [NeZero N] in
theorem h2Map_faceJ_bijective : Function.Bijective
    (EdgeNat.h2Map (faceJ N h) (faceRep N (jmath h) n) (lineFaceRepLit N n h) (faceJT N n h) (faceJ_hT N n h)) :=
  ⟨EdgeNat.h2Map_injective _ _ _ _ _ (faceJ_bijective N h) (dualIso n).bijective,
    EdgeNat.h2Map_surjective _ _ _ _ _ (faceJ_bijective N h) (dualIso n).bijective⟩

end TernaryPeriodPolynomials.Argument.EisensteinDual
