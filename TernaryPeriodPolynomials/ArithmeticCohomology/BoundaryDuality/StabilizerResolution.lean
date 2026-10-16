module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.FlagShapiro
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TracePairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Vanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Transfer

@[expose] public section


/-!
# `H⁴` of the stabilizers from a free resolution of the level

A free resolution of `ℂ` by permutation modules over a group restricts to a free resolution over
every subgroup (along an injective homomorphism the actions stay free). So a free resolution of
length three over a subgroup `Γ'` of finite index in the arithmetic level gives `H⁴ = 0` for
`Γ' ∩ Γ_y` and, by transfer, for the stabilizer `Γ_y` of every point of every `GL₃(ℚ)`-set. In
particular the free resolution that gives `H⁴(Γ, ℂ) = 0` also gives the vertex primitives of the
twisted cup products on lines (`lineCupExact_of_freeResolution`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.StabilizerResolution

open TernaryPeriodPolynomials.TopVanishing
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TracePairing
open TernaryPeriodPolynomials.BoundaryDuality.FlagShapiro

/-- The restriction of a free resolution along an injective homomorphism: the same cells and
boundaries, with the action pulled back. -/
def restrictResolution {Λ Λ' : Type} [Group Λ] [Group Λ'] {N : ℕ} (X : FreeResolution Λ' N)
    (φ : Λ →* Λ') (hφ : Function.Injective φ) : FreeResolution Λ N where
  cell := X.cell
  action := fun k => MulAction.compHom (X.cell k) φ
  d := X.d
  equivariant := fun k γ => X.equivariant k (φ γ)
  d_comp_d := X.d_comp_d
  point := X.point
  free := fun k γ s h => hφ ((X.free k (φ γ) s h).trans (map_one φ).symm)
  exact := X.exact
  top := X.top

/-- `H⁴` of the stabilizer of any point vanishes, given a free resolution of length three over a
finite-index subgroup of the level. -/
theorem topVanishing_pointStabilizer {Γ' : Subgroup RationalGL3}
    (hindex : Γ'.relIndex rationalLevel ≠ 0) (X : FreeResolution Γ' 3) {Y : Type}
    [MulAction RationalGL3 Y] (y : Y) : IsTopVanishing (pointStabilizer y) := by
  have hS : pointStabilizer y ≤ rationalLevel := inf_le_left
  have hle' : Γ' ⊓ pointStabilizer y ≤ Γ' := inf_le_left
  have hres : IsTopVanishing (Γ' ⊓ pointStabilizer y) :=
    topVanishing_of_freeResolution
      (restrictResolution X (Subgroup.inclusion hle') (Subgroup.inclusion_injective hle'))
  refine IsTopVanishing.of_le_of_relIndex inf_le_right ?_ hres
  rw [Subgroup.inf_relIndex_right]
  exact fun h => hindex (Subgroup.relIndex_eq_zero_of_le_right hS h)

/-- **Vertex primitives from the free resolution of the level.** The free resolution that gives
`H⁴(Γ, ℂ) = 0` also makes every twisted cup product of a line and a plane two-cocycle exact on
lines. -/
theorem lineCupExact_of_freeResolution {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)
    {Γ' : Subgroup RationalGL3} (hindex : Γ'.relIndex rationalLevel ≠ 0)
    (X : FreeResolution Γ' 3) : LineCupExact T :=
  fun z y => lineCupExact_of_topVanishing T
    (fun F => topVanishing_pointStabilizer hindex X F) z y

end TernaryPeriodPolynomials.BoundaryDuality.StabilizerResolution
