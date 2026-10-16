module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentCochain

@[expose] public section


/-!
# The Levi identity for the relative representative on an arbitrary stabilizer

`ParabolicDualityIdentCochain` proves the identity between the mixed radical value of the relative
representative and the Levi cocycle at `k⁻¹` for the good-line stabilizer.  Here the same algebra is
proved for an arbitrary subgroup `Γ` of `GL₃(ℚ)` and an arbitrary pair of radical elements, which is
what the identity-plane edge needs (and, later, the bad line and the good plane).

For `ω` an equivariant primitive of a cocycle `ζ` over a subgroup `U`, `k` an element with
`k U k⁻¹ ⊆ U` fixing `ζ`, and `u k = k u''` with `u, u'' ∈ U`:

  `[ω(k, k u'') - ρ(k) ω(1, u'')] - [ω(u, u k) - ρ(u) ω(1, k)] + A(k⁻¹)(1, u) = (ρ(u) - 1)(-w)`,

with `A(h) = h ⋆ ω - ω` the Levi cocycle and `w = ρ(k) A(k)(1, k⁻¹)` (`levi_identity`).  The bracketed
expressions are the values of the relative representative `relCocycleOn` of the ambient cocycle
(`relCocycleOn_apply`), which vanishes on radical first arguments (`relCocycleOn_vanish`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
  (pull1 leviCocycle leviCocycle_inv leviCocycle_equivariant leviCocycle_closed)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant (pull1_lattice)

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

section Core

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- **The relative representative on a subgroup `Γ`**: the ambient two-cocycle of `C` minus the
boundary of `g ↦ ω(1, g)`. -/
def relCocycleOn (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (ω : (Fin 2 → RationalGL3) → V) (C : cocycles Γ ρ) :
    groupCohomology.cocycles₂ (subgroupCoefficientRep Γ ρ) :=
  ambientCocycleToGroup Γ ρ C -
    twoBoundaryCycle (subgroupCoefficientRep Γ ρ) (fun g : Γ => ω ![1, g.val])

/-- The value of the relative representative on a pair. -/
theorem relCocycleOn_apply (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (ω : (Fin 2 → RationalGL3) → V) (C : cocycles Γ ρ)
    (hd : ∀ a b c, differentialOneRaw ω ![a, b, c] = C.val.val ![a, b, c]) (g h : Γ) :
    relCocycleOn Γ ρ ω C (g, h) = ω ![g.val, g.val * h.val] - ρ g.val (ω ![1, h.val]) := by
  have h1 : ω ![g.val, g.val * h.val] - ω ![1, g.val * h.val] + ω ![1, g.val] =
      C.val.val ![1, g.val, g.val * h.val] := hd 1 g.val (g.val * h.val)
  change C.val.val ![1, g.val, g.val * h.val] -
      (ρ g.val (ω ![1, h.val]) - ω ![1, g.val * h.val] + ω ![1, g.val]) = _
  rw [← h1]
  abel

/-- The relative representative vanishes when the first argument lies in the subgroup `U` over
which `ω` is equivariant. -/
theorem relCocycleOn_vanish (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (ω : (Fin 2 → RationalGL3) → V) (C : cocycles Γ ρ)
    (hd : ∀ a b c, differentialOneRaw ω ![a, b, c] = C.val.val ![a, b, c])
    {U : Subgroup RationalGL3} (hω : ∀ g ∈ U, ∀ a b, ω ![g * a, g * b] = ρ g (ω ![a, b]))
    {g h : Γ} (hg : g.val ∈ U) : relCocycleOn Γ ρ ω C (g, h) = 0 := by
  rw [relCocycleOn_apply Γ ρ ω C hd]
  have h1 := hω g.val hg 1 h.val
  rw [mul_one] at h1
  rw [h1]
  exact sub_self _

/-- **The relative two-cocycle** attached to `C` and `ω` for a homomorphism `ι` into `Γ` whose
image lies in `U`. -/
def relOn (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (ω : (Fin 2 → RationalGL3) → V) (C : cocycles Γ ρ)
    (hd : ∀ a b c, differentialOneRaw ω ![a, b, c] = C.val.val ![a, b, c])
    {U : Subgroup RationalGL3} (hω : ∀ g ∈ U, ∀ a b, ω ![g * a, g * b] = ρ g (ω ![a, b]))
    {N : Type} [Group N] (ι : N →* Γ) (hι : ∀ p, (ι p).val ∈ U) :
    relativeTwoCocycles ι (subgroupCoefficientRep Γ ρ) :=
  ⟨relCocycleOn Γ ρ ω C, fun p _ => relCocycleOn_vanish Γ ρ ω C hd hω (hι p)⟩

/-- The relative representative has the class of the ambient two-cocycle. -/
theorem relOn_H2 (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (ω : (Fin 2 → RationalGL3) → V) (C : cocycles Γ ρ)
    (hd : ∀ a b c, differentialOneRaw ω ![a, b, c] = C.val.val ![a, b, c])
    {U : Subgroup RationalGL3} (hω : ∀ g ∈ U, ∀ a b, ω ![g * a, g * b] = ρ g (ω ![a, b]))
    {N : Type} [Group N] (ι : N →* Γ) (hι : ∀ p, (ι p).val ∈ U) :
    groupCohomology.H2π (subgroupCoefficientRep Γ ρ) (relOn Γ ρ ω C hd hω ι hι).val =
      groupCohomology.H2π (subgroupCoefficientRep Γ ρ) (ambientCocycleToGroup Γ ρ C) := by
  change groupCohomology.H2π (subgroupCoefficientRep Γ ρ)
    (ambientCocycleToGroup Γ ρ C -
      twoBoundaryCycle (subgroupCoefficientRep Γ ρ) (fun g : Γ => ω ![1, g.val])) = _
  rw [map_sub]
  exact sub_eq_self.mpr (twoBoundaryCycle_H2_zero _ _)

/-- **The Levi identity.**  See the module documentation. -/
theorem levi_identity (ρ : Representation ℂ RationalGL3 V) (ω : (Fin 2 → RationalGL3) → V)
    (ζ : (Fin 3 → RationalGL3) → V)
    (hd : ∀ a b c, differentialOneRaw ω ![a, b, c] = ζ ![a, b, c]) {U : Subgroup RationalGL3}
    (hω : ∀ g ∈ U, ∀ a b, ω ![g * a, g * b] = ρ g (ω ![a, b])) {k : RationalGL3}
    (hζ : ∀ a b c, ζ ![k * a, k * b, k * c] = ρ k (ζ ![a, b, c]))
    (hn : ∀ u ∈ U, k * u * k⁻¹ ∈ U) {u u'' : RationalGL3} (hu : u ∈ U) (hu'' : u'' ∈ U)
    (hconj : u * k = k * u'') :
    ((ω ![k, k * u''] - ρ k (ω ![1, u''])) - (ω ![u, u * k] - ρ u (ω ![1, k]))) +
        leviCocycle ρ ω k⁻¹ ![1, u] =
      ρ u (-(ρ k (leviCocycle ρ ω k ![1, k⁻¹]))) - (-(ρ k (leviCocycle ρ ω k ![1, k⁻¹]))) := by
  have hA : UCocycle ρ U (leviCocycle ρ ω k) :=
    ⟨leviCocycle_equivariant ρ hω hn, leviCocycle_closed ρ hd hζ⟩
  have hP := pull1_lattice ρ hA k u u'' hu'' hconj
  have hinv : leviCocycle ρ ω k⁻¹ ![1, u] = -(pull1 ρ k⁻¹ (leviCocycle ρ ω k) ![1, u]) :=
    congrFun (leviCocycle_inv ρ ω k) ![1, u]
  have hr1 : ω ![k, k * u''] - ρ k (ω ![1, u'']) = ρ k (leviCocycle ρ ω k ![1, u'']) := by
    have h := rho_leviCocycle_apply ρ ω k 1 u''
    rw [mul_one] at h
    exact h.symm
  have hr2 : ω ![u, u * k] - ρ u (ω ![1, k]) = 0 := by
    have h := hω u hu 1 k
    rw [mul_one] at h
    rw [h, sub_self]
  rw [hr1, hr2, sub_zero, hinv, hP, map_neg]
  abel

end Core

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

end
