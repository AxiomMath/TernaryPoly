module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadSum
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EdgeNaturality

@[expose] public section


/-!
# The evaluation of a radical cocycle at a point of `S / Stab`, on the sublattice

Formalized by Claude Sonnet 5.5.

For a point `y` of `S/Stab` and a radical cocycle `c` with values in `Fun(S/Stab, E)`, `evAtCoc y c : r ↦ c(r^{m₀})(y)` is a radical cocycle of the sub-extension `Stab` with values in `E`.  The map
`acoc x c` of the edge naturality (`pullback along r ↦ r^{m₀}`, evaluation at the base point) applied to the Levi conjugate of `c` by `(out x)⁻¹` equals `ρ(s ℓ) ∘ evAtCoc (yBase x) c ∘ ψ_ℓ`
(`acoc_apply`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c

variable {S L L' : Type} [Group S] [Group L] [Group L'] {ext : GroupExtension RadicalLattice S L} {s : ext.Splitting}
  {Stab : Subgroup S} {E₂ : Type} [Group E₂] {α : E₂ →* S} {ext' : GroupExtension RadicalLattice E₂ L'} {s' : ext'.Splitting} {ιL : L' →* L} {m0 : ℕ}
  {Lsub : Subgroup L} {E : Type} [AddCommGroup E] [Module ℂ E]

variable (hc : Compat ext s Stab α ext' s' ιL m0) (ρ : Representation ℂ S E)

include hc in
theorem hinl_pow (r : RadicalLattice) : α (ext'.inl r) = ext.inl ((powMonoidHom m0 : RadicalLattice →* RadicalLattice) r) :=
  hc.inl_eq r

include hc in
/-- `evAtCoc`: the evaluation of a radical cocycle at `y` on the sublattice. -/
def evAtCoc (y : YN ext Stab) (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ))) :
    groupCohomology.cocycles₁ (Rep.res ext'.inl (AS α ρ)) :=
  ⟨fun r => cval ρ c (r ^ m0) y, by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro a b
    show cval ρ c ((a * b) ^ m0) y = ρ (α (ext'.inl a)) (cval ρ c (b ^ m0) y) + cval ρ c (a ^ m0) y
    rw [mul_pow, cocycleW ρ c (a ^ m0) (b ^ m0)]
    rw [Pi.add_apply, indRepQ_apply, inv_smul_eq_iff.mpr (pow_smul_fix hc a y).symm]
    rw [hc.inl_eq]
    rfl⟩

include hc in
theorem evAtCoc_apply (y : YN ext Stab) (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ))) (r : RadicalLattice) :
    (evAtCoc hc ρ y c).1 r = cval ρ c (r ^ m0) y := rfl

include hc in
/-- The pullback along `r ↦ r^{m₀}` composed with evaluation at the base point (the cocycle map of `EdgeNat.radH1Map`). -/
def pbCoc : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ)) →ₗ[ℂ] groupCohomology.cocycles₁ (Rep.res ext'.inl (AS α ρ)) :=
  oneCocyclePullback (Rep.res ext.inl (WI ext Stab ρ)) (Rep.res ext'.inl (AS α ρ)) (powMonoidHom m0) (evT ext Stab α ρ) (by
    intro r
    apply LinearMap.ext
    intro v
    exact (EdgeNat.hT_rad α (powMonoidHom m0) (hinl_pow hc) (WI ext Stab ρ) (AS α ρ) (evT ext Stab α ρ)
      (evT_hT α hc.mem_stab ρ) r v).symm)

include hc in
/-- **The cocycle map attached to the Levi coset `x`**: the Levi conjugate by `(out x)⁻¹`, then `pbCoc`. -/
def acoc (x : L ⧸ Lsub) : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ)) →ₗ[ℂ] groupCohomology.cocycles₁ (Rep.res ext'.inl (AS α ρ)) :=
  (pbCoc hc ρ).comp (splitRadicalCocycleAction s (WI ext Stab ρ) (Quotient.out x)⁻¹)

theorem yBase_eq (x : L ⧸ Lsub) : ((s (Quotient.out x)⁻¹ : S))⁻¹ • y0 ext Stab = yBase ext s Stab x := by
  rw [← map_inv, inv_inv]
  show (QuotientGroup.mk (s (Quotient.out x) * 1) : S ⧸ Stab) = QuotientGroup.mk (s (Quotient.out x))
  rw [mul_one]

include hc in
theorem acoc_apply (x : L ⧸ Lsub) (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ))) (r : RadicalLattice) :
    (acoc (s := s) (Lsub := Lsub) hc ρ x c).1 r =
      ρ (s (Quotient.out x)⁻¹) ((evAtCoc hc ρ (yBase ext s Stab x) c).1 (splitRadicalInput s (Quotient.out x)⁻¹ r)) := by
  have h1 : (acoc (s := s) (Lsub := Lsub) hc ρ x c).1 r =
      indRepQ (Q := YN ext Stab) ρ (s (Quotient.out x)⁻¹) (cval ρ c (splitRadicalInput s (Quotient.out x)⁻¹ (r ^ m0))) (y0 ext Stab) := rfl
  rw [h1, indRepQ_apply, yBase_eq, evAtCoc_apply, map_pow]

end TernaryPeriodPolynomials.Argument.RadicalInduction
