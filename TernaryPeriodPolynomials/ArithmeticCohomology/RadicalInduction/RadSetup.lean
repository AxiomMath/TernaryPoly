module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.Orbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalCocycles
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EdgeNaturality

@[expose] public section


/-!
# Setup for the radical-level induction identity

Formalized by Claude Sonnet 5.5.

`WI ext Stab ρ = Fun(S/Stab, E)` with `(g F)(y) = ρ(g) F(g⁻¹ y)` as a representation of `S`; its restriction to the radical lattice is the induced representation of the radical lattice acting on
`YN ext Stab` (`resW_apply`, `resW_eq`).  `AS α ρ` is the representation `ρ ∘ α` of the sub-extension, `evT` the evaluation at the base point `y0` of `S/Stab`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction

variable {S L L' : Type} [Group S] [Group L] [Group L'] {ext : GroupExtension RadicalLattice S L} {s : ext.Splitting}
  {Stab : Subgroup S} {E₂ : Type} [Group E₂] {α : E₂ →* S} {ext' : GroupExtension RadicalLattice E₂ L'} {s' : ext'.Splitting} {ιL : L' →* L} {m0 : ℕ}
  {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']

instance (ext : GroupExtension RadicalLattice S L) (Stab : Subgroup S) : MulAction S (YN ext Stab) :=
  inferInstanceAs (MulAction S (S ⧸ Stab))

theorem smul_YN (g : S) (e : S) : g • YN.mk ext Stab e = YN.mk ext Stab (g * e) := rfl

/-- `Fun(S/Stab, E)` as a representation of `S`. -/
def WI (ext : GroupExtension RadicalLattice S L) (Stab : Subgroup S) (ρ : Representation ℂ S E) : Rep ℂ S :=
  Rep.of (indRepQ (Q := YN ext Stab) ρ)

theorem resW_apply (ρ : Representation ℂ S E) (a : RadicalLattice) (F : YN ext Stab → E) (y : YN ext Stab) :
    (Rep.res ext.inl (WI ext Stab ρ)).ρ a F y = ρ (ext.inl a) (F (a⁻¹ • y)) := by
  change ρ (ext.inl a) (F ((ext.inl a)⁻¹ • y)) = _
  have h : (ext.inl a)⁻¹ • y = a⁻¹ • y := by
    rw [← map_inv]; rfl
  rw [h]

theorem resW_eq (ρ : Representation ℂ S E) (a : RadicalLattice) (F : YN ext Stab → E) :
    (Rep.res ext.inl (WI ext Stab ρ)).ρ a F = indRepQ (Q := YN ext Stab) (ρ.comp ext.inl) a F := by
  funext y
  rw [resW_apply]
  rfl

/-- The base point `1 · Stab` of `S / Stab`. -/
def y0 (ext : GroupExtension RadicalLattice S L) (Stab : Subgroup S) : YN ext Stab := YN.mk ext Stab 1

theorem stab_smul_y0 {g : S} (hg : g ∈ Stab) : g • y0 ext Stab = y0 ext Stab := by
  show (QuotientGroup.mk (g * 1) : S ⧸ Stab) = QuotientGroup.mk 1
  rw [QuotientGroup.eq]
  simpa using Stab.inv_mem hg

/-- The representation of `E₂` on `E` through `α`. -/
abbrev AS (α : E₂ →* S) (ρ : Representation ℂ S E) : Rep ℂ E₂ := Rep.of (ρ.comp α)

/-- Evaluation at the base point. -/
def evT (ext : GroupExtension RadicalLattice S L) (Stab : Subgroup S) (α : E₂ →* S) (ρ : Representation ℂ S E) : WI ext Stab ρ →ₗ[ℂ] AS α ρ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : YN ext Stab => E) (y0 ext Stab)

theorem evT_apply (α : E₂ →* S) (ρ : Representation ℂ S E) (F : YN ext Stab → E) : evT ext Stab α ρ F = F (y0 ext Stab) := rfl

theorem evT_hT (α : E₂ →* S) (hα : ∀ g, α g ∈ Stab) (ρ : Representation ℂ S E) (g : E₂) (F : WI ext Stab ρ) :
    evT ext Stab α ρ ((WI ext Stab ρ).ρ (α g) F) = (AS α ρ).ρ g (evT ext Stab α ρ F) := by
  change ρ (α g) (F ((α g)⁻¹ • y0 ext Stab)) = ρ (α g) (F (y0 ext Stab))
  congr 2
  rw [inv_smul_eq_iff, stab_smul_y0 (hα g)]

end TernaryPeriodPolynomials.Argument.RadicalInduction
