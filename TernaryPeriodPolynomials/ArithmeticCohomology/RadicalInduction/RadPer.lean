module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadAco

@[expose] public section


/-!
# The radical identity: the Koszul value of induced cocycles is the sum over the Levi cosets

Formalized by Claude Sonnet 5.5.

**`phiC_ind`**: for `Stab ≤ S` a split sub-extension (`Compat`) of finite index with radical `m₀ℤ²` (so radical index `m₀²`), `W = Fun(S/Stab, E)`, `W' = Fun(S/Stab, E')` and radical cocycles `c, c'`,
`PhiC_W(c, c') = ∑_{x ∈ L/L'} PhiC_E(acoc x c, acoc x c')` with exactly the scalar `1`: the factor `m₀²` of the transformation `altForm_gen` of the Koszul form under the passage to the sublattice cancels
the orbit size `m₀²` of the radical lattice on `S/Stab`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c

variable {S L L' : Type} [Group S] [Group L] [Group L'] {ext : GroupExtension RadicalLattice S L} {s : ext.Splitting}
  {Stab : Subgroup S} {E₂ : Type} [Group E₂] {α : E₂ →* S} {ext' : GroupExtension RadicalLattice E₂ L'} {s' : ext'.Splitting} {ιL : L' →* L} {m0 : ℕ}
  {Lsub : Subgroup L} {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']

variable (hc : Compat ext s Stab α ext' s' ιL m0) (ρ : Representation ℂ S E) (ρ' : Representation ℂ S E') (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ)
  (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b)

include hc he in
theorem phiC_acoc (x : L ⧸ Lsub) (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ)))
    (c' : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ'))) :
    PhiC (Rep.res ext'.inl (AS α ρ)) (Rep.res ext'.inl (AS α ρ')) e
        (acoc (s := s) (Lsub := Lsub) hc ρ x c) (acoc (s := s) (Lsub := Lsub) hc ρ' x c') =
      PhiC (Rep.res ext'.inl (AS α ρ)) (Rep.res ext'.inl (AS α ρ')) e
        (evAtCoc hc ρ (yBase ext s Stab x) c) (evAtCoc hc ρ' (yBase ext s Stab x) c') := by
  have hS' : ∀ (r : RadicalLattice) (b : E'), (Rep.res ext'.inl (AS α ρ')).ρ r (ρ' (s (Quotient.out x)⁻¹) b) =
      ρ' (s (Quotient.out x)⁻¹) ((Rep.res ext'.inl (AS α ρ')).ρ (splitRadicalInput s (Quotient.out x)⁻¹ r) b) := by
    intro r b
    change ρ' (α (ext'.inl r)) (ρ' (s (Quotient.out x)⁻¹) b) =
      ρ' (s (Quotient.out x)⁻¹) (ρ' (α (ext'.inl (splitRadicalInput s (Quotient.out x)⁻¹ r))) b)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hc.inl_eq, hc.inl_eq,
      ← map_pow (splitRadicalInput s (Quotient.out x)⁻¹), splitRadicalInput_commute]
  have key := PhiC_pullback (A := Rep.res ext'.inl (AS α ρ)) (A' := Rep.res ext'.inl (AS α ρ')) (e := e)
    (fun g a b => he _ a b) (splitRadicalInput s (Quotient.out x)⁻¹) (ρ (s (Quotient.out x)⁻¹)) (ρ' (s (Quotient.out x)⁻¹))
    hS' (fun a b => he _ a b) (evAtCoc hc ρ (yBase ext s Stab x) c) (acoc (s := s) (Lsub := Lsub) hc ρ x c)
    (evAtCoc hc ρ' (yBase ext s Stab x) c') (acoc (s := s) (Lsub := Lsub) hc ρ' x c')
    (fun r => acoc_apply hc ρ x c r) (fun r => acoc_apply hc ρ' x c' r)
  rw [key, hc.det]
  simp

include hc in
theorem phiC_evAtCoc (y : YN ext Stab) (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ)))
    (c' : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ'))) :
    PhiC (Rep.res ext'.inl (AS α ρ)) (Rep.res ext'.inl (AS α ρ')) e (evAtCoc hc ρ y c) (evAtCoc hc ρ' y c') =
      APx (ρ'.comp ext.inl) e (rl1 ^ m0) (rl2 ^ m0) (cval ρ c) (cval ρ' c') y := by
  rw [PhiC_apply]
  unfold APx AP
  change e (cval ρ c (rl1 ^ m0) y) (ρ' (α (ext'.inl rl1)) (cval ρ' c' (rl2 ^ m0) y)) -
      e (cval ρ c (rl2 ^ m0) y) (ρ' (α (ext'.inl rl2)) (cval ρ' c' (rl1 ^ m0) y)) = _
  rw [hc.inl_eq, hc.inl_eq]
  rfl

section Ind

variable (hr : ιL.range = Lsub) [NeZero m0] [Fintype (YN ext Stab)] [Fintype (L ⧸ Lsub)]

include hc he hr in
/-- **The radical identity** (scalar exactly `1`): the Koszul pairing of cocycles with values in `Fun(S/Stab, E)` is the sum over the Levi cosets of the Koszul pairings of the pulled-back evaluated cocycles. -/
theorem phiC_ind (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ)))
    (c' : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ'))) :
    PhiC (Rep.res ext.inl (WI ext Stab ρ)) (Rep.res ext.inl (WI ext Stab ρ')) (eW ρ ρ' e) c c' =
      ∑ x : L ⧸ Lsub, PhiC (Rep.res ext'.inl (AS α ρ)) (Rep.res ext'.inl (AS α ρ')) e
        (acoc (s := s) (Lsub := Lsub) hc ρ x c) (acoc (s := s) (Lsub := Lsub) hc ρ' x c') := by
  rw [phiC_W_sum ρ ρ' e hc hr he c c']
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [phiC_acoc hc ρ ρ' e he x c c', phiC_evAtCoc hc ρ ρ' e]

end Ind

end TernaryPeriodPolynomials.Argument.RadicalInduction
