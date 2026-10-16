module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadSetup

@[expose] public section


/-!
# The Koszul value of a radical cocycle with values in `Fun(S / Stab, E)` as a sum over the Levi cosets

Formalized by Claude Sonnet 5.5.

For crossed homomorphisms `c, c'` of the radical lattice `N` with values in `Fun(S/Stab, E)`, `Fun(S/Stab, E')`, the Koszul value `PhiC(c, c')` is the sum, over the Levi cosets `x ∈ L / L'`, of the
Koszul values `APx` of the evaluations of `c, c'` at the base points `yBase x` on the generators `rl₁^{m₀}, rl₂^{m₀}` of the sublattice (`phiC_W_sum`).  The factor `m₀²` of `altForm_gen` cancels
against the orbit size `m₀²` of `sum_orbits`: the scalar is exactly `1`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction

variable {S L L' : Type} [Group S] [Group L] [Group L'] {ext : GroupExtension RadicalLattice S L} {s : ext.Splitting}
  {Stab : Subgroup S} {E₂ : Type} [Group E₂] {α : E₂ →* S} {ext' : GroupExtension RadicalLattice E₂ L'} {s' : ext'.Splitting} {ιL : L' →* L} {m0 : ℕ}
  {Lsub : Subgroup L} {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']

theorem pow_smul_fix (hc : Compat ext s Stab α ext' s' ιL m0) (r : RadicalLattice) (y : YN ext Stab) : (r ^ m0) • y = y := by
  induction y using QuotientGroup.induction_on with
  | H e =>
    show (QuotientGroup.mk (ext.inl (r ^ m0) * e) : S ⧸ Stab) = QuotientGroup.mk e
    rw [QuotientGroup.eq]
    have h := conj_pow_mem hc e r⁻¹
    have e1 : (ext.inl (r ^ m0) * e)⁻¹ * e = e⁻¹ * ext.inl ((r⁻¹) ^ m0) * e := by
      rw [inv_pow, map_inv]; group
    rw [e1]
    exact h

section Cocycle

variable (ρ : Representation ℂ S E) (ρ' : Representation ℂ S E') (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ)

/-- The values of a radical cocycle with values in `Fun(S/Stab, E)`, as functions. -/
def cval (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ))) : RadicalLattice → (YN ext Stab → E) := c.1

/-- The summed pairing on the restrictions to the radical lattice. -/
def eW [Fintype (YN ext Stab)] : Rep.res ext.inl (WI ext Stab ρ) →ₗ[ℂ] Rep.res ext.inl (WI ext Stab ρ') →ₗ[ℂ] ℂ := eindQ e

theorem cocycleW (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ))) (a b : RadicalLattice) :
    cval ρ c (a * b) = indRepQ (Q := YN ext Stab) (ρ.comp ext.inl) a (cval ρ c b) + cval ρ c a := by
  have h := (groupCohomology.mem_cocycles₁_iff c.1).1 c.2 a b
  have h2 := resW_eq (ext := ext) (Stab := Stab) ρ a (cval ρ c b)
  exact h.trans (congrArg (· + cval ρ c a) h2)

theorem phiC_W_eq (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ)))
    (c' : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ'))) [Fintype (YN ext Stab)] :
    PhiC (Rep.res ext.inl (WI ext Stab ρ)) (Rep.res ext.inl (WI ext Stab ρ')) (eW ρ ρ' e) c c' =
      altForm (indRepQ (Q := YN ext Stab) (ρ'.comp ext.inl)) (eindQ e) (cval ρ c) (cval ρ' c') rl1 rl2 := by
  rw [PhiC_apply]
  unfold altForm
  have h1 := resW_eq (ext := ext) (Stab := Stab) ρ' rl1 (cval ρ' c' rl2)
  have h2 := resW_eq (ext := ext) (Stab := Stab) ρ' rl2 (cval ρ' c' rl1)
  exact congrArg₂ (· - ·) (congrArg (fun F => eindQ e (cval ρ c rl1) F) h1) (congrArg (fun F => eindQ e (cval ρ c rl2) F) h2)

section Sum

variable (hc : Compat ext s Stab α ext' s' ιL m0) (hr : ιL.range = Lsub) [NeZero m0] [Fintype (YN ext Stab)]
  [Fintype (L ⧸ Lsub)] (he : ∀ g a b, e (ρ g a) (ρ' g b) = e a b)

include hc hr he in
/-- **The Koszul value of the cocycles with values in `Fun(S/Stab, ·)` is the sum over the Levi cosets of the Koszul values of the evaluations at the base points on the generators `rl₁^{m₀}, rl₂^{m₀}`**:
`m₀²` from `altForm_gen` cancels the orbit size `m₀²`. -/
theorem phiC_W_sum (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ)))
    (c' : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ'))) :
    PhiC (Rep.res ext.inl (WI ext Stab ρ)) (Rep.res ext.inl (WI ext Stab ρ')) (eW ρ ρ' e) c c' =
      ∑ x : L ⧸ Lsub, APx (ρ'.comp ext.inl) e (rl1 ^ m0) (rl2 ^ m0) (cval ρ c) (cval ρ' c') (yBase ext s Stab x) := by
  have hN : ∀ (g : RadicalLattice) a b, e ((ρ.comp ext.inl) g a) ((ρ'.comp ext.inl) g b) = e a b := fun g a b => he _ a b
  have heW : ∀ (g : RadicalLattice) a b, eindQ e (indRepQ (Q := YN ext Stab) (ρ.comp ext.inl) g a)
      (indRepQ (Q := YN ext Stab) (ρ'.comp ext.inl) g b) = eindQ e a b := fun g a b => eindQ_inv _ _ e hN g a b
  have hcW := cocycleW ρ c
  have hcW' := cocycleW ρ' c'
  have h_alt := altForm_gen heW hcW hcW' rl1 rl2 (m0 : ℤ) 0 0 (m0 : ℤ)
  simp only [zpow_natCast, zpow_zero, mul_one, one_mul] at h_alt
  have hu : ∀ y : YN ext Stab, (rl1 ^ m0) • y = y := pow_smul_fix hc rl1
  have hv : ∀ y : YN ext Stab, (rl2 ^ m0) • y = y := pow_smul_fix hc rl2
  have h_AP := AP_ind (e := e) (ρ' := ρ'.comp ext.inl) (rl1 ^ m0) (rl2 ^ m0) hu hv (cval ρ c) (cval ρ' c')
  have h_sum := sum_orbits hc hr (fun y => APx (ρ'.comp ext.inl) e (rl1 ^ m0) (rl2 ^ m0) (cval ρ c) (cval ρ' c') y)
    (fun n y => APx_smul hN _ _ hu hv _ _ (cocycleW ρ c) (cocycleW ρ' c') n y)
  have h_alt' : altForm (indRepQ (Q := YN ext Stab) (ρ'.comp ext.inl)) (eindQ e) (cval ρ c) (cval ρ' c') (rl1 ^ m0) (rl2 ^ m0) =
      ∑ y, APx (ρ'.comp ext.inl) e (rl1 ^ m0) (rl2 ^ m0) (cval ρ c) (cval ρ' c') y := h_AP
  rw [phiC_W_eq]
  rw [h_alt', h_sum] at h_alt
  have hm : ((m0 ^ 2 : ℕ) : ℂ) ≠ 0 := by
    have : m0 ≠ 0 := NeZero.ne m0
    positivity
  apply mul_left_cancel₀ hm
  push_cast at h_alt ⊢
  linear_combination -h_alt

end Sum

end Cocycle

end TernaryPeriodPolynomials.Argument.RadicalInduction
