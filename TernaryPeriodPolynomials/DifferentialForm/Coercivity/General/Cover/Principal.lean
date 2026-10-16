module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Basic
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Consumer
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperFinite

@[expose] public section


/-!
# General coercivity: principal congruence subgroups are admissible

Every subgroup of the level-three principal congruence subgroup of `GL₃(ℤ)`, embedded in `GL₃(ℝ)`,
is `Admissible`.  In particular the principal congruence subgroups `Γ(N)` with `3 ∣ N`, their
intersections with the sum-covector fixer `K`, and the cover `principalSixInK` are admissible.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering
open TernaryPoly.SymmetricSpaceArithmeticProper TernaryPoly.IntegralGL3Congruence

/-- Every subgroup of `Γ(3)` embeds into `GL₃(ℝ)` as an admissible group. -/
theorem admissible_map_realIntegral (H : Subgroup IntegralGL) (hH : H ≤ principalThree) :
    Admissible (H.map realIntegral) where
  det_one := by
    rintro _ ⟨h, hh, rfl⟩
    rw [realIntegral_det, principalThree_det_one h (hH hh)]
    exact Int.cast_one
  free := by
    rintro _ ⟨h, hh, rfl⟩ S hS
    rw [principalThree_finiteOrder_eq_one h (hH hh) (integral_fixed_isOfFinOrder h S hS), map_one]
  transporters C D hC hD := by
    have hf := (compact_transporter_finite C D hC hD).image realIntegral
    refine (hf.preimage (Subtype.val_injective.injOn)).subset ?_
    rintro ⟨_, g, hg, rfl⟩ ⟨_, ⟨S, hS, rfl⟩, hT⟩
    exact ⟨g, ⟨S, hS, hT⟩, rfl⟩

/-- The principal congruence subgroup of level divisible by three lies in the level-three one. -/
theorem principal_le_principalThree {N : ℕ} (h3 : 3 ∣ N) : principal N ≤ principalThree := by
  intro g hg
  apply (mem_principal_iff 3 g).mpr
  intro i j
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h3) ((mem_principal_iff N g).mp hg i j)

/-- The principal congruence subgroup `Γ(N)` of level divisible by three, inside `GL₃(ℝ)`. -/
def principalReal (N : ℕ) : Subgroup RealGL := (principal N).map realIntegral

/-- Principal congruence subgroups of level divisible by three are admissible. -/
theorem admissible_principalReal {N : ℕ} (h3 : 3 ∣ N) : Admissible (principalReal N) :=
  admissible_map_realIntegral _ (principal_le_principalThree h3)

/-- The cover (`Γ(6)` inside the sum-covector fixer `K`) as a subgroup of `GL₃(ℝ)`. -/
def principalSixInKReal : Subgroup RealGL :=
  (principalSixInK.map TernaryPoly.ModThreeGoodAction.K.subtype).map realIntegral

/-- The cover is admissible. -/
theorem admissible_principalSixInKReal : Admissible principalSixInKReal :=
  admissible_map_realIntegral _ (by
    rintro _ ⟨g, hg, rfl⟩
    exact principalSix_le_three ((mem_principalSixInK g).mp hg))

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
