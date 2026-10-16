module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Invariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.TwistKoszul

@[expose] public section


/-!
# Orientation reversal of the Farey integrand and independence of the representative triangles

Formalized by Claude Sonnet 5.5.

For `g ∈ GL₂(ℤ)` of determinant `-1` the head and tail of an oriented dual edge are exchanged (`head_smul_neg`, `tail_smul_neg`), so the triangle integrand of the cup form changes sign under pull-back (`integ_comp_neg`):
this is the orientation reversal of the modular curve, the explicit sign `det g` of the frame change.  `sum_tri_normalizer`: for a `Γ(N)`-invariant function on triangles, the sum over the representative triangles is unchanged by translation by an element normalising `Γ(N)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open scoped Classical

theorem isSL_of_neg_mul {g h : IntegralGL} (hg : g.val.det = -1) (hh : h.val.det = -1) : IsSL (g * h) := by
  unfold IsSL
  rw [Units.val_mul, Matrix.det_mul, hg, hh]; norm_num

theorem head_smul_neg {g : IntegralGL} (hg : g.val.det = -1) (q : OTE) : head (g • q) = g • tail q := by
  obtain ⟨h, hh, hq⟩ := ote_transitive_sl q
  have hgh : (g * h).val.det = -1 := by
    rw [Units.val_mul, Matrix.det_mul, hg]; unfold IsSL at hh; rw [hh]; norm_num
  have hsl : IsSL (g * h * s0) := isSL_of_neg_mul hgh s0_det
  have hp : (g * h * s0) • p0 = g • q := by
    rw [mul_smul, MulAction.mem_stabilizer_iff.mp s0_mem, mul_smul, hq]
  rw [head_eq hsl hp, tail_eq hh hq, mul_smul, mul_smul, s0_cusp2]

theorem tail_smul_neg {g : IntegralGL} (hg : g.val.det = -1) (q : OTE) : tail (g • q) = g • head q := by
  obtain ⟨h, hh, hq⟩ := ote_transitive_sl q
  have hgh : (g * h).val.det = -1 := by
    rw [Units.val_mul, Matrix.det_mul, hg]; unfold IsSL at hh; rw [hh]; norm_num
  have hsl : IsSL (g * h * s0) := isSL_of_neg_mul hgh s0_det
  have hp : (g * h * s0) • p0 = g • q := by
    rw [mul_smul, MulAction.mem_stabilizer_iff.mp s0_mem, mul_smul, hq]
  rw [tail_eq hsl hp, head_eq hh hq, mul_smul, mul_smul, s0_cusp1]

variable {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']

/-- **Orientation reversal**: pulling back along a determinant `-1` element changes the sign of the triangle integrand. -/
theorem integ_comp_neg (ε : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ) (Φ : RationalLine2 → A) (Φ' : RationalLine2 → A') {g : IntegralGL}
    (hg : g.val.det = -1) (y : Tri) :
    integ ε (fun c => Φ (g • c)) (fun c => Φ' (g • c)) y = - integ ε Φ Φ' (g • y) := by
  unfold integ
  rw [nbF_smul, Finset.sum_image (fun a _ b _ h => MulAction.injective g h), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [head_smul_neg hg, tail_smul_neg hg]
  ring


/-- **The sum over the representative triangles does not depend on the representatives**: translating by an element `g` normalising `Γ(N)` does not change the sum of a `Γ(N)`-invariant function. -/
theorem sum_tri_normalizer {N : ℕ} (hN : 3 ≤ N) (g : IntegralGL)
    (hg : ∀ γ : gammaNGL N, g * (γ : IntegralGL) * g⁻¹ ∈ gammaNGL N)
    (hg' : ∀ γ : gammaNGL N, g⁻¹ * (γ : IntegralGL) * g ∈ gammaNGL N)
    (F : Tri → ℂ) (hF : ∀ (γ : gammaNGL N) (y : Tri), F ((γ : IntegralGL) • y) = F y) :
    ∑ y ∈ (gammaNFareyData hN).RT.R, F (g • y) = ∑ y ∈ (gammaNFareyData hN).RT.R, F y := by
  set D := gammaNFareyData hN with hD
  refine Finset.sum_bij (fun y _ => ((dec D.RT (g • y)).1 : Tri)) (fun y _ => (dec D.RT (g • y)).1.2) ?_ ?_ ?_
  · intro y1 h1 y2 h2 h
    have s1 := dec_spec D.RT (g • y1)
    have s2 := dec_spec D.RT (g • y2)
    set r := ((dec D.RT (g • y1)).1 : Tri) with hr
    set d1 := (dec D.RT (g • y1)).2 with hd1
    set d2 := (dec D.RT (g • y2)).2 with hd2
    have s2' : d2 • r = g • y2 := by
      have : ((dec D.RT (g • y2)).1 : Tri) = r := h.symm
      rw [← this]; exact s2
    have hmem : g⁻¹ * ((d2 * d1⁻¹ : gammaNGL N) : IntegralGL) * g ∈ gammaNGL N := hg' _
    have e1 : y1 = g⁻¹ • ((d1 : IntegralGL) • r) := by
      have := s1
      change (d1 : IntegralGL) • r = g • y1 at this
      rw [this, inv_smul_smul]
    have e2 : y2 = g⁻¹ • ((d2 : IntegralGL) • r) := by
      have := s2'
      change (d2 : IntegralGL) • r = g • y2 at this
      rw [this, inv_smul_smul]
    have hrel : (⟨_, hmem⟩ : gammaNGL N) • y1 = y2 := by
      change (g⁻¹ * ((d2 * d1⁻¹ : gammaNGL N) : IntegralGL) * g) • y1 = y2
      rw [e1, ← mul_smul, ← mul_smul]
      have e3 : g⁻¹ * ((d2 * d1⁻¹ : gammaNGL N) : IntegralGL) * g * g⁻¹ * (d1 : IntegralGL) =
          g⁻¹ * (d2 : IntegralGL) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [e3, mul_smul]
      exact e2.symm
    exact D.RT.inj y1 (by simpa using h1) y2 (by simpa using h2) _ hrel
  · intro r hr
    obtain ⟨y, hy, γ, hγ⟩ := D.RT.cover (g⁻¹ • r)
    refine ⟨y, hy, ?_⟩
    have hy' : y = (γ : IntegralGL)⁻¹ • g⁻¹ • r := by
      rw [← hγ]; change y = (γ : IntegralGL)⁻¹ • (γ : IntegralGL) • y; rw [inv_smul_smul]
    have hδ : g * ((γ⁻¹ : gammaNGL N) : IntegralGL) * g⁻¹ ∈ gammaNGL N := hg _
    have hrel : (⟨_, hδ⟩ : gammaNGL N) • r = g • y := by
      change (g * ((γ⁻¹ : gammaNGL N) : IntegralGL) * g⁻¹) • r = g • y
      rw [hy', ← mul_smul, ← mul_smul]
      simp only [Subgroup.coe_inv]
    rw [dec_eq D.RT D.freeT (p := (⟨r, hr⟩, ⟨_, hδ⟩)) hrel]
  · intro y _
    have s := dec_spec D.RT (g • y)
    calc F (g • y) = F ((dec D.RT (g • y)).2 • ((dec D.RT (g • y)).1 : Tri)) := by rw [s]
      _ = F ((dec D.RT (g • y)).1 : Tri) := hF _ _

end TernaryPeriodPolynomials.Argument.FrameInvariance
