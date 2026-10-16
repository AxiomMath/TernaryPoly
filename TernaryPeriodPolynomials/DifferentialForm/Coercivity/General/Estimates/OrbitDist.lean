module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.SmoothSlope
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Basic

@[expose] public section


/-! # General coercivity, Tier B: the distance to an orbit and its cutoff profiles

The distance `rho` from a point to the orbit of a base point is a `Γ`-invariant `1`-Lipschitz function
of the covering space.  Its truncations `mProfile` are invariant, `1/r`-Lipschitz, take values in
`[0, 1]`, are `1` on `rho ≤ r` and vanish for `rho ≥ 2 r`; their supports project into the compact
subsets `proj '' closedBall S0 R` of the orbit space, which exhaust it.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceTraceMetric
  TernaryPoly.SymmetricSpaceRiemannian Set Metric Filter
open scoped ContDiff Topology

variable {Γ : Subgroup RealGL}

attribute [local instance] spaceMetricSpace

theorem dist_smul_Space (g : RealGL) (S T : Space) : dist (g • S) (g • T) = dist S T := by
  have e : edist (g • S) (g • T) = edist S T := riemannianEDist_act g S T
  rw [dist_edist, dist_edist, e]

theorem dist_smul_Space' (γ : Γ) (S T : Space) : dist (γ • S) (γ • T) = dist S T :=
  dist_smul_Space (γ : RealGL) S T

/-- The distance to the orbit of a base point: a `Γ`-invariant `1`-Lipschitz function. -/
def rho (Γ : Subgroup RealGL) (S0 S : Space) : ℝ :=
  infDist S (Set.range fun γ : Γ => γ • S0)

theorem rho_nonneg (S0 S : Space) : 0 ≤ rho Γ S0 S := infDist_nonneg

theorem abs_rho_sub_le (S0 S T : Space) : |rho Γ S0 S - rho Γ S0 T| ≤ dist S T := by
  have h1 := Metric.infDist_le_infDist_add_dist (x := S) (y := T)
    (s := Set.range fun γ : Γ => γ • S0)
  have h2 := Metric.infDist_le_infDist_add_dist (x := T) (y := S)
    (s := Set.range fun γ : Γ => γ • S0)
  rw [dist_comm] at h2
  rw [abs_le]
  unfold rho
  constructor <;> linarith

theorem rho_smul (S0 : Space) (γ : Γ) (S : Space) : rho Γ S0 (γ • S) = rho Γ S0 S := by
  have hiso : Isometry (fun T : Space => γ • T) :=
    Isometry.of_dist_eq fun S T => dist_smul_Space' γ S T
  have himg : (fun T : Space => γ • T) '' (Set.range fun γ' : Γ => γ' • S0) =
      Set.range fun γ' : Γ => γ' • S0 := by
    rw [← Set.range_comp]
    have : ((fun T : Space => γ • T) ∘ fun γ' : Γ => γ' • S0) =
        (fun γ' : Γ => γ' • S0) ∘ (fun γ' : Γ => γ * γ') := by
      funext γ'
      simp [mul_smul]
    rw [this]
    exact (Equiv.mulLeft γ).surjective.range_comp _
  calc rho Γ S0 (γ • S)
      = infDist (γ • S) ((fun T : Space => γ • T) '' (Set.range fun γ' : Γ => γ' • S0)) := by
        unfold rho
        rw [himg]
    _ = rho Γ S0 S := Metric.infDist_image hiso

/-- The cutoff profile of the distance to the orbit: `1` up to radius `r`, `0` from `2r` on. -/
def mProfile (Γ : Subgroup RealGL) (S0 : Space) (r : ℝ) (S : Space) : ℝ :=
  max 0 (min 1 (2 - rho Γ S0 S / r))

theorem mProfile_mem (S0 : Space) (r : ℝ) (S : Space) :
    0 ≤ mProfile Γ S0 r S ∧ mProfile Γ S0 r S ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem mProfile_smul (S0 : Space) (r : ℝ) (γ : Γ) (S : Space) :
    mProfile Γ S0 r (γ • S) = mProfile Γ S0 r S := by
  unfold mProfile
  rw [rho_smul]

theorem abs_clamp_sub (s t : ℝ) : |max 0 (min 1 s) - max 0 (min 1 t)| ≤ |s - t| := by
  have h := abs_le.mp (le_refl |s - t|)
  rw [abs_le]
  constructor <;> simp only [max_def, min_def] <;> split_ifs <;> linarith [h.1, h.2]

theorem abs_mProfile_sub (S0 : Space) {r : ℝ} (hr : 0 < r) (S T : Space) :
    |mProfile Γ S0 r S - mProfile Γ S0 r T| ≤ (1 / r) * dist S T := by
  have h1 : |(2 - rho Γ S0 S / r) - (2 - rho Γ S0 T / r)| ≤ (1 / r) * dist S T := by
    have : (2 - rho Γ S0 S / r) - (2 - rho Γ S0 T / r) = -((rho Γ S0 S - rho Γ S0 T) / r) := by
      ring
    rw [this, abs_neg, abs_div, abs_of_pos hr, div_eq_mul_inv, mul_comm, one_div]
    exact mul_le_mul_of_nonneg_left (abs_rho_sub_le S0 S T) (inv_nonneg.mpr hr.le)
  exact (abs_clamp_sub _ _).trans h1

theorem mProfile_eq_one (S0 : Space) {r : ℝ} (hr : 0 < r) {S : Space} (h : rho Γ S0 S ≤ r) :
    mProfile Γ S0 r S = 1 := by
  have : 1 ≤ 2 - rho Γ S0 S / r := by
    have : rho Γ S0 S / r ≤ 1 := (div_le_one hr).mpr h
    linarith
  unfold mProfile
  rw [min_eq_left this]
  simp

theorem rho_lt_of_mProfile_ne_zero (S0 : Space) {r : ℝ} (hr : 0 < r) {S : Space}
    (h : mProfile Γ S0 r S ≠ 0) : rho Γ S0 S < 2 * r := by
  by_contra hcon
  rw [not_lt] at hcon
  apply h
  have : 2 - rho Γ S0 S / r ≤ 0 := by
    have : 2 ≤ rho Γ S0 S / r := (le_div_iff₀ hr).mpr (by linarith)
    linarith
  unfold mProfile
  rw [max_eq_left]
  exact (min_le_right _ _).trans this

theorem isCompact_projBall (S0 : Space) (R : ℝ) : IsCompact (proj Γ '' closedBall S0 R) := by
  have : ProperSpace Space := space_proper
  exact (isCompact_closedBall S0 R).image continuous_proj

theorem proj_mem_of_rho_lt (S0 : Space) {R : ℝ} {S : Space} (h : rho Γ S0 S < R) :
    proj Γ S ∈ proj Γ '' closedBall S0 R := by
  have hne : (Set.range fun γ : Γ => γ • S0).Nonempty := ⟨_, 1, rfl⟩
  obtain ⟨_, ⟨γ, rfl⟩, hd⟩ := (Metric.infDist_lt_iff hne).mp h
  refine ⟨γ⁻¹ • S, mem_closedBall.mpr ?_, proj_smul γ⁻¹ S⟩
  have e : dist (γ⁻¹ • S) S0 = dist S (γ • S0) := by
    have := dist_smul_Space' γ⁻¹ S (γ • S0)
    rwa [inv_smul_smul] at this
  rw [e]
  exact hd.le

theorem rho_le_of_proj_mem (S0 : Space) {R : ℝ} {S : Space}
    (h : proj Γ S ∈ proj Γ '' closedBall S0 R) : rho Γ S0 S ≤ R := by
  obtain ⟨T, hT, hTS⟩ := h
  obtain ⟨γ, hγ⟩ := proj_eq_iff.mp hTS.symm
  rw [← rho_smul S0 γ S, hγ]
  have h1 : rho Γ S0 T ≤ dist T S0 :=
    Metric.infDist_le_dist_of_mem (x := T) (s := Set.range fun γ : Γ => γ • S0)
      ⟨1, one_smul _ _⟩ |>.trans_eq (by rfl)
  exact h1.trans (mem_closedBall.mp hT)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
