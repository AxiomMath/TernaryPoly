module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Coord

@[expose] public section


/-!
# The Hilbert space of equivariant forms

`Hs d = L²(U, dx dy; ℂ^d × ℂ^d)` carries the weighted `S`-coordinates `√ϑ · coord L` of a form `L`.
The closed subspace `eqvSub` is the orthogonal complement of the vectors expressing invariance under
the slash action (`mvec`).  The weighted coordinates of every equivariant form of finite energy
lie in it (`xvec_mem_eqvSub`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_mul mob_one IsCover cutoff cutoff_nonneg)
open TernaryPeriodPolynomials.Argument.ESFoundations.Weyl (XP mkX)

variable {Γ : Subgroup SL(2, ℤ)} {d : ℕ}

namespace HodgeDatum

variable (D : HodgeDatum Γ d) (W : Weights Γ)

theorem inner_wcoord (L₁ L₂ : Form d) (z : ℂ) :
    ⟪D.wcoord W L₁ z, D.wcoord W L₂ z⟫_ℝ = W.θ z * D.pairE L₁ L₂ z := by
  unfold wcoord
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    Real.mul_self_sqrt (W.θ_nonneg z), D.inner_coord]

/-- The second part `(ϑ(γ z) / √ϑ(z)) · coord L₁` of the invariance vectors. -/
def tcoord (γ : Γ) (L₁ : Form d) (z : ℂ) : XP (Wd d) :=
  (W.θ (mob (γ : SL(2, ℤ)) z) / Real.sqrt (W.θ z)) • D.coord L₁ z

theorem inner_tcoord (γ : Γ) (L₁ L₂ : Form d) {z : ℂ} (hz : z ∈ U) :
    ⟪D.tcoord W γ L₁ z, D.wcoord W L₂ z⟫_ℝ = W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ L₂ z := by
  unfold tcoord wcoord
  rw [real_inner_smul_left, real_inner_smul_right, D.inner_coord, ← mul_assoc]
  have h : 0 < Real.sqrt (W.θ z) := Real.sqrt_pos.mpr (W.θ_pos hz)
  congr 1
  field_simp

theorem continuousOn_tcoord (γ : Γ) {L₁ : Form d} (hL : ContinuousOn L₁ U) :
    ContinuousOn (D.tcoord W γ L₁) U := by
  have h1 : ContinuousOn (fun z => W.θ (mob (γ : SL(2, ℤ)) z)) U :=
    W.continuousOn_θ.comp (Partition.contDiffOn_mob (γ : SL(2, ℤ)) (n := 0)).continuousOn
      (Partition.mapsTo_mob _)
  have h2 : ContinuousOn (fun z => Real.sqrt (W.θ z)) U := W.continuousOn_θ.sqrt
  exact (h1.div h2 fun z hz => (Real.sqrt_pos.mpr (W.θ_pos hz)).ne').smul (D.continuousOn_coord hL)

theorem memLp_tcoord (γ : Γ) {L₁ : Form d} (hL : CptForm L₁) :
    MemLp (D.tcoord W γ L₁) 2 (volume.restrict U) := by
  obtain ⟨hc, K, hK, hKU, h0⟩ := hL
  refine memLp_of_cpt (D.continuousOn_tcoord W γ hc) hK hKU fun z hz hzK => ?_
  have e0 : mkX (0 : Wd d) 0 = 0 := rfl
  simp [tcoord, coord, h0 z hz hzK, e0]

/-- The invariance vector attached to `γ` and a compactly supported form `L₁`: the weighted
coordinates of `slash γ⁻¹ L₁` minus those of `L₁` pulled back by `γ`. -/
def mvec (γ : Γ) {L₁ : Form d} (hL : CptForm L₁) : Hs d :=
  (CptForm.memLp D W (CptForm.slash D γ⁻¹ hL)).toLp _ - (D.memLp_tcoord W γ hL).toLp _

/-- The closed subspace of "equivariant" vectors: the orthogonal complement of the invariance
vectors. -/
def eqvSub : Submodule ℝ (Hs d) :=
  (Submodule.span ℝ {v : Hs d | ∃ (γ : Γ) (L₁ : Form d) (hL : CptForm L₁), v = D.mvec W γ hL})ᗮ

/-- The weighted coordinates of a form of finite energy, as an element of `Hs d`. -/
def xvec {L : Form d} (hL : Good D W L) : Hs d := (Good.memLp D W hL).toLp _

theorem inner_mvec_xvec (γ : Γ) {L₁ : Form d} (hL₁ : CptForm L₁) {L : Form d} (hL : Good D W L) :
    ⟪D.mvec W γ hL₁, D.xvec W hL⟫_ℝ =
      (∫ z in U, W.θ z * D.pairE (D.slash γ⁻¹ L₁) L z) -
        ∫ z in U, W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ L z := by
  have h1 := inner_toLp_eq (CptForm.memLp D W (CptForm.slash D γ⁻¹ hL₁)) (Good.memLp D W hL)
  have h2 := inner_toLp_eq (D.memLp_tcoord W γ hL₁) (Good.memLp D W hL)
  have e1 : ∫ z in U, ⟪D.wcoord W (D.slash γ⁻¹ L₁) z, D.wcoord W L z⟫_ℝ =
      ∫ z in U, W.θ z * D.pairE (D.slash γ⁻¹ L₁) L z :=
    integral_congr_ae (Eventually.of_forall fun z => D.inner_wcoord W _ _ z)
  have e2 : ∫ z in U, ⟪D.tcoord W γ L₁ z, D.wcoord W L z⟫_ℝ =
      ∫ z in U, W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ L z :=
    setIntegral_congr_fun isOpen_U.measurableSet fun z hz => D.inner_tcoord W γ L₁ L hz
  unfold mvec xvec
  rw [inner_sub_left, h1, h2, e1, e2]

theorem mem_eqvSub_iff {x : Hs d} :
    x ∈ D.eqvSub W ↔ ∀ (γ : Γ) (L₁ : Form d) (hL : CptForm L₁), ⟪D.mvec W γ hL, x⟫_ℝ = 0 := by
  unfold eqvSub
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h γ L₁ hL
    exact h _ (Submodule.subset_span ⟨γ, L₁, hL, rfl⟩)
  · intro h v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨γ, L₁, hL, rfl⟩ := hv
      exact h γ L₁ hL
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [real_inner_smul_left, ha, mul_zero]

theorem continuousOn_pairE {L₁ L₂ : Form d} (h₁ : ContinuousOn L₁ U) (h₂ : ContinuousOn L₂ U) :
    ContinuousOn (D.pairE L₁ L₂) U := by
  have hS := D.S_smooth.continuousOn
  have e1 : ∀ L : Form d, ContinuousOn L U → ContinuousOn (fun z => D.S z (L z 1)) U :=
    fun L hL => hS.clm_apply (hL.clm_apply continuousOn_const)
  have e2 : ∀ L : Form d, ContinuousOn L U → ContinuousOn (fun z => D.S z (L z Complex.I)) U :=
    fun L hL => hS.clm_apply (hL.clm_apply continuousOn_const)
  exact ((e1 _ h₁).inner (e1 _ h₂)).add ((e2 _ h₁).inner (e2 _ h₂))

/-- The change of variables for the invariance vectors. -/
theorem integral_cov (γ : Γ) {L₁ L : Form d} (h₁ : ContinuousOn L₁ U) (hL : ContinuousOn L U)
    (hE : D.Eqv L) :
    ∫ z in U, W.θ z * D.pairE (D.slash γ⁻¹ L₁) L z =
      ∫ z in U, W.θ (mob (γ : SL(2, ℤ)) z) * D.pairE L₁ L z := by
  set g : ℂ → ℝ := fun w => W.θ (mob (γ : SL(2, ℤ)) w) * D.pairE L₁ L w with hg
  have hgc : ContinuousOn g U :=
    (W.continuousOn_θ.comp (Partition.contDiffOn_mob (γ : SL(2, ℤ)) (n := 0)).continuousOn
      (Partition.mapsTo_mob _)).mul (D.continuousOn_pairE h₁ hL)
  have h := integral_flat_mob ((γ : SL(2, ℤ))⁻¹) (hgc.aestronglyMeasurable isOpen_U.measurableSet)
  rw [← h]
  refine setIntegral_congr_fun isOpen_U.measurableSet fun w hw => ?_
  have e1 : D.pairE (D.slash γ⁻¹ L₁) L w = D.pairE (D.slash γ⁻¹ L₁) (D.slash γ⁻¹ L) w := by
    unfold HodgeDatum.pairE
    rw [hE γ⁻¹ w hw]
  have e2 := D.pairE_slash γ⁻¹ L₁ L hw
  have e3 : mob (γ : SL(2, ℤ)) (mob ((γ : SL(2, ℤ))⁻¹) w) = w := by
    rw [← mob_mul, mul_inv_cancel, mob_one hw]
  simp only [Subgroup.coe_inv] at e2
  simp only [hg, e3, jac, smul_eq_mul]
  rw [e1, e2]
  ring

end HodgeDatum

theorem HodgeDatum.xvec_mem_eqvSub (D : HodgeDatum Γ d) (W : Weights Γ) {L : Form d}
    (hL : Good D W L) (hE : D.Eqv L) : D.xvec W hL ∈ D.eqvSub W := by
  rw [mem_eqvSub_iff]
  intro γ L₁ hL₁
  rw [inner_mvec_xvec, D.integral_cov W γ hL₁.1 hL.cont hE, sub_self]

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
