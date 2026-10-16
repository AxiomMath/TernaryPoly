module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CompactSupport.Cusps
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CompactSupport.Geometry
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CompactSupport.Cutoffs

@[expose] public section


/-!
# Cusp surgery: an equivariant correction that kills a primitive deep in the horoballs

Step 1 of the unconditional Eichler--Shimura route.
Given `CuspData` (representatives `G` of the cusp classes of a finite-index `Γ ∌ -1`, a generator
of each cusp stabiliser, and a vector `v g` whose coboundary is the cocycle `c` on the stabiliser of
the cusp `g ∞`), and a function `φ` on the upper half plane, the local model near the cusp `g` is
`weight g w • (φ w + v g)`, where `weight g` is a smooth cutoff supported in the horoball
`Im (g⁻¹ w) > 3/2`, equal to `1` on `Im (g⁻¹ w) > 2` after summing the translates by the
stabiliser (`eta_finsum`).  The correction `corr = ∑_{γ ∈ Γ} ρ(γ) θ(γ⁻¹ z)` is smooth
(`contDiffOn_corr`, local finiteness `exists_finite_nbhd_theta`), satisfies `corr (γ z) = ρ γ (corr z)`
(`corr_mob`), and equals `φ w + v g₀` at every point of the height-two horoball at a representative
`g₀` when `φ(γ z) = ρ γ (φ z) + c γ` (`corr_deep`).

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularGroup Complex
open scoped Modular MatrixGroups ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport

open TernaryPeriodPolynomials.Argument.ESFoundations
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)

variable {Γ : Subgroup SL(2, ℤ)} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Choices at the cusps: representatives of the cusp classes, a generator of each cusp
stabiliser, and a vector whose coboundary is the cocycle on the whole stabiliser. -/
structure CuspData (ρ : Γ →* (W →ₗ[ℝ] W)) (c : Γ → W) where
  G : Finset SL(2, ℤ)
  inequiv : ∀ g ∈ G, ∀ g' ∈ G, CuspRel Γ g g' → g = g'
  cover : ∀ g : SL(2, ℤ), ∃ g₀ ∈ G, CuspRel Γ g g₀
  γ₀ : SL(2, ℤ) → SL(2, ℤ)
  v : SL(2, ℤ) → W
  mem : ∀ g, γ₀ g ∈ cuspStab Γ g
  pos : ∀ g, 0 < transLen (g⁻¹ * γ₀ g * g)
  zp : ∀ g, cuspStab Γ g = Subgroup.zpowers (γ₀ g)
  vec : ∀ g, ∀ γ : Γ, (γ : SL(2, ℤ)) ∈ cuspStab Γ g → c γ = ρ γ (v g) - v g

theorem exists_cuspData [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∉ Γ) (ρ : Γ →* (W →ₗ[ℝ] W))
    (c : Γ → W) (hc : ∀ δ γ : Γ, c (δ * γ) = c δ + ρ δ (c γ))
    (hpar : ∀ γ : Γ, IsParabolicElt γ.1 → ∃ u : W, c γ = ρ γ u - u) :
    Nonempty (CuspData ρ c) := by
  obtain ⟨G, h1, h2⟩ := exists_cuspReps Γ
  choose γ₀ hmem hpos hz v hv using exists_cusp_vector ρ c hneg hc hpar
  exact ⟨⟨G, h1, h2, γ₀, v, hmem, hpos, hz, hv⟩⟩

variable {ρ : Γ →* (W →ₗ[ℝ] W)} {c : Γ → W} (D : CuspData ρ c)

/-- The translation length of the generator of the stabiliser of the cusp `g ∞`. -/
def CuspData.width (g : SL(2, ℤ)) : ℝ := (transLen (g⁻¹ * D.γ₀ g * g) : ℝ)

theorem CuspData.width_pos (g : SL(2, ℤ)) : 0 < D.width g := by
  unfold CuspData.width
  exact_mod_cast D.pos g

/-- The cutoff at the cusp `g ∞`: `chi` of the height times `eta` of the width coordinate. -/
def CuspData.weight (g : SL(2, ℤ)) (w : ℂ) : ℝ :=
  chi (mob g⁻¹ w).im * eta ((mob g⁻¹ w).re / D.width g)

theorem CuspData.weight_ne_zero {g : SL(2, ℤ)} {w : ℂ} (h : D.weight g w ≠ 0) :
    3 / 2 < (mob g⁻¹ w).im ∧ |(mob g⁻¹ w).re / D.width g| < 1 := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
  refine ⟨?_, abs_lt_of_eta_ne_zero h2⟩
  by_contra h'
  exact h1 (chi_eq_zero (not_lt.mp h'))

variable (φ : ℂ → W)

/-- The local model: the cutoffs times `φ + v`, summed over the cusp representatives. -/
def CuspData.theta (w : ℂ) : W := ∑ g ∈ D.G, D.weight g w • (φ w + D.v g)

theorem CuspData.exists_finite_nbhd_theta {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ ∃ T : Finset Γ, ∀ z ∈ V, ∀ γ : Γ,
      D.theta φ (mob (γ : SL(2, ℤ))⁻¹ z) ≠ 0 → γ ∈ T := by
  classical
  set B : ℝ := ∑ g ∈ D.G, D.width g with hB
  obtain ⟨V, hVo, hzV, hVU, T₁, hT₁⟩ := exists_finite_nbhd_re hz₀ B
  refine ⟨V, hVo, hzV, hVU,
    ((T₁ ×ˢ D.G).image fun p : SL(2, ℤ) × SL(2, ℤ) => p.1⁻¹ * p.2⁻¹).subtype (· ∈ Γ), ?_⟩
  intro z hz γ hγ
  obtain ⟨g, hg, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
  have hw : D.weight g (mob (γ : SL(2, ℤ))⁻¹ z) ≠ 0 := fun h0 => hne (by rw [h0, zero_smul])
  obtain ⟨him, hre⟩ := D.weight_ne_zero hw
  have hwp := D.width_pos g
  have hrel : mob (g⁻¹ * (γ : SL(2, ℤ))⁻¹) z = mob g⁻¹ (mob (γ : SL(2, ℤ))⁻¹ z) := mob_mul _ _ _
  have hwB : D.width g ≤ B :=
    Finset.single_le_sum (f := fun g => D.width g) (fun g _ => (D.width_pos g).le) hg
  have hre' : |(mob (g⁻¹ * (γ : SL(2, ℤ))⁻¹) z).re| ≤ B := by
    rw [hrel]
    rw [abs_div, abs_of_pos hwp, div_lt_one hwp] at hre
    linarith
  have ha := hT₁ z hz _ ⟨hre', by rw [hrel]; linarith⟩
  rw [Finset.mem_subtype, Finset.mem_image]
  exact ⟨(g⁻¹ * (γ : SL(2, ℤ))⁻¹, g), Finset.mem_product.mpr ⟨ha, hg⟩, by group⟩

theorem CuspData.contDiffOn_weight (g : SL(2, ℤ)) : ContDiffOn ℝ ∞ (D.weight g) U := by
  have him : ContDiffOn ℝ ∞ (fun w => (mob g⁻¹ w).im) U :=
    Complex.imCLM.contDiff.comp_contDiffOn (contDiffOn_mob g⁻¹)
  have hre : ContDiffOn ℝ ∞ (fun w => (mob g⁻¹ w).re / D.width g) U :=
    (Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_mob g⁻¹)).div_const _
  exact (contDiff_chi.comp_contDiffOn him).mul (contDiff_eta.comp_contDiffOn hre)

theorem CuspData.contDiffOn_theta (hφ : ContDiffOn ℝ ∞ φ U) : ContDiffOn ℝ ∞ (D.theta φ) U :=
  ContDiffOn.sum fun g _ => (D.contDiffOn_weight g).smul (hφ.add contDiffOn_const)

/-- The equivariant correction `∑_{γ ∈ Γ} ρ(γ) θ(γ⁻¹ z)`. -/
def CuspData.corr (z : ℂ) : W := ∑ᶠ γ : Γ, ρ γ (D.theta φ (mob (γ : SL(2, ℤ))⁻¹ z))

theorem CuspData.hasFiniteSupport {z : ℂ} (hz : z ∈ U) :
    Function.HasFiniteSupport fun γ : Γ => ρ γ (D.theta φ (mob (γ : SL(2, ℤ))⁻¹ z)) := by
  obtain ⟨V, -, hzV, -, T, hT⟩ := D.exists_finite_nbhd_theta φ hz
  refine T.finite_toSet.subset fun γ hγ => hT z hzV γ fun h0 => hγ ?_
  simp only [h0, map_zero]

theorem CuspData.contDiffOn_corr [FiniteDimensional ℝ W] (hφ : ContDiffOn ℝ ∞ φ U) : ContDiffOn ℝ ∞ (D.corr φ) U := by
  refine contDiffOn_of_locally_contDiffOn fun z₀ hz₀ => ?_
  obtain ⟨V, hVo, hzV, -, T, hT⟩ := D.exists_finite_nbhd_theta φ hz₀
  refine ⟨V, hVo, hzV, ?_⟩
  have h : ContDiffOn ℝ ∞
      (fun z => ∑ γ ∈ T, ρ γ (D.theta φ (mob (γ : SL(2, ℤ))⁻¹ z))) (U ∩ V) :=
    ContDiffOn.sum fun γ _ =>
      ((ρ γ).toContinuousLinearMap.contDiff.comp_contDiffOn
        (((D.contDiffOn_theta φ hφ).comp (contDiffOn_mob _) (mapsTo_mob _)))).mono
          Set.inter_subset_left
  refine h.congr fun z hz => ?_
  exact finsum_eq_sum_of_support_subset _ fun γ hγ => hT z hz.2 γ fun h0 => hγ (by simp only [h0, map_zero])

/-- The correction is equivariant for the representation `ρ`. -/
theorem CuspData.corr_mob (δ : Γ) {z : ℂ} (hz : z ∈ U) :
    D.corr φ (mob (δ : SL(2, ℤ)) z) = ρ δ (D.corr φ z) := by
  have hz' : mob (δ : SL(2, ℤ)) z ∈ U := mob_mem _ _
  have hshift : ∀ γ : Γ, ρ (δ * γ) (D.theta φ (mob ((δ * γ : Γ) : SL(2, ℤ))⁻¹ (mob δ z))) =
      ρ δ (ρ γ (D.theta φ (mob (γ : SL(2, ℤ))⁻¹ z))) := by
    intro γ
    rw [← mob_mul, Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right, map_mul,
      Module.End.mul_apply]
  unfold CuspData.corr
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)
    (f := fun γ : Γ => ρ γ (D.theta φ (mob (γ : SL(2, ℤ))⁻¹ (mob δ z))))]
  simp only [Equiv.coe_mulLeft, hshift]
  rw [map_finsum (ρ δ) (D.hasFiniteSupport φ hz)]


/-! ### The correction at a deep point of a horoball -/

theorem CuspData.weight_cusp {g0 : SL(2, ℤ)} (hg0 : g0 ∈ D.G) {w : ℂ}
    (hdeep : 2 < (mob g0⁻¹ w).im) (γ : Γ) {g : SL(2, ℤ)} (hg : g ∈ D.G)
    (h : D.weight g (mob (γ : SL(2, ℤ))⁻¹ w) ≠ 0) :
    g = g0 ∧ (γ : SL(2, ℤ)) ∈ cuspStab Γ g0 := by
  obtain ⟨him, -⟩ := D.weight_ne_zero h
  have hu : mob g0⁻¹ w ∈ U := mob_mem _ _
  have hmob : mob (g⁻¹ * (γ : SL(2, ℤ))⁻¹ * g0) (mob g0⁻¹ w) =
      mob g⁻¹ (mob (γ : SL(2, ℤ))⁻¹ w) := by
    rw [← mob_mul, ← mob_mul]; congr 1; group
  have ha : (g⁻¹ * (γ : SL(2, ℤ))⁻¹ * g0) 1 0 = 0 :=
    lowerLeft_of_mob hu (by linarith) (by rw [hmob]; linarith)
  have hrel : CuspRel Γ g0 g := ⟨(γ : SL(2, ℤ))⁻¹, Γ.inv_mem γ.2, ha⟩
  have hgg : g0 = g := D.inequiv g0 hg0 g hg hrel
  subst hgg
  refine ⟨rfl, ?_⟩
  have hinv : (γ : SL(2, ℤ))⁻¹ ∈ cuspStab Γ g0 :=
    (mem_cuspStab_iff Γ g0 _).mpr ⟨Γ.inv_mem γ.2, ha⟩
  simpa using (cuspStab Γ g0).inv_mem hinv

theorem CuspData.corr_deep (hφ : ∀ δ : Γ, ∀ z ∈ U, φ (mob (δ : SL(2, ℤ)) z) = ρ δ (φ z) + c δ)
    {g0 : SL(2, ℤ)} (hg0 : g0 ∈ D.G) {w : ℂ} (hw : w ∈ U) (hdeep : 2 < (mob g0⁻¹ w).im) :
    D.corr φ w = φ w + D.v g0 := by
  classical
  have ha0Γ : D.γ₀ g0 ∈ Γ := ((mem_cuspStab_iff Γ g0 _).mp (D.mem g0)).1
  have ha0 : (g0⁻¹ * D.γ₀ g0 * g0) 1 0 = 0 := ((mem_cuspStab_iff Γ g0 _).mp (D.mem g0)).2
  set a0 : Γ := ⟨D.γ₀ g0, ha0Γ⟩ with ha0def
  set T0 : ℤ := transLen (g0⁻¹ * D.γ₀ g0 * g0) with hT0
  have hT0pos : 0 < T0 := D.pos g0
  have hwidth : D.width g0 = (T0 : ℝ) := rfl
  have hcoe : ∀ j : ℤ, ((a0 ^ j : Γ) : SL(2, ℤ)) = D.γ₀ g0 ^ j := fun j => by
    rw [Subgroup.coe_zpow]
  let ι : ℤ → Γ := fun j => a0 ^ j
  have hι : Function.Injective ι := by
    intro j j' hjj
    have h1 : D.γ₀ g0 ^ j = D.γ₀ g0 ^ j' := by
      rw [← hcoe, ← hcoe]; exact congrArg Subtype.val hjj
    have h2 := congrArg (fun x => transLen (g0⁻¹ * x * g0)) h1
    have e : ∀ k : ℤ, g0⁻¹ * D.γ₀ g0 ^ k * g0 = (g0⁻¹ * D.γ₀ g0 * g0) ^ k := fun k => by
      have := conj_zpow (a := g0⁻¹) (b := D.γ₀ g0) (i := k)
      simpa using this.symm
    rw [e, e, (transLen_zpow ha0 j).2, (transLen_zpow ha0 j').2] at h2
    have : j = j' := by
      have := mul_right_cancel₀ hT0pos.ne' h2
      exact this
    exact this
  set x := (mob g0⁻¹ w).re with hx
  set ψ := φ w + D.v g0 with hψ
  have hu : mob g0⁻¹ w ∈ U := mob_mem _ _
  -- the terms along the stabiliser
  have hterm : ∀ j : ℤ, ρ (ι j) (D.theta φ (mob ((ι j : Γ) : SL(2, ℤ))⁻¹ w)) =
      eta (x / T0 - j) • ψ := by
    intro j
    have hinvcoe : ((ι j : Γ) : SL(2, ℤ))⁻¹ = D.γ₀ g0 ^ (-j) := by
      show ((a0 ^ j : Γ) : SL(2, ℤ))⁻¹ = _
      rw [hcoe, zpow_neg]
    have hmemstab : D.γ₀ g0 ^ (-j) ∈ cuspStab Γ g0 := (cuspStab Γ g0).zpow_mem (D.mem g0) _
    have hshift := mob_conj_zpow ha0 (-j) w
    have hweight : D.weight g0 (mob ((ι j : Γ) : SL(2, ℤ))⁻¹ w) = eta (x / T0 - j) := by
      unfold CuspData.weight
      rw [hinvcoe, hshift, hwidth]
      have him : (mob g0⁻¹ w + (((-j * T0 : ℤ)) : ℂ)).im = (mob g0⁻¹ w).im := by simp
      have hre : (mob g0⁻¹ w + (((-j * T0 : ℤ)) : ℂ)).re = x - j * T0 := by
        simp [hx]; ring
      rw [him, hre, chi_eq_one (by linarith)]
      have hT0r : (T0 : ℝ) ≠ 0 := by exact_mod_cast hT0pos.ne'
      have : (x - j * T0) / T0 = x / T0 - j := by field_simp
      rw [this, one_mul]
    have hother : ∀ g ∈ D.G, g ≠ g0 → D.weight g (mob ((ι j : Γ) : SL(2, ℤ))⁻¹ w) = 0 := by
      intro g hg hne
      by_contra hne'
      exact hne (D.weight_cusp hg0 hdeep (ι j) hg hne').1
    have htheta : D.theta φ (mob ((ι j : Γ) : SL(2, ℤ))⁻¹ w) =
        eta (x / T0 - j) • (φ (mob ((ι j : Γ) : SL(2, ℤ))⁻¹ w) + D.v g0) := by
      unfold CuspData.theta
      rw [Finset.sum_eq_single g0 (fun g hg hne => by rw [hother g hg hne, zero_smul])
        (fun h => absurd hg0 h), hweight]
    have hvec := D.vec g0 (ι j)⁻¹ (by
      show ((ι j)⁻¹ : Γ).1 ∈ cuspStab Γ g0
      rw [Subgroup.coe_inv, hinvcoe]; exact hmemstab)
    have hφj := hφ (ι j)⁻¹ w hw
    have hφeq : φ (mob ((ι j : Γ) : SL(2, ℤ))⁻¹ w) + D.v g0 = ρ (ι j)⁻¹ ψ := by
      have : mob ((ι j : Γ) : SL(2, ℤ))⁻¹ w = mob (((ι j)⁻¹ : Γ) : SL(2, ℤ)) w := by
        rw [Subgroup.coe_inv]
      rw [this, hφj, hvec, hψ, map_add]
      abel
    rw [htheta, hφeq, map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  have hsupp : Function.support
      (fun γ : Γ => ρ γ (D.theta φ (mob (γ : SL(2, ℤ))⁻¹ w))) ⊆ Set.range ι := by
    intro γ hγ
    have hθ : D.theta φ (mob (γ : SL(2, ℤ))⁻¹ w) ≠ 0 := fun h0 => hγ (by simp only [h0, map_zero])
    obtain ⟨g, hg, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hθ
    have hwt : D.weight g (mob (γ : SL(2, ℤ))⁻¹ w) ≠ 0 := fun h0 => hne (by rw [h0, zero_smul])
    obtain ⟨-, hstab⟩ := D.weight_cusp hg0 hdeep γ hg hwt
    rw [D.zp g0, Subgroup.mem_zpowers_iff] at hstab
    obtain ⟨j, hj⟩ := hstab
    exact ⟨j, Subtype.ext (by show ((a0 ^ j : Γ) : SL(2, ℤ)) = _; rw [hcoe]; exact hj)⟩
  unfold CuspData.corr
  have h1 : ∑ᶠ γ : Γ, ρ γ (D.theta φ (mob (γ : SL(2, ℤ))⁻¹ w)) =
      ∑ᶠ γ ∈ Set.range ι, ρ γ (D.theta φ (mob (γ : SL(2, ℤ))⁻¹ w)) := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp]
  rw [h1, finsum_mem_range (f := fun γ : Γ => ρ γ (D.theta φ (mob (γ : SL(2, ℤ))⁻¹ w))) hι]
  simp only [hterm]
  rw [← finsum_smul, eta_finsum, one_smul]

end TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport
