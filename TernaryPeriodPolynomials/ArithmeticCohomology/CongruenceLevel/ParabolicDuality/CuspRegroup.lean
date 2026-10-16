module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspFan

@[expose] public section


/-!
# Orbit representatives of oriented dual edges adapted to the cusps of `Γ(N)`

Formalized by Claude Sonnet 5.5.  Context: `ar:eq:facepair`.

For `N ≥ 3` choose a system `cuspReps` of representatives of the `Γ(N)`-orbits of cusps and for each cusp `c` an element `cuspElt c ∈ SL₂(ℤ)`
with `cuspElt c • cusp₁ = c`.  Then the oriented dual edges `(cuspElt c * Tk k) • p0.swap` (`c` a representative, `0 ≤ k < N`) form a system of
representatives `edgeReps` of the `Γ(N)`-orbits of oriented dual edges: they are the edges whose head is `c`, modulo the stabilizer
`⟨cuspElt c * Tk N * (cuspElt c)⁻¹⟩` of `c` in `Γ(N)`.  `sum_edgeReps` rewrites an orbit sum over oriented edges as a sum over the cusp orbits
and over one period of the fan at each cusp.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

theorem exists_sl_cusp (c : RationalLine2) : ∃ g : IntegralGL, IsSL g ∧ g • cusp1 = c := by
  obtain ⟨v, hv⟩ := exists_gen c
  exact ⟨primitiveCompletion v hv.1, primitiveCompletion_det v hv.1,
    smul_cusp1_eq hv (Or.inl (primitiveCompletion_first_column v hv.1))⟩

/-- A choice of `SL₂(ℤ)` element carrying `cusp₁` to `c`. -/
def cuspElt (c : RationalLine2) : IntegralGL := Classical.choose (exists_sl_cusp c)

theorem cuspElt_sl (c : RationalLine2) : IsSL (cuspElt c) := (Classical.choose_spec (exists_sl_cusp c)).1

theorem cuspElt_cusp1 (c : RationalLine2) : cuspElt c • cusp1 = c := (Classical.choose_spec (exists_sl_cusp c)).2

section Reps

variable {N : ℕ}

theorem gammaN_finiteOrbitsCusp (hN : 3 ≤ N) : Finite (MulAction.orbitRel.Quotient (gammaNGL N) RationalLine2) := by
  have := gammaN_finiteIndex hN
  have : (gammaNGL N).subtype.range.FiniteIndex := by
    rw [Subgroup.range_subtype]; exact gammaN_finiteIndex hN
  obtain ⟨I, hI, hcov⟩ := TernaryPeriodPolynomials.Argument.HeckeNormalization.exists_finite_orbit_reps
    (X := RationalLine2) (gammaNGL N).subtype (x₀ := cusp1) (fun y => by
      obtain ⟨g, -, hg⟩ := exists_sl_cusp y
      exact ⟨g, hg⟩)
  have := hI.to_subtype
  refine Finite.of_surjective (fun i : I => (Quotient.mk (MulAction.orbitRel (gammaNGL N) RationalLine2) i.1)) ?_
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨i, hi, σ, hσ⟩ := hcov x
    refine ⟨⟨i, hi⟩, ?_⟩
    refine Quotient.sound (MulAction.orbitRel_apply.mpr ?_)
    exact ⟨σ⁻¹, by rw [hσ]; change ((σ⁻¹ : gammaNGL N) : IntegralGL) • ((σ : IntegralGL) • i) = i; simp⟩

/-- Representatives of the `Γ(N)`-orbits of cusps. -/
def cuspReps (hN : 3 ≤ N) : RepSystem (gammaNGL N) RationalLine2 := repSystemOfFinite (gammaN_finiteOrbitsCusp hN)

theorem edgeRep_head (c : RationalLine2) (k : ℤ) : head ((cuspElt c * Tk k) • p0.swap) = c := by
  rw [head_smul ((cuspElt_sl c).mul (Tk_isSL k)), head_swap, tail_p0, mul_smul, Tk_cusp1, cuspElt_cusp1]

theorem edgeRep_eq_aux (c : RationalLine2) (m : ℤ) (n j k : ℤ) (hm : m = n * j + k) (hn : Tk (n * j) ∈ gammaNGL N) :
    ∃ σ : IntegralGL, σ ∈ gammaNGL N ∧ (cuspElt c * Tk m) • p0.swap = σ • ((cuspElt c * Tk k) • p0.swap) := by
  refine ⟨cuspElt c * Tk (n * j) * (cuspElt c)⁻¹, gammaN_conj hn, ?_⟩
  rw [hm, Tk_add]
  rw [← mul_smul]
  congr 1
  group

/-- **Representatives of the oriented dual edges** adapted to the cusps. -/
def edgeReps (hN : 3 ≤ N) : RepSystem (gammaNGL N) OTE where
  R := ((cuspReps hN).R ×ˢ Finset.range N).image (fun p => (cuspElt p.1 * Tk (p.2 : ℤ)) • p0.swap)
  cover := by
    intro q
    obtain ⟨c, hc, γ, hγ⟩ := (cuspReps hN).cover (head q)
    have hγsl : IsSL (γ : IntegralGL) := gammaN_isSL hN γ.2
    have hq' : head ((γ : IntegralGL)⁻¹ • q) = c := by
      rw [head_smul hγsl.inv, ← hγ]
      exact inv_smul_smul _ _
    have hq'' : head ((cuspElt c)⁻¹ • ((γ : IntegralGL)⁻¹ • q)) = cusp1 := by
      rw [head_smul (cuspElt_sl c).inv, hq', inv_smul_eq_iff.mpr (cuspElt_cusp1 c).symm]
    obtain ⟨m, hm⟩ := fan_classification hq''
    have hNpos : (0 : ℤ) < N := by exact_mod_cast (by omega : 0 < N)
    have hk0 : 0 ≤ m % (N : ℤ) := Int.emod_nonneg _ hNpos.ne'
    have hk1 : m % (N : ℤ) < N := Int.emod_lt_of_pos _ hNpos
    have hmk : m = (N : ℤ) * (m / N) + m % (N : ℤ) := by
      have := Int.mul_ediv_add_emod m N
      linarith
    obtain ⟨σ, hσ, hσq⟩ := edgeRep_eq_aux (N := N) c m (N : ℤ) (m / N) (m % (N : ℤ)) hmk (Tk_mem_gammaN _)
    refine ⟨(cuspElt c * Tk ((m % (N : ℤ)).toNat : ℤ)) • p0.swap, ?_, ⟨γ.1 * σ, mul_mem γ.2 hσ⟩, ?_⟩
    · refine Finset.mem_image.mpr ⟨(c, (m % (N : ℤ)).toNat), Finset.mem_product.mpr ⟨hc, ?_⟩, rfl⟩
      rw [Finset.mem_range]
      omega
    · have hk : (((m % (N : ℤ)).toNat : ℕ) : ℤ) = m % (N : ℤ) := Int.toNat_of_nonneg hk0
      have hq : q = (γ : IntegralGL) • ((cuspElt c * Tk m) • p0.swap) := by
        rw [mul_smul, ← hm, smul_inv_smul, smul_inv_smul]
      change (γ.1 * σ) • ((cuspElt c * Tk (((m % (N : ℤ)).toNat : ℕ) : ℤ)) • p0.swap) = q
      rw [hk]
      calc (γ.1 * σ) • ((cuspElt c * Tk (m % (N : ℤ))) • p0.swap)
          = γ.1 • (σ • ((cuspElt c * Tk (m % (N : ℤ))) • p0.swap)) := mul_smul _ _ _
        _ = γ.1 • ((cuspElt c * Tk m) • p0.swap) := by rw [← hσq]
        _ = q := hq.symm
  inj := by
    intro r hr r' hr' γ hγ
    obtain ⟨⟨c, k⟩, hck, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨⟨c', k'⟩, hck', rfl⟩ := Finset.mem_image.mp hr'
    obtain ⟨hc, hk⟩ := Finset.mem_product.mp hck
    obtain ⟨hc', hk'⟩ := Finset.mem_product.mp hck'
    simp only [Finset.mem_range] at hk hk'
    have hγsl : IsSL (γ : IntegralGL) := gammaN_isSL hN γ.2
    have hγ' : (γ : IntegralGL) • ((cuspElt c * Tk (k : ℤ)) • p0.swap) = (cuspElt c' * Tk (k' : ℤ)) • p0.swap := hγ
    have hh := congrArg head hγ'
    rw [head_smul hγsl, edgeRep_head, edgeRep_head] at hh
    have hcc : c = c' := (cuspReps hN).inj c hc c' hc' γ hh
    subst hcc
    have hesl : IsSL (cuspElt c) := cuspElt_sl c
    obtain ⟨e, he⟩ : ∃ e, e = cuspElt c := ⟨_, rfl⟩
    rw [← he] at hγ' hesl
    have hτ : ((e⁻¹ * (γ : IntegralGL) * e) • (Tk (k : ℤ) • p0.swap) : OTE) = Tk (k' : ℤ) • p0.swap := by
      calc (e⁻¹ * (γ : IntegralGL) * e) • (Tk (k : ℤ) • p0.swap)
          = e⁻¹ • ((γ : IntegralGL) • ((e * Tk (k : ℤ)) • p0.swap)) := by simp only [mul_smul]
        _ = e⁻¹ • ((e * Tk (k' : ℤ)) • p0.swap) := by rw [hγ']
        _ = Tk (k' : ℤ) • p0.swap := by rw [mul_smul, inv_smul_smul]
    have hτmem : e⁻¹ * (γ : IntegralGL) * e ∈ gammaNGL N := by
      have := gammaN_conj (k := e⁻¹) (g := (γ : IntegralGL)) γ.2
      rwa [inv_inv] at this
    have hτ1 : (e⁻¹ * (γ : IntegralGL) * e) • cusp1 = cusp1 := by
      have h2 := congrArg head hτ
      rw [head_smul ((hesl.inv.mul hγsl).mul hesl), Tk_swap_head, Tk_swap_head] at h2
      exact h2
    obtain ⟨j, hj⟩ := gammaN_stab_cusp1 hN hτmem hτ1
    rw [hj, ← mul_smul, ← Tk_add] at hτ
    have hkk := Tk_swap_inj hτ
    have hNpos : (3 : ℤ) ≤ N := by exact_mod_cast hN
    have hk_i : (k : ℤ) < N := by exact_mod_cast hk
    have hk'_i : (k' : ℤ) < N := by exact_mod_cast hk'
    have hk0 : (0 : ℤ) ≤ k := Nat.cast_nonneg _
    have hk0' : (0 : ℤ) ≤ k' := Nat.cast_nonneg _
    have hj0 : j = 0 := by
      rcases lt_trichotomy j 0 with h | h | h
      · exfalso; nlinarith
      · exact h
      · exfalso; nlinarith
    subst hj0
    have hkk' : k' = k := by
      have : (k : ℤ) = k' := by simpa using hkk
      omega
    subst hkk'
    rfl

/-- **Orbit sums over oriented dual edges, cusp by cusp**: one period of the fan at each cusp representative. -/
theorem sum_edgeReps (hN : 3 ≤ N) (ψ : OTE → ℂ) :
    ∑ r ∈ (edgeReps hN).R, ψ r =
      ∑ c ∈ (cuspReps hN).R, ∑ k ∈ Finset.range N, ψ ((cuspElt c * Tk (k : ℤ)) • p0.swap) := by
  show ∑ r ∈ ((cuspReps hN).R ×ˢ Finset.range N).image (fun p => (cuspElt p.1 * Tk (p.2 : ℤ)) • p0.swap), ψ r = _
  rw [Finset.sum_image, Finset.sum_product]
  rintro ⟨c, k⟩ _ ⟨c', k'⟩ _ h
  have hh := congrArg head h
  simp only [edgeRep_head] at hh
  subst hh
  have h2 : Tk (k : ℤ) • p0.swap = Tk (k' : ℤ) • p0.swap := by
    simp only [mul_smul] at h
    exact MulAction.injective (cuspElt c) h
  have := Tk_swap_inj h2
  have hkk : k = k' := by exact_mod_cast this
  rw [hkk]

end Reps

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
