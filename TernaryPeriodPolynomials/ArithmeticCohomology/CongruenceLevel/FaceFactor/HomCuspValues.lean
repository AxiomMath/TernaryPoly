module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Farey.StokesTau
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CuspHomSum

@[expose] public section


/-!
# The cusp values of rational homomorphisms of `Γ(N)` fill the sum-zero hyperplane (the Laplacian of the cusp graph)

Formalized by Claude Sonnet 5.5.  Step (B) of the face factorisation (`BaseSumZero`): the image of `Hom(Γ(N), ℚ) → ℚ^{cusp orbits}` is the sum-zero hyperplane.

For `ψ : (cuspReps hN).R → ℚ` the cusp function `Φ_ψ` (equivariant extension, trivial action) has the Farey differential `G_ψ = dΦ_ψ ∈ C¹` with rational values, whose cocycle `coc G_ψ` is an additive
homomorphism `Γ(N) → ℂ` with rational values, and `coc G_ψ (σ_c) = lap ψ c = ∑_{k<N} (ψ c − ψ (rep (tail q_{c,k})))`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

section Def

variable {N : ℕ} (hN : 3 ≤ N)

/-- The trivial one-dimensional representation. -/
abbrev trivRep : Rep ℂ (gammaNGL N) := Rep.trivial ℂ (gammaNGL N) ℂ

theorem trivRep_apply (g : gammaNGL N) (v : ℂ) : (trivRep (N := N)).ρ g v = v := rfl

/-- The multiplication coupling of the trivial representation. -/
def trivCoupling : Coupling (trivRep (N := N)).ρ (trivRep (N := N)).ρ :=
  { e := LinearMap.mul ℂ ℂ
    inv := fun γ v w => rfl
    left := fun v hv => by have := hv 1; rwa [LinearMap.mul_apply', mul_one] at this
    right := fun w hw => by have := hw 1; rwa [LinearMap.mul_apply', one_mul] at this }

/-- The orbit representative of a cusp. -/
def cuspRepOf (x : RationalLine2) : ↥(cuspReps hN).R := (dec (cuspReps hN) x).1

theorem cuspRepOf_smul (g : gammaNGL N) (x : RationalLine2) :
    cuspRepOf hN ((g : IntegralGL) • x) = cuspRepOf hN x := by
  have h1 : (dec (cuspReps hN) x).2 • ((dec (cuspReps hN) x).1 : RationalLine2) = x := dec_spec (cuspReps hN) x
  have h2 : (dec (cuspReps hN) ((g : IntegralGL) • x)).2 • ((dec (cuspReps hN) ((g : IntegralGL) • x)).1 : RationalLine2) =
      (g : IntegralGL) • x := dec_spec (cuspReps hN) ((g : IntegralGL) • x)
  apply Subtype.ext
  refine (cuspReps hN).inj _ (dec (cuspReps hN) ((g : IntegralGL) • x)).1.2 _ (dec (cuspReps hN) x).1.2
    ((dec (cuspReps hN) x).2⁻¹ * g⁻¹ * (dec (cuspReps hN) ((g : IntegralGL) • x)).2) ?_
  have h3 : g⁻¹ • ((g : IntegralGL) • x) = x := inv_smul_smul g x
  rw [mul_smul, mul_smul, h2, h3]
  rw [inv_smul_eq_iff]
  exact h1.symm

theorem cuspRepOf_rep (c : ↥(cuspReps hN).R) : cuspRepOf hN (c : RationalLine2) = c := by
  have h1 : (dec (cuspReps hN) (c : RationalLine2)).2 • ((dec (cuspReps hN) (c : RationalLine2)).1 : RationalLine2) = c :=
    dec_spec (cuspReps hN) (c : RationalLine2)
  apply Subtype.ext
  exact (cuspReps hN).inj _ (dec (cuspReps hN) (c : RationalLine2)).1.2 _ c.2 _ h1

/-- The equivariant (constant on orbits) extension of `ψ` to all cusps. -/
def PhiOf (ψ : ↥(cuspReps hN).R → ℚ) (x : RationalLine2) : ℂ := (ψ (cuspRepOf hN x) : ℂ)

theorem PhiOf_mem (ψ : ↥(cuspReps hN).R → ℚ) :
    PhiOf hN ψ ∈ EqFn (gammaNGL N) RationalLine2 (trivRep (N := N)).ρ := fun γ x => by
  change PhiOf hN ψ ((γ : IntegralGL) • x) = PhiOf hN ψ x
  unfold PhiOf
  rw [cuspRepOf_smul]

/-- The Farey differential `dΦ_ψ`. -/
def Gcoch (ψ : ↥(cuspReps hN).R → ℚ) : C1 (trivRep (N := N)).ρ :=
  bdryTw (trivRep (N := N)).ρ hN ⟨PhiOf hN ψ, eqFn_le_Tw _ (PhiOf_mem hN ψ)⟩

theorem Gcoch_apply (ψ : ↥(cuspReps hN).R → ℚ) (q : OTE) :
    (Gcoch hN ψ).1 q = PhiOf hN ψ (head q) - PhiOf hN ψ (tail q) := rfl

theorem Gcoch_rat (ψ : ↥(cuspReps hN).R → ℚ) (q : OTE) : ∃ r : ℚ, (Gcoch hN ψ).1 q = (r : ℂ) :=
  ⟨ψ (cuspRepOf hN (head q)) - ψ (cuspRepOf hN (tail q)), by rw [Gcoch_apply]; unfold PhiOf; push_cast; ring⟩

theorem evalChain_rat {F : OTE → ℂ} (hF : ∀ q, ∃ r : ℚ, F q = (r : ℂ)) (c : PE) : ∃ s : ℚ, evalChain F c = (s : ℂ) := by
  choose F' hF' using hF
  refine ⟨c.coeff.sum fun p r => r * F' p, ?_⟩
  unfold evalChain
  rw [Finsupp.sum, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hF' p, smul_eq_mul]

theorem coc_rat (ψ : ↥(cuspReps hN).R → ℚ) (γ : gammaNGL N) : ∃ r : ℚ, coc (trivRep (N := N)).ρ (Gcoch hN ψ) γ = (r : ℂ) :=
  evalChain_rat (Gcoch_rat hN ψ) _

theorem coc_add (ψ : ↥(cuspReps hN).R → ℚ) (g h : gammaNGL N) :
    coc (trivRep (N := N)).ρ (Gcoch hN ψ) (g * h) = coc (trivRep (N := N)).ρ (Gcoch hN ψ) g + coc (trivRep (N := N)).ρ (Gcoch hN ψ) h := by
  rw [coc_mul]
  change coc _ _ h + coc _ _ g = _
  ring

/-- The graph Laplacian of the cusp graph. -/
def lapF (ψ : ↥(cuspReps hN).R → ℚ) (c : ↥(cuspReps hN).R) : ℚ :=
  ∑ k ∈ Finset.range N, (ψ c - ψ (cuspRepOf hN (tail ((cuspElt (c : RationalLine2) * Tk (k : ℤ)) • p0.swap))))

theorem coc_cusp (ψ : ↥(cuspReps hN).R → ℚ) (c : ↥(cuspReps hN).R) :
    coc (trivRep (N := N)).ρ (Gcoch hN ψ) (cuspSigma (c : RationalLine2)) = (lapF hN ψ c : ℂ) := by
  have h := fan_G_sum (Gcoch hN ψ) (c : RationalLine2)
  have e : ∀ (P : ℂ), (trivRep (N := N)).ρ (cuspSigma (c : RationalLine2)) P = P := fun P => rfl
  rw [e] at h
  have h2 : coc (trivRep (N := N)).ρ (Gcoch hN ψ) (cuspSigma (c : RationalLine2)) =
      ∑ k ∈ Finset.range N, (Gcoch hN ψ).1 ((cuspElt (c : RationalLine2) * Tk (k : ℤ)) • p0.swap) := by
    rw [h]; ring
  rw [h2]
  unfold lapF
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Gcoch_apply, edgeRep_head]
  unfold PhiOf
  rw [cuspRepOf_rep]

theorem lapF_sum_zero (ψ : ↥(cuspReps hN).R → ℚ) : ∑ c, lapF hN ψ c = 0 := by
  have h := hom_cusp_sum_zero hN (fun γ => coc (trivRep (N := N)).ρ (Gcoch hN ψ) γ) (coc_add hN ψ)
  rw [← Finset.sum_coe_sort (cuspReps hN).R (fun c => coc (trivRep (N := N)).ρ (Gcoch hN ψ) (cuspSigma c))] at h
  have h2 : ∑ c : ↥(cuspReps hN).R, coc (trivRep (N := N)).ρ (Gcoch hN ψ) (cuspSigma (c : RationalLine2)) =
      ((∑ c, lapF hN ψ c : ℚ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun c _ => coc_cusp hN ψ c
  rw [h2] at h
  exact_mod_cast h

theorem lap_ker_const (ψ : ↥(cuspReps hN).R → ℚ) (hlap : ∀ c, lapF hN ψ c = 0) (c c' : ↥(cuspReps hN).R) : ψ c = ψ c' := by
  have hkey := pV_bdry_eq hN (trivCoupling (N := N)) (PhiOf_mem hN ψ) (Gcoch hN ψ)
  have h0 : pV (trivCoupling (N := N)) (gammaNFareyData hN) (Gcoch hN ψ) (Gcoch hN ψ) = 0 := by
    change pV (trivCoupling (N := N)) (gammaNFareyData hN) (bdryTw (trivRep (N := N)).ρ hN
      ⟨PhiOf hN ψ, eqFn_le_Tw _ (PhiOf_mem hN ψ)⟩) (Gcoch hN ψ) = 0
    rw [hkey]
    have : ∀ c ∈ (cuspReps hN).R, (trivCoupling (N := N)).e (PhiOf hN ψ c)
        (coc (trivRep (N := N)).ρ (Gcoch hN ψ) (cuspSigma c)) = 0 := by
      intro c hc
      have h1 := coc_cusp hN ψ ⟨c, hc⟩
      have h2 : lapF hN ψ ⟨c, hc⟩ = 0 := hlap _
      change PhiOf hN ψ c * coc (trivRep (N := N)).ρ (Gcoch hN ψ) (cuspSigma c) = 0
      rw [h1, h2]
      simp
    rw [Finset.sum_eq_zero this, mul_zero]
  rw [pV_apply] at h0
  unfold pairR at h0
  choose a ha using Gcoch_rat hN ψ
  have h1 : ∑ r ∈ (gammaNFareyData hN).RE.R, (a r * a r : ℚ) = 0 := by
    have : (((∑ r ∈ (gammaNFareyData hN).RE.R, (a r * a r : ℚ)) : ℚ) : ℂ) = 0 := by
      push_cast
      rw [← h0]
      refine Finset.sum_congr rfl fun r _ => ?_
      change _ = (Gcoch hN ψ).1 r * (Gcoch hN ψ).1 r
      rw [ha r]
    exact_mod_cast this
  have h2 : ∀ r ∈ (gammaNFareyData hN).RE.R, a r = 0 := by
    intro r hr
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => mul_self_nonneg (a r))).mp h1 r hr
    exact mul_self_eq_zero.mp this
  have h3 : (Gcoch hN ψ).1 = 0 :=
    eq_zero_of_rep_zero (trivRep (N := N)).ρ (gammaNFareyData hN).RE (Gcoch hN ψ).2.1 (fun r hr => by rw [ha r, h2 r hr]; simp)
  have h4 : ∀ q : OTE, PhiOf hN ψ (head q) = PhiOf hN ψ (tail q) := fun q => by
    have := congrFun h3 q
    rw [Gcoch_apply] at this
    exact sub_eq_zero.mp this
  have h5 := cusp_const h4
  have h6 : (ψ c : ℂ) = (ψ c' : ℂ) := by
    have e1 := h5 (c : RationalLine2)
    have e2 := h5 (c' : RationalLine2)
    unfold PhiOf at e1 e2
    rw [cuspRepOf_rep] at e1 e2
    rw [e1, e2]
  exact_mod_cast h6

/-- The Laplacian as a ℚ-linear map. -/
def lapL : (↥(cuspReps hN).R → ℚ) →ₗ[ℚ] (↥(cuspReps hN).R → ℚ) where
  toFun ψ := lapF hN ψ
  map_add' ψ φ := by
    funext c
    simp only [lapF, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  map_smul' a ψ := by
    funext c
    simp only [lapF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The sum functional. -/
def sumL : (↥(cuspReps hN).R → ℚ) →ₗ[ℚ] ℚ := ∑ c : ↥(cuspReps hN).R, LinearMap.proj c

theorem sumL_apply (ψ : ↥(cuspReps hN).R → ℚ) : sumL hN ψ = ∑ c, ψ c := by
  simp [sumL]

theorem cuspReps_nonempty : Nonempty ↥(cuspReps hN).R := by
  obtain ⟨r, hr, -⟩ := (cuspReps hN).cover cusp1
  exact ⟨⟨r, hr⟩⟩

theorem range_lapL : LinearMap.range (lapL hN) = LinearMap.ker (sumL hN) := by
  obtain ⟨c0⟩ := cuspReps_nonempty hN
  apply Submodule.eq_of_le_of_finrank_le
  · rintro _ ⟨ψ, rfl⟩
    rw [LinearMap.mem_ker, sumL_apply]
    exact lapF_sum_zero hN ψ
  · have h1 := LinearMap.finrank_range_add_finrank_ker (lapL hN)
    have h2 := LinearMap.finrank_range_add_finrank_ker (sumL hN)
    have hsurj : LinearMap.range (sumL hN) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro a
      refine ⟨Pi.single c0 a, ?_⟩
      rw [sumL_apply]
      simp
    have h3 : Module.finrank ℚ (LinearMap.range (sumL hN)) = 1 := by
      rw [hsurj]; simp
    have h4 : Module.finrank ℚ (LinearMap.ker (lapL hN)) ≤ 1 := by
      have hle : LinearMap.ker (lapL hN) ≤ Submodule.span ℚ {fun _ => (1 : ℚ)} := by
        intro ψ hψ
        rw [Submodule.mem_span_singleton]
        refine ⟨ψ c0, ?_⟩
        funext c
        have := lap_ker_const hN ψ (fun c' => by
          have := congrFun (LinearMap.mem_ker.mp hψ) c'
          exact this) c0 c
        simp [this]
      calc Module.finrank ℚ (LinearMap.ker (lapL hN)) ≤ Module.finrank ℚ (Submodule.span ℚ {fun _ : ↥(cuspReps hN).R => (1 : ℚ)}) :=
            Submodule.finrank_mono hle
        _ = 1 := finrank_span_singleton (fun h => one_ne_zero (congrFun h c0))
    have h5 : Module.finrank ℚ (↥(cuspReps hN).R → ℚ) = Fintype.card ↥(cuspReps hN).R := by simp
    omega

/-- **(B), Farey core: the cusp values of rational homomorphisms of `Γ(N)` fill the sum-zero hyperplane.**  For every `x : cusp orbit representatives → ℚ` of sum zero there is an additive
homomorphism `φ : Γ(N) → ℚ` with `φ(σ_c) = x c` for all cusp representatives `c`. -/
theorem exists_hom_cusp_values (x : ↥(cuspReps hN).R → ℚ) (hx : ∑ c, x c = 0) :
    ∃ φ : gammaNGL N → ℚ, (∀ g h, φ (g * h) = φ g + φ h) ∧ ∀ c : ↥(cuspReps hN).R, φ (cuspSigma (c : RationalLine2)) = x c := by
  have hmem : x ∈ LinearMap.range (lapL hN) := by
    rw [range_lapL, LinearMap.mem_ker, sumL_apply]
    exact hx
  obtain ⟨ψ, hψ⟩ := hmem
  choose φ hφ using coc_rat hN ψ
  refine ⟨φ, fun g h => ?_, fun c => ?_⟩
  · have := coc_add hN ψ g h
    rw [hφ, hφ, hφ] at this
    exact Rat.cast_injective (α := ℂ) (by push_cast; exact this)
  · have h1 := coc_cusp hN ψ c
    rw [hφ] at h1
    have h2 : lapF hN ψ c = x c := congrFun hψ c
    rw [← h2]
    exact Rat.cast_injective (α := ℂ) h1

end Def

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
