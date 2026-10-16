module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FStar
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ReflectionForm
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.GammaNPlane

@[expose] public section


/-!
# The finite reflection for a group normalized by `J`: levels `SL₂(ℤ)` and `Γ₂(N)`

Paper: Lemma C.3 (`ar:lem:seed`).

For a group `Λ ⊂ GL₂(ℝ)` with `J Λ J = Λ`, `J = diag(-1, 1)` (e.g. `SL₂(ℤ)` and the principal
congruence subgroups `Γ₂(N)`, `leviGroup_J_stable`), `fStarGen Λ hJ f` is the cusp form
`f^*(τ) = \overline{f(-\bar τ)}` of the same weight. For a plane group `D` with Levi block in `Λ`,
the `ε`-twisted combination `reflSeedInvGen` of the seed of `f` and the antiholomorphic seed of
`f^*` is a closed equivariant form on which the reflection acts by `ε ρ(r)`
(`pullForm_refl_reflSeedGen`), with class `[ω_f] + ε (-1)^{n+1} [\overline{ω_{f^*}}]`
(`deRhamClass_reflSeedInvGen`). With `D = gammaNPlaneData N`, `Λ = leviGroup N` this is the
reflection projection at the paper's level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup ComplexConjugate OnePoint
open scoped MatrixGroups Pointwise
open TernaryPoly.SmoothLocalDeRham
open TernaryPeriodPolynomials.Argument

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.Argument.SeedC3

theorem J_inv : (J : GL (Fin 2) ℝ)⁻¹ = J :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, J_sq])

theorem conjAct_J_smul (Λ : Subgroup (GL (Fin 2) ℝ)) (hJ : ∀ γ ∈ Λ, J * γ * J ∈ Λ) :
    ConjAct.toConjAct (J : GL (Fin 2) ℝ) • Λ = Λ := by
  ext γ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
    ConjAct.ofConjAct_toConjAct, J_inv, J_inv]
  constructor
  · intro h
    have := hJ _ h
    have e : J * (J * γ * J) * J = γ := by
      calc J * (J * γ * J) * J = (J * J) * γ * (J * J) := by simp only [mul_assoc]
        _ = γ := by rw [← sq, J_sq]; simp
    rwa [e] at this
  · intro h
    exact hJ _ h

section

variable (Λ : Subgroup (GL (Fin 2) ℝ)) (hJ : ∀ γ ∈ Λ, J * γ * J ∈ Λ) {k : ℤ} (f : CuspForm Λ k)

include hJ

theorem fStarGen_slash_invariant {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Λ) :
    (⇑f ∣[k] J) ∣[k] γ = ⇑f ∣[k] J := by
  have h1 : J * γ = (J * γ * J) * J := by
    rw [mul_assoc (J * γ) J J, ← sq, J_sq, mul_one]
  rw [← SlashAction.slash_mul, h1, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq f _ (hJ γ hγ)]

theorem fStarGen_zero_at_cusps {c : OnePoint ℝ} (hc : IsCusp c Λ) :
    c.IsZeroAt (⇑f ∣[k] J) k := by
  intro g hg
  have hJc : IsCusp (J • c) Λ := by
    have := hc.smul J
    rwa [conjAct_J_smul Λ hJ] at this
  have h1 : J * g = (J * g * J) * J := by
    rw [mul_assoc (J * g) J J, ← sq, J_sq, mul_one]
  have h2 : (J * g * J) • (∞ : OnePoint ℝ) = J • c := by
    rw [mul_smul, mul_smul, J_smul_infty, hg]
  have h3 := CuspFormClass.zero_at_cusps f hJc (J * g * J) h2
  rw [← SlashAction.slash_mul, h1, SlashAction.slash_mul]
  exact h3.slash _ (by simp [J])

/-- **The conjugate cusp form** `f^*(τ) = \overline{f(-\bar τ)}` for a group `Λ` normalized by
`J = diag(-1, 1)`. -/
def fStarGen : CuspForm Λ k where
  toFun := ⇑f ∣[k] J
  slash_action_eq' _ hγ := fStarGen_slash_invariant Λ hJ f hγ
  holo' := (ModularFormClass.holo f).slash _ J
  zero_at_cusps' hc := fStarGen_zero_at_cusps Λ hJ f hc

theorem fStarGen_apply (τ : ℍ) :
    fStarGen Λ hJ f τ = conj (f (ofComplex (-(conj (τ : ℂ))))) := by
  change (⇑f ∣[k] J) τ = _
  rw [slash_J_eq]

end

section Refl

variable (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (hJ : ∀ γ ∈ Λ, J * γ * J ∈ Λ) {n : ℕ}
  (f : CuspForm Λ ((n + 3 : ℕ) : ℤ))

omit [Λ.HasDetOne] in
theorem fStarGen_cuspH {z : ℂ} (hz : 0 < z.im) :
    cuspH Λ n (fStarGen Λ hJ f) z = conj (cuspH Λ n f (-(conj z))) := by
  change fStarGen Λ hJ f (ofComplex z) = _
  rw [fStarGen_apply, ofComplex_apply_of_im_pos hz]
  rfl

variable {G : Type} [Group G] (D : PlaneData G) (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ)

/-- The `ε`-twisted combination `ω_f + ε (-1)^{n+1} \overline{ω_{f^*}}`, for a group `Λ` normalized
by `J`. -/
def reflSeedInvGen (ε : ℝ) : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n) :=
  cuspSeedInv D hΛ (f := f) +
    (ε * (-1 : ℝ) ^ (n + 1)) • cuspSeedConjInv D hΛ (f := fStarGen Λ hJ f)

theorem pullForm_refl_reflSeedGen {ε : ℝ} (hε : ε * ε = 1) :
    ZigZag.pullForm isOpen_faceSet reflAction reflGen 2
        ((reflSeedInvGen Λ hJ f D hΛ ε :
          ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) : Form (F := Coef n) faceSet 2) =
      ε • ZigZag.twForm (reflCoefCLM n) 2
        ((reflSeedInvGen Λ hJ f D hΛ ε :
          ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) : Form (F := Coef n) faceSet 2) := by
  have hrel : ∀ z : ℂ, 0 < z.im →
      cuspH Λ n (fStarGen Λ hJ f) z = conj (cuspH Λ n f (-conj z)) :=
    fun z hz => fStarGen_cuspH Λ hJ f hz
  have h1 := pullForm_refl_seed n (cuspH Λ n f) (cuspH Λ n (fStarGen Λ hJ f))
    (cuspH_holo Λ n f) (cuspH_holo Λ n (fStarGen Λ hJ f)) hrel
  have h2 := pullForm_refl_conjSeed n (cuspH Λ n f) (cuspH Λ n (fStarGen Λ hJ f))
    (cuspH_holo Λ n f) (cuspH_holo Λ n (fStarGen Λ hJ f)) hrel
  have hcc : ((-1 : ℝ) ^ (n + 1)) * ((-1 : ℝ) ^ (n + 1)) = 1 := by
    rw [← mul_pow]; norm_num
  have hR : ((reflSeedInvGen Λ hJ f D hΛ ε :
      ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) : Form (F := Coef n) faceSet 2) =
      d isOpen_faceSet 1 (Psi.etaForm (cuspH Λ n f) (cuspH_holo Λ n f) n) +
        (ε * (-1 : ℝ) ^ (n + 1)) • ZigZag.twForm (conjCLM n) 2
          (d isOpen_faceSet 1 (Psi.etaForm (cuspH Λ n (fStarGen Λ hJ f))
            (cuspH_holo Λ n (fStarGen Λ hJ f)) n)) := rfl
  rw [hR, map_add, _root_.map_smul, h1, h2, ZigZag.twForm_mul]
  simp only [map_add, _root_.map_smul, smul_add, smul_smul]
  have e1 : ε * (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = ε := by rw [mul_assoc, hcc, mul_one]
  have e2 : ε * (ε * (-1 : ℝ) ^ (n + 1)) = (-1 : ℝ) ^ (n + 1) := by
    rw [← mul_assoc, hε, one_mul]
  rw [e1, e2, add_comm]

theorem deRhamClass_reflSeedInvGen (ε : ℝ) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
        (reflSeedInvGen Λ hJ f D hΛ ε) =
      cuspSeedClass D hΛ (f := f) +
        (ε * (-1 : ℝ) ^ (n + 1)) • cuspSeedConjClass D hΛ (f := fStarGen Λ hJ f) := by
  unfold reflSeedInvGen
  rw [map_add, _root_.map_smul, deRhamClass_cuspSeed, deRhamClass_cuspSeedConj]

end Refl

/-! ### The principal congruence level -/

theorem leviGroup_J_stable (N : ℕ) :
    ∀ γ ∈ ConvergenceC4.leviGroup N, J * γ * J ∈ ConvergenceC4.leviGroup N := by
  rintro γ ⟨s, hs, rfl⟩
  refine ⟨jConj s, ?_, (J_mul_mapGL_mul_J s).symm⟩
  change s ∈ CongruenceSubgroup.Gamma N at hs
  change jConj s ∈ CongruenceSubgroup.Gamma N
  rw [CongruenceSubgroup.Gamma_mem] at hs ⊢
  obtain ⟨h00, h01, h10, h11⟩ := hs
  simp only [jConj, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  refine ⟨h00, ?_, ?_, h11⟩ <;> simp [h01, h10]

end TernaryPeriodPolynomials.Argument.SeedC3S4c
