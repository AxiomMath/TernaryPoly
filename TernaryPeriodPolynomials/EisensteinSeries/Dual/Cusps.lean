module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Transport
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.Face

@[expose] public section


open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

/-!
# The transport of the constant terms of `ℰ_P` to the dual series: `r_P, r_Q, r_B` for `Γ(N)`

Formalized by Claude Sonnet 5.5.

From `r_P ℰ_P(ξ) = ξ, r_Q ℰ_P(ξ) = Tξ, r_B ℰ_P(ξ) = 0` (`eq:constantterms`) for `ȷ(Γ)` to
`r_Q ℰ_Q^∨(η) = η, r_P ℰ_Q^∨(η) = T^∨ η, r_B ℰ_Q^∨(η) = 0` (`eq:dualconstantterms`).  For `Γ = Γ(N)` (preserved by `ȷ`), with the cusps
`h ∈ SL₃(ℤ)` (`Γ_{h⁻¹Ph}`, `Γ_{h⁻¹Qh}`, `Γ_{h⁻¹Bh}`):

* `ConstantTermsAt N n ρ c ξ ζ`: the three families of restriction identities for a class `c ∈ H²(Γ(N), ρ)`;
* `dual_restrictions_transport` (UNCONDITIONAL): the `r_Q` (resp. `r_P`, `r_B`) restriction of `ȷ^* c'` at `h` is the `ȷ`-pullback of the
  `r_P` (resp. `r_Q`, `r_B`) restriction of `c'` at `ȷ(h)`;
* `dual_constant_terms_transport`, `dual_constant_terms_T`: the dual constant terms from the plane statements, with the second constant-term
  map `T^∨ = ȷ^* ∘ T ∘ (ȷ^*)⁻¹` (`dualT`); the face pullbacks are isomorphisms (`pullQP_bijective`, `pullPQ_bijective`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces

section Groups

variable (N : ℕ) (h : SL(3, ℤ))

theorem gammaNQAt_le_N : gammaNQAt N h ≤ gammaN N := by
  intro p hp
  have h1 : h * p * h⁻¹ ∈ gammaN N := ((mem_gammaNQAt N h).1 hp).1
  have h2 := (gammaN_normal N).conj_mem _ h1 h⁻¹
  simpa [mul_assoc] using h2

theorem gammaNBAt_le_N : gammaNBAt N h ≤ gammaN N := by
  intro p hp
  have h1 : h * p * h⁻¹ ∈ gammaN N := (mem_gammaNBAt.1 hp).1
  have h2 := (gammaN_normal N).conj_mem _ h1 h⁻¹
  simpa [mul_assoc] using h2

/-- `ȷ` as an endomorphism of `Γ(N)`. -/
def jN : gammaN N →* gammaN N where
  toFun g := ⟨jmath g.1, jmath_mem_gammaN.2 g.2⟩
  map_one' := Subtype.ext jmath_one
  map_mul' a b := Subtype.ext (jmath_mul a.1 b.1)

theorem jN_val (g : gammaN N) : (jN N g).1 = jmath g.1 := rfl

end Groups

section Faces

variable {N : ℕ} {n : ℕ}

/-- The dual coefficient system of `Γ(N)`: `δ ↦ ρ(ȷ(δ))`. -/
abbrev dualRhoN (N n : ℕ) : Representation ℝ (gammaN N) (Coef n) := dualRho (gammaN N) (gammaN N) (jN N) n

/-- **The dual class** `ȷ^* c'` of a class `c' ∈ H²(Γ(N), E_n)` (for `c'` the class of `ℰ_P(ω_f)`: the class of `ℰ_Q^∨`). -/
def jPull (N n : ℕ) : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n)) →
    groupCohomology.H2 (Rep.of (dualRhoN N n)) :=
  fun c' => (groupCohomology.map (jN N) (resMor (jN N) (dualRhoN N n) (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom c'

/-- The restriction of the dual coefficient system to a subgroup `S ≤ Γ(N)` (the `E^∨|_S`). -/
abbrev facePull {S S' : Subgroup SL(3, ℤ)} (hS : S ≤ gammaN N) (hS' : S' ≤ gammaN N)
    (hSS' : ∀ s : S, jmath s.1 ∈ S') (n : ℕ) :
    groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp (Subgroup.inclusion hS'))) →ₗ[ℝ]
      groupCohomology.H2 (Rep.of ((dualRhoN N n).comp (Subgroup.inclusion hS))) :=
  (groupCohomology.map (jRestr S S' hSS')
    (resMor (jRestr S S' hSS') ((dualRhoN N n).comp (Subgroup.inclusion hS))
      ((gammaRho (gammaN N) n).comp (Subgroup.inclusion hS'))
      (fun s => by
        simp only [MonoidHom.coe_comp, Function.comp_apply, dualRho]
        rw [jRestr_comm (gammaN N) (gammaN N) (jN N) (fun _ => rfl) S S' hS hS' hSS' s])) 2).hom

/-- **Transport of restrictions to an arbitrary pair of subgroups** (specialization of `dual_restriction_transport`). -/
theorem jPull_res {S S' : Subgroup SL(3, ℤ)} (hS : S ≤ gammaN N) (hS' : S' ≤ gammaN N)
    (hSS' : ∀ s : S, jmath s.1 ∈ S') (c' : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n))) :
    resTo S hS (dualRhoN N n) (jPull N n c') = facePull hS hS' hSS' n (resTo S' hS' (gammaRho (gammaN N) n) c') :=
  dual_restriction_transport (gammaN N) (gammaN N) (jN N) (fun _ => rfl) S S' hS hS' hSS' n c'

/-- If `ȷ(S) = S'` exactly, `ȷ` restricts to an isomorphism `S ≃* S'`. -/
def jEquivFace {S S' : Subgroup SL(3, ℤ)} (hSS' : ∀ s : SL(3, ℤ), jmath s ∈ S' ↔ s ∈ S) : S ≃* S' where
  toFun s := ⟨jmath s.1, (hSS' s.1).2 s.2⟩
  invFun s' := ⟨jmath s'.1, (hSS' (jmath s'.1)).1 (by rw [jmath_jmath]; exact s'.2)⟩
  left_inv s := Subtype.ext (jmath_jmath _)
  right_inv s := Subtype.ext (jmath_jmath _)
  map_mul' a b := Subtype.ext (jmath_mul a.1 b.1)

/-- **The face pullback is bijective** when `ȷ(S) = S'`: it is the isomorphism of group cohomology induced by `ȷ : S ≃* S'`
and the identity of the coefficient module. -/
theorem facePull_bijective {S S' : Subgroup SL(3, ℤ)} (hS : S ≤ gammaN N) (hS' : S' ≤ gammaN N)
    (hSS' : ∀ s : SL(3, ℤ), jmath s ∈ S' ↔ s ∈ S) (n : ℕ) :
    Function.Bijective (facePull hS hS' (fun s => (hSS' s.1).2 s.2) n) := by
  let e : S' ≃* S := (jEquivFace hSS').symm
  let e' : (Rep.of ((gammaRho (gammaN N) n).comp (Subgroup.inclusion hS'))).V ≃ₗ[ℝ]
      (Rep.of ((dualRhoN N n).comp (Subgroup.inclusion hS))).V := LinearEquiv.refl ℝ _
  have he : ∀ g, e' ∘ₗ (Rep.of ((gammaRho (gammaN N) n).comp (Subgroup.inclusion hS'))).ρ g =
      (Rep.of ((dualRhoN N n).comp (Subgroup.inclusion hS))).ρ (e g) ∘ₗ e' := by
    intro g
    apply LinearMap.ext
    intro q
    have h1 : jN N (Subgroup.inclusion hS (e g)) = Subgroup.inclusion hS' g :=
      Subtype.ext (by
        change jmath (jmath g.1) = g.1
        exact jmath_jmath _)
    change (gammaRho (gammaN N) n (Subgroup.inclusion hS' g)) q = (dualRhoN N n (Subgroup.inclusion hS (e g))) q
    rw [dualRho_apply, h1]
  have h := CategoryTheory.ConcreteCategory.bijective_of_isIso (groupCohomology.mapIso e e' he 2).hom
  have hfun : (facePull hS hS' (fun s => (hSS' s.1).2 s.2) n) = (groupCohomology.mapIso e e' he 2).hom.hom := by
    unfold facePull
    congr 1
  rw [hfun]
  exact h

end Faces

section Cusps

variable {N n : ℕ}

theorem jmath_Q_to_P (h : SL(3, ℤ)) (s : gammaNQAt N h) : jmath s.1 ∈ gammaNPAt N (jmath h) :=
  jmath_mem_gammaNPAt_iff.2 s.2

theorem jmath_P_to_Q (h : SL(3, ℤ)) (s : gammaNPAt N h) : jmath s.1 ∈ gammaNQAt N (jmath h) :=
  jmath_mem_gammaNQAt_iff.2 s.2

theorem jmath_B_to_B (h : SL(3, ℤ)) (s : gammaNBAt N h) : jmath s.1 ∈ gammaNBAt N (jmath h) :=
  jmath_mem_gammaNBAt_iff.2 s.2

/-- The `ȷ`-pullback `H²(Γ_{ȷ(h)⁻¹ P ȷ(h)}, E) → H²(Γ_{h⁻¹ Q h}, E^∨)`. -/
abbrev pullQP (N n : ℕ) (h : SL(3, ℤ)) :=
  facePull (N := N) (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n

/-- The `ȷ`-pullback `H²(Γ_{ȷ(h)⁻¹ Q ȷ(h)}, E) → H²(Γ_{h⁻¹ P h}, E^∨)`. -/
abbrev pullPQ (N n : ℕ) (h : SL(3, ℤ)) :=
  facePull (N := N) (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h) n

/-- The `ȷ`-pullback of flag restrictions. -/
abbrev pullBB (N n : ℕ) (h : SL(3, ℤ)) :=
  facePull (N := N) (gammaNBAt_le_N N h) (gammaNBAt_le_N N (jmath h)) (jmath_B_to_B h) n

/-- **Transport of the three families of restrictions `r_P, r_Q, r_B`** (unconditional): for every class `c'` of `Γ(N)` with
coefficients `E_n`, the restriction of `ȷ^* c'` to the line cusp (resp. plane cusp, flag) at `h` is the `ȷ`-pullback of the restriction
of `c'` to the plane cusp (resp. line cusp, flag) at `ȷ(h)`.  Applied to `c' = [ℰ_P(ω_f)]` this is the passage from
`eq:constantterms` to `eq:dualconstantterms`. -/
theorem dual_restrictions_transport (c' : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n))) :
    (∀ h : SL(3, ℤ), resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (jPull N n c') =
        pullQP N n h (resTo (gammaNPAt N (jmath h)) (gammaNPAt_le N (jmath h)) (gammaRho (gammaN N) n) c')) ∧
    (∀ h : SL(3, ℤ), resTo (gammaNPAt N h) (gammaNPAt_le N h) (dualRhoN N n) (jPull N n c') =
        pullPQ N n h (resTo (gammaNQAt N (jmath h)) (gammaNQAt_le_N N (jmath h)) (gammaRho (gammaN N) n) c')) ∧
    (∀ h : SL(3, ℤ), resTo (gammaNBAt N h) (gammaNBAt_le_N N h) (dualRhoN N n) (jPull N n c') =
        pullBB N n h (resTo (gammaNBAt N (jmath h)) (gammaNBAt_le_N N (jmath h)) (gammaRho (gammaN N) n) c')) :=
  ⟨fun _ => jPull_res _ _ _ c', fun _ => jPull_res _ _ _ c', fun _ => jPull_res _ _ _ c'⟩

/-- **The constant-term statements** (`eq:constantterms`, `eq:dualconstantterms`) for a class `c ∈ H²(Γ(N), ρ)` with prescribed
plane-cusp values `ξ h`, line-cusp values `ζ h` (restriction to `Γ_{h⁻¹Ph}`, `Γ_{h⁻¹Qh}`) and zero flag restrictions at every
cusp `h`.  For `ρ = gammaRho` and `c = [ℰ_P(ξ)]`, `ξ h` is the seed (`r_P = ξ`), `ζ h = Tξ` (`r_Q`); S6's plane statements are of
this form. -/
def ConstantTermsAt (N n : ℕ) (ρ : Representation ℝ (gammaN N) (Coef n)) (c : groupCohomology.H2 (Rep.of ρ))
    (ξ : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of (ρ.comp (Subgroup.inclusion (gammaNPAt_le N h)))))
    (ζ : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of (ρ.comp (Subgroup.inclusion (gammaNQAt_le_N N h))))) : Prop :=
  (∀ h, resTo (gammaNPAt N h) (gammaNPAt_le N h) ρ c = ξ h) ∧
  (∀ h, resTo (gammaNQAt N h) (gammaNQAt_le_N N h) ρ c = ζ h) ∧
  (∀ h, resTo (gammaNBAt N h) (gammaNBAt_le_N N h) ρ c = 0)

/-- **Transport theorem for the constant terms** (unconditional in the dual statement, conditional only on the plane statements for
`ℰ_P`): if `c'` has plane-cusp values `ξ'`, line-cusp values `ζ'` and zero flag restrictions, then `ȷ^* c'` has plane-cusp
values `ȷ^*ζ'(ȷ h)`, line-cusp values `ȷ^*ξ'(ȷ h)` and zero flag restrictions. -/
theorem dual_constant_terms_transport
    (c' : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n)))
    (ξ' : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp
      (Subgroup.inclusion (gammaNPAt_le N h)))))
    (ζ' : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp
      (Subgroup.inclusion (gammaNQAt_le_N N h)))))
    (H : ConstantTermsAt N n (gammaRho (gammaN N) n) c' ξ' ζ') :
    ConstantTermsAt N n (dualRhoN N n) (jPull N n c')
      (fun h => pullPQ N n h (ζ' (jmath h))) (fun h => pullQP N n h (ξ' (jmath h))) := by
  obtain ⟨hP, hQ, hB⟩ := H
  obtain ⟨t1, t2, t3⟩ := dual_restrictions_transport (N := N) (n := n) c'
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [t2 h, hQ]
  · rw [t1 h, hP]
  · rw [t3 h, hB, map_zero]

theorem pullQP_bijective (h : SL(3, ℤ)) : Function.Bijective (pullQP N n h) :=
  facePull_bijective (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (fun _ => jmath_mem_gammaNPAt_iff) n

theorem pullPQ_bijective (h : SL(3, ℤ)) : Function.Bijective (pullPQ N n h) :=
  facePull_bijective (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (fun _ => jmath_mem_gammaNQAt_iff) n

/-- **The second constant-term map `T^∨`** at the cusp `h`, from a family `T` of first constant-term maps
`T_h : H²(Γ_{h⁻¹Ph}, E) → H²(Γ_{h⁻¹Qh}, E)` (`r_Q ℰ_P(ξ) = Tξ`): `T^∨_h = ȷ^* ∘ T_{ȷ(h)} ∘ (ȷ^*)⁻¹`.  No invertibility or adjoint
normalization of `T` or `T^∨` is assumed. -/
def dualT (T : ∀ h : SL(3, ℤ),
      groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp (Subgroup.inclusion (gammaNPAt_le N h)))) →ₗ[ℝ]
        groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))))
    (h : SL(3, ℤ)) :
    groupCohomology.H2 (Rep.of ((dualRhoN N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))) →ₗ[ℝ]
      groupCohomology.H2 (Rep.of ((dualRhoN N n).comp (Subgroup.inclusion (gammaNPAt_le N h)))) :=
  pullPQ N n h ∘ₗ T (jmath h) ∘ₗ (LinearEquiv.ofBijective (pullQP N n h) (pullQP_bijective h)).symm.toLinearMap

/-- **The dual constant terms `ar:eq:dualconstantterms`, from the plane statements `ar:eq:constantterms`**: if
`r_P c' = ξ'`, `r_Q c' = Tξ'`, `r_B c' = 0` at every cusp, then `ȷ^* c'` satisfies `r_Q = η`, `r_P = T^∨ η`, `r_B = 0` with
`η_h = ȷ^* ξ'(ȷ h)`. -/
theorem dual_constant_terms_T
    (c' : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n)))
    (T : ∀ h : SL(3, ℤ),
      groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp (Subgroup.inclusion (gammaNPAt_le N h)))) →ₗ[ℝ]
        groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))))
    (ξ' : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of ((gammaRho (gammaN N) n).comp
      (Subgroup.inclusion (gammaNPAt_le N h)))))
    (H : ConstantTermsAt N n (gammaRho (gammaN N) n) c' ξ' (fun h => T h (ξ' h))) :
    ∀ h : SL(3, ℤ),
      resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (jPull N n c') = pullQP N n h (ξ' (jmath h)) ∧
      resTo (gammaNPAt N h) (gammaNPAt_le N h) (dualRhoN N n) (jPull N n c') =
        dualT T h (pullQP N n h (ξ' (jmath h))) ∧
      resTo (gammaNBAt N h) (gammaNBAt_le_N N h) (dualRhoN N n) (jPull N n c') = 0 := by
  obtain ⟨hP, hQ, hB⟩ := dual_constant_terms_transport c' ξ' _ H
  intro h
  refine ⟨hQ h, ?_, hB h⟩
  rw [hP h]
  unfold dualT
  simp only [LinearMap.comp_apply]
  rw [LinearEquiv.coe_coe, LinearEquiv.ofBijective_symm_apply_apply]

end Cusps

end TernaryPeriodPolynomials.Argument.EisensteinDual
