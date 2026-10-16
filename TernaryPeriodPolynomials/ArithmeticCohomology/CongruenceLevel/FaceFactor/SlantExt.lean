module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.ShuffleBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSNormalForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalAlt
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalCocycles
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalLevi

@[expose] public section


/-!
# Fibre integration of a primitive of `z ∪ z'`, in extension language (T1 + T2)

Formalized by Claude Sonnet 5.5.

Setting: `ext : GroupExtension RadicalLattice E L`, `s` a splitting with `radDet (splitRadicalInput s A) = 1`, `z`, `z'` relative two-cocycles in normal form
(`z(s a, s b) = 0`, `z(inl r, s l) = 0`) with coefficients `V`, `W'`, an invariant pairing `e` and `γ` a 3-cochain with `dγ = z ∪ z'` (`cup22`) vanishing on triples of radical elements.
`primitive_mu_cup22`: `μ σ = ⟨γ, Sh(ν; σ)⟩` satisfies `μ β - μ(αβ) + μ α = -(K(e₁,e₂) - K(e₂,e₁))`, `K(e_i, e_j) = e(c̃ α e_i, ρ'(e_i)((α·c̃' β) e_j))`, i.e. `- altForm (c̃ α) (α·c̃' β) e₁ e₂`.
`mu_cup12`: `⟨cup12 w z', Sh(ν; σ)⟩ = -altForm (w|_N) (c̃' σ) e₁ e₂`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

variable {E L : Type} [Group E] [Group L] {ext : GroupExtension RadicalLattice E L} (s : ext.Splitting)

/-- The shuffle model of the split extension of `ℤ²`, and the torus basis in additive coordinates. -/
abbrev pmE : PairModel E (Additive RadicalLattice) L := pairModelOfSplitting s

theorem hmu_of_det (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (α : L) :
    ∃ m : (Additive RadicalLattice × Additive RadicalLattice × Additive RadicalLattice) →₀ ℚ,
      torusBd3 (Additive RadicalLattice) m =
        nuChain ((pmE s).ψ α⁻¹ (Additive.ofMul latE1)) ((pmE s).ψ α⁻¹ (Additive.ofMul latE2)) -
          nuChain (Additive.ofMul latE1) (Additive.ofMul latE2) := by
  rw [pm_psi_inv, pm_psi_inv]
  exact hmu_of_torus (splitRadicalInput s α) (hdet α)

section Cup

variable {V W' : Rep ℂ E} [Module ℚ V] [Module ℚ W'] (ρ' : Representation ℚ E W')
  (hρ' : ∀ g x, ρ' g x = W'.ρ g x) (e : V →ₗ[ℚ] W' →ₗ[ℚ] ℚ)

theorem edge_val_ll_nl (W : Rep ℂ E) (z : relativeTwoCocycles ext.inl W)
    (hmix : ∀ (r : RadicalLattice) (l : L), z.val (ext.inl r, s l) = 0) (α : L) (r : RadicalLattice) :
    z.val ((pmE s).ll α, (pmE s).nl ((pmE s).ψ α⁻¹ (Additive.ofMul r))) = splitEdgeCycle s W α z r := by
  rw [pm_ll, pm_psi_inv, pm_nl_ofMul, splitEdgeCycle_apply, hmix, sub_zero]

include hρ' in
/-- **T2, `z ∪ z'`**: only the placement `[α | α·v₁ | β | (αβ)·v₂]` contributes. -/
theorem sh2_cup22_ext (z : relativeTwoCocycles ext.inl V) (z' : relativeTwoCocycles ext.inl W')
    (hU : ∀ a b : L, z.val (s a, s b) = 0) (hmix : ∀ (r : RadicalLattice) (l : L), z.val (ext.inl r, s l) = 0)
    (hmix' : ∀ (r : RadicalLattice) (l : L), z'.val (ext.inl r, s l) = 0) (v₁ v₂ : RadicalLattice) (α β : L) :
    (pmE s).sh2' (cup22 ρ' e (fun a b => z.val (a, b)) (fun a b => z'.val (a, b))) (Additive.ofMul v₁) (Additive.ofMul v₂) α β =
      -e (splitEdgeCycle s V α z v₁)
        (ρ' (ext.inl v₁) (splitRadicalCocycleAction s W' α (splitEdgeCycle s W' β z') v₂)) := by
  have hl := relativeTwoCocycle_radical_left s V z hmix
  have hl' := relativeTwoCocycle_radical_left s W' z' hmix'
  rw [(pmE s).T2_cup22 ρ' e (fun a b => z.val (a, b)) (fun a b => z'.val (a, b))
    (fun v g => by rw [pm_nl]; exact hl _ _) (fun a b => by rw [pm_ll, pm_ll]; exact hU a b)
    (fun v g => by rw [pm_nl]; exact hl' _ _)]
  have e1 := edge_val_ll_nl s V z hmix α v₁
  have e2 : z'.val ((pmE s).ll β, (pmE s).nl ((pmE s).ψ (α * β)⁻¹ (Additive.ofMul v₂))) =
      splitEdgeCycle s W' β z' (splitRadicalInput s α v₂) := by
    have := edge_val_ll_nl s W' z' hmix' β (splitRadicalInput s α v₂)
    rw [← this, pm_psi_inv, pm_psi_inv, splitRadicalInput_mul]
  rw [e1, e2, pm_pr, map_mul, Module.End.mul_apply, splitRadicalCocycleAction_apply]
  simp only [hρ']

/-- **T2, `w ∪ z'`**: `⟨cup12 w z', Sh(ν; σ)⟩ = -(e(w e₁, e₁ · c̃'σ e₂) - e(w e₂, e₂ · c̃'σ e₁))`. -/
theorem mu_cup12_ext (w : E → V) (z' : relativeTwoCocycles ext.inl W')
    (hmix' : ∀ (r : RadicalLattice) (l : L), z'.val (ext.inl r, s l) = 0) (σ : L) :
    (pmE s).mu (cup12 ρ' e w (fun a b => z'.val (a, b))) (Additive.ofMul latE1) (Additive.ofMul latE2) σ =
      -(e (w (ext.inl latE1)) (ρ' (ext.inl latE1) (splitEdgeCycle s W' σ z' latE2)) -
        e (w (ext.inl latE2)) (ρ' (ext.inl latE2) (splitEdgeCycle s W' σ z' latE1))) := by
  have hl' := relativeTwoCocycle_radical_left s W' z' hmix'
  have key : ∀ v₁ v₂ : RadicalLattice, (pmE s).sh1 (cup12 ρ' e w (fun a b => z'.val (a, b))) (Additive.ofMul v₁)
      (Additive.ofMul v₂) σ = -e (w (ext.inl v₁)) (ρ' (ext.inl v₁) (splitEdgeCycle s W' σ z' v₂)) := by
    intro v₁ v₂
    rw [(pmE s).T2_cup12 ρ' e w (fun a b => z'.val (a, b)) (fun v g => by rw [pm_nl]; exact hl' _ _),
      pm_nl_ofMul, edge_val_ll_nl s W' z' hmix' σ v₂]
  unfold PairModel.mu
  rw [key, key]
  ring

include hρ' in
/-- **The fibre integration of a primitive of `z ∪ z'`.** `γ` a 3-cochain of `Q` vanishing on triples of radical elements with `dγ = z ∪ z'`, and `μ σ = ⟨γ, Sh(ν; σ)⟩`:
`μ β - μ(αβ) + μ α = -(K(e₁, e₂) - K(e₂, e₁))`, `K(u, v) = e(c̃α u, u · (α·c̃'β) v)`, i.e. `-altForm (c̃ α) (α·c̃' β) e₁ e₂`. -/
theorem fibre_primitive (hdet : ∀ A, radDet (splitRadicalInput s A) = 1)
    (z : relativeTwoCocycles ext.inl V) (z' : relativeTwoCocycles ext.inl W')
    (hU : ∀ a b : L, z.val (s a, s b) = 0) (hmix : ∀ (r : RadicalLattice) (l : L), z.val (ext.inl r, s l) = 0)
    (hmix' : ∀ (r : RadicalLattice) (l : L), z'.val (ext.inl r, s l) = 0)
    (γ : E → E → E → ℚ) (hγ : ∀ a b c : RadicalLattice, γ (ext.inl a) (ext.inl b) (ext.inl c) = 0)
    (hd : dd3T γ = cup22 ρ' e (fun a b => z.val (a, b)) (fun a b => z'.val (a, b))) (α β : L) :
    (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) β -
        (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) (α * β) +
          (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) α =
      -(e (splitEdgeCycle s V α z latE1)
          (ρ' (ext.inl latE1) (splitRadicalCocycleAction s W' α (splitEdgeCycle s W' β z') latE2)) -
        e (splitEdgeCycle s V α z latE2)
          (ρ' (ext.inl latE2) (splitRadicalCocycleAction s W' α (splitEdgeCycle s W' β z') latE1))) := by
  have hl := relativeTwoCocycle_radical_left s V z hmix
  have hl' := relativeTwoCocycle_radical_left s W' z' hmix'
  have h1 : (pmE s).Ge1 γ := fun a b c => by
    rw [pm_nl, pm_nl, pm_nl]; exact hγ _ _ _
  have h2 : (pmE s).ShapeOne (dd3T γ) := by
    apply (pmE s).shapeOne_of_left_third
    intro g₁ g₂ g₃ g₄ h
    rw [hd]
    unfold cup22
    rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · rw [pm_nl]; simp [hl]
    · rw [pm_nl]; simp [hl']
  rw [(pmE s).T1 γ h1 h2 (Additive.ofMul latE1) (Additive.ofMul latE2) (hmu_of_det s hdet) α β, hd,
    sh2_cup22_ext s ρ' hρ' e z z' hU hmix hmix' latE1 latE2 α β,
    sh2_cup22_ext s ρ' hρ' e z z' hU hmix hmix' latE2 latE1 α β]
  ring

end Cup

section Alt

variable {V W' : Rep ℂ E} [Module ℚ V] [Module ℚ W'] (ρ' : Representation ℚ E W')
  (hρ' : ∀ g x, ρ' g x = W'.ρ g x) (e : V →ₗ[ℚ] W' →ₗ[ℚ] ℚ) (eC : V →ₗ[ℂ] W' →ₗ[ℂ] ℂ) (r : ℂ →ₗ[ℚ] ℚ)
  (he : ∀ x y, e x y = r (eC x y))

include hρ' he in
/-- `fibre_primitive` with the pairing `e = r ∘ eC`: the right-hand side is `-r (altForm (c̃ α) (α·c̃' β) e₁ e₂)`. -/
theorem fibre_primitive_alt (hdet : ∀ A, radDet (splitRadicalInput s A) = 1)
    (z : relativeTwoCocycles ext.inl V) (z' : relativeTwoCocycles ext.inl W')
    (hU : ∀ a b : L, z.val (s a, s b) = 0) (hmix : ∀ (r : RadicalLattice) (l : L), z.val (ext.inl r, s l) = 0)
    (hmix' : ∀ (r : RadicalLattice) (l : L), z'.val (ext.inl r, s l) = 0)
    (γ : E → E → E → ℚ) (hγ : ∀ a b c : RadicalLattice, γ (ext.inl a) (ext.inl b) (ext.inl c) = 0)
    (hd : dd3T γ = cup22 ρ' e (fun a b => z.val (a, b)) (fun a b => z'.val (a, b))) (α β : L) :
    (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) β -
        (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) (α * β) +
          (pmE s).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) α =
      -r (altForm (Rep.res ext.inl W').ρ eC (splitEdgeCycle s V α z)
        (splitRadicalCocycleAction s W' α (splitEdgeCycle s W' β z')) latE1 latE2) := by
  rw [fibre_primitive s ρ' hρ' e hdet z z' hU hmix hmix' γ hγ hd α β]
  unfold altForm
  simp only [he, map_sub]
  simp only [hρ']
  rfl

include hρ' he in
/-- `mu_cup12_ext` as `-r (altForm (w|_N) (c̃'σ) e₁ e₂)`. -/
theorem mu_cup12_alt (w : E → V) (z' : relativeTwoCocycles ext.inl W')
    (hmix' : ∀ (r : RadicalLattice) (l : L), z'.val (ext.inl r, s l) = 0) (σ : L) :
    (pmE s).mu (cup12 ρ' e w (fun a b => z'.val (a, b))) (Additive.ofMul latE1) (Additive.ofMul latE2) σ =
      -r (altForm (Rep.res ext.inl W').ρ eC (fun u => w (ext.inl u)) (splitEdgeCycle s W' σ z') latE1 latE2) := by
  rw [mu_cup12_ext s ρ' e w z' hmix' σ]
  unfold altForm
  simp only [he, map_sub]
  simp only [hρ']
  rfl

end Alt

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
