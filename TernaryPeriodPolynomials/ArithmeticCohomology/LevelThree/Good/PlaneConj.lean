module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalHecke

@[expose] public section


/-!
# Conjugation of ambient stabilizer cohomology

Let `ρ` be a representation of a group `G`, `g ∈ G`, and let `H, H' ≤ G` with `g H' g⁻¹ ⊆ H`.
The formula `f ↦ (x ↦ ρ(g)⁻¹ f(g x))` sends `H`-equivariant homogeneous cochains on the ambient
vertices `G` to `H'`-equivariant ones and commutes with the differentials, hence induces a map
`H²(H, ρ) → H²(H', ρ)` (`conjH2`); when also `g⁻¹ H g ⊆ H'` the map with `g⁻¹` is inverse to it
(`conjH2Equiv`). No condition relates `g` to an arithmetic level: this is the transport used to move
the stabilizer of the good plane into block-upper-triangular coordinates by a *rational* frame.

If two local correspondences `S` of `H` and `S'` of `H'` match up to conjugation
(`(g⁻¹ s g)⁻¹ s' ∈ H'` along a bijection), the transport intertwines their local Hecke operators
(`conjH2_cohomologyAction`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneConj

open TernaryPeriodPolynomials.Spectral.LocalHecke

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (g : G) (H H' : Subgroup G)
  (hH : ∀ h ∈ H', g * h * g⁻¹ ∈ H)

theorem rho_apply_apply (a b : G) (w : V) : ρ a (ρ b w) = ρ (a * b) w := by
  rw [map_mul, Module.End.mul_apply]

/-- The conjugated cochain `x ↦ ρ(g)⁻¹ f(g x)`. -/
def conjCochain (k : ℕ) : cochains H ρ k →ₗ[ℂ] cochains H' ρ k where
  toFun f := ⟨fun x => ρ g⁻¹ (f.val (fun i => g * x i)), by
    intro γ x
    have hγ := f.property ⟨g * γ.val * g⁻¹, hH γ.val γ.property⟩ (fun i => g * x i)
    have hx : (fun i => g * (γ.val * x i)) = fun i => (g * γ.val * g⁻¹) * (g * x i) := by
      funext i
      group
    change ρ g⁻¹ (f.val (fun i => g * (γ.val * x i))) = ρ γ.val (ρ g⁻¹ (f.val (fun i => g * x i)))
    rw [hx, hγ]
    change ρ g⁻¹ (ρ (g * γ.val * g⁻¹) _) = ρ γ.val (ρ g⁻¹ _)
    rw [rho_apply_apply ρ, rho_apply_apply ρ]
    congr 2
    group⟩
  map_add' f f' := by
    apply Subtype.ext
    funext x
    change ρ g⁻¹ (f.val (fun i => g * x i) + f'.val (fun i => g * x i)) =
      ρ g⁻¹ (f.val (fun i => g * x i)) + ρ g⁻¹ (f'.val (fun i => g * x i))
    exact map_add _ _ _
  map_smul' a f := by
    apply Subtype.ext
    funext x
    change ρ g⁻¹ (a • f.val (fun i => g * x i)) = a • ρ g⁻¹ (f.val (fun i => g * x i))
    exact map_smul _ _ _

theorem conjCochain_apply (k : ℕ) (f : cochains H ρ k) (x : Fin (k + 1) → G) :
    (conjCochain ρ g H H' hH k f).val x = ρ g⁻¹ (f.val (fun i => g * x i)) := rfl

theorem conjCochain_differentialOne (f : cochains H ρ 1) :
    conjCochain ρ g H H' hH 2 (differentialOne H ρ f) =
      differentialOne H' ρ (conjCochain ρ g H H' hH 1 f) := by
  apply Subtype.ext
  funext x
  change ρ g⁻¹ (f.val ![g * x 1, g * x 2] - f.val ![g * x 0, g * x 2] + f.val ![g * x 0, g * x 1]) =
    ρ g⁻¹ (f.val (fun i => g * ![x 1, x 2] i)) - ρ g⁻¹ (f.val (fun i => g * ![x 0, x 2] i)) +
      ρ g⁻¹ (f.val (fun i => g * ![x 0, x 1] i))
  simp only [translate_pair, map_add, map_sub]

theorem conjCochain_cocycle (C : cocycles H ρ) :
    conjCochain ρ g H H' hH 2 C.val ∈ cocycles H' ρ := by
  funext x
  have hzero := congrFun C.property (fun i => g * x i)
  change ρ g⁻¹ (C.val.val (fun i => g * ![x 1, x 2, x 3] i)) -
      ρ g⁻¹ (C.val.val (fun i => g * ![x 0, x 2, x 3] i)) +
      ρ g⁻¹ (C.val.val (fun i => g * ![x 0, x 1, x 3] i)) -
      ρ g⁻¹ (C.val.val (fun i => g * ![x 0, x 1, x 2] i)) = 0
  simp only [translate_triple]
  rw [← map_sub, ← map_add, ← map_sub]
  change C.val.val ![g * x 1, g * x 2, g * x 3] - C.val.val ![g * x 0, g * x 2, g * x 3] +
    C.val.val ![g * x 0, g * x 1, g * x 3] - C.val.val ![g * x 0, g * x 1, g * x 2] = 0
    at hzero
  rw [hzero, map_zero]

/-- The conjugated cocycle. -/
def conjCycle : cocycles H ρ →ₗ[ℂ] cocycles H' ρ :=
  ((conjCochain ρ g H H' hH 2).comp (cocycles H ρ).subtype).codRestrict _
    (conjCochain_cocycle ρ g H H' hH)

theorem conjCycle_val (C : cocycles H ρ) :
    (conjCycle ρ g H H' hH C).val = conjCochain ρ g H H' hH 2 C.val := rfl

theorem conjCycle_boundaryMap (f : cochains H ρ 1) :
    conjCycle ρ g H H' hH (boundaryMap H ρ f) =
      boundaryMap H' ρ (conjCochain ρ g H H' hH 1 f) := by
  apply Subtype.ext
  exact conjCochain_differentialOne ρ g H H' hH f

/-- **The conjugation transport on `H²`.** -/
def conjH2 : H2 H ρ →ₗ[ℂ] H2 H' ρ :=
  (LinearMap.range (boundaryMap H ρ)).mapQ (LinearMap.range (boundaryMap H' ρ))
    (conjCycle ρ g H H' hH) (by
      rintro C ⟨f, rfl⟩
      exact ⟨conjCochain ρ g H H' hH 1 f, (conjCycle_boundaryMap ρ g H H' hH f).symm⟩)

theorem conjH2_classOf (C : cocycles H ρ) :
    conjH2 ρ g H H' hH (classOf H ρ C) = classOf H' ρ (conjCycle ρ g H H' hH C) := rfl

variable (hH' : ∀ h ∈ H, g⁻¹ * h * g⁻¹⁻¹ ∈ H')

include hH' in
theorem conjH2_left_inv (y : H2 H ρ) :
    conjH2 ρ g⁻¹ H' H hH' (conjH2 ρ g H H' hH y) = y := by
  induction y using Submodule.Quotient.induction_on with
  | _ C =>
  change classOf H ρ (conjCycle ρ g⁻¹ H' H hH' (conjCycle ρ g H H' hH C)) = classOf H ρ C
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change ρ g⁻¹⁻¹ (ρ g⁻¹ (C.val.val (fun i => g * (g⁻¹ * x i)))) = C.val.val x
  rw [rho_apply_apply ρ]
  simp

include hH' in
theorem conjH2_right_inv (y : H2 H' ρ) :
    conjH2 ρ g H H' hH (conjH2 ρ g⁻¹ H' H hH' y) = y := by
  induction y using Submodule.Quotient.induction_on with
  | _ C =>
  change classOf H' ρ (conjCycle ρ g H H' hH (conjCycle ρ g⁻¹ H' H hH' C)) = classOf H' ρ C
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change ρ g⁻¹ (ρ g⁻¹⁻¹ (C.val.val (fun i => g⁻¹ * (g * x i)))) = C.val.val x
  rw [rho_apply_apply ρ]
  simp

/-- **The conjugation transport as a linear equivalence.** -/
def conjH2Equiv : H2 H ρ ≃ₗ[ℂ] H2 H' ρ :=
  LinearEquiv.ofLinearMap (conjH2 ρ g H H' hH) (conjH2 ρ g⁻¹ H' H hH')
    (LinearMap.ext (conjH2_right_inv ρ g H H' hH hH'))
    (LinearMap.ext (conjH2_left_inv ρ g H H' hH hH'))

theorem conjH2Equiv_apply (y : H2 H ρ) : conjH2Equiv ρ g H H' hH hH' y = conjH2 ρ g H H' hH y :=
  rfl

/-! ### Local Hecke operators -/

theorem conjCochain_cochainAction (S : LocalCorrespondence H) (S' : LocalCorrespondence H')
    (e : S.representatives ≃ S'.representatives)
    (he : ∀ s : S.representatives, (g⁻¹ * s.val * g)⁻¹ * (e s).val ∈ H') (k : ℕ)
    (f : cochains H ρ k) :
    conjCochain ρ g H H' hH k (cochainAction ρ S k f) =
      cochainAction ρ S' k (conjCochain ρ g H H' hH k f) := by
  apply Subtype.ext
  funext x
  change ρ g⁻¹ (∑ s ∈ S.representatives, ρ s (f.val (fun i => s⁻¹ * (g * x i)))) =
    ∑ s' ∈ S'.representatives, ρ s' (ρ g⁻¹ (f.val (fun i => g * (s'⁻¹ * x i))))
  rw [map_sum, ← Finset.sum_coe_sort S.representatives, ← Finset.sum_coe_sort S'.representatives]
  refine Fintype.sum_equiv e _ _ (fun s => ?_)
  let l : H' := ⟨_, he s⟩
  let l' : H := ⟨g * l⁻¹.val * g⁻¹, hH _ (H'.inv_mem l.property)⟩
  have hx : (fun i => g * ((e s).val⁻¹ * x i)) = fun i => l'.val * (s.val⁻¹ * (g * x i)) := by
    funext i
    simp only [l', l, Subgroup.coe_inv]
    group
  rw [hx, f.property l' (fun i => s.val⁻¹ * (g * x i)), rho_apply_apply ρ,
    rho_apply_apply ρ, rho_apply_apply ρ]
  congr 2
  simp only [l', l, Subgroup.coe_inv]
  group

/-- **Conjugation intertwines matching local Hecke operators.** -/
theorem conjH2_cohomologyAction (S : LocalCorrespondence H) (S' : LocalCorrespondence H')
    (e : S.representatives ≃ S'.representatives)
    (he : ∀ s : S.representatives, (g⁻¹ * s.val * g)⁻¹ * (e s).val ∈ H') (y : H2 H ρ) :
    conjH2 ρ g H H' hH (cohomologyAction ρ S y) = cohomologyAction ρ S' (conjH2 ρ g H H' hH y) := by
  induction y using Submodule.Quotient.induction_on with
  | _ C =>
  change conjH2 ρ g H H' hH (cohomologyAction ρ S (classOf H ρ C)) =
    cohomologyAction ρ S' (conjH2 ρ g H H' hH (classOf H ρ C))
  rw [cohomologyAction_classOf, conjH2_classOf, conjH2_classOf, cohomologyAction_classOf]
  congr 1
  apply Subtype.ext
  exact conjCochain_cochainAction ρ g H H' hH S S' e he 2 C.val

end TernaryPeriodPolynomials.LevelThree.GoodPlaneConj
