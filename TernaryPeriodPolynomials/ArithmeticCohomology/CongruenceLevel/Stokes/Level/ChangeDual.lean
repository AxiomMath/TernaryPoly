module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeMackey

@[expose] public section


/-!
# The dual of `Fun(G/Δ, E)` is `Fun(G/Δ, E*)`

Formalized by Claude Sonnet 5.5.

For finite `G/Δ` the pairing `(φ, f) ↦ ∑_x φ_x(f_x)` identifies `Fun(G/Δ, E*)` with the linear dual of `Fun(G/Δ, E)`
(`dualPairEquiv`), `G`-equivariantly for `permRep ρ.dual Δ` and `(permRep ρ Δ).dual` (`dualPairEquiv_equivariant`, `dualRepHom`,
`dualRepInv`), compatibly with the orbit idempotents `e_O = jL ∘ qL` of `LevelChangeMackey` (`dualPair_idem`: the transpose of `e_O` on `V*`
is `e_O` on `Fun(G/Δ, E*)`).  Hence the induced classes of `H²(Δ, E*)` give classes of `H²(G, V.dual)` (`dualHom_bijective`) on which the
orbit decomposition of the dual side is the same as for `E*` coefficients.
-/

open CategoryTheory

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

section Dual

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ : Subgroup G)
  [Fintype (G ⧸ Δ)]

open Classical

/-- `φ ↦ (f ↦ Σ_x φ_x (f_x))`. -/
def dualPairL : ((G ⧸ Δ) → Module.Dual ℂ E) →ₗ[ℂ] Module.Dual ℂ ((G ⧸ Δ) → E) where
  toFun φ :=
    { toFun := fun f => ∑ x, φ x (f x)
      map_add' := fun f g => by simp [Finset.sum_add_distrib]
      map_smul' := fun a f => by simp [Finset.mul_sum] }
  map_add' φ ψ := by
    ext f
    simp [Finset.sum_add_distrib]
  map_smul' a φ := by
    ext f
    simp [Finset.mul_sum]

theorem dualPairL_apply (φ : (G ⧸ Δ) → Module.Dual ℂ E) (f : (G ⧸ Δ) → E) :
    dualPairL Δ φ f = ∑ x, φ x (f x) := rfl

/-- The inverse: `ψ ↦ (x ↦ ψ ∘ single_x)`. -/
def dualUnpairL : Module.Dual ℂ ((G ⧸ Δ) → E) →ₗ[ℂ] ((G ⧸ Δ) → Module.Dual ℂ E) where
  toFun ψ x := ψ.comp (LinearMap.single ℂ (fun _ : G ⧸ Δ => E) x)
  map_add' ψ χ := by funext x; ext e; rfl
  map_smul' a ψ := by funext x; ext e; rfl

/-- `Fun(X, E*) ≃ (Fun(X, E))*` for finite `X`. -/
def dualPairEquiv : ((G ⧸ Δ) → Module.Dual ℂ E) ≃ₗ[ℂ] Module.Dual ℂ ((G ⧸ Δ) → E) :=
  LinearEquiv.ofLinearMap (dualPairL Δ) (dualUnpairL Δ)
    (by
      refine LinearMap.ext fun ψ => LinearMap.ext fun f => ?_
      change ∑ x, ψ (Pi.single x (f x)) = ψ f
      rw [← map_sum, Finset.univ_sum_single])
    (by
      refine LinearMap.ext fun φ => funext fun x => LinearMap.ext fun e => ?_
      change ∑ y, φ y (LinearMap.single ℂ (fun _ : G ⧸ Δ => E) x e y) = φ x e
      simp only [LinearMap.coe_single]
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy; simp [Pi.single_eq_of_ne hy]
      · intro h; exact absurd (Finset.mem_univ _) h)

theorem dualPairEquiv_equivariant (g : G) (φ : (G ⧸ Δ) → Module.Dual ℂ E) :
    dualPairEquiv Δ (permRep ρ.dual Δ g φ) = (permRep ρ Δ).dual g (dualPairEquiv Δ φ) := by
  refine LinearMap.ext fun f => ?_
  have hF := Equiv.sum_comp (MulAction.toPerm g⁻¹ : Equiv.Perm (G ⧸ Δ))
    (fun y => φ y (ρ g⁻¹ (f (g • y))))
  have hL : (dualPairEquiv Δ (permRep ρ.dual Δ g φ)) f = ∑ x, φ (g⁻¹ • x) (ρ g⁻¹ (f x)) := rfl
  have hR : ((permRep ρ Δ).dual g (dualPairEquiv Δ φ)) f = ∑ y, φ y (ρ g⁻¹ (f (g • y))) := by
    change ∑ y, φ y ((permRep ρ Δ g⁻¹ f) y) = _
    simp only [permRep_apply, inv_inv]
  rw [hL, hR, ← hF]
  refine Finset.sum_congr rfl fun x _ => ?_
  change _ = φ (g⁻¹ • x) (ρ g⁻¹ (f (g • g⁻¹ • x)))
  rw [smul_inv_smul]

/-- The equivariant morphism `Fun(G/Δ, E*) ⟶ (Fun(G/Δ, E))*`. -/
def dualRepHom : Rep.of (permRep ρ.dual Δ) ⟶ Rep.of (permRep ρ Δ).dual :=
  Rep.ofHom ⟨(dualPairEquiv Δ).toLinearMap, fun g => by
    refine LinearMap.ext fun φ => ?_
    exact dualPairEquiv_equivariant ρ Δ g φ⟩

/-- The inverse morphism. -/
def dualRepInv : Rep.of (permRep ρ Δ).dual ⟶ Rep.of (permRep ρ.dual Δ) :=
  Rep.ofHom ⟨(dualPairEquiv Δ).symm.toLinearMap, fun g => by
    refine LinearMap.ext fun ψ => ?_
    change (dualPairEquiv Δ).symm ((permRep ρ Δ).dual g ψ) = permRep ρ.dual Δ g ((dualPairEquiv Δ).symm ψ)
    rw [LinearEquiv.symm_apply_eq, dualPairEquiv_equivariant, LinearEquiv.apply_symm_apply]⟩

theorem dualRepHom_dualRepInv : dualRepHom ρ Δ ≫ dualRepInv ρ Δ = 𝟙 _ := by
  refine Rep.hom_ext ?_
  exact Representation.IntertwiningMap.ext (LinearMap.ext fun φ => (dualPairEquiv Δ).symm_apply_apply φ)

theorem dualRepInv_dualRepHom : dualRepInv ρ Δ ≫ dualRepHom ρ Δ = 𝟙 _ := by
  refine Rep.hom_ext ?_
  exact Representation.IntertwiningMap.ext (LinearMap.ext fun ψ => (dualPairEquiv Δ).apply_symm_apply ψ)

/-- The transport of degree-two classes `H²(G, Fun(G/Δ, E*)) → H²(G, (Fun(G/Δ, E))*)` is bijective. -/
theorem dualHom_bijective : Function.Bijective (h2Hom (dualRepHom ρ Δ)) := by
  refine ⟨fun a b h => ?_, fun b => ⟨h2Hom (dualRepInv ρ Δ) b, ?_⟩⟩
  · have := congrArg (h2Hom (dualRepInv ρ Δ)) h
    rwa [← h2Hom_comp, ← h2Hom_comp, dualRepHom_dualRepInv, h2Hom_id, h2Hom_id] at this
  · rw [← h2Hom_comp, dualRepInv_dualRepHom, h2Hom_id]

/-- `e_O` on `Fun(G/Δ, E*)` is the transpose of `e_O` on `Fun(G/Δ, E)`. -/
theorem dualPair_idem (S : Subgroup G) (x : G ⧸ Δ) (φ : (G ⧸ Δ) → Module.Dual ℂ E) :
    dualPairEquiv Δ (jL S x (qL S x φ)) = (jL S x ∘ₗ qL S x).dualMap (dualPairEquiv Δ φ) := by
  refine LinearMap.ext fun f => ?_
  change ∑ y, (jL S x (qL S x φ)) y (f y) = ∑ y, φ y ((jL S x (qL S x f)) y)
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ MulAction.orbit ↥S x
  · rw [jL_qL_of_mem S x φ hy, jL_qL_of_mem S x f hy]
  · rw [jL_qL_of_not_mem S x φ hy, jL_qL_of_not_mem S x f hy]
    simp

end Dual

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
