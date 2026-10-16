module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeDual

@[expose] public section


/-!
# The orbit component of an induced module and its contragredient

Formalized by Claude Sonnet 5.5.

Let `V = Fun(S/Stab, E)` be the orbit component of `Res_S Fun(G/Δ, E)` at `x ∈ G/Δ` (`jRep`, `qRep` of `LevelChangeMackey`).  The transposes `qDual = (qL)ᵀ : V^* → W^*`, `jDual = (jL)ᵀ : W^* → V^*` of the orbit projection and
inclusion are `S`-equivariant, `jDual ∘ qDual = id`, `(qDual b)(jL a) = b a` and (`dualPair_jL`) the pairing `Σ_z (jL φ)(z)(f z) = Σ_y φ(y)((qL f)(y))`, i.e. `dualRepHom (jL φ) = qDual (dualRepHom φ)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open MulAction
open scoped Classical

section Comp

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) {Δ : Subgroup G}
  (S : Subgroup G) (x : G ⧸ Δ)

/-- The transpose of the orbit projection. -/
def qDual : Module.Dual ℂ ((↥S ⧸ stabilizer ↥S x) → E) →ₗ[ℂ] Module.Dual ℂ ((G ⧸ Δ) → E) := (qL S x).dualMap

/-- The transpose of the orbit inclusion. -/
def jDual : Module.Dual ℂ ((G ⧸ Δ) → E) →ₗ[ℂ] Module.Dual ℂ ((↥S ⧸ stabilizer ↥S x) → E) := (jL S x).dualMap

theorem qDual_apply (b : Module.Dual ℂ ((↥S ⧸ stabilizer ↥S x) → E)) (f : (G ⧸ Δ) → E) : qDual S x b f = b (qL S x f) := rfl

theorem jDual_apply (b : Module.Dual ℂ ((G ⧸ Δ) → E)) (φ : (↥S ⧸ stabilizer ↥S x) → E) : jDual S x b φ = b (jL S x φ) := rfl

theorem jDual_qDual (b : Module.Dual ℂ ((↥S ⧸ stabilizer ↥S x) → E)) : jDual S x (qDual S x b) = b := by
  refine LinearMap.ext fun φ => ?_
  rw [jDual_apply, qDual_apply, qL_jL]

theorem qDual_jL (b : Module.Dual ℂ ((↥S ⧸ stabilizer ↥S x) → E)) (φ : (↥S ⧸ stabilizer ↥S x) → E) :
    qDual S x b (jL S x φ) = b φ := by
  rw [qDual_apply, qL_jL]

theorem qDual_equivariant (s : ↥S) (b : Module.Dual ℂ ((↥S ⧸ stabilizer ↥S x) → E)) :
    qDual S x ((permRep (ρ.comp S.subtype) (stabilizer ↥S x)).dual s b) = (permRep ρ Δ).dual s.1 (qDual S x b) := by
  refine LinearMap.ext fun f => ?_
  have h := Rep.hom_comm_apply (qRep ρ S x) s⁻¹ f
  change b (permRep (ρ.comp S.subtype) (stabilizer ↥S x) s⁻¹ (qL S x f)) = b (qL S x (permRep ρ Δ (s⁻¹).val f))
  exact congrArg b h.symm

theorem jDual_equivariant (s : ↥S) (b : Module.Dual ℂ ((G ⧸ Δ) → E)) :
    jDual S x ((permRep ρ Δ).dual s.1 b) = (permRep (ρ.comp S.subtype) (stabilizer ↥S x)).dual s (jDual S x b) := by
  refine LinearMap.ext fun φ => ?_
  have h := Rep.hom_comm_apply (jRep ρ S x) s⁻¹ φ
  change b (permRep ρ Δ (s⁻¹).val (jL S x φ)) = b (jL S x (permRep (ρ.comp S.subtype) (stabilizer ↥S x) s⁻¹ φ))
  exact congrArg b h.symm

variable [Fintype (G ⧸ Δ)] [Fintype (↥S ⧸ stabilizer ↥S x)]

theorem dualPair_jL (φ : (↥S ⧸ stabilizer ↥S x) → Module.Dual ℂ E) (f : (G ⧸ Δ) → E) :
    dualPairEquiv Δ (jL S x φ) f = dualPairEquiv (stabilizer ↥S x) φ (qL S x f) := by
  change ∑ z, (jL S x φ) z (f z) = ∑ y, φ y ((qL S x f) y)
  set e := orbEq S x with he
  have hR : ∑ y, φ y ((qL S x f) y) = ∑ w : orbit ↥S x, φ (e w) (f w.1) := by
    rw [← Equiv.sum_comp e.symm (fun w : orbit ↥S x => φ (e w) (f w.1))]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Equiv.apply_symm_apply]
    rfl
  rw [hR]
  have hF : ∀ z ∈ (Finset.univ : Finset (G ⧸ Δ)), (jL S x φ) z (f z) ≠ 0 → z ∈ orbit ↥S x := by
    intro z _ hz
    by_contra h
    apply hz
    simp [jL, h]
  rw [← Finset.sum_filter_of_ne hF]
  rw [Finset.sum_subtype (p := fun z => z ∈ orbit ↥S x) (Finset.univ.filter (fun z => z ∈ orbit ↥S x))
    (fun z => by simp) (fun z => (jL S x φ) z (f z))]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hw : w.1 ∈ orbit ↥S x := w.2
  simp [jL, hw]
  rfl

end Comp

end TernaryPeriodPolynomials.Argument.RadicalInduction
