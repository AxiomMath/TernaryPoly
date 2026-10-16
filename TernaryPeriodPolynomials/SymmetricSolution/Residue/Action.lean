module

public import TernaryPeriodPolynomials.SymmetricSolution.Residue.Fiber
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Equivariance

@[expose] public section


/-!
# the `GL₃(ℚ)`-action on `R_n = ⨁_H (V_{n+1}/L V_n) ⊗ (ℚL)^*` in tensor form

H9's `residueFiberTensorEquiv n H : ResidueFiber n H ≃ (V_{n+1}/L_H V_n) ⊗ (ℚ L_H)^*` (`ResidueTensor`) presents each residue fibre as in the paper.  The library
(`TernaryPoly.SinglePole`) already carries a `GL₃(ℚ)`-action `residueAction n e` on the direct sum of the quotient presentations, with the exact sequence
`0 → V_n → M_n → R_n → 0` equivariant (`equivariant_residue_short_exact`).  Here:

* `ResidueTensorSum n = ⨁_H (V_{n+1}/L_H V_n) ⊗ (ℚ L_H)^*` and `residueTensorAll n : Residues n ≃ₗ ResidueTensorSum n` (the direct sum of H9's equivalences);
* `tensorAction n e`: the transported `GL₃(ℚ)`-action (`e` the determinant exponent), a `Representation` by construction, compatible with `residueFiberTensorEquiv`
  (`tensorAction_lof_residueFiberTensorEquiv`);
* `tensorAction_lof_tmul`: the intrinsic formula.  If `g⁻¹` substitution sends the equation `L_H` to `c · L_J` (`J` the transported hyperplane), then
  `g · ([p] ⊗ λ)_H = ([g p] ⊗ μ)_J` where `g p = det(g)^e (p ∘ g⁻¹)` is the coefficient action on `V_{n+1}`, and `μ` is the functional on `ℚ L_J` with
  `μ(g ℓ) = λ(ℓ)` (the dual factor is moved by the line isomorphism `g : ℚL_H → ℚL_J`, `lineMap`);
* `tensorResidue n`, `tensorResidue_short_exact`: the residue `M_n → R_n` to the tensor form is equivariant, surjective, and has kernel `V_n`
  (`eq:residue-exact` in tensor form), with `tensorResidue (q/L_H) = [q] ⊗ L_H^∨` (`tensorResidue_simplePole`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open TernaryPoly.SinglePole
open scoped TensorProduct DirectSum

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.ResidueAction

open TernaryPeriodPolynomials.Argument.Identities.ResidueTensor
open TernaryPoly.PolynomialGLAction (substitute determinantCharacter homogeneousAction)

/-- The tensor presentation `(V_{n+1}/L_H V_n) ⊗ (ℚ L_H)^*` of the residue fibre at `H`. -/
abbrev TensorFibre (n : ℕ) (H : Normal) : Type :=
  quotLin n (equation H) ⊗[ℚ] Module.Dual ℚ (Submodule.span ℚ {equation H})

/-- `R_n = ⨁_H (V_{n+1}/L_H V_n) ⊗ (ℚ L_H)^*` in tensor form. -/
abbrev ResidueTensorSum (n : ℕ) : Type := ⨁ H : Normal, TensorFibre n H

/-- H9's equivalences, summed over the hyperplanes. -/
def residueTensorAll (n : ℕ) : Residues n ≃ₗ[ℚ] ResidueTensorSum n :=
  DFinsupp.mapRange.linearEquiv (fun H : Normal => residueFiberTensorEquiv n H)

theorem residueTensorAll_lof (n : ℕ) (H : Normal) (x : ResidueFiber n H) :
    residueTensorAll n (DirectSum.lof ℚ Normal (ResidueFiber n) H x) =
      DirectSum.lof ℚ Normal (TensorFibre n) H (residueFiberTensorEquiv n H x) := by
  change DFinsupp.mapRange (fun H => residueFiberTensorEquiv n H)
    (fun H => map_zero _) (DFinsupp.single H x) = _
  rw [DFinsupp.mapRange_single]
  rfl

/-- **The `GL₃(ℚ)`-action on `R_n` in tensor form**: the residue action transported along H9's equivalences. -/
def tensorAction (n : ℕ) (e : ℤ) : Representation ℚ TernaryPoly.PolynomialGLAction.GL3 (ResidueTensorSum n) :=
  (residueTensorAll n).conjRingEquiv.toMonoidHom.comp (residueAction n e)

theorem tensorAction_apply (n : ℕ) (e : ℤ) (g : TernaryPoly.PolynomialGLAction.GL3) (x : ResidueTensorSum n) :
    tensorAction n e g x = residueTensorAll n (residueAction n e g ((residueTensorAll n).symm x)) := rfl

/-- **Compatibility with `residueFiberTensorEquiv`**: the tensor action of `g` on the image of a class at `H` is the image of the quotient action. -/
theorem tensorAction_residueTensorAll (n : ℕ) (e : ℤ) (g : TernaryPoly.PolynomialGLAction.GL3) (x : Residues n) :
    tensorAction n e g (residueTensorAll n x) = residueTensorAll n (residueAction n e g x) := by
  rw [tensorAction_apply, LinearEquiv.symm_apply_apply]

theorem tensorAction_lof_residueFiberTensorEquiv (n : ℕ) (e : ℤ) (g : TernaryPoly.PolynomialGLAction.GL3)
    (H : Normal) (x : ResidueFiber n H) :
    tensorAction n e g (DirectSum.lof ℚ Normal (TensorFibre n) H (residueFiberTensorEquiv n H x)) =
      residueTensorAll n (residueAction n e g (DirectSum.lof ℚ Normal (ResidueFiber n) H x)) := by
  rw [← residueTensorAll_lof, tensorAction_residueTensorAll]

theorem residueFiberTensorEquiv_mk (n : ℕ) (H : Normal) (q : V (n+1)) :
    residueFiberTensorEquiv n H ((numeratorRelations n H).mkQ q) =
      (Submodule.Quotient.mk q : quotLin n (equation H)) ⊗ₜ[ℚ] lineDual (equation H) (equation_ne_zero H) := by
  have h := residue_fraction_tensor n H q
  rwa [residue_component_fraction] at h

theorem act_equation (g : TernaryPoly.PolynomialGLAction.GL3) (H J : Normal) (c : ℚ)
    (hc : substitute (g⁻¹ : TernaryPoly.PolynomialGLAction.GL3) (denominator H) = C c * denominator J) :
    homogeneousAction 1 0 g (equation H) = c • equation J := by
  apply Subtype.ext
  change TernaryPoly.PolynomialGLAction.action 0 g (denominator H) = c • denominator J
  rw [TernaryPoly.PolynomialGLAction.action_apply]
  simp only [TernaryPoly.PolynomialGLAction.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    zpow_zero, one_smul]
  rw [hc, MvPolynomial.smul_eq_C_mul]

/-- The line isomorphism `g : ℚ L_H → ℚ L_J` induced by the (untwisted) inverse substitution, when `g⁻¹ L_H = c L_J`. -/
def lineMap (g : TernaryPoly.PolynomialGLAction.GL3) (H J : Normal) (c : ℚ)
    (hc : substitute (g⁻¹ : TernaryPoly.PolynomialGLAction.GL3) (denominator H) = C c * denominator J) :
    Submodule.span ℚ {equation H} →ₗ[ℚ] Submodule.span ℚ {equation J} :=
  (homogeneousAction 1 0 g).restrict (by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, act_equation g H J c hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem lineMap_self (g : TernaryPoly.PolynomialGLAction.GL3) (H J : Normal) (c : ℚ)
    (hc : substitute (g⁻¹ : TernaryPoly.PolynomialGLAction.GL3) (denominator H) = C c * denominator J) :
    lineMap g H J c hc ⟨equation H, Submodule.mem_span_singleton_self _⟩ =
      c • (⟨equation J, Submodule.mem_span_singleton_self _⟩ : Submodule.span ℚ {equation J}) :=
  Subtype.ext (act_equation g H J c hc)

/-- **The tensor action on a fibre element `[p] ⊗ L_H^∨`.** -/
theorem tensorAction_lof_dual (n : ℕ) (e : ℤ) (g : TernaryPoly.PolynomialGLAction.GL3) (H J : Normal) (c : ℚ)
    (hc : substitute (g⁻¹ : TernaryPoly.PolynomialGLAction.GL3) (denominator H) = C c * denominator J)
    (p : V (n+1)) :
    tensorAction n e g (DirectSum.lof ℚ Normal (TensorFibre n) H
        ((Submodule.Quotient.mk p : quotLin n (equation H)) ⊗ₜ[ℚ] lineDual (equation H) (equation_ne_zero H))) =
      DirectSum.lof ℚ Normal (TensorFibre n) J
        ((Submodule.Quotient.mk (TernaryPoly.SinglePole.transformedNumerator n e g c p) :
          quotLin n (equation J)) ⊗ₜ[ℚ] lineDual (equation J) (equation_ne_zero J)) := by
  rw [← residueFiberTensorEquiv_mk, tensorAction_lof_residueFiberTensorEquiv,
    residueAction_lof n e g H J c hc, residueTensorAll_lof, residueFiberTensorEquiv_mk]

theorem transformedNumerator_mk (n : ℕ) (e : ℤ) (g : TernaryPoly.PolynomialGLAction.GL3) (J : Normal) (c : ℚ)
    (p : V (n+1)) :
    (Submodule.Quotient.mk (TernaryPoly.SinglePole.transformedNumerator n e g c p) : quotLin n (equation J)) =
      c⁻¹ • (Submodule.Quotient.mk (homogeneousAction (n+1) e g p) : quotLin n (equation J)) := by
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  change determinantCharacter e g • c⁻¹ • substitute (g⁻¹ : TernaryPoly.PolynomialGLAction.GL3) p.val =
    c⁻¹ • (TernaryPoly.PolynomialGLAction.action e g p.val)
  rw [TernaryPoly.PolynomialGLAction.action_apply, smul_comm]

/-- **The tensor action, intrinsically.**  Let `g⁻¹ L_H = c L_J` (`c ≠ 0`; `J` the transported hyperplane, `transformed_denominator_exists`).  For `p ∈ V_{n+1}`,
`λ ∈ (ℚ L_H)^*` and `μ ∈ (ℚ L_J)^*` with `μ(g ℓ) = λ(ℓ)` for `ℓ ∈ ℚ L_H` (`lineMap`), the element `[p] ⊗ λ` of the fibre at `H` goes to `[g p] ⊗ μ` in the fibre at `J`,
where `g p = det(g)^e · (p ∘ g⁻¹)` is the coefficient action on `V_{n+1}`. -/
theorem tensorAction_lof_tmul (n : ℕ) (e : ℤ) (g : TernaryPoly.PolynomialGLAction.GL3) (H J : Normal) (c : ℚ) (hc0 : c ≠ 0)
    (hc : substitute (g⁻¹ : TernaryPoly.PolynomialGLAction.GL3) (denominator H) = C c * denominator J)
    (p : V (n+1)) (l : Module.Dual ℚ (Submodule.span ℚ {equation H}))
    (μ : Module.Dual ℚ (Submodule.span ℚ {equation J}))
    (hμ : ∀ ℓ, μ (lineMap g H J c hc ℓ) = l ℓ) :
    tensorAction n e g (DirectSum.lof ℚ Normal (TensorFibre n) H
        ((Submodule.Quotient.mk p : quotLin n (equation H)) ⊗ₜ[ℚ] l)) =
      DirectSum.lof ℚ Normal (TensorFibre n) J
        ((Submodule.Quotient.mk (homogeneousAction (n+1) e g p) : quotLin n (equation J)) ⊗ₜ[ℚ] μ) := by
  have hl := dual_eq_smul (equation H) (equation_ne_zero H) l
  have hm := dual_eq_smul (equation J) (equation_ne_zero J) μ
  have key : l ⟨equation H, Submodule.mem_span_singleton_self _⟩ =
      c * μ ⟨equation J, Submodule.mem_span_singleton_self _⟩ := by
    rw [← hμ, lineMap_self, map_smul, smul_eq_mul]
  rw [hl, hm, TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  simp only [map_smul]
  rw [tensorAction_lof_dual n e g H J c hc, transformedNumerator_mk, ← TensorProduct.smul_tmul' c⁻¹]
  simp only [map_smul, smul_smul, key]
  congr 1
  field_simp

/-- The residue of the tensor-form exact sequence: `M_n → R_n = ⨁_H (V_{n+1}/L_H V_n) ⊗ (ℚ L_H)^*`. -/
def tensorResidue (n : ℕ) : singlePole n →ₗ[ℚ] ResidueTensorSum n :=
  (residueTensorAll n).toLinearMap ∘ₗ residue n

theorem tensorResidue_equivariant (n : ℕ) (e : ℤ) (g : TernaryPoly.PolynomialGLAction.GL3) (x : singlePole n) :
    tensorAction n e g (tensorResidue n x) = tensorResidue n (singlePoleAction n e g x) := by
  simp only [tensorResidue, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [tensorAction_residueTensorAll, residue_equivariant]

/-- `res_H(q / L_H) = [q] ⊗ L_H^∨`. -/
theorem tensorResidue_simplePole (n : ℕ) (H : Normal) (q : V (n+1)) :
    tensorResidue n (simplePole n H q) = DirectSum.lof ℚ Normal (TensorFibre n) H
      ((Submodule.Quotient.mk q : quotLin n (equation H)) ⊗ₜ[ℚ] lineDual (equation H) (equation_ne_zero H)) := by
  simp only [tensorResidue, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [residue_simplePole, residueTensorAll_lof, residueFiberTensorEquiv_mk]

/-- **`eq:residue-exact` in tensor form, with both equivariances.** -/
theorem tensorResidue_short_exact (n : ℕ) (e : ℤ) :
    Function.Injective (polynomialInclusion n) ∧
    (tensorResidue n).ker = (polynomialInclusion n).range ∧
    Function.Surjective (tensorResidue n) ∧
    (∀ g p, singlePoleAction n e g (polynomialInclusion n p) =
      polynomialInclusion n (homogeneousAction n e g p)) ∧
    (∀ g x, tensorAction n e g (tensorResidue n x) = tensorResidue n (singlePoleAction n e g x)) :=
  ⟨polynomialInclusion_injective n, by
    rw [tensorResidue, LinearEquiv.ker_comp]; exact residue_exact n,
    (residueTensorAll n).surjective.comp (residue_surjective n),
    polynomialInclusion_equivariant n e, tensorResidue_equivariant n e⟩

end TernaryPeriodPolynomials.Argument.Identities.ResidueAction
