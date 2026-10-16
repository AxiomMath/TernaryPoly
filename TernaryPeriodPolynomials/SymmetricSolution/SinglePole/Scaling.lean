module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Residue

@[expose] public section


open MvPolynomial
open scoped DirectSum
noncomputable section
namespace TernaryPoly.SinglePole
open ModThreeGoodAction AugmentedFrameComplex PrimitiveLineHeight
attribute [local instance] Classical.propDecidable

@[simp] theorem embed_C (c : ℚ) : embed (C c) = algebraMap ℚ Frac c :=
  (IsScalarTower.algebraMap_apply ℚ Poly Frac c).symm

/-- The inverse scalar is exactly the denominator-dual convention in the residue fiber. -/
theorem divide_scaled_form (c : ℚ) (L p : Poly) :
    embed p / embed (C c * L) = embed (c⁻¹ • p) / embed L := by
  have hs : embed (c⁻¹ • p) = c⁻¹ • embed p :=
    (IsScalarTower.toAlgHom ℚ Poly Frac).toLinearMap.map_smul c⁻¹ p
  rw [hs,map_mul,embed_C]
  simp only [Algebra.smul_def,map_inv₀,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Every nonzero rational linear form is a nonzero scalar multiple of its chosen normal denominator. -/
theorem form_scalar_denominator (v : Space) (hv : v ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧ form v = C c * denominator (vectorLine v hv) := by
  let H := vectorLine v hv
  have hmem : v ∈ Submodule.span ℚ {rationalVector (primitiveGenerator H)} := by
    rw [primitiveGenerator_span]
    exact Submodule.mem_span_singleton_self v
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c,?_,?_⟩
  · intro hc0
    rw [hc0,zero_smul] at hc
    exact hv hc.symm
  · change form v = C c * denominator H
    calc
      form v = form (c • rationalVector (primitiveGenerator H)) := congrArg form hc.symm
      _ = C c * denominator H := form_smul c _

/-- A numerator over a chosen linear denominator is an actual element of M_n. -/
def simplePole (n : ℕ) (H : Normal) (p : V (n+1)) : singlePole n :=
  (presentationMap n).rangeRestrict (0,DirectSum.lof ℚ Normal (fun _ => V (n+1)) H p)

@[simp] theorem simplePole_val (n : ℕ) (H : Normal) (p : V (n+1)) :
    (simplePole n H p).val = fractionMap n H p := by
  change polynomialMap n 0 + poleSum n (DirectSum.lof ℚ Normal (fun _ => V (n+1)) H p) = _
  rw [map_zero,zero_add]
  exact DirectSum.toModule_lof ℚ (M := fun _ : Normal => V (n+1))
    (φ := fractionMap n) H p

theorem residue_simplePole (n : ℕ) (H : Normal) (p : V (n+1)) :
    residue n (simplePole n H p) =
      DirectSum.lof ℚ Normal (ResidueFiber n) H ((numeratorRelations n H).mkQ p) := by
  rw [simplePole,residue_presentation]
  change numeratorResidues n (DirectSum.lof ℚ Normal (fun _ => V (n+1)) H p) = _
  exact DirectSum.lmap_lof (fun J => (numeratorRelations n J).mkQ) H p

/-- The finite-sum definition includes every nonzero rational linear form, with exact inverse scaling. -/
theorem fraction_mem_singlePole (n : ℕ) (v : Space) (hv : v ≠ 0) (p : V (n+1)) :
    embed p.val / embed (form v) ∈ singlePole n := by
  obtain ⟨c,_,hc⟩ := form_scalar_denominator v hv
  rw [hc,divide_scaled_form]
  simpa only [simplePole_val,fractionMap_apply,SetLike.val_smul] using
    (simplePole n (vectorLine v hv) (c⁻¹ • p)).property

/-- Explicit finite sums over arbitrary nonzero rational linear forms belong to M_n. -/
theorem arbitrary_finite_sum_mem (n : ℕ) {ι : Type*} (s : Finset ι)
    (v : ι → Space) (hv : ∀ i ∈ s, v i ≠ 0)
    (p : V n) (q : ι → V (n+1)) :
    embed p.val + ∑ i ∈ s, embed (q i).val / embed (form (v i)) ∈ singlePole n := by
  apply (singlePole n).add_mem
  · simpa only [polynomialInclusion_val] using (polynomialInclusion n p).property
  · exact (singlePole n).sum_mem fun i hi => fraction_mem_singlePole n (v i) (hv i hi) (q i)

end TernaryPoly.SinglePole
