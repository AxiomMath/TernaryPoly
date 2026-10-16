module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Psi

@[expose] public section


/-!
# Lemma B.1, range form: the Farey triangle classes are not boundaries

Appendix B, Lemma B.1: the classes `F2 t` of the Farey triangles `t` are not boundaries, i.e. no nonzero scalar multiple
of a Farey class lies in the range of `Φ(d₃)`; this follows from the linear form `exists_psi`.

Formalized by Claude Haiku 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

/-- A nonzero multiple of a Farey triangle class is not a boundary of `Φ(RG₃)`. -/
theorem smul_F2_not_mem_range (t : FareyTree.Tri) {c : ℚ} (hc : c ≠ 0) :
    c • F2 t ∉ LinearMap.range (dPhi 2).hom.toLinearMap := by
  obtain ⟨ψ, hψ0, hψ1⟩ := exists_psi
  rintro ⟨x, hx⟩
  have h2 : ψ ((dPhi 2).hom x) = ψ (c • F2 t) := congrArg ψ hx
  rw [hψ0 x, map_smul, hψ1 t, smul_eq_mul, mul_one] at h2
  exact hc h2.symm

/-- A Farey triangle class is not a boundary of `Φ(RG₃)`. -/
theorem F2_not_mem_range (t : FareyTree.Tri) : F2 t ∉ LinearMap.range (dPhi 2).hom.toLinearMap := by
  have h := smul_F2_not_mem_range t (c := 1) one_ne_zero
  rwa [one_smul] at h

/-- A linear combination of Farey triangle classes with nonzero total coefficient is not a boundary of `Φ(RG₃)`. -/
theorem sum_F2_not_mem_range (s : Finset FareyTree.Tri) (c : FareyTree.Tri → ℚ) (hs : ∑ t ∈ s, c t ≠ 0) :
    ∑ t ∈ s, c t • F2 t ∉ LinearMap.range (dPhi 2).hom.toLinearMap := by
  obtain ⟨ψ, hψ0, hψ1⟩ := exists_psi
  rintro ⟨x, hx⟩
  have h2 : ψ ((dPhi 2).hom x) = ψ (∑ t ∈ s, c t • F2 t) := congrArg ψ hx
  rw [hψ0 x, map_sum] at h2
  simp only [map_smul, hψ1, smul_eq_mul, mul_one] at h2
  exact hs h2.symm

/-- The Farey triangle classes are nonzero. -/
theorem F2_ne_zero (t : FareyTree.Tri) : F2 t ≠ 0 := by
  obtain ⟨ψ, -, hψ1⟩ := exists_psi
  intro h
  have h1 := hψ1 t
  rw [h, map_zero] at h1
  exact zero_ne_one h1

end TernaryPeriodPolynomials.Argument.AppendixBResidue
