module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel

@[expose] public section


/-!
# The flag maps `dualFlag`, `dualPlaneFlag`, `dualEdge` are mutually inverse

`dualFlag : Flags .line → Flags .plane`, `dualPlaneFlag : Flags .plane → Flags .line` and
`dualEdge : Edges → Edges` are induced by `g ↦ φ(g) J` (`J` the long Weyl element). Since
`φ(φ g · J) · J = g · (φ(J) J)` and `φ(J) J = diag(1/3, 1, 3)` is diagonal, each composite of two
of them is the identity.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

theorem dualInvolution_longWeyl_mul_entries (i j : Fin 3) :
    (dualInvolution longWeyl * longWeyl).val i j = Matrix.diagonal ![(1 : ℚ) / 3, 1, 3] i j := by
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, dualInvolution_val_apply,
      longWeyl, longWeylMatrix]

theorem dualInvolution_longWeyl_mul_mem_borel :
    dualInvolution longWeyl * longWeyl ∈ parabolic .plane ⊓ parabolic .line := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · change (dualInvolution longWeyl * longWeyl).val 2 0 = 0
    rw [dualInvolution_longWeyl_mul_entries]
    rfl
  · change (dualInvolution longWeyl * longWeyl).val 2 1 = 0
    rw [dualInvolution_longWeyl_mul_entries]
    rfl
  · change (dualInvolution longWeyl * longWeyl).val 1 0 = 0
    rw [dualInvolution_longWeyl_mul_entries]
    rfl
  · change (dualInvolution longWeyl * longWeyl).val 2 0 = 0
    rw [dualInvolution_longWeyl_mul_entries]
    rfl

theorem dualPlaneFlag_dualFlag (F : Flags .line) : dualPlaneFlag (dualFlag F) = F := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective F
  rw [dualFlag_mk, dualPlaneFlag_mk]
  symm
  apply QuotientGroup.eq.mpr
  have h : g⁻¹ * (dualInvolution (dualInvolution g * longWeyl) * longWeyl) =
      dualInvolution longWeyl * longWeyl := by
    rw [map_mul, dualInvolution_involutive]
    group
  rw [h]
  exact dualInvolution_longWeyl_mul_mem_borel.2

theorem dualFlag_dualPlaneFlag (F : Flags .plane) : dualFlag (dualPlaneFlag F) = F := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective F
  rw [dualPlaneFlag_mk, dualFlag_mk]
  symm
  apply QuotientGroup.eq.mpr
  have h : g⁻¹ * (dualInvolution (dualInvolution g * longWeyl) * longWeyl) =
      dualInvolution longWeyl * longWeyl := by
    rw [map_mul, dualInvolution_involutive]
    group
  rw [h]
  exact dualInvolution_longWeyl_mul_mem_borel.1

theorem dualEdge_dualEdge (e : Edges) : dualEdge (dualEdge e) = e := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective e
  rw [dualEdge_mk, dualEdge_mk]
  symm
  apply QuotientGroup.eq.mpr
  have h : g⁻¹ * (dualInvolution (dualInvolution g * longWeyl) * longWeyl) =
      dualInvolution longWeyl * longWeyl := by
    rw [map_mul, dualInvolution_involutive]
    group
  rw [h]
  exact dualInvolution_longWeyl_mul_mem_borel

end TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
