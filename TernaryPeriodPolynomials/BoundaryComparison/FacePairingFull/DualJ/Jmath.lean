module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Flags

@[expose] public section


/-!
# The paper's involution `ȷ(g) = J (g⁻¹)ᵀ J`

Paper (Appendix C.4, "The dual series and the boundary relation"): `J` is the antidiagonal permutation
matrix and `ȷ(g) = J (g⁻¹)ᵀ J`. It "exchanges `P, Q` and pulls `E` back to its dual, after the fixed linear change
of coefficient coordinates by `J`".

This file defines `ȷ` literally (`jmath`, with `J = longWeyl`) and proves the facts through which the model's
level-preserving involution `φ(g) = a (g⁻¹)ᵀ a⁻¹`, `a = diag(1,1,3)` (`dualInvolution`), represents it:

* `jmath_eq_conj`: `ȷ(g) = w φ(g) w⁻¹` with the fixed matrix `w = J a⁻¹` (`jmathConj`); hence
  `ȷ(Γ) = w Γ w⁻¹` is a rational conjugate of the level group `Γ` (`φ` preserves `Γ`);
* `mem_plane_jmath_iff`, `mem_line_jmath_iff`: `ȷ` exchanges the plane and line parabolics, so it induces the maps
  `jFlagLine`, `jFlagPlane`, `jEdge` on flag varieties, equivariant along `ȷ` (`jFlagLine_smul`, …);
* `dualFlag_eq_jFlagLine` (and the plane and edge versions): the model's `φ`-equivariant flag maps (which involve
  the long Weyl element) are the `ȷ`-equivariant ones translated by `w⁻¹`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Matrix TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ

theorem longWeyl_inv : longWeyl⁻¹ = longWeyl := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  exact longWeylMatrix_mul_self

theorem longWeyl_mul_self : longWeyl * longWeyl = 1 := by
  have h := mul_inv_cancel longWeyl
  rwa [longWeyl_inv] at h

theorem inverseTranspose_longWeyl : inverseTranspose longWeyl = longWeyl := by
  apply Units.ext
  rw [inverseTranspose_val, longWeyl_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **The paper's `ȷ(g) = J (g⁻¹)ᵀ J`**, `J` the antidiagonal permutation matrix (`longWeyl`). -/
def jmath : RationalGL3 →* RationalGL3 :=
  (MulAut.conj longWeyl⁻¹).toMonoidHom.comp inverseTranspose

theorem jmath_apply (g : RationalGL3) :
    jmath g = longWeyl * inverseTranspose g * longWeyl := by
  change longWeyl⁻¹ * inverseTranspose g * (longWeyl⁻¹)⁻¹ = _
  rw [inv_inv, longWeyl_inv]

/-- The entries of `ȷ(g)`: `ȷ(g)_{ij} = (g⁻¹)_{(2-j)(2-i)}`. -/
theorem jmath_val (g : RationalGL3) (i j : Fin 3) :
    (jmath g).val i j = (g⁻¹).val j.rev i.rev := by
  have h : jmath g = longWeyl⁻¹ * inverseTranspose g * longWeyl := by
    rw [jmath_apply, longWeyl_inv]
  rw [h, longWeyl_conj_val, inverseTranspose_val]
  rfl

theorem jmath_jmath (g : RationalGL3) : jmath (jmath g) = g := by
  rw [jmath_apply, jmath_apply g, map_mul, map_mul, inverseTranspose_longWeyl,
    inverseTranspose_involutive]
  calc longWeyl * (longWeyl * g * longWeyl) * longWeyl
      = (longWeyl * longWeyl) * g * (longWeyl * longWeyl) := by simp only [mul_assoc]
    _ = g := by rw [longWeyl_mul_self, one_mul, mul_one]

/-- The fixed matrix `w = J a⁻¹` with `ȷ = Ad(w) ∘ φ`. -/
def jmathConj : RationalGL3 := longWeyl * levelScale⁻¹

/-- **`ȷ` is the model's level-preserving involution `φ` up to conjugation by the fixed matrix `w = J a⁻¹`.** -/
theorem jmath_eq_conj (g : RationalGL3) :
    jmath g = jmathConj * dualInvolution g * jmathConj⁻¹ := by
  rw [jmath_apply, dualInvolution_apply]
  unfold jmathConj
  rw [_root_.mul_inv_rev, inv_inv, longWeyl_inv]
  group

theorem dualInvolution_eq_conj (g : RationalGL3) :
    dualInvolution g = jmathConj⁻¹ * jmath g * jmathConj := by
  rw [jmath_eq_conj]
  group

/-- `ȷ` is an involution. -/
theorem jmath_involutive : Function.Involutive jmath := jmath_jmath

theorem parabolic_plane_iff (g : RationalGL3) :
    g ∈ parabolic .plane ↔ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := Iff.rfl

theorem parabolic_line_iff (g : RationalGL3) :
    g ∈ parabolic .line ↔ g.val 1 0 = 0 ∧ g.val 2 0 = 0 := Iff.rfl

/-- `ȷ` carries the line parabolic `Q` into the plane parabolic `P`, and conversely. -/
theorem mem_plane_jmath_iff (g : RationalGL3) :
    jmath g ∈ parabolic .plane ↔ g ∈ parabolic .line := by
  have key : jmath g ∈ parabolic .plane ↔ g⁻¹ ∈ parabolic .line := by
    rw [parabolic_plane_iff, parabolic_line_iff, jmath_val, jmath_val]
    exact Iff.intro (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)
  rw [key, inv_mem_iff]

theorem mem_line_jmath_iff (g : RationalGL3) :
    jmath g ∈ parabolic .line ↔ g ∈ parabolic .plane := by
  have key : jmath g ∈ parabolic .line ↔ g⁻¹ ∈ parabolic .plane := by
    rw [parabolic_plane_iff, parabolic_line_iff, jmath_val, jmath_val]
    exact Iff.intro (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)
  rw [key, inv_mem_iff]

theorem mem_borel_jmath_iff (g : RationalGL3) :
    jmath g ∈ parabolic .plane ⊓ parabolic .line ↔ g ∈ parabolic .plane ⊓ parabolic .line := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_plane_jmath_iff, mem_line_jmath_iff, and_comm]

/-- The line flags of `GL₃(ℚ)` map to plane flags along `ȷ`. -/
def jFlagLine : Flags .line → Flags .plane :=
  Quotient.map' jmath fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact (mem_plane_jmath_iff _).mpr h

/-- The plane flags map to line flags along `ȷ`. -/
def jFlagPlane : Flags .plane → Flags .line :=
  Quotient.map' jmath fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact (mem_line_jmath_iff _).mpr h

/-- The complete flags map to complete flags along `ȷ`. -/
def jEdge : Edges → Edges :=
  Quotient.map' jmath fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact (mem_borel_jmath_iff _).mpr h

theorem jFlagLine_mk (g : RationalGL3) :
    jFlagLine (QuotientGroup.mk g) = QuotientGroup.mk (jmath g) := rfl

theorem jFlagPlane_mk (g : RationalGL3) :
    jFlagPlane (QuotientGroup.mk g) = QuotientGroup.mk (jmath g) := rfl

theorem jEdge_mk (g : RationalGL3) :
    jEdge (QuotientGroup.mk g) = QuotientGroup.mk (jmath g) := rfl

theorem jFlagLine_smul (g : RationalGL3) (F : Flags .line) :
    jFlagLine (g • F) = jmath g • jFlagLine F := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective F
  rw [MulAction.Quotient.smul_mk, jFlagLine_mk, jFlagLine_mk, MulAction.Quotient.smul_mk,
    smul_eq_mul, smul_eq_mul, map_mul]

theorem jFlagPlane_smul (g : RationalGL3) (F : Flags .plane) :
    jFlagPlane (g • F) = jmath g • jFlagPlane F := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective F
  rw [MulAction.Quotient.smul_mk, jFlagPlane_mk, jFlagPlane_mk, MulAction.Quotient.smul_mk,
    smul_eq_mul, smul_eq_mul, map_mul]

theorem jEdge_smul (g : RationalGL3) (e : Edges) :
    jEdge (g • e) = jmath g • jEdge e := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective e
  rw [MulAction.Quotient.smul_mk, jEdge_mk, jEdge_mk, MulAction.Quotient.smul_mk,
    smul_eq_mul, smul_eq_mul, map_mul]

/-- `ȷ` exchanges the endpoints of a complete flag. -/
theorem endpoint_plane_jEdge (e : Edges) :
    endpoint .plane (jEdge e) = jFlagLine (endpoint .line e) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective e
  rfl

theorem endpoint_line_jEdge (e : Edges) :
    endpoint .line (jEdge e) = jFlagPlane (endpoint .plane e) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective e
  rfl

theorem conj_levelScale_mem_borel :
    longWeyl⁻¹ * levelScale * longWeyl ∈ parabolic .plane ⊓ parabolic .line := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> rw [longWeyl_conj_val] <;> simp [levelScale]

theorem jmathConj_inv : jmathConj⁻¹ = levelScale * longWeyl := by
  unfold jmathConj
  rw [_root_.mul_inv_rev, inv_inv, longWeyl_inv]

/-- Multiplying by the diagonal matrix `J a J` stays inside a coset: the key step of the comparison of the
`φ`-equivariant flag maps with the `ȷ`-equivariant ones. -/
theorem relative_position (g : RationalGL3) :
    (dualInvolution g * longWeyl)⁻¹ * (jmathConj⁻¹ * jmath g) =
      longWeyl⁻¹ * levelScale * longWeyl := by
  have h1 : jmathConj⁻¹ * jmath g = dualInvolution g * jmathConj⁻¹ := by
    rw [jmath_eq_conj]
    group
  rw [h1, jmathConj_inv]
  group

/-- The model's `φ`-equivariant flag map is the `ȷ`-equivariant one translated by `w⁻¹ = a J`. -/
theorem dualFlag_eq_jFlagLine (F : Flags .line) : dualFlag F = jmathConj⁻¹ • jFlagLine F := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective F
  rw [dualFlag_mk, jFlagLine_mk, MulAction.Quotient.smul_mk, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [relative_position]
  exact conj_levelScale_mem_borel.1

theorem dualPlaneFlag_eq_jFlagPlane (F : Flags .plane) :
    dualPlaneFlag F = jmathConj⁻¹ • jFlagPlane F := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective F
  rw [dualPlaneFlag_mk, jFlagPlane_mk, MulAction.Quotient.smul_mk, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [relative_position]
  exact conj_levelScale_mem_borel.2

theorem dualEdge_eq_jEdge (e : Edges) : dualEdge e = jmathConj⁻¹ • jEdge e := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective e
  rw [dualEdge_mk, jEdge_mk, MulAction.Quotient.smul_mk, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [relative_position]
  exact conj_levelScale_mem_borel

end TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ
