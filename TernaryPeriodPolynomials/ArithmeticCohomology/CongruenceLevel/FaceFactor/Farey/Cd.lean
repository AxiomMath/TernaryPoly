module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.LineTree
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.TreeCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.GammaNTransfer

@[expose] public section


/-!
# The dual Farey tree and the cohomological dimension of the face groups

Formalized by Claude Sonnet 5.5.

`fareyTree`: the dual Farey tree with the free action of a subgroup with `FareyData` is a `TreeData`.  `cdLe_three_of_ext`: every extension of Mathlib's `Γ(N)` (`N ≥ 3`) by `ℤ²`, in particular the line groups
`Γ(N) ∩ h⁻¹Qh` and the plane groups `Γ(N) ∩ h⁻¹Ph`, has cohomological dimension `≤ 3` (trivial coefficients): `H⁴ = 0`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open CategoryTheory CategoryTheory.Limits
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPoly.RankTwoAugmentedFrames
open scoped Classical

section Potential

variable {V : Type} [AddCommGroup V] [Module ℚ V]

/-- Evaluation of a function on oriented edges against a rational chain, with rational coefficients. -/
def evalChainQ (F : OTE → V) (c : PE) : V := c.coeff.sum fun p r => r • F p

theorem evalChainQ_add (F : OTE → V) (x y : PE) : evalChainQ F (x + y) = evalChainQ F x + evalChainQ F y := by
  unfold evalChainQ
  rw [MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun p => by simp) (fun p r₁ r₂ => by rw [add_smul])

theorem evalChainQ_zero (F : OTE → V) : evalChainQ F 0 = 0 := by
  simp [evalChainQ]

theorem evalChainQ_sub (F : OTE → V) (x y : PE) : evalChainQ F (x - y) = evalChainQ F x - evalChainQ F y := by
  have := evalChainQ_add F (x - y) y
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem evalChainQ_single (F : OTE → V) (p : OTE) (r : ℚ) :
    evalChainQ F (MonoidAlgebra.single p r) = r • F p := by
  unfold evalChainQ
  rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  simp

theorem evalChainQ_edgeVec (F : OTE → V) (hF : ∀ q : OTE, F q.swap = -F q) (p : OTE) :
    evalChainQ F (edgeVec p) = F p := by
  have e : edgeVec p = MonoidAlgebra.single p (1 / 2 : ℚ) - MonoidAlgebra.single p.swap (1 / 2 : ℚ) := by
    unfold edgeVec
    rw [smul_sub, MonoidAlgebra.smul_single, MonoidAlgebra.smul_single]
    simp
  rw [e, evalChainQ_sub, evalChainQ_single, evalChainQ_single, hF, smul_neg, sub_neg_eq_add, ← add_smul]
  norm_num

/-- The potential of an antisymmetric edge function on the dual Farey tree, for coefficients in a `ℚ`-vector space. -/
def potQ (F : OTE → V) (t : Tri) : V := evalChainQ F ((bd t : P1) : PE)

theorem potQ_delta (F : OTE → V) (hF : ∀ q : OTE, F q.swap = -F q) (q : OTE) :
    potQ F q.1.2 - potQ F q.1.1 = F q := by
  unfold potQ
  rw [← evalChainQ_sub]
  have : (((bd q.1.2 : P1) : PE) - ((bd q.1.1 : P1) : PE)) = ((bd q.1.2 - bd q.1.1 : P1) : PE) := rfl
  rw [this, bd_edge, evalChainQ_edgeVec F hF]

end Potential

/-- **The dual Farey tree** with the free action of a subgroup `Γ` with `FareyData`. -/
def fareyTree {Γ : Subgroup IntegralGL} (D : FareyData Γ) : TreeData Γ where
  Vt := Tri
  Et := OTE
  swap := OTE.swap
  src q := q.1.1
  tgt q := q.1.2
  src_smul _ _ := rfl
  tgt_smul _ _ := rfl
  swap_smul γ q := (OTE.swap_smul (γ : IntegralGL) q).symm
  src_swap _ := rfl
  swap_swap := OTE.swap_swap
  free_v := D.freeT
  free_e := D.freeO
  nonempty_v := ⟨triPlus⟩
  conn _ _ P h v w := (tri_const (P := P) h v).trans (tri_const (P := P) h w).symm
  pot _ _ _ F hF := ⟨potQ F, potQ_delta F hF⟩


section Fin

variable {k : Type} [CommRing k] [Algebra ℚ k] [Invertible (2 : k)]

/-- **Cohomological dimension `≤ 3` of the line (and plane) group.**  A group `R` with a surjection onto `Γ(N)` (`N ≥ 3`, in the Farey model) whose kernel is
`ℤ²` has cohomological dimension `≤ 3` (trivial coefficients). -/
theorem cdLe_three_of_extension {N : ℕ} (hN : 3 ≤ N) {R : Type} [Group R] (π : R →* gammaNGL N) (hπ : Function.Surjective π)
    (e : π.ker ≃* Multiplicative (ℤ × ℤ)) : CdLe k R 3 :=
  cdLe_succ π hπ (fareyTree (gammaNFareyData hN)) (CdLe.of_mulEquiv e.symm (cdLe_int2 (k := k)))

end Fin

section Ext

variable {k : Type} [CommRing k] [Algebra ℚ k] [Invertible (2 : k)]

/-- **A split-or-not extension of `Γ(N)` (Mathlib's `CongruenceSubgroup.Gamma N`) by `ℤ²` has cohomological dimension `≤ 3`** (trivial coefficients): this
applies to the line groups `Γ(N) ∩ h⁻¹Qh` and the plane groups `Γ(N) ∩ h⁻¹Ph` of all faces. -/
theorem cdLe_three_of_ext {N : ℕ} (hN : 3 ≤ N) {E : Type} [Group E]
    (ext : GroupExtension (Multiplicative (ℤ × ℤ)) E (CongruenceSubgroup.Gamma N)) : CdLe k E 3 := by
  let π : E →* gammaNGL N := (gammaEquiv hN).toMonoidHom.comp ext.rightHom
  have hπ : Function.Surjective π := (gammaEquiv hN).surjective.comp ext.rightHom_surjective
  have hker : ∀ x : E, x ∈ π.ker ↔ ext.rightHom x = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    change gammaEquiv hN (ext.rightHom x) = 1 ↔ _
    exact map_eq_one_iff _ (gammaEquiv hN).injective
  have hinl : ∀ r, ext.inl r ∈ π.ker := by
    intro r
    rw [hker]
    exact MonoidHom.mem_ker.mp (ext.range_inl_eq_ker_rightHom ▸ ⟨r, rfl⟩)
  let f : Multiplicative (ℤ × ℤ) →* π.ker := ext.inl.codRestrict π.ker hinl
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact ext.inl_injective (congrArg Subtype.val hab)
    · rintro ⟨x, hx⟩
      have : x ∈ ext.inl.range := by
        rw [ext.range_inl_eq_ker_rightHom]
        exact MonoidHom.mem_ker.mpr ((hker x).mp hx)
      obtain ⟨r, hr⟩ := this
      exact ⟨r, Subtype.ext hr⟩
  exact cdLe_three_of_extension (k := k) hN π hπ (MulEquiv.ofBijective f hf).symm

end Ext


end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
