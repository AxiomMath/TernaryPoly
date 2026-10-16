module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.CuspidalP
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.ChangeB
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.DualFlags

@[expose] public section


open scoped MatrixGroups DirectSum
open CategoryTheory
open scoped Classical
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.FormClassK

/-!
# Change of face representatives for the dual construction

Formalized by Claude Sonnet 5.5.
The faces of the dual construction are the `ȷ`-images of the faces.  the `dualE` uses the cusps `LineFaces.rep j` (series cusps of `E^∨`), whereas `dualEJ`
uses `ȷ(planeFaceRepr x)`.  The two families of representatives are related by the face correspondence `jFaceEquiv : LineFaces N ≃ PlaneFaces N` (`ȷ` carries line faces to plane
faces), and by `q h γ` (`q ∈ P(ℤ)`, `γ ∈ Γ(N)`); the series at related cusps agree (`EisensteinClass/CuspChangeB`).

* `jFaceEquiv`: `j ↦ [ȷ(j.rep)]`, inverse `x ↦ [ȷ(planeFaceRepr x)]`;
* `dualE_eq_dualEJ`: for every tuple `u'` indexed by the line faces there is a tuple `u` indexed by the plane faces with `dualE u' = dualEJ u` (equality of classes).
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinDual

variable (N : ℕ) (n : ℕ)

theorem lineRel_jmath {l l' : SL(3, ℤ)} (h : (lineFaceSetoid N).r l l') : (planeFaceSetoid N).r (jmath l) (jmath l') := by
  obtain ⟨q, hq, γ, hγ, rfl⟩ := h
  refine ⟨jmath q, ?_, jmath γ, jmath_mem_gammaN.2 hγ, by rw [jmath_mul, jmath_mul]⟩
  have := (jmath_mem_lineBorel_iff (A := jmath q)).1
  rw [jmath_jmath] at this
  exact this hq

theorem planeRel_jmath {p p' : SL(3, ℤ)} (h : (planeFaceSetoid N).r p p') : (lineFaceSetoid N).r (jmath p) (jmath p') := by
  obtain ⟨q, hq, γ, hγ, rfl⟩ := h
  exact ⟨jmath q, jmath_mem_lineBorel_iff.2 hq, jmath γ, jmath_mem_gammaN.2 hγ, by rw [jmath_mul, jmath_mul]⟩

/-- The plane face of the cusp `ȷ(j.rep)`. -/
def tauFace (j : LineFaces N) : PlaneFaces N := Quotient.mk (planeFaceSetoid N) (jmath j.rep)

/-- The line face of the cusp `ȷ(planeFaceRepr x)`. -/
def sigmaFace (x : PlaneFaces N) : LineFaces N := LineFaces.mk (jmath (planeFaceRepr x))

theorem rel_tau (j : LineFaces N) : (planeFaceSetoid N).r (planeFaceRepr (tauFace N j)) (jmath j.rep) :=
  Quotient.mk_out (s := planeFaceSetoid N) (jmath j.rep)

theorem tau_sigma (x : PlaneFaces N) : tauFace N (sigmaFace N x) = x := by
  have h1 := lineRel_jmath N (LineFaces.rel_rep (N := N) (jmath (planeFaceRepr x)))
  rw [jmath_jmath] at h1
  have e2 : (Quotient.mk (planeFaceSetoid N) (planeFaceRepr x) : PlaneFaces N) = x := Quotient.out_eq x
  exact (Quotient.sound h1).symm.trans e2

theorem sigma_tau (j : LineFaces N) : sigmaFace N (tauFace N j) = j := by
  have h1 := planeRel_jmath N (rel_tau N j)
  rw [jmath_jmath] at h1
  have e2 : (Quotient.mk (lineFaceSetoid N) j.rep : LineFaces N) = j := Quotient.out_eq j
  exact (Quotient.sound h1).trans e2

/-- **The face correspondence** `ȷ : LineFaces N ≃ PlaneFaces N`. -/
def jFaceEquiv : LineFaces N ≃ PlaneFaces N where
  toFun := tauFace N
  invFun := sigmaFace N
  left_inv := sigma_tau N
  right_inv := tau_sigma N



section Reps

variable [NeZero N]

/-- **The classes `dualE` (S7: representatives `LineFaces.rep j`) and `dualEJ` (representatives `ȷ(planeFaceRepr x)`) agree**: for every tuple `u'` indexed by the line faces
there is a tuple `u` indexed by the plane faces with `dualE u' = dualEJ u`. -/
theorem dualE_eq_dualEJ (hn : 4 ≤ n) (u' : DualTuple N n) :
    ∃ u : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ), dualE hn u' = dualEJ N n hn u := by
  have key : ∀ j : LineFaces N, ∃ (s : Bool) (φ : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ) →
      CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)), ∀ (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (b : Bool),
        Statements.EisensteinClass.eisensteinAtClass_gammaN N n f (jmath j.rep) b hn =
          Statements.EisensteinClass.eisensteinAtClass_gammaN N n (φ f) (planeFaceRepr (tauFace N j)) (xor b s) hn := by
    intro j
    obtain ⟨q, hq, γ, hγ, e⟩ := rel_tau N j
    obtain ⟨s, φ, h⟩ := exists_cuspChange_class N n hn hq
    exact ⟨s, φ, fun f b => by rw [e]; exact h f (planeFaceRepr (tauFace N j)) γ hγ b⟩
  choose s φ hsφ using key
  let bx : Bool → (Bool ≃ Bool) := fun s => ⟨fun b => xor b s, fun b => xor b s, fun b => by cases b <;> cases s <;> rfl,
    fun b => by cases b <;> cases s <;> rfl⟩
  refine ⟨fun x b'' => φ ((jFaceEquiv N).symm x) (u' ((jFaceEquiv N).symm x) (xor b'' (s ((jFaceEquiv N).symm x)))), ?_⟩
  change ∑ j : LineFaces N, ∑ b : Bool, dualClassC N n (u' j b) hn b j.rep = _
  unfold dualEJ
  rw [← Equiv.sum_comp (jFaceEquiv N)]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [← Equiv.sum_comp (bx (s j))]
  refine Finset.sum_congr rfl fun b _ => ?_
  conv_rhs => rw [dualClassC_jmath]
  change dualClassC N n (u' j b) hn b j.rep = jPullC N n (EisensteinClass.complexify (gammaN N) n
    (Statements.EisensteinClass.eisensteinAtClass_gammaN N n
      (φ ((jFaceEquiv N).symm (jFaceEquiv N j)) (u' ((jFaceEquiv N).symm (jFaceEquiv N j))
        (xor (xor b (s j)) (s ((jFaceEquiv N).symm (jFaceEquiv N j))))))
      (planeFaceRepr (jFaceEquiv N j)) (xor b (s j)) hn))
  rw [Equiv.symm_apply_apply]
  have hb : xor (xor b (s j)) (s j) = b := by cases b <;> cases s j <;> rfl
  rw [hb]
  change _ = jPullC N n (EisensteinClass.complexify (gammaN N) n
    (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (φ j (u' j b)) (planeFaceRepr (tauFace N j)) (xor b (s j)) hn))
  rw [← hsφ j (u' j b) b]
  unfold dualClassC
  rfl

end Reps

end TernaryPeriodPolynomials.Argument.EisensteinDual
