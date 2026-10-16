module

public import TernaryPeriodPolynomials.GroupCohomology.Homology.ResolutionConj
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Push
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.TreeInstance

@[expose] public section


/-!
# Transfer, invariance and top-degree injectivity for an arbitrary resolution

Formalized by Claude Sonnet 5.5.

For `N ⊲ K` of finite index and a complex `Y` of `K`-representations: `trY` is the transfer chain map
`CxK Y ⟶ CxN N Y` with `QY ≫ trY = avgY` (`QY_trY`) and `trY ≫ QY = 𝟙` (`trY_QY`); `avgY` is idempotent and invariant
(`avgY_idem`, `GY_avgY`, `avgY_GY`) and kills the kernel of `QY` (`ker_QY`).  In the top degree `cycleClass` is injective
when `d 4 3 = 0` (`cycleClass_injective_top`), whence `invariant_of_avgN_fixed`: a top cycle representing an
`avgN`-fixed class is fixed by `avgY`, equals `trY (QY ζ)`, and `QY ζ` represents the corestriction.
-/

open CategoryTheory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {K : Type} [Group K] (N : Subgroup K) [N.Normal] [N.FiniteIndex]
  (Y : ChainComplex (Rep.{0} ℚ K) ℕ)

omit [N.Normal] in
theorem card_ne_zero_quot : ((Fintype.card (K ⧸ N) : ℚ)) ≠ 0 := by
  exact_mod_cast (Fintype.card_pos (α := K ⧸ N)).ne'

/-- The transfer chain map `CxK Y ⟶ CxN N Y`. -/
def trY : CxK Y ⟶ CxN N Y := TY N Y ((Fintype.card (K ⧸ N) : ℚ)⁻¹)

theorem QY_trY : QY N Y ≫ trY N Y = avgY N Y := QY_TY N Y _

theorem trY_QY : trY N Y ≫ QY N Y = 𝟙 _ := TY_QY N Y (card_ne_zero_quot N)

theorem GY_avgY (g : K) : GY N Y g ≫ avgY N Y = avgY N Y := by
  rw [← QY_trY, ← Category.assoc, GY_QY]

theorem avgY_idem : avgY N Y ≫ avgY N Y = avgY N Y := by
  conv_lhs => rw [← QY_trY]
  rw [Category.assoc, ← Category.assoc (trY N Y), trY_QY, Category.id_comp, QY_trY]

theorem ker_QY (j : ℕ) (z z' : (CxN N Y).X j)
    (h : ((QY N Y).f j).hom z = ((QY N Y).f j).hom z') :
    ((avgY N Y).f j).hom z = ((avgY N Y).f j).hom z' := by
  rw [← QY_trY]
  change ((trY N Y).f j).hom (((QY N Y).f j).hom z) = ((trY N Y).f j).hom (((QY N Y).f j).hom z')
  rw [h]

theorem gamMap_tSum {V : Type} [AddCommGroup V] [Module ℚ V] (ρ : Representation ℚ K V) (g : K) (v : V) :
    gamMap N ρ g (tSum N ρ v) = tSum N ρ v := by
  rw [tSum_apply, map_sum]
  have key : ∀ x : K ⧸ N, gamMap N ρ g (Coinvariants.mk _ (ρ x.out v)) =
      gamMap N ρ ((g : K ⧸ N) * x).out (Coinvariants.mk _ v) := by
    intro x
    have e : ((g : K ⧸ N) * x) = ((g * x.out : K) : K ⧸ N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [e, gamMap_out, gamMap_mul]
    simp [gamMap]
  simp only [key]
  exact (Equiv.sum_comp (Equiv.mulLeft (g : K ⧸ N)) (fun y => gamMap N ρ y.out (Coinvariants.mk _ v))).trans rfl

theorem trY_GY (g : K) : trY N Y ≫ GY N Y g = trY N Y := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  refine ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun v => ?_))
  change gamMap N (Y.X i).ρ g (tMap N (Y.X i).ρ _ (Coinvariants.mk _ v)) = tMap N (Y.X i).ρ _ (Coinvariants.mk _ v)
  rw [tMap_mk, map_smul, gamMap_tSum]

theorem avgY_GY (g : K) : avgY N Y ≫ GY N Y g = avgY N Y := by
  rw [← QY_trY, Category.assoc, trY_GY]

end TernaryPeriodPolynomials.Argument.GroupHomology

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.Argument.HochschildSerre

/-- In the top degree, `cycleClass` is injective on cycles. -/
theorem cycleClass_injective_top (C : ChainComplex (ModuleCat.{0} ℚ) ℕ) (h4 : C.d 4 3 = 0)
    (z z' : C.X 3) (hz : (C.d 3 2).hom z = 0) (hz' : (C.d 3 2).hom z' = 0)
    (h : cycleClass C z hz = cycleClass C z' hz') : z = z' := by
  have hd : C.d ((ComplexShape.down ℕ).prev 3) 3 = 0 := by
    rw [show (ComplexShape.down ℕ).prev 3 = 4 from ChainComplex.prev ℕ 3]; exact h4
  let w : (C.sc 3).cycles := C.cyclesMk z 2 next32 hz - C.cyclesMk z' 2 next32 hz'
  have hw : (C.sc 3).homologyπ.hom w = 0 := by
    change (C.homologyπ 3).hom (C.cyclesMk z 2 next32 hz - C.cyclesMk z' 2 next32 hz') = 0
    rw [map_sub]
    exact sub_eq_zero.2 h
  obtain ⟨x, hx⟩ := moduleCat_boundary_of_homologyπ_eq_zero (C.sc 3) w hw
  have h1 : (C.sc 3).iCycles.hom ((C.sc 3).toCycles.hom x) = (C.sc 3).f.hom x := by
    have := congrArg (fun t => t.hom x) (C.sc 3).toCycles_i
    exact this
  have h2 : (C.sc 3).f.hom x = 0 := by
    have : (C.sc 3).f = C.d ((ComplexShape.down ℕ).prev 3) 3 := rfl
    rw [this, hd]; rfl
  have h3 : (C.sc 3).iCycles.hom w = z - z' := by
    change (C.iCycles 3).hom (C.cyclesMk z 2 next32 hz - C.cyclesMk z' 2 next32 hz') = z - z'
    rw [map_sub]
    exact congrArg₂ (· - ·) (HomologicalComplex.i_cyclesMk C z 2 next32 hz)
      (HomologicalComplex.i_cyclesMk C z' 2 next32 hz')
  rw [hx] at h1
  rw [h3, h2] at h1
  exact sub_eq_zero.1 h1

section Invariant

open TernaryPeriodPolynomials.Argument.GroupHomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {K : Type} [Group K] (N : Subgroup K) [N.Normal] [N.FiniteIndex]
  (R : ProjectiveResolution (Rep.trivial ℚ K ℚ)) (A : Rep.{0} ℚ K)

/-- **A top-degree cycle representing an `avgN`-fixed class is `trY`-image of its quotient.** -/
theorem invariant_of_avgN_fixed (h4 : (CxN N (YAR R A)).d 4 3 = 0)
    (w : groupHomology (Rep.res N.subtype A) 3) (hw : avgN N A 3 w = w)
    (ζ : (CxN N (YAR R A)).X 3) (hζ : ((CxN N (YAR R A)).d 3 2).hom ζ = 0)
    (hcl : cycleClass (CxN N (YAR R A)) ζ hζ = (eNR N R A 3).hom.hom w) :
    ((avgY N (YAR R A)).f 3).hom ζ = ζ ∧
    ζ = ((trY N (YAR R A)).f 3).hom (((QY N (YAR R A)).f 3).hom ζ) ∧
    ∃ hz' : ((CxK (YAR R A)).d 3 2).hom (((QY N (YAR R A)).f 3).hom ζ) = 0,
      cycleClass (CxK (YAR R A)) (((QY N (YAR R A)).f 3).hom ζ) hz' =
        (eKR R A 3).hom.hom (corN N A 3 w) := by
  have hza : ((CxN N (YAR R A)).d 3 2).hom (((avgY N (YAR R A)).f 3).hom ζ) = 0 := by
    have := congrArg (fun t => t.hom ζ) ((avgY N (YAR R A)).comm 3 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this, hζ, map_zero]
  have h1 : cycleClass (CxN N (YAR R A)) (((avgY N (YAR R A)).f 3).hom ζ) hza = cycleClass (CxN N (YAR R A)) ζ hζ := by
    rw [← homologyMap_cycleClass (avgY N (YAR R A)) ζ hζ hza, hcl, ← eNR_avgN' N R A 3 w, hw]
  have hfix := cycleClass_injective_top (CxN N (YAR R A)) h4 _ _ hza hζ h1
  refine ⟨hfix, ?_, ?_⟩
  · have e : ((avgY N (YAR R A)).f 3).hom ζ = ((trY N (YAR R A)).f 3).hom (((QY N (YAR R A)).f 3).hom ζ) := by
      rw [← QY_trY]; rfl
    exact hfix.symm.trans e
  · have hz' : ((CxK (YAR R A)).d 3 2).hom (((QY N (YAR R A)).f 3).hom ζ) = 0 := by
      have := congrArg (fun t => t.hom ζ) ((QY N (YAR R A)).comm 3 2)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this, hζ, map_zero]
    refine ⟨hz', ?_⟩
    rw [← homologyMap_cycleClass (QY N (YAR R A)) ζ hζ hz', hcl, eKR_corN]

end Invariant

end TernaryPeriodPolynomials.Argument.AppendixBResidue
