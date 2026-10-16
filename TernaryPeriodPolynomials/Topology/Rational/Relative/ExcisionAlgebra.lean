module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import TernaryPeriodPolynomials.GroupCohomology.Relative.ChainSequence

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeExcisionAlgebra
open CategoryTheory Limits

/-- The actual cokernel map of a square whose signed biproduct sequence is exact and epi is an isomorphism. -/
theorem cokernel_map_isIso_of_shortExact {C : Type*} [Category C] [Abelian C]
    {I U V S : C} (a : I ⟶ U) (b : I ⟶ V) (u : U ⟶ S) (v : V ⟶ S)
    (h : b ≫ v = a ≫ u)
    (he : (ShortComplex.mk (biprod.lift a (-b)) (biprod.desc u v)
      (by simp [biprod.lift_desc,Preadditive.neg_comp,h])).ShortExact) :
    IsIso (cokernel.map b u a v h) := by
  let Q := ShortComplex.mk (biprod.lift a (-b)) (biprod.desc u v)
    (by simp [biprod.lift_desc,Preadditive.neg_comp,h])
  have hQ : Q.ShortExact := he
  have : Epi Q.g := hQ.epi_g
  let t : S ⟶ cokernel b := hQ.exact.desc (biprod.desc 0 (cokernel.π b))
    (by simp [Q,biprod.lift_desc,Preadditive.neg_comp])
  have ht : biprod.desc u v ≫ t = biprod.desc 0 (cokernel.π b) := hQ.exact.g_desc _ _
  have hu : u ≫ t = 0 := by
    have h' := congrArg (fun f => biprod.inl ≫ f) ht
    simpa using h'
  have hv : v ≫ t = cokernel.π b := by
    have h' := congrArg (fun f => biprod.inr ≫ f) ht
    simpa using h'
  let s : cokernel u ⟶ cokernel b := cokernel.desc u t hu
  refine ⟨s, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π b)).mp
    simp only [cokernel.map,cokernel.π_desc_assoc,Category.assoc,s,cokernel.π_desc,Category.comp_id]
    exact hv
  · apply (cancel_epi (cokernel.π u)).mp
    simp only [s,cokernel.π_desc_assoc,Category.comp_id]
    apply (cancel_epi Q.g).mp
    change biprod.desc u v ≫ (t ≫ _) = biprod.desc u v ≫ _
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc,cokernel.condition]
      rw [← Category.assoc,hu,zero_comp]
    · simp only [biprod.inr_desc_assoc]
      rw [← Category.assoc,hv]
      simp [cokernel.map]


/-- A square of actual chain inclusions with quasi-isomorphisms on both absolute terms
induces a quasi-isomorphism of its actual relative cokernel complexes. -/
theorem cokernel_map_quasiIso {K L K' L' : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (i : K ⟶ L) (i' : K' ⟶ L') [Mono i] [Mono i']
    (p : K ⟶ K') (q : L ⟶ L') (h : i ≫ q = p ≫ i')
    [QuasiIso p] [QuasiIso q] :
    QuasiIso (cokernel.map i i' p q h) := by
  let φ : RelativeChainSequence.sequence i ⟶ RelativeChainSequence.sequence i' :=
    { τ₁ := p
      τ₂ := q
      τ₃ := cokernel.map i i' p q h
      comm₁₂ := h.symm
      comm₂₃ := by simp [RelativeChainSequence.sequence,cokernel.map] }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (RelativeChainSequence.shortExact i) (RelativeChainSequence.shortExact i') (by change QuasiIso p; infer_instance)
    (by change QuasiIso q; infer_instance)

end TernaryPoly.RelativeExcisionAlgebra
