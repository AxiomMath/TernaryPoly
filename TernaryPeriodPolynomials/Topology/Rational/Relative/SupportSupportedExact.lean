module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportSupported

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open SphereOddDegree

/-- The two literal biproduct projections detect equality of module elements. -/
theorem module_biprod_element_ext {M N : ModuleCat.{0} ℚ} {x y : (M ⊞ N : ModuleCat.{0} ℚ)}
    (h₁ : (biprod.fst : M ⊞ N ⟶ M) x = (biprod.fst : M ⊞ N ⟶ M) y)
    (h₂ : (biprod.snd : M ⊞ N ⟶ N) x = (biprod.snd : M ⊞ N ⟶ N) y) : x = y := by
  have hx := congrArg (fun f : M ⊞ N ⟶ M ⊞ N => f x) (biprod.total (X := M) (Y := N))
  have hy := congrArg (fun f : M ⊞ N ⟶ M ⊞ N => f y) (biprod.total (X := M) (Y := N))
  change (biprod.inl : M ⟶ M ⊞ N) ((biprod.fst : M ⊞ N ⟶ M) x) + (biprod.inr : N ⟶ M ⊞ N) ((biprod.snd : M ⊞ N ⟶ N) x) = x at hx
  change (biprod.inl : M ⟶ M ⊞ N) ((biprod.fst : M ⊞ N ⟶ M) y) + (biprod.inr : N ⟶ M ⊞ N) ((biprod.snd : M ⊞ N ⟶ N) y) = y at hy
  rw [← hx, ← hy, h₁, h₂]

/-- The two literal chain-biproduct projections detect equality in every degree. -/
theorem chain_biprod_element_ext {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (n : ℕ)
    {x y : (K ⊞ L).X n}
    (h₁ : (biprod.fst : K ⊞ L ⟶ K).f n x = (biprod.fst : K ⊞ L ⟶ K).f n y)
    (h₂ : (biprod.snd : K ⊞ L ⟶ L).f n x = (biprod.snd : K ⊞ L ⟶ L).f n y) : x = y := by
  apply (ModuleCat.mono_iff_injective (biprodXIso K L n).hom).mp inferInstance
  apply module_biprod_element_ext
  · simpa only [← ModuleCat.comp_apply, biprodXIso_hom_fst] using h₁
  · simpa only [← ModuleCat.comp_apply, biprodXIso_hom_snd] using h₂

variable {X : Type} [TopologicalSpace X]

/-- The actual signed supported-chain row is exact in every degree, for arbitrary subsets. -/
theorem supportedRow_degree_exact (U V : Set X) (n : ℕ) :
    ((supportedRow U V).map (eval (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  let u := (biprod.fst : subChainComplex ℚ (TopCat.of X) U ⊞
    subChainComplex ℚ (TopCat.of X) V ⟶ _).f n z
  let v := (biprod.snd : subChainComplex ℚ (TopCat.of X) U ⊞
    subChainComplex ℚ (TopCat.of X) V ⟶ _).f n z
  have huv : u.val + v.val = 0 := by
    change (supportedSum U V).f n z = 0 at hz
    unfold supportedSum at hz
    rw [biprod.desc_eq] at hz
    exact hz
  have huV : u.val ∈ subChainSubmodule ℚ (TopCat.of X) V n := by
    rw [eq_neg_of_add_eq_zero_left huv]
    exact Submodule.neg_mem _ v.property
  let c : (subChainComplex ℚ (TopCat.of X) (U ∩ V)).X n :=
    ⟨u.val, by rw [supported_inter]; exact ⟨u.property, huV⟩⟩
  refine ⟨c, ?_⟩
  apply chain_biprod_element_ext n
  · have h := congrArg (fun f => f.f n c)
      (biprod.lift_fst (subChainInclusion (R := ℚ) (X := TopCat.of X) (U ∩ V) U Set.inter_subset_left)
        (-(subChainInclusion _ _ Set.inter_subset_right)))
    exact h
  · have h := congrArg (fun f => f.f n c)
      (biprod.lift_snd (subChainInclusion (R := ℚ) (X := TopCat.of X) (U ∩ V) U Set.inter_subset_left)
        (-(subChainInclusion _ _ Set.inter_subset_right)))
    change (biprod.snd : _ ⟶ subChainComplex ℚ (TopCat.of X) V).f n
      ((supportedDiagonal U V).f n c) = v
    erw [h]
    apply Subtype.ext
    change -u.val = v.val
    simpa using congrArg Neg.neg (eq_neg_of_add_eq_zero_left huv)

/-- Actual supported singular chains form an exact signed row, without a covering hypothesis. -/
theorem supportedRow_exact (U V : Set X) : (supportedRow U V).Exact :=
  exact_of_degreewise_exact _ (supportedRow_degree_exact U V)

/-- The actual signed intersection inclusion is a chain monomorphism. -/
instance supportedDiagonal_mono (U V : Set X) : Mono (supportedDiagonal U V) := by
  have hi : Mono (subChainInclusion (R := ℚ) (X := TopCat.of X) (U ∩ V) U Set.inter_subset_left) := by
    apply mono_of_mono_f
    intro n
    apply (ModuleCat.mono_iff_injective _).mpr
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : subChainSubmodule ℚ (TopCat.of X) U n => z.val) h
  exact mono_of_mono_fac (biprod.lift_fst _ _)

/-- The actual small sum of U- and V-supported chains, defined by its signed intersection relation. -/
abbrev supportedSmallSum (U V : Set X) := cokernel (supportedDiagonal U V)

/-- The small sum embeds literally in full chains through the actual sum map. -/
def supportedSmallSumInclusion (U V : Set X) : supportedSmallSum U V ⟶ chains X :=
  cokernel.desc (supportedDiagonal U V) (supportedSum U V) (supportedDiagonal_sum U V)

/-- Exactness of the actual supported row proves that its small sum injects in full chains. -/
instance supportedSmallSumInclusion_mono (U V : Set X) : Mono (supportedSmallSumInclusion U V) :=
  (supportedRow_exact U V).mono_cokernelDesc

end TernaryPoly.RationalRelativeSupport
