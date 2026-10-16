module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Measure

@[expose] public section


/-!
# Integrals over a disjoint family of congruence cells (abstract form)

Formalized by Claude Sonnet 5.5.
Paper: "absolutely convergent ... Fubini".

If a function `F` on `𝔸_f² × ℝ²` vanishes off a countable disjoint family of measurable cells `S i ⊂ 𝔸_f²` of finite measure,
equals `G i (w)` on `S i × ℝ²`, with `G i` integrable and `i ↦ μ(S i) ∫‖G i‖` summable, then `F` is integrable and
`∫ F = Σ_i μ(S i) ∫ G i`.  (`cells_integral`; used for every cusp, both seed types, and every coefficient.)
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

/-- The finite congruence measure `μ × μ` on `𝔸_f²`. -/
abbrev finMeas2 : Measure (FiniteAdeles × FiniteAdeles) := finiteMeasure.prod finiteMeasure

/-- The measure `(μ × μ) × Lebesgue` on `𝔸_f² × ℝ²`. -/
abbrev nuZ : Measure ((FiniteAdeles × FiniteAdeles) × (Fin 2 → ℝ)) := finMeas2.prod (volume : Measure (Fin 2 → ℝ))

theorem setIntegral_cell_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Set (FiniteAdeles × FiniteAdeles))
    (g : (Fin 2 → ℝ) → E) :
    ∫ z in S ×ˢ (Set.univ : Set (Fin 2 → ℝ)), g z.2 ∂nuZ = finMeas2.real S • ∫ w, g w := by
  rw [← Measure.prod_restrict, Measure.restrict_univ, integral_fun_snd]
  simp [Measure.real]

theorem integrableOn_cell_snd {E : Type*} [NormedAddCommGroup E] (S : Set (FiniteAdeles × FiniteAdeles))
    (hS : finMeas2 S < ⊤) {g : (Fin 2 → ℝ) → E} (hg : Integrable g) :
    IntegrableOn (fun z => g z.2) (S ×ˢ (Set.univ : Set (Fin 2 → ℝ))) nuZ := by
  unfold IntegrableOn
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  have : IsFiniteMeasure (finMeas2.restrict S) := ⟨by rw [Measure.restrict_apply_univ]; exact hS⟩
  exact hg.comp_snd _

theorem cells_integral {ι : Type*} [Countable ι] (S : ι → Set (FiniteAdeles × FiniteAdeles))
    (hS : ∀ i, MeasurableSet (S i)) (hfin : ∀ i, finMeas2 (S i) < ⊤) (hd : Pairwise (Function.onFun Disjoint S))
    (Fz : (FiniteAdeles × FiniteAdeles) × (Fin 2 → ℝ) → ℂ) (G : ι → (Fin 2 → ℝ) → ℂ)
    (hon : ∀ i z, z.1 ∈ S i → Fz z = G i z.2) (hzero : ∀ z, (∀ i, z.1 ∉ S i) → Fz z = 0)
    (hG : ∀ i, Integrable (G i)) (hsum : Summable fun i => finMeas2.real (S i) * ∫ w, ‖G i w‖) :
    Integrable Fz nuZ ∧ ∫ z, Fz z ∂nuZ = ∑' i, (finMeas2.real (S i) : ℂ) * ∫ w, G i w := by
  set T : ι → Set ((FiniteAdeles × FiniteAdeles) × (Fin 2 → ℝ)) := fun i => S i ×ˢ Set.univ with hT
  have hTm : ∀ i, MeasurableSet (T i) := fun i => (hS i).prod MeasurableSet.univ
  have hTd : Pairwise (Function.onFun Disjoint T) := fun i j h => Set.disjoint_prod.2 (Or.inl (hd h))
  have hInt : ∀ i, IntegrableOn Fz (T i) nuZ := fun i =>
    (integrableOn_cell_snd (S i) (hfin i) (hG i)).congr_fun (fun z hz => (hon i z hz.1).symm) (hTm i)
  have hnorm : ∀ i, ∫ z in T i, ‖Fz z‖ ∂nuZ = finMeas2.real (S i) * ∫ w, ‖G i w‖ := by
    intro i
    calc ∫ z in T i, ‖Fz z‖ ∂nuZ = ∫ z in T i, (fun w => ‖G i w‖) z.2 ∂nuZ :=
          setIntegral_congr_fun (hTm i) (fun z hz => by simp only [hon i z hz.1])
      _ = _ := by rw [hT, setIntegral_cell_snd (S i) (fun w => ‖G i w‖), smul_eq_mul]
  have hUnion : IntegrableOn Fz (⋃ i, T i) nuZ :=
    integrableOn_iUnion_of_summable_integral_norm hInt (by simp_rw [hnorm]; exact hsum)
  have hz : ∀ z, z ∉ (⋃ i, T i) → Fz z = 0 := by
    intro z hz'
    exact hzero z (fun i hi => hz' (Set.mem_iUnion.2 ⟨i, hi, trivial⟩))
  refine ⟨hUnion.integrable_of_forall_notMem_eq_zero hz, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, integral_iUnion hTm hTd hUnion]
  refine tsum_congr fun i => ?_
  calc ∫ z in T i, Fz z ∂nuZ = ∫ z in T i, (fun w => G i w) z.2 ∂nuZ :=
        setIntegral_congr_fun (hTm i) (fun z hz => hon i z hz.1)
    _ = _ := by rw [hT, setIntegral_cell_snd (S i) (fun w => G i w), Complex.real_smul]

end TernaryPeriodPolynomials.Argument.FormClassK
