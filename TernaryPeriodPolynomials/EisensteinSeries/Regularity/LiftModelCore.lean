module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.FiniteModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.CompletionRepresentation

@[expose] public section


/-!
# Fixed vectors of the completion of a pre-unitary representation

Let `ρ` be a norm-preserving representation of `GL₂(𝔸_f)` on an inner product space `V` all of
whose vectors are fixed by some open compact subgroup, and let `σ = completionRep ρ _` be the
extension to the Hilbert space completion `Ṽ`.  If the fixed spaces `V^U` are finite dimensional
for every open compact subgroup `U`, then so are the fixed spaces `Ṽ^U`, and every smooth vector
of `Ṽ` lies in `V`.  The proof averages over the finite quotient `U / (U ∩ W)`, where `W` is an
open subgroup fixing a given vector: the average of a vector of `V` lies in `V^U` and is at least
as close as the vector to any `U`-fixed vector of `Ṽ`.  The orbit maps of vectors of `V` are
locally constant, hence continuous (`continuous_orbit_of_fixed`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
open TernaryPeriodPolynomials.Automorphic.CompletionRepresentation

namespace TernaryPeriodPolynomials.Regularity

namespace CompletionFixed

section Rep

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem rep_mul_apply (ρ : Representation ℂ G M) (a b : G) (m : M) :
    ρ (a * b) m = ρ a (ρ b m) := by
  rw [map_mul, Module.End.mul_apply]

theorem rep_one_apply (ρ : Representation ℂ G M) (m : M) : ρ 1 m = m := by
  rw [map_one, Module.End.one_apply]

end Rep

/-! ### Locally constant orbit maps -/

section Orbit

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- If an open subgroup fixes `v`, the orbit map of `v` is locally constant, hence continuous. -/
theorem continuous_orbit_of_fixed (ρ : Representation ℂ BinaryFiniteGL V) (v : V)
    {W : Subgroup BinaryFiniteGL} (hW : IsOpen (W : Set BinaryFiniteGL))
    (hv : ∀ w : W, ρ w v = v) : Continuous fun g => ρ g v := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hmem : (fun g' : BinaryFiniteGL => g⁻¹ * g') ⁻¹' (W : Set BinaryFiniteGL) ∈ nhds g := by
    refine (hW.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
    show g⁻¹ * g ∈ (W : Set BinaryFiniteGL)
    rw [inv_mul_cancel]
    exact W.one_mem
  have heq : (fun g' => ρ g' v) =ᶠ[nhds g] fun _ => ρ g v := by
    filter_upwards [hmem] with g' hg'
    have hg'W : g⁻¹ * g' ∈ W := hg'
    calc ρ g' v = ρ (g * (g⁻¹ * g')) v := by rw [mul_inv_cancel_left]
      _ = ρ g (ρ (g⁻¹ * g') v) := rep_mul_apply ρ g (g⁻¹ * g') v
      _ = ρ g v := by rw [show ρ (g⁻¹ * g') v = v from hv ⟨g⁻¹ * g', hg'W⟩]
  exact continuousAt_const.congr heq.symm

end Orbit

/-! ### Averaging over a compact open subgroup -/

section Average

/-- For a compact subgroup `U` and an open subgroup `V` fixing `m`, the average of the translates
`ρ (g i) m`, with `g i` running over representatives of the finite quotient `U / (U ∩ V)`, is fixed
by `U`. -/
theorem exists_average {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : Type*} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    {U V : Subgroup G} (hU : IsCompact (U : Set G)) (hV : IsOpen (V : Set G)) {m : M}
    (hm : ∀ v : V, ρ v m = m) :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → G), 0 < Fintype.card ι ∧ (∀ i, g i ∈ U) ∧
      ∀ u : U, ρ u ((Fintype.card ι : ℂ)⁻¹ • ∑ i, ρ (g i) m) =
        (Fintype.card ι : ℂ)⁻¹ • ∑ i, ρ (g i) m := by
  classical
  have : CompactSpace U := isCompact_iff_compactSpace.1 hU
  have hW : IsOpen ((V.subgroupOf U : Subgroup U) : Set U) := by
    show IsOpen ((fun x : U => (x : G)) ⁻¹' (V : Set G))
    exact hV.preimage continuous_subtype_val
  have : Finite (U ⧸ V.subgroupOf U) := Subgroup.quotient_finite_of_isOpen _ hW
  let _ : Fintype (U ⧸ V.subgroupOf U) := Fintype.ofFinite _
  have : Nonempty (U ⧸ V.subgroupOf U) := ⟨((1 : U) : U ⧸ V.subgroupOf U)⟩
  have hfix : ∀ y x : U, ((y⁻¹ * x : U) : G) ∈ V → ρ (y : G) m = ρ (x : G) m := by
    intro y x hyx
    have h3 : ρ ((y⁻¹ * x : U) : G) m = m := hm ⟨_, hyx⟩
    have h4 : (y : G) * ((y⁻¹ * x : U) : G) = (x : G) := by
      rw [← Subgroup.coe_mul, mul_inv_cancel_left]
    calc ρ (y : G) m = ρ (y : G) (ρ ((y⁻¹ * x : U) : G) m) := by rw [h3]
      _ = ρ ((y : G) * ((y⁻¹ * x : U) : G)) m := (rep_mul_apply ρ _ _ m).symm
      _ = ρ (x : G) m := by rw [h4]
  have hΦ : ∀ x : U, ρ ((((x : U ⧸ V.subgroupOf U).out : U)) : G) m = ρ (x : G) m := by
    intro x
    have h1 : ((((x : U ⧸ V.subgroupOf U).out : U)) : U ⧸ V.subgroupOf U) =
        (x : U ⧸ V.subgroupOf U) := QuotientGroup.out_eq' _
    have h2 := QuotientGroup.eq.1 h1
    exact hfix _ _ (Subgroup.mem_subgroupOf.1 h2)
  refine ⟨U ⧸ V.subgroupOf U, inferInstance, fun q => (((q.out : U)) : G), Fintype.card_pos,
    fun q => (q.out : U).2, ?_⟩
  intro u
  have key : ∀ q : U ⧸ V.subgroupOf U,
      ρ (u : G) (ρ (((q.out : U)) : G) m) = ρ ((((u • q).out : U)) : G) m := by
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    have hsmul : u • (x : U ⧸ V.subgroupOf U) = ((u * x : U) : U ⧸ V.subgroupOf U) := rfl
    rw [hsmul, hΦ x, hΦ (u * x)]
    exact (rep_mul_apply ρ (u : G) (x : G) m).symm
  rw [map_smul, map_sum]
  congr 1
  calc ∑ q : U ⧸ V.subgroupOf U, ρ (u : G) (ρ (((q.out : U)) : G) m)
      = ∑ q : U ⧸ V.subgroupOf U, ρ ((((u • q).out : U)) : G) m :=
        Finset.sum_congr rfl fun q _ => key q
    _ = ∑ q : U ⧸ V.subgroupOf U, ρ (((q.out : U)) : G) m :=
        Equiv.sum_comp (MulAction.toPerm u : Equiv.Perm (U ⧸ V.subgroupOf U))
          (fun q : U ⧸ V.subgroupOf U => ρ (((q.out : U)) : G) m)

/-- Averaging a family of norm-preserving maps does not increase the distance to a common fixed
vector. -/
theorem norm_average_sub_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {ι : Type*}
    [Fintype ι] (hι : 0 < Fintype.card ι) (T : ι → X →ₗ[ℂ] X) (hT : ∀ i x, ‖T i x‖ = ‖x‖)
    {e : X} (he : ∀ i, T i e = e) (x : X) :
    ‖(Fintype.card ι : ℂ)⁻¹ • (∑ i, T i x) - e‖ ≤ ‖x - e‖ := by
  have hN : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hι.ne'
  have hNr : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 hι
  have hsum : (∑ i, T i e) = (Fintype.card ι : ℂ) • e := by
    simp only [he, Finset.sum_const, Finset.card_univ]
    exact (Nat.cast_smul_eq_nsmul (R := ℂ) _ _).symm
  have h1 : (Fintype.card ι : ℂ)⁻¹ • (∑ i, T i x) - e =
      (Fintype.card ι : ℂ)⁻¹ • (∑ i, T i (x - e)) := by
    simp only [map_sub, Finset.sum_sub_distrib, hsum, smul_sub, smul_smul, inv_mul_cancel₀ hN,
      one_smul]
  have hbound : ‖∑ i, T i (x - e)‖ ≤ (Fintype.card ι : ℝ) * ‖x - e‖ := by
    calc ‖∑ i, T i (x - e)‖ ≤ ∑ i, ‖T i (x - e)‖ := norm_sum_le _ _
      _ = ∑ _i : ι, ‖x - e‖ := Finset.sum_congr rfl fun i _ => hT i (x - e)
      _ = (Fintype.card ι : ℝ) * ‖x - e‖ := by simp
  have hnorm : ‖((Fintype.card ι : ℕ) : ℂ)⁻¹‖ = ((Fintype.card ι : ℕ) : ℝ)⁻¹ := by simp
  rw [h1, norm_smul, hnorm]
  calc ((Fintype.card ι : ℕ) : ℝ)⁻¹ * ‖∑ i, T i (x - e)‖
      ≤ ((Fintype.card ι : ℕ) : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * ‖x - e‖) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hNr.le)
    _ = ‖x - e‖ := inv_mul_cancel_left₀ hNr.ne' _

end Average

/-! ### The completion -/

section Completion

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The inclusion of `V` into its completion, as a linear map. -/
def coeLin (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V →ₗ[ℂ] UniformSpace.Completion V :=
  (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := V)).toLinearMap

theorem coeLin_apply (v : V) : coeLin V v = (v : UniformSpace.Completion V) := rfl

theorem coeLin_injective : Function.Injective (coeLin V) := fun _ _ h =>
  UniformSpace.Completion.coe_injective (α := V) h

/-- Every vector of `V` is fixed by an open compact subgroup of `GL₂(𝔸_f)`. -/
def AllSmooth (ρ : Representation ℂ BinaryFiniteGL V) : Prop :=
  ∀ v : V, ∃ W : Subgroup BinaryFiniteGL, IsOpenCompact W ∧ ∀ w : W, ρ w v = v

variable (ρ : Representation ℂ BinaryFiniteGL V) (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖)

/-- The inclusion `V → Ṽ` maps smooth vectors to smooth vectors. -/
theorem coe_mem_finiteSmooth (hsm : AllSmooth ρ) (v : V) :
    coeLin V v ∈ finiteSmooth (completionRep ρ hρ) := by
  obtain ⟨W, hW, hv⟩ := hsm v
  refine ⟨W, hW, fun w => ?_⟩
  rw [coeLin_apply, completionRep_coe, hv w]

/-- The `U`-fixed vectors of the completion are the closure of the image of the `U`-fixed vectors
of `V`, which is closed since it is finite dimensional. -/
theorem fixed_completion_le_map (hsm : AllSmooth ρ) {U : Subgroup BinaryFiniteGL}
    (hU : IsCompact (U : Set BinaryFiniteGL)) [FiniteDimensional ℂ (fixedSubmodule ρ U)] :
    fixedSubmodule (completionRep ρ hρ) U ≤ (fixedSubmodule ρ U).map (coeLin V) := by
  intro e he
  have hclosed : IsClosed (((fixedSubmodule ρ U).map (coeLin V) :
      Submodule ℂ (UniformSpace.Completion V)) : Set (UniformSpace.Completion V)) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : e ∈ closure (((fixedSubmodule ρ U).map (coeLin V) :
      Submodule ℂ (UniformSpace.Completion V)) : Set (UniformSpace.Completion V)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := Metric.denseRange_iff.mp
      (UniformSpace.Completion.denseRange_coe : DenseRange ((↑) : V → UniformSpace.Completion V))
      e ε hε
    obtain ⟨W, hW, hWm⟩ := hsm m
    obtain ⟨ι, hι, g, hpos, hgU, hinv⟩ := exists_average ρ hU hW.1 hWm
    obtain ⟨P, hPdef⟩ : ∃ P : V, P = (Fintype.card ι : ℂ)⁻¹ • ∑ i, ρ (g i) m := ⟨_, rfl⟩
    have hPmem : P ∈ fixedSubmodule ρ U := by
      rw [hPdef]
      exact (mem_fixedSubmodule ρ).2 hinv
    refine ⟨coeLin V P, Submodule.mem_map_of_mem hPmem, ?_⟩
    have hcoe : coeLin V P =
        (Fintype.card ι : ℂ)⁻¹ • ∑ i, completionRep ρ hρ (g i) (m : UniformSpace.Completion V) := by
      rw [hPdef, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coeLin_apply, completionRep_coe]
    have hle := norm_average_sub_le hpos (fun i => completionRep ρ hρ (g i))
      (fun i x => completionRep_norm ρ hρ (g i) x) (e := e)
      (fun i => he ⟨g i, hgU i⟩) (m : UniformSpace.Completion V)
    calc dist e (coeLin V P) = ‖coeLin V P - e‖ := by rw [dist_comm, dist_eq_norm]
      _ = ‖(Fintype.card ι : ℂ)⁻¹ •
            (∑ i, completionRep ρ hρ (g i) (m : UniformSpace.Completion V)) - e‖ := by
          rw [hcoe]
      _ ≤ ‖(m : UniformSpace.Completion V) - e‖ := hle
      _ = dist e (m : UniformSpace.Completion V) := by rw [dist_comm, dist_eq_norm]
      _ < ε := hm
  rw [hclosed.closure_eq] at hmem
  exact hmem

/-- The fixed spaces of the completion are finite dimensional when those of `V` are. -/
theorem finiteDimensional_fixed_completion (hsm : AllSmooth ρ)
    (hfin : ∀ U : Subgroup BinaryFiniteGL, IsOpenCompact U →
      FiniteDimensional ℂ (fixedSubmodule ρ U))
    {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U) :
    FiniteDimensional ℂ (fixedSubmodule (completionRep ρ hρ) U) := by
  have := hfin U hU
  have : FiniteDimensional ℂ ((fixedSubmodule ρ U).map (coeLin V)) := inferInstance
  exact Submodule.finiteDimensional_of_le (fixed_completion_le_map ρ hρ hsm hU.2)

/-- Every smooth vector of the completion lies in `V`. -/
theorem finiteSmooth_completion_le (hsm : AllSmooth ρ)
    (hfin : ∀ U : Subgroup BinaryFiniteGL, IsOpenCompact U →
      FiniteDimensional ℂ (fixedSubmodule ρ U)) :
    finiteSmooth (completionRep ρ hρ) ≤ LinearMap.range (coeLin V) := by
  rintro e ⟨U, hU, he⟩
  have := hfin U hU
  obtain ⟨v, -, rfl⟩ := Submodule.mem_map.1 (fixed_completion_le_map ρ hρ hsm hU.2 he)
  exact LinearMap.mem_range_self _ v

end Completion

end CompletionFixed

end TernaryPeriodPolynomials.Regularity

end
