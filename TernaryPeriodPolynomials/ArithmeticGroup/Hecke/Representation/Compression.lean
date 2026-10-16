module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.FixedHecke

@[expose] public section


/-!
# Compressions to fixed vectors and Schur's lemma for Hecke operators

For a subgroup `K` of `GL₂(𝔸)` let `V = σ.H^K`. The compressions `C_g = e ∘ π(g)|_V`, with `e` the
orthogonal projection onto `V`, form a `star`-closed irreducible family on `V`. This uses only
irreducibility of `σ`. Every Hecke operator of a finite double coset `K g K` restricts to `V` as
`#(KgK/K) · C_g`. Hence any Hecke operator commuting with all compressions is a scalar on `V`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.RepresentationTheory

variable (σ : CuspidalRepresentation) (K : Subgroup BinaryAdelicGL)

instance fixedVectors_completeSpace : CompleteSpace (fixedVectors σ K) :=
  (fixedVectors_isClosed σ K).completeSpace_coe

/-- The compression `e ∘ π(g)` to the fixed vectors. -/
def compression (g : BinaryAdelicGL) : fixedVectors σ K →L[ℂ] fixedVectors σ K :=
  (fixedVectors σ K).orthogonalProjectionOnto ∘L cuspOperator σ g ∘L (fixedVectors σ K).subtypeL

variable {σ K}

theorem inner_projection_fixed (x : σ.H) (w : fixedVectors σ K) :
    inner ℂ (((fixedVectors σ K).orthogonalProjectionOnto x : fixedVectors σ K) : σ.H) (w : σ.H) =
      inner ℂ x (w : σ.H) := by
  have h := Submodule.starProjection_inner_eq_zero (K := fixedVectors σ K) x w w.property
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

theorem inner_compression (g : BinaryAdelicGL) (v w : fixedVectors σ K) :
    inner ℂ (compression σ K g v) w = inner ℂ (σ.π g v) (w : σ.H) := by
  change inner ℂ (((fixedVectors σ K).orthogonalProjectionOnto (cuspOperator σ g v) :
    fixedVectors σ K) : σ.H) (w : σ.H) = _
  rw [inner_projection_fixed, cuspOperator_apply]

theorem compression_star (g : BinaryAdelicGL) :
    star (compression σ K g) = compression σ K g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_compression]
  conv_rhs => rw [← inner_conj_symm, inner_compression, inner_conj_symm]
  have hx : σ.π g (σ.π g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc inner ℂ (σ.π g⁻¹ (x : σ.H)) (y : σ.H)
      = inner ℂ (σ.π g (σ.π g⁻¹ (x : σ.H))) (σ.π g y) := (cuspOperator_inner σ g _ _).symm
    _ = inner ℂ (x : σ.H) (σ.π g y) := by rw [hx]

/-- The compressions act irreducibly on the fixed vectors. -/
theorem compression_irreducible (W : Submodule ℂ (fixedVectors σ K)) (hW : IsClosed (W : Set (fixedVectors σ K)))
    (hinv : ∀ T ∈ Set.range (compression σ K), ∀ v ∈ W, T v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let U : Submodule ℂ σ.H :=
    { carrier := {u | ∀ g : BinaryAdelicGL, ∀ w ∈ W, inner ℂ (σ.π g (w : σ.H)) u = 0}
      add_mem' := by
        intro a b ha hb g w hw
        rw [inner_add_right, ha g w hw, hb g w hw, add_zero]
      zero_mem' := by intro g w hw; simp
      smul_mem' := by
        intro c a ha g w hw
        rw [inner_smul_right, ha g w hw, mul_zero] }
  have hUc : IsClosed (U : Set σ.H) := by
    have : (U : Set σ.H) = ⋂ g : BinaryAdelicGL, ⋂ w : ↥W,
        {u | inner ℂ (σ.π g ((w : fixedVectors σ K) : σ.H)) u = 0} := by
      ext u; simp [U]
    rw [this]
    exact isClosed_iInter fun g => isClosed_iInter fun w =>
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hUi : ∀ h v, v ∈ U → σ.π h v ∈ U := by
    intro h v hv g w hw
    have key := hv (h⁻¹ * g) w hw
    have hinner := cuspOperator_inner σ h (σ.π (h⁻¹ * g) (w : σ.H)) v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at hinner
    rw [hinner, key]
  rcases σ.irreducible U hUc hUi with hbot | htop
  · right
    have : CompleteSpace W := hW.completeSpace_coe
    apply Submodule.orthogonal_eq_bot_iff.mp
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hmem : (u : σ.H) ∈ U := by
      intro g w hw
      rw [← inner_compression g w u]
      have h := (Submodule.mem_orthogonal' W u).mp hu _ (hinv _ ⟨g, rfl⟩ w hw)
      rw [← inner_conj_symm, h, map_zero]
    rw [hbot, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  · left
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hmem : ((w : fixedVectors σ K) : σ.H) ∈ U := by rw [htop]; trivial
    have := hmem 1 w hw
    rw [map_one, Module.End.one_apply, inner_self_eq_zero] at this
    exact Subtype.ext this

/-- **Schur's lemma on fixed vectors.** An operator on `σ.H^K` commuting with every compression
is a scalar. -/
theorem fixed_schur (A : fixedVectors σ K →L[ℂ] fixedVectors σ K)
    (hA : ∀ g, Commute A (compression σ K g)) :
    ∃ z : ℂ, ∀ v, A v = z • v := by
  rcases subsingleton_or_nontrivial (fixedVectors σ K) with hsub | hnt
  · exact ⟨0, fun v => Subsingleton.elim _ _⟩
  · obtain ⟨z, hz⟩ := eq_scalar_of_commute (Set.range (compression σ K))
      (by rintro _ ⟨g, rfl⟩; exact ⟨g⁻¹, (compression_star g).symm⟩)
      compression_irreducible A (by rintro _ ⟨g, rfl⟩; exact hA g)
    exact ⟨z, fun v => by rw [hz]; simp⟩

/-- On fixed vectors the Hecke operator of `K g K` is `#(KgK/K)` times the compression of `π(g)`. -/
theorem heckeOperator_eq_compression (T : DoubleCoset K) (v : fixedVectors σ K) :
    heckeOperator σ T v = ((T.reps.card : ℂ) • compression σ K T.g v : fixedVectors σ K) := by
  have hmem := heckeOperator_mem_fixed σ T v.property
  have : (⟨heckeOperator σ T v, hmem⟩ : fixedVectors σ K) = (T.reps.card : ℂ) • compression σ K T.g v := by
    apply ext_inner_right ℂ
    intro u
    rw [inner_smul_left, inner_compression]
    change inner ℂ (heckeOperator σ T v) (u : σ.H) = _
    rw [inner_heckeOperator_fixed σ T v.property u.property]
    simp
  rw [← this]

/-- **Hecke operators are scalars on fixed vectors**, as soon as the compression of the double coset
commutes with all compressions (commutativity of the relevant Hecke algebra). -/
theorem heckeOperator_scalar (T : DoubleCoset K)
    (hcomm : ∀ h, Commute (compression σ K T.g) (compression σ K h)) :
    ∃ z : ℂ, ∀ v ∈ fixedVectors σ K, heckeOperator σ T v = z • v := by
  obtain ⟨z, hz⟩ := fixed_schur (compression σ K T.g) hcomm
  refine ⟨(T.reps.card : ℂ) * z, fun v hv => ?_⟩
  rw [heckeOperator_eq_compression T ⟨v, hv⟩, hz]
  simp [smul_smul]

end TernaryPeriodPolynomials.RepresentationTheory
