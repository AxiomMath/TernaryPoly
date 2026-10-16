module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.GelfandTrick

@[expose] public section


/-!
# Local Hecke operators at arbitrary level elsewhere

Let `Kl ≤ Gl` (the local group at one place) and `K'` a subgroup commuting with `Gl` (the level
at the other places). Assume every `h ∈ GL₂(𝔸)` factors as `u · x` with `x ∈ Gl` and `u`
commuting with `Gl`. A Gelfand involution for `Kl` that is Cartan on `Gl` then makes every local
Hecke operator of `Kl g Kl` (`g ∈ Gl`) act by a scalar on the vectors fixed by `Kl ⊔ K'`.

This is the version needed for inducing data of level `K₁(3)`, with the place `p ≠ 3`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.RepresentationTheory

variable {σ : CuspidalRepresentation}

theorem fixedVectors_sup {A B : Subgroup BinaryAdelicGL} {v : σ.H} :
    v ∈ fixedVectors σ (A ⊔ B) ↔ v ∈ fixedVectors σ A ∧ v ∈ fixedVectors σ B := by
  constructor
  · intro h
    exact ⟨fun k => h ⟨k.val, le_sup_left (a := A) k.property⟩,
      fun k => h ⟨k.val, le_sup_right (a := A) k.property⟩⟩
  · rintro ⟨hA, hB⟩
    let S : Subgroup BinaryAdelicGL :=
      { carrier := {g | σ.π g v = v}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hle : A ⊔ B ≤ S := sup_le (fun a ha => hA ⟨a, ha⟩) (fun b hb => hB ⟨b, hb⟩)
    intro k
    exact hle k.property

/-- Projections onto fixed vectors of commuting subgroups commute. -/
theorem starProjection_comm_of_commute {A B : Subgroup BinaryAdelicGL}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (x : σ.H) :
    (fixedVectors σ A).starProjection ((fixedVectors σ B).starProjection x) =
      (fixedVectors σ B).starProjection ((fixedVectors σ A).starProjection x) := by
  set eA := (fixedVectors σ A).starProjection
  set eB := (fixedVectors σ B).starProjection
  -- `eB` commutes with `π a` for `a ∈ A`
  have hBpi : ∀ a ∈ A, ∀ y, eB (σ.π a y) = σ.π a (eB y) := fun a ha y =>
    projection_pi_comm a (fun b => hAB a ha b.val b.property) y
  have hBfix : ∀ y ∈ fixedVectors σ A, eB y ∈ fixedVectors σ A := by
    intro y hy k
    rw [← hBpi k.val k.property, hy k]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hBfix _ (Submodule.starProjection_apply_mem _ x)
  · intro w hw
    rw [← map_sub, Submodule.inner_starProjection_left_eq_right]
    exact Submodule.starProjection_inner_eq_zero x _ (hBfix w hw)

/-- The projection onto `σ.H^(A ⊔ B)` is the product of the two projections. -/
theorem starProjection_sup {A B : Subgroup BinaryAdelicGL}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (x : σ.H) :
    (fixedVectors σ (A ⊔ B)).starProjection x =
      (fixedVectors σ A).starProjection ((fixedVectors σ B).starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [fixedVectors_sup]
    refine ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
    rw [starProjection_comm_of_commute hAB]
    exact Submodule.starProjection_apply_mem _ _
  · intro w hw
    obtain ⟨hwA, hwB⟩ := fixedVectors_sup.mp hw
    rw [inner_sub_left, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hwA, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hwB, sub_self]

theorem pi_comm_apply {a b : BinaryAdelicGL} (h : a * b = b * a) (y : σ.H) :
    σ.π a (σ.π b y) = σ.π b (σ.π a y) := by
  rw [← Module.End.mul_apply, ← map_mul, h, map_mul, Module.End.mul_apply]

/-- **Local Hecke operators act by scalars** on vectors fixed by `Kl ⊔ K'`. -/
theorem localHecke_scalar (Kl K' Gl : Subgroup BinaryAdelicGL) (hKl : Kl ≤ Gl)
    (hcomm : ∀ k ∈ K', ∀ x ∈ Gl, k * x = x * k)
    (decomp : ∀ h : BinaryAdelicGL, ∃ u x : BinaryAdelicGL,
      h = u * x ∧ x ∈ Gl ∧ ∀ y ∈ Gl, u * y = y * u)
    (J : GelfandInvolution Kl) (hGlF : Gl ≤ J.F)
    (cosets : ∀ x ∈ Gl, ∃ T : DoubleCoset Kl, T.g = x)
    (T : DoubleCoset Kl) (hT : T.g ∈ Gl) :
    ∃ z : ℂ, ∀ v ∈ fixedVectors σ (Kl ⊔ K'), heckeOperator σ T v = z • v := by
  set K := Kl ⊔ K'
  set V := fixedVectors σ K
  set eL := (fixedVectors σ Kl).starProjection
  set eP := (fixedVectors σ K').starProjection
  have hLP : ∀ a ∈ Kl, ∀ b ∈ K', a * b = b * a := fun a ha b hb => (hcomm b hb a (hKl ha)).symm
  have heV : ∀ x, V.starProjection x = eL (eP x) := fun x => starProjection_sup hLP x
  have hcommLP : ∀ x, eL (eP x) = eP (eL x) := fun x => starProjection_comm_of_commute hLP x
  -- elements of `Gl` commute with `eP`
  have hGlP : ∀ x ∈ Gl, ∀ y, eP (σ.π x y) = σ.π x (eP y) := fun x hx y =>
    projection_pi_comm x (fun k => (hcomm k.val k.property x hx).symm) y
  have hrepsGl : ∀ r ∈ T.reps, r ∈ Gl := by
    intro r hr
    obtain ⟨a, b, rfl⟩ := T.inDouble r hr
    exact Gl.mul_mem (Gl.mul_mem (hKl a.property) hT) (hKl b.property)
  have hn : (T.reps.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr T.reps_nonempty).ne'
  -- the Hecke operator on `Kl`-fixed vectors
  have hhecke : ∀ y ∈ fixedVectors σ Kl, heckeOperator σ T y = (T.reps.card : ℂ) • eL (σ.π T.g y) := by
    intro y hy
    have h1 := compression_coe_eq (σ := σ) T ⟨y, hy⟩
    rw [compression_coe] at h1
    change eL (σ.π T.g y) = _ at h1
    rw [h1, heckeOperator_apply, smul_smul, mul_inv_cancel₀ hn, one_smul]
  -- the Hecke operator preserves `V`
  have hheckeV : ∀ v ∈ V, heckeOperator σ T v ∈ V := by
    intro v hv
    obtain ⟨hvL, hvP⟩ := fixedVectors_sup.mp hv
    rw [fixedVectors_sup]
    refine ⟨heckeOperator_mem_fixed σ T hvL, ?_⟩
    intro k
    rw [heckeOperator_apply, map_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [pi_comm_apply (hcomm k.val k.property r (hrepsGl r hr)), hvP k]
  -- `Kl`-fixedness is preserved by `eP`
  have hPfix : ∀ y ∈ fixedVectors σ Kl, eP y ∈ fixedVectors σ Kl := by
    intro y hy k
    rw [← hGlP k.val (hKl k.property), hy k]
  let A : V →L[ℂ] V := V.orthogonalProjectionOnto ∘L heckeOperator σ T ∘L V.subtypeL
  have hA : ∀ v : V, ((A v : V) : σ.H) = heckeOperator σ T v := by
    intro v
    change V.starProjection (heckeOperator σ T v) = _
    exact Submodule.starProjection_eq_self_iff.mpr (hheckeV v v.property)
  have hcommA : ∀ h, Commute A (compression σ K h) := by
    intro h
    -- commutation with every compression
    obtain ⟨u, x, rfl, hx, hu⟩ := decomp h
    obtain ⟨Tx, rfl⟩ := cosets x hx
    have huL : ∀ y, eL (σ.π u y) = σ.π u (eL y) := fun y =>
      projection_pi_comm u (fun k => hu k.val (hKl k.property)) y
    ext1 v
    apply Subtype.ext
    change ((A (compression σ K (u * Tx.g) v) : V) : σ.H) = ((compression σ K (u * Tx.g) (A v) : V) : σ.H)
    rw [hA, compression_coe, compression_coe, hA, heV, heV]
    set y := eP (σ.π u v) with hy
    have hvL : (v : σ.H) ∈ fixedVectors σ Kl := (fixedVectors_sup.mp v.property).1
    have hyL : y ∈ fixedVectors σ Kl := by
      apply hPfix
      intro k
      rw [pi_comm_apply (hu k.val (hKl k.property)).symm, hvL k]
    have hLHS : eP (σ.π (u * Tx.g) v) = σ.π Tx.g y := by
      rw [map_mul, Module.End.mul_apply, pi_comm_apply (hu _ hx), hGlP _ hx]
    rw [hLHS]
    rw [hhecke _ (Submodule.starProjection_apply_mem _ _)]
    rw [hhecke _ hvL]
    have hRHS : eL (eP (σ.π (u * Tx.g) ((T.reps.card : ℂ) • eL (σ.π T.g v)))) =
        (T.reps.card : ℂ) • eL (σ.π Tx.g (eL (σ.π T.g y))) := by
      rw [map_smul, map_smul, map_smul, map_mul, Module.End.mul_apply]
      congr 1
      rw [pi_comm_apply (hu _ hx), ← huL, pi_comm_apply (hu _ hT), hGlP _ hx, ← hcommLP,
        hGlP _ hT]
    rw [hRHS]
    congr 1
    -- local commutation of compressions for `Kl`
    have key := compression_commute (σ := σ) J T Tx (hGlF hT) (hGlF hx)
    have := congrArg (fun F => ((F ⟨y, hyL⟩ : fixedVectors σ Kl) : σ.H)) key.eq
    exact this

  obtain ⟨z, hz⟩ := fixed_schur A hcommA
  refine ⟨z, fun v hv => ?_⟩
  have := congrArg Subtype.val (hz ⟨v, hv⟩)
  rw [hA] at this
  exact this
/-- Compressions of local elements commute with all compressions, at level `Kl ⊔ K'`. -/
theorem compression_local_commute (Kl K' Gl : Subgroup BinaryAdelicGL) (hKl : Kl ≤ Gl)
    (hcomm : ∀ k ∈ K', ∀ x ∈ Gl, k * x = x * k)
    (decomp : ∀ h : BinaryAdelicGL, ∃ u x : BinaryAdelicGL,
      h = u * x ∧ x ∈ Gl ∧ ∀ y ∈ Gl, u * y = y * u)
    (J : GelfandInvolution Kl) (hGlF : Gl ≤ J.F)
    (cosets : ∀ x ∈ Gl, ∃ T : DoubleCoset Kl, T.g = x)
    (g : BinaryAdelicGL) (hg : g ∈ Gl) (h : BinaryAdelicGL) :
    Commute (compression σ (Kl ⊔ K') g) (compression σ (Kl ⊔ K') h) := by
  set K := Kl ⊔ K'
  set V := fixedVectors σ K
  set eL := (fixedVectors σ Kl).starProjection
  set eP := (fixedVectors σ K').starProjection
  have hLP : ∀ a ∈ Kl, ∀ b ∈ K', a * b = b * a := fun a ha b hb => (hcomm b hb a (hKl ha)).symm
  have heV : ∀ x, V.starProjection x = eL (eP x) := fun x => starProjection_sup hLP x
  have hcommLP : ∀ x, eL (eP x) = eP (eL x) := fun x => starProjection_comm_of_commute hLP x
  have hGlP : ∀ x ∈ Gl, ∀ y, eP (σ.π x y) = σ.π x (eP y) := fun x hx y =>
    projection_pi_comm x (fun k => (hcomm k.val k.property x hx).symm) y
  have hPfix : ∀ y ∈ fixedVectors σ Kl, eP y ∈ fixedVectors σ Kl := by
    intro y hy k
    rw [← hGlP k.val (hKl k.property), hy k]
  obtain ⟨u, x, rfl, hx, hu⟩ := decomp h
  obtain ⟨Tx, rfl⟩ := cosets x hx
  obtain ⟨Tg, rfl⟩ := cosets g hg
  have huL : ∀ y, eL (σ.π u y) = σ.π u (eL y) := fun y =>
    projection_pi_comm u (fun k => hu k.val (hKl k.property)) y
  ext1 v
  apply Subtype.ext
  change ((compression σ K Tg.g (compression σ K (u * Tx.g) v) : V) : σ.H) =
    ((compression σ K (u * Tx.g) (compression σ K Tg.g v) : V) : σ.H)
  rw [compression_coe, compression_coe, compression_coe, compression_coe, heV, heV, heV, heV]
  set y := eP (σ.π u v) with hy
  have hvL : (v : σ.H) ∈ fixedVectors σ Kl := (fixedVectors_sup.mp v.property).1
  have hvP : (v : σ.H) ∈ fixedVectors σ K' := (fixedVectors_sup.mp v.property).2
  have hyL : y ∈ fixedVectors σ Kl := by
    apply hPfix
    intro k
    rw [pi_comm_apply (hu k.val (hKl k.property)).symm, hvL k]
  have hLHS : eP (σ.π (u * Tx.g) v) = σ.π Tx.g y := by
    rw [map_mul, Module.End.mul_apply, pi_comm_apply (hu _ hx), hGlP _ hx]
  have hPv : eP (v : σ.H) = v := Submodule.starProjection_eq_self_iff.mpr hvP
  have hPy : eP (eL (σ.π Tx.g y)) = eL (σ.π Tx.g y) := by
    rw [← hcommLP, hGlP _ hx, hy,
      Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
  have hRHS : eL (eP (σ.π (u * Tx.g) (eL (σ.π Tg.g v)))) = eL (σ.π Tx.g (eL (σ.π Tg.g y))) := by
    rw [map_mul, Module.End.mul_apply]
    rw [pi_comm_apply (hu _ hx), ← huL, pi_comm_apply (hu _ hg), hGlP _ hx, ← hcommLP,
      hGlP _ hg]
  rw [hLHS, hGlP _ hg, hGlP _ hg, hPv, hPy, hRHS]
  have key := compression_commute (σ := σ) J Tg Tx (hGlF hg) (hGlF hx)
  have := congrArg (fun F => ((F ⟨y, hyL⟩ : fixedVectors σ Kl) : σ.H)) key.eq
  exact this

/-- **The compressed local Hecke algebra acts by scalars.** Any finite combination of compressions
of local elements is a scalar on `σ.H^(Kl ⊔ K')`. -/
theorem localCombination_scalar (Kl K' Gl : Subgroup BinaryAdelicGL) (hKl : Kl ≤ Gl)
    (hcomm : ∀ k ∈ K', ∀ x ∈ Gl, k * x = x * k)
    (decomp : ∀ h : BinaryAdelicGL, ∃ u x : BinaryAdelicGL,
      h = u * x ∧ x ∈ Gl ∧ ∀ y ∈ Gl, u * y = y * u)
    (J : GelfandInvolution Kl) (hGlF : Gl ≤ J.F)
    (cosets : ∀ x ∈ Gl, ∃ T : DoubleCoset Kl, T.g = x)
    {ι : Type*} (S : Finset ι) (c : ι → ℂ) (x : ι → BinaryAdelicGL) (hx : ∀ i ∈ S, x i ∈ Gl) :
    ∃ z : ℂ, ∀ v, (∑ i ∈ S, c i • compression σ (Kl ⊔ K') (x i)) v = z • v := by
  apply fixed_schur
  intro h
  apply Commute.sum_left
  intro i hi
  have hC := compression_local_commute (σ := σ) Kl K' Gl hKl hcomm decomp J hGlF cosets (x i) (hx i hi) h
  ext1 w
  have := congrArg (fun F : fixedVectors σ (Kl ⊔ K') →L[ℂ] fixedVectors σ (Kl ⊔ K') => F w) hC.eq
  change c i • compression σ (Kl ⊔ K') (x i) (compression σ (Kl ⊔ K') h w) =
    compression σ (Kl ⊔ K') h (c i • compression σ (Kl ⊔ K') (x i) w)
  rw [map_smul]
  exact congrArg (c i • ·) this

end TernaryPeriodPolynomials.RepresentationTheory
