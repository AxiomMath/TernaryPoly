module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyRank
public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Generation

@[expose] public section


/-!
# The action of `GL₂(ℤ)` on the dual Farey tree

Formalized by Claude Sonnet 5.5.

`GL₂(ℤ)` acts on the rational lines (`cuspMulAction`), on the Farey triangles `Tri` (`triMulAction`; `smul_frame`:
`g • frame h = frame (g h)`), and on the set `OTE` of oriented edges of the dual tree, i.e. ordered pairs of adjacent
triangles (`oteMulAction`), with the reversal involution `OTE.swap`.  All triangle and oriented-edge stabilizers are
finite (`tri_stabilizer_finite`, `ote_stabilizer_finite`: the stabilizer of the standard triangle consists of matrices
with entries in `{-1, 0, 1}`).  Every triangle is a translate of `triPlus` (`exists_smul_triPlus`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FareyTree

open TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.RankTwoVertexLinks
  TernaryPoly.RankTwoHeightLinks TernaryPoly.BinaryModularSymbol

/-- `GL₂(ℤ)` acts on the rational lines of the plane. -/
instance cuspMulAction : MulAction IntegralGL RationalLine2 where
  smul g L := lineAction (integral g) L
  one_smul L := by
    show lineAction (integral 1) L = L
    rw [map_one]; exact lineAction_one L
  mul_smul g h L := by
    show lineAction (integral (g * h)) L = lineAction (integral g) (lineAction (integral h) L)
    rw [map_mul]; exact lineAction_mul _ _ L

theorem cusp_smul_def (g : IntegralGL) (L : RationalLine2) : g • L = lineAction (integral g) L := rfl

theorem smul_augmentedLine (g h : IntegralGL) (i : Fin 3) :
    g • augmentedLine h i = augmentedLine (g * h) i := lineAction_augmentedLine g h i

theorem smul_frame (g h : IntegralGL) :
    (augmentedFrame h).image (g • ·) = augmentedFrame (g * h) := by
  unfold augmentedFrame
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact smul_augmentedLine g h i

/-- `GL₂(ℤ)` acts on the triangles of the Farey complex. -/
instance triMulAction : MulAction IntegralGL Tri where
  smul g t := ⟨t.1.image (g • ·), by
    obtain ⟨h, hh⟩ := t.2
    exact ⟨g * h, by rw [hh, smul_frame]⟩⟩
  one_smul t := by
    apply Subtype.ext
    show t.1.image ((1 : IntegralGL) • ·) = t.1
    simp
  mul_smul g h t := by
    apply Subtype.ext
    show t.1.image ((g * h) • ·) = (t.1.image (h • ·)).image (g • ·)
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact mul_smul g h x

theorem tri_smul_val (g : IntegralGL) (t : Tri) : (g • t).1 = t.1.image (g • ·) := rfl

theorem mem_tri_smul {g : IntegralGL} {t : Tri} {x : RationalLine2} :
    x ∈ (g • t).1 ↔ g⁻¹ • x ∈ t.1 := by
  rw [tri_smul_val, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g⁻¹ • x, h, by simp⟩

theorem smul_mem_tri_smul {g : IntegralGL} {t : Tri} {x : RationalLine2} (hx : x ∈ t.1) :
    g • x ∈ (g • t).1 := by
  rw [mem_tri_smul]; simpa using hx

theorem TAdj.smul {t t' : Tri} (h : TAdj t t') (g : IntegralGL) : TAdj (g • t) (g • t') := by
  obtain ⟨hne, x, y, hxy, hx, hy, hx', hy'⟩ := h
  refine ⟨fun e => hne (MulAction.injective g e), g • x, g • y, fun e => hxy (MulAction.injective g e),
    smul_mem_tri_smul hx, smul_mem_tri_smul hy, smul_mem_tri_smul hx', smul_mem_tri_smul hy'⟩

theorem exists_smul_triPlus (t : Tri) : ∃ g : IntegralGL, t = g • triPlus := by
  obtain ⟨h, hh⟩ := t.2
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : IntegralGL, triPlus.1 = augmentedFrame g₀ :=
    ⟨colGL e1 e2 e12_unimod, frame_plus isGen_cusp1 isGen_cusp2 e12_unimod⟩
  refine ⟨h * g₀⁻¹, ?_⟩
  apply Subtype.ext
  rw [hh, tri_smul_val, hg₀, smul_frame]
  simp

theorem cusp1_eq : cusp1 = augmentedLine 1 0 := by
  have h1 := col_isGen (1 : IntegralGL) 0
  have : (fun i => (1 : IntegralGL).val i 0) = e1 := by
    funext i; fin_cases i <;> simp [e1]
  rw [this] at h1
  exact (isGen_cusp1.line_eq_iff h1).mpr (Or.inl rfl)

theorem cusp2_eq : cusp2 = augmentedLine 1 1 := by
  have h1 := col_isGen (1 : IntegralGL) 1
  have : (fun i => (1 : IntegralGL).val i 1) = e2 := by
    funext i; fin_cases i <;> simp [e2]
  rw [this] at h1
  exact (isGen_cusp2.line_eq_iff h1).mpr (Or.inl rfl)

theorem smul_cusp1 (g : IntegralGL) : g • cusp1 = augmentedLine g 0 := by
  rw [cusp1_eq, smul_augmentedLine, mul_one]

theorem smul_cusp2 (g : IntegralGL) : g • cusp2 = augmentedLine g 1 := by
  rw [cusp2_eq, smul_augmentedLine, mul_one]

theorem gen_bound_triPlus {z : RationalLine2} (hz : z ∈ triPlus.1) {c : IntegralVector}
    (hc : IsGen z c) : |c 0| ≤ 1 ∧ |c 1| ≤ 1 := by
  simp only [triPlus, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · rcases isGen_cusp1.eq_or_neg hc with e | e <;> subst e <;> simp [e1]
  · rcases isGen_cusp2.eq_or_neg hc with e | e <;> subst e <;> simp [e2]
  · rcases (isGen_plusLine e12_unimod).eq_or_neg hc with e | e <;> subst e <;> simp [e1, e2]

theorem stabilizer_triPlus_finite : Finite (MulAction.stabilizer IntegralGL triPlus) := by
  have hbound : ∀ g ∈ MulAction.stabilizer IntegralGL triPlus, ∀ i j : Fin 2, |g.val i j| ≤ 1 := by
    intro g hg
    have hg' : g • triPlus = triPlus := hg
    have h0 : g • cusp1 ∈ triPlus.1 := by
      rw [← hg']; exact smul_mem_tri_smul (by simp [triPlus])
    have h1 : g • cusp2 ∈ triPlus.1 := by
      rw [← hg']; exact smul_mem_tri_smul (by simp [triPlus])
    rw [← hg'] at h0 h1
    have h0' := h0
    have h1' := h1
    rw [hg'] at h0' h1'
    have c0 := gen_bound_triPlus h0' (by rw [smul_cusp1]; exact col_isGen g 0)
    have c1 := gen_bound_triPlus h1' (by rw [smul_cusp2]; exact col_isGen g 1)
    intro i j
    fin_cases i <;> fin_cases j
    · exact c0.1
    · exact c1.1
    · exact c0.2
    · exact c1.2
  have hfin : Set.Finite (Set.pi Set.univ (fun _ : Fin 2 =>
      Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-1 : ℤ) 1))) :=
    Set.Finite.pi (fun _ => Set.Finite.pi (fun _ => Set.finite_Icc _ _))
  have hinj : Function.Injective (fun g : IntegralGL => (fun i j => g.val i j : Fin 2 → Fin 2 → ℤ)) := by
    intro g h e
    apply Units.ext
    ext i j
    exact congrFun (congrFun e i) j
  have := hfin.preimage (hinj.injOn)
  refine (this.subset ?_).to_subtype
  intro g hg
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  intro i j
  exact abs_le.mp (hbound g hg i j)

theorem tri_stabilizer_finite (t : Tri) : Finite (MulAction.stabilizer IntegralGL t) := by
  obtain ⟨g, rfl⟩ := exists_smul_triPlus t
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have := stabilizer_triPlus_finite
  exact Finite.of_equiv _ (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv

/-- Oriented edges of the dual Farey tree: ordered pairs of adjacent triangles. -/
def OTE : Type := {p : Tri × Tri // TAdj p.1 p.2}

instance oteMulAction : MulAction IntegralGL OTE where
  smul g p := ⟨(g • p.1.1, g • p.1.2), p.2.smul g⟩
  one_smul _ := Subtype.ext (Prod.ext (one_smul _ _) (one_smul _ _))
  mul_smul g h _ := Subtype.ext (Prod.ext (mul_smul g h _) (mul_smul g h _))

theorem ote_smul_val (g : IntegralGL) (p : OTE) : (g • p).1 = (g • p.1.1, g • p.1.2) := rfl

/-- Reversal of an oriented edge. -/
def OTE.swap (p : OTE) : OTE := ⟨(p.1.2, p.1.1), p.2.symm⟩

@[simp] theorem OTE.swap_swap (p : OTE) : p.swap.swap = p := rfl

theorem OTE.swap_smul (g : IntegralGL) (p : OTE) : (g • p).swap = g • p.swap := rfl

theorem OTE.swap_ne (p : OTE) : p.swap ≠ p := by
  intro e
  have := congrArg (fun q : OTE => q.1.1) e
  exact p.2.1 this.symm

theorem ote_stabilizer_finite (p : OTE) : Finite (MulAction.stabilizer IntegralGL p) := by
  have := tri_stabilizer_finite p.1.1
  refine Finite.of_injective (fun g : MulAction.stabilizer IntegralGL p =>
    (⟨g.1, ?_⟩ : MulAction.stabilizer IntegralGL p.1.1)) ?_
  · have : g.1 • p = p := g.2
    have := congrArg (fun q : OTE => q.1.1) this
    exact this
  · intro g h e
    have := Subtype.ext_iff.mp e
    exact Subtype.ext this

end TernaryPeriodPolynomials.Argument.FareyTree
