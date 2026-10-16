module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Thom

@[expose] public section


/-!
# The relative homology of a slab in a box has rank at most one

For the box `{‖u‖ < ε, ‖t‖ < R} ⊆ ℝ³ × ℝ²` (a homeomorphic copy `X`) and the closed slab
`W = {‖t‖ ≤ δ}` with `0 < δ < R`, the relative homology `H₂(X, X ∖ W; ℚ)` has dimension at most one
(`box_rank_one`): two rational 2-chains whose boundaries lie over `X ∖ W` are proportional modulo
chains over `X ∖ W` and boundaries as soon as one of them is not trivial.

The proof contracts `X`, so that the relative class of a 2-chain is determined by the class of its
boundary in `H₁(X ∖ W; ℚ)`, and uses that `X ∖ W` is homotopy equivalent to the punctured plane
(explicit straight-line homotopies), so `H₁(X ∖ W; ℚ) ≅ ℚ`.  The linear algebra is isolated in
`rank_one_of_functional`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory CategoryTheory.Limits HomologicalComplex SphereOddDegree
  SphereOddDegree.AffineBarycentricSubdivision TernaryPoly
  TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalRelativeSingular
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSphere

/-- Two-dimensional Euclidean space. -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- The model box `{‖u‖ < ε, ‖t‖ < R}` in `ℝ³ × ℝ²`. -/
def boxSet (ε R : ℝ) : Set (R3 × R2) := {p | ‖p.1‖ < ε ∧ ‖p.2‖ < R}

/-- Radial interpolation coefficient. -/
def boxLam (c s : ℝ) (t : R2) : ℝ := s + (1 - s) * (c / ‖t‖)

theorem boxLam_pos {c s : ℝ} {t : R2} (hc : 0 < c) (ht : 0 < ‖t‖) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < boxLam c s t := by
  unfold boxLam
  have : 0 < c / ‖t‖ := div_pos hc ht
  rcases eq_or_lt_of_le hs0 with h | h
  · subst h; simpa using this
  · have : 0 ≤ (1 - s) * (c / ‖t‖) := mul_nonneg (by linarith) (by positivity)
    linarith

theorem boxLam_norm_smul {c s : ℝ} {t : R2} (hc : 0 < c) (ht : 0 < ‖t‖) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖boxLam c s t • t‖ = s * ‖t‖ + (1 - s) * c := by
  rw [norm_smul, Real.norm_of_nonneg (boxLam_pos hc ht hs0 hs1).le]
  unfold boxLam
  field_simp

theorem boxLam_bounds {ε R δ c s : ℝ} {u : R3} {t : R2} (hc1 : δ < c) (hc2 : c < R) (hδ : 0 < δ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hu : ‖u‖ < ε) (ht1 : δ < ‖t‖) (ht2 : ‖t‖ < R) :
    ‖s • u‖ < ε ∧ ‖boxLam c s t • t‖ < R ∧ δ < ‖boxLam c s t • t‖ := by
  have hc : 0 < c := hδ.trans hc1
  have ht : 0 < ‖t‖ := hδ.trans ht1
  rw [boxLam_norm_smul hc ht hs0 hs1, norm_smul, Real.norm_of_nonneg hs0]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [norm_nonneg u]
  · set m := min (R - ‖t‖) (R - c) with hm
    have hm0 : 0 < m := lt_min (by linarith) (by linarith)
    have h1 : m ≤ R - ‖t‖ := min_le_left _ _
    have h2 : m ≤ R - c := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0, mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hs1)]
  · set m := min (‖t‖ - δ) (c - δ) with hm
    have hm0 : 0 < m := lt_min (by linarith) (by linarith)
    have h1 : m ≤ ‖t‖ - δ := min_le_left _ _
    have h2 : m ≤ c - δ := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0, mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hs1)]

theorem boxLam_continuous {c : ℝ} {Y : Type} [TopologicalSpace Y] {s : Y → ℝ} {t : Y → R2}
    (hs : Continuous s) (ht : Continuous t) (hne : ∀ y, ‖t y‖ ≠ 0) :
    Continuous (fun y => boxLam c (s y) (t y)) := by
  unfold boxLam
  exact hs.add ((continuous_const.sub hs).mul (continuous_const.div ht.norm hne))


section Annulus

variable {ε R δ : ℝ} {X : TopCat.{0}} (e : X ≃ₜ boxSet ε R)

/-- The part of `X` over the annulus `δ < ‖t‖`. -/
def boxAnnSet (δ : ℝ) : Set X := {x | δ < ‖((e x : boxSet ε R) : R3 × R2).2‖}

/-- The `t`-coordinate. -/
def boxTOf (x : X) : R2 := ((e x : boxSet ε R) : R3 × R2).2

/-- The `u`-coordinate. -/
def boxUOf (x : X) : R3 := ((e x : boxSet ε R) : R3 × R2).1

theorem boxTOf_cont : Continuous (boxTOf e) :=
  continuous_snd.comp (continuous_subtype_val.comp e.continuous)

theorem boxUOf_cont : Continuous (boxUOf e) :=
  continuous_fst.comp (continuous_subtype_val.comp e.continuous)

theorem boxUOf_lt (x : X) : ‖boxUOf e x‖ < ε := (e x).2.1

theorem boxTOf_lt (x : X) : ‖boxTOf e x‖ < R := (e x).2.2

/-- The radius of the model circle. -/
def boxRadius (δ R : ℝ) : ℝ := (δ + R) / 2

theorem boxRadius_lt (hδR : δ < R) : δ < boxRadius δ R ∧ boxRadius δ R < R := by
  unfold boxRadius; constructor <;> linarith

/-- The point `(s u, λ(s,t) t)` of the box. -/
def boxPt (hδ : 0 < δ) (hδR : δ < R) (s : unitInterval) (x : boxAnnSet e δ) : boxSet ε R :=
  ⟨(((s : ℝ) • boxUOf e x.1), boxLam (boxRadius δ R) s (boxTOf e x.1) • boxTOf e x.1), by
    have hb := boxLam_bounds (c := boxRadius δ R) (boxRadius_lt hδR).1 (boxRadius_lt hδR).2 hδ s.2.1 s.2.2
      (boxUOf_lt e x.1) x.2 (boxTOf_lt e x.1)
    exact ⟨hb.1, hb.2.1⟩⟩


theorem boxPt_gt (hδ : 0 < δ) (hδR : δ < R) (s : unitInterval) (x : boxAnnSet e δ) :
    δ < ‖(boxPt e hδ hδR s x : R3 × R2).2‖ :=
  (boxLam_bounds (c := boxRadius δ R) (boxRadius_lt hδR).1 (boxRadius_lt hδR).2 hδ s.2.1 s.2.2
      (boxUOf_lt e x.1) x.2 (boxTOf_lt e x.1)).2.2

theorem boxTOf_ne (hδ : 0 < δ) (x : boxAnnSet e δ) : ‖boxTOf e x.1‖ ≠ 0 :=
  (hδ.trans x.2).ne'

theorem boxPt_cont (hδ : 0 < δ) (hδR : δ < R) :
    Continuous (fun p : unitInterval × boxAnnSet e δ => boxPt e hδ hδR p.1 p.2) := by
  refine Continuous.subtype_mk ?_ _
  have ht : Continuous (fun p : unitInterval × boxAnnSet e δ => boxTOf e p.2.1) :=
    (boxTOf_cont e).comp (continuous_subtype_val.comp continuous_snd)
  have hs : Continuous (fun p : unitInterval × boxAnnSet e δ => ((p.1 : unitInterval) : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  refine Continuous.prodMk (hs.smul ((boxUOf_cont e).comp (continuous_subtype_val.comp
    continuous_snd))) ((boxLam_continuous hs ht (fun p => boxTOf_ne e hδ p.2)).smul ht)

theorem boxRetr_mem (hδ : 0 < δ) (hδR : δ < R) (p : unitInterval × boxAnnSet e δ) :
    e.symm (boxPt e hδ hδR p.1 p.2) ∈ boxAnnSet e δ := by
  show δ < ‖boxTOf e (e.symm (boxPt e hδ hδR p.1 p.2))‖
  simp only [boxTOf, Homeomorph.apply_symm_apply]
  exact boxPt_gt e hδ hδR p.1 p.2

/-- The straight-line deformation of the annulus onto the circle `‖t‖ = boxRadius`. -/
def boxRetr (hδ : 0 < δ) (hδR : δ < R) : C(unitInterval × boxAnnSet e δ, boxAnnSet e δ) :=
  ⟨fun p => ⟨e.symm (boxPt e hδ hδR p.1 p.2), boxRetr_mem e hδ hδR p⟩,
    Continuous.subtype_mk (e.symm.continuous.comp (boxPt_cont e hδ hδR)) _⟩


theorem boxTOf_mem_punct (hδ : 0 < δ) (x : boxAnnSet e δ) : boxTOf e x.1 ∈ ({0}ᶜ : Set R2) := by
  intro h
  exact boxTOf_ne e hδ x (by rw [Set.mem_singleton_iff.mp h, norm_zero])

/-- The projection of the annulus part of the box to the punctured plane. -/
def boxAnnToPunct (hδ : 0 < δ) : C(boxAnnSet e δ, Punctured 2) :=
  ⟨fun x => ⟨boxTOf e x.1, boxTOf_mem_punct e hδ x⟩,
    Continuous.subtype_mk ((boxTOf_cont e).comp continuous_subtype_val) _⟩

theorem boxPunct_norm_pos (t : Punctured 2) : 0 < ‖t.1‖ :=
  norm_pos_iff.2 (fun h => t.2 (Set.mem_singleton_iff.2 h))

/-- The point of the box over `t` on the model circle. -/
def boxCPt (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R) (t : Punctured 2) : boxSet ε R :=
  ⟨(0, boxLam (boxRadius δ R) 0 t.1 • t.1), by
    refine ⟨by simpa using hε, ?_⟩
    rw [boxLam_norm_smul (hδ.trans (boxRadius_lt hδR).1) (boxPunct_norm_pos t) le_rfl zero_le_one]
    have := (boxRadius_lt hδR).2
    linarith⟩

theorem boxCPt_mem (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R) (t : Punctured 2) :
    e.symm (boxCPt hε hδ hδR t) ∈ boxAnnSet e δ := by
  show δ < ‖boxTOf e (e.symm (boxCPt hε hδ hδR t))‖
  simp only [boxTOf, Homeomorph.apply_symm_apply, boxCPt]
  rw [boxLam_norm_smul (hδ.trans (boxRadius_lt hδR).1) (boxPunct_norm_pos t) le_rfl zero_le_one]
  have := (boxRadius_lt hδR).1
  linarith


theorem boxCPt_cont (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R) :
    Continuous (fun t : Punctured 2 => boxCPt (ε := ε) hε hδ hδR t) := by
  refine Continuous.subtype_mk ?_ _
  have ht : Continuous (fun t : Punctured 2 => t.1) := continuous_subtype_val
  refine Continuous.prodMk continuous_const
    ((boxLam_continuous continuous_const ht (fun t => (boxPunct_norm_pos t).ne')).smul ht)

/-- The inclusion of the model circle into the annulus part. -/
def boxPunctToAnn (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R) : C(Punctured 2, boxAnnSet e δ) :=
  ⟨fun t => ⟨e.symm (boxCPt hε hδ hδR t), boxCPt_mem e hε hδ hδR t⟩,
    Continuous.subtype_mk (e.symm.continuous.comp (boxCPt_cont hε hδ hδR)) _⟩

/-- The annulus part of the box is homotopy equivalent to the punctured plane. -/
def boxAnnHomotopyEquiv (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R) :
    ContinuousMap.HomotopyEquiv (boxAnnSet e δ) (Punctured 2) where
  toFun := boxAnnToPunct e hδ
  invFun := boxPunctToAnn e hε hδ hδR
  left_inv := ⟨{
    toFun := boxRetr e hδ hδR
    map_zero_left := by
      intro x
      apply Subtype.ext
      show e.symm (boxPt e hδ hδR 0 x) = e.symm (boxCPt hε hδ hδR ⟨boxTOf e x.1, boxTOf_mem_punct e hδ x⟩)
      congr 1
      apply Subtype.ext
      simp [boxPt, boxCPt, boxTOf, boxLam]
    map_one_left := by
      intro x
      apply Subtype.ext
      show e.symm (boxPt e hδ hδR 1 x) = x.1
      rw [Homeomorph.symm_apply_eq]
      apply Subtype.ext
      simp [boxPt, boxTOf, boxUOf, boxLam] }⟩
  right_inv := ⟨{
    toFun := fun p => ⟨boxLam (boxRadius δ R) p.1 p.2.1 • p.2.1, by
      intro h
      have := boxLam_pos (hδ.trans (boxRadius_lt hδR).1) (boxPunct_norm_pos p.2) p.1.2.1 p.1.2.2
      have h0 : ‖boxLam (boxRadius δ R) p.1 p.2.1 • p.2.1‖ = 0 := by
        rw [Set.mem_singleton_iff.mp h, norm_zero]
      rw [norm_smul, Real.norm_of_nonneg this.le] at h0
      exact (mul_pos this (boxPunct_norm_pos p.2)).ne' h0⟩
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      have ht : Continuous (fun p : unitInterval × Punctured 2 => p.2.1) :=
        continuous_subtype_val.comp continuous_snd
      have hs : Continuous (fun p : unitInterval × Punctured 2 => ((p.1 : unitInterval) : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      exact (boxLam_continuous hs ht (fun p => (boxPunct_norm_pos p.2).ne')).smul ht
    map_zero_left := by
      intro t
      apply Subtype.ext
      simp [boxTOf, boxAnnToPunct, boxPunctToAnn, boxCPt]
    map_one_left := by
      intro t
      apply Subtype.ext
      simp [boxLam] }⟩

end Annulus


theorem boxExists_lam_sc (S : ShortComplex (ModuleCat.{0} ℚ)) (Ψ : S.homology ≅ ModuleCat.of ℚ ℚ) :
    ∃ lam : LinearMap.ker S.g.hom →ₗ[ℚ] ℚ,
      ∀ c, lam c = 0 → ∃ b, S.f.hom b = c.1 := by
  let Ψ' : S.moduleCatLeftHomologyData.H ≅ ModuleCat.of ℚ ℚ := S.moduleCatHomologyIso.symm ≪≫ Ψ
  refine ⟨Ψ'.hom.hom ∘ₗ (LinearMap.range S.moduleCatToCycles).mkQ, ?_⟩
  intro c hc
  have h1 : (LinearMap.range S.moduleCatToCycles).mkQ c = 0 := by
    have : Function.Injective Ψ'.hom.hom :=
      (ModuleCat.mono_iff_injective Ψ'.hom).1 inferInstance
    exact this (hc.trans (map_zero Ψ'.hom.hom).symm)
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨b, hb⟩ := h1
  exact ⟨b, congrArg Subtype.val hb⟩

theorem boxExists_lam (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (Φ : K.homology 1 ≅ ModuleCat.of ℚ ℚ) :
    ∃ lam : LinearMap.ker (K.d 1 0).hom →ₗ[ℚ] ℚ,
      ∀ c, lam c = 0 → ∃ b, (K.d 2 1).hom b = c.1 :=
  boxExists_lam_sc (K.sc' 2 1 0) ((K.homologyIsoSc' 2 1 0 (by simp) (by simp)).symm ≪≫ Φ)


theorem rank_one_of_functional
    {V₃ V₂ V₁ V₀ A₂ A₁ A₀ : Type} [AddCommGroup V₃] [Module ℚ V₃] [AddCommGroup V₂] [Module ℚ V₂]
    [AddCommGroup V₁] [Module ℚ V₁] [AddCommGroup V₀] [Module ℚ V₀]
    [AddCommGroup A₂] [Module ℚ A₂] [AddCommGroup A₁] [Module ℚ A₁] [AddCommGroup A₀] [Module ℚ A₀]
    (d₃ : V₃ →ₗ[ℚ] V₂) (d₂ : V₂ →ₗ[ℚ] V₁) (d₁ : V₁ →ₗ[ℚ] V₀)
    (e₂ : A₂ →ₗ[ℚ] V₂) (e₁ : A₁ →ₗ[ℚ] V₁) (e₀ : A₀ →ₗ[ℚ] V₀)
    (δ₂ : A₂ →ₗ[ℚ] A₁) (δ₁ : A₁ →ₗ[ℚ] A₀)
    (he₁ : Function.Injective e₁) (he₀ : Function.Injective e₀)
    (c₂ : ∀ x, d₂ (e₂ x) = e₁ (δ₂ x)) (c₁ : ∀ x, d₁ (e₁ x) = e₀ (δ₁ x))
    (hd₁₂ : ∀ x, d₁ (d₂ x) = 0)
    (hacyc : ∀ x, d₂ x = 0 → x ∈ LinearMap.range d₃)
    (lam : LinearMap.ker δ₁ →ₗ[ℚ] ℚ)
    (hlam : ∀ c : LinearMap.ker δ₁, lam c = 0 → ∃ b, δ₂ b = c.1)
    (a z : V₂) (ha : d₂ a ∈ LinearMap.range e₁) (hz : d₂ z ∈ LinearMap.range e₁)
    (haB : a ∉ LinearMap.range e₂ ⊔ LinearMap.range d₃) :
    ∃ q : ℚ, z - q • a ∈ LinearMap.range e₂ ⊔ LinearMap.range d₃ := by
  classical
  let Zr : Submodule ℚ V₂ := Submodule.comap d₂ (LinearMap.range e₁)
  have hc : ∀ w : Zr, ∃ c : LinearMap.ker δ₁, e₁ c.1 = d₂ w.1 := by
    intro w
    obtain ⟨c, hc⟩ := w.2
    refine ⟨⟨c, ?_⟩, hc⟩
    apply he₀
    rw [← c₁, hc, hd₁₂, map_zero]
  let ch : Zr → LinearMap.ker δ₁ := fun w => (hc w).choose
  have hch : ∀ w : Zr, e₁ (ch w).1 = d₂ w.1 := fun w => (hc w).choose_spec
  let Λ : Zr →ₗ[ℚ] ℚ :=
    { toFun := fun w => lam (ch w)
      map_add' := by
        intro w w'
        have : ch (w + w') = ch w + ch w' := by
          apply Subtype.ext
          apply he₁
          simp only [Submodule.coe_add, map_add, hch]
        rw [this, map_add]
      map_smul' := by
        intro r w
        have : ch (r • w) = r • ch w := by
          apply Subtype.ext
          apply he₁
          simp only [hch, Submodule.coe_smul, map_smul]
        rw [this, map_smul]; rfl }
  have key : ∀ w : Zr, Λ w = 0 → w.1 ∈ LinearMap.range e₂ ⊔ LinearMap.range d₃ := by
    intro w hw
    obtain ⟨b, hb⟩ := hlam (ch w) hw
    have h1 : d₂ (w.1 - e₂ b) = 0 := by
      rw [map_sub, c₂, hb, hch, sub_self]
    obtain ⟨y, hy⟩ := hacyc _ h1
    have : w.1 = e₂ b + d₃ y := by
      rw [hy]; abel
    rw [this]
    exact Submodule.add_mem_sup ⟨b, rfl⟩ ⟨y, rfl⟩
  let wa : Zr := ⟨a, ha⟩
  let wz : Zr := ⟨z, hz⟩
  have hΛa : Λ wa ≠ 0 := fun h => haB (key wa h)
  refine ⟨Λ wz / Λ wa, key (wz - (Λ wz / Λ wa) • wa) ?_⟩
  rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hΛa, sub_self]


section Box

theorem boxSet_convex (ε R : ℝ) : Convex ℝ (boxSet ε R) := by
  have : boxSet ε R = Metric.ball (0 : R3) ε ×ˢ Metric.ball (0 : R2) R := by
    ext p; simp [boxSet]
  rw [this]
  exact (convex_ball _ _).prod (convex_ball _ _)

theorem boxSet_contractible {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (X : TopCat.{0})
    (e : X ≃ₜ boxSet ε R) : ContractibleSpace X := by
  have : ContinuousSMul ℝ (R3 × R2) := Prod.continuousSMul
  have : ContractibleSpace (boxSet ε R) :=
    (boxSet_convex ε R).contractibleSpace ⟨(0, 0), by simp [boxSet, hε, hR]⟩
  exact e.contractibleSpace

theorem boxChains_acyclic_two (Y : Type) [TopologicalSpace Y] [ContractibleSpace Y]
    (x : (chains Y).X 2) (h : ((chains Y).d 2 1).hom x = 0) :
    x ∈ LinearMap.range ((chains Y).d 3 2).hom := by
  have hex := (exactAt_iff' (chains Y) 3 2 1 (by simp) (by simp)).1
    (chains_exactAt (X := Y) 2 (by norm_num))
  exact (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 hex (show x ∈ LinearMap.ker ((chains Y).d 2 1).hom from h)

/-- The homology of the annulus part of the box in degree one is `ℚ`. -/
def boxAnnHomologyIso {ε R δ : ℝ} {X : TopCat.{0}} (e : X ≃ₜ boxSet ε R)
    (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R) :
    (chains ↥(boxAnnSet e δ)).homology 1 ≅ ModuleCat.of ℚ ℚ :=
  (chainHomotopyEquiv (boxAnnHomotopyEquiv e hε hδ hδR)).toHomologyIso 1 ≪≫
    puncturedHomologyIso 1 1 ≪≫ topHomologyIso 1 (by omega)

theorem boxSubChain_eq_range {X : TopCat.{0}} (S : Set X) (n : ℕ) :
    subChainSubmodule ℚ X S n = LinearMap.range (singularChainMap ℚ (sInclusion S) n).hom := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (subChainCorestrict_bijective (R := ℚ) S n).2 ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, rfl⟩
    exact singularChainMap_sInclusion_mem S n x

theorem box_rank_one (ε R δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R)
    (X : TopCat.{0}) (e : X ≃ₜ boxSet ε R)
    (Wset : Set X) (hW : Wset = {x | ‖((e x : R3 × R2)).2‖ ≤ δ})
    (a z : singularChainGroup ℚ X 2)
    (ha : (singularBoundary ℚ X 1).hom a ∈ subChainSubmodule ℚ X Wsetᶜ 1)
    (hz : (singularBoundary ℚ X 1).hom z ∈ subChainSubmodule ℚ X Wsetᶜ 1)
    (haB : a ∉ subChainSubmodule ℚ X Wsetᶜ 2 ⊔ LinearMap.range (singularBoundary ℚ X 2).hom) :
    ∃ q : ℚ, z - q • a ∈ subChainSubmodule ℚ X Wsetᶜ 2 ⊔
      LinearMap.range (singularBoundary ℚ X 2).hom := by
  have hA : Wsetᶜ = boxAnnSet e δ := by
    subst hW; ext x; simp [boxAnnSet]
  rw [hA] at ha hz haB ⊢
  have : ContractibleSpace X := boxSet_contractible hε (hδ.trans hδR) X e
  obtain ⟨lam, hlam⟩ := boxExists_lam (chains ↥(boxAnnSet e δ)) (boxAnnHomologyIso e hε hδ hδR)
  have hinj : ∀ n, Function.Injective (singularChainMap ℚ (sInclusion (boxAnnSet e δ)) n).hom :=
    fun n => singularChainMap_injective_of_pushSimplex_injective _ n
      (pushSimplex_sInclusion_injective _ n)
  rw [boxSubChain_eq_range] at ha hz haB ⊢
  exact rank_one_of_functional (singularBoundary ℚ X 2).hom (singularBoundary ℚ X 1).hom
    (singularBoundary ℚ X 0).hom
    (singularChainMap ℚ (sInclusion (boxAnnSet e δ)) 2).hom
    (singularChainMap ℚ (sInclusion (boxAnnSet e δ)) 1).hom
    (singularChainMap ℚ (sInclusion (boxAnnSet e δ)) 0).hom
    (singularBoundary ℚ (TopCat.of ↥(boxAnnSet e δ)) 1).hom
    (singularBoundary ℚ (TopCat.of ↥(boxAnnSet e δ)) 0).hom
    (hinj 1) (hinj 0)
    (fun x => singularChainMap_boundary_apply ℚ _ 1 x)
    (fun x => singularChainMap_boundary_apply ℚ _ 0 x)
    (fun x => by
      rw [← ModuleCat.comp_apply]
      have := (chains X).d_comp_d 2 1 0
      exact congrArg (fun m => m.hom x) this)
    (fun x hx => boxChains_acyclic_two X x hx)
    lam hlam a z ha hz haB

end Box

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
