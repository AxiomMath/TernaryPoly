module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Shapiro
public import TernaryPeriodPolynomials.GroupCohomology.Relative.ExtObstruction
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Shapiro.Bridge
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.Cohomology
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.RelativeVertexCohomology

@[expose] public section


/-!
# The exact segment for `Ext¹_{K†}(Q₀, E)`

The paper defines `Ext¹_H(V, M)` as the equivalence classes of extensions `0 → M → E → V → 0` of `H`-modules, and in the proof of
`prop:alternating-even` applies `Hom_{K†}(-, E)` to the exact sequence
`0 → Q₀ → ℚ[K†/H_BB] ⊕ ℚ[K†/H_BG] → ℚ[K†/H_L] ⊕ ℚ[K†/H_P] → 0`
and uses Shapiro's lemma to obtain the exact segment
`H¹(H_BB,E) ⊕ H¹(H_BG,E) → Ext¹_{K†}(Q₀,E) → H²(H_L,E) ⊕ H²(H_P,E)`.

Here `Ext` is Mathlib's `Ext` in the abelian category `Rep ℚ K` (the library's `K` is `K†` in the original coordinates); its degree-one elements are the classes of
extensions (every short exact sequence `0 → M → E → V → 0` defines its class `ShortExact.extClass ∈ Ext¹(V, M)`; the converse -- that every class is of this form and that the
class determines the extension up to equivalence -- is the Yoneda description, which Mathlib does not state and which is not used below).  We prove:

* `prodExtEquiv`: `Ext^n(A ⊕ B, E) ≃+ Ext^n(A, E) × Ext^n(B, E)`;
* `edgesExtEquiv`, `verticesExtEquiv`: the Shapiro identifications `Ext¹(ℚ[edges], E) ≃+ H¹(H_BB,E) × H¹(H_BG,E)` and `Ext²(ℚ[vertices], E) ≃+ H²(H_L,E) × H²(H_P,E)`
  (`RelativeShapiroBridge.cosetExtEquivGroupCohomology` and `edgesIso`, `verticesIso`);
* `segmentIn`, `segmentOut`: the two maps of the segment (restriction along `Q₀ ↪ ℚ[edges]`, and the connecting map composed with Shapiro);
* `ext_Q0_segment_exact`: **the segment is exact** at `Ext¹(Q₀, E)`;
* `ext_Q0_vanishing_of_segment`: the four stabilizer vanishings give `Ext¹(Q₀, E) = 0`, as a corollary of the segment (the earlier `ext_Q0_vanishing` is the same statement).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.ExtSegment

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open TernaryPoly TernaryPoly.RelativeExtObstructionSequences TernaryPoly.RelativeOrbitStabilizers
open TernaryPoly.RelativeShapiroModules TernaryPoly.RelativeShapiroBridge TernaryPoly.RelativeExtObstruction

/-- The inclusions and projections of a binary product of representations. -/
def prodInl (A B : Rep.{0} ℚ K) : A ⟶ productRep A B :=
  Rep.ofHom ⟨LinearMap.inl ℚ A B, fun _ => by ext x <;> simp [Representation.prod]⟩

def prodInr (A B : Rep.{0} ℚ K) : B ⟶ productRep A B :=
  Rep.ofHom ⟨LinearMap.inr ℚ A B, fun _ => by ext x <;> simp [Representation.prod]⟩

def prodFst (A B : Rep.{0} ℚ K) : productRep A B ⟶ A := Rep.ofHom ⟨LinearMap.fst ℚ A B, fun _ => rfl⟩

def prodSnd (A B : Rep.{0} ℚ K) : productRep A B ⟶ B := Rep.ofHom ⟨LinearMap.snd ℚ A B, fun _ => rfl⟩

theorem prod_total (A B : Rep.{0} ℚ K) :
    prodFst A B ≫ prodInl A B + prodSnd A B ≫ prodInr A B = 𝟙 (productRep A B) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  change (c.1, 0) + (0, c.2) = c
  simp

theorem prodInl_fst (A B : Rep.{0} ℚ K) : prodInl A B ≫ prodFst A B = 𝟙 A := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  rfl

theorem prodInr_snd (A B : Rep.{0} ℚ K) : prodInr A B ≫ prodSnd A B = 𝟙 B := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  rfl

theorem prodInl_snd (A B : Rep.{0} ℚ K) : prodInl A B ≫ prodSnd A B = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  rfl

theorem prodInr_fst (A B : Rep.{0} ℚ K) : prodInr A B ≫ prodFst A B = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  rfl

/-- **`Ext^n(A ⊕ B, E) ≃+ Ext^n(A, E) × Ext^n(B, E)`** for a binary product of representations. -/
def prodExtEquiv (A B E : Rep.{0} ℚ K) (n : ℕ) :
    Ext.{1} (productRep A B) E n ≃+ Ext.{1} A E n × Ext.{1} B E n where
  toFun x := ((Ext.mk₀ (prodInl A B)).comp x (zero_add n), (Ext.mk₀ (prodInr A B)).comp x (zero_add n))
  invFun p := (Ext.mk₀ (prodFst A B)).comp p.1 (zero_add n) + (Ext.mk₀ (prodSnd A B)).comp p.2 (zero_add n)
  left_inv x := by
    simp only [Ext.mk₀_comp_mk₀_assoc]
    rw [← Ext.add_comp, ← Ext.mk₀_add, prod_total, Ext.mk₀_id_comp]
  right_inv p := by
    simp only [Ext.comp_add, Ext.mk₀_comp_mk₀_assoc, prodInl_fst, prodInl_snd, prodInr_fst, prodInr_snd,
      Ext.mk₀_id_comp, Ext.mk₀_zero, Ext.zero_comp, add_zero, zero_add]
  map_add' x y := by
    simp only [Ext.comp_add, Prod.mk_add_mk]

/-- Shapiro for two cosets: `Ext^{n+1}(ℚ[K/H₁] ⊕ ℚ[K/H₂], E) ≃+ H^{n+1}(H₁,E) × H^{n+1}(H₂,E)`. -/
def coProdExtEquiv (H₁ H₂ : Subgroup K) (E : Rep.{0} ℚ K) (n : ℕ) :
    Ext.{1} (productRep (CosetRep H₁) (CosetRep H₂)) E (n + 1) ≃+
      groupCohomology (Rep.res H₁.subtype E) (n + 1) × groupCohomology (Rep.res H₂.subtype E) (n + 1) :=
  (prodExtEquiv (CosetRep H₁) (CosetRep H₂) E (n + 1)).trans
    ((cosetExtEquivGroupCohomology H₁ E n).prodCongr (cosetExtEquivGroupCohomology H₂ E n))

/-- **The edge term**: `Ext¹(ℚ[edges], E) ≃+ H¹(H_BB,E) × H¹(H_BG,E)`. -/
def edgesExtEquiv (E : Rep.{0} ℚ K) :
    Ext.{1} RelativeEdgesRep E 1 ≃+
      groupCohomology (Rep.res HBB.subtype E) 1 × groupCohomology (Rep.res HBG.subtype E) 1 :=
  (RelativeShapiroComparison.extCongrLeft edgesIso 1).trans (coProdExtEquiv HBB HBG E 0)

/-- **The vertex term**: `Ext²(ℚ[vertices], E) ≃+ H²(H_L,E) × H²(H_P,E)`. -/
def verticesExtEquiv (E : Rep.{0} ℚ K) :
    Ext.{1} RelativeVerticesRep E 2 ≃+
      groupCohomology (Rep.res HL.subtype E) 2 × groupCohomology (Rep.res HP.subtype E) 2 :=
  (RelativeShapiroComparison.extCongrLeft verticesIso 2).trans (coProdExtEquiv HL HP E 1)

/-- The first map of the segment: `H¹(H_BB,E) ⊕ H¹(H_BG,E) → Ext¹(ℚ[edges], E) → Ext¹_{K†}(Q₀, E)`. -/
def segmentIn (E : Rep.{0} ℚ K) :
    (groupCohomology (Rep.res HBB.subtype E) 1 × groupCohomology (Rep.res HBG.subtype E) 1) →+
      Ext.{1} QuotientCyclesRep E 1 :=
  ((Ext.mk₀ relativeCycleInclusion).precomp E (zero_add 1)).comp (edgesExtEquiv E).symm.toAddMonoidHom

/-- The second map of the segment: the connecting map of the vertex sequence followed by Shapiro,
`Ext¹_{K†}(Q₀, E) → Ext²(ℚ[vertices], E) ≃ H²(H_L,E) ⊕ H²(H_P,E)`. -/
def segmentOut (E : Rep.{0} ℚ K) :
    Ext.{1} QuotientCyclesRep E 1 →+
      (groupCohomology (Rep.res HL.subtype E) 2 × groupCohomology (Rep.res HP.subtype E) 2) :=
  (verticesExtEquiv E).toAddMonoidHom.comp (relativeSequence_shortExact.extClass.precomp E (rfl : 1 + 1 = 2))

theorem segmentIn_apply (E : Rep.{0} ℚ K) (y : groupCohomology (Rep.res HBB.subtype E) 1 ×
    groupCohomology (Rep.res HBG.subtype E) 1) :
    segmentIn E y = ((Ext.mk₀ relativeCycleInclusion).precomp E (zero_add 1)) ((edgesExtEquiv E).symm y) := rfl

theorem segmentOut_apply (E : Rep.{0} ℚ K) (x : Ext.{1} QuotientCyclesRep E 1) :
    segmentOut E x = verticesExtEquiv E ((relativeSequence_shortExact.extClass.precomp E (rfl : 1 + 1 = 2)) x) := rfl

/-- **The displayed segment is exact**:
`H¹(H_BB,E) ⊕ H¹(H_BG,E) → Ext¹_{K†}(Q₀,E) → H²(H_L,E) ⊕ H²(H_P,E)`. -/
theorem ext_Q0_segment_exact (E : Rep.{0} ℚ K) : Function.Exact (segmentIn E) (segmentOut E) := by
  have ex : Function.Exact ((Ext.mk₀ relativeCycleInclusion).precomp E (zero_add 1))
      (relativeSequence_shortExact.extClass.precomp E (rfl : 1 + 1 = 2)) := by
    have := Ext.contravariant_sequence_exact₁' relativeSequence_shortExact E 1 2 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact this
  intro x
  constructor
  · intro h
    have h0 : (relativeSequence_shortExact.extClass.precomp E (rfl : 1 + 1 = 2)) x = 0 :=
      (verticesExtEquiv E).injective ((segmentOut_apply E x).symm.trans (h.trans (map_zero (verticesExtEquiv E)).symm))
    obtain ⟨z, hz⟩ := (ex x).mp h0
    exact ⟨edgesExtEquiv E z, by rw [segmentIn_apply, AddEquiv.symm_apply_apply]; exact hz⟩
  · rintro ⟨y, rfl⟩
    have h1 := (ex (segmentIn E y)).mpr ⟨(edgesExtEquiv E).symm y, (segmentIn_apply E y).symm⟩
    exact (segmentOut_apply E (segmentIn E y)).trans ((congrArg (verticesExtEquiv E) h1).trans (map_zero _))

/-- **`Ext¹_{K†}(Q₀, E) = 0` from the segment**: the four stabilizer vanishings
`H¹(H_BB,E) = H¹(H_BG,E) = 0 = H²(H_L,E) = H²(H_P,E)` kill the middle term. -/
theorem ext_Q0_vanishing_of_segment (E : Rep.{0} ℚ K)
    (hBB : IsZero (groupCohomology (Rep.res HBB.subtype E) 1))
    (hBG : IsZero (groupCohomology (Rep.res HBG.subtype E) 1))
    (hL : IsZero (groupCohomology (Rep.res HL.subtype E) 2))
    (hP : IsZero (groupCohomology (Rep.res HP.subtype E) 2)) :
    Subsingleton (Ext.{1} QuotientCyclesRep E 1) := by
  have sBB := ModuleCat.isZero_iff_subsingleton.mp hBB
  have sBG := ModuleCat.isZero_iff_subsingleton.mp hBG
  have sL := ModuleCat.isZero_iff_subsingleton.mp hL
  have sP := ModuleCat.isZero_iff_subsingleton.mp hP
  have hz (x : Ext.{1} QuotientCyclesRep E 1) : x = 0 := by
    have h0 : segmentOut E x = 0 := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    obtain ⟨y, rfl⟩ := (ext_Q0_segment_exact E x).mp h0
    have hy : y = 0 := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    rw [hy, map_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- **`Ext¹_{K†}(Q₀, E) = 0` for `E = Sym^n((ℚ³)*)`, `n` even, from the exact segment and the four proved stabilizer vanishings.** -/
theorem ext_Q0_vanishing_via_segment (n : ℕ) (hn : Even n) :
    Subsingleton (Ext.{1} QuotientCyclesRep (RelativeExtObstruction.coefficientRep n) 1) :=
  ext_Q0_vanishing_of_segment _ (RelativeEdgeCohomology.hbb_H1_zero n hn)
    (RelativeEdgeCohomology.hbg_H1_zero n hn) (RelativeVertexCohomology.hl_H2_zero n)
    (RelativeVertexCohomology.hp_H2_zero n hn)

end TernaryPeriodPolynomials.Argument.Identities.ExtSegment
