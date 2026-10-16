module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.ConeRecursion

@[expose] public section


/-!
# The cellular chain map of the well-rounded retract into singular chains of the bordification

For the library's `Γ(3)`-complex of the well-rounded retract (`FreeResolution.wellRounded`: cells
`Cell`, boundary `δC` with label signs `insSign`, augmentation `εC`) we build, by the cone recursion of
`ConeRecursion` (`φ_{n+1}(C) = b(C) * Σ_D inc(C,D) φ_n(D)`, `φ_0(v) = ε(v) [b(v)]`, base point `b(C)` = the
average of the Gram matrices of the vertices whose minimal lines contain `C`), a chain `cellAt n C` of
`underlyingChains (TopCat.of Glued)` (`cellSing C = cellAt C.grade C`) with:

* `cellAt_zero`: `cellAt 0 v = ε(v) • (point at ν(Gram v))` (the signed vertex of the retract);
* `d_cellAt`, `d_cellAt_nbrs`: for `C.grade = n + 1`, `d (cellAt (n+1) C) = Σ_w insSign C w • cellAt n (C ∪ {w})`
  (the library's boundary with its label signs; the `ℂ`-form of the coefficients is `castC_incQ`);
* `cellAt_support`: every affine simplex of the formal chain `coneData.phi n C` has its vertices in `reach C`,
  the convex hull of the Gram matrices of the vertices of `C`, and `cellAt n C` is the image of it under the
  realization `Q ↦ [Q⁻¹]`.  `reach_well_rounded` says that every point of `reach C` lies in the well-rounded
  retract in the strong sense: it is positive definite, takes the value `≥ 1` on every nonzero integer vector
  (`reach_ge_one`), takes the value exactly `1` on every minimal line of the cell (`reach_eq_one`: by
  linearity from the vertex Gram matrices, whose minimal sets contain the cell), and the lines of the cell
  span.  (`reach_ge_one` alone would only show that the cell lies in the Ryshkov polyhedron.)
* `cellAt_smul`: `cellAt n (γ • C) = ρ(levelLift γ) (cellAt n C)` for `γ ∈ Γ(3)`, where `ρ` is the standard
  action of `IntegralGL3` on the singular chains of `Glued`; `cellAt_smul_six` is the form for
  `Γ(6) = principalSix` (the library) through `levelOfSix`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

open Finsupp GeneralEisenstein TernaryPoly TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing

/-- Rational chains as complex chains. -/
def castC (α : Type) : (α →₀ ℚ) →ₗ[ℚ] (α →₀ ℂ) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap ℚ ℂ)

theorem castC_single {α : Type} (a : α) (q : ℚ) : castC α (single a q) = single a (q : ℂ) := by
  simp [castC]

theorem castC_injective (α : Type) : Function.Injective (castC α) := by
  intro z z' h
  ext a
  have := congrArg (fun w => w a) h
  simpa [castC] using this

theorem castC_apply {α : Type} (z : α →₀ ℚ) (a : α) : castC α z a = (z a : ℂ) := by
  simp [castC]

/-- The integer sign of inserting a line into a set of lines. -/
def insSignQ (T : Finset Line) (w : Line) : ℚ :=
  (-1) ^ ((T.image Line.label).filter (· < w.label)).card

theorem insSign_eq (T : Finset Line) (w : Line) : insSign T w = (insSignQ T w : ℂ) := by
  simp [insSign, insSignQ]

/-- The rational form of the coboundary of a set of lines. -/
def coboundaryOfQ (T : Finset Line) : Finset Line →₀ ℚ :=
  ∑ w ∈ nbrs T, insSignQ T w • single (insert w T) (1 : ℚ)

theorem coboundaryOf_eq (T : Finset Line) :
    coboundaryOf T = castC (Finset Line) (coboundaryOfQ T) := by
  rw [coboundaryOf, coboundaryOfQ, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, castC_single, insSign_eq]
  simp [Finsupp.smul_single]

/-- The rational boundary of a cell. -/
def incQ (C : Cell) : Cell →₀ ℚ :=
  Finsupp.comapDomain Cell.val (coboundaryOfQ C.val) Cell.val_injective.injOn

theorem incQ_apply (C D : Cell) : incQ C D = coboundaryOfQ C.val D.val := rfl

theorem castC_incQ (C : Cell) : castC Cell (incQ C) = δC (single C 1) := by
  ext D
  rw [castC_apply, incQ_apply]
  have h : δC (single C 1) D = coboundaryOf C.val D.val := by
    change ofF (δF (toF (single C 1))) D = _
    rw [toF_single, δF_single, ofF_apply]
  rw [h, coboundaryOf_eq, castC_apply]

/-- The rational boundary operator. -/
def LQ : (Cell →₀ ℚ) →ₗ[ℚ] (Cell →₀ ℚ) := linearCombination ℚ incQ

theorem castC_LQ (z : Cell →₀ ℚ) : castC Cell (LQ z) = δC (castC Cell z) := by
  have h : castC Cell ∘ₗ LQ = (δC.restrictScalars ℚ) ∘ₗ castC Cell := by
    apply Finsupp.lhom_ext
    intro C a
    simp only [LinearMap.comp_apply, LQ, linearCombination_single, map_smul, castC_incQ,
      castC_single, LinearMap.coe_restrictScalars]
    have e : (single C (a : ℂ) : Cell →₀ ℂ) = (a : ℂ) • single C 1 := by simp
    rw [e, map_smul]
    ext D
    simp [Finsupp.smul_apply, Rat.smul_def]
  exact LinearMap.congr_fun h z

theorem LQ_LQ : LQ ∘ₗ LQ = 0 := by
  apply LinearMap.ext
  intro z
  apply castC_injective Cell
  rw [LinearMap.comp_apply, castC_LQ, castC_LQ, LinearMap.zero_apply, map_zero]
  exact LinearMap.congr_fun δC_δC (castC Cell z)

/-- The rational form of `iota`. -/
def iotaQ (x : ZMod 3) : ℚ := if x = 1 then 1 else if x = -1 then -1 else 0

theorem iota_eq (x : ZMod 3) : iota x = (iotaQ x : ℂ) := by
  unfold iota iotaQ
  split_ifs <;> simp

/-- The rational augmentation of a cell. -/
def epsQ (C : Cell) : ℚ := if C.val.card = 6 then iotaQ (epsMod C.val) else 0

theorem epsF_eq (C : Cell) : epsF C.val = (epsQ C : ℂ) := by
  unfold epsF epsQ
  split_ifs
  · exact iota_eq _
  · simp

/-- The rational augmentation on chains. -/
def EQ : (Cell →₀ ℚ) →ₗ[ℚ] ℚ := linearCombination ℚ epsQ

theorem εC_castC (z : Cell →₀ ℚ) : εC (castC Cell z) = (EQ z : ℂ) := by
  have h : ((εC.restrictScalars ℚ) ∘ₗ castC Cell) = (Algebra.linearMap ℚ ℂ) ∘ₗ EQ := by
    apply Finsupp.lhom_ext
    intro C a
    simp only [LinearMap.comp_apply, castC_single, LinearMap.coe_restrictScalars, EQ,
      linearCombination_single, smul_eq_mul, Algebra.linearMap_apply, εC_single_smul, epsF_eq]
    push_cast
    rfl
  exact LinearMap.congr_fun h z

theorem EQ_LQ : EQ ∘ₗ LQ = 0 := by
  apply LinearMap.ext
  intro z
  apply (Rat.cast_injective (α := ℂ))
  rw [LinearMap.comp_apply, ← εC_castC, castC_LQ, LinearMap.zero_apply, Rat.cast_zero]
  exact LinearMap.congr_fun εC_δC (castC Cell z)

theorem epsQ_grade (C : Cell) (h : C.grade ≠ 0) : epsQ C = 0 := by
  have := εC_grade C h
  rw [εC_single, epsF_eq] at this
  exact_mod_cast this

theorem incQ_grade (C D : Cell) (h : incQ C D ≠ 0) : D.grade + 1 = C.grade := by
  apply δC_grade C D
  rw [Finsupp.mem_support_iff, ← castC_incQ, castC_apply]
  exact_mod_cast h

/-! ### Base points -/

/-- The vertices whose minimal lines contain the cell. -/
def vertFin (C : Cell) : Finset Vtx := (vertSet_finite C.isCell.1).toFinset

theorem mem_vertFin (C : Cell) (v : Vtx) : v ∈ vertFin C ↔ C.val ⊆ v.M := by
  unfold vertFin
  rw [Set.Finite.mem_toFinset]
  rfl

theorem vertFin_nonempty (C : Cell) : (vertFin C).Nonempty := by
  obtain ⟨v, hv⟩ := C.isCell.2
  exact ⟨v, (mem_vertFin C v).mpr hv⟩

/-- The barycentre of the vertex forms of a cell. -/
def bptMat (C : Cell) : Mat :=
  ((vertFin C).card : ℝ)⁻¹ • ∑ v ∈ vertFin C, formR v.gram

theorem bptMat_posDef (C : Cell) : (bptMat C).PosDef := by
  have hcard : (0 : ℝ) < (vertFin C).card := by exact_mod_cast (vertFin_nonempty C).card_pos
  exact (Matrix.posDef_sum (vertFin_nonempty C) fun v _ => formR_gram_posDef v).smul
    (inv_pos.mpr hcard)

/-- The base point of a cell: the average of the Gram matrices of its vertices. -/
def bpt (C : Cell) : PDMat := ⟨bptMat C, bptMat_posDef C⟩

theorem translate_translate (k k' : IntegralGL3) (v : Vtx) :
    Vtx.translate k (Vtx.translate k' v) = Vtx.translate (k * k') v := by
  apply Vtx.ext
  change act k⁻¹ (act k'⁻¹ v.gram) = act (k * k')⁻¹ v.gram
  rw [act_act, mul_inv_rev]

theorem translate_one (v : Vtx) : Vtx.translate 1 v = v := by
  apply Vtx.ext
  change act (1 : IntegralGL3)⁻¹ v.gram = v.gram
  rw [inv_one]
  simp [act, toQ_one]

theorem translate_injective (k : IntegralGL3) : Function.Injective (Vtx.translate k) := by
  intro v w h
  have := congrArg (Vtx.translate k⁻¹) h
  rwa [translate_translate, translate_translate, inv_mul_cancel, translate_one, translate_one] at this

theorem formR_translate (k : IntegralGL3) (v : Vtx) :
    formR (Vtx.translate k v).gram = actMat k (formR v.gram) := by
  change formR (act k⁻¹ v.gram) = _
  rw [formR_act]
  rfl

theorem mem_vertFin_smul (γ : principalLevel) (C : Cell) (v : Vtx) :
    v ∈ vertFin (γ • C) ↔ Vtx.translate (levelLift γ)⁻¹ v ∈ vertFin C := by
  rw [mem_vertFin, mem_vertFin]
  change γ • C.val ⊆ v.M ↔ _
  constructor
  · intro h t ht
    rw [Vtx.mem_M_translate, inv_inv]
    have := h (Finset.smul_mem_smul_finset (a := γ) ht)
    rwa [level_smul] at this
  · intro h x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_smul_finset.mp hx
    have := h ht
    rw [Vtx.mem_M_translate, inv_inv] at this
    rwa [level_smul]

theorem actMat_smul (g : IntegralGL3) (c : ℝ) (M : Mat) : actMat g (c • M) = c • actMat g M := by
  simp only [actMat, Matrix.mul_smul, Matrix.smul_mul]

theorem actMat_finsum {ι : Type} (g : IntegralGL3) (s : Finset ι) (M : ι → Mat) :
    actMat g (∑ i ∈ s, M i) = ∑ i ∈ s, actMat g (M i) := by
  simp only [actMat, Finset.mul_sum, Finset.sum_mul]

instance : MulAction principalLevel PDMat := MulAction.compHom PDMat levelLift

theorem smul_level_val (γ : principalLevel) (M : PDMat) : (γ • M).1 = actMat (levelLift γ) M.1 := rfl

theorem vertFin_smul (γ : principalLevel) (C : Cell) :
    vertFin (γ • C) = (vertFin C).image (Vtx.translate (levelLift γ)) := by
  ext v
  rw [mem_vertFin_smul, Finset.mem_image]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    rw [translate_translate, mul_inv_cancel, translate_one]
  · rintro ⟨v', hv', rfl⟩
    rwa [translate_translate, inv_mul_cancel, translate_one]

theorem bpt_smul (γ : principalLevel) (C : Cell) : bpt (γ • C) = γ • bpt C := by
  apply Subtype.ext
  change bptMat (γ • C) = actMat (levelLift γ) (bptMat C)
  unfold bptMat
  rw [vertFin_smul, Finset.card_image_of_injective _ (translate_injective _),
    Finset.sum_image (fun a _ b _ h => translate_injective _ h), actMat_smul, actMat_finsum]
  simp only [formR_translate]

theorem epsQ_smul (γ : principalLevel) (C : Cell) : epsQ (γ • C) = epsQ C := by
  unfold epsQ
  rw [Cell.smul_val, card_level_smul, epsMod_smul]

theorem incQ_smul (γ : principalLevel) (C : Cell) :
    incQ (γ • C) = Finsupp.mapDomain (γ • ·) (incQ C) := by
  apply castC_injective Cell
  have h1 : castC Cell (Finsupp.mapDomain (γ • ·) (incQ C)) =
      chainAct principalLevel γ (castC Cell (incQ C)) := by
    generalize incQ C = z
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [Finsupp.mapDomain_add, map_add, map_add, map_add, hf, hg]
    | single a q =>
      rw [Finsupp.mapDomain_single, castC_single, castC_single, chainAct_single]
  rw [h1, castC_incQ, castC_incQ]
  have := LinearMap.congr_fun (δC_equivariant γ) (single C 1)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, chainAct_single] at this
  exact this

/-! ### Support -/

/-- The convex hull (in `Q`-coordinates) of the vertex forms of the cell. -/
def reach (C : Cell) : Set PDMat :=
  {p | p.1 ∈ convexHull ℝ ((fun v : Vtx => formR v.gram) '' {v | C.val ⊆ v.M})}

theorem bpt_mem_reach (C : Cell) : bpt C ∈ reach C := by
  change bptMat C ∈ convexHull ℝ _
  have hcard : (0 : ℝ) < (vertFin C).card := by exact_mod_cast (vertFin_nonempty C).card_pos
  unfold bptMat
  rw [Finset.smul_sum]
  refine (convex_convexHull ℝ _).sum_mem (fun v _ => inv_nonneg.mpr hcard.le) ?_ (fun v hv =>
    subset_convexHull ℝ _ ⟨v, (mem_vertFin C v).mp hv, rfl⟩)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_inv_cancel₀ hcard.ne'

theorem subset_of_incQ_ne_zero (C D : Cell) (h : incQ C D ≠ 0) : C.val ⊆ D.val := by
  have hD : D.val ∈ (coboundaryOfQ C.val).support := by
    rw [Finsupp.mem_support_iff]
    exact h
  obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hD)
  have hS' := Finsupp.support_smul hw
  have := Finsupp.support_single_subset hS'
  rw [Finset.mem_singleton] at this
  rw [this]
  exact Finset.subset_insert _ _

theorem reach_mono (C D : Cell) (h : incQ C D ≠ 0) : reach D ⊆ reach C := by
  intro p hp
  refine convexHull_mono (Set.image_mono ?_) hp
  intro v hv
  exact (subset_of_incQ_ne_zero C D h).trans hv

/-- The cone data of the well-rounded retract. -/
def coneData : ConeData Cell PDMat where
  grade := Cell.grade
  inc := incQ
  eps := epsQ
  bpt := bpt
  inc_grade := incQ_grade
  eps_grade := epsQ_grade
  inc_inc := LQ_LQ
  eps_inc := EQ_LQ

/-- The value of a real form at an integer vector. -/
def qfR (M : Mat) (x : Vec) : ℝ := ∑ i, ∑ j, M i j * (x i : ℝ) * (x j : ℝ)

theorem qfR_formR (A : Form) (x : Vec) : qfR (formR A) x = (qf A x : ℝ) := by
  simp [qfR, formR, qf]

theorem convex_qfR_ge_one (x : Vec) : Convex ℝ {M : Mat | 1 ≤ qfR M x} := by
  intro a ha b hb s t hs ht hst
  have e : qfR (s • a + t • b) x = s * qfR a x + t * qfR b x := by
    simp only [qfR, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    ring_nf
  change 1 ≤ qfR (s • a + t • b) x
  rw [e]
  have ha' : 1 ≤ qfR a x := ha
  have hb' : 1 ≤ qfR b x := hb
  nlinarith

/-- Every point of `reach C` takes values `≥ 1` on nonzero integer vectors (the Ryshkov polyhedron; the
well-rounded retract also needs `reach_eq_one` and spanning, see `reach_well_rounded`). -/
theorem reach_ge_one (C : Cell) {p : PDMat} (hp : p ∈ reach C) {x : Vec} (hx : x ≠ 0) :
    1 ≤ qfR p.1 x := by
  have hsub : (fun v : Vtx => formR v.gram) '' {v | C.val ⊆ v.M} ⊆ {M : Mat | 1 ≤ qfR M x} := by
    rintro _ ⟨v, -, rfl⟩
    change 1 ≤ qfR (formR v.gram) x
    rw [qfR_formR]
    exact_mod_cast v.qf_ge_one hx
  exact convexHull_min hsub (convex_qfR_ge_one x) hp

theorem convex_qfR_eq_one (x : Vec) : Convex ℝ {M : Mat | qfR M x = 1} := by
  intro a ha b hb s t hs ht hst
  have e : qfR (s • a + t • b) x = s * qfR a x + t * qfR b x := by
    simp only [qfR, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    ring_nf
  change qfR (s • a + t • b) x = 1
  rw [e]
  have ha' : qfR a x = 1 := ha
  have hb' : qfR b x = 1 := hb
  rw [ha', hb']
  linarith

/-- Every point of `reach C` takes the value `1` on each minimal line of the cell. -/
theorem reach_eq_one (C : Cell) {p : PDMat} (hp : p ∈ reach C) {x : Vec} (hx : Line.mk x ∈ C.val) :
    qfR p.1 x = 1 := by
  have hsub : (fun v : Vtx => formR v.gram) '' {v | C.val ⊆ v.M} ⊆ {M : Mat | qfR M x = 1} := by
    rintro _ ⟨v, hv, rfl⟩
    change qfR (formR v.gram) x = 1
    rw [qfR_formR]
    have := (v.mem_M_mk x).mp (hv hx)
    rw [this]
    simp
  exact convexHull_min hsub (convex_qfR_eq_one x) hp

/-- **The cells lie in the well-rounded retract**: every point of `reach C` is positive definite, takes
the value `≥ 1` on all nonzero integer vectors, takes the value exactly `1` on the minimal lines of the
cell, and these lines span. -/
theorem reach_well_rounded (C : Cell) {p : PDMat} (hp : p ∈ reach C) :
    (∀ x : Vec, x ≠ 0 → 1 ≤ qfR p.1 x) ∧ (∀ x : Vec, Line.mk x ∈ C.val → qfR p.1 x = 1) ∧
      Spans C.val :=
  ⟨fun _ hx => reach_ge_one C hp hx, fun _ hx => reach_eq_one C hp hx, C.isCell.1⟩

theorem affMap_mem_reach (C : Cell) {n : ℕ} (y : AffSimp PDMat n) (hy : ∀ i, y i ∈ reach C)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) : affMap n y t ∈ reach C := by
  change (∑ i, t.weights i • (y i).1) ∈ convexHull ℝ _
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => t.weights_nonneg i) t.total_of_fintype (fun i _ => hy i)

theorem affSing_apply {n : ℕ} (y : AffSimp PDMat n) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (TopCat.of Glued).toSSetObjEquiv _ (affSing y) t = nu (affMap n y t) := by
  simp [affSing]

/-! ### The cell chains -/

/-- The singular chain, of degree `n`, attached to a cell by the cone recursion
(for a cell of grade `n`; all `n` are defined). -/
def cellAt (n : ℕ) (C : Cell) : (underlyingChains (TopCat.of Glued)).X n :=
  realize n (coneData.phi n C)

/-- The singular chain of a cell, in degree equal to its grade. -/
def cellSing (C : Cell) : (underlyingChains (TopCat.of Glued)).X C.grade := cellAt C.grade C

theorem cellAt_zero (C : Cell) :
    cellAt 0 C = epsQ C • sing (TopCat.of Glued) (affSing (fun _ => bpt C)) := by
  unfold cellAt
  change realize 0 (epsQ C • ptAff (bpt C)) = _
  rw [map_smul, ptAff, realize_single, one_smul]

theorem realize_Phi (n : ℕ) (z : Cell →₀ ℚ) :
    realize n (coneData.Phi n z) = z.sum fun D a => a • cellAt n D := by
  rw [ConeData.Phi, linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [map_smul]
  rfl

theorem d_cellAt (n : ℕ) (C : Cell) (hC : C.grade = n + 1) :
    ((underlyingChains (TopCat.of Glued)).d (n + 1) n).hom (cellAt (n + 1) C) =
      (incQ C).sum fun D a => a • cellAt n D := by
  unfold cellAt
  rw [d_realize, coneData.phi_boundary n C hC, realize_Phi]
  rfl

theorem cellAt_smul (γ : principalLevel) (n : ℕ) (C : Cell) :
    cellAt n (γ • C) = (chainRep IntegralGL3 (TopCat.of Glued) n).ρ (levelLift γ) (cellAt n C) := by
  unfold cellAt
  rw [coneData.phi_smul bpt_smul epsQ_smul incQ_smul n γ C, realize_smul]
  rfl

theorem cellAt_support (n : ℕ) (C : Cell) :
    ∀ y ∈ (coneData.phi n C).support, ∀ i, y i ∈ reach C :=
  coneData.phi_support reach bpt_mem_reach reach_mono n C

/-! ### The boundary in terms of the library's insertion signs -/

/-- Inserting a neighbouring line into a cell gives a cell. -/
def insertCell (C : Cell) (w : Line) (hw : w ∈ nbrs C.val) : Cell :=
  ⟨insert w C.val, C.isCell.1.mono (Finset.subset_insert _ _), ((mem_nbrs C.isCell.1 w).mp hw).2⟩

theorem insertCell_val (C : Cell) (w : Line) (hw : w ∈ nbrs C.val) :
    (insertCell C w hw).val = insert w C.val := rfl

theorem incQ_eq_sum (C : Cell) :
    incQ C = ∑ w : ↥(nbrs C.val), insSignQ C.val w • single (insertCell C w w.2) (1 : ℚ) := by
  ext D
  rw [incQ_apply, coboundaryOfQ, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  rw [← Finset.sum_coe_sort (nbrs C.val)]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Finsupp.smul_apply, Finsupp.single_apply, Cell.ext_iff, insertCell_val]

theorem d_cellAt_nbrs (n : ℕ) (C : Cell) (hC : C.grade = n + 1) :
    ((underlyingChains (TopCat.of Glued)).d (n + 1) n).hom (cellAt (n + 1) C) =
      ∑ w : ↥(nbrs C.val), insSignQ C.val w • cellAt n (insertCell C w w.2) := by
  rw [d_cellAt n C hC]
  have : ((incQ C).sum fun D a => a • cellAt n D) = linearCombination ℚ (cellAt n) (incQ C) := rfl
  rw [this, incQ_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, linearCombination_single, one_smul]

/-! ### Equivariance for `Γ(6)` -/

/-- A level-three element of `IntegralGL3` as an element of the library's `Γ(3)`. -/
def levelOfThree (g : IntegralGL3) (hg : g ∈ TernaryPoly.IntegralGL3Congruence.principalThree) :
    principalLevel :=
  ⟨integralToRational g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩

theorem levelLift_levelOfThree (g : IntegralGL3)
    (hg : g ∈ TernaryPoly.IntegralGL3Congruence.principalThree) :
    levelLift (levelOfThree g hg) = g := by
  apply integralToRational_injective
  rw [integralToRational_levelLift]
  rfl

/-- An element of `Γ(6)` (the library's `principalSix`) as an element of the library's `Γ(3)`. -/
def levelOfSix (g : TernaryPoly.IntegralGL3Congruence.principalSix) : principalLevel :=
  levelOfThree g.1 (TernaryPoly.IntegralGL3Congruence.principalSix_le_three g.2)

theorem levelLift_levelOfSix (g : TernaryPoly.IntegralGL3Congruence.principalSix) :
    levelLift (levelOfSix g) = g.1 :=
  levelLift_levelOfThree _ _

/-- **Equivariance of the cell chains for `Γ(6)` acting on `Glued` by the standard action.** -/
theorem cellAt_smul_six (g : TernaryPoly.IntegralGL3Congruence.principalSix) (n : ℕ) (C : Cell) :
    cellAt n (levelOfSix g • C) = (chainRep IntegralGL3 (TopCat.of Glued) n).ρ g.1 (cellAt n C) := by
  rw [cellAt_smul, levelLift_levelOfSix]

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
