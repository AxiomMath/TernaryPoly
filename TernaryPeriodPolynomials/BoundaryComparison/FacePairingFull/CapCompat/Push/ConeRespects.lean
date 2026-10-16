module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeCarrierData

@[expose] public section


/-!
# Diagonals of a pushout cone respect pushout carriers

A subspace family `Kf` *respects* a diagonal system `S` if `Δ` maps `Kf n` into the span of tensors `u ⊗ v` with
`u ∈ Kf p`, `v ∈ Kf q`.  If the three strata respect `KA`, `KL`, `KP` (and `a(KA) ⊆ KL`, `b(KA) ⊆ KP`), the pushout
cone respects `coneK KA KL KP`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

theorem tensorHom_hom_tmul {X Y X' Y' : Rep.{0} ℚ Γ} (f : X ⟶ X') (g : Y ⟶ Y') (u : X) (v : Y) :
    (f ⊗ₘ g).hom (u ⊗ₜ[ℚ] v) = f.hom u ⊗ₜ[ℚ] g.hom v := by
  rw [Rep.hom_tensorHom]; rfl

/-- The diagonal sends a subspace family into the span of tensors of elements of the family. -/
def DiagRespects {D : ChainComplex (Rep.{0} ℚ Γ) ℕ} (S : DiagSystem D) (Kf : ∀ m, Submodule ℚ (D.X m)) : Prop :=
  ∀ (p q n : ℕ) (h : p + q = n), ∀ x ∈ Kf n, (S.Δ p q n h).hom x ∈ Submodule.span ℚ
    {t | ∃ (u : D.X p) (v : D.X q), u ∈ Kf p ∧ v ∈ Kf q ∧ t = (u ⊗ₜ[ℚ] v : (D.X p ⊗ D.X q : Rep.{0} ℚ Γ))}

theorem DiagRespects_bot {D : ChainComplex (Rep.{0} ℚ Γ) ℕ} (S : DiagSystem D) :
    DiagRespects S (fun _ => ⊥) := by
  intro p q n h x hx
  rw [Submodule.mem_bot] at hx
  rw [hx, map_zero]; exact Submodule.zero_mem _

namespace PushCone

variable {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
  (𝒞 : PushCone A L P K a b) (KA : ∀ m, Submodule ℚ (A.X m)) (KL : ∀ m, Submodule ℚ (L.X m))
  (KP : ∀ m, Submodule ℚ (P.X m))

theorem iL_mem_coneK (m : ℕ) {u : L.X m} (hu : u ∈ KL m) : (𝒞.iL m).hom u ∈ 𝒞.coneK KA KL KP m := by
  cases m with
  | zero => exact (𝒞.mem_coneK_zero KA KL KP _).mpr ⟨u, hu, 0, (KP 0).zero_mem, by simp⟩
  | succ m => exact (𝒞.mem_coneK_succ KA KL KP m _).mpr ⟨0, (KA m).zero_mem, u, hu, 0, (KP (m+1)).zero_mem, by simp⟩

theorem iP_mem_coneK (m : ℕ) {u : P.X m} (hu : u ∈ KP m) : (𝒞.iP m).hom u ∈ 𝒞.coneK KA KL KP m := by
  cases m with
  | zero => exact (𝒞.mem_coneK_zero KA KL KP _).mpr ⟨0, (KL 0).zero_mem, u, hu, by simp⟩
  | succ m => exact (𝒞.mem_coneK_succ KA KL KP m _).mpr ⟨0, (KA m).zero_mem, 0, (KL (m+1)).zero_mem, u, hu, by simp⟩

theorem iA_mem_coneK (m : ℕ) {u : A.X m} (hu : u ∈ KA m) : (𝒞.iA m).hom u ∈ 𝒞.coneK KA KL KP (m+1) :=
  (𝒞.mem_coneK_succ KA KL KP m _).mpr ⟨u, hu, 0, (KL (m+1)).zero_mem, 0, (KP (m+1)).zero_mem, by simp⟩

variable (SA : DiagSystem A) (SL : DiagSystem L) (SP : DiagSystem P)

/-- The span of tensors of elements of the cone carrier. -/
def tensSpan (p q : ℕ) : Submodule ℚ (K.X p ⊗ K.X q : Rep.{0} ℚ Γ) :=
  Submodule.span ℚ {t | ∃ (u : K.X p) (v : K.X q), u ∈ 𝒞.coneK KA KL KP p ∧ v ∈ 𝒞.coneK KA KL KP q ∧
    t = (u ⊗ₜ[ℚ] v : (K.X p ⊗ K.X q : Rep.{0} ℚ Γ))}

theorem tI_mem (hA : DiagRespects SA KA) (ha : ∀ m, ∀ x ∈ KA m, (a.f m).hom x ∈ KL m)
    (p' q n' : ℕ) (h : p' + q = n') {x0 : A.X n'} (hx : x0 ∈ KA n') :
    (𝒞.tI SA p' q n' h).hom x0 ∈ 𝒞.tensSpan KA KL KP (p'+1) q := by
  unfold tI
  rw [Rep.hom_comp]
  change (𝒞.iA p' ⊗ₘ (a.f q ≫ 𝒞.iL q)).hom ((SA.Δ p' q n' h).hom x0) ∈ _
  refine span_map_mem ((𝒞.iA p' ⊗ₘ (a.f q ≫ 𝒞.iL q)).hom.toLinearMap) ?_ (hA p' q n' h x0 hx)
  rintro t ⟨u, v, hu, hv, rfl⟩
  refine Submodule.subset_span ⟨(𝒞.iA p').hom u, (𝒞.iL q).hom ((a.f q).hom v), 𝒞.iA_mem_coneK KA KL KP p' hu,
    𝒞.iL_mem_coneK KA KL KP q (ha q v hv), ?_⟩
  exact tensorHom_hom_tmul _ _ _ _

theorem tII_mem (hA : DiagRespects SA KA) (hb : ∀ m, ∀ x ∈ KA m, (b.f m).hom x ∈ KP m)
    (p q' n' : ℕ) (h : p + q' = n') {x0 : A.X n'} (hx : x0 ∈ KA n') :
    (𝒞.tII SA p q' n' h).hom x0 ∈ 𝒞.tensSpan KA KL KP p (q'+1) := by
  unfold tII
  rw [Rep.hom_comp]
  change ((b.f p ≫ 𝒞.iP p) ⊗ₘ 𝒞.iA q').hom ((SA.Δ p q' n' h).hom x0) ∈ _
  refine span_map_mem ((((b.f p ≫ 𝒞.iP p) ⊗ₘ 𝒞.iA q')).hom.toLinearMap) ?_ (hA p q' n' h x0 hx)
  rintro t ⟨u, v, hu, hv, rfl⟩
  refine Submodule.subset_span ⟨(𝒞.iP p).hom ((b.f p).hom u), (𝒞.iA q').hom v,
    𝒞.iP_mem_coneK KA KL KP p (hb p u hu), 𝒞.iA_mem_coneK KA KL KP q' hv, ?_⟩
  exact tensorHom_hom_tmul _ _ _ _

theorem coneK_respects (hA : DiagRespects SA KA) (hL : DiagRespects SL KL) (hP : DiagRespects SP KP)
    (ha : ∀ m, ∀ x ∈ KA m, (a.f m).hom x ∈ KL m) (hb : ∀ m, ∀ x ∈ KA m, (b.f m).hom x ∈ KP m)
    (p q n : ℕ) (h : p + q = n) {x : K.X n} (hx : x ∈ 𝒞.coneK KA KL KP n) :
    (𝒞.Δ SA SL SP p q n h).hom x ∈ 𝒞.tensSpan KA KL KP p q := by
  have hLterm : ∀ {l : L.X n}, l ∈ KL n →
      (𝒞.Δ SA SL SP p q n h).hom ((𝒞.iL n).hom l) ∈ 𝒞.tensSpan KA KL KP p q := by
    intro l hl
    have := congrArg (fun φ => φ.hom l) (iL_Δ' (𝒞 := 𝒞) (SA := SA) (SL := SL) (SP := SP) p q n h)
    simp only [Rep.hom_comp] at this
    rw [show (𝒞.Δ SA SL SP p q n h).hom ((𝒞.iL n).hom l) =
      (𝒞.iL p ⊗ₘ 𝒞.iL q).hom ((SL.Δ p q n h).hom l) from this]
    refine span_map_mem ((𝒞.iL p ⊗ₘ 𝒞.iL q).hom.toLinearMap) ?_ (hL p q n h l hl)
    rintro t ⟨u, v, hu, hv, rfl⟩
    exact Submodule.subset_span ⟨(𝒞.iL p).hom u, (𝒞.iL q).hom v, 𝒞.iL_mem_coneK KA KL KP p hu,
      𝒞.iL_mem_coneK KA KL KP q hv, tensorHom_hom_tmul _ _ _ _⟩
  have hPterm : ∀ {p' : P.X n}, p' ∈ KP n →
      (𝒞.Δ SA SL SP p q n h).hom ((𝒞.iP n).hom p') ∈ 𝒞.tensSpan KA KL KP p q := by
    intro l hl
    have := congrArg (fun φ => φ.hom l) (iP_Δ' (𝒞 := 𝒞) (SA := SA) (SL := SL) (SP := SP) p q n h)
    simp only [Rep.hom_comp] at this
    rw [show (𝒞.Δ SA SL SP p q n h).hom ((𝒞.iP n).hom l) =
      (𝒞.iP p ⊗ₘ 𝒞.iP q).hom ((SP.Δ p q n h).hom l) from this]
    refine span_map_mem ((𝒞.iP p ⊗ₘ 𝒞.iP q).hom.toLinearMap) ?_ (hP p q n h l hl)
    rintro t ⟨u, v, hu, hv, rfl⟩
    exact Submodule.subset_span ⟨(𝒞.iP p).hom u, (𝒞.iP q).hom v, 𝒞.iP_mem_coneK KA KL KP p hu,
      𝒞.iP_mem_coneK KA KL KP q hv, tensorHom_hom_tmul _ _ _ _⟩
  cases n with
  | zero =>
    obtain ⟨l, hl, p', hp', rfl⟩ := (𝒞.mem_coneK_zero KA KL KP x).mp hx
    rw [map_add]
    exact Submodule.add_mem _ (hLterm hl) (hPterm hp')
  | succ n =>
    obtain ⟨x0, hx0, l, hl, p', hp', rfl⟩ := (𝒞.mem_coneK_succ KA KL KP n x).mp hx
    rw [map_add, map_add]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ (hLterm hl)) (hPterm hp')
    have := congrArg (fun φ => φ.hom x0) (𝒞.iA_Δ SA SL SP p q n h)
    change (𝒞.Δ SA SL SP p q (n+1) h).hom ((𝒞.iA n).hom x0) = (𝒞.aPart SA p q n h).hom x0 at this
    rw [this]
    change (𝒞.tIc SA p q n h).hom x0 + ((-1 : ℤ)^p) • (𝒞.tIIc SA p q n h).hom x0 ∈ _
    refine Submodule.add_mem _ ?_ (Submodule.smul_of_tower_mem _ _ ?_)
    · cases p with
      | zero => simp [tIc]
      | succ p' => exact 𝒞.tI_mem KA KL KP SA hA ha p' q n _ hx0
    · cases q with
      | zero => simp [tIIc]
      | succ q' => exact 𝒞.tII_mem KA KL KP SA hA hb p q' n _ hx0

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
