module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.Cone

@[expose] public section


/-!
# The diagonal of a homotopy pushout cone

Let `K` be the homotopy pushout cone of strictly diagonal-compatible chain maps `a : A ⟶ L`, `b : A ⟶ P` between
complexes with diagonal systems.  The diagonal of `K` is the Alexander-Whitney diagonal on `L` and `P`, and on the
shifted copy of `A` (with `d(x[1]) = -(dx)[1] + a x - b x`)

  `Δ(x[1]) = Σ x'[1] ⊗ a(x'') + (-1)^p Σ b(x') ⊗ x''[1]`   (`p` the front degree).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]
  {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}

namespace PushCone

variable (𝒞 : PushCone A L P K a b) (SA : DiagSystem A) (SL : DiagSystem L) (SP : DiagSystem P)

/-- The term `x'[1] ⊗ a x''` of the diagonal of a shifted corner chain. -/
def tI (p' q n' : ℕ) (h : p' + q = n') : A.X n' ⟶ K.X (p'+1) ⊗ K.X q :=
  SA.Δ p' q n' h ≫ (𝒞.iA p' ⊗ₘ (a.f q ≫ 𝒞.iL q))

/-- The term `b x' ⊗ x''[1]` of the diagonal of a shifted corner chain. -/
def tII (p q' n' : ℕ) (h : p + q' = n') : A.X n' ⟶ K.X p ⊗ K.X (q'+1) :=
  SA.Δ p q' n' h ≫ ((b.f p ≫ 𝒞.iP p) ⊗ₘ 𝒞.iA q')

/-- The first term, zero if the front degree is zero. -/
def tIc : ∀ (p q n' : ℕ), p + q = n' + 1 → (A.X n' ⟶ K.X p ⊗ K.X q)
  | 0, _, _, _ => 0
  | p'+1, q, n', h => 𝒞.tI SA p' q n' (by omega)

/-- The second term, zero if the back degree is zero. -/
def tIIc : ∀ (p q n' : ℕ), p + q = n' + 1 → (A.X n' ⟶ K.X p ⊗ K.X q)
  | _, 0, _, _ => 0
  | p, q'+1, n', h => 𝒞.tII SA p q' n' (by omega)

/-- The diagonal of a shifted corner chain. -/
def aPart (p q n' : ℕ) (h : p + q = n' + 1) : A.X n' ⟶ K.X p ⊗ K.X q :=
  𝒞.tIc SA p q n' h + ((-1 : ℤ)^p) • 𝒞.tIIc SA p q n' h

/-- The diagonal of the pushout cone. -/
def Δ : ∀ (p q n : ℕ), p + q = n → (K.X n ⟶ K.X p ⊗ K.X q)
  | p, q, 0, h => 𝒞.desc0 (SL.Δ p q 0 h ≫ (𝒞.iL p ⊗ₘ 𝒞.iL q)) (SP.Δ p q 0 h ≫ (𝒞.iP p ⊗ₘ 𝒞.iP q))
  | p, q, n'+1, h => 𝒞.desc n' (𝒞.aPart SA p q n' h) (SL.Δ p q (n'+1) h ≫ (𝒞.iL p ⊗ₘ 𝒞.iL q))
      (SP.Δ p q (n'+1) h ≫ (𝒞.iP p ⊗ₘ 𝒞.iP q))

/-- The augmentation of the pushout cone. -/
def eps : K.X 0 ⟶ 𝟙_ (Rep.{0} ℚ Γ) := 𝒞.desc0 SL.eps SP.eps

@[reassoc]
theorem iL_Δ_zero (p q : ℕ) (h : p + q = 0) :
    𝒞.iL 0 ≫ 𝒞.Δ SA SL SP p q 0 h = SL.Δ p q 0 h ≫ (𝒞.iL p ⊗ₘ 𝒞.iL q) :=
  𝒞.iL0_desc0 _ _

@[reassoc]
theorem iP_Δ_zero (p q : ℕ) (h : p + q = 0) :
    𝒞.iP 0 ≫ 𝒞.Δ SA SL SP p q 0 h = SP.Δ p q 0 h ≫ (𝒞.iP p ⊗ₘ 𝒞.iP q) :=
  𝒞.iP0_desc0 _ _

@[reassoc]
theorem iA_Δ (p q n' : ℕ) (h : p + q = n' + 1) :
    𝒞.iA n' ≫ 𝒞.Δ SA SL SP p q (n'+1) h = 𝒞.aPart SA p q n' h :=
  𝒞.iA_desc n' _ _ _

@[reassoc]
theorem iL_Δ (p q n' : ℕ) (h : p + q = n' + 1) :
    𝒞.iL (n'+1) ≫ 𝒞.Δ SA SL SP p q (n'+1) h = SL.Δ p q (n'+1) h ≫ (𝒞.iL p ⊗ₘ 𝒞.iL q) :=
  𝒞.iL_desc n' _ _ _

@[reassoc]
theorem iP_Δ (p q n' : ℕ) (h : p + q = n' + 1) :
    𝒞.iP (n'+1) ≫ 𝒞.Δ SA SL SP p q (n'+1) h = SP.Δ p q (n'+1) h ≫ (𝒞.iP p ⊗ₘ 𝒞.iP q) :=
  𝒞.iP_desc n' _ _ _

/-- Strict diagonal compatibility of `a` and `b` (with the augmentations). -/
structure Strict : Prop where
  a_strict : ∀ p q n (h : p + q = n), a.f n ≫ SL.Δ p q n h = SA.Δ p q n h ≫ (a.f p ⊗ₘ a.f q)
  b_strict : ∀ p q n (h : p + q = n), b.f n ≫ SP.Δ p q n h = SA.Δ p q n h ≫ (b.f p ⊗ₘ b.f q)
  a_eps : a.f 0 ≫ SL.eps = SA.eps
  b_eps : b.f 0 ≫ SP.eps = SA.eps

variable {𝒞 SA SL SP}

@[reassoc]
theorem iL_Δ' (p q n : ℕ) (h : p + q = n) :
    𝒞.iL n ≫ 𝒞.Δ SA SL SP p q n h = SL.Δ p q n h ≫ (𝒞.iL p ⊗ₘ 𝒞.iL q) := by
  cases n with
  | zero => exact 𝒞.iL_Δ_zero SA SL SP p q h
  | succ n' => exact 𝒞.iL_Δ SA SL SP p q n' h

@[reassoc]
theorem iP_Δ' (p q n : ℕ) (h : p + q = n) :
    𝒞.iP n ≫ 𝒞.Δ SA SL SP p q n h = SP.Δ p q n h ≫ (𝒞.iP p ⊗ₘ 𝒞.iP q) := by
  cases n with
  | zero => exact 𝒞.iP_Δ_zero SA SL SP p q h
  | succ n' => exact 𝒞.iP_Δ SA SL SP p q n' h

theorem eps_d (hS : Strict (a := a) (b := b) SA SL SP) : K.d 1 0 ≫ 𝒞.eps SL SP = 0 := by
  apply 𝒞.ext 0
  · rw [← Category.assoc, 𝒞.dA0, Preadditive.sub_comp, Category.assoc, Category.assoc]
    unfold eps
    rw [𝒞.iL0_desc0, 𝒞.iP0_desc0, hS.a_eps, hS.b_eps, sub_self, comp_zero]
  · rw [← Category.assoc, 𝒞.dL, Category.assoc]
    unfold eps
    rw [𝒞.iL0_desc0, SL.eps_d, comp_zero]
  · rw [← Category.assoc, 𝒞.dP, Category.assoc]
    unfold eps
    rw [𝒞.iP0_desc0, SP.eps_d, comp_zero]

theorem tensor_unit_right' {X Y Z : Rep.{0} ℚ Γ} (f : X ⟶ Y) (e : Z ⟶ 𝟙_ (Rep.{0} ℚ Γ)) :
    (f ⊗ₘ e) ≫ (ρ_ Y).hom = (X ◁ e) ≫ (ρ_ X).hom ≫ f := by
  rw [MonoidalCategory.tensorHom_def', Category.assoc, MonoidalCategory.rightUnitor_naturality]

theorem tensor_whisker_eps {X Y W Z : Rep.{0} ℚ Γ} (f : X ⟶ Y) (g : W ⟶ Z) (e : Z ⟶ 𝟙_ (Rep.{0} ℚ Γ)) :
    (f ⊗ₘ g) ≫ (Y ◁ e) ≫ (ρ_ Y).hom = (X ◁ (g ≫ e)) ≫ (ρ_ X).hom ≫ f := by
  rw [← Category.assoc, ← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id, tensor_unit_right']

theorem counit (hS : Strict (a := a) (b := b) SA SL SP) (p : ℕ) :
    𝒞.Δ SA SL SP p 0 p (add_zero p) ≫ (K.X p ◁ 𝒞.eps SL SP) ≫ (ρ_ (K.X p)).hom = 𝟙 (K.X p) := by
  have hL : ∀ p, 𝒞.iL p ≫ 𝒞.Δ SA SL SP p 0 p (add_zero p) ≫ (K.X p ◁ 𝒞.eps SL SP) ≫ (ρ_ (K.X p)).hom =
      𝒞.iL p := by
    intro p
    rw [← Category.assoc, iL_Δ', Category.assoc, tensor_whisker_eps]
    unfold eps
    rw [𝒞.iL0_desc0]
    calc SL.Δ p 0 p (add_zero p) ≫ (L.X p ◁ SL.eps) ≫ (ρ_ (L.X p)).hom ≫ 𝒞.iL p
        = (SL.Δ p 0 p (add_zero p) ≫ (L.X p ◁ SL.eps) ≫ (ρ_ (L.X p)).hom) ≫ 𝒞.iL p := by
          simp only [Category.assoc]
      _ = 𝒞.iL p := by rw [SL.counit]; simp
  have hP : ∀ p, 𝒞.iP p ≫ 𝒞.Δ SA SL SP p 0 p (add_zero p) ≫ (K.X p ◁ 𝒞.eps SL SP) ≫ (ρ_ (K.X p)).hom =
      𝒞.iP p := by
    intro p
    rw [← Category.assoc, iP_Δ', Category.assoc, tensor_whisker_eps]
    unfold eps
    rw [𝒞.iP0_desc0]
    calc SP.Δ p 0 p (add_zero p) ≫ (P.X p ◁ SP.eps) ≫ (ρ_ (P.X p)).hom ≫ 𝒞.iP p
        = (SP.Δ p 0 p (add_zero p) ≫ (P.X p ◁ SP.eps) ≫ (ρ_ (P.X p)).hom) ≫ 𝒞.iP p := by
          simp only [Category.assoc]
      _ = 𝒞.iP p := by rw [SP.counit]; simp
  cases p with
  | zero =>
    apply 𝒞.ext0
    · rw [hL 0, Category.comp_id]
    · rw [hP 0, Category.comp_id]
  | succ p' =>
    apply 𝒞.ext p'
    · have e : 𝒞.aPart SA (p'+1) 0 p' (by omega) = 𝒞.tI SA p' 0 p' rfl := by
        simp [aPart, tIc, tIIc]
      rw [← Category.assoc, iA_Δ, e]
      unfold tI
      rw [Category.assoc, tensor_whisker_eps]
      have e2 : a.f 0 ≫ 𝒞.iL 0 ≫ 𝒞.eps SL SP = SA.eps := by
        unfold eps; rw [𝒞.iL0_desc0, hS.a_eps]
      rw [Category.assoc (a.f 0) (𝒞.iL 0), e2]
      calc SA.Δ p' 0 p' (by omega) ≫ (A.X p' ◁ SA.eps) ≫ (ρ_ (A.X p')).hom ≫ 𝒞.iA p'
          = (SA.Δ p' 0 p' (by omega) ≫ (A.X p' ◁ SA.eps) ≫ (ρ_ (A.X p')).hom) ≫ 𝒞.iA p' := by
            simp only [Category.assoc]
        _ = 𝒞.iA p' ≫ 𝟙 (K.X (p'+1)) := by rw [SA.counit]; simp
    · rw [hL (p'+1), Category.comp_id]
    · rw [hP (p'+1), Category.comp_id]

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
