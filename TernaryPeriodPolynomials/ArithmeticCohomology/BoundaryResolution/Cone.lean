module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Basic
public import Mathlib.Algebra.Homology.HomotopyCofiber

@[expose] public section

noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison.Cone
open CategoryTheory Category Limits HomologicalComplex Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  (S : ShortComplex (ChainComplex C ℕ))
  (r : ∀ n, S.X₂.X n ⟶ S.X₁.X n)

abbrev total := homotopyCofiber S.f

theorem downRel (n : ℕ) : (ComplexShape.down ℕ).Rel (n+1) n := rfl

def left (i j : ℕ) (h : (ComplexShape.down ℕ).Rel j i) : S.X₁.X i ⟶ (total S).X j :=
  homotopyCofiber.inlX S.f i j h

def right (n : ℕ) : S.X₂.X n ⟶ (total S).X n := homotopyCofiber.inrX S.f n

def second (n : ℕ) : (total S).X n ⟶ S.X₂.X n := homotopyCofiber.sndX S.f n

def first (n : ℕ) : (total S).X (n+1) ⟶ S.X₁.X n :=
  homotopyCofiber.fstX S.f (n+1) n (downRel n)

@[simp] theorem left_second (i j : ℕ) (h : (ComplexShape.down ℕ).Rel j i) :
    left S i j h ≫ second S j=0 := homotopyCofiber.inlX_sndX S.f i j h

@[simp] theorem left_first (n : ℕ) : left S n (n+1) (downRel n) ≫ first S n=𝟙 _ :=
  homotopyCofiber.inlX_fstX S.f n (n+1) (downRel n)

theorem d_second (n : ℕ) : (total S).d (n+1) n ≫ second S n=
    first S n ≫ S.f.f n + second S (n+1) ≫ S.X₂.d (n+1) n :=
  homotopyCofiber.d_sndX S.f (n+1) n (downRel n)

theorem left_d_second (n : ℕ) : left S n (n+1) (downRel n) ≫ (total S).d (n+1) n ≫ second S n=S.f.f n := by
  rw [d_second,comp_add,←Category.assoc,←Category.assoc,left_first,left_second,id_comp,zero_comp,add_zero]

/-- The actual total cone projects to the quotient through the prescribed short-complex map. -/
def projection : total S ⟶ S.X₃ := homotopyCofiber.desc S.f S.g (Homotopy.ofEq S.zero)

@[simp] theorem inr_projection : homotopyCofiber.inr S.f ≫ projection S=S.g :=
  homotopyCofiber.inr_desc _ _ _

@[simp] theorem right_projection_f (n : ℕ) : right S n ≫ (projection S).f n=S.g.f n :=
  homotopyCofiber.inrX_desc_f _ _ _ n

@[simp] theorem left_projection_f (i j : ℕ) (h : (ComplexShape.down ℕ).Rel j i) :
    left S i j h ≫ (projection S).f j=0 := homotopyCofiber.inlX_desc_f _ _ _ i j h

/-- The actual graded splitting gives the cone contraction in the flag direction. -/
def contraction (i j : ℕ) (h : (ComplexShape.down ℕ).Rel j i) :
    (total S).X i ⟶ (total S).X j :=
  second S i ≫ r i ≫ left S i j h

def correction : total S ⟶ total S := Homotopy.nullHomotopicMap' (contraction S r)
def retractMap : total S ⟶ total S := 𝟙 _-correction S r

theorem correction_projection : correction S r ≫ projection S=0 := by
  rw [correction,Homotopy.nullHomotopicMap'_comp]
  have h : (fun i j h => contraction S r i j h ≫ (projection S).f j)=
      (fun i j (_ : (ComplexShape.down ℕ).Rel j i) => (0 : (total S).X i ⟶ S.X₃.X j)) := by
    funext i j h
    simp only [contraction,Category.assoc,left_projection_f,comp_zero]
  rw [h]
  apply HomologicalComplex.hom_ext
  intro n
  simp [Homotopy.nullHomotopicMap',Homotopy.nullHomotopicMap,dNext,prevD]

theorem retractMap_projection : retractMap S r ≫ projection S=projection S := by
  rw [retractMap,sub_comp,id_comp,correction_projection,sub_zero]

variable (fr : ∀ n, S.f.f n ≫ r n=𝟙 _)

include fr in
/-- The correction is the identity on the shifted flag summand. -/
theorem inl_correction (n : ℕ) :
    left S n (n+1) (downRel n) ≫ (correction S r).f (n+1)=left S n (n+1) (downRel n) := by
  rw [correction,Homotopy.nullHomotopicMap'_f (downRel (n+1)) (downRel n)]
  simp only [contraction,comp_add,Category.assoc]
  rw [←Category.assoc (left S n (n+1) (downRel n)) (second S (n+1)),left_second,zero_comp,add_zero]
  rw [←Category.assoc ((total S).d (n+1) n) (second S n),
    ←Category.assoc (left S n (n+1) (downRel n)) ((total S).d (n+1) n ≫ second S n),left_d_second]
  rw [←Category.assoc,fr,id_comp]

include fr in
theorem inl_retractMap (n : ℕ) : left S n (n+1) (downRel n) ≫ (retractMap S r).f (n+1)=0 := by
  change _ ≫ (𝟙 _-(correction S r).f (n+1))=0
  rw [comp_sub,comp_id,inl_correction S r fr,sub_self]

theorem left_d_zero : left S 0 1 (downRel 0) ≫ (total S).d 1 0=S.f.f 0 ≫ right S 0 :=
  homotopyCofiber.inlX_d' S.f 1 0 (downRel 0) (by simp [ComplexShape.down_Rel])

theorem left_d_succ (n : ℕ) : left S (n+1) (n+2) (downRel (n+1)) ≫ (total S).d (n+2) (n+1)=
    -S.X₁.d (n+1) n ≫ left S n (n+1) (downRel n) + S.f.f (n+1) ≫ right S (n+1) :=
  homotopyCofiber.inlX_d S.f (n+2) (n+1) n (downRel (n+1)) (downRel n)

include fr in
theorem f_right_retract (n : ℕ) : S.f.f n ≫ right S n ≫ (retractMap S r).f n=0 := by
  have h := congrArg (fun m => left S n (n+1) (downRel n) ≫ m) ((retractMap S r).comm (n+1) n)
  rw [←Category.assoc,inl_retractMap S r fr,zero_comp] at h
  cases n with
  | zero =>
    change 0=left S 0 1 (downRel 0) ≫ (total S).d 1 0 ≫ (retractMap S r).f 0 at h
    rw [←Category.assoc,left_d_zero] at h
    exact (Category.assoc _ _ _).symm.trans h.symm
  | succ n =>
    rw [←Category.assoc,left_d_succ,add_comp] at h
    simp only [neg_comp,Category.assoc,inl_retractMap S r fr,comp_zero,neg_zero,zero_add] at h
    exact h.symm

variable (s : ∀ n, S.X₃.X n ⟶ S.X₂.X n)
  (gs : ∀ n, s n ≫ S.g.f n=𝟙 _)
  (split : ∀ n, r n ≫ S.f.f n + S.g.f n ≫ s n=𝟙 _)

/-- The inverse sends a quotient chain to its chosen lift corrected by the explicit cone contraction. -/
def inverseDegree (n : ℕ) : S.X₃.X n ⟶ (total S).X n := s n ≫ right S n ≫ (retractMap S r).f n

include fr split in
theorem g_inverseDegree (n : ℕ) : S.g.f n ≫ inverseDegree S r s n=right S n ≫ (retractMap S r).f n := by
  have h := congrArg (fun m => m ≫ right S n ≫ (retractMap S r).f n) (split n)
  simp only [add_comp,Category.assoc,f_right_retract S r fr,comp_zero,zero_add,id_comp] at h
  exact h

omit [HasBinaryBiproducts C] in
include gs in
theorem g_epi (n : ℕ) : Epi (S.g.f n) := epi_of_epi_fac (gs n)

include fr gs split in
/-- The corrected lift is an actual chain map, by the quotient epimorphism and chain commutation. -/
def inverse : S.X₃ ⟶ total S where
  f := inverseDegree S r s
  comm' i j _ := by
    have : Epi (S.g.f i) := g_epi S s gs i
    apply (cancel_epi (S.g.f i)).mp
    rw [←Category.assoc,g_inverseDegree S r fr s split]
    rw [Category.assoc,(retractMap S r).comm]
    have hr : right S i ≫ (total S).d i j=S.X₂.d i j ≫ right S j :=
      homotopyCofiber.inrX_d S.f i j
    rw [←Category.assoc,hr,Category.assoc,←g_inverseDegree S r fr s split,
      ←Category.assoc,←S.g.comm,Category.assoc]

include fr gs split in
theorem projection_inverse : projection S ≫ inverse S r fr s gs split=retractMap S r := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply homotopyCofiber.ext_from_X' S.f 0 (by simp [ComplexShape.down_Rel])
    change right S 0 ≫ ((projection S).f 0 ≫ inverseDegree S r s 0)=right S 0 ≫ (retractMap S r).f 0
    rw [←Category.assoc,right_projection_f,g_inverseDegree S r fr s split]
  | succ n =>
    apply homotopyCofiber.ext_from_X S.f n (n+1) (downRel n)
    · change left S n (n+1) (downRel n) ≫ ((projection S).f (n+1) ≫ inverseDegree S r s (n+1))=
        left S n (n+1) (downRel n) ≫ (retractMap S r).f (n+1)
      rw [←Category.assoc,left_projection_f,zero_comp,inl_retractMap S r fr]
    · change right S (n+1) ≫ ((projection S).f (n+1) ≫ inverseDegree S r s (n+1))=
        right S (n+1) ≫ (retractMap S r).f (n+1)
      rw [←Category.assoc,right_projection_f,g_inverseDegree S r fr s split]

include fr gs split in
theorem inverse_projection : inverse S r fr s gs split ≫ projection S=𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  have h : (retractMap S r).f n ≫ (projection S).f n=(projection S).f n :=
    congrArg (fun m => m.f n) (retractMap_projection S r)
  change (s n ≫ right S n ≫ (retractMap S r).f n) ≫ (projection S).f n=𝟙 _
  rw [Category.assoc,Category.assoc,h,right_projection_f,gs]

/-- The explicit cone correction is homotopic to the identity. -/
def retractHomotopy : Homotopy (retractMap S r) (𝟙 _) := by
  simpa only [retractMap,correction,sub_add_cancel,add_zero] using
    (Homotopy.refl (retractMap S r)).add (Homotopy.nullHomotopy' (contraction S r)).symm

/-- Every specified degreewise splitting yields a genuine cone-to-quotient homotopy equivalence. -/
def equivalence : _root_.HomotopyEquiv (total S) S.X₃ where
  hom := projection S
  inv := inverse S r fr s gs split
  homotopyHomInvId := (Homotopy.ofEq (projection_inverse S r fr s gs split)).trans (retractHomotopy S r)
  homotopyInvHomId := Homotopy.ofEq (inverse_projection S r fr s gs split)

end TernaryPoly.BoundaryFaceResolutionComparison.Cone
