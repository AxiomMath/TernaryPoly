module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Degrees

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap.Descent
open CategoryTheory Homology

variable (C : CochainComplex (ModuleCat.{0} ℚ) ℕ)
  (K L : ChainComplex (ModuleCat.{0} ℚ) ℕ)

/-- The canonical scalar-chain degree relabelling in a cap identity. -/
def castLeft (a b : ℕ) : K.X (a+b+1) ≅ K.X (a+1+b) :=
  K.XIsoOfEq (by omega)

/-- Cycle vanishing remains valid with any equal outgoing degree. -/
theorem cycle_at (n m : ℕ) (h : n-1 = m) (c : Cycles (K.sc' (n+1) n (n-1))) :
    K.d n m c.val = 0 := by
  have hh : K.d n (n-1) c.val = 0 := c.property
  have hd := congrArg (fun f => f c.val) (K.d_comp_XIsoOfEq_hom h n)
  rw [← hd]
  change (K.XIsoOfEq h).hom (K.d n (n-1) c.val) = 0
  rw [hh,map_zero]

/-- A proved signed Leibniz identity is the algebraic input for homology descent. -/
def Leibniz (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b) : Prop :=
  ∀ a b x c, β a b x (K.d (a+b+1) (a+b) c) =
    β (a+1) b (C.d a (a+1) x) ((castLeft K a b).hom c) +
      (-1 : ℤ)^a • L.d (b+1) b (β a (b+1) x c)

variable (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b)
  (hβ : Leibniz C K L β)
include hβ

/-- A concrete Leibniz operation sends cycles to cycles. -/
theorem cycles (a b : ℕ) (x : Cycles (C.sc' (a-1) a (a+1)))
    (c : Cycles (K.sc' (a+b+1) (a+b) (a+b-1))) :
    L.d b (b-1) (β a b x.val c.val) = 0 := by
  cases b with
  | zero => rw [L.shape _ _ (by simp)]; rfl
  | succ b =>
    have hx : C.d a (a+1) x.val = 0 := x.property
    have h := hβ a b x.val c.val
    erw [cycle_at K (a+b+1) (a+b) (by omega) c, map_zero, hx, map_zero, LinearMap.zero_apply, zero_add] at h
    have hs : (-1 : ℤ)^a * (-1 : ℤ)^a = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have hh := congrArg (fun z => (-1 : ℤ)^a • z) h
    simp only [smul_zero,smul_smul,hs,one_zsmul] at hh
    exact hh.symm

/-- An actual scalar boundary has an explicit local primitive. -/
theorem chain_boundary (a b : ℕ) (x : Cycles (C.sc' (a-1) a (a+1)))
    (c : K.X (a+b+1)) :
    ∃ u : L.X (b+1), L.d (b+1) b u = β a b x.val (K.d (a+b+1) (a+b) c) := by
  refine ⟨(-1 : ℤ)^a • β a (b+1) x.val c, ?_⟩
  have hx : C.d a (a+1) x.val = 0 := x.property
  erw [map_zsmul,hβ a b x.val c,hx,map_zero,LinearMap.zero_apply,zero_add]

/-- An actual cochain boundary has an explicit local primitive, also in degree zero. -/
theorem cochain_boundary (a b : ℕ) (x : C.X (a-1))
    (c : Cycles (K.sc' (a+b+1) (a+b) (a+b-1))) :
    ∃ u : L.X (b+1), L.d (b+1) b u = β a b (C.d (a-1) a x) c.val := by
  cases a with
  | zero =>
    refine ⟨0, ?_⟩
    rw [C.shape 0 0 (by simp),map_zero]
    change 0 = β 0 b 0 c.val
    rw [map_zero]
    rfl
  | succ a =>
    let c' := (castLeft K a b).inv c.val
    have hc : K.d (a+b+1) (a+b) c' = 0 := by
      have hd := congrArg (fun g => g c.val) (K.XIsoOfEq_inv_comp_d (show a+b+1 = a+1+b by omega) (a+b))
      change K.d (a+b+1) (a+b) c' = K.d (a+1+b) (a+b) c.val at hd
      rw [hd]
      exact cycle_at K _ _ (by omega) c
    have h := hβ a b x c'
    have he : (castLeft K a b).hom c' = c.val :=
      congrArg (fun g => g c.val) (castLeft K a b).inv_hom_id
    rw [hc,map_zero,he] at h
    refine ⟨-((-1 : ℤ)^a • β a (b+1) x c'), ?_⟩
    rw [map_neg,map_zsmul]
    exact (eq_neg_iff_add_eq_zero.mpr h.symm).symm

/-- Homology descent of a concrete signed Leibniz operation through both actual boundary quotients. -/
def homologySC (a b : ℕ) : (C.sc' (a-1) a (a+1)).homology →ₗ[ℚ]
    (K.sc' (a+b+1) (a+b) (a+b-1)).homology →ₗ[ℚ] (L.sc' (b+1) b (b-1)).homology :=
  induced _ _ _ (β a b) (cycles C K L β hβ a b)
    (cochain_boundary C K L β hβ a b) (chain_boundary C K L β hβ a b)

/-- The actual homology operation associated with a proved concrete signed cap identity. -/
def homology (a b : ℕ) : C.homology a →ₗ[ℚ] K.homology (a+b) →ₗ[ℚ] L.homology b :=
  (((homologySC C K L β hβ a b).compl₂
      (K.homologyIsoSc' (a+b+1) (a+b) (a+b-1) (down_prev _) (down_next _)).hom.hom).comp
      (C.homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).hom.hom).compr₂
      (L.homologyIsoSc' (b+1) b (b-1) (down_prev _) (down_next _)).inv.hom

end TernaryPoly.SingularLocalCap.Descent
