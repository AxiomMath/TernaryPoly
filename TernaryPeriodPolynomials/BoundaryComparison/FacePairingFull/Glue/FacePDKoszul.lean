module

public import Mathlib

@[expose] public section


/-!
# The two-generator Koszul pairing of the radical (torus-fibre Poincare duality)

Formalized by Claude Sonnet 5.5.

For a rank-two abelian group `U = ⟨s₁, s₂⟩ ≅ ℤ²` acting on a finite-dimensional space `E` (generators `s₁, s₂`) and on `E'`
(generators `t₁, t₂`), with an invariant perfect pairing `e : E × E' → ℂ` (`e (s_i v) (t_i w) = e v w`, e.g. a representation
and its dual), the Koszul complex `E → E² → E` computes `H¹(U, E)` (`Z1 / B1`), and the cup product of one-cocycles
evaluated on the fundamental class `[s₁|s₂] - [s₂|s₁]` of the torus is

`Phi ((p₁, p₂), (q₁, q₂)) = e p₁ (t₁ q₂) - e p₂ (t₂ q₁)`.

`pairing : H¹(U, E) × H¹(U, E') → ℂ` is well defined (`Phi_d0`, `Phi_d0'`) and **perfect in both arguments**
(`pairing_left_nondegenerate`, `pairing_right_nondegenerate`).  The proof is the duality of the Koszul complex
with its dual: `Phi` is a perfect pairing of the 1-cochains, `d0` is adjoint to `d1'` (`Phi_d0`) and `d1` to `d0'`
(`Phi_d0'`), hence the annihilator of the cocycles is the space of coboundaries (`left_annihilator`, `right_annihilator`).
-/

open Module

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD

namespace Koszul

structure KData (E E' : Type*) [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E'] where
  s₁ : E ≃ₗ[ℂ] E
  s₂ : E ≃ₗ[ℂ] E
  t₁ : E' ≃ₗ[ℂ] E'
  t₂ : E' ≃ₗ[ℂ] E'
  e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ
  comm : ∀ v, s₁ (s₂ v) = s₂ (s₁ v)
  comm' : ∀ w, t₁ (t₂ w) = t₂ (t₁ w)
  inv₁ : ∀ v w, e (s₁ v) (t₁ w) = e v w
  inv₂ : ∀ v w, e (s₂ v) (t₂ w) = e v w
  left : ∀ v, (∀ w, e v w = 0) → v = 0
  right : ∀ w, (∀ v, e v w = 0) → w = 0

variable {E E' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  (K : KData E E')

namespace KData

def d0 : E →ₗ[ℂ] E × E where
  toFun x := (K.s₁ x - x, K.s₂ x - x)
  map_add' x y := by ext <;> simp <;> abel
  map_smul' c x := by ext <;> simp [smul_sub]

def d1 : E × E →ₗ[ℂ] E where
  toFun p := (K.s₂ p.1 - p.1) - (K.s₁ p.2 - p.2)
  map_add' x y := by simp; abel
  map_smul' c x := by simp [smul_sub]

def d0' : E' →ₗ[ℂ] E' × E' where
  toFun x := (K.t₁ x - x, K.t₂ x - x)
  map_add' x y := by ext <;> simp <;> abel
  map_smul' c x := by ext <;> simp [smul_sub]

def d1' : E' × E' →ₗ[ℂ] E' where
  toFun p := (K.t₂ p.1 - p.1) - (K.t₁ p.2 - p.2)
  map_add' x y := by simp; abel
  map_smul' c x := by simp [smul_sub]

theorem d0_apply (x : E) : K.d0 x = (K.s₁ x - x, K.s₂ x - x) := rfl
theorem d1_apply (p : E × E) : K.d1 p = (K.s₂ p.1 - p.1) - (K.s₁ p.2 - p.2) := rfl
theorem d0'_apply (x : E') : K.d0' x = (K.t₁ x - x, K.t₂ x - x) := rfl
theorem d1'_apply (p : E' × E') : K.d1' p = (K.t₂ p.1 - p.1) - (K.t₁ p.2 - p.2) := rfl

/-- The Koszul (cup) pairing on 1-cochains: `⟨p₁, t₁ q₂⟩ - ⟨p₂, t₂ q₁⟩`. -/
def Phi : (E × E) →ₗ[ℂ] (E' × E') →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun p q => K.e p.1 (K.t₁ q.2) - K.e p.2 (K.t₂ q.1))
    (fun p p' q => by simp [sub_add_sub_comm])
    (fun c p q => by simp [mul_sub])
    (fun p q q' => by simp [sub_add_sub_comm])
    (fun c p q => by simp [mul_sub])

theorem Phi_apply (p : E × E) (q : E' × E') :
    K.Phi p q = K.e p.1 (K.t₁ q.2) - K.e p.2 (K.t₂ q.1) := rfl

theorem Phi_d0 (x : E) (q : E' × E') : K.Phi (K.d0 x) q = K.e x (K.d1' q) := by
  rw [Phi_apply, d0_apply, d1'_apply]
  simp only [map_sub, LinearMap.sub_apply, K.inv₁, K.inv₂]
  abel

theorem Phi_d0' (p : E × E) (y : E') :
    K.Phi p (K.d0' y) = - K.e (K.d1 p) (K.t₁ (K.t₂ y)) := by
  rw [Phi_apply, d0'_apply, d1_apply]
  simp only [map_sub, LinearMap.sub_apply]
  have a1 : K.e (K.s₂ p.1) (K.t₁ (K.t₂ y)) = K.e p.1 (K.t₁ y) := by
    rw [K.comm' y]; exact K.inv₂ _ _
  have a2 : K.e (K.s₁ p.2) (K.t₁ (K.t₂ y)) = K.e p.2 (K.t₂ y) := K.inv₁ _ _
  have a3 : K.t₂ (K.t₁ y) = K.t₁ (K.t₂ y) := (K.comm' y).symm
  simp only [a1, a2, a3]
  abel

theorem d1_d0 (x : E) : K.d1 (K.d0 x) = 0 := by
  rw [d0_apply, d1_apply]
  simp only [map_sub, K.comm x]
  abel

theorem d1'_d0' (x : E') : K.d1' (K.d0' x) = 0 := by
  rw [d0'_apply, d1'_apply]
  simp only [map_sub, K.comm' x]
  abel

theorem Phi_left_zero (p : E × E) (h : ∀ q, K.Phi p q = 0) : p = 0 := by
  have h1 : p.1 = 0 := K.left _ (fun w => by
    have := h (0, K.t₁.symm w)
    simpa [Phi_apply] using this)
  have h2 : p.2 = 0 := K.left _ (fun w => by
    have := h (K.t₂.symm w, 0)
    simpa [Phi_apply] using this)
  exact Prod.ext h1 h2

theorem Phi_right_zero (q : E' × E') (h : ∀ p, K.Phi p q = 0) : q = 0 := by
  have h1 : q.2 = 0 := by
    have : K.t₁ q.2 = 0 := K.right _ (fun v => by simpa [Phi_apply] using h (v, 0))
    simpa using this
  have h2 : q.1 = 0 := by
    have : K.t₂ q.1 = 0 := K.right _ (fun v => by simpa [Phi_apply] using h (0, v))
    simpa using this
  exact Prod.ext h2 h1

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']

theorem exists_left_rep (μ : Module.Dual ℂ E') : ∃ x : E, ∀ w, μ w = K.e x w := by
  have hinj : Function.Injective K.e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact K.left v (fun w => by simpa using congrArg (fun f => f w) hv)
  have hinj' : Function.Injective K.e.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact K.right w (fun v => by simpa using congrArg (fun f => f v) hw)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := LinearMap.finrank_le_finrank_of_injective hinj'
  rw [Subspace.dual_finrank_eq] at h1 h2
  have heq : Module.finrank ℂ E = Module.finrank ℂ (Module.Dual ℂ E') := by
    rw [Subspace.dual_finrank_eq]; exact le_antisymm h1 h2
  have hsurj : Function.Surjective K.e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj
  obtain ⟨x, hx⟩ := hsurj μ
  exact ⟨x, fun w => by rw [← hx]⟩

theorem exists_right_rep (μ : Module.Dual ℂ E) : ∃ y : E', ∀ v, μ v = K.e v y := by
  have hinj : Function.Injective K.e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact K.left v (fun w => by simpa using congrArg (fun f => f w) hv)
  have hinj' : Function.Injective K.e.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact K.right w (fun v => by simpa using congrArg (fun f => f v) hw)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := LinearMap.finrank_le_finrank_of_injective hinj'
  rw [Subspace.dual_finrank_eq] at h1 h2
  have heq : Module.finrank ℂ E' = Module.finrank ℂ (Module.Dual ℂ E) := by
    rw [Subspace.dual_finrank_eq]; exact le_antisymm h2 h1
  have hsurj : Function.Surjective K.e.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj'
  obtain ⟨y, hy⟩ := hsurj μ
  exact ⟨y, fun v => by rw [← hy]; rfl⟩

theorem exists_factor {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (d : V →ₗ[ℂ] U) (f : V →ₗ[ℂ] ℂ) (h : ∀ v, d v = 0 → f v = 0) :
    ∃ l : Module.Dual ℂ U, ∀ v, f v = l (d v) := by
  have hf : f ∈ (LinearMap.ker d).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    exact h v hv
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hf
  obtain ⟨l, hl⟩ := hf
  exact ⟨l, fun v => by rw [← hl]; rfl⟩

/-- Left kernel: a 1-cochain orthogonal to all cocycles of the dual is a coboundary. -/
theorem left_annihilator (p : E × E) (h : ∀ q, K.d1' q = 0 → K.Phi p q = 0) : ∃ x, p = K.d0 x := by
  obtain ⟨l, hl⟩ := exists_factor K.d1' (K.Phi p) h
  obtain ⟨x, hx⟩ := K.exists_left_rep l
  refine ⟨x, ?_⟩
  have : p - K.d0 x = 0 := Phi_left_zero K _ (fun q => by
    rw [map_sub, LinearMap.sub_apply, Phi_d0, hl q, hx]; ring)
  exact sub_eq_zero.1 this

/-- Right kernel: a 1-cochain of the dual orthogonal to all cocycles is a coboundary. -/
theorem right_annihilator (q : E' × E') (h : ∀ p, K.d1 p = 0 → K.Phi p q = 0) : ∃ y, q = K.d0' y := by
  obtain ⟨l, hl⟩ := exists_factor K.d1 (K.Phi.flip q) h
  obtain ⟨y, hy⟩ := K.exists_right_rep l
  refine ⟨K.t₂.symm (K.t₁.symm (-y)), ?_⟩
  symm
  refine sub_eq_zero.1 (Phi_right_zero K _ (fun p => ?_))
  have h1 : K.Phi p q = K.e (K.d1 p) y := by
    have := hl p
    rw [LinearMap.flip_apply] at this
    rw [this, hy]
  rw [map_sub, Phi_d0', h1]
  simp

/-- The cocycles `Z¹` of the Koszul complex of `E`. -/
def Z1 : Submodule ℂ (E × E) := LinearMap.ker K.d1

def Z1' : Submodule ℂ (E' × E') := LinearMap.ker K.d1'

/-- The coboundary map into the cocycles. -/
def d0Z : E →ₗ[ℂ] K.Z1 := K.d0.codRestrict K.Z1 (fun x => K.d1_d0 x)

def d0Z' : E' →ₗ[ℂ] K.Z1' := K.d0'.codRestrict K.Z1' (fun x => K.d1'_d0' x)

/-- `H¹(ℤ², E)`, computed by the two-generator Koszul complex. -/
abbrev H1 := K.Z1 ⧸ LinearMap.range K.d0Z

abbrev H1' := K.Z1' ⧸ LinearMap.range K.d0Z'

/-- The Koszul pairing on cocycles. -/
def P0 : K.Z1 →ₗ[ℂ] K.Z1' →ₗ[ℂ] ℂ :=
  K.Phi.compl₁₂ K.Z1.subtype K.Z1'.subtype

/-- **The Koszul pairing** `H¹(ℤ², E) × H¹(ℤ², E') → ℂ` (cup product into `H²(ℤ², ℂ) = ℂ`, the orientation line). -/
def pairing : K.H1 →ₗ[ℂ] K.H1' →ₗ[ℂ] ℂ :=
  Submodule.liftQ (LinearMap.range K.d0Z)
    { toFun := fun z => Submodule.liftQ (LinearMap.range K.d0Z') (K.P0 z) (by
        rintro _ ⟨y, rfl⟩
        change K.Phi (z : E × E) (K.d0' y) = 0
        rw [Phi_d0', show K.d1 (z : E × E) = 0 from z.2]
        simp)
      map_add' := fun z z' => by
        ext w
        simp
      map_smul' := fun c z => by
        ext w
        simp }
    (by
      rintro _ ⟨x, rfl⟩
      ext w
      change K.Phi (K.d0 x) (w : E' × E') = 0
      rw [Phi_d0, show K.d1' (w : E' × E') = 0 from w.2]
      simp)

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] in
theorem pairing_mk (z : K.Z1) (z' : K.Z1') :
    K.pairing (Submodule.Quotient.mk z) (Submodule.Quotient.mk z') = K.Phi z z' := rfl

/-- **Perfectness of the Koszul pairing (left).** -/
theorem pairing_left_nondegenerate (a : K.H1) (h : ∀ b : K.H1', K.pairing a b = 0) : a = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  rw [Submodule.Quotient.mk_eq_zero]
  obtain ⟨x, hx⟩ := left_annihilator K (z : E × E) (fun q hq => by
    have := h (Submodule.Quotient.mk ⟨q, hq⟩)
    rwa [pairing_mk] at this)
  exact ⟨x, Subtype.ext hx.symm⟩

/-- **Perfectness of the Koszul pairing (right).** -/
theorem pairing_right_nondegenerate (b : K.H1') (h : ∀ a : K.H1, K.pairing a b = 0) : b = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.Quotient.mk_eq_zero]
  obtain ⟨y, hy⟩ := right_annihilator K (z : E' × E') (fun p hp => by
    have := h (Submodule.Quotient.mk ⟨p, hp⟩)
    rwa [pairing_mk] at this)
  exact ⟨y, Subtype.ext hy.symm⟩

end KData

end Koszul

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD
