module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Radical frames

A radical frame in `GL₃(ℚ)` is an abelian unipotent subgroup `u(ℚ²)` together with a Levi
subgroup `M` acting on it through integral matrices: `m u(r) m⁻¹ = u(A_m r)` with
`A_m ∈ GL₂(ℤ)`. For `N > 0` the level-`N` lattice of the frame is
`u(ℤ²) · {m | A_m ≡ 1 mod N}`; it is a subgroup of `GL₃(ℚ)`.

Written by AxiomCode.
-/

open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

/-- The general linear group in two variables. -/
abbrev GLTwo (R : Type*) [CommRing R] : Type _ := Matrix.GeneralLinearGroup (Fin 2) R

/-- The column action of an integral `2 × 2` matrix on `ℚ²`. -/
def leviAct (A : GLTwo ℤ) (r : ℚ × ℚ) : ℚ × ℚ :=
  (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ) * r.1 + ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℚ) * r.2,
    ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ) * r.1 + ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℚ) * r.2)

/-- The column action of an integral `2 × 2` matrix on `ℤ²`. -/
def intAct (A : GLTwo ℤ) (ℓ : ℤ × ℤ) : ℤ × ℤ :=
  ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * ℓ.1 + (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * ℓ.2,
    (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * ℓ.1 + (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * ℓ.2)

theorem leviAct_intCast (A : GLTwo ℤ) (ℓ : ℤ × ℤ) :
    leviAct A ((ℓ.1 : ℚ), (ℓ.2 : ℚ)) = (((intAct A ℓ).1 : ℚ), ((intAct A ℓ).2 : ℚ)) := by
  simp only [leviAct, intAct, Int.cast_add, Int.cast_mul]

/-- Reduction of integral matrices modulo `N`. -/
def reduction (N : ℕ) : GLTwo ℤ →* GLTwo (ZMod N) :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod N))

/-- An abelian unipotent radical with an integral Levi action. The Levi group is an abstract group
`Levi` mapping to `GL₃(ℚ)` by `leviHom`; it acts on the radical coordinates through the integral
matrices `leviMatrix`. -/
structure RadicalFrame where
  /-- The radical coordinates. -/
  radical : Multiplicative (ℚ × ℚ) →* RationalGL3
  radical_injective : Function.Injective radical
  /-- The Levi group. -/
  Levi : Type
  [leviGroup : Group Levi]
  /-- The Levi group inside `GL₃(ℚ)`. -/
  leviHom : Levi →* RationalGL3
  /-- The integral matrix of the Levi action on the radical. -/
  leviMatrix : Levi →* GLTwo ℤ
  conj : ∀ (m : Levi) (r : ℚ × ℚ),
    leviHom m * radical (Multiplicative.ofAdd r) * (leviHom m)⁻¹ =
      radical (Multiplicative.ofAdd (leviAct (leviMatrix m) r))
  disjoint : ∀ (m : Levi) (r : ℚ × ℚ), leviHom m = radical (Multiplicative.ofAdd r) → m = 1

attribute [instance] RadicalFrame.leviGroup

namespace RadicalFrame

variable (F : RadicalFrame)

/-- The integral points of the radical. -/
def integral (ℓ : ℤ × ℤ) : RationalGL3 :=
  F.radical (Multiplicative.ofAdd ((ℓ.1 : ℚ), (ℓ.2 : ℚ)))

theorem integral_zero : F.integral 0 = 1 := by
  have h : (((0 : ℤ × ℤ).1 : ℚ), ((0 : ℤ × ℤ).2 : ℚ)) = 0 := by ext <;> simp
  rw [integral, h, ofAdd_zero, map_one]

theorem integral_add (ℓ ℓ' : ℤ × ℤ) : F.integral (ℓ + ℓ') = F.integral ℓ * F.integral ℓ' := by
  have h : (((ℓ + ℓ').1 : ℚ), ((ℓ + ℓ').2 : ℚ)) =
      ((ℓ.1 : ℚ), (ℓ.2 : ℚ)) + ((ℓ'.1 : ℚ), (ℓ'.2 : ℚ)) := by ext <;> simp
  rw [integral, h, ofAdd_add, map_mul]
  rfl

theorem integral_neg (ℓ : ℤ × ℤ) : F.integral (-ℓ) = (F.integral ℓ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← integral_add, neg_add_cancel, integral_zero]

theorem levi_mul_integral (m : F.Levi) (ℓ : ℤ × ℤ) :
    F.leviHom m * F.integral ℓ = F.integral (intAct (F.leviMatrix m) ℓ) * F.leviHom m := by
  have h := F.conj m ((ℓ.1 : ℚ), (ℓ.2 : ℚ))
  rw [leviAct_intCast] at h
  rw [integral, integral, ← h]
  group

/-- The Levi elements with `A_m ≡ 1 mod N`. -/
def leviLevel (N : ℕ) : Subgroup F.Levi :=
  ((reduction N).comp F.leviMatrix).ker

/-- The level-`N` lattice `u(ℤ²) · {m | A_m ≡ 1 mod N}`. -/
def lattice (N : ℕ) : Subgroup RationalGL3 where
  carrier := {g | ∃ ℓ : ℤ × ℤ, ∃ m ∈ F.leviLevel N, g = F.integral ℓ * F.leviHom m}
  one_mem' := ⟨0, 1, (F.leviLevel N).one_mem, by simp [integral_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨ℓ, m, hm, rfl⟩ ⟨ℓ', m', hm', rfl⟩
    refine ⟨ℓ + intAct (F.leviMatrix m) ℓ', m * m', (F.leviLevel N).mul_mem hm hm', ?_⟩
    rw [F.integral_add, map_mul]
    calc F.integral ℓ * F.leviHom m * (F.integral ℓ' * F.leviHom m')
        = F.integral ℓ * (F.leviHom m * F.integral ℓ') * F.leviHom m' := by group
      _ = _ := by rw [F.levi_mul_integral]; group
  inv_mem' := by
    rintro _ ⟨ℓ, m, hm, rfl⟩
    refine ⟨intAct (F.leviMatrix m⁻¹) (-ℓ), m⁻¹, (F.leviLevel N).inv_mem hm, ?_⟩
    rw [← F.levi_mul_integral, F.integral_neg, map_inv]
    group

theorem integral_mem (N : ℕ) (ℓ : ℤ × ℤ) : F.integral ℓ ∈ F.lattice N :=
  ⟨ℓ, 1, (F.leviLevel N).one_mem, by simp⟩

theorem levi_mem (N : ℕ) (m : F.Levi) (hm : m ∈ F.leviLevel N) : F.leviHom m ∈ F.lattice N :=
  ⟨0, m, hm, by simp [integral_zero]⟩

theorem lattice_mono {N N' : ℕ} (h : N ∣ N') : F.lattice N' ≤ F.lattice N := by
  rintro _ ⟨ℓ, m, hm, rfl⟩
  refine ⟨ℓ, m, ?_, rfl⟩
  change (reduction N) (F.leviMatrix m) = 1
  have hm' : (reduction N') (F.leviMatrix m) = 1 := hm
  have hcomp : (ZMod.castHom h (ZMod N)).comp (Int.castRingHom (ZMod N')) =
      Int.castRingHom (ZMod N) := RingHom.ext_int _ _
  have key : (Matrix.GeneralLinearGroup.map (ZMod.castHom h (ZMod N))) ((reduction N')
      (F.leviMatrix m)) = (reduction N) (F.leviMatrix m) := by
    apply Units.ext
    ext i j
    simp only [reduction, Matrix.GeneralLinearGroup.map_apply]
    exact RingHom.congr_fun hcomp
      (((F.leviMatrix m : GLTwo ℤ) : Matrix (Fin 2) (Fin 2) ℤ) i j)
  rw [← key, hm', map_one]

end RadicalFrame

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
