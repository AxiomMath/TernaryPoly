module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH2

@[expose] public section


/-!
# The good-plane stabilizer as a split extension `ℤ² ⋊ (Γ₁'(3) × ℤˣ)`

In the block coordinates of `GoodPlaneFrame` the stabilizer `Λ = ΛG` of the good plane consists of
the elements `Pg b m d = P(b, κ(m), d)` (`b ∈ ℤ²`, `m ∈ Γ₁'(3)`, `d ∈ ℤˣ`), and
`Pg b m d · Pg b' m' d' = Pg (b + d κ(m) b') (m m') (d d')` (`Pg_mul`). The coordinates are unique
(`Pg_injective`), so `Λ` is a split extension of the Levi group `Γ₁'(3) × ℤˣ` by the radical
lattice `ℤ²` (`goodPlaneExtension`, `goodPlaneSplitting`), the form to which Sol's Hochschild–Serre
edge machinery applies. The coefficient representation restricts on the radical to exactly Sol's
`upperRadicalLatticeRep` (`coefRep_radical`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneModel

open TernaryPeriodPolynomials.Spectral
open PlaneCoordinates LevelOneCosets IdentityPlaneCosets
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame

/-- The Levi group `Γ₁'(3) × ℤˣ` of the good plane. -/
abbrev Levi : Type := binaryArithmeticLevel × ℤˣ

/-- The integral vector `d · κ(m) · b`. -/
def act (m : binaryArithmeticLevel) (d : ℤˣ) (b : ℤ × ℤ) : ℤ × ℤ :=
  (d : ℤ) • imul (kap m).val b

theorem act_zero (m : binaryArithmeticLevel) (d : ℤˣ) : act m d 0 = 0 := by
  simp [act, imul]

theorem act_one (d : ℤˣ) (b : ℤ × ℤ) : act 1 d b = (d : ℤ) • b := by
  simp only [act, map_one, Units.val_one, imul_one]

theorem uq_mul (d d' : ℤˣ) : uq (d * d') = uq d * uq d' :=
  map_mul (Units.map (Int.castRingHom ℚ : ℤ →* ℚ)) d d'

theorem uq_one : uq 1 = 1 := map_one (Units.map (Int.castRingHom ℚ : ℤ →* ℚ))

theorem uq_injective : Function.Injective uq := by
  intro d d' h
  have h' : ((d : ℤ) : ℚ) = ((d' : ℤ) : ℚ) := congrArg (fun u : ℚˣ => (u : ℚ)) h
  apply Units.ext
  exact_mod_cast h'

theorem Pg_mul (b b' : ℤ × ℤ) (m m' : binaryArithmeticLevel) (d d' : ℤˣ) :
    Pg b m d * Pg b' m' d' = Pg (b + act m d b') (m * m') (d * d') := by
  unfold Pg
  rw [P_mul]
  congr 1
  · rw [uq_inv, bmul_integralEmbed, icast_add, act, ← icast_smul_int]
  · rw [map_mul, map_mul]
  · rw [uq_mul]

theorem Pg_zero_one_one : Pg 0 1 1 = 1 := by
  unfold Pg
  rw [uq_one, map_one, map_one, icast_zero]
  exact P_one

theorem Pg_injective {b b' : ℤ × ℤ} {m m' : binaryArithmeticLevel} {d d' : ℤˣ}
    (h : Pg b m d = Pg b' m' d') : b = b' ∧ m = m' ∧ d = d' := by
  obtain ⟨h1, h2, h3⟩ := P_injective h
  exact ⟨icast_injective h1, kap_injective (integralEmbed_injective h2), uq_injective h3⟩

/-- The element `Pg b m d` of `Λ`. -/
def Gel (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) : ΛG := ⟨Pg b m d, Pg_mem b m d⟩

theorem Gel_val (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) : (Gel b m d).val = Pg b m d := rfl

theorem Gel_mul (b b' : ℤ × ℤ) (m m' : binaryArithmeticLevel) (d d' : ℤˣ) :
    Gel b m d * Gel b' m' d' = Gel (b + act m d b') (m * m') (d * d') :=
  Subtype.ext (Pg_mul b b' m m' d d')

theorem Gel_one : Gel 0 1 1 = 1 := Subtype.ext Pg_zero_one_one

theorem Gel_injective {b b' : ℤ × ℤ} {m m' : binaryArithmeticLevel} {d d' : ℤˣ}
    (h : Gel b m d = Gel b' m' d') : b = b' ∧ m = m' ∧ d = d' :=
  Pg_injective (congrArg Subtype.val h)

theorem Gel_surjective (h : ΛG) : ∃ b m d, h = Gel b m d := by
  obtain ⟨b, m, d, e⟩ := (mem_ΛG_iff h.val).mp h.property
  exact ⟨b, m, d, Subtype.ext e⟩

/-! ### The subgroup `d = 1` and its standard elements -/

/-- The Levi embedding `m ↦ κ(m) = δ⁻¹ m δ ∈ GL₂(ℚ)`. -/
def Em : binaryArithmeticLevel →* GL (Fin 2) ℚ := integralEmbed.comp kap

theorem Em_apply (m : binaryArithmeticLevel) : Em m = integralEmbed (kap m) := rfl

/-- The elements `P(b, κ(m), 1)` of `Λ`, in the shape used by the identity-plane pipeline. -/
def PK (b : ℤ × ℤ) (m : binaryArithmeticLevel) : RationalGL3 := P (icast b) (Em m) 1

theorem PK_eq_Pg (b : ℤ × ℤ) (m : binaryArithmeticLevel) : PK b m = Pg b m 1 := by
  simp only [PK, Pg, Em_apply, uq_one]

theorem PK_mem (b : ℤ × ℤ) (m : binaryArithmeticLevel) : PK b m ∈ ΛG := by
  rw [PK_eq_Pg]
  exact Pg_mem _ _ _

/-- The radical element `u(b)` of `Λ`. -/
def UK (b : ℤ × ℤ) : ΛG := ⟨PK b 1, PK_mem b 1⟩

/-- The Levi element `diag(κ(m), 1)` of `Λ`. -/
def LK (m : binaryArithmeticLevel) : ΛG := ⟨PK 0 m, PK_mem 0 m⟩

/-- The mixed element `u(b) diag(κ(m), 1)` of `Λ`. -/
def MK (b : ℤ × ℤ) (m : binaryArithmeticLevel) : ΛG := ⟨PK b m, PK_mem b m⟩

/-- The element `diag(1, 1, -1)` of `Λ`. -/
def DK : ΛG := Gel 0 1 (-1)

theorem MK_eq_Gel (b : ℤ × ℤ) (m : binaryArithmeticLevel) : MK b m = Gel b m 1 :=
  Subtype.ext (PK_eq_Pg b m)

/-! ### The extension -/

/-- The Levi component of an element of `Λ` (chosen decomposition). -/
def projFun (h : ΛG) : Levi :=
  ((Gel_surjective h).choose_spec.choose, (Gel_surjective h).choose_spec.choose_spec.choose)

theorem projFun_Gel (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) :
    projFun (Gel b m d) = (m, d) := by
  have hs := (Gel_surjective (Gel b m d)).choose_spec.choose_spec.choose_spec
  obtain ⟨-, h2, h3⟩ := Gel_injective hs.symm
  exact Prod.ext h2 h3

/-- The projection `Λ → Γ₁'(3) × ℤˣ`. -/
def proj : ΛG →* Levi where
  toFun := projFun
  map_one' := by
    have h := projFun_Gel 0 1 1
    rw [Gel_one] at h
    exact h
  map_mul' h h' := by
    obtain ⟨b, m, d, rfl⟩ := Gel_surjective h
    obtain ⟨b', m', d', rfl⟩ := Gel_surjective h'
    calc projFun (Gel b m d * Gel b' m' d')
        = projFun (Gel (b + act m d b') (m * m') (d * d')) := by rw [Gel_mul]
      _ = (m, d) * (m', d') := projFun_Gel _ _ _
      _ = projFun (Gel b m d) * projFun (Gel b' m' d') := by rw [projFun_Gel, projFun_Gel]

theorem proj_Gel (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) : proj (Gel b m d) = (m, d) :=
  projFun_Gel b m d

theorem upperRadicalLattice_eq (b : RadicalLattice) :
    upperRadicalLattice b = Pg b.toAdd 1 1 := by
  have e : Pg b.toAdd 1 1 = P (icast b.toAdd) 1 1 := by
    unfold Pg
    rw [uq_one, map_one, map_one]
  rw [e]
  apply Units.ext
  rw [P_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperRadicalLattice, planeUnipotent, icast]

theorem upperRadicalLattice_mem (b : RadicalLattice) : upperRadicalLattice b ∈ ΛG := by
  rw [upperRadicalLattice_eq]
  exact Pg_mem _ _ _

/-- The radical inclusion `ℤ² → Λ`. -/
def radInc : RadicalLattice →* ΛG := upperRadicalLattice.codRestrict ΛG upperRadicalLattice_mem

theorem radInc_eq (b : RadicalLattice) : radInc b = Gel b.toAdd 1 1 :=
  Subtype.ext (upperRadicalLattice_eq b)

/-- The Levi section `(m, d) ↦ Pg 0 m d`. -/
def secL : Levi →* ΛG where
  toFun ℓ := Gel 0 ℓ.1 ℓ.2
  map_one' := Gel_one
  map_mul' ℓ ℓ' := by
    rw [Gel_mul, act_zero, zero_add]
    rfl

theorem secL_apply (m : binaryArithmeticLevel) (d : ℤˣ) : secL (m, d) = Gel 0 m d := rfl

theorem proj_secL (ℓ : Levi) : proj (secL ℓ) = ℓ := proj_Gel 0 ℓ.1 ℓ.2

theorem radInc_injective : Function.Injective radInc := by
  intro b b' h
  exact upperRadicalLattice_injective (congrArg Subtype.val h)

theorem range_radInc : radInc.range = proj.ker := by
  ext h
  constructor
  · rintro ⟨b, rfl⟩
    rw [radInc_eq, MonoidHom.mem_ker, proj_Gel]
    rfl
  · intro hk
    obtain ⟨b, m, d, rfl⟩ := Gel_surjective h
    rw [MonoidHom.mem_ker, proj_Gel] at hk
    have hm : m = 1 := congrArg Prod.fst hk
    have hd : d = 1 := congrArg Prod.snd hk
    subst hm hd
    exact ⟨Multiplicative.ofAdd b, radInc_eq _⟩

/-- **The good-plane stabilizer as a group extension** `1 → ℤ² → Λ → Γ₁'(3) × ℤˣ → 1`. -/
def goodPlaneExtension : GroupExtension RadicalLattice ΛG Levi :=
  ⟨radInc, proj, radInc_injective, range_radInc, fun ℓ => ⟨secL ℓ, proj_secL ℓ⟩⟩

/-- **The Levi splitting.** -/
def goodPlaneSplitting : goodPlaneExtension.Splitting := ⟨secL, proj_secL⟩

/-! ### Coefficients and the conjugation action -/

variable (n : ℕ)

/-- The coefficient representation of `Λ`. -/
abbrev coefRep : Rep ℂ ΛG :=
  subgroupCoefficientRep ΛG (rationalCoefficientComponent n trivialCharacter)

theorem coefRep_radical :
    Rep.res goodPlaneExtension.inl (coefRep n) = upperRadicalLatticeRep n := rfl

theorem secL_eq (ℓ : Levi) : secL ℓ = Gel 0 ℓ.1 ℓ.2 := rfl

theorem conjAct_apply (ℓ : Levi) (b : RadicalLattice) :
    goodPlaneSplitting.conjAct ℓ b =
      Multiplicative.ofAdd (act ℓ.1 ℓ.2 b.toAdd) := by
  apply radInc_injective
  have h := goodPlaneExtension.inl_conjAct_comm (e := secL ℓ) (n := b)
  change radInc (goodPlaneSplitting.conjAct ℓ b) = secL ℓ * radInc b * (secL ℓ)⁻¹ at h
  rw [h, radInc_eq b, radInc_eq (Multiplicative.ofAdd _), mul_inv_eq_iff_eq_mul, secL_eq,
    Gel_mul, Gel_mul]
  simp only [toAdd_ofAdd]
  congr 1
  · rw [act_zero, zero_add, add_zero]
  · simp
  · simp

end TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
