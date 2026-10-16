module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Frame
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.IntegralFlags
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.UnitriangularConj

@[expose] public section


/-!
# Explicit radical frames of the rational maximal-parabolic flags

Every rational flag `x` is `QuotientGroup.mk (g : GL₃(ℚ))` for an integral `g ∈ GL₃(ℤ)`
(`exists_integral_representative`). For such `g` the frames `planeFrame g`, `lineFrame g` are the
radical frames with radical `u_g(r) = g u(3 r) g⁻¹` and Levi group `GL₂(ℤ)` embedded as
`g diag(B, 1) g⁻¹` (plane) resp. `g diag(1, B) g⁻¹` (line); on the line side the Levi element `B`
acts on the radical coordinates through the inverse transpose `(B⁻¹)ᵀ`.

For every level `3 K` (`K ≥ 1`) the lattice of the frame lies in `Γ ⊓ Stab(x)` with finite
relative index, and the radical consists of conjugates of upper unitriangular matrices.

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

namespace FlagFrames

/-! ### Generic group-theoretic helpers -/

theorem conj_mul_eq {G : Type*} [Group G] (a R M : G) :
    a * (R * M) * a⁻¹ = a * R * a⁻¹ * (a * M * a⁻¹) := by group

theorem inv_conj_conj {G : Type*} [Group G] (a X : G) : a⁻¹ * (a * X * a⁻¹) * a = X := by group

theorem conj_quot_eq {G : Type*} [Group G] (a R' M' R M : G) :
    a * (R' * M') * a⁻¹ * (a * (R * M) * a⁻¹)⁻¹ =
      a * R' * a⁻¹ * (a * (M' * M⁻¹) * a⁻¹) * (a * R * a⁻¹)⁻¹ := by group

/-- Conjugation by `a` as a monoid endomorphism of `GL₃(ℚ)`. -/
def conjHom (a : RationalGL3) : RationalGL3 →* RationalGL3 where
  toFun h := a * h * a⁻¹
  map_one' := by
    show a * 1 * a⁻¹ = 1
    simp
  map_mul' h k := by
    show a * (h * k) * a⁻¹ = a * h * a⁻¹ * (a * k * a⁻¹)
    group

theorem conjHom_apply (a h : RationalGL3) : conjHom a h = a * h * a⁻¹ := rfl

theorem conjHom_injective (a : RationalGL3) : Function.Injective (conjHom a) := by
  intro h k hk
  have h' : a * h * a⁻¹ = a * k * a⁻¹ := hk
  exact mul_left_cancel (mul_right_cancel h')

theorem finite_gl (n N : ℕ) [NeZero N] : Finite (Matrix.GeneralLinearGroup (Fin n) (ZMod N)) :=
  Finite.of_injective
    (fun u : Matrix.GeneralLinearGroup (Fin n) (ZMod N) =>
      (fun i j => u.val i j : Fin n → Fin n → ZMod N))
    (fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))

/-- A subgroup has finitely many right cosets as soon as a map to a finite type separates them. -/
theorem finite_quotient_of_fibers {G : Type*} [Group G] (H : Subgroup G) {T : Type*} [Finite T]
    (F : G → T) (hF : ∀ a b, F a = F b → b * a⁻¹ ∈ H) :
    Finite (Quotient (QuotientGroup.rightRel H)) := by
  classical
  refine Finite.of_surjective
    (fun t : T => if h : ∃ a, F a = t then
      (Quotient.mk (QuotientGroup.rightRel H) (Classical.choose h) :
        Quotient (QuotientGroup.rightRel H))
      else Quotient.mk (QuotientGroup.rightRel H) 1) ?_
  intro q
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  have h : ∃ a', F a' = F a := ⟨a, rfl⟩
  refine ⟨F a, ?_⟩
  have hg : (if h' : ∃ a', F a' = F a then
      (Quotient.mk (QuotientGroup.rightRel H) (Classical.choose h') :
        Quotient (QuotientGroup.rightRel H))
      else Quotient.mk (QuotientGroup.rightRel H) 1) =
      Quotient.mk (QuotientGroup.rightRel H) (Classical.choose h) := dite_eq_left h
  refine hg.trans ?_
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr (hF _ _ (Classical.choose_spec h))

theorem relIndex_ne_zero_of_finite {G : Type*} [Group G] (H L : Subgroup G)
    (h : Finite (Quotient (QuotientGroup.rightRel (H.subgroupOf L)))) :
    H.relIndex L ≠ 0 := by
  have := h
  have : Finite (↥L ⧸ H.subgroupOf L) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (s := H.subgroupOf L))
  show (H.subgroupOf L).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem finite_of_relIndex_ne_zero {G : Type*} [Group G] (H L : Subgroup G)
    (h : H.relIndex L ≠ 0) : Finite (Quotient (QuotientGroup.rightRel (H.subgroupOf L))) := by
  have : (H.subgroupOf L).FiniteIndex := ⟨h⟩
  have : Finite (↥L ⧸ H.subgroupOf L) := Subgroup.finite_quotient_of_finiteIndex
  exact Finite.of_equiv _
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel (s := H.subgroupOf L)).symm

theorem mem_stabilizer_iff_conj {G : Type*} [Group G] (P : Subgroup G) (h γ : G) :
    γ ∈ MulAction.stabilizer G (QuotientGroup.mk h : G ⧸ P) ↔ h⁻¹ * γ * h ∈ P := by
  rw [MulAction.mem_stabilizer_iff]
  have e : γ • (QuotientGroup.mk h : G ⧸ P) = QuotientGroup.mk (γ * h) := rfl
  rw [e, QuotientGroup.eq]
  have e2 : (γ * h)⁻¹ * h = (h⁻¹ * γ * h)⁻¹ := by group
  rw [e2, inv_mem_iff]

/-! ### Reduction of integral matrices -/

theorem map_zmod_eq_one_iff {n : Type} [DecidableEq n] [Fintype n] (N : ℕ)
    (X : Matrix.GeneralLinearGroup n ℤ) :
    Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod N)) X = 1 ↔
      ∀ i j, (N : ℤ) ∣ X.val i j - (1 : Matrix n n ℤ) i j := by
  have e1 : ∀ i j, (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod N)) X).val i j =
      ((X.val i j : ℤ) : ZMod N) := fun _ _ => rfl
  have e2 : ∀ i j, (1 : Matrix.GeneralLinearGroup n (ZMod N)).val i j =
      (((1 : Matrix n n ℤ) i j : ℤ) : ZMod N) := by
    intro i j
    rw [Units.val_one]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  constructor
  · intro h i j
    have hij : (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod N)) X).val i j =
        (1 : Matrix.GeneralLinearGroup n (ZMod N)).val i j := by rw [h]
    rw [e1, e2] at hij
    have hz : ((X.val i j - (1 : Matrix n n ℤ) i j : ℤ) : ZMod N) = 0 := by
      rw [Int.cast_sub, hij, sub_self]
    exact (CharP.intCast_eq_zero_iff (ZMod N) N _).mp hz
  · intro h
    apply Units.ext
    ext i j
    have hz : ((X.val i j - (1 : Matrix n n ℤ) i j : ℤ) : ZMod N) = 0 :=
      (CharP.intCast_eq_zero_iff (ZMod N) N _).mpr (h i j)
    rw [Int.cast_sub, sub_eq_zero] at hz
    rw [e1, e2]
    exact hz

theorem reduction_eq_one_iff (N : ℕ) (B : GLTwo ℤ) :
    reduction N B = 1 ↔ ∀ i j, (N : ℤ) ∣ B.val i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
  map_zmod_eq_one_iff N B

theorem reductionThree_eq_one_iff (X : IntegralGL3) :
    reductionThree X = 1 ↔ ∀ i j, (3 : ℤ) ∣ X.val i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
  have h := map_zmod_eq_one_iff 3 X
  change Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) X = 1 ↔ _
  exact_mod_cast h

theorem arithmeticLevel_of_reduction_eq_one (Z : IntegralGL3) (h : reductionThree Z = 1) :
    Z ∈ arithmeticLevel := by
  change reductionThree Z ∈ rowStabilizer
  rw [h]
  exact one_mem _

theorem mem_rationalLevel_of_reduction (Z : IntegralGL3) (h : reductionThree Z = 1) :
    integralRational Z ∈ rationalLevel :=
  ⟨⟨Z, arithmeticLevel_of_reduction_eq_one Z h⟩, rfl⟩

/-- The inverse transpose of an integral `2 × 2` matrix. -/
def invTranspose : GLTwo ℤ →* GLTwo ℤ where
  toFun B := ⟨Matrix.transpose (B⁻¹ : GLTwo ℤ).val, Matrix.transpose B.val,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' B C := by
    apply Units.ext
    simp [Matrix.transpose_mul]

theorem invTranspose_apply (B : GLTwo ℤ) (i j : Fin 2) :
    (invTranspose B).val i j = (B⁻¹ : GLTwo ℤ).val j i := rfl

theorem invTranspose_inv_apply (B : GLTwo ℤ) (i j : Fin 2) :
    ((invTranspose B)⁻¹ : GLTwo ℤ).val i j = B.val j i := rfl

theorem reduction_invTranspose (N : ℕ) (B : GLTwo ℤ) :
    reduction N (invTranspose B) = 1 ↔ reduction N B = 1 := by
  have h1 : reduction N B = 1 ↔ reduction N B⁻¹ = 1 := by
    rw [map_inv, inv_eq_one]
  have hsymm : ∀ i j : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℤ) i j =
      (1 : Matrix (Fin 2) (Fin 2) ℤ) j i := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · simp [hij, Ne.symm hij]
  rw [h1, reduction_eq_one_iff, reduction_eq_one_iff]
  constructor
  · intro h i j
    have h' := h j i
    rw [hsymm j i] at h'
    exact h'
  · intro h i j
    have h' := h j i
    rw [hsymm j i] at h'
    exact h'

/-! ### Entry formulas -/

theorem intMap_apply {R : Type*} [CommRing R] (X : IntegralGL3) (i j : Fin 3) :
    (Matrix.GeneralLinearGroup.map (Int.castRingHom R) X).val i j = ((X.val i j : ℤ) : R) :=
  rfl

theorem integralRational_apply (X : IntegralGL3) (i j : Fin 3) :
    (integralRational X).val i j = ((X.val i j : ℤ) : ℚ) := intMap_apply X i j

theorem map_algebraMap_integralRational (X : IntegralGL3) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (integralRational X) =
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) X := by
  apply Units.ext
  ext i j
  have h1 : (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (integralRational X)).val i j =
      algebraMap ℚ ℝ ((X.val i j : ℤ) : ℚ) := rfl
  rw [h1, intMap_apply]
  simp

theorem planeUnipotent_val {R : Type*} [CommRing R] (s t : R) :
    (planeUnipotent s t).val = !![1, 0, s; 0, 1, t; 0, 0, 1] := rfl

theorem lineUnipotent_val {R : Type*} [CommRing R] (s t : R) :
    (lineUnipotent s t).val = !![1, s, t; 0, 1, 0; 0, 0, 1] := rfl

theorem planeUnipotent_zero {R : Type*} [CommRing R] : planeUnipotent (0 : R) 0 = 1 :=
  (planeUnipotentHom R).map_one

theorem lineUnipotent_zero {R : Type*} [CommRing R] : lineUnipotent (0 : R) 0 = 1 :=
  (lineUnipotentHom R).map_one

theorem planeLevi_one_val {R : Type*} [CommRing R] (B : GLTwo R) :
    (planeLevi B 1).val =
      !![B.val 0 0, B.val 0 1, 0; B.val 1 0, B.val 1 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem lineLevi_one_val {R : Type*} [CommRing R] (B : GLTwo R) :
    (lineLevi 1 B).val =
      !![1, 0, 0; 0, B.val 0 0, B.val 0 1; 0, B.val 1 0, B.val 1 1] := by
  rw [lineLevi_val, Units.val_one]

theorem integralRational_planeUnipotent (s t : ℤ) :
    integralRational (planeUnipotent s t) = planeUnipotent (s : ℚ) (t : ℚ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [integralRational_apply, planeUnipotent_val]

theorem integralRational_lineUnipotent (s t : ℤ) :
    integralRational (lineUnipotent s t) = lineUnipotent (s : ℚ) (t : ℚ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [integralRational_apply, lineUnipotent_val]

/-- The column action of an integral `2 × 2` matrix on `ℝ²` (the formula of `realAct`). -/
def realActCol (A : GLTwo ℤ) (r : ℝ × ℝ) : ℝ × ℝ :=
  (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) * r.1 +
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) * r.2,
    ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * r.1 +
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) * r.2)

/-! ### The structure of a base frame -/

/-- The data of a radical frame in standard position (before conjugation by `g`), with the
integrality information needed for the congruence-level analysis. The radical already carries
the scaling `r ↦ u(3 r)`. -/
structure BaseFrame where
  /-- The rational parabolic subgroup containing radical and Levi. -/
  parab : Subgroup RationalGL3
  /-- The scaled radical coordinates. -/
  rad : Multiplicative (ℚ × ℚ) →* RationalGL3
  rad_injective : Function.Injective rad
  rad_mem : ∀ x, rad x ∈ parab
  rad_unitri : ∀ x, TernaryPeriodPolynomials.FlagExactness.IsUnitri (rad x)
  /-- The integral Levi group. -/
  levi : GLTwo ℤ →* IntegralGL3
  levi_mem : ∀ B, integralRational (levi B) ∈ parab
  /-- The matrix through which the Levi element acts on radical coordinates. -/
  mat : GLTwo ℤ →* GLTwo ℤ
  conj : ∀ (B : GLTwo ℤ) (r : ℚ × ℚ),
    integralRational (levi B) * rad (Multiplicative.ofAdd r) * (integralRational (levi B))⁻¹ =
      rad (Multiplicative.ofAdd (leviAct (mat B) r))
  disjoint : ∀ (B : GLTwo ℤ) (r : ℚ × ℚ),
    integralRational (levi B) = rad (Multiplicative.ofAdd r) → B = 1
  /-- The integral points of the radical. -/
  radInt : ℤ × ℤ → IntegralGL3
  radInt_map : ∀ ℓ : ℤ × ℤ,
    integralRational (radInt ℓ) = rad (Multiplicative.ofAdd ((ℓ.1 : ℚ), (ℓ.2 : ℚ)))
  radInt_red : ∀ ℓ : ℤ × ℤ, reductionThree (radInt ℓ) = 1
  levi_red : ∀ B : GLTwo ℤ, reduction 3 (mat B) = 1 → reductionThree (levi B) = 1
  decomp : ∀ X : IntegralGL3, reductionThree X = 1 → integralRational X ∈ parab →
    ∃ (ℓ : ℤ × ℤ) (B : GLTwo ℤ), reduction 3 (mat B) = 1 ∧
      (X = radInt ℓ * levi B ∨ X = levi B * radInt ℓ)

/-- The frame obtained from a base frame by conjugating with `a`. -/
def BaseFrame.frame (b : BaseFrame) (a : RationalGL3) : RadicalFrame where
  radical := (conjHom a).comp b.rad
  radical_injective := (conjHom_injective a).comp b.rad_injective
  Levi := GLTwo ℤ
  leviGroup := inferInstance
  leviHom := (conjHom a).comp (integralRational.comp b.levi)
  leviMatrix := b.mat
  conj := fun m r => by
    have h := b.conj m r
    show a * integralRational (b.levi m) * a⁻¹ * (a * b.rad (Multiplicative.ofAdd r) * a⁻¹) *
      (a * integralRational (b.levi m) * a⁻¹)⁻¹ =
        a * b.rad (Multiplicative.ofAdd (leviAct (b.mat m) r)) * a⁻¹
    rw [← h]
    group
  disjoint := fun m r h => by
    apply b.disjoint m r
    have h' : a * integralRational (b.levi m) * a⁻¹ =
        a * b.rad (Multiplicative.ofAdd r) * a⁻¹ := h
    exact mul_left_cancel (mul_right_cancel h')

theorem BaseFrame.frame_integral (b : BaseFrame) (a : RationalGL3) (ℓ : ℤ × ℤ) :
    (b.frame a).integral ℓ = a * b.rad (Multiplicative.ofAdd ((ℓ.1 : ℚ), (ℓ.2 : ℚ))) * a⁻¹ :=
  rfl

theorem BaseFrame.frame_leviHom (b : BaseFrame) (a : RationalGL3) (B : GLTwo ℤ) :
    (b.frame a).leviHom B = a * integralRational (b.levi B) * a⁻¹ := rfl

theorem BaseFrame.mem_leviLevel (b : BaseFrame) (a : RationalGL3) (N : ℕ) (B : GLTwo ℤ) :
    B ∈ (b.frame a).leviLevel N ↔ reduction N (b.mat B) = 1 :=
  MonoidHom.mem_ker

theorem BaseFrame.mem_lattice_iff (b : BaseFrame) (a : RationalGL3) (N : ℕ) (y : RationalGL3) :
    y ∈ (b.frame a).lattice N ↔ ∃ (ℓ : ℤ × ℤ) (B : GLTwo ℤ), reduction N (b.mat B) = 1 ∧
      y = a * (b.rad (Multiplicative.ofAdd ((ℓ.1 : ℚ), (ℓ.2 : ℚ))) *
        integralRational (b.levi B)) * a⁻¹ := by
  constructor
  · rintro ⟨ℓ, m, hm, rfl⟩
    refine ⟨ℓ, m, (b.mem_leviLevel a N m).mp hm, ?_⟩
    rw [conj_mul_eq]
    rfl
  · rintro ⟨ℓ, B, hB, rfl⟩
    refine ⟨ℓ, B, (b.mem_leviLevel a N B).mpr hB, ?_⟩
    rw [conj_mul_eq]
    rfl

theorem BaseFrame.mul_mem_lattice (b : BaseFrame) (a : RationalGL3) (N : ℕ) (ℓ : ℤ × ℤ)
    (B : GLTwo ℤ) (hB : reduction N (b.mat B) = 1) :
    a * (b.rad (Multiplicative.ofAdd ((ℓ.1 : ℚ), (ℓ.2 : ℚ))) * integralRational (b.levi B)) *
        a⁻¹ ∈ (b.frame a).lattice N ∧
      a * (integralRational (b.levi B) *
        b.rad (Multiplicative.ofAdd ((ℓ.1 : ℚ), (ℓ.2 : ℚ)))) * a⁻¹ ∈ (b.frame a).lattice N := by
  have h1 := (b.frame a).integral_mem N ℓ
  have h2 := (b.frame a).levi_mem N B ((b.mem_leviLevel a N B).mpr hB)
  constructor
  · rw [conj_mul_eq]
    exact mul_mem h1 h2
  · rw [conj_mul_eq]
    exact mul_mem h2 h1

theorem BaseFrame.quot_mem_lattice (b : BaseFrame) (a : RationalGL3) (N : ℕ) (ℓ ℓ' : ℤ × ℤ)
    (B B' : GLTwo ℤ) (hB : reduction N (b.mat (B' * B⁻¹)) = 1) :
    a * (b.rad (Multiplicative.ofAdd ((ℓ'.1 : ℚ), (ℓ'.2 : ℚ))) * integralRational (b.levi B')) *
        a⁻¹ * (a * (b.rad (Multiplicative.ofAdd ((ℓ.1 : ℚ), (ℓ.2 : ℚ))) *
          integralRational (b.levi B)) * a⁻¹)⁻¹ ∈ (b.frame a).lattice N := by
  have h1 := (b.frame a).integral_mem N ℓ'
  have h2 := (b.frame a).levi_mem N (B' * B⁻¹) ((b.mem_leviLevel a N _).mpr hB)
  have h3 := inv_mem ((b.frame a).integral_mem N ℓ)
  have h := mul_mem (mul_mem h1 h2) h3
  have hl : (b.frame a).leviHom (B' * B⁻¹) =
      a * (integralRational (b.levi B') * (integralRational (b.levi B))⁻¹) * a⁻¹ := by
    show a * integralRational (b.levi (B' * B⁻¹)) * a⁻¹ = _
    simp only [map_mul, map_inv]
  rw [hl] at h
  rw [conj_quot_eq]
  exact h

theorem BaseFrame.mem_lattice_of_conj (b : BaseFrame) (g X : IntegralGL3)
    (hred : reductionThree X = 1) (hP : integralRational X ∈ b.parab) :
    integralRational (g * X * g⁻¹) ∈ (b.frame (integralRational g)).lattice 3 := by
  obtain ⟨ℓ, B, hB, h | h⟩ := b.decomp X hred hP
  · subst h
    have e : integralRational (g * (b.radInt ℓ * b.levi B) * g⁻¹) =
        integralRational g * (b.rad (Multiplicative.ofAdd ((ℓ.1 : ℚ), (ℓ.2 : ℚ))) *
          integralRational (b.levi B)) * (integralRational g)⁻¹ := by
      simp only [map_mul, map_inv, b.radInt_map]
    rw [e]
    exact (b.mul_mem_lattice (integralRational g) 3 ℓ B hB).1
  · subst h
    have e : integralRational (g * (b.levi B * b.radInt ℓ) * g⁻¹) =
        integralRational g * (integralRational (b.levi B) *
          b.rad (Multiplicative.ofAdd ((ℓ.1 : ℚ), (ℓ.2 : ℚ)))) * (integralRational g)⁻¹ := by
      simp only [map_mul, map_inv, b.radInt_map]
    rw [e]
    exact (b.mul_mem_lattice (integralRational g) 3 ℓ B hB).2

/-- The arithmetic stabilizer `Γ ⊓ Stab(g P)` of the flag of the frame. -/
abbrev BaseFrame.flagLevel (b : BaseFrame) (g : IntegralGL3) : Subgroup RationalGL3 :=
  rationalLevel ⊓ MulAction.stabilizer RationalGL3
    (QuotientGroup.mk (integralRational g) : RationalGL3 ⧸ b.parab)

theorem BaseFrame.lattice_le_flagLevel (b : BaseFrame) (g : IntegralGL3) (N : ℕ) (hN : 3 ∣ N) :
    (b.frame (integralRational g)).lattice N ≤ b.flagLevel g := by
  intro y hy
  have hy3 : y ∈ (b.frame (integralRational g)).lattice 3 :=
    (b.frame (integralRational g)).lattice_mono hN hy
  obtain ⟨ℓ, B, hB, rfl⟩ := (b.mem_lattice_iff (integralRational g) 3 y).mp hy3
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hZ : reductionThree (g * (b.radInt ℓ * b.levi B) * g⁻¹) = 1 := by
      simp [map_mul, map_inv, b.radInt_red ℓ, b.levi_red B hB]
    convert mem_rationalLevel_of_reduction _ hZ using 1
    simp only [map_mul, map_inv, b.radInt_map]
  · rw [mem_stabilizer_iff_conj, inv_conj_conj]
    exact mul_mem (b.rad_mem _) (b.levi_mem _)

theorem BaseFrame.fiber_three (b : BaseFrame) (g : IntegralGL3) (a c : b.flagLevel g)
    (A C : IntegralGL3) (hA : integralRational A = (a : RationalGL3))
    (hC : integralRational C = (c : RationalGL3))
    (hred : reductionThree A = reductionThree C) :
    ((c * a⁻¹ : b.flagLevel g) : RationalGL3) ∈ (b.frame (integralRational g)).lattice 3 := by
  have hX : reductionThree (g⁻¹ * (C * A⁻¹) * g) = 1 := by
    simp only [map_mul, map_inv]
    rw [← hred]
    simp
  have hstab : (c : RationalGL3) * (a : RationalGL3)⁻¹ ∈ MulAction.stabilizer RationalGL3
      (QuotientGroup.mk (integralRational g) : RationalGL3 ⧸ b.parab) :=
    mul_mem (Subgroup.mem_inf.mp c.property).2 (inv_mem (Subgroup.mem_inf.mp a.property).2)
  have hιX : integralRational (g⁻¹ * (C * A⁻¹) * g) =
      (integralRational g)⁻¹ * ((c : RationalGL3) * (a : RationalGL3)⁻¹) *
        integralRational g := by
    simp only [map_mul, map_inv, hA, hC]
  have hP : integralRational (g⁻¹ * (C * A⁻¹) * g) ∈ b.parab := by
    rw [hιX]
    exact (mem_stabilizer_iff_conj _ _ _).mp hstab
  have key := b.mem_lattice_of_conj g _ hX hP
  have e : integralRational (g * (g⁻¹ * (C * A⁻¹) * g) * g⁻¹) =
      (c : RationalGL3) * (a : RationalGL3)⁻¹ := by
    simp only [map_mul, map_inv, hA, hC]
    group
  rw [e] at key
  exact key

theorem BaseFrame.finite_three (b : BaseFrame) (g : IntegralGL3) :
    Finite (Quotient (QuotientGroup.rightRel
      (((b.frame (integralRational g)).lattice 3).subgroupOf (b.flagLevel g)))) := by
  classical
  have hint : ∀ γ : b.flagLevel g, ∃ A : IntegralGL3, integralRational A = (γ : RationalGL3) := by
    intro γ
    obtain ⟨⟨A, _⟩, hA⟩ := (Subgroup.mem_inf.mp γ.property).1
    exact ⟨A, hA⟩
  have : Finite (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)) := finite_gl 3 3
  refine finite_quotient_of_fibers _
    (fun γ : b.flagLevel g => reductionThree (Classical.choose (hint γ))) ?_
  intro a c hF
  rw [Subgroup.mem_subgroupOf]
  exact b.fiber_three g a c _ _ (Classical.choose_spec (hint a)) (Classical.choose_spec (hint c))
    hF

theorem BaseFrame.fiber_levels (b : BaseFrame) (a : RationalGL3) (N : ℕ) (y y' : RationalGL3)
    (ℓ ℓ' : ℤ × ℤ) (B B' : GLTwo ℤ)
    (hy : y = a * (b.rad (Multiplicative.ofAdd ((ℓ.1 : ℚ), (ℓ.2 : ℚ))) *
      integralRational (b.levi B)) * a⁻¹)
    (hy' : y' = a * (b.rad (Multiplicative.ofAdd ((ℓ'.1 : ℚ), (ℓ'.2 : ℚ))) *
      integralRational (b.levi B')) * a⁻¹)
    (hred : reduction N (b.mat B) = reduction N (b.mat B')) :
    y' * y⁻¹ ∈ (b.frame a).lattice N := by
  subst hy hy'
  have h1 : reduction N (b.mat (B' * B⁻¹)) = 1 := by
    simp only [map_mul, map_inv]
    rw [hred]
    exact mul_inv_cancel _
  exact b.quot_mem_lattice a N ℓ ℓ' B B' h1

theorem BaseFrame.relIndex_levels (b : BaseFrame) (a : RationalGL3) (K : ℕ) (hK : 0 < K) :
    ((b.frame a).lattice (3 * K)).relIndex ((b.frame a).lattice 3) ≠ 0 := by
  classical
  have : NeZero (3 * K) := ⟨by omega⟩
  have : Finite (Matrix.GeneralLinearGroup (Fin 2) (ZMod (3 * K))) := finite_gl 2 (3 * K)
  have hint : ∀ y : (b.frame a).lattice 3, ∃ q : (ℤ × ℤ) × GLTwo ℤ,
      (y : RationalGL3) = a * (b.rad (Multiplicative.ofAdd ((q.1.1 : ℚ), (q.1.2 : ℚ))) *
        integralRational (b.levi q.2)) * a⁻¹ := by
    intro y
    obtain ⟨ℓ, B, _, hy⟩ := (b.mem_lattice_iff a 3 y).mp y.property
    exact ⟨(ℓ, B), hy⟩
  apply relIndex_ne_zero_of_finite
  refine finite_quotient_of_fibers _
    (fun y : (b.frame a).lattice 3 =>
      reduction (3 * K) (b.mat (Classical.choose (hint y)).2)) ?_
  intro y y' hF
  rw [Subgroup.mem_subgroupOf]
  exact b.fiber_levels a (3 * K) y y' _ _ _ _ (Classical.choose_spec (hint y))
    (Classical.choose_spec (hint y')) hF

theorem BaseFrame.relIndex_flagLevel (b : BaseFrame) (g : IntegralGL3) (K : ℕ) (hK : 0 < K) :
    ((b.frame (integralRational g)).lattice (3 * K)).relIndex (b.flagLevel g) ≠ 0 := by
  have h1 := b.relIndex_levels (integralRational g) K hK
  have h2 : ((b.frame (integralRational g)).lattice 3).relIndex (b.flagLevel g) ≠ 0 :=
    relIndex_ne_zero_of_finite _ _ (b.finite_three g)
  have hle1 : (b.frame (integralRational g)).lattice (3 * K) ≤
      (b.frame (integralRational g)).lattice 3 :=
    (b.frame (integralRational g)).lattice_mono (dvd_mul_right 3 K)
  have hle2 : (b.frame (integralRational g)).lattice 3 ≤ b.flagLevel g :=
    b.lattice_le_flagLevel g 3 (dvd_refl 3)
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2]
  exact mul_ne_zero h1 h2

theorem BaseFrame.radical_mem_conjUnitri (b : BaseFrame) (a : RationalGL3)
    (x : Multiplicative (ℚ × ℚ)) :
    (b.frame a).radical x ∈ TernaryPeriodPolynomials.FlagExactness.conjUnitri a := by
  rw [TernaryPeriodPolynomials.FlagExactness.mem_conjUnitri]
  have e : a⁻¹ * (b.frame a).radical x * a = b.rad x := by
    show a⁻¹ * (a * b.rad x * a⁻¹) * a = b.rad x
    exact inv_conj_conj a (b.rad x)
  rw [e]
  exact b.rad_unitri x

/-! ### The plane side -/

/-- The integral Levi embedding `B ↦ diag(B, 1)`. -/
def planeLeviInt : GLTwo ℤ →* IntegralGL3 :=
  (planeLeviHom ℤ).comp (MonoidHom.inl (GLTwo ℤ) ℤˣ)

theorem planeLeviInt_apply (B : GLTwo ℤ) : planeLeviInt B = planeLevi B 1 := rfl

/-- The scaled plane radical `r ↦ u(3 r)`. -/
def planeRad : Multiplicative (ℚ × ℚ) →* RationalGL3 where
  toFun x := planeUnipotent (3 * x.toAdd.1) (3 * x.toAdd.2)
  map_one' := by simp [planeUnipotent_zero]
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, mul_add]
    exact planeUnipotent_add _ _ _ _

theorem planeRad_apply (x : Multiplicative (ℚ × ℚ)) :
    planeRad x = planeUnipotent (3 * x.toAdd.1) (3 * x.toAdd.2) := rfl

theorem planeRad_injective : Function.Injective planeRad := by
  intro x y h
  have h1 : (3 : ℚ) * x.toAdd.1 = 3 * y.toAdd.1 := congrArg (fun g : GL3 ℚ => g.val 0 2) h
  have h2 : (3 : ℚ) * x.toAdd.2 = 3 * y.toAdd.2 := congrArg (fun g : GL3 ℚ => g.val 1 2) h
  apply Multiplicative.toAdd.injective
  exact Prod.ext (mul_left_cancel₀ (by norm_num) h1) (mul_left_cancel₀ (by norm_num) h2)

theorem plane_conj_core {R : Type*} [CommRing R] (B : GLTwo ℤ) (s t s' t' : R)
    (hs : s' = ((B.val 0 0 : ℤ) : R) * s + ((B.val 0 1 : ℤ) : R) * t)
    (ht : t' = ((B.val 1 0 : ℤ) : R) * s + ((B.val 1 1 : ℤ) : R) * t) :
    Matrix.GeneralLinearGroup.map (Int.castRingHom R) (planeLevi B 1) * planeUnipotent s t =
      planeUnipotent s' t' * Matrix.GeneralLinearGroup.map (Int.castRingHom R) (planeLevi B 1) := by
  subst hs ht
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi_one_val, planeUnipotent_val, Matrix.mul_apply, Fin.sum_univ_three]

theorem planeLevi_eq_unipotent {B : GLTwo ℤ} {s t : ℚ}
    (h : integralRational (planeLevi B 1) = planeUnipotent s t) : B = 1 := by
  have e := fun i j => congrArg (fun z : RationalGL3 => z.val i j) h
  have h00 : ((B.val 0 0 : ℤ) : ℚ) = 1 := e 0 0
  have h01 : ((B.val 0 1 : ℤ) : ℚ) = 0 := e 0 1
  have h10 : ((B.val 1 0 : ℤ) : ℚ) = 0 := e 1 0
  have h11 : ((B.val 1 1 : ℤ) : ℚ) = 1 := e 1 1
  have i00 : B.val 0 0 = 1 := by exact_mod_cast h00
  have i01 : B.val 0 1 = 0 := by exact_mod_cast h01
  have i10 : B.val 1 0 = 0 := by exact_mod_cast h10
  have i11 : B.val 1 1 = 1 := by exact_mod_cast h11
  apply Units.ext
  rw [Units.val_one, Matrix.eta_fin_two B.val, i00, i01, i10, i11, Matrix.one_fin_two]

theorem plane_red_unipotent (s t : ℤ) (hs : (3 : ℤ) ∣ s) (ht : (3 : ℤ) ∣ t) :
    reductionThree (planeUnipotent s t) = 1 := by
  rw [reductionThree_eq_one_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [planeUnipotent_val] <;> omega

theorem plane_levi_red (B : GLTwo ℤ) (hB : reduction 3 B = 1) :
    reductionThree (planeLevi B 1) = 1 := by
  have hB' := (reduction_eq_one_iff 3 B).mp hB
  have d00 : (3 : ℤ) ∣ B.val 0 0 - 1 := by simpa using hB' 0 0
  have d01 : (3 : ℤ) ∣ B.val 0 1 := by simpa using hB' 0 1
  have d10 : (3 : ℤ) ∣ B.val 1 0 := by simpa using hB' 1 0
  have d11 : (3 : ℤ) ∣ B.val 1 1 - 1 := by simpa using hB' 1 1
  rw [reductionThree_eq_one_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [planeLevi_one_val] <;> omega

theorem plane_decomp (X : IntegralGL3) (hred : reductionThree X = 1)
    (hP : integralRational X ∈ planeParabolic ℚ) :
    ∃ (ℓ : ℤ × ℤ) (B : GLTwo ℤ), reduction 3 B = 1 ∧
      X = planeUnipotent (3 * ℓ.1) (3 * ℓ.2) * planeLevi B 1 := by
  have hP' : InPlaneParabolic (integralRational X) := hP
  have h20 : X.val 2 0 = 0 := by
    have h : ((X.val 2 0 : ℤ) : ℚ) = 0 := hP'.1
    exact_mod_cast h
  have h21 : X.val 2 1 = 0 := by
    have h : ((X.val 2 1 : ℤ) : ℚ) = 0 := hP'.2
    exact_mod_cast h
  obtain ⟨Y, hY⟩ : ∃ Y : IntegralGL3, Y = X⁻¹ := ⟨_, rfl⟩
  have hXY : X.val * Y.val = 1 := by
    rw [hY]
    exact Units.mul_inv X
  have hYX : Y.val * X.val = 1 := by
    rw [hY]
    exact Units.inv_mul X
  have hPY : InPlaneParabolic (integralRational Y) := by
    rw [hY, map_inv]
    exact inPlane_inv hP'
  have hY20 : Y.val 2 0 = 0 := by
    have h : ((Y.val 2 0 : ℤ) : ℚ) = 0 := hPY.1
    exact_mod_cast h
  have hY21 : Y.val 2 1 = 0 := by
    have h : ((Y.val 2 1 : ℤ) : ℚ) = 0 := hPY.2
    exact_mod_cast h
  have e : ∀ i j, X.val i 0 * Y.val 0 j + X.val i 1 * Y.val 1 j + X.val i 2 * Y.val 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := fun i j => by
    rw [← hXY, Matrix.mul_apply, Fin.sum_univ_three]
  have e' : ∀ i j, Y.val i 0 * X.val 0 j + Y.val i 1 * X.val 1 j + Y.val i 2 * X.val 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := fun i j => by
    rw [← hYX, Matrix.mul_apply, Fin.sum_univ_three]
  have f00 : X.val 0 0 * Y.val 0 0 + X.val 0 1 * Y.val 1 0 = 1 := by
    simpa [hY20] using e 0 0
  have f01 : X.val 0 0 * Y.val 0 1 + X.val 0 1 * Y.val 1 1 = 0 := by
    simpa [hY21] using e 0 1
  have f10 : X.val 1 0 * Y.val 0 0 + X.val 1 1 * Y.val 1 0 = 0 := by
    simpa [hY20] using e 1 0
  have f11 : X.val 1 0 * Y.val 0 1 + X.val 1 1 * Y.val 1 1 = 1 := by
    simpa [hY21] using e 1 1
  have g00 : Y.val 0 0 * X.val 0 0 + Y.val 0 1 * X.val 1 0 = 1 := by
    simpa [h20] using e' 0 0
  have g01 : Y.val 0 0 * X.val 0 1 + Y.val 0 1 * X.val 1 1 = 0 := by
    simpa [h21] using e' 0 1
  have g10 : Y.val 1 0 * X.val 0 0 + Y.val 1 1 * X.val 1 0 = 0 := by
    simpa [h20] using e' 1 0
  have g11 : Y.val 1 0 * X.val 0 1 + Y.val 1 1 * X.val 1 1 = 1 := by
    simpa [h21] using e' 1 1
  have f22 : X.val 2 2 * Y.val 2 2 = 1 := by
    simpa [h20, h21] using e 2 2
  obtain ⟨B, hB00, hB01, hB10, hB11⟩ : ∃ B : GLTwo ℤ, B.val 0 0 = X.val 0 0 ∧
      B.val 0 1 = X.val 0 1 ∧ B.val 1 0 = X.val 1 0 ∧ B.val 1 1 = X.val 1 1 :=
    ⟨⟨!![X.val 0 0, X.val 0 1; X.val 1 0, X.val 1 1],
      !![Y.val 0 0, Y.val 0 1; Y.val 1 0, Y.val 1 1],
      by rw [Matrix.one_fin_two, Matrix.mul_fin_two, f00, f01, f10, f11],
      by rw [Matrix.one_fin_two, Matrix.mul_fin_two, g00, g01, g10, g11]⟩,
      rfl, rfl, rfl, rfl⟩
  have hd := (reductionThree_eq_one_iff X).mp hred
  have d00 : (3 : ℤ) ∣ X.val 0 0 - 1 := by simpa using hd 0 0
  have d01 : (3 : ℤ) ∣ X.val 0 1 := by simpa using hd 0 1
  have d02 : (3 : ℤ) ∣ X.val 0 2 := by simpa using hd 0 2
  have d10 : (3 : ℤ) ∣ X.val 1 0 := by simpa using hd 1 0
  have d11 : (3 : ℤ) ∣ X.val 1 1 - 1 := by simpa using hd 1 1
  have d12 : (3 : ℤ) ∣ X.val 1 2 := by simpa using hd 1 2
  have d22 : (3 : ℤ) ∣ X.val 2 2 - 1 := by simpa using hd 2 2
  have h22 : X.val 2 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one f22 with h | h
    · exact h
    · omega
  obtain ⟨k1, hk1⟩ := d02
  obtain ⟨k2, hk2⟩ := d12
  have hBred : reduction 3 B = 1 := by
    rw [reduction_eq_one_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hB00, hB01, hB10, hB11] <;> omega
  refine ⟨(k1, k2), B, hBred, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeUnipotent_val, planeLevi_one_val, Matrix.mul_apply, Fin.sum_univ_three,
      hB00, hB01, hB10, hB11, hk1, hk2, h20, h21, h22]

/-- The plane base frame: radical `u(3 r)`, Levi `diag(B, 1)` acting by `B`. -/
def planeBase : BaseFrame where
  parab := planeParabolic ℚ
  rad := planeRad
  rad_injective := planeRad_injective
  rad_mem := fun x => ⟨rfl, rfl⟩
  rad_unitri := fun x => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  levi := planeLeviInt
  levi_mem := fun B => inPlane_map (Int.castRingHom ℚ) (planeLevi B 1) (planeLevi_mem B 1)
  mat := MonoidHom.id _
  conj := fun B r => by
    have key := plane_conj_core (R := ℚ) B (3 * r.1) (3 * r.2) (3 * (leviAct B r).1)
      (3 * (leviAct B r).2) (by simp only [leviAct]; ring) (by simp only [leviAct]; ring)
    rw [mul_inv_eq_iff_eq_mul]
    exact key
  disjoint := fun B r h => planeLevi_eq_unipotent (s := 3 * r.1) (t := 3 * r.2) h
  radInt := fun ℓ => planeUnipotent (3 * ℓ.1) (3 * ℓ.2)
  radInt_map := fun ℓ => by
    show integralRational (planeUnipotent (3 * ℓ.1) (3 * ℓ.2)) = _
    rw [integralRational_planeUnipotent]
    push_cast
    rfl
  radInt_red := fun ℓ => plane_red_unipotent _ _ (dvd_mul_right 3 ℓ.1) (dvd_mul_right 3 ℓ.2)
  levi_red := fun B hB => plane_levi_red B hB
  decomp := fun X hred hP => by
    obtain ⟨ℓ, B, hB, hX⟩ := plane_decomp X hred hP
    exact ⟨ℓ, B, hB, Or.inl hX⟩

/-- The real form of the inverse conjugation by the plane Levi element (`diag(B, 1)`). -/
theorem plane_real_conj (B : GLTwo ℤ) (r : ℝ × ℝ) :
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) (planeLevi B 1))⁻¹ *
        planeUnipotent (3 * r.1) (3 * r.2) *
        Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) (planeLevi B 1) =
      planeUnipotent (3 * (realActCol B⁻¹ r).1) (3 * (realActCol B⁻¹ r).2) := by
  have E : B.val * (B⁻¹ : GLTwo ℤ).val = 1 := Units.mul_inv B
  have e : ∀ i j, B.val i 0 * (B⁻¹ : GLTwo ℤ).val 0 j +
      B.val i 1 * (B⁻¹ : GLTwo ℤ).val 1 j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
    fun i j => by rw [← E, Matrix.mul_apply, Fin.sum_univ_two]
  have i00 : B.val 0 0 * (B⁻¹ : GLTwo ℤ).val 0 0 +
      B.val 0 1 * (B⁻¹ : GLTwo ℤ).val 1 0 = 1 := by simpa using e 0 0
  have i01 : B.val 0 0 * (B⁻¹ : GLTwo ℤ).val 0 1 +
      B.val 0 1 * (B⁻¹ : GLTwo ℤ).val 1 1 = 0 := by simpa using e 0 1
  have i10 : B.val 1 0 * (B⁻¹ : GLTwo ℤ).val 0 0 +
      B.val 1 1 * (B⁻¹ : GLTwo ℤ).val 1 0 = 0 := by simpa using e 1 0
  have i11 : B.val 1 0 * (B⁻¹ : GLTwo ℤ).val 0 1 +
      B.val 1 1 * (B⁻¹ : GLTwo ℤ).val 1 1 = 1 := by simpa using e 1 1
  have q00 : ((B.val 0 0 : ℤ) : ℝ) * (((B⁻¹ : GLTwo ℤ).val 0 0 : ℤ) : ℝ) +
      ((B.val 0 1 : ℤ) : ℝ) * (((B⁻¹ : GLTwo ℤ).val 1 0 : ℤ) : ℝ) = 1 := by
    exact_mod_cast i00
  have q01 : ((B.val 0 0 : ℤ) : ℝ) * (((B⁻¹ : GLTwo ℤ).val 0 1 : ℤ) : ℝ) +
      ((B.val 0 1 : ℤ) : ℝ) * (((B⁻¹ : GLTwo ℤ).val 1 1 : ℤ) : ℝ) = 0 := by
    exact_mod_cast i01
  have q10 : ((B.val 1 0 : ℤ) : ℝ) * (((B⁻¹ : GLTwo ℤ).val 0 0 : ℤ) : ℝ) +
      ((B.val 1 1 : ℤ) : ℝ) * (((B⁻¹ : GLTwo ℤ).val 1 0 : ℤ) : ℝ) = 0 := by
    exact_mod_cast i10
  have q11 : ((B.val 1 0 : ℤ) : ℝ) * (((B⁻¹ : GLTwo ℤ).val 0 1 : ℤ) : ℝ) +
      ((B.val 1 1 : ℤ) : ℝ) * (((B⁻¹ : GLTwo ℤ).val 1 1 : ℤ) : ℝ) = 1 := by
    exact_mod_cast i11
  have core := plane_conj_core (R := ℝ) B (3 * (realActCol B⁻¹ r).1) (3 * (realActCol B⁻¹ r).2)
    (3 * r.1) (3 * r.2)
    (by simp only [realActCol]; linear_combination (-(3 * r.1)) * q00 - (3 * r.2) * q01)
    (by simp only [realActCol]; linear_combination (-(3 * r.1)) * q10 - (3 * r.2) * q11)
  rw [mul_assoc, ← core, inv_mul_cancel_left]

/-! ### The line side -/

/-- The integral Levi embedding `B ↦ diag(1, B)`. -/
def lineLeviInt : GLTwo ℤ →* IntegralGL3 :=
  (lineLeviHom ℤ).comp (MonoidHom.inr ℤˣ (GLTwo ℤ))

theorem lineLeviInt_apply (B : GLTwo ℤ) : lineLeviInt B = lineLevi 1 B := rfl

/-- The scaled line radical `r ↦ u(3 r)`. -/
def lineRad : Multiplicative (ℚ × ℚ) →* RationalGL3 where
  toFun x := lineUnipotent (3 * x.toAdd.1) (3 * x.toAdd.2)
  map_one' := by simp [lineUnipotent_zero]
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, mul_add]
    exact lineUnipotent_add _ _ _ _

theorem lineRad_apply (x : Multiplicative (ℚ × ℚ)) :
    lineRad x = lineUnipotent (3 * x.toAdd.1) (3 * x.toAdd.2) := rfl

theorem lineRad_injective : Function.Injective lineRad := by
  intro x y h
  have h1 : (3 : ℚ) * x.toAdd.1 = 3 * y.toAdd.1 := congrArg (fun g : GL3 ℚ => g.val 0 1) h
  have h2 : (3 : ℚ) * x.toAdd.2 = 3 * y.toAdd.2 := congrArg (fun g : GL3 ℚ => g.val 0 2) h
  apply Multiplicative.toAdd.injective
  exact Prod.ext (mul_left_cancel₀ (by norm_num) h1) (mul_left_cancel₀ (by norm_num) h2)

/-- Conjugating the radical by the line Levi element `diag(1, B)` acts by `(s, t) ↦ (s, t) B⁻¹`;
equivalently by the matrix `(B⁻¹)ᵀ` on column coordinates. -/
theorem line_conj_core {R : Type*} [CommRing R] (B : GLTwo ℤ) (s t s' t' : R)
    (hs : s' = (((B⁻¹ : GLTwo ℤ).val 0 0 : ℤ) : R) * s +
      (((B⁻¹ : GLTwo ℤ).val 1 0 : ℤ) : R) * t)
    (ht : t' = (((B⁻¹ : GLTwo ℤ).val 0 1 : ℤ) : R) * s +
      (((B⁻¹ : GLTwo ℤ).val 1 1 : ℤ) : R) * t) :
    Matrix.GeneralLinearGroup.map (Int.castRingHom R) (lineLevi 1 B) * lineUnipotent s t =
      lineUnipotent s' t' * Matrix.GeneralLinearGroup.map (Int.castRingHom R) (lineLevi 1 B) := by
  have E : (B⁻¹ : GLTwo ℤ).val * B.val = 1 := Units.inv_mul B
  have e : ∀ i j, (B⁻¹ : GLTwo ℤ).val i 0 * B.val 0 j +
      (B⁻¹ : GLTwo ℤ).val i 1 * B.val 1 j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
    fun i j => by rw [← E, Matrix.mul_apply, Fin.sum_univ_two]
  have i00 : (B⁻¹ : GLTwo ℤ).val 0 0 * B.val 0 0 +
      (B⁻¹ : GLTwo ℤ).val 0 1 * B.val 1 0 = 1 := by simpa using e 0 0
  have i01 : (B⁻¹ : GLTwo ℤ).val 0 0 * B.val 0 1 +
      (B⁻¹ : GLTwo ℤ).val 0 1 * B.val 1 1 = 0 := by simpa using e 0 1
  have i10 : (B⁻¹ : GLTwo ℤ).val 1 0 * B.val 0 0 +
      (B⁻¹ : GLTwo ℤ).val 1 1 * B.val 1 0 = 0 := by simpa using e 1 0
  have i11 : (B⁻¹ : GLTwo ℤ).val 1 0 * B.val 0 1 +
      (B⁻¹ : GLTwo ℤ).val 1 1 * B.val 1 1 = 1 := by simpa using e 1 1
  have q00 : (((B⁻¹ : GLTwo ℤ).val 0 0 : ℤ) : R) * ((B.val 0 0 : ℤ) : R) +
      (((B⁻¹ : GLTwo ℤ).val 0 1 : ℤ) : R) * ((B.val 1 0 : ℤ) : R) = 1 := by
    have h := congrArg (Int.cast : ℤ → R) i00
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one] at h
    exact h
  have q01 : (((B⁻¹ : GLTwo ℤ).val 0 0 : ℤ) : R) * ((B.val 0 1 : ℤ) : R) +
      (((B⁻¹ : GLTwo ℤ).val 0 1 : ℤ) : R) * ((B.val 1 1 : ℤ) : R) = 0 := by
    have h := congrArg (Int.cast : ℤ → R) i01
    simp only [Int.cast_add, Int.cast_mul, Int.cast_zero] at h
    exact h
  have q10 : (((B⁻¹ : GLTwo ℤ).val 1 0 : ℤ) : R) * ((B.val 0 0 : ℤ) : R) +
      (((B⁻¹ : GLTwo ℤ).val 1 1 : ℤ) : R) * ((B.val 1 0 : ℤ) : R) = 0 := by
    have h := congrArg (Int.cast : ℤ → R) i10
    simp only [Int.cast_add, Int.cast_mul, Int.cast_zero] at h
    exact h
  have q11 : (((B⁻¹ : GLTwo ℤ).val 1 0 : ℤ) : R) * ((B.val 0 1 : ℤ) : R) +
      (((B⁻¹ : GLTwo ℤ).val 1 1 : ℤ) : R) * ((B.val 1 1 : ℤ) : R) = 1 := by
    have h := congrArg (Int.cast : ℤ → R) i11
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one] at h
    exact h
  have k1 : s' * ((B.val 0 0 : ℤ) : R) + t' * ((B.val 1 0 : ℤ) : R) = s := by
    rw [hs, ht]
    linear_combination s * q00 + t * q10
  have k2 : s' * ((B.val 0 1 : ℤ) : R) + t' * ((B.val 1 1 : ℤ) : R) = t := by
    rw [hs, ht]
    linear_combination s * q01 + t * q11
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineLevi_one_val, lineUnipotent_val, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | linear_combination k1 | linear_combination (-1 : R) * k1 |
        linear_combination k2 | linear_combination (-1 : R) * k2

/-- The real form of the inverse conjugation by the line Levi element `diag(1, B)`; it needs no
inverse matrices because `u(s, t) diag(1, B) = diag(1, B) u((s, t) B)`. -/
theorem line_real_core {R : Type*} [CommRing R] (B : GLTwo ℤ) (s t s'' t'' : R)
    (hs : s'' = s * ((B.val 0 0 : ℤ) : R) + t * ((B.val 1 0 : ℤ) : R))
    (ht : t'' = s * ((B.val 0 1 : ℤ) : R) + t * ((B.val 1 1 : ℤ) : R)) :
    lineUnipotent s t * Matrix.GeneralLinearGroup.map (Int.castRingHom R) (lineLevi 1 B) =
      Matrix.GeneralLinearGroup.map (Int.castRingHom R) (lineLevi 1 B) * lineUnipotent s'' t'' := by
  subst hs ht
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineLevi_one_val, lineUnipotent_val, Matrix.mul_apply, Fin.sum_univ_three]

theorem line_real_conj (B : GLTwo ℤ) (r : ℝ × ℝ) :
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) (lineLevi 1 B))⁻¹ *
        lineUnipotent (3 * r.1) (3 * r.2) *
        Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) (lineLevi 1 B) =
      lineUnipotent (3 * (realActCol (invTranspose B)⁻¹ r).1)
        (3 * (realActCol (invTranspose B)⁻¹ r).2) := by
  have core := line_real_core (R := ℝ) B (3 * r.1) (3 * r.2)
    (3 * (realActCol (invTranspose B)⁻¹ r).1) (3 * (realActCol (invTranspose B)⁻¹ r).2)
    (by simp only [realActCol, invTranspose_inv_apply]; ring)
    (by simp only [realActCol, invTranspose_inv_apply]; ring)
  rw [mul_assoc, core, inv_mul_cancel_left]

theorem line_levi_red (B : GLTwo ℤ) (hB : reduction 3 B = 1) :
    reductionThree (lineLevi 1 B) = 1 := by
  have hB' := (reduction_eq_one_iff 3 B).mp hB
  have d00 : (3 : ℤ) ∣ B.val 0 0 - 1 := by simpa using hB' 0 0
  have d01 : (3 : ℤ) ∣ B.val 0 1 := by simpa using hB' 0 1
  have d10 : (3 : ℤ) ∣ B.val 1 0 := by simpa using hB' 1 0
  have d11 : (3 : ℤ) ∣ B.val 1 1 - 1 := by simpa using hB' 1 1
  rw [reductionThree_eq_one_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lineLevi_one_val] <;> omega

theorem line_red_unipotent (s t : ℤ) (hs : (3 : ℤ) ∣ s) (ht : (3 : ℤ) ∣ t) :
    reductionThree (lineUnipotent s t) = 1 := by
  rw [reductionThree_eq_one_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lineUnipotent_val] <;> omega

theorem lineLevi_eq_unipotent {B : GLTwo ℤ} {s t : ℚ}
    (h : integralRational (lineLevi 1 B) = lineUnipotent s t) : B = 1 := by
  have e := fun i j => congrArg (fun z : RationalGL3 => z.val i j) h
  have h00 : ((B.val 0 0 : ℤ) : ℚ) = 1 := by
    simpa [integralRational_apply, lineLevi_one_val, lineUnipotent_val] using e 1 1
  have h01 : ((B.val 0 1 : ℤ) : ℚ) = 0 := by
    simpa [integralRational_apply, lineLevi_one_val, lineUnipotent_val] using e 1 2
  have h10 : ((B.val 1 0 : ℤ) : ℚ) = 0 := by
    simpa [integralRational_apply, lineLevi_one_val, lineUnipotent_val] using e 2 1
  have h11 : ((B.val 1 1 : ℤ) : ℚ) = 1 := by
    simpa [integralRational_apply, lineLevi_one_val, lineUnipotent_val] using e 2 2
  have i00 : B.val 0 0 = 1 := by exact_mod_cast h00
  have i01 : B.val 0 1 = 0 := by exact_mod_cast h01
  have i10 : B.val 1 0 = 0 := by exact_mod_cast h10
  have i11 : B.val 1 1 = 1 := by exact_mod_cast h11
  apply Units.ext
  rw [Units.val_one, Matrix.eta_fin_two B.val, i00, i01, i10, i11, Matrix.one_fin_two]

theorem line_decomp (X : IntegralGL3) (hred : reductionThree X = 1)
    (hP : integralRational X ∈ lineParabolic ℚ) :
    ∃ (ℓ : ℤ × ℤ) (B : GLTwo ℤ), reduction 3 B = 1 ∧
      X = lineLevi 1 B * lineUnipotent (3 * ℓ.1) (3 * ℓ.2) := by
  have hP' : InLineParabolic (integralRational X) := hP
  have h10 : X.val 1 0 = 0 := by
    have h : ((X.val 1 0 : ℤ) : ℚ) = 0 := hP'.1
    exact_mod_cast h
  have h20 : X.val 2 0 = 0 := by
    have h : ((X.val 2 0 : ℤ) : ℚ) = 0 := hP'.2
    exact_mod_cast h
  obtain ⟨Y, hY⟩ : ∃ Y : IntegralGL3, Y = X⁻¹ := ⟨_, rfl⟩
  have hXY : X.val * Y.val = 1 := by
    rw [hY]
    exact Units.mul_inv X
  have hYX : Y.val * X.val = 1 := by
    rw [hY]
    exact Units.inv_mul X
  have hPY : InLineParabolic (integralRational Y) := by
    rw [hY, map_inv]
    exact inLine_inv hP'
  have hY10 : Y.val 1 0 = 0 := by
    have h : ((Y.val 1 0 : ℤ) : ℚ) = 0 := hPY.1
    exact_mod_cast h
  have hY20 : Y.val 2 0 = 0 := by
    have h : ((Y.val 2 0 : ℤ) : ℚ) = 0 := hPY.2
    exact_mod_cast h
  have e : ∀ i j, X.val i 0 * Y.val 0 j + X.val i 1 * Y.val 1 j + X.val i 2 * Y.val 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := fun i j => by
    rw [← hXY, Matrix.mul_apply, Fin.sum_univ_three]
  have e' : ∀ i j, Y.val i 0 * X.val 0 j + Y.val i 1 * X.val 1 j + Y.val i 2 * X.val 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := fun i j => by
    rw [← hYX, Matrix.mul_apply, Fin.sum_univ_three]
  have f00 : X.val 0 0 * Y.val 0 0 = 1 := by
    simpa [hY10, hY20] using e 0 0
  have f11 : X.val 1 1 * Y.val 1 1 + X.val 1 2 * Y.val 2 1 = 1 := by
    simpa [h10] using e 1 1
  have f12 : X.val 1 1 * Y.val 1 2 + X.val 1 2 * Y.val 2 2 = 0 := by
    simpa [h10] using e 1 2
  have f21 : X.val 2 1 * Y.val 1 1 + X.val 2 2 * Y.val 2 1 = 0 := by
    simpa [h20] using e 2 1
  have f22 : X.val 2 1 * Y.val 1 2 + X.val 2 2 * Y.val 2 2 = 1 := by
    simpa [h20] using e 2 2
  have g11 : Y.val 1 1 * X.val 1 1 + Y.val 1 2 * X.val 2 1 = 1 := by
    simpa [hY10] using e' 1 1
  have g12 : Y.val 1 1 * X.val 1 2 + Y.val 1 2 * X.val 2 2 = 0 := by
    simpa [hY10] using e' 1 2
  have g21 : Y.val 2 1 * X.val 1 1 + Y.val 2 2 * X.val 2 1 = 0 := by
    simpa [hY20] using e' 2 1
  have g22 : Y.val 2 1 * X.val 1 2 + Y.val 2 2 * X.val 2 2 = 1 := by
    simpa [hY20] using e' 2 2
  obtain ⟨B, hB00, hB01, hB10, hB11⟩ : ∃ B : GLTwo ℤ, B.val 0 0 = X.val 1 1 ∧
      B.val 0 1 = X.val 1 2 ∧ B.val 1 0 = X.val 2 1 ∧ B.val 1 1 = X.val 2 2 :=
    ⟨⟨!![X.val 1 1, X.val 1 2; X.val 2 1, X.val 2 2],
      !![Y.val 1 1, Y.val 1 2; Y.val 2 1, Y.val 2 2],
      by rw [Matrix.one_fin_two, Matrix.mul_fin_two, f11, f12, f21, f22],
      by rw [Matrix.one_fin_two, Matrix.mul_fin_two, g11, g12, g21, g22]⟩,
      rfl, rfl, rfl, rfl⟩
  have hd := (reductionThree_eq_one_iff X).mp hred
  have d00 : (3 : ℤ) ∣ X.val 0 0 - 1 := by simpa using hd 0 0
  have d01 : (3 : ℤ) ∣ X.val 0 1 := by simpa using hd 0 1
  have d02 : (3 : ℤ) ∣ X.val 0 2 := by simpa using hd 0 2
  have d11 : (3 : ℤ) ∣ X.val 1 1 - 1 := by simpa using hd 1 1
  have d12 : (3 : ℤ) ∣ X.val 1 2 := by simpa using hd 1 2
  have d21 : (3 : ℤ) ∣ X.val 2 1 := by simpa using hd 2 1
  have d22 : (3 : ℤ) ∣ X.val 2 2 - 1 := by simpa using hd 2 2
  have h00 : X.val 0 0 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one f00 with h | h
    · exact h
    · omega
  obtain ⟨k1, hk1⟩ := d01
  obtain ⟨k2, hk2⟩ := d02
  have hBred : reduction 3 B = 1 := by
    rw [reduction_eq_one_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hB00, hB01, hB10, hB11] <;> omega
  refine ⟨(k1, k2), B, hBred, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineUnipotent_val, lineLevi_one_val, Matrix.mul_apply, Fin.sum_univ_three,
      hB00, hB01, hB10, hB11, hk1, hk2, h10, h20, h00]

/-- The line base frame: radical `u(3 r)`, Levi `diag(1, B)` acting by `(B⁻¹)ᵀ`. -/
def lineBase : BaseFrame where
  parab := lineParabolic ℚ
  rad := lineRad
  rad_injective := lineRad_injective
  rad_mem := fun x => ⟨rfl, rfl⟩
  rad_unitri := fun x => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  levi := lineLeviInt
  levi_mem := fun B => inLine_map (Int.castRingHom ℚ) (lineLevi 1 B) (lineLevi_mem 1 B)
  mat := invTranspose
  conj := fun B r => by
    have key := line_conj_core (R := ℚ) B (3 * r.1) (3 * r.2)
      (3 * (leviAct (invTranspose B) r).1) (3 * (leviAct (invTranspose B) r).2)
      (by simp only [leviAct, invTranspose_apply]; ring)
      (by simp only [leviAct, invTranspose_apply]; ring)
    rw [mul_inv_eq_iff_eq_mul]
    exact key
  disjoint := fun B r h => lineLevi_eq_unipotent (s := 3 * r.1) (t := 3 * r.2) h
  radInt := fun ℓ => lineUnipotent (3 * ℓ.1) (3 * ℓ.2)
  radInt_map := fun ℓ => by
    show integralRational (lineUnipotent (3 * ℓ.1) (3 * ℓ.2)) = _
    rw [integralRational_lineUnipotent]
    push_cast
    rfl
  radInt_red := fun ℓ => line_red_unipotent _ _ (dvd_mul_right 3 ℓ.1) (dvd_mul_right 3 ℓ.2)
  levi_red := fun B hB => line_levi_red B ((reduction_invTranspose 3 B).mp hB)
  decomp := fun X hred hP => by
    obtain ⟨ℓ, B, hB, hX⟩ := line_decomp X hred hP
    exact ⟨ℓ, B, (reduction_invTranspose 3 B).mpr hB, Or.inr hX⟩

/-- The two base frames, indexed by the side. -/
def sideBase : Side → BaseFrame
  | .plane => planeBase
  | .line => lineBase

theorem sideBase_parab (s : Side) : (sideBase s).parab = parabolic s := by
  cases s <;> rfl

end FlagFrames

open FlagFrames

/-- Every rational flag has an integral representative. -/
theorem exists_integral_representative (s : Side) (x : Flags s) :
    ∃ g : IntegralGL3, (QuotientGroup.mk (integralRational g) : Flags s) = x :=
  TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags.integral_representative s x

/-- The frame of the flag `QuotientGroup.mk g`, `g ∈ GL₃(ℤ)`, on the side `s`: the radical is
`r ↦ g u(3 r) g⁻¹` and the Levi group is `GL₂(ℤ)` embedded as `g diag(B, 1) g⁻¹` (plane) resp.
`g diag(1, B) g⁻¹` (line). -/
def sideFrame (s : Side) (g : IntegralGL3) : RadicalFrame :=
  (sideBase s).frame (integralRational g)

/-- The frame of a plane flag. -/
def planeFrame (g : IntegralGL3) : RadicalFrame := sideFrame .plane g

/-- The frame of a line flag. -/
def lineFrame (g : IntegralGL3) : RadicalFrame := sideFrame .line g

theorem sideFrame_levi (s : Side) (g : IntegralGL3) : (sideFrame s g).Levi = GLTwo ℤ := by
  cases s <;> rfl

theorem planeFrame_radical_apply (g : IntegralGL3) (x : Multiplicative (ℚ × ℚ)) :
    (planeFrame g).radical x = integralRational g *
      planeUnipotent (3 * x.toAdd.1) (3 * x.toAdd.2) * (integralRational g)⁻¹ := rfl

theorem lineFrame_radical_apply (g : IntegralGL3) (x : Multiplicative (ℚ × ℚ)) :
    (lineFrame g).radical x = integralRational g *
      lineUnipotent (3 * x.toAdd.1) (3 * x.toAdd.2) * (integralRational g)⁻¹ := rfl

theorem planeFrame_leviHom_apply (g : IntegralGL3) (B : GLTwo ℤ) :
    (planeFrame g).leviHom B = integralRational g * integralRational (planeLevi B 1) *
      (integralRational g)⁻¹ := rfl

theorem lineFrame_leviHom_apply (g : IntegralGL3) (B : GLTwo ℤ) :
    (lineFrame g).leviHom B = integralRational g * integralRational (lineLevi 1 B) *
      (integralRational g)⁻¹ := rfl

theorem planeFrame_leviMatrix (g : IntegralGL3) (B : GLTwo ℤ) :
    (planeFrame g).leviMatrix B = B := rfl

theorem lineFrame_leviMatrix (g : IntegralGL3) (B : GLTwo ℤ) :
    (lineFrame g).leviMatrix B = invTranspose B := rfl

/-- (3a) The level-`N` lattice, `3 ∣ N`, lies in the arithmetic stabilizer of the flag. -/
theorem sideFrame_lattice_le (s : Side) (g : IntegralGL3) (N : ℕ) (hN : 3 ∣ N) :
    (sideFrame s g).lattice N ≤ rationalLevel ⊓
      MulAction.stabilizer RationalGL3 (QuotientGroup.mk (integralRational g) : Flags s) := by
  cases s
  · exact planeBase.lattice_le_flagLevel g N hN
  · exact lineBase.lattice_le_flagLevel g N hN

theorem sideFrame_lattice_le_rationalLevel (s : Side) (g : IntegralGL3) (N : ℕ) (hN : 3 ∣ N) :
    (sideFrame s g).lattice N ≤ rationalLevel :=
  (sideFrame_lattice_le s g N hN).trans inf_le_left

theorem sideFrame_lattice_le_stabilizer (s : Side) (g : IntegralGL3) (N : ℕ) (hN : 3 ∣ N) :
    (sideFrame s g).lattice N ≤
      MulAction.stabilizer RationalGL3 (QuotientGroup.mk (integralRational g) : Flags s) :=
  (sideFrame_lattice_le s g N hN).trans inf_le_right

/-- (3b) The lattice of level `3 K` has finite relative index in `Γ ⊓ Stab(x)`. -/
theorem sideFrame_relIndex_ne_zero (s : Side) (g : IntegralGL3) (K : ℕ) (hK : 0 < K) :
    ((sideFrame s g).lattice (3 * K)).relIndex (rationalLevel ⊓
      MulAction.stabilizer RationalGL3 (QuotientGroup.mk (integralRational g) : Flags s)) ≠ 0 := by
  cases s
  · exact planeBase.relIndex_flagLevel g K hK
  · exact lineBase.relIndex_flagLevel g K hK

/-- (3b) in the form required by `exists_primitive_of_finiteIndex`. -/
theorem sideFrame_finite_quotient (s : Side) (g : IntegralGL3) (K : ℕ) (hK : 0 < K) :
    Finite (Quotient (QuotientGroup.rightRel (((sideFrame s g).lattice (3 * K)).subgroupOf
      (rationalLevel ⊓ MulAction.stabilizer RationalGL3
        (QuotientGroup.mk (integralRational g) : Flags s))))) :=
  finite_of_relIndex_ne_zero _ _ (sideFrame_relIndex_ne_zero s g K hK)

/-- The radical points lie in the conjugate of the upper unitriangular group by `g`. -/
theorem sideFrame_radical_mem_conjUnitri (s : Side) (g : IntegralGL3) (r : ℚ × ℚ) :
    (sideFrame s g).radical (Multiplicative.ofAdd r) ∈
      TernaryPeriodPolynomials.FlagExactness.conjUnitri (integralRational g) :=
  (sideBase s).radical_mem_conjUnitri (integralRational g) _

/-- The data of a flag: an integral representative whose frame has the properties (3a), (3b). -/
theorem exists_sideFrame (s : Side) (x : Flags s) :
    ∃ g : IntegralGL3, (QuotientGroup.mk (integralRational g) : Flags s) = x ∧
      (sideFrame s g).lattice 3 ≤ rationalLevel ⊓ MulAction.stabilizer RationalGL3 x ∧
      ∀ K : ℕ, 0 < K → ((sideFrame s g).lattice (3 * K)).relIndex
        (rationalLevel ⊓ MulAction.stabilizer RationalGL3 x) ≠ 0 := by
  obtain ⟨g, rfl⟩ := exists_integral_representative s x
  exact ⟨g, rfl, sideFrame_lattice_le s g 3 (dvd_refl 3),
    fun K hK => sideFrame_relIndex_ne_zero s g K hK⟩

/-! ### Standard-position Levi matrices -/

/-- (R1) In standard position the Levi element lies in the rational parabolic subgroup. -/
theorem sideFrame_levi_std_mem (s : Side) (g : IntegralGL3) (m : GLTwo ℤ) :
    (integralRational g)⁻¹ * (sideFrame s g).leviHom m * integralRational g ∈ parabolic s := by
  have h : (integralRational g)⁻¹ * (sideFrame s g).leviHom m * integralRational g =
      integralRational ((sideBase s).levi m) := by
    show (integralRational g)⁻¹ * (integralRational g * integralRational ((sideBase s).levi m) *
      (integralRational g)⁻¹) * integralRational g = _
    exact inv_conj_conj _ _
  rw [h]
  cases s
  · exact planeBase.levi_mem m
  · exact lineBase.levi_mem m

/-- (R2), plane side: the inverse conjugation of the real radical by the standard-position Levi
element is the radical point moved by `(leviMatrix m)⁻¹`. -/
theorem planeFrame_levi_std_real (g : IntegralGL3) (m : GLTwo ℤ) (r : ℝ × ℝ) :
    (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((integralRational g)⁻¹ * (planeFrame g).leviHom m * integralRational g))⁻¹ *
      planeUnipotent (3 * r.1) (3 * r.2) *
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((integralRational g)⁻¹ * (planeFrame g).leviHom m * integralRational g) =
    planeUnipotent (3 * (realActCol ((planeFrame g).leviMatrix m)⁻¹ r).1)
      (3 * (realActCol ((planeFrame g).leviMatrix m)⁻¹ r).2) := by
  have hP : (integralRational g)⁻¹ * (planeFrame g).leviHom m * integralRational g =
      integralRational (planeLevi m 1) := by
    show (integralRational g)⁻¹ * (integralRational g * integralRational (planeLeviInt m) *
      (integralRational g)⁻¹) * integralRational g = _
    exact inv_conj_conj _ _
  rw [hP, map_algebraMap_integralRational]
  exact plane_real_conj m r

/-- (R2), line side. -/
theorem lineFrame_levi_std_real (g : IntegralGL3) (m : GLTwo ℤ) (r : ℝ × ℝ) :
    (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((integralRational g)⁻¹ * (lineFrame g).leviHom m * integralRational g))⁻¹ *
      lineUnipotent (3 * r.1) (3 * r.2) *
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((integralRational g)⁻¹ * (lineFrame g).leviHom m * integralRational g) =
    lineUnipotent (3 * (realActCol ((lineFrame g).leviMatrix m)⁻¹ r).1)
      (3 * (realActCol ((lineFrame g).leviMatrix m)⁻¹ r).2) := by
  have hP : (integralRational g)⁻¹ * (lineFrame g).leviHom m * integralRational g =
      integralRational (lineLevi 1 m) := by
    show (integralRational g)⁻¹ * (integralRational g * integralRational (lineLeviInt m) *
      (integralRational g)⁻¹) * integralRational g = _
    exact inv_conj_conj _ _
  rw [hP, map_algebraMap_integralRational]
  exact line_real_conj m r

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
