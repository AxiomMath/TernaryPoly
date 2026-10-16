module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Fiber.Permutations

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinarySignedFibers
open OrdinaryCovectors OrdinaryCovectorOrbits OrdinaryPolynomialNorm OrdinaryFiberPermutations

/-- Negate the indicated row coordinate. -/
def flipRow (i : Fin 3) (r : Covector) : Covector := fun j => if j=i then -r j else r j
/-- Negate the indicated polynomial variable. -/
def flipPoly (i : Fin 3) : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ (fun j => if j=i then -X j else X j)

theorem flipRow_conjugate (i : Fin 3) (r : Covector) :
    flipRow i r=permuteRow (Equiv.swap i 2)
      (sign3 (permuteRow (Equiv.swap i 2) r)) := by
  fin_cases i <;> funext j <;> fin_cases j <;>
    simp [flipRow,permuteRow,sign3,Equiv.swap_apply_def]

theorem flipPoly_conjugate (i : Fin 3) :
    (permutePoly (Equiv.swap i 2)).comp
      (D3.comp (permutePoly (Equiv.swap i 2)))=flipPoly i := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [permutePoly,flipPoly,D3,AlgHom.comp_apply,Equiv.swap_apply_def]

/-- Permutation equivariance transports the third sign equation to each coordinate. -/
theorem flip_equivariance (F : Covector → TernaryPolynomial)
    (hp : ∀ π r,F (permuteRow π r)=permutePoly π (F r))
    (h3 : ∀ r,F (sign3 r)= -D3 (F r)) (i : Fin 3) (r : Covector) :
    F (flipRow i r)= -flipPoly i (F r) := by
  rw [flipRow_conjugate,hp,h3,hp,map_neg]
  congr 1
  exact DFunLike.congr_fun (flipPoly_conjugate i) (F r)

/-- A finite set specifies every independent diagonal sign. -/
def signRow (s : Finset (Fin 3)) (r : Covector) : Covector :=
  fun i => if i∈s then -r i else r i
def signPoly (s : Finset (Fin 3)) : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ (fun i => if i∈s then -X i else X i)

theorem signRow_insert (s : Finset (Fin 3)) (i : Fin 3) (hi : i∉s) (r : Covector) :
    signRow (insert i s) r=flipRow i (signRow s r) := by
  funext j
  by_cases hji : j=i
  · subst j
    simp [signRow,flipRow,hi]
  · simp [signRow,flipRow,hji]

theorem signPoly_insert (s : Finset (Fin 3)) (i : Fin 3) (hi : i∉s) :
    (flipPoly i).comp (signPoly s)=signPoly (insert i s) := by
  apply MvPolynomial.algHom_ext
  intro j
  by_cases hji : j=i
  · subst j
    simp [flipPoly,signPoly,hi,AlgHom.comp_apply]
  · by_cases hjs : j∈s <;> simp [flipPoly,signPoly,hji,hjs,AlgHom.comp_apply]

theorem signPoly_empty : signPoly ∅=AlgHom.id ℚ TernaryPolynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [signPoly]

/-- Every diagonal sign has precisely the product-of-signs character. -/
theorem sign_equivariance (F : Covector → TernaryPolynomial)
    (hf : ∀ i r,F (flipRow i r)= -flipPoly i (F r)) :
    ∀ s r,F (signRow s r)=(-1 : ℚ)^s.card • signPoly s (F r) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro r
    rw [signPoly_empty]
    change F r=(1 : ℚ) • F r
    simp
  | @insert i s hi ih =>
    intro r
    rw [signRow_insert s i hi,hf,ih,map_smul]
    have he := DFunLike.congr_fun (signPoly_insert s i hi) (F r)
    change flipPoly i (signPoly s (F r))=signPoly (insert i s) (F r) at he
    rw [he,Finset.card_insert_of_notMem hi,pow_succ,mul_smul,neg_one_smul,smul_neg]

/-- The complete coefficient equation for every signed coordinate permutation. -/
theorem signed_permutation_equivariance (F : Covector → TernaryPolynomial)
    (hp : ∀ π r,F (permuteRow π r)=permutePoly π (F r))
    (h3 : ∀ r,F (sign3 r)= -D3 (F r))
    (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) (r : Covector) :
    F (permuteRow π (signRow s r))=
      (-1 : ℚ)^s.card • permutePoly π (signPoly s (F r)) := by
  rw [hp,sign_equivariance F (flip_equivariance F hp h3),map_smul]

/-- Actual seed values satisfy all48 signed-permutation equations. -/
theorem seedValue_signed_permutation {f P Q : TernaryPolynomial}
    (h : SymmetricSeedData f P Q) (hc : C f=f) (hs : S f=f)
    (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) (r : Covector) :
    OrdinarySeedFibers.seedValue f P Q (permuteRow π (signRow s r))=
      (-1 : ℚ)^s.card • permutePoly π (signPoly s (OrdinarySeedFibers.seedValue f P Q r)) :=
  signed_permutation_equivariance _ (seedValue_permutation h hc hs)
    (OrdinarySeedFibers.seedValue_sign3 h) s π r

end TernaryPoly.OrdinarySignedFibers
