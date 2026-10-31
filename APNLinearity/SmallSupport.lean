module

public import APNLinearity.DerivativeGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.SmallSupport
noncomputable section

/-- The polynomial used on the residue class `4ℤ + 2`. -/
theorem polynomialP_nonnegative (a t : ℤ) (ha : 4 ∣ a) (ht : t % 4 = 2) :
    0 ≤ polynomialP a t := by
  have hp : (t + a) % 4 = 2 := by omega
  have hm : (t - a) % 4 = 2 := by omega
  have hsq (u : ℤ) (hu : u % 4 = 2) : 4 ≤ u ^ 2 := by
    have : u ≤ -2 ∨ 2 ≤ u := by omega
    rcases this with h | h <;> nlinarith
  exact mul_nonneg (sub_nonneg.mpr (hsq _ hp)) (sub_nonneg.mpr (hsq _ hm))

private theorem closest_square_ordered (N a b : ℤ) (hN : 16 ∣ N)
    (ha : 0 ≤ a) (hab : a < b) (ha4 : 4 ∣ a) (hb4 : 4 ∣ b)
    (he : (b ^ 2 - N) ^ 2 = (a ^ 2 - N) ^ 2)
    (hm : (a ^ 2 - N) ^ 2 ≤ ((a + 4) ^ 2 - N) ^ 2) : False := by
  have hs : a ^ 2 < b ^ 2 := by nlinarith
  have hf : (b ^ 2 - a ^ 2) * (b ^ 2 + a ^ 2 - 2 * N) = 0 := by
    nlinarith [he]
  have hmid : b ^ 2 + a ^ 2 = 2 * N := by
    have := (mul_eq_zero.mp hf).resolve_left (by omega)
    omega
  have hstep : a + 4 ≤ b := by omega
  have hne : b ≠ a + 4 := by
    intro hb
    obtain ⟨k, rfl⟩ := ha4
    obtain ⟨q, rfl⟩ := hN
    rw [hb] at hmid
    have : 2 * (k ^ 2 + k) + 1 = 2 * q := by nlinarith [hmid]
    omega
  have hgap : a + 8 ≤ b := by omega
  have hleft : 0 < (a + 4) ^ 2 - a ^ 2 := by nlinarith
  have hright : 0 < b ^ 2 - (a + 4) ^ 2 := by nlinarith
  have hprod := mul_pos hleft hright
  have hid : ((a + 4) ^ 2 - N) ^ 2 - (a ^ 2 - N) ^ 2 =
      -(((a + 4) ^ 2 - a ^ 2) * (b ^ 2 - (a + 4) ^ 2)) := by
    nlinarith [congrArg (fun z : ℤ => ((a + 4) ^ 2 - a ^ 2) * z) hmid]
  linarith

/-- A unique closest square among squares of nonnegative multiples of four. -/
theorem closest_multiple_four_square (N : ℤ) (hN : 16 ∣ N) :
    ∃ a : ℤ, 0 ≤ a ∧ 4 ∣ a ∧
      (∀ b : ℤ, 4 ∣ b → (a ^ 2 - N) ^ 2 ≤ (b ^ 2 - N) ^ 2) ∧
      (∀ b : ℤ, 4 ∣ b → (b ^ 2 - N) ^ 2 = (a ^ 2 - N) ^ 2 → b ^ 2 = a ^ 2) := by
  let f : ℕ → ℕ := fun k => (((4 * (k : ℤ)) ^ 2 - N) ^ 2).toNat
  let a : ℤ := 4 * ((Function.argmin f : ℕ) : ℤ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha4 : 4 ∣ a := ⟨_, rfl⟩
  have hm (b : ℤ) (hb : 4 ∣ b) : (a ^ 2 - N) ^ 2 ≤ (b ^ 2 - N) ^ 2 := by
    obtain ⟨k, rfl⟩ := hb
    have h := le_of_not_gt (Function.not_lt_argmin f k.natAbs)
    dsimp [f, a] at h ⊢
    have hs : (4 * (k.natAbs : ℤ)) ^ 2 = (4 * k) ^ 2 := by
      rw [mul_pow, mul_pow, Int.natCast_natAbs, sq_abs]
    rw [hs] at h
    have hpos := sq_nonneg ((4 * k) ^ 2 - N)
    have hpos' := sq_nonneg ((4 * ((Function.argmin f : ℕ) : ℤ)) ^ 2 - N)
    omega
  refine ⟨a, ha, ha4, hm, ?_⟩
  intro b hb he
  have hb4 : 4 ∣ |b| := (dvd_abs 4 b).2 hb
  have habs : (|b| ^ 2 - N) ^ 2 = (a ^ 2 - N) ^ 2 := by simpa using he
  rcases lt_trichotomy a |b| with hlt | heq | hgt
  · exact (closest_square_ordered N a |b| hN ha hlt ha4 hb4 habs
      (hm (a + 4) (dvd_add ha4 (dvd_refl 4)))).elim
  · nlinarith [sq_abs b]
  · have hh := hm (|b| + 4) (dvd_add hb4 (dvd_refl 4))
    rw [← habs] at hh
    exact (closest_square_ordered N |b| a hN (abs_nonneg b) hgt hb4 ha4 habs.symm hh).elim

/-- The arithmetic rigidity step of the two-point argument. -/
theorem arithmetic_rigidity : ∀ (N : ℤ), 16 ≤ N → 16 ∣ N → ∀ (p : ℕ), 1 ≤ p →
    ∀ (X Y : Fin p → ℤ),
      (∀ i, X i % 4 = 2 ∧ Y i % 4 = 0) →
      arithmeticMean (fun i => X i ^ 2) = (N : ℝ) - 4 →
      arithmeticMean (fun i => Y i ^ 2) = (N : ℝ) →
      arithmeticMean (fun i => X i ^ 4 + Y i ^ 4) = 2 * (N : ℝ) ^ 2 + 8 * N - 48 →
      IsSquare N ∧ ∀ i, Y i ^ 2 = N := by
  intro N _ hN p hp X Y hxy hX hY hfour
  obtain ⟨a, _, ha4, hmin, hunique⟩ := closest_multiple_four_square N hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hX' : (∑ i, ((X i : ℝ) ^ 2)) = p * ((N : ℝ) - 4) := by
    simpa only [arithmeticMean, Int.cast_pow, mul_comm] using (div_eq_iff (ne_of_gt hpR)).mp hX
  have hY' : (∑ i, ((Y i : ℝ) ^ 2)) = p * (N : ℝ) := by
    simpa only [arithmeticMean, Int.cast_pow, mul_comm] using
      (div_eq_iff (ne_of_gt hpR)).mp hY
  have hfour' : (∑ i, ((X i : ℝ) ^ 4 + (Y i : ℝ) ^ 4)) =
      p * (2 * (N : ℝ) ^ 2 + 8 * N - 48) := by
    simpa only [arithmeticMean, Int.cast_add, Int.cast_pow, mul_comm] using
      (div_eq_iff (ne_of_gt hpR)).mp hfour
  let D (i : Fin p) : ℝ := (polynomialP a (X i) : ℝ) +
    (((Y i : ℝ) ^ 2 - N) ^ 2 - ((a : ℝ) ^ 2 - N) ^ 2)
  have hD (i : Fin p) : 0 ≤ D i := by
    have hP : (0 : ℝ) ≤ (polynomialP a (X i) : ℝ) := by
      exact_mod_cast polynomialP_nonnegative a (X i) ha4 (hxy i).1
    have hM : ((a : ℝ) ^ 2 - N) ^ 2 ≤ ((Y i : ℝ) ^ 2 - N) ^ 2 := by
      exact_mod_cast hmin (Y i) (Int.dvd_of_emod_eq_zero (hxy i).2)
    dsimp [D]
    linarith
  have hsum : ∑ i, D i = 0 := by
    have hi (i : Fin p) : D i = (X i : ℝ) ^ 4 + (Y i : ℝ) ^ 4 -
        2 * ((a : ℝ) ^ 2 + 4) * (X i : ℝ) ^ 2 -
        2 * (N : ℝ) * (Y i : ℝ) ^ 2 +
        ((a : ℝ) ^ 2 - 4) ^ 2 + (N : ℝ) ^ 2 - ((a : ℝ) ^ 2 - N) ^ 2 := by
      dsimp [D, polynomialP]
      push_cast
      ring
    simp only [hi, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← Finset.sum_add_distrib, hfour', hX', hY']
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have heach (i : Fin p) : Y i ^ 2 = a ^ 2 := by
    have hi : D i = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hD j)).mp hsum i
      (Finset.mem_univ i)
    have hP : (0 : ℝ) ≤ (polynomialP a (X i) : ℝ) := by
      exact_mod_cast polynomialP_nonnegative a (X i) ha4 (hxy i).1
    have hM := hmin (Y i) (Int.dvd_of_emod_eq_zero (hxy i).2)
    have hMR : ((a : ℝ) ^ 2 - N) ^ 2 ≤ ((Y i : ℝ) ^ 2 - N) ^ 2 := by exact_mod_cast hM
    have he : ((Y i : ℝ) ^ 2 - N) ^ 2 = ((a : ℝ) ^ 2 - N) ^ 2 := by
      dsimp [D] at hi
      linarith
    apply hunique (Y i) (Int.dvd_of_emod_eq_zero (hxy i).2)
    exact_mod_cast he
  have hNa : N = a ^ 2 := by
    have hr (i : Fin p) : (Y i : ℝ) ^ 2 = (a : ℝ) ^ 2 := by exact_mod_cast heach i
    simp_rw [hr] at hY'
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hY'
    have : (N : ℝ) = (a : ℝ) ^ 2 := by nlinarith
    exact_mod_cast this
  exact ⟨⟨a, by simpa [pow_two] using hNa⟩, fun i => (heach i).trans hNa.symm⟩

/-- Reindex the two equally sized character classes by the tuples in the lemma. -/
theorem arithmetic_rigidity_finsets {ι : Type*} (S T : Finset ι) (α : ι → ℤ)
    (N : ℤ) (hN : 16 ≤ N) (hN16 : 16 ∣ N) (hpos : 0 < S.card)
    (hcard : T.card = S.card)
    (hS : ∀ x ∈ S, α x % 4 = 2) (hT : ∀ x ∈ T, α x % 4 = 0)
    (hS2 : (∑ x ∈ S, α x ^ 2) = S.card * (N - 4))
    (hT2 : (∑ x ∈ T, α x ^ 2) = S.card * N)
    (h4 : (∑ x ∈ S, α x ^ 4) + (∑ x ∈ T, α x ^ 4) =
      S.card * (2 * N ^ 2 + 8 * N - 48)) :
    IsSquare N ∧ ∀ x ∈ T, α x ^ 2 = N := by
  classical
  let eS := S.equivFin.symm
  let eT := (Finset.equivFinOfCardEq hcard).symm
  let X : Fin S.card → ℤ := fun i => α (eS i)
  let Y : Fin S.card → ℤ := fun i => α (eT i)
  have sumS (f : ℤ → ℝ) : (∑ i, f (X i)) = ∑ x ∈ S, f (α x) := by
    calc
      _ = ∑ x : S, f (α x) := Fintype.sum_equiv eS _ _ (fun _ => rfl)
      _ = _ := Finset.sum_coe_sort S (fun x => f (α x))
  have sumT (f : ℤ → ℝ) : (∑ i, f (Y i)) = ∑ x ∈ T, f (α x) := by
    calc
      _ = ∑ x : T, f (α x) := Fintype.sum_equiv eT _ _ (fun _ => rfl)
      _ = _ := Finset.sum_coe_sort T (fun x => f (α x))
  have hp : (S.card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hSX : arithmeticMean (fun i => X i ^ 2) = (N : ℝ) - 4 := by
    unfold arithmeticMean
    rw [sumS (fun z => (z ^ 2 : ℤ))]
    apply (div_eq_iff hp).2
    have := congrArg (fun z : ℤ => (z : ℝ)) hS2
    simpa [mul_comm] using this
  have hTY : arithmeticMean (fun i => Y i ^ 2) = (N : ℝ) := by
    unfold arithmeticMean
    rw [sumT (fun z => (z ^ 2 : ℤ))]
    apply (div_eq_iff hp).2
    have := congrArg (fun z : ℤ => (z : ℝ)) hT2
    simpa [mul_comm] using this
  have hfour : arithmeticMean (fun i => X i ^ 4 + Y i ^ 4) =
      2 * (N : ℝ) ^ 2 + 8 * N - 48 := by
    unfold arithmeticMean
    simp only [Int.cast_add, Finset.sum_add_distrib]
    rw [sumS (fun z => (z ^ 4 : ℤ)), sumT (fun z => (z ^ 4 : ℤ))]
    apply (div_eq_iff hp).2
    have := congrArg (fun z : ℤ => (z : ℝ)) h4
    simpa [mul_comm] using this
  obtain ⟨hsq, he⟩ := arithmetic_rigidity N hN hN16 S.card hpos X Y
    (fun i => ⟨hS _ (eS i).property, hT _ (eT i).property⟩) hSX hTY hfour
  refine ⟨hsq, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := eT.surjective ⟨x, hx⟩
  simpa only [Y, hi] using he i

end
end APNLinearity.SmallSupport

open scoped BigOperators

namespace APNLinearity.SmallSupport
noncomputable section
open _root_.APNLinearity.Fourier Sidon

abbrev CharacterSpace (n m : ℕ) := BinarySpace n × BinarySpace m

def characterDot {n m : ℕ} (u z : CharacterSpace n m) : Bit := binaryDot u.1 z.1 + binaryDot u.2 z.2

@[simp] theorem characterDot_zero_left {n m : ℕ} (z : CharacterSpace n m) : characterDot 0 z = 0 := by
  simp [characterDot]

@[simp] theorem characterDot_zero_right {n m : ℕ} (u : CharacterSpace n m) : characterDot u 0 = 0 := by
  simp [characterDot]

@[simp] theorem characterDot_add_left {n m : ℕ} (u v z : CharacterSpace n m) :
    characterDot (u + v) z = characterDot u z + characterDot v z := by
  simp only [characterDot, Prod.fst_add, Prod.snd_add, dot_add_left]
  ring

@[simp] theorem characterDot_add_right {n m : ℕ} (u z w : CharacterSpace n m) :
    characterDot u (z + w) = characterDot u z + characterDot u w := by
  simp only [characterDot, Prod.fst_add, Prod.snd_add, dot_add_right]
  ring

theorem characterDot_comm {n m : ℕ} (u z : CharacterSpace n m) :
    characterDot u z = characterDot z u := by simp [characterDot, dot_comm]

def characterFunctional {n m : ℕ} (u : CharacterSpace n m) : CharacterSpace n m →ₗ[Bit] Bit where
  toFun := characterDot u
  map_add' := characterDot_add_right u
  map_smul' c z := by rcases bit_eq_zero_or_one c with rfl | rfl <;> simp

theorem characterDot_sum {n m : ℕ} {ι : Type*} (u : CharacterSpace n m)
    (S : Finset ι) (f : ι → CharacterSpace n m) :
    characterDot u (∑ i ∈ S, f i) = ∑ i ∈ S, characterDot u (f i) :=
  map_sum (characterFunctional u) _ _

@[simp] theorem product_add_self {n m : ℕ} (x : CharacterSpace n m) : x + x = 0 := by
  ext <;> simp

theorem product_character_comm {n m : ℕ} (u z : CharacterSpace n m) :
    productCharacter u z = productCharacter z u := congrArg bitSign (characterDot_comm u z)

theorem product_character_add_left {n m : ℕ} (u v z : CharacterSpace n m) :
    productCharacter (u + v) z = productCharacter u z * productCharacter v z := by
  change bitSign (characterDot (u + v) z) = _
  rw [characterDot_add_left, sign_add]
  rfl

/-- Counting negative signs, with their parity expressed by their sum in `Bit`. -/
theorem sign_sum_congruence {ι : Type*} (S : Finset ι) (f : ι → Bit) :
    (∑ i ∈ S, bitSign (f i)) % 4 =
      ((S.card : ℤ) - 2 * ((∑ i ∈ S, f i).val : ℤ)) % 4 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    rcases bit_eq_zero_or_one (f i) with hf | hf <;>
      rcases bit_eq_zero_or_one (∑ j ∈ S, f j) with hs | hs
    all_goals simp only [hf, hs, sign_zero, sign_one, zero_add, add_zero,
      bit_add_self, Nat.cast_add, Nat.cast_one] at *
    all_goals norm_num only [show (0 : Bit).val = 0 from rfl,
      show (1 : Bit).val = 1 from rfl, Nat.cast_zero, Nat.cast_one] at *
    all_goals omega

theorem product_sum_congruence {n m : ℕ} (A : Finset (CharacterSpace n m))
    (u : CharacterSpace n m) :
    productCharacterSum A u % 4 =
      ((A.card : ℤ) - 2 * (characterDot u (∑ z ∈ A, z)).val) % 4 := by
  rw [characterDot_sum]
  exact sign_sum_congruence A (characterDot u)

/-- Orthogonality, including a twist by the sum of the deleted support. -/
theorem product_twisted_second {n m : ℕ} (A : Finset (CharacterSpace n m))
    (s : CharacterSpace n m) :
    (∑ u, productCharacter u s * productCharacterSum A u ^ 2) =
      (spaceSize n : ℤ) * spaceSize m *
        ((A ×ˢ A).filter (fun z => z.1 + z.2 = s)).card := by
  classical
  have hz (x y : CharacterSpace n m) : x + y = 0 ↔ x = y := by
    constructor
    · intro h
      have := congrArg (fun z => z + y) h
      simpa [add_assoc] using this
    · rintro rfl
      simp
  have hex (u : CharacterSpace n m) :
      productCharacter u s * productCharacterSum A u ^ 2 =
        ∑ x ∈ A, ∑ y ∈ A, productCharacter u (s + (x + y)) := by
    simp only [productCharacterSum, product_character_add, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp_rw [hex]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := A), product_orthogonality, hz]
  rw [← Finset.sum_product A A (fun z =>
    if s = z.1 + z.2 then (spaceSize n : ℤ) * spaceSize m else 0)]
  rw [← Finset.sum_filter]
  simp [eq_comm, mul_comm]

theorem product_second_moment {n m : ℕ} (A : Finset (CharacterSpace n m)) :
    (∑ u, productCharacterSum A u ^ 2) = (spaceSize n : ℤ) * spaceSize m * A.card := by
  classical
  have hz (x y : CharacterSpace n m) : x + y = 0 ↔ x = y := by
    constructor
    · intro h
      have := congrArg (fun z => z + y) h
      simpa [add_assoc] using this
    · rintro rfl
      simp
  have hc : ((A ×ˢ A).filter (fun z => z.1 + z.2 = 0)).card = A.card := by
    have he : (A ×ˢ A).filter (fun z => z.1 + z.2 = 0) = A.image (fun x => (x, x)) := by
      ext z
      simp [hz, eq_comm]
      aesop
    rw [he, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  have h := product_twisted_second A 0
  simpa [productCharacter, hc] using h

/-- The two input-character classes each have half the input space. -/
theorem dot_fiber_card {n : ℕ} (d : BinarySpace n) (hd : d ≠ 0) (c : Bit) :
    2 * (Finset.univ.filter (fun a => binaryDot a d = c)).card = spaceSize n := by
  classical
  obtain ⟨b, hb⟩ := exists_dot_one hd
  have hswap : (Finset.univ.filter (fun a => binaryDot a d = 0)).card =
      (Finset.univ.filter (fun a => binaryDot a d = 1)).card := by
    apply Finset.card_bij (fun a _ => a + b)
    · intro a ha
      simpa [dot_add_left, hb] using ha
    · intro a _ a' _ h
      exact add_right_cancel h
    · intro a ha
      refine ⟨a + b, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [dot_add_left, ha, hb, bit_add_self]
  have htotal : (Finset.univ.filter (fun a => binaryDot a d = 0)).card +
      (Finset.univ.filter (fun a => binaryDot a d = 1)).card = spaceSize n := by
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun a : BinarySpace n => binaryDot a d = 0)
    have hn (a : BinarySpace n) : (¬ binaryDot a d = 0) ↔ binaryDot a d = 1 := by
      rcases bit_eq_zero_or_one (binaryDot a d) with h | h <;> simp [h]
    simpa only [hn, Finset.card_univ, card_binary] using hc
  rcases bit_eq_zero_or_one c with rfl | rfl <;> omega

end
end APNLinearity.SmallSupport

open scoped BigOperators

namespace APNLinearity.SmallSupport
noncomputable section
open _root_.APNLinearity.Fourier Sidon Normalization

theorem two_point_normalization {n : ℕ} (hn : 1 ≤ n) (F : VectorialFunction n)
    (hF : IsAPN F) (b : BinarySpace n) (hb : b ≠ 0) (a : BinarySpace n) (c : Bit)
    (hdist : hammingDistance (component F b) (affineBoolean a c) = 2) :
    ∃ (d : BinarySpace n) (H : VectorialMap n (n - 1)), d ≠ 0 ∧ H 0 = 0 ∧ H d = 0 ∧
      DerivativeBound (splitMap (indicator {0, d}) H) := by
  classical
  obtain ⟨H, hH⟩ := normalize_component n hn F hF b hb a c
  let g := component F b + affineBoolean a c
  have hg : weight g = 2 := by rwa [distance_eq_weight] at hdist
  obtain ⟨r, s, hrs, hsupport⟩ := Finset.card_eq_two.mp hg
  have hmem (x : BinarySpace n) : g x = 1 ↔ x = r ∨ x = s := by
    have := Finset.ext_iff.mp hsupport x
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] using this
  let d := r + s
  have hd : d ≠ 0 := by
    intro he
    exact hrs ((binary_add_eq_zero_iff r s).1 he)
  have hshift : (fun x => g (x + r)) = indicator {0, d} := by
    ext x
    have hr : x + r = r ↔ x = 0 := by
      constructor
      · intro he
        simpa using congrArg (fun z => z + r) he
      · rintro rfl
        simp
    have hs : x + r = s ↔ x = d := by
      constructor
      · intro he
        simpa [d, add_comm] using congrArg (fun z => z + r) he
      · rintro rfl
        simp [d, add_comm]
    by_cases hx : x = 0 ∨ x = d
    · have he : g (x + r) = 1 := (hmem _).2 (by simpa only [hr, hs] using hx)
      simp [indicator, hx, he]
    · have he : g (x + r) = 0 := (bit_eq_zero_or_one _).resolve_right
        (fun h => hx (by simpa only [hr, hs] using (hmem _).1 h))
      simp [indicator, hx, he]
  obtain ⟨e, he⟩ := exists_dot_one hd
  let J : VectorialMap n (n - 1) := fun x => H (x + r)
  have hJ : DerivativeBound (splitMap (indicator {0, d}) J) := by
    have := apn_input_translation (splitMap g H) hH r
    have heq : splitMap (indicator {0, d}) J = (fun x => splitMap g H (x + r)) := by
      funext x
      exact Prod.ext (congrFun hshift x).symm rfl
    rw [heq]
    exact this
  let σ := J d + J 0
  let L : BinarySpace n →+ Bit × BinarySpace (n - 1) :=
    { toFun := fun x => (0, binaryDot e x • σ)
      map_zero' := by simp
      map_add' := by intro x y; simp [add_smul] }
  let K : VectorialMap n (n - 1) := fun x => J x + binaryDot e x • σ + J 0
  refine ⟨d, K, hd, ?_, ?_, ?_⟩
  · simp [K]
  · simp [K, σ, he, add_assoc]
  · have ht (y : Bit × BinarySpace (n - 1)) : y + y = 0 := by ext <;> simp
    have := (affine_addition_iff ht (splitMap (indicator {0, d}) J) L (0, J 0)).2 hJ
    have heq : splitMap (indicator {0, d}) K =
        (fun x => splitMap (indicator {0, d}) J x + L x + (0, J 0)) := by
      funext x
      apply Prod.ext
      · simp [splitMap, L]
      · rfl
    rw [heq]
    exact this

theorem pair_indicator_derivative {n : ℕ} (d x : BinarySpace n) :
    derivative (indicator {0, d}) d x = 0 := by
  classical
  have hz : x + d = 0 ↔ x = d := binary_add_eq_zero_iff x d
  have hd : x + d = d ↔ x = 0 := by
    constructor
    · intro h
      simpa using congrArg (fun z => z + d) h
    · rintro rfl
      simp
  have he : indicator {0, d} (x + d) = indicator {0, d} x := by
    simp [indicator, hz, hd, or_comm]
  simp [derivative, he]

theorem sum_complement {n : ℕ} {Y : Type*} [AddCommMonoid Y]
    (E : Finset (BinarySpace n)) (f : BinarySpace n → Y) :
    (∑ x ∈ Finset.univ \ E, f x) + (∑ x ∈ E, f x) = ∑ x, f x := by
  classical
  exact Finset.sum_sdiff (Finset.subset_univ E)

/-- The normalized projected set, its sum, and the forbidden pair sum. -/
theorem two_point_graph_data {n : ℕ} (hn : 4 ≤ n) (d : BinarySpace n) (hd : d ≠ 0)
    (H : VectorialMap n (n - 1)) (h0 : H 0 = 0) (hdH : H d = 0)
    (hF : DerivativeBound (splitMap (indicator {0, d}) H)) :
    let A := restrictedGraph (Finset.univ \ {0, d}) H
    IsBinarySidon A ∧ A.card = spaceSize n - 2 ∧
      (∑ z ∈ A, z) = (d, 0) ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y ≠ (d, 0) := by
  classical
  dsimp only
  let A := restrictedGraph (Finset.univ \ {0, d}) H
  have hcard : A.card = spaceSize n - 2 := by
    dsimp [A]
    rw [Counts.restricted_graph_card, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [Ne.symm hd, spaceSize]
  have hsumH : (∑ x, H x) = 0 :=
    zero_derivative_sum n (by omega) (indicator {0, d}) H hF d hd (pair_indicator_derivative d)
  have hsum : (∑ z ∈ A, z) = (d, 0) := by
    have hgraph : (∑ z ∈ A, z) = ∑ x ∈ Finset.univ \ {0, d}, (x, H x) := by
      exact Counts.sum_restricted_graph H _ id
    rw [hgraph]
    have hx := sum_complement {0, d} (fun x : BinarySpace n => x)
    have hy := sum_complement {0, d} H
    simp only [Finset.sum_insert (show (0 : BinarySpace n) ∉ {d} by simp [Ne.symm hd]),
      Finset.sum_singleton, zero_add, h0, hdH, add_zero] at hx hy
    rw [sum_binary_eq_zero (by omega)] at hx
    rw [hsumH] at hy
    apply Prod.ext
    · simpa only [Prod.fst_sum] using (binary_add_eq_zero_iff _ _).1 hx
    · simpa only [Prod.snd_sum] using hy
  refine ⟨complement_graph_sidon n {0, d} H hF, hcard, hsum, ?_⟩
  intro x hx y hy he
  obtain ⟨u, hu, rfl⟩ := (mem_restrictedGraph _ _ _).1 hx
  obtain ⟨v, hv, rfl⟩ := (mem_restrictedGraph _ _ _).1 hy
  have huv : u + v = d := congrArg Prod.fst he
  have hHv : H u + H v = 0 := congrArg Prod.snd he
  have hu0 : u ≠ 0 := by
    intro h
    exact (Finset.mem_sdiff.mp hu).2 (by simp [h])
  have hud : u ≠ d := by
    intro h
    exact (Finset.mem_sdiff.mp hu).2 (by simp [h])
  have hgu : indicator {0, d} u = 0 := by simp [indicator, hu0, hud]
  have hgv : indicator {0, d} v = 0 := by
    rw [indicator, ite_eq_right (Finset.mem_sdiff.mp hv).2]
  have hder : derivative (splitMap (indicator {0, d}) H) d u =
      derivative (splitMap (indicator {0, d}) H) d 0 := by
    have hvu : u + d = v := by rw [← huv]; simp
    apply Prod.ext
    · change indicator {0, d} (u + d) + indicator {0, d} u =
        indicator {0, d} (0 + d) + indicator {0, d} 0
      rw [hvu, hgu, hgv]
      simp [indicator]
    · change H (u + d) + H u = H (0 + d) + H 0
      rw [hvu, zero_add, hdH, h0, add_zero]
      simpa [add_comm] using hHv
  rcases (apn_iff_collision _).1 hF d hd u 0 hder with h | h
  · exact hu0 h.symm
  · have := congrArg (fun z => z + d) h
    exact hud (by simpa using this.symm)

end
end APNLinearity.SmallSupport

open scoped BigOperators

namespace APNLinearity.SmallSupport
noncomputable section
open _root_.APNLinearity.Fourier Sidon
attribute [local instance 10] Classical.propDecidable

def inputClass {n : ℕ} (d : BinarySpace n) (e : Bit) : Finset (BinarySpace n) :=
  Finset.univ.filter (fun a => binaryDot a d = e)

def residualClass {n m : ℕ} (d : BinarySpace n) (e : Bit) : Finset (CharacterSpace n m) :=
  inputClass d e ×ˢ (Finset.univ.erase 0)

theorem sum_input_classes {n : ℕ} (d : BinarySpace n) (f : BinarySpace n → ℤ) :
    (∑ a, f a) = (∑ a ∈ inputClass d 0, f a) + ∑ a ∈ inputClass d 1, f a := by
  have hn (a : BinarySpace n) : (¬ binaryDot a d = 0) ↔ binaryDot a d = 1 := by
    rcases bit_eq_zero_or_one (binaryDot a d) with h | h <;> simp [h]
  simpa only [inputClass, hn] using
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => binaryDot a d = 0) f).symm

theorem twisted_input_classes {n : ℕ} (d : BinarySpace n) (f : BinarySpace n → ℤ) :
    (∑ a, character a d * f a) =
      (∑ a ∈ inputClass d 0, f a) - ∑ a ∈ inputClass d 1, f a := by
  rw [sum_input_classes d]
  have h0 (a : BinarySpace n) (ha : a ∈ inputClass d 0) : character a d = 1 := by
    rw [character, (Finset.mem_filter.mp ha).2, sign_zero]
  have h1 (a : BinarySpace n) (ha : a ∈ inputClass d 1) : character a d = -1 := by
    rw [character, (Finset.mem_filter.mp ha).2, sign_one]
  have h0s : (∑ a ∈ inputClass d 0, character a d * f a) = ∑ a ∈ inputClass d 0, f a :=
    Finset.sum_congr rfl (fun a ha => by rw [h0 a ha, one_mul])
  have h1s : (∑ a ∈ inputClass d 1, character a d * f a) = ∑ a ∈ inputClass d 1, -f a :=
    Finset.sum_congr rfl (fun a ha => by rw [h1 a ha, neg_one_mul])
  rw [h0s, h1s, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem residual_sum {n m : ℕ} (d : BinarySpace n) (e : Bit) (f : CharacterSpace n m → ℤ) :
    (∑ u ∈ residualClass d e, f u) =
      (∑ a ∈ inputClass d e, ∑ c, f (a, c)) - ∑ a ∈ inputClass d e, f (a, 0) := by
  rw [residualClass, Finset.sum_product]
  simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  rw [Finset.sum_sub_distrib]

theorem residual_card {n m : ℕ} (d : BinarySpace n) (hd : d ≠ 0) (e : Bit) :
    2 * (@residualClass n m d e).card = spaceSize n * (spaceSize m - 1) := by
  rw [residualClass, Finset.card_product,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_binary]
  have := dot_fiber_card d hd e
  dsimp only [inputClass]
  nlinarith

/-- Every row of the input-only character table, before taking moments. -/
theorem two_point_input_character {n m : ℕ} (d : BinarySpace n) (hd : d ≠ 0)
    (H : VectorialMap n m) (a : BinarySpace n) :
    productCharacterSum (restrictedGraph (Finset.univ \ {0, d}) H) (a, 0) =
      (if a = 0 then (spaceSize n : ℤ) else 0) - 1 - character a d := by
  classical
  unfold productCharacterSum
  rw [Counts.sum_restricted_graph]
  simp only [product_character_eq, character_zero_left, mul_one]
  have h := sum_complement {0, d} (character a)
  rw [Finset.sum_insert (show (0 : BinarySpace n) ∉ {d} by simp [Ne.symm hd]),
    Finset.sum_singleton, character_zero_right] at h
  have hort : (∑ x, character a x) = if a = 0 then (spaceSize n : ℤ) else 0 := by
    simpa only [character_comm] using character_orthogonality n a
  rw [hort] at h
  omega

theorem two_point_input_moments {n m : ℕ} (d : BinarySpace n) (hd : d ≠ 0)
    (H : VectorialMap n m) :
    let α := productCharacterSum (restrictedGraph (Finset.univ \ {0, d}) H)
    (∑ a ∈ inputClass d 0, α (a, 0) ^ 2) =
      ((spaceSize n : ℤ) - 2) ^ 2 + 4 * ((inputClass d 0).card - 1) ∧
    (∑ a ∈ inputClass d 0, α (a, 0) ^ 4) =
      ((spaceSize n : ℤ) - 2) ^ 4 + 16 * ((inputClass d 0).card - 1) ∧
    (∀ a ∈ inputClass d 1, α (a, 0) = 0) := by
  dsimp only
  have h0 : (0 : BinarySpace n) ∈ inputClass d 0 := by simp [inputClass]
  have hzero : productCharacterSum (restrictedGraph (Finset.univ \ {0, d}) H) (0, 0) =
      (spaceSize n : ℤ) - 2 := by rw [two_point_input_character d hd]; simp; ring
  have hother (a : BinarySpace n) (ha : a ∈ (inputClass d 0).erase 0) :
      productCharacterSum (restrictedGraph (Finset.univ \ {0, d}) H) (a, 0) = -2 := by
    rw [two_point_input_character d hd, ite_eq_right (Finset.mem_erase.mp ha).1]
    have ha0 := (Finset.mem_filter.mp (Finset.mem_erase.mp ha).2).2
    simp [character, ha0]
  have hm (j : ℕ) :
      (∑ a ∈ inputClass d 0,
        productCharacterSum (restrictedGraph (Finset.univ \ {0, d}) H) (a, 0) ^ j) =
      ((spaceSize n : ℤ) - 2) ^ j + ((inputClass d 0).card - 1) * (-2) ^ j := by
    rw [← Finset.sum_erase_add _ _ h0, hzero,
      Finset.sum_congr rfl (fun a ha => congrArg (fun z : ℤ => z ^ j) (hother a ha))]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem h0,
      Nat.cast_sub (Finset.card_pos.mpr ⟨0, h0⟩), Nat.cast_one]
    ring
  refine ⟨by simpa [mul_comm] using hm 2, by simpa [mul_comm] using hm 4, ?_⟩
  intro a ha
  have ha1 := (Finset.mem_filter.mp ha).2
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha1
  rw [two_point_input_character d hd, ite_eq_right ha0]
  simp [character, ha1]

/-- Subtract the input-character table from the half moments and fourth moment. -/
theorem two_point_residual_rigidity {n : ℕ} (hn : 4 ≤ n) (d : BinarySpace n) (hd : d ≠ 0)
    (H : VectorialMap n (n - 1))
    (hA : IsBinarySidon (restrictedGraph (Finset.univ \ {0, d}) H))
    (hcard : (restrictedGraph (Finset.univ \ {0, d}) H).card = spaceSize n - 2)
    (hsum : (∑ z ∈ restrictedGraph (Finset.univ \ {0, d}) H, z) = (d, 0))
    (hpair : ∀ x ∈ restrictedGraph (Finset.univ \ {0, d}) H,
      ∀ y ∈ restrictedGraph (Finset.univ \ {0, d}) H, x + y ≠ (d, 0)) :
    IsSquare (spaceSize n : ℤ) ∧
      ∀ a c, binaryDot a d = 1 → c ≠ 0 →
        productCharacterSum (restrictedGraph (Finset.univ \ {0, d}) H) (a, c) ^ 2 = spaceSize n := by
  let A := restrictedGraph (Finset.univ \ {0, d}) H
  let α := productCharacterSum A
  let S : Finset (CharacterSpace n (n - 1)) := residualClass d 0
  let T : Finset (CharacterSpace n (n - 1)) := residualClass d 1
  let N : ℤ := spaceSize n
  let M : ℤ := spaceSize (n - 1)
  have hN : 16 ≤ N := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    norm_num at this
    dsimp [N, spaceSize]
    exact_mod_cast this
  have hN16 : 16 ∣ N := by
    have := pow_dvd_pow (2 : ℤ) hn
    norm_num at this
    exact this
  have hNM : N = 2 * M := by
    dsimp [N, M, spaceSize]
    calc (2 : ℤ) ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
         _ = 2 * 2 ^ (n - 1) := by rw [pow_succ]; ring
  have hMN : 8 ≤ M := by omega
  have hAc : (A.card : ℤ) = N - 2 := by
    have hNnat : 2 ≤ spaceSize n := by change (16 : ℤ) ≤ (spaceSize n : ℤ) at hN; omega
    dsimp [A]
    rw [hcard, Nat.cast_sub hNnat]
    rfl
  have hc (e : Bit) : ((@residualClass n (n - 1) d e).card : ℤ) = M * (M - 1) := by
    have h := residual_card (m := n - 1) d hd e
    have h' := congrArg (fun z : ℕ => (z : ℤ)) h
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (spaceSize_pos (n - 1)),
      Nat.cast_one] at h'
    change 2 * ((@residualClass n (n - 1) d e).card : ℤ) = N * (M - 1) at h'
    rw [hNM] at h'
    nlinarith
  have hSc : (S.card : ℤ) = M * (M - 1) := hc 0
  have hTc : (T.card : ℤ) = M * (M - 1) := hc 1
  have hST : T.card = S.card := by omega
  have hp : 0 < S.card := by nlinarith
  have hq : ((inputClass d 0).card : ℤ) = M := by
    have h : 2 * ((inputClass d 0).card : ℤ) = N := by
      dsimp [inputClass, N]
      exact_mod_cast dot_fiber_card d hd 0
    omega
  have hmod (e : Bit) (u : CharacterSpace n (n - 1)) (hu : u ∈ residualClass d e) :
      α u % 4 = (N - 2 - 2 * (e.val : ℤ)) % 4 := by
    have he := (Finset.mem_filter.mp (Finset.mem_product.mp hu).1).2
    have h := product_sum_congruence A u
    rw [hsum, hAc] at h
    simpa only [characterDot, dot_zero_right, add_zero, he] using h
  have hSmod (u : CharacterSpace n (n - 1)) (hu : u ∈ S) : α u % 4 = 2 := by
    have h := hmod 0 u hu
    norm_num only [show (0 : Bit).val = 0 from rfl, Nat.cast_zero, mul_zero, sub_zero] at h
    omega
  have hTmod (u : CharacterSpace n (n - 1)) (hu : u ∈ T) : α u % 4 = 0 := by
    have h := hmod 1 u hu
    norm_num only [show (1 : Bit).val = 1 from rfl, Nat.cast_one, mul_one] at h
    omega
  have htwist : (∑ u, productCharacter u (d, 0) * α u ^ 2) = 0 := by
    have hz : ((A ×ˢ A).filter (fun z => z.1 + z.2 = (d, 0))) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro z hz he
      exact hpair z.1 (Finset.mem_product.mp hz).1 z.2 (Finset.mem_product.mp hz).2 he
    simpa only [hz, Finset.card_empty, Nat.cast_zero, mul_zero] using product_twisted_second A (d, 0)
  have hsecond := product_second_moment A
  change (∑ u, α u ^ 2) = N * M * A.card at hsecond
  rw [hAc, Fintype.sum_prod_type, sum_input_classes d] at hsecond
  have htwist' :
      (∑ a ∈ inputClass d 0, ∑ c, α (a, c) ^ 2) -
      (∑ a ∈ inputClass d 1, ∑ c, α (a, c) ^ 2) = 0 := by
    rw [Fintype.sum_prod_type] at htwist
    simp only [product_character_eq, character_zero_right, mul_one,
      ← Finset.mul_sum] at htwist
    rwa [twisted_input_classes d] at htwist
  have hfour := product_sidon_fourth_moment n (n - 1) A hA
  change (∑ u, α u ^ 4) = N * M * (3 * (A.card : ℤ) ^ 2 - 2 * A.card) at hfour
  rw [hAc, Fintype.sum_prod_type, sum_input_classes d] at hfour
  obtain ⟨hi2, hi4, hi1⟩ := two_point_input_moments d hd H
  change (∑ a ∈ inputClass d 0, α (a, 0) ^ 2) = (N - 2) ^ 2 + 4 * _ at hi2
  change (∑ a ∈ inputClass d 0, α (a, 0) ^ 4) = (N - 2) ^ 4 + 16 * _ at hi4
  rw [hq] at hi2 hi4
  have hz (j : ℕ) (hj : j ≠ 0) : (∑ a ∈ inputClass d 1, α (a, 0) ^ j) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [show α (a, 0) = 0 from hi1 a ha, zero_pow hj]
  have hS2 : (∑ u ∈ S, α u ^ 2) = S.card * (N - 4) := by
    rw [residual_sum, hi2, hSc]
    rw [hNM] at hsecond ⊢
    nlinarith [htwist']
  have hT2 : (∑ u ∈ T, α u ^ 2) = S.card * N := by
    rw [residual_sum, hz 2 (by decide), sub_zero, hSc]
    rw [hNM] at hsecond ⊢
    nlinarith [htwist']
  have h4 : (∑ u ∈ S, α u ^ 4) + (∑ u ∈ T, α u ^ 4) =
      S.card * (2 * N ^ 2 + 8 * N - 48) := by
    rw [residual_sum, residual_sum, hi4, hz 4 (by decide), sub_zero, hSc]
    rw [hNM] at hfour ⊢
    nlinarith [hfour]
  obtain ⟨hsq, he⟩ := arithmetic_rigidity_finsets S T α N hN hN16 hp hST hSmod hTmod hS2 hT2 h4
  refine ⟨hsq, ?_⟩
  intro a c ha hc'
  exact he (a, c) (by simp [T, residualClass, inputClass, ha, hc'])

end
end APNLinearity.SmallSupport

open scoped BigOperators

namespace APNLinearity.SmallSupport
noncomputable section
open _root_.APNLinearity.Fourier Sidon Components

theorem sum_component_walsh {n m : ℕ} (H : VectorialMap n m) (a : BinarySpace n) :
    (∑ c, walsh (mapComponent H c) a) =
      (spaceSize m : ℤ) * ∑ x ∈ Finset.univ.filter (fun x => H x = 0), character a x := by
  classical
  simp only [walsh, mapComponent, sign_add]
  change (∑ c, ∑ x, character c (H x) * character a x) = _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, character_orthogonality m]
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem two_point_walsh {n m : ℕ} (d : BinarySpace n) (hd : d ≠ 0)
    (H : VectorialMap n m) (h0 : H 0 = 0) (hdH : H d = 0)
    (a : BinarySpace n) (ha : binaryDot a d = 1) (c : BinarySpace m) :
    productCharacterSum (restrictedGraph (Finset.univ \ {0, d}) H) (a, c) =
      walsh (mapComponent H c) a := by
  classical
  unfold productCharacterSum
  rw [Counts.sum_restricted_graph]
  have h := sum_complement {0, d} (fun x => productCharacter (a, c) (x, H x))
  rw [Finset.sum_insert (show (0 : BinarySpace n) ∉ {d} by simp [Ne.symm hd]),
    Finset.sum_singleton] at h
  simpa [productCharacter, h0, hdH, ha, walsh, component, mapComponent, add_comm] using h

/-- Orthogonality makes the odd signed sum divisible by an even multiple of its magnitude. -/
theorem two_point_parity_obstruction {n : ℕ} (hn : 4 ≤ n)
    (H : VectorialMap n (n - 1)) (a : BinarySpace n) (ha : a ≠ 0)
    (hsq : IsSquare (spaceSize n : ℤ))
    (hW : ∀ c, c ≠ 0 → walsh (mapComponent H c) a ^ 2 = spaceSize n) : False := by
  classical
  obtain ⟨w, hw⟩ := hsq
  have hw' : w ^ 2 = (2 : ℤ) ^ n := by simpa [spaceSize, pow_two] using hw.symm
  obtain ⟨k, hnk, _⟩ := square_power_two w hw'
  have hk : 2 ≤ k := by omega
  let v : ℤ := 2 ^ k
  let ε : BinarySpace (n - 1) → ℤ := fun c => if walsh (mapComponent H c) a = v then 1 else -1
  let C : Finset (BinarySpace (n - 1)) := Finset.univ.erase 0
  have hv : 0 < v := pow_pos (by norm_num) _
  have hN : (spaceSize n : ℤ) = v ^ 2 := by simp [spaceSize, hnk, v, pow_add, pow_two]
  have he (c : BinarySpace (n - 1)) (hc : c ≠ 0) : walsh (mapComponent H c) a = v * ε c := by
    have h := hW c hc
    rw [hN] at h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · simp [ε, h]
    · have hne : walsh (mapComponent H c) a ≠ v := by rw [h]; omega
      simp only [ε, ite_eq_right hne, mul_neg_one]
      exact h
  have hzero : walsh (mapComponent H 0) a = 0 := by
    simp only [walsh, mapComponent, dot_zero_left, zero_add]
    change (∑ x, character a x) = 0
    simpa only [character_comm, ite_eq_right ha] using character_orthogonality n a
  have hsum := Finset.sum_erase_add Finset.univ (fun c => walsh (mapComponent H c) a)
    (Finset.mem_univ (0 : BinarySpace (n - 1)))
  have heSum : (∑ c ∈ C, walsh (mapComponent H c) a) = v * ∑ c ∈ C, ε c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c hc => he c (Finset.mem_erase.mp hc).1)
  change (∑ c ∈ C, walsh (mapComponent H c) a) + _ = _ at hsum
  rw [heSum, hzero, add_zero, sum_component_walsh] at hsum
  have hM : (spaceSize (n - 1) : ℤ) = v * (2 : ℤ) ^ (n - 1 - k) := by
    simp only [spaceSize, Nat.cast_pow, Nat.cast_ofNat, v, ← pow_add]
    congr 1
    omega
  have hcancel : (∑ c ∈ C, ε c) =
      (2 : ℤ) ^ (n - 1 - k) * ∑ x ∈ Finset.univ.filter (fun x => H x = 0), character a x := by
    apply mul_left_cancel₀ hv.ne'
    rw [hM] at hsum
    simpa [mul_assoc] using hsum
  have heBit (c : BinarySpace (n - 1)) : (ε c : Bit) = 1 := by
    dsimp [ε]
    split_ifs <;> decide
  have htwo : (2 : Bit) = 0 := rfl
  have hsumBit : ((∑ c ∈ C, ε c : ℤ) : Bit) = 1 := by
    rw [Int.cast_sum]
    simp only [heBit, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc : C.card = spaceSize (n - 1) - 1 := by simp [C, spaceSize]
    rw [hc, Nat.cast_sub (spaceSize_pos (n - 1))]
    simp only [spaceSize, Nat.cast_pow, Nat.cast_ofNat, htwo,
      zero_pow (show n - 1 ≠ 0 by omega), Nat.cast_one, zero_sub, ZMod.neg_eq_self_mod_two]
  have hcast := congrArg (fun z : ℤ => (z : Bit)) hcancel
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, htwo,
    zero_pow (show n - 1 - k ≠ 0 by omega), hsumBit, zero_mul] at hcast
  exact one_ne_zero hcast

theorem exclude_distance_two : ∀ (n : ℕ), 4 ≤ n → ∀ (F : VectorialFunction n), IsAPN F →
    ∀ b, b ≠ 0 → ∀ a c,
      hammingDistance (component F b) (affineBoolean a c) ≠ 2 := by
  intro n hn F hF b hb a c hdist
  obtain ⟨d, H, hd, h0, hdH, hH⟩ := two_point_normalization (by omega) F hF b hb a c hdist
  obtain ⟨hS, hcard, hsum, hpair⟩ := two_point_graph_data hn d hd H h0 hdH hH
  obtain ⟨hsq, hrigid⟩ := two_point_residual_rigidity hn d hd H hS hcard hsum hpair
  obtain ⟨a', ha'⟩ := exists_dot_one hd
  have ha0 : a' ≠ 0 := by intro h; simp [h] at ha'
  apply two_point_parity_obstruction hn H a' ha0 hsq
  intro c' hc'
  rw [← two_point_walsh d hd H h0 hdH a' ha' c']
  exact hrigid a' c' ha' hc'

end

end APNLinearity.SmallSupport
