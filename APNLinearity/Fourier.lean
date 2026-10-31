module

public import APNLinearity.Algebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.Fourier
noncomputable section

/-- Translation by a character with value -1 proves orthogonality. -/
theorem character_orthogonality : ∀ (n : ℕ) (x : BinarySpace n),
    (∑ a, character a x) = if x = 0 then (spaceSize n : ℤ) else 0 := by
  intro n x
  classical
  by_cases hx : x = 0
  · subst x
    simp [spaceSize]
  · obtain ⟨t, ht⟩ := exists_dot_one hx
    have ht' : character t x = -1 := by simp [character, ht]
    have hs := sum_translate (fun a => character a x) t
    simp only [character_add_left, ht', mul_neg_one, Finset.sum_neg_distrib] at hs
    rw [ite_eq_right hx]
    omega

theorem orthogonality_cast {R : Type*} [CommRing R] {n : ℕ} (x : BinarySpace n) :
    (∑ a, (character a x : R)) = if x = 0 then (spaceSize n : R) else 0 := by
  classical
  rw [← Int.cast_sum, character_orthogonality n x]
  split_ifs <;> simp

/-- The same unnormalized transform over integers or reals. -/
def transform {R : Type*} [CommRing R] {n : ℕ} (u : BinarySpace n → R) (a : BinarySpace n) : R :=
  ∑ x, u x * (character a x : R)

theorem transform_twice {R : Type*} [CommRing R] {n : ℕ}
    (u : BinarySpace n → R) (x : BinarySpace n) :
    transform (transform u) x = (spaceSize n : R) * u x := by
  classical
  unfold transform
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ a, u y * (character a y : R) * (character x a : R)) =
        ∑ y, u y * (∑ a, (character a (y + x) : R)) := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.mul_sum, character_add_right, Int.cast_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [character_comm x a, mul_assoc]
    _ = (spaceSize n : R) * u x := by
      simp only [orthogonality_cast, binary_add_eq_zero_iff]
      simp [mul_comm]

theorem transform_pairing {R : Type*} [CommRing R] {n : ℕ}
    (u v : BinarySpace n → R) :
    (∑ a, transform u a * v a) = ∑ x, u x * transform v x := by
  unfold transform
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  rw [character_comm a x]
  ring

theorem transform_parseval {R : Type*} [CommRing R] {n : ℕ}
    (u : BinarySpace n → R) :
    (∑ a, transform u a ^ 2) = (spaceSize n : R) * ∑ x, u x ^ 2 := by
  simp_rw [pow_two]
  rw [transform_pairing]
  simp_rw [transform_twice]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem fourier_eq_transform {n : ℕ} (u : BinarySpace n → ℝ) : fourier u = transform u := rfl

theorem fourier_inversion : ∀ (n : ℕ) (u : BinarySpace n → ℝ) (x : BinarySpace n),
    u x = (∑ a, fourier u a * (character a x : ℝ)) / (spaceSize n : ℝ) := by
  intro n u x
  have hn : (spaceSize n : ℝ) ≠ 0 := by exact_mod_cast (spaceSize_pos n).ne'
  apply (eq_div_iff hn).2
  simpa only [transform, fourier, character_comm, mul_comm] using (transform_twice u x).symm

theorem fourier_parseval : ∀ (n : ℕ) (u : BinarySpace n → ℝ),
    (∑ a, fourier u a ^ 2) = (spaceSize n : ℝ) * ∑ x, u x ^ 2 := by
  intro n u
  exact transform_parseval u

theorem walsh_eq_transform {n : ℕ} (f : BooleanFunction n) :
    walsh f = transform (fun x => bitSign (f x)) := by
  ext a
  simp [walsh, transform, character]

theorem walsh_parseval : ∀ (n : ℕ) (f : BooleanFunction n), (∑ a, walsh f a ^ 2) = (spaceSize n : ℤ) ^ 2 := by
  intro n f
  have h := transform_parseval (fun x => bitSign (f x))
  simp only [← walsh_eq_transform, sign_sq] at h
  simpa [spaceSize, pow_two] using h

theorem walsh_affine_shift : ∀ (n : ℕ) (f : BooleanFunction n) (a a₀ : BinarySpace n) (c : Bit),
    walsh (f + affineBoolean a₀ c) a = bitSign c * walsh f (a + a₀) := by
  intro n f a a₀ c
  simp only [walsh, Pi.add_apply, affineBoolean, dot_add_left, sign_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem sign_eq_one_sub_twice (x : Bit) : bitSign x = 1 - 2 * (if x = 1 then 1 else 0 : ℤ) := by
  rcases bit_eq_zero_or_one x with rfl | rfl <;> norm_num

theorem sign_sum_weight {n : ℕ} (f : BooleanFunction n) :
    (∑ x, bitSign (f x)) = (spaceSize n : ℤ) - 2 * (weight f : ℤ) := by
  classical
  simp only [sign_eq_one_sub_twice, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [weight, spaceSize]

theorem distance_eq_weight {n : ℕ} (f g : BooleanFunction n) :
    hammingDistance f g = weight (f + g) := by
  classical
  unfold hammingDistance weight
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
  rcases bit_eq_zero_or_one (f x) with h | h <;>
    rcases bit_eq_zero_or_one (g x) with k | k <;> simp [h, k]

theorem distance_walsh : ∀ (n : ℕ) (f : BooleanFunction n) (a : BinarySpace n) (c : Bit),
    2 * (hammingDistance f (affineBoolean a c) : ℤ) =
      (spaceSize n : ℤ) - bitSign c * walsh f a := by
  intro n f a c
  have hs := sign_sum_weight (f + affineBoolean a c)
  have ht : (∑ x, bitSign ((f + affineBoolean a c) x)) = bitSign c * walsh f a := by
    simp only [Pi.add_apply, affineBoolean, sign_add, walsh, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [ht, ← distance_eq_weight] at hs
  linarith

theorem walsh_even : ∀ (n : ℕ), 1 ≤ n → ∀ (f : BooleanFunction n) (a : BinarySpace n), 2 ∣ walsh f a := by
  intro n hn f a
  have hN : (2 : ℤ) ∣ (spaceSize n : ℤ) := by
    exact_mod_cast (dvd_pow_self (2 : ℕ) (by omega : n ≠ 0))
  have hd := distance_walsh n f a 0
  simp only [sign_zero, one_mul] at hd
  have hw : walsh f a = (spaceSize n : ℤ) - 2 * hammingDistance f (affineBoolean a 0) := by
    linarith
  rw [hw]
  exact dvd_sub hN (dvd_mul_right _ _)

theorem exists_walsh_ne_zero {n : ℕ} (f : BooleanFunction n) : ∃ a, walsh f a ≠ 0 := by
  by_contra h
  push Not at h
  have hp := walsh_parseval n f
  simp only [h, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero] at hp
  have hn : (0 : ℤ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  nlinarith

theorem walsh_abs_le {n : ℕ} (f : BooleanFunction n) (a : BinarySpace n) :
    |walsh f a| ≤ (spaceSize n : ℤ) := by
  have hs (x : BinarySpace n) : |bitSign (f x + binaryDot a x)| = 1 := by
    rcases sign_cases (f x + binaryDot a x) with h | h <;> simp [h]
  calc
    |walsh f a| ≤ ∑ x, |bitSign (f x + binaryDot a x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = (spaceSize n : ℤ) := by
      simp only [hs, Finset.sum_const, Finset.card_univ, card_binary, nsmul_eq_mul, mul_one]

theorem walsh_zero_component {n : ℕ} (F : VectorialFunction n) (a : BinarySpace n) :
    walsh (component F 0) a = if a = 0 then (spaceSize n : ℤ) else 0 := by
  simp only [walsh, component, dot_zero_left, zero_add]
  change (∑ x, character a x) = _
  simpa only [character_comm] using character_orthogonality n a

/-- A plateaued spectrum has an integer magnitude because its coefficients are integers. -/
theorem integer_plateaued_magnitude (n : ℕ) (f : BooleanFunction n) :
    (∃ amplitude : ℤ, HasPlateauedMagnitude f amplitude) ↔ IsPlateaued f := by
  constructor
  · rintro ⟨amplitude, hp, hh⟩
    refine ⟨(amplitude : ℝ), by exact_mod_cast hp, ?_⟩
    intro a
    rcases hh a with h | h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (Or.inl (by exact_mod_cast h))
    · exact Or.inr (Or.inr (by exact_mod_cast h))
  · rintro ⟨amplitude, hp, hh⟩
    obtain ⟨a₀, ha₀⟩ := exists_walsh_ne_zero f
    have hmag : (|walsh f a₀| : ℝ) = amplitude := by
      rcases hh a₀ with h | h | h
      · exact False.elim (ha₀ (by exact_mod_cast h))
      · rw [h, abs_of_pos hp]
      · rw [h, abs_neg, abs_of_pos hp]
    refine ⟨|walsh f a₀|, ?_, ?_⟩
    · exact abs_pos.mpr ha₀
    · intro a
      rcases hh a with h | h | h
      · exact Or.inl (by exact_mod_cast h)
      · right; left
        have : (walsh f a : ℝ) = (|walsh f a₀| : ℤ) := by simpa using h.trans hmag.symm
        exact_mod_cast this
      · right; right
        have : (walsh f a : ℝ) = -((|walsh f a₀| : ℤ) : ℝ) := by
          simpa using h.trans (congrArg Neg.neg hmag.symm)
        exact_mod_cast this

end
end APNLinearity.Fourier
