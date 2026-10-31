module

public import APNLinearity.Auxiliary

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace APNLinearity

@[simp] theorem spaceSize_pos (n : ℕ) : 0 < spaceSize n := by
  exact pow_pos (by decide) n

@[simp] theorem card_binary (n : ℕ) : Fintype.card (BinarySpace n) = spaceSize n := by
  simp [BinarySpace, Bit, spaceSize]

@[simp] theorem sign_zero : bitSign (0 : Bit) = 1 := by simp [bitSign]

@[simp] theorem sign_one : bitSign (1 : Bit) = -1 := by simp [bitSign]

@[simp] theorem dot_zero_right (n : ℕ) (a : BinarySpace n) : binaryDot a 0 = 0 := by
  simp [binaryDot]

end APNLinearity

open scoped BigOperators

namespace APNLinearity

@[simp] theorem bit_add_self (x : Bit) : x + x = 0 := by
  exact CharTwo.add_self_eq_zero x

@[simp] theorem binary_add_self {n : ℕ} (x : BinarySpace n) : x + x = 0 := by
  ext i
  exact bit_add_self (x i)

@[simp] theorem binary_add_cancel_right {n : ℕ} (x y : BinarySpace n) : x + y + y = x := by
  rw [add_assoc, binary_add_self, add_zero]

@[simp] theorem binary_add_cancel_left {n : ℕ} (x y : BinarySpace n) : x + (x + y) = y := by
  rw [← add_assoc, binary_add_self, zero_add]

theorem bit_eq_zero_or_one (x : Bit) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] theorem sign_add (x y : Bit) : bitSign (x + y) = bitSign x * bitSign y := by
  fin_cases x <;> fin_cases y <;> decide

@[simp] theorem sign_sq (x : Bit) : bitSign x ^ 2 = 1 := by
  rcases bit_eq_zero_or_one x with rfl | rfl <;> norm_num

theorem sign_ne_zero (x : Bit) : bitSign x ≠ 0 := by
  rcases bit_eq_zero_or_one x with rfl | rfl <;> norm_num

theorem sign_cases (x : Bit) : bitSign x = 1 ∨ bitSign x = -1 := by
  rcases bit_eq_zero_or_one x with rfl | rfl <;> simp

@[simp] theorem sign_eq_one_iff (x : Bit) : bitSign x = 1 ↔ x = 0 := by
  rcases bit_eq_zero_or_one x with rfl | rfl <;> norm_num

@[simp] theorem sign_eq_neg_one_iff (x : Bit) : bitSign x = -1 ↔ x = 1 := by
  rcases bit_eq_zero_or_one x with rfl | rfl <;> norm_num

theorem sign_injective : Function.Injective bitSign := by
  intro x y h
  rcases bit_eq_zero_or_one x with rfl | rfl <;>
    rcases bit_eq_zero_or_one y with rfl | rfl <;> simp_all

@[simp] theorem dot_zero_left {n : ℕ} (x : BinarySpace n) : binaryDot 0 x = 0 := by
  simp [binaryDot]

theorem dot_comm {n : ℕ} (a x : BinarySpace n) : binaryDot a x = binaryDot x a := by
  simp [binaryDot, mul_comm]

@[simp] theorem dot_add_left {n : ℕ} (a b x : BinarySpace n) :
    binaryDot (a + b) x = binaryDot a x + binaryDot b x := by
  simp [binaryDot, add_mul, Finset.sum_add_distrib]

@[simp] theorem dot_add_right {n : ℕ} (a x y : BinarySpace n) :
    binaryDot a (x + y) = binaryDot a x + binaryDot a y := by
  simp [binaryDot, mul_add, Finset.sum_add_distrib]

theorem exists_dot_one {n : ℕ} {x : BinarySpace n} (hx : x ≠ 0) :
    ∃ a : BinarySpace n, binaryDot a x = 1 := by
  have hi : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    ext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := hi
  have hxi : x i = 1 := (bit_eq_zero_or_one (x i)).resolve_left hi
  refine ⟨fun j => if j = i then 1 else 0, ?_⟩
  simp [binaryDot, ite_mul, hxi]

@[simp] theorem character_zero_left {n : ℕ} (x : BinarySpace n) : character 0 x = 1 := by
  simp [character]

@[simp] theorem character_zero_right {n : ℕ} (a : BinarySpace n) : character a 0 = 1 := by
  simp [character]

theorem character_comm {n : ℕ} (a x : BinarySpace n) : character a x = character x a := by
  rw [character, dot_comm, character]

@[simp] theorem character_add_left {n : ℕ} (a b x : BinarySpace n) :
    character (a + b) x = character a x * character b x := by
  simp [character]

@[simp] theorem character_add_right {n : ℕ} (a x y : BinarySpace n) :
    character a (x + y) = character a x * character a y := by
  simp [character]

@[simp] theorem character_sq {n : ℕ} (a x : BinarySpace n) : character a x ^ 2 = 1 :=
  sign_sq _

theorem sum_translate {n : ℕ} {R : Type*} [AddCommMonoid R]
    (u : BinarySpace n → R) (t : BinarySpace n) : (∑ x, u (x + t)) = ∑ x, u x := by
  exact Fintype.sum_equiv (Equiv.addRight t) _ u (fun _ => rfl)

theorem binary_add_eq_zero_iff {n : ℕ} (x y : BinarySpace n) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (fun z => z + y) h
    simpa using this
  · rintro rfl
    exact binary_add_self _

end APNLinearity
