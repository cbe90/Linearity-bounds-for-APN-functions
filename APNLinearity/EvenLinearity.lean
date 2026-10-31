module

public import APNLinearity.SmallSupport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.EvenBound
noncomputable section
open _root_.APNLinearity.Fourier

theorem partial_parseval {n m : ℕ} (D : Finset (BinarySpace n)) (K : VectorialMap n m)
    (b : BinarySpace m) :
    (∑ a, partialWalsh D K b a ^ 2) = (spaceSize n : ℤ) * D.card := by
  classical
  have he : partialWalsh D K b =
      transform (fun x => if x ∈ D then character b (K x) else (0 : ℤ)) := by
    funext a
    simp [partialWalsh, transform, ite_mul]
  rw [he, transform_parseval]
  have hs (x : BinarySpace n) : (if x ∈ D then character b (K x) else (0 : ℤ)) ^ 2 =
      if x ∈ D then 1 else 0 := by split_ifs <;> simp
  simp only [hs]
  simp

theorem output_transform_dvd {n m : ℕ} (D : Finset (BinarySpace n)) (K : VectorialMap n m)
    (a : BinarySpace n) (y : BinarySpace m) :
    (spaceSize m : ℤ) ∣ transform (fun b => partialWalsh D K b a) y := by
  classical
  have he : transform (fun b => partialWalsh D K b a) y =
      (spaceSize m : ℤ) * ∑ x ∈ D, if K x = y then character a x else 0 := by
    unfold transform partialWalsh
    simp only [Finset.sum_mul, Int.cast_id]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have h : (∑ b, character b (K x) * character a x * character y b) =
        character a x * ∑ b, character b (K x + y) := by
      simp only [Finset.mul_sum, character_add_right]
      apply Finset.sum_congr rfl
      intro b _
      rw [character_comm y b]
      ring
    rw [h, character_orthogonality]
    simp only [binary_add_eq_zero_iff]
    split_ifs <;> ring
  rw [he]
  exact dvd_mul_right _ _

theorem odd_multiple_square (v z : ℤ) (_hv : 0 < v) (hz : 2 * v ∣ z - v) :
    v ^ 2 ≤ z ^ 2 := by
  obtain ⟨k, hk⟩ := hz
  have h : z = v * (2 * k + 1) := by nlinarith [hk]
  have hk' : 1 ≤ (2 * k + 1) ^ 2 := by
    by_cases hk0 : 0 ≤ k
    · nlinarith [sq_nonneg k]
    · have hk1 : k ≤ -1 := by omega
      nlinarith [sq_nonneg (k + 1)]
  rw [h, mul_pow]
  nlinarith [mul_nonneg (sq_nonneg v) (show 0 ≤ (2 * k + 1) ^ 2 - 1 by omega)]

/-- The signs nearest to a spectrum have an odd multiple of v as each Fourier value. -/
theorem sign_transform_congruence {m : ℕ} (v s₀ : ℤ) (s : BinarySpace m → ℤ)
    (hM : (spaceSize m : ℤ) = 2 * v) (hzero : s 0 = s₀)
    (hdiv : 2 * v ∣ s₀) (hs : ∀ b, b ≠ 0 → s b = v ∨ s b = -v)
    (y : BinarySpace m) : 2 * v ∣ transform s y - v := by
  classical
  let B : Finset (BinarySpace m) := Finset.univ.erase 0
  have hb (b : BinarySpace m) (hb : b ∈ B) : 2 * v ∣ s b * character y b - v := by
    rcases hs b (Finset.mem_erase.mp hb).1 with h | h <;>
      rcases sign_cases (binaryDot y b) with hc | hc <;>
      simp only [character, h, hc] <;> ring_nf <;> simp
  have hsum := Finset.dvd_sum hb
  have hcount : (B.card : ℤ) = 2 * v - 1 := by
    have hnat : B.card + 1 = spaceSize m := by
      simp only [B, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_binary]
      have := spaceSize_pos m
      omega
    have : (B.card : ℤ) + 1 = spaceSize m := by exact_mod_cast hnat
    omega
  have hpartition := Finset.sum_erase_add Finset.univ (fun b => s b * character y b)
    (Finset.mem_univ (0 : BinarySpace m))
  change (∑ b ∈ B, s b * character y b) + s 0 * character y 0 = transform s y at hpartition
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcount] at hsum
  rw [hzero, character_zero_right, mul_one] at hpartition
  have hd : 2 * v ∣ (2 * v - 1) * v - v := by
    use v - 1
    ring
  have hall := dvd_add (dvd_add hsum hdiv) hd
  convert hall using 1
  nlinarith [hpartition]

/-- The Fourier parity obstruction for one fixed input character. -/
theorem spectrum_distance {m : ℕ} (T : BinarySpace m → ℤ) (v s₀ : ℤ)
    (hv : 0 < v) (hM : (spaceSize m : ℤ) = 2 * v) (hdiv : 2 * v ∣ s₀)
    (hT : ∀ y, 2 * v ∣ transform T y) :
    v ^ 2 ≤ (T 0 - s₀) ^ 2 +
      ∑ b ∈ Finset.univ.erase 0, (|T b| - v) ^ 2 := by
  classical
  let s : BinarySpace m → ℤ := fun b => if b = 0 then s₀ else if 0 ≤ T b then v else -v
  have hs : ∀ b, b ≠ 0 → s b = v ∨ s b = -v := by
    intro b hb
    simp only [s, ite_eq_right hb]
    split_ifs <;> simp
  have hz : s 0 = s₀ := by simp [s]
  have hp (y : BinarySpace m) : v ^ 2 ≤ transform (fun b => T b - s b) y ^ 2 := by
    have he : transform (fun b => T b - s b) y = transform T y - transform s y := by
      simp [transform, sub_mul, Finset.sum_sub_distrib]
    have hd := sign_transform_congruence v s₀ s hM hz hdiv hs y
    have htwo : 2 * v ∣ 2 * v := dvd_refl _
    have hh := dvd_sub (dvd_sub (hT y) hd) htwo
    apply odd_multiple_square v _ hv
    rw [he]
    convert hh using 1
    ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hp y)
  rw [transform_parseval] at hsum
  simp only [Finset.sum_const, Finset.card_univ, card_binary, nsmul_eq_mul] at hsum
  have hm : (0 : ℤ) < spaceSize m := by exact_mod_cast spaceSize_pos m
  have hbound := (mul_le_mul_iff_right₀ hm).mp hsum
  have hterm (b : BinarySpace m) (hb : b ∈ Finset.univ.erase 0) :
      (T b - s b) ^ 2 = (|T b| - v) ^ 2 := by
    have hb' := (Finset.mem_erase.mp hb).1
    simp only [s, ite_eq_right hb']
    split_ifs with ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (by omega : T b < 0)]
      ring
  have he := Finset.sum_erase_add Finset.univ (fun b => (T b - s b) ^ 2)
    (Finset.mem_univ (0 : BinarySpace m))
  rw [Finset.sum_congr rfl hterm, hz] at he
  linarith


theorem zero_component_distance {n m : ℕ} (D : Finset (BinarySpace n)) (K : VectorialMap n m) :
    (∑ a, (partialWalsh D K 0 a - if a = 0 then (spaceSize n : ℤ) else 0) ^ 2) =
      (spaceSize n : ℤ) * ((spaceSize n : ℤ) - D.card) := by
  classical
  let u : BinarySpace n → ℤ := fun x => (if x ∈ D then 1 else 0) - 1
  have hu (a : BinarySpace n) : transform u a =
      partialWalsh D K 0 a - if a = 0 then (spaceSize n : ℤ) else 0 := by
    simp only [transform, u, sub_mul, Finset.sum_sub_distrib, one_mul, Int.cast_id]
    have hc : (∑ x, character a x) = if a = 0 then (spaceSize n : ℤ) else 0 := by
      simpa only [character_comm] using character_orthogonality n a
    rw [hc]
    simp [partialWalsh, ite_mul]
  have hp := transform_parseval u
  simp only [hu] at hp
  have he (x : BinarySpace n) : u x ^ 2 = 1 - if x ∈ D then 1 else 0 := by
    dsimp [u]
    split_ifs <;> norm_num
  simp only [he, Finset.sum_sub_distrib] at hp
  simpa [spaceSize] using hp


theorem restricted_distance {n m : ℕ} (D : Finset (BinarySpace n)) (K : VectorialMap n m)
    (v : ℤ) (hv : 0 < v) (hN : (spaceSize n : ℤ) = v ^ 2)
    (hM : (spaceSize m : ℤ) = 2 * v) (hdiv : 2 * v ∣ (spaceSize n : ℤ)) :
    (spaceSize n : ℤ) * D.card ≤
      ∑ b ∈ Finset.univ.erase 0, ∑ a, (|partialWalsh D K b a| - v) ^ 2 := by
  classical
  have hp (a : BinarySpace n) := spectrum_distance (fun b => partialWalsh D K b a) v
    (if a = 0 then (spaceSize n : ℤ) else 0) hv hM
    (by split_ifs; exact hdiv; exact dvd_zero _)
    (fun y => by rw [← hM]; exact output_transform_dvd D K a y)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hp a)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_binary,
    nsmul_eq_mul, ← hN] at hs
  rw [zero_component_distance, Finset.sum_comm] at hs
  nlinarith

theorem square_deviation_bound (w v : ℤ) (hv : 0 ≤ v) :
    v ^ 2 * (|w| - v) ^ 2 ≤ (w ^ 2 - v ^ 2) ^ 2 := by
  have h := mul_nonneg
    (mul_nonneg (abs_nonneg w) (show 0 ≤ |w| + 2 * v by positivity))
    (sq_nonneg (|w| - v))
  nlinarith only [h, sq_abs w]

theorem restricted_fourth_excess {n m : ℕ} (D : Finset (BinarySpace n)) (K : VectorialMap n m)
    (v : ℤ) (hv : 0 < v) (hN : (spaceSize n : ℤ) = v ^ 2)
    (hM : (spaceSize m : ℤ) = 2 * v) (hdiv : 2 * v ∣ (spaceSize n : ℤ)) :
    (spaceSize n : ℤ) ^ 2 * D.card ≤
      ∑ b ∈ Finset.univ.erase 0, ∑ a, (partialWalsh D K b a ^ 2 - spaceSize n) ^ 2 := by
  have hd := mul_le_mul_of_nonneg_left (restricted_distance D K v hv hN hM hdiv)
    (show (0 : ℤ) ≤ spaceSize n by positivity)
  have hp : (spaceSize n : ℤ) *
      (∑ b ∈ Finset.univ.erase 0, ∑ a, (|partialWalsh D K b a| - v) ^ 2) ≤
      ∑ b ∈ Finset.univ.erase 0, ∑ a, (partialWalsh D K b a ^ 2 - spaceSize n) ^ 2 := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro a _
    rw [hN]
    exact square_deviation_bound _ v hv.le
  nlinarith

theorem even_restricted_moments : ∀ (n : ℕ), 4 ≤ n → Even n → ∀ (D : Finset (BinarySpace n))
    (K : VectorialMap n (n / 2 + 1)),
    (spaceSize n : ℤ) ^ 2 * D.card ≤
      ∑ b ∈ Finset.univ.erase 0, ∑ a, (partialWalsh D K b a ^ 2 - spaceSize n) ^ 2 := by
  intro n hn he D K
  obtain ⟨k, hk⟩ := he
  have hhalf : n / 2 = k := by omega
  apply restricted_fourth_excess D K (2 ^ k) (by positivity)
  · simp [spaceSize, hk, pow_add, pow_two]
  · simp [spaceSize, hhalf, pow_succ, mul_comm]
  · have hdiv : (2 : ℕ) ^ (k + 1) ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have hh : (2 : ℤ) ^ (k + 1) ∣ 2 ^ n := by exact_mod_cast hdiv
    simpa only [spaceSize, Nat.cast_pow, Nat.cast_ofNat, pow_succ, mul_comm] using hh

/-- The subset formulation permits a map defined only on its given domain. -/
theorem even_subset_moments : ∀ (n : ℕ), 4 ≤ n → Even n → ∀ (D : Finset (BinarySpace n))
    (K : D → BinarySpace (n / 2 + 1)),
    (spaceSize n : ℤ) ^ 2 * D.card ≤
      ∑ b ∈ Finset.univ.erase 0, ∑ a : BinarySpace n,
        ((∑ x : D, bitSign (binaryDot b (K x) + binaryDot a x)) ^ 2 - spaceSize n) ^ 2 := by
  intro n hn he D K
  classical
  let K' : VectorialMap n (n / 2 + 1) := fun x => if hx : x ∈ D then K ⟨x, hx⟩ else 0
  have hw (b : BinarySpace (n / 2 + 1)) (a : BinarySpace n) :
      partialWalsh D K' b a = ∑ x : D, bitSign (binaryDot b (K x) + binaryDot a x) := by
    rw [partialWalsh, ← Finset.sum_coe_sort]
    simp [K', character, sign_add]
  simpa only [hw] using even_restricted_moments n hn he D K'

theorem partial_univ {n m : ℕ} (K : VectorialMap n m) (b : BinarySpace m) (a : BinarySpace n) :
    partialWalsh Finset.univ K b a = walsh (mapComponent K b) a := by
  simp [partialWalsh, walsh, mapComponent, sign_add, character]

theorem full_excess_eq {n m : ℕ} (K : VectorialMap n m) (b : BinarySpace m) :
    (∑ a, (partialWalsh Finset.univ K b a ^ 2 - spaceSize n) ^ 2) =
      fourthMoment (mapComponent K b) - (spaceSize n : ℤ) ^ 3 := by
  have hp := partial_parseval Finset.univ K b
  simp only [partial_univ, Finset.card_univ, card_binary] at hp ⊢
  have he (w : ℤ) : (w ^ 2 - spaceSize n) ^ 2 =
      w ^ 4 - 2 * (spaceSize n : ℤ) * w ^ 2 + (spaceSize n : ℤ) ^ 2 := by ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, card_binary, nsmul_eq_mul, hp, fourthMoment]
  ring

theorem even_full_moments : ∀ (n : ℕ), 4 ≤ n → Even n → ∀ (K : VectorialMap n (n / 2 + 1)),
    (spaceSize n : ℤ) ^ 3 ≤
      ∑ b ∈ Finset.univ.erase 0, (fourthMoment (mapComponent K b) - (spaceSize n : ℤ) ^ 3) := by
  intro n hn he K
  have h := even_restricted_moments n hn he Finset.univ K
  simpa only [Finset.card_univ, card_binary, full_excess_eq, ← pow_succ] using h

end
end APNLinearity.EvenBound

open scoped BigOperators

namespace APNLinearity.EvenBound
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev ComponentSpaces (m r : ℕ) :=
  {B : Submodule Bit (BinarySpace m) // Module.finrank Bit B = r}

instance componentSpacesFinite (m r : ℕ) : Finite (ComponentSpaces m r) := by
  have : Finite (Submodule Bit (BinarySpace m)) :=
    Finite.of_injective (fun B : Submodule Bit (BinarySpace m) => (B : Set (BinarySpace m)))
      SetLike.coe_injective
  infer_instance

instance componentSpacesFintype (m r : ℕ) : Fintype (ComponentSpaces m r) := Fintype.ofFinite _

theorem componentSpaces_nonempty {m r : ℕ} (hr : r ≤ m) : Nonempty (ComponentSpaces m r) := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := Bit) (M := BinarySpace m)
    (n := r) (by simpa [BinarySpace, Module.finrank_fintype_fun_eq_card] using hr)
  exact ⟨⟨Submodule.span Bit (Set.range v), by simpa using finrank_span_eq_card hv⟩⟩

def componentSpaceEquiv {m r : ℕ} (e : BinarySpace m ≃ₗ[Bit] BinarySpace m) :
    ComponentSpaces m r ≃ ComponentSpaces m r :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (by
    intro B
    change Module.finrank Bit B = r ↔ Module.finrank Bit (B.map e.toLinearMap) = r
    rw [LinearEquiv.finrank_map_eq])

@[simp] theorem mem_componentSpaceEquiv {m r : ℕ} (e : BinarySpace m ≃ₗ[Bit] BinarySpace m)
    (B : ComponentSpaces m r) (b : BinarySpace m) :
    e b ∈ (componentSpaceEquiv e B).val ↔ b ∈ B.val := by
  change e b ∈ B.val.map e.toLinearMap ↔ b ∈ B.val
  rw [Submodule.mem_map_equiv]
  simp

theorem linearEquiv_of_nonzero {m : ℕ} (x y : BinarySpace m) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : BinarySpace m ≃ₗ[Bit] BinarySpace m, e x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton Bit (BinarySpace m) x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton Bit (BinarySpace m) y hy
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e, ?_⟩
  have h := he (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h.symm

def incidence {m r : ℕ} (b : BinarySpace m) : ℤ :=
  ∑ B : ComponentSpaces m r, if b ∈ B.val then 1 else 0

theorem incidence_eq {m r : ℕ} (x y : BinarySpace m) (hx : x ≠ 0) (hy : y ≠ 0) :
    incidence (r := r) x = incidence (r := r) y := by
  classical
  obtain ⟨e, he⟩ := linearEquiv_of_nonzero x y hx hy
  unfold incidence
  apply Fintype.sum_equiv (componentSpaceEquiv e)
  intro B
  rw [← he, mem_componentSpaceEquiv]

theorem componentSpace_nonzero_card {m r : ℕ} (B : ComponentSpaces m r) :
    (∑ b ∈ Finset.univ.erase (0 : BinarySpace m), if b ∈ B.val then (1 : ℤ) else 0) =
      (spaceSize r : ℤ) - 1 := by
  classical
  let : Fintype B.val := Fintype.ofFinite _
  have hc : Fintype.card B.val = spaceSize r := by
    rw [Module.card_eq_pow_finrank (K := Bit), ZMod.card, B.property]
    rfl
  have hall : (∑ b : BinarySpace m, if b ∈ B.val then (1 : ℤ) else 0) = spaceSize r := by
    rw [← hc]
    simp [Fintype.card_subtype]
  have he := Finset.sum_erase_add Finset.univ (fun b : BinarySpace m => if b ∈ B.val then (1 : ℤ) else 0)
    (Finset.mem_univ 0)
  simp only [Submodule.zero_mem, ite_true, hall] at he
  omega

/-- Every nonzero component index has the same incidence among subspaces. -/
theorem subspace_average {m r : ℕ} (hm : 0 < m) (hr : r ≤ m)
    (f : BinarySpace m → ℤ) (S : ℤ)
    (hS : ∀ B : ComponentSpaces m r,
      S ≤ ∑ b ∈ Finset.univ.erase 0, if b ∈ B.val then f b else 0) :
    ((spaceSize m : ℤ) - 1) * S ≤
      ((spaceSize r : ℤ) - 1) * ∑ b ∈ Finset.univ.erase 0, f b := by
  classical
  let b₀ : BinarySpace m := fun _ => 1
  have hb₀ : b₀ ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hm⟩
    simp [b₀] at this
  let C := incidence (r := r) b₀
  let A : ℤ := Fintype.card (ComponentSpaces m r)
  have : Nonempty (ComponentSpaces m r) := componentSpaces_nonempty hr
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (Fintype.card_pos (α := ComponentSpaces m r))
  have hinc (b : BinarySpace m) (hb : b ∈ Finset.univ.erase 0) : incidence (r := r) b = C :=
    incidence_eq b b₀ (Finset.mem_erase.mp hb).1 hb₀
  have hcard : ((Finset.univ.erase (0 : BinarySpace m)).card : ℤ) = (spaceSize m : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_binary,
      Nat.cast_sub (spaceSize_pos m)]
    norm_num
  have hcount : A * ((spaceSize r : ℤ) - 1) = ((spaceSize m : ℤ) - 1) * C := by
    calc
      _ = ∑ B : ComponentSpaces m r, ∑ b ∈ Finset.univ.erase 0,
          if b ∈ B.val then (1 : ℤ) else 0 := by
        simp only [componentSpace_nonzero_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, A]
      _ = ∑ b ∈ Finset.univ.erase 0, incidence (r := r) b := by
        rw [Finset.sum_comm]
        rfl
      _ = _ := by simp only [Finset.sum_congr rfl hinc, Finset.sum_const, nsmul_eq_mul, hcard]
  have hsum : (∑ B : ComponentSpaces m r, ∑ b ∈ Finset.univ.erase 0,
      if b ∈ B.val then f b else 0) = C * ∑ b ∈ Finset.univ.erase 0, f b := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← hinc b hb]
    unfold incidence
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro B _
    split_ifs <;> simp
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun B _ => hS B)
  rw [hsum] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  change A * S ≤ C * ∑ b ∈ Finset.univ.erase 0, f b at hs
  have hM : 0 ≤ (spaceSize m : ℤ) - 1 := by have := spaceSize_pos m; omega
  have hmul := mul_le_mul_of_nonneg_left hs hM
  have hcount' := congrArg (fun z : ℤ => z * ∑ b ∈ Finset.univ.erase 0, f b) hcount
  apply (mul_le_mul_iff_right₀ hA).mp
  nlinarith [hmul, hcount']

/-- Coordinates dual to an embedding of component indices. -/
def dualCoordinates {r m : ℕ} (L : BinarySpace r →ₗ[Bit] BinarySpace m) (y : BinarySpace m) : BinarySpace r :=
  fun i => binaryDot (L (Pi.single i 1)) y

theorem dot_dualCoordinates {r m : ℕ} (L : BinarySpace r →ₗ[Bit] BinarySpace m)
    (b : BinarySpace r) (y : BinarySpace m) : binaryDot b (dualCoordinates L y) = binaryDot (L b) y := by
  classical
  have hb : b = ∑ i, b i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply, Pi.smul_apply]
  conv_rhs => rw [hb, map_sum]
  simp only [binaryDot, dualCoordinates, Finset.sum_apply, Pi.smul_apply, map_smul,
    Finset.sum_mul, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Finset.mul_sum, mul_assoc]


theorem sum_component_coordinates {m r : ℕ} (B : ComponentSpaces m r)
    (e : BinarySpace r ≃ₗ[Bit] B.val) (f : BinarySpace m → ℤ) :
    (∑ b ∈ Finset.univ.erase 0, f (e b).val) =
      ∑ c ∈ Finset.univ.erase 0, if c ∈ B.val then f c else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun b _ => (e b).val)
  · intro b hb
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, (e b).property⟩
    intro h
    have he : e b = 0 := Subtype.ext h
    exact (Finset.mem_erase.mp hb).1 (e.injective (by simpa using he))
  · intro a _ b _ h
    exact e.injective (Subtype.ext h)
  · intro c hc
    obtain ⟨hc, hB⟩ := Finset.mem_filter.mp hc
    refine ⟨e.symm ⟨c, hB⟩, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · intro h
      have he := congrArg e h
      simp only [e.apply_symm_apply, map_zero] at he
      exact (Finset.mem_erase.mp hc).1 (congrArg Subtype.val he)
    · simp
  · intro _ _
    rfl

/-- Averaging the restricted-domain estimate over all subspaces of component indices. -/
theorem averaged_fourth_excess {n m r : ℕ} (hm : 0 < m) (hr : r ≤ m)
    (D : Finset (BinarySpace n)) (H : VectorialMap n m)
    (v : ℤ) (hv : 0 < v) (hN : (spaceSize n : ℤ) = v ^ 2)
    (hR : (spaceSize r : ℤ) = 2 * v) (hdiv : 2 * v ∣ (spaceSize n : ℤ)) :
    ((spaceSize m : ℤ) - 1) * ((spaceSize n : ℤ) ^ 2 * D.card) ≤
      ((spaceSize r : ℤ) - 1) *
        ∑ c ∈ Finset.univ.erase 0, ∑ a, (partialWalsh D H c a ^ 2 - spaceSize n) ^ 2 := by
  apply subspace_average hm hr
  intro B
  let e : BinarySpace r ≃ₗ[Bit] B.val := LinearEquiv.ofFinrankEq (R := Bit) (BinarySpace r) B.val (by
    simp [BinarySpace, Module.finrank_fintype_fun_eq_card, B.property])
  let L : BinarySpace r →ₗ[Bit] BinarySpace m := B.val.subtype.comp e.toLinearMap
  let K : VectorialMap n r := fun x => dualCoordinates L (H x)
  have he (b : BinarySpace r) (a : BinarySpace n) :
      partialWalsh D K b a = partialWalsh D H (e b).val a := by
    unfold partialWalsh
    apply Finset.sum_congr rfl
    intro x _
    simp only [character, K, dot_dualCoordinates]
    rfl
  have h := restricted_fourth_excess D K v hv hN hR hdiv
  simp only [he] at h
  rw [sum_component_coordinates B e (fun c =>
    ∑ a, (partialWalsh D H c a ^ 2 - spaceSize n) ^ 2)] at h
  exact h

end
end APNLinearity.EvenBound

open scoped BigOperators

namespace APNLinearity.EvenBound
noncomputable section
open _root_.APNLinearity.Fourier

theorem partial_fourth_total {n m : ℕ} (D : Finset (BinarySpace n)) (H : VectorialMap n m)
    (hS : IsBinarySidon (restrictedGraph D H)) :
    (∑ c, ∑ a, partialWalsh D H c a ^ 4) =
      (spaceSize n : ℤ) * spaceSize m * (3 * (D.card : ℤ) ^ 2 - 2 * D.card) := by
  have he (a : BinarySpace n) (c : BinarySpace m) :
      productCharacterSum (restrictedGraph D H) (a, c) = partialWalsh D H c a := by
    unfold productCharacterSum
    rw [Counts.sum_restricted_graph]
    simp [partialWalsh, Sidon.product_character_eq, mul_comm]
  have h := Sidon.product_sidon_fourth_moment n m (restrictedGraph D H) hS
  simp only [Counts.restricted_graph_card, Fintype.sum_prod_type, he] at h
  rw [Finset.sum_comm] at h
  exact h

theorem partial_zero_fourth {n m : ℕ} (D : Finset (BinarySpace n)) (H : VectorialMap n m) :
    (D.card : ℤ) ^ 4 ≤ ∑ a, partialWalsh D H 0 a ^ 4 := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun a => partialWalsh D H 0 a ^ 4) (fun _ _ => by positivity)
    (Finset.mem_univ (0 : BinarySpace n))
  simpa [partialWalsh] using h

theorem partial_excess_expansion {n m : ℕ} (D : Finset (BinarySpace n)) (H : VectorialMap n m) :
    (∑ c ∈ Finset.univ.erase 0, ∑ a, (partialWalsh D H c a ^ 2 - spaceSize n) ^ 2) +
      (∑ a, partialWalsh D H 0 a ^ 4) =
    (∑ c, ∑ a, partialWalsh D H c a ^ 4) -
      ((spaceSize m : ℤ) - 1) * (spaceSize n : ℤ) ^ 2 * (2 * D.card - spaceSize n) := by
  classical
  have hp (c : BinarySpace m) : (∑ a, (partialWalsh D H c a ^ 2 - spaceSize n) ^ 2) =
      (∑ a, partialWalsh D H c a ^ 4) - (spaceSize n : ℤ) ^ 2 * (2 * D.card - spaceSize n) := by
    have he (w : ℤ) : (w ^ 2 - spaceSize n) ^ 2 =
        w ^ 4 - 2 * (spaceSize n : ℤ) * w ^ 2 + (spaceSize n : ℤ) ^ 2 := by ring
    simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, card_binary, nsmul_eq_mul, partial_parseval]
    ring
  simp only [hp, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.univ.erase (0 : BinarySpace m)).card : ℤ) = (spaceSize m : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_binary,
      Nat.cast_sub (spaceSize_pos m)]
    norm_num
  rw [hc]
  have he := Finset.sum_erase_add Finset.univ (fun c => ∑ a, partialWalsh D H c a ^ 4)
    (Finset.mem_univ (0 : BinarySpace m))
  linear_combination he

/-- Upper estimate for the excess moment of the projected Sidon graph. -/
theorem projected_excess_upper {n m : ℕ} (D : Finset (BinarySpace n)) (H : VectorialMap n m)
    (hS : IsBinarySidon (restrictedGraph D H))
    (hM : 2 * spaceSize m = spaceSize n) (t : ℤ)
    (hD : (D.card : ℤ) = (spaceSize n : ℤ) - t) (ht : 0 < t)
    (hhalf : 2 * t ≤ (spaceSize n : ℤ)) :
    (∑ c ∈ Finset.univ.erase 0, ∑ a, (partialWalsh D H c a ^ 2 - spaceSize n) ^ 2) <
      2 * (spaceSize n : ℤ) ^ 2 * t * D.card := by
  let N : ℤ := spaceSize n
  let d : ℤ := D.card
  let M : ℤ := spaceSize m
  let R : ℤ := ∑ c ∈ Finset.univ.erase 0, ∑ a, (partialWalsh D H c a ^ 2 - spaceSize n) ^ 2
  let Z : ℤ := ∑ a, partialWalsh D H 0 a ^ 4
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast spaceSize_pos n
  have hm : 2 * M = N := by
    dsimp [M, N]
    exact_mod_cast hM
  have hd : d = N - t := hD
  have hsq : N ^ 2 * (2 * d - N) ^ 2 ≤ d ^ 4 := by
    have hnon : 0 ≤ N * (2 * d - N) := mul_nonneg hN.le (by dsimp [N, d] at *; omega)
    have hle : N * (2 * d - N) ≤ d ^ 2 := by nlinarith [sq_nonneg t]
    have hh := mul_self_le_mul_self hnon hle
    nlinarith only [hh]
  have hz : d ^ 4 ≤ Z := partial_zero_fourth D H
  have he := partial_excess_expansion D H
  rw [partial_fourth_total D H hS] at he
  change R + Z = N * M * (3 * d ^ 2 - 2 * d) - (M - 1) * N ^ 2 * (2 * d - N) at he
  have hm' := congrArg (fun z : ℤ => z * (N * (3 * d ^ 2 - 2 * d) - N ^ 2 * (2 * d - N))) hm
  have hpoly : N ^ 2 * t * (4 * d - 2 - t) =
      N ^ 2 * (3 * d ^ 2 - 2 * d) - (N - 2) * N ^ 2 * (2 * d - N) -
        2 * N ^ 2 * (2 * d - N) ^ 2 := by
    have hNt : N = d + t := by omega
    rw [hNt]
    ring
  have hbase : 2 * R ≤ N ^ 2 * t * (4 * d - 2 - t) := by
    nlinarith only [hsq, hz, he, hm', hpoly]
  have hgap : 0 < N ^ 2 * t * (2 + t) := by positivity
  change R < 2 * N ^ 2 * t * d
  nlinarith [hbase, hgap]

/-- Combining the lower and upper moment bounds gives t > sqrt(N)/8. -/
theorem distance_of_moment_bounds (N v M d t R : ℝ)
    (hv : 4 ≤ v) (hN : N = v ^ 2) (hM : 2 * M = N)
    (hd : 0 < d) (hlo : (M - 1) * (N ^ 2 * d) ≤ (2 * v - 1) * R)
    (hup : R < 2 * N ^ 2 * t * d) : v / 8 < t := by
  have hv' : 0 < 2 * v - 1 := by linarith
  have hN' : 0 < N := by nlinarith
  have hpos : 0 < N ^ 2 * d := by positivity
  have hh := mul_lt_mul_of_pos_left hup hv'
  have hcancel : (M - 1) * (N ^ 2 * d) < ((2 * v - 1) * (2 * t)) * (N ^ 2 * d) := by
    nlinarith [hlo, hh]
  have hc := (mul_lt_mul_iff_left₀ hpos).mp hcancel
  by_contra h
  have ht : 0 ≤ v - 8 * t := by linarith
  have hmul := mul_nonneg hv'.le ht
  nlinarith [hc, hmul]

end
end APNLinearity.EvenBound

open scoped BigOperators

namespace APNLinearity.EvenBound
noncomputable section
open _root_.APNLinearity.Fourier

/-- Normalization at a component attaining the minimum affine distance. -/
theorem minimum_distance_projection {n : ℕ} (hn : 1 ≤ n) (F : VectorialFunction n) (hF : IsAPN F) :
    ∃ (D : Finset (BinarySpace n)) (H : VectorialMap n (n - 1)),
      D.card + nonlinearity F = spaceSize n ∧ IsBinarySidon (restrictedGraph D H) := by
  classical
  obtain ⟨b, hb, a, c, hd⟩ := distance_attained n hn F
  obtain ⟨H, hH⟩ := Normalization.normalize_component n hn F hF b hb a c
  let g := component F b + affineBoolean a c
  let E := Finset.univ.filter (fun x => g x = 1)
  have hE : E.card = nonlinearity F := by
    simpa only [distance_eq_weight, weight, E, g] using hd
  have hg : g = indicator E := by
    ext x
    rcases bit_eq_zero_or_one (g x) with hx | hx <;> simp [indicator, E, hx]
  refine ⟨Finset.univ \ E, H, ?_, ?_⟩
  · have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
    simpa only [Finset.card_univ, card_binary, hE] using h
  · apply Normalization.complement_graph_sidon n E H
    change DerivativeBound (splitMap g H) at hH
    rwa [hg] at hH

/-- The strict even-dimensional estimate before applying Walsh parity. -/
theorem even_linearity_strict {n : ℕ} (hn : 4 ≤ n) (he : Even n)
    (F : VectorialFunction n) (hF : IsAPN F) :
    (linearity F : ℝ) < (spaceSize n : ℝ) - Real.sqrt (spaceSize n : ℝ) / 4 := by
  classical
  obtain ⟨k, hnk⟩ := he
  have hk : 2 ≤ k := by omega
  let v : ℤ := 2 ^ k
  have hv : 0 < v := by positivity
  have hv4 : 4 ≤ v := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hk
    norm_num at h
    exact h
  have hN : (spaceSize n : ℤ) = v ^ 2 := by simp [spaceSize, hnk, v, pow_add, pow_two]
  have hR : (spaceSize (k + 1) : ℤ) = 2 * v := by simp [spaceSize, v, pow_succ, mul_comm]
  have hdiv : 2 * v ∣ (spaceSize n : ℤ) := by
    rw [← hR]
    exact_mod_cast (pow_dvd_pow (2 : ℕ) (show k + 1 ≤ n by omega))
  have hM : 2 * spaceSize (n - 1) = spaceSize n := by
    rw [spaceSize, spaceSize, ← pow_succ']
    congr 1
    omega
  obtain ⟨D, H, hD, hS⟩ := minimum_distance_projection (by omega) F hF
  have hlin := linearity_distance n (by omega) F
  have hp := Components.linearity_lt_size (by omega : 3 ≤ n) F hF
  have hlinR : 2 * (nonlinearity F : ℝ) + linearity F = spaceSize n := by exact_mod_cast hlin
  have ht : 0 < nonlinearity F := by
    have : (0 : ℝ) < nonlinearity F := by linarith
    exact_mod_cast this
  have hhalf : 2 * nonlinearity F ≤ spaceSize n := by
    have hL := linearity_nonneg F
    have hr : 2 * (nonlinearity F : ℝ) ≤ spaceSize n := by linarith
    exact_mod_cast hr
  have hDpos : 0 < D.card := by have := spaceSize_pos n; omega
  have hDZ : (D.card : ℤ) = (spaceSize n : ℤ) - nonlinearity F := by
    have h : (D.card : ℤ) + nonlinearity F = spaceSize n := by exact_mod_cast hD
    omega
  have hlo := averaged_fourth_excess (m := n - 1) (r := k + 1)
    (by omega) (by omega) D H v hv hN hR hdiv
  rw [hR] at hlo
  have hup := projected_excess_upper D H hS hM (nonlinearity F : ℤ) hDZ
    (by exact_mod_cast ht) (by exact_mod_cast hhalf)
  let R : ℤ := ∑ c ∈ Finset.univ.erase 0, ∑ a, (partialWalsh D H c a ^ 2 - spaceSize n) ^ 2
  have hbound := distance_of_moment_bounds (spaceSize n) v (spaceSize (n - 1)) D.card
    (nonlinearity F) R (by exact_mod_cast hv4) (by exact_mod_cast hN)
    (by exact_mod_cast hM) (by exact_mod_cast hDpos)
    (by exact_mod_cast hlo) (by exact_mod_cast hup)
  have hroot : Real.sqrt (spaceSize n : ℝ) = (v : ℝ) := by
    have hNR : (spaceSize n : ℝ) = (v : ℝ) ^ 2 := by exact_mod_cast hN
    rw [hNR, Real.sqrt_sq (by exact_mod_cast hv.le)]
  rw [hroot]
  linarith

/-- Excluding affine distances zero, one, and two. -/
theorem linearity_le_sub_six {n : ℕ} (hn : 4 ≤ n) (F : VectorialFunction n) (hF : IsAPN F) :
    (linearity F : ℝ) ≤ (spaceSize n : ℝ) - 6 := by
  obtain ⟨b, hb, a, c, hd⟩ := distance_attained n (by omega) F
  have hlin : 2 * (nonlinearity F : ℝ) + linearity F = spaceSize n := by
    exact_mod_cast linearity_distance n (by omega) F
  have hp := SmallSupport.linearity_le_sub_four n (by omega) F hF
  have htR : (2 : ℝ) ≤ nonlinearity F := by linarith
  have ht : 2 ≤ nonlinearity F := by exact_mod_cast htR
  have htwo := SmallSupport.exclude_distance_two n hn F hF b hb a c
  rw [hd] at htwo
  have hthree : (3 : ℝ) ≤ nonlinearity F := by exact_mod_cast (show 3 ≤ nonlinearity F by omega)
  linarith

theorem sqrt_spaceSize {n : ℕ} (he : Even n) :
    Real.sqrt (spaceSize n : ℝ) = (2 : ℝ) ^ (n / 2) := by
  obtain ⟨k, hk⟩ := he
  have hhalf : n / 2 = k := by omega
  have hN : (spaceSize n : ℝ) = ((2 : ℝ) ^ k) ^ 2 := by
    simp [spaceSize, hk, pow_add, pow_two]
  rw [hN, hhalf, Real.sqrt_sq (by positivity)]

theorem sqrt_quarter_multiple {n j : ℕ} (he : Even n) (hj : j + 2 ≤ n / 2) :
    Real.sqrt (spaceSize n : ℝ) / 4 =
      (2 : ℝ) ^ j * ((2 : ℕ) ^ (n / 2 - (j + 2)) : ℕ) := by
  rw [sqrt_spaceSize he]
  push_cast
  have hpow : (2 : ℝ) ^ (n / 2) =
      (2 : ℝ) ^ (n / 2 - (j + 2)) * ((2 : ℝ) ^ j * 4) := by
    calc
      _ = (2 : ℝ) ^ (n / 2 - (j + 2) + (j + 2)) := by congr 1; omega
      _ = _ := by rw [pow_add, pow_add]; norm_num
  rw [hpow]
  ring

/-- Walsh parity rounds the strict estimate down by two. -/
theorem even_linearity_bound {n : ℕ} (hn : 5 ≤ n) (he : Even n)
    (F : VectorialFunction n) (hF : IsAPN F) :
    (linearity F : ℝ) ≤ (spaceSize n : ℝ) - Real.sqrt (spaceSize n : ℝ) / 4 - 2 := by
  have hstrict := even_linearity_strict (by omega) he F hF
  have hlin : 2 * (nonlinearity F : ℝ) + linearity F = spaceSize n := by
    exact_mod_cast linearity_distance n (by omega) F
  have hh : 3 ≤ n / 2 := by obtain ⟨k, hk⟩ := he; omega
  have hroot := sqrt_quarter_multiple (j := 1) he hh
  norm_num only [pow_one] at hroot
  rw [hroot] at hstrict ⊢
  have ht : ((2 ^ (n / 2 - 3) : ℕ) : ℝ) < nonlinearity F := by linarith
  have htn : 2 ^ (n / 2 - 3) + 1 ≤ nonlinearity F := by
    have : 2 ^ (n / 2 - 3) < nonlinearity F := by exact_mod_cast ht
    omega
  have htR : ((2 ^ (n / 2 - 3) : ℕ) : ℝ) + 1 ≤ nonlinearity F := by exact_mod_cast htn
  linarith

end
end APNLinearity.EvenBound
