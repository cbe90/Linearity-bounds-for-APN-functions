module

public import APNLinearity.EvenLinearity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.OddDimension
noncomputable section
open _root_.APNLinearity.Fourier EvenBound

theorem rounded_sign_transform {m : ℕ} (v p s₀ : ℤ) (σ : BinarySpace m → ℤ)
    (hM : (spaceSize m : ℤ) = 2 * v) (hzero : σ 0 = s₀)
    (hdiv : 2 * v ∣ s₀) (hp : 2 * v ∣ p - v)
    (hs : ∀ b, b ≠ 0 → σ b = p ∨ σ b = -p) (y : BinarySpace m) :
    2 * v ∣ transform σ y - v := by
  classical
  let B : Finset (BinarySpace m) := Finset.univ.erase 0
  have hneg : 2 * v ∣ -p - v := by
    convert dvd_sub (dvd_neg.mpr hp) (dvd_refl (2 * v)) using 1
    ring
  have hb (b : BinarySpace m) (hb : b ∈ B) : 2 * v ∣ σ b * character y b - v := by
    rcases hs b (Finset.mem_erase.mp hb).1 with h | h <;>
      rcases sign_cases (binaryDot y b) with hc | hc <;>
      simp only [character, h, hc, mul_one, mul_neg_one, neg_neg] <;> assumption
  have hsum := Finset.dvd_sum hb
  have hcount : (B.card : ℤ) = 2 * v - 1 := by
    have hnat : B.card + 1 = spaceSize m := by
      simp only [B, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_binary]
      have := spaceSize_pos m
      omega
    have : (B.card : ℤ) + 1 = spaceSize m := by exact_mod_cast hnat
    omega
  have hpartition := Finset.sum_erase_add Finset.univ (fun b => σ b * character y b)
    (Finset.mem_univ (0 : BinarySpace m))
  change (∑ b ∈ B, σ b * character y b) + σ 0 * character y 0 = transform σ y at hpartition
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcount] at hsum
  rw [hzero, character_zero_right, mul_one] at hpartition
  have hd : 2 * v ∣ (2 * v - 1) * v - v := by use v - 1; ring
  have hall := dvd_add (dvd_add hsum hdiv) hd
  convert hall using 1
  nlinarith [hpartition]

/-- The Fourier comparison on a component-index space of size `2*v`. -/
theorem rounded_spectrum_distance {m : ℕ} (T : BinarySpace m → ℤ) (v p s₀ : ℤ)
    (hv : 0 < v) (hM : (spaceSize m : ℤ) = 2 * v) (hdiv : 2 * v ∣ s₀)
    (hp : 2 * v ∣ p - v) (hzero : T 0 = s₀)
    (hT : ∀ y, 2 * v ∣ transform T y) :
    v ^ 2 ≤ ∑ b ∈ Finset.univ.erase 0, (|T b| - p) ^ 2 := by
  classical
  let σ : BinarySpace m → ℤ := fun b => if b = 0 then s₀ else if 0 ≤ T b then p else -p
  have hs : ∀ b, b ≠ 0 → σ b = p ∨ σ b = -p := by
    intro b hb
    simp only [σ, ite_eq_right hb]
    split_ifs <;> simp
  have hz : σ 0 = s₀ := by simp [σ]
  have hsq (y : BinarySpace m) : v ^ 2 ≤ transform (fun b => T b - σ b) y ^ 2 := by
    have he : transform (fun b => T b - σ b) y = transform T y - transform σ y := by
      simp [transform, sub_mul, Finset.sum_sub_distrib]
    have hd := rounded_sign_transform v p s₀ σ hM hz hdiv hp hs y
    have hh := dvd_sub (dvd_sub (hT y) hd) (dvd_refl (2 * v))
    apply odd_multiple_square v _ hv
    rw [he]
    convert hh using 1
    ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hsq y)
  rw [transform_parseval] at hsum
  simp only [Finset.sum_const, Finset.card_univ, card_binary, nsmul_eq_mul] at hsum
  have hm : (0 : ℤ) < spaceSize m := by exact_mod_cast spaceSize_pos m
  have hbound := (mul_le_mul_iff_right₀ hm).mp hsum
  have hterm (b : BinarySpace m) (hb : b ∈ Finset.univ.erase 0) :
      (T b - σ b) ^ 2 = (|T b| - p) ^ 2 := by
    simp only [σ, ite_eq_right (Finset.mem_erase.mp hb).1]
    split_ifs with ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (by omega : T b < 0)]
      ring
  have he := Finset.sum_erase_add Finset.univ (fun b => (T b - σ b) ^ 2)
    (Finset.mem_univ (0 : BinarySpace m))
  rw [Finset.sum_congr rfl hterm, hz, hzero, sub_self, zero_pow (by decide), add_zero] at he
  rwa [← he] at hbound

/-- Either all deviations are small, or a single large deviation supplies the bound. -/
theorem fourth_deviation_bound {ι : Type*} (S : Finset ι) (w : ι → ℤ) (v p : ℤ)
    (hv : 0 ≤ v) (hp : v ≤ p) (hd : v ^ 2 ≤ ∑ i ∈ S, (|w i| - p) ^ 2) :
    v ^ 2 * (2 * p - v) ^ 2 ≤ ∑ i ∈ S, (w i ^ 2 - p ^ 2) ^ 2 := by
  classical
  have he (i : ι) : (w i ^ 2 - p ^ 2) ^ 2 = (|w i| - p) ^ 2 * (|w i| + p) ^ 2 := by
    calc
      _ = (|w i| ^ 2 - p ^ 2) ^ 2 := by rw [sq_abs]
      _ = _ := by ring
  by_cases hsmall : ∀ i ∈ S, |(|w i| - p)| < v
  · have h := mul_le_mul_of_nonneg_left hd (sq_nonneg (2 * p - v))
    have hh : (2 * p - v) ^ 2 * (∑ i ∈ S, (|w i| - p) ^ 2) ≤
        ∑ i ∈ S, (w i ^ 2 - p ^ 2) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hlow := (abs_lt.mp (hsmall i hi)).1
      have hsq := pow_le_pow_left₀ (show 0 ≤ 2 * p - v by omega)
        (show 2 * p - v ≤ |w i| + p by omega) 2
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (|w i| - p))]
    nlinarith only [h, hh]
  · obtain ⟨i, hlarge⟩ := not_forall.mp hsmall
    obtain ⟨hi, hlarge⟩ := not_imp.mp hlarge
    have hl : v ≤ |(|w i| - p)| := le_of_not_gt hlarge
    have hsingle : v * (2 * p - v) ≤ |w i ^ 2 - p ^ 2| := by
      rcases le_abs.mp hl with hhigh | hlow
      · have hsq := pow_le_pow_left₀ (show 0 ≤ p + v by omega)
          (show p + v ≤ |w i| by omega) 2
        rw [sq_abs] at hsq
        have ha := le_abs_self (w i ^ 2 - p ^ 2)
        nlinarith [sq_nonneg v]
      · have hsq := pow_le_pow_left₀ (abs_nonneg (w i))
          (show |w i| ≤ p - v by omega) 2
        rw [sq_abs] at hsq
        have ha := neg_le_abs (w i ^ 2 - p ^ 2)
        nlinarith
    have hsq := pow_le_pow_left₀ (mul_nonneg hv (by omega)) hsingle 2
    rw [sq_abs, mul_pow] at hsq
    exact hsq.trans (Finset.single_le_sum (fun j _ => sq_nonneg (w j ^ 2 - p ^ 2)) hi)

theorem full_walsh_comparison {n m : ℕ} (K : VectorialMap n m) (a : BinarySpace n)
    (v p : ℤ) (hv : 0 < v) (hpv : v ≤ p) (hM : (spaceSize m : ℤ) = 2 * v)
    (hdiv : 2 * v ∣ (spaceSize n : ℤ)) (hp : 2 * v ∣ p - v) :
    v ^ 2 * (2 * p - v) ^ 2 ≤
      ∑ b ∈ Finset.univ.erase 0, (walsh (mapComponent K b) a ^ 2 - p ^ 2) ^ 2 := by
  apply fourth_deviation_bound _ _ v p hv.le hpv
  apply rounded_spectrum_distance _ v p (if a = 0 then (spaceSize n : ℤ) else 0)
    hv hM (by split_ifs; exact hdiv; exact dvd_zero _) hp
  · simp only [walsh, mapComponent, dot_zero_left, zero_add]
    change (∑ x, character a x) = _
    simpa only [character_comm] using character_orthogonality n a
  · intro y
    rw [← hM]
    simpa only [partial_univ] using output_transform_dvd Finset.univ K a y

end
end APNLinearity.OddDimension

namespace APNLinearity.OddDimension
noncomputable section

theorem nearest_sqrt_distance (n p : ℕ)
    (hp : p = ⌊Real.sqrt (spaceSize n : ℝ)⌋₊ ∨ p = ⌈Real.sqrt (spaceSize n : ℝ)⌉₊) :
    |(p : ℝ) - Real.sqrt (spaceSize n : ℝ)| < 1 := by
  rcases hp with rfl | rfl
  · have hle := Nat.floor_le (Real.sqrt_nonneg (spaceSize n : ℝ))
    have hlt := Nat.lt_floor_add_one (Real.sqrt (spaceSize n : ℝ))
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · have hle := Nat.le_ceil (Real.sqrt (spaceSize n : ℝ))
    have hlt := Nat.ceil_lt_add_one (Real.sqrt_nonneg (spaceSize n : ℝ))
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- In odd dimension at least five, both neighboring integers lie strictly between consecutive powers of two. -/
theorem odd_nearest_between {n p : ℕ} (hn : 5 ≤ n) (ho : Odd n)
    (hp : |(p : ℝ) - Real.sqrt (spaceSize n : ℝ)| < 1) :
    ∃ k : ℕ, n = 2 * k + 1 ∧ 2 ≤ k ∧ 2 ^ k < p ∧ p < 2 ^ (k + 1) := by
  obtain ⟨k, hk⟩ := ho.exists_bit1
  have hk2 : 2 ≤ k := by omega
  let q : ℝ := 2 ^ k
  have hq : 4 ≤ q := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk2
    norm_num at h
    exact h
  have hN : (spaceSize n : ℝ) = 2 * q ^ 2 := by
    change ((2 ^ n : ℕ) : ℝ) = 2 * q ^ 2
    push_cast
    rw [hk, pow_add, pow_one, show 2 * k = k + k by omega, pow_add]
    dsimp [q]
    ring
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ spaceSize n by positivity)
  have hs0 := Real.sqrt_nonneg (spaceSize n : ℝ)
  have hlo : q + 1 < Real.sqrt (spaceSize n : ℝ) := by
    by_contra h
    have hsq := pow_le_pow_left₀ hs0 (le_of_not_gt h) 2
    nlinarith [sq_nonneg (q - 4)]
  have hhi : Real.sqrt (spaceSize n : ℝ) < 2 * q - 1 := by
    by_contra h
    have hsq := pow_le_pow_left₀ (show 0 ≤ 2 * q - 1 by linarith) (le_of_not_gt h) 2
    nlinarith [sq_nonneg (q - 4)]
  obtain ⟨hp1, hp2⟩ := abs_lt.mp hp
  refine ⟨k, hk, hk2, ?_, ?_⟩
  · have h : (2 : ℝ) ^ k < p := by change q < p; linarith
    exact_mod_cast h
  · have h : (p : ℝ) < (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      change (p : ℝ) < q * 2
      linarith
    exact_mod_cast h

theorem odd_nearest_parameters {n p s : ℕ} (hn : 5 ≤ n) (ho : Odd n)
    (hp : p = ⌊Real.sqrt (spaceSize n : ℝ)⌋₊ ∨ p = ⌈Real.sqrt (spaceSize n : ℝ)⌉₊)
    (hd : 2 ^ s ∣ p) (hnd : ¬ 2 ^ (s + 1) ∣ p) (hs : 5 ≤ s) :
    |(p : ℝ) - Real.sqrt (spaceSize n : ℝ)| < 1 ∧
      (2 * (2 : ℤ) ^ s ∣ (p : ℤ) - (2 : ℤ) ^ s) ∧
      3 * 2 ^ s ≤ p ∧ s + 1 < n ∧ 4 * 2 ^ s ≤ spaceSize n ∧ 32 ≤ 2 ^ s := by
  have hclose := nearest_sqrt_distance n p hp
  obtain ⟨k, hk, hk2, hklo, hkhi⟩ := odd_nearest_between hn ho hclose
  have hne : p ≠ 2 ^ s := by
    intro he
    by_cases hsk : s ≤ k
    · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hsk
      omega
    · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show k + 1 ≤ s by omega)
      omega
  obtain ⟨t, ht⟩ := hd
  have htodd : Odd t := by
    apply Nat.not_even_iff_odd.mp
    intro he
    obtain ⟨u, hu⟩ := even_iff_two_dvd.mp he
    apply hnd
    refine ⟨u, ?_⟩
    rw [ht, hu, pow_succ]
    ring
  have ht0 : t ≠ 0 := by intro he; simp only [he, mul_zero] at ht; omega
  have ht1 : t ≠ 1 := by intro he; simp only [he, mul_one] at ht; exact hne ht
  have ht3 : 3 ≤ t := by have hmod := Nat.odd_iff.mp htodd; omega
  have hp3 : 3 * 2 ^ s ≤ p := by
    rw [ht]
    nlinarith [Nat.mul_le_mul_left (2 ^ s) ht3]
  have hsle : s ≤ k := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show k + 1 ≤ s by omega)
    omega
  have hspan : s + 1 < n := by omega
  have hsize : 4 * 2 ^ s ≤ spaceSize n := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show s + 2 ≤ n by omega)
    simpa only [spaceSize, pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm] using hpow
  have hv32 : 32 ≤ 2 ^ s := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hs
    norm_num at hpow
    exact hpow
  refine ⟨hclose, ?_, hp3, hspan, hsize, hv32⟩
  obtain ⟨u, hu⟩ := htodd.exists_bit1
  have htZ : (p : ℤ) = (2 : ℤ) ^ s * (2 * (u : ℤ) + 1) := by
    exact_mod_cast (show p = 2 ^ s * (2 * u + 1) by rw [ht, hu])
  refine ⟨(u : ℤ), ?_⟩
  rw [htZ]
  ring

/-- The two numerical estimates used in the subspace excess-moment bound. -/
theorem nearest_moment_estimates (N p v : ℝ) (hN : 32 ≤ N) (hv : 32 ≤ v)
    (hp : 3 * v ≤ p) (hclose : |p - Real.sqrt N| < 1) :
    5 * N < 2 * (2 * p - v) ^ 2 ∧ (p ^ 2 - N) ^ 2 < 5 * N := by
  have hp96 : 96 ≤ p := by linarith
  have hs := Real.sq_sqrt (show 0 ≤ N by linarith)
  have hs0 := Real.sqrt_nonneg N
  obtain ⟨hc1, hc2⟩ := abs_lt.mp hclose
  have hNlt : N < (p + 1) ^ 2 := by
    have h := mul_pos (show 0 < p + 1 - Real.sqrt N by linarith)
      (show 0 < p + 1 + Real.sqrt N by linarith)
    nlinarith
  constructor
  · have hsq := pow_le_pow_left₀ (show 0 ≤ 5 * p by linarith)
      (show 5 * p ≤ 3 * (2 * p - v) by linarith) 2
    have hpoly := mul_nonneg (show 0 ≤ p - 96 by linarith)
      (show 0 ≤ 5 * p + 390 by linarith)
    nlinarith [hNlt, hsq, hpoly]
  · have hd : (p - Real.sqrt N) ^ 2 < 1 := by
      have h := mul_pos (show 0 < 1 - (p - Real.sqrt N) by linarith)
        (show 0 < 1 + (p - Real.sqrt N) by linarith)
      nlinarith
    have hsum : (p + Real.sqrt N) ^ 2 < (2 * Real.sqrt N + 1) ^ 2 := by
      have h := mul_pos (show 0 < 2 * Real.sqrt N + 1 - (p + Real.sqrt N) by linarith)
        (show 0 < 2 * Real.sqrt N + 1 + (p + Real.sqrt N) by linarith)
      nlinarith
    have hlast : (2 * Real.sqrt N + 1) ^ 2 < 5 * N := by
      nlinarith [sq_nonneg (Real.sqrt N - 4)]
    have hid : (p ^ 2 - N) ^ 2 = (p - Real.sqrt N) ^ 2 * (p + Real.sqrt N) ^ 2 := by
      calc
        _ = (p ^ 2 - (Real.sqrt N) ^ 2) ^ 2 := by rw [hs]
        _ = _ := by ring
    rw [hid]
    have hpos : 0 < (p + Real.sqrt N) ^ 2 := sq_pos_of_pos (by linarith)
    have hmul := mul_lt_mul_of_pos_right hd hpos
    nlinarith only [hmul, hsum, hlast]

end
end APNLinearity.OddDimension

open scoped BigOperators

namespace APNLinearity.OddDimension
noncomputable section
open EvenBound
attribute [local instance] Classical.propDecidable

def pairMap {m : ℕ} (z x : BinarySpace m) : BinarySpace 2 →ₗ[Bit] BinarySpace m :=
  (LinearMap.proj 0).smulRight z + (LinearMap.proj 1).smulRight x

theorem pairMap_injective {m : ℕ} (z x : BinarySpace m) (hz : z ≠ 0) (hx : x ≠ 0)
    (hxz : x ≠ z) : Function.Injective (pairMap z x) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  change a 0 • z + a 1 • x = 0 at ha
  rcases bit_eq_zero_or_one (a 0) with h0 | h0 <;>
    rcases bit_eq_zero_or_one (a 1) with h1 | h1
  · ext i
    fin_cases i <;> simp [h0, h1]
  · simp only [h0, h1, zero_smul, one_smul, zero_add] at ha
    exact (hx ha).elim
  · simp only [h0, h1, zero_smul, one_smul, add_zero] at ha
    exact (hz ha).elim
  · simp only [h0, h1, one_smul] at ha
    exact (hxz ((binary_add_eq_zero_iff z x).mp ha).symm).elim

/-- The stabilizer of a nonzero vector acts transitively on the other nonzero vectors. -/
theorem linearEquiv_fix_and_map {m : ℕ} (z x y : BinarySpace m)
    (hz : z ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ e : BinarySpace m ≃ₗ[Bit] BinarySpace m, e z = z ∧ e x = y := by
  let Lx := pairMap z x
  let Ly := pairMap z y
  let ex := LinearEquiv.ofInjective Lx (pairMap_injective z x hz hx hxz)
  let ey := LinearEquiv.ofInjective Ly (pairMap_injective z y hz hy hyz)
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  have hev (a : BinarySpace 2) : e (Lx a) = Ly a := by
    have h := he (ex a)
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
    exact h.symm
  refine ⟨e, ?_, ?_⟩
  · simpa [Lx, Ly, pairMap] using hev (Pi.single 0 1)
  · simpa [Lx, Ly, pairMap] using hev (Pi.single 1 1)

abbrev AvoidingSpaces (m r : ℕ) (z : BinarySpace m) :=
  {B : ComponentSpaces m r // z ∉ B.val}

instance avoidingSpacesFintype (m r : ℕ) (z : BinarySpace m) : Fintype (AvoidingSpaces m r z) :=
  Fintype.ofFinite _

theorem avoidingSpaces_nonempty {m r : ℕ} (hr : r < m) (z : BinarySpace m) (hz : z ≠ 0) :
    Nonempty (AvoidingSpaces m r z) := by
  obtain ⟨B⟩ := componentSpaces_nonempty hr.le
  have hproper : B.val ≠ ⊤ := by
    intro h
    have hf := B.property
    rw [h] at hf
    simp only [finrank_top, BinarySpace, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hf
    omega
  obtain ⟨x, hx⟩ : ∃ x : BinarySpace m, x ∉ B.val := by
    by_contra h
    push Not at h
    apply hproper
    ext x
    simp [h x]
  have hx0 : x ≠ 0 := by intro h; apply hx; rw [h]; exact B.val.zero_mem
  obtain ⟨e, he⟩ := linearEquiv_of_nonzero x z hx0 hz
  refine ⟨⟨componentSpaceEquiv e B, ?_⟩⟩
  intro hb
  apply hx
  apply (mem_componentSpaceEquiv e B x).mp
  rwa [he]

def avoidingSpaceEquiv {m r : ℕ} {z : BinarySpace m} (e : BinarySpace m ≃ₗ[Bit] BinarySpace m)
    (he : e z = z) : AvoidingSpaces m r z ≃ AvoidingSpaces m r z :=
  (componentSpaceEquiv e).subtypeEquiv (by
    intro B
    conv_rhs => rw [← he, mem_componentSpaceEquiv])

@[simp] theorem mem_avoidingSpaceEquiv {m r : ℕ} {z : BinarySpace m}
    (e : BinarySpace m ≃ₗ[Bit] BinarySpace m) (he : e z = z) (B : AvoidingSpaces m r z) (b : BinarySpace m) :
    e b ∈ (avoidingSpaceEquiv e he B).val.val ↔ b ∈ B.val.val :=
  mem_componentSpaceEquiv e B.val b

def avoidingIncidence {m r : ℕ} (z b : BinarySpace m) : ℤ :=
  ∑ B : AvoidingSpaces m r z, if b ∈ B.val.val then 1 else 0

theorem avoidingIncidence_eq {m r : ℕ} (z x y : BinarySpace m)
    (hz : z ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hxz : x ≠ z) (hyz : y ≠ z) :
    avoidingIncidence (r := r) z x = avoidingIncidence (r := r) z y := by
  obtain ⟨e, hez, hexy⟩ := linearEquiv_fix_and_map z x y hz hx hy hxz hyz
  unfold avoidingIncidence
  apply Fintype.sum_equiv (avoidingSpaceEquiv e hez)
  intro B
  rw [← hexy, mem_avoidingSpaceEquiv]

/-- Strict averaging over all subspaces of the prescribed dimension avoiding `z`. -/
theorem avoiding_subspace_average {m r : ℕ} (hm : 2 ≤ m) (hr : r < m)
    (z : BinarySpace m) (hz : z ≠ 0) (f : BinarySpace m → ℤ) (S : ℤ)
    (hS : ∀ B : AvoidingSpaces m r z,
      S < ∑ b ∈ (Finset.univ.erase 0).erase z, if b ∈ B.val.val then f b else 0) :
    ((spaceSize m : ℤ) - 2) * S <
      ((spaceSize r : ℤ) - 1) * ∑ b ∈ (Finset.univ.erase 0).erase z, f b := by
  let I : Finset (BinarySpace m) := (Finset.univ.erase 0).erase z
  have hsize : 4 ≤ spaceSize m := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hm
    norm_num at h
    exact h
  have hcard : (I.card : ℤ) = (spaceSize m : ℤ) - 2 := by
    have hnat : I.card + 2 = spaceSize m := by
      simp only [I, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_binary]
      omega
    have h : (I.card : ℤ) + 2 = spaceSize m := by exact_mod_cast hnat
    omega
  obtain ⟨b₁, hb₁⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hb₁z := (Finset.mem_erase.mp hb₁).1
  have hb₁0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hb₁).2).1
  let C := avoidingIncidence (r := r) z b₁
  let A : ℤ := Fintype.card (AvoidingSpaces m r z)
  have : Nonempty (AvoidingSpaces m r z) := avoidingSpaces_nonempty hr z hz
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (Fintype.card_pos (α := AvoidingSpaces m r z))
  have hinc (b : BinarySpace m) (hb : b ∈ I) : avoidingIncidence (r := r) z b = C :=
    avoidingIncidence_eq z b b₁ hz
      (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1 hb₁0
      (Finset.mem_erase.mp hb).1 hb₁z
  have hBcard (B : AvoidingSpaces m r z) :
      (∑ b ∈ I, if b ∈ B.val.val then (1 : ℤ) else 0) = (spaceSize r : ℤ) - 1 := by
    have h := Finset.sum_erase_add (Finset.univ.erase 0)
      (fun b => if b ∈ B.val.val then (1 : ℤ) else 0)
      (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ _⟩)
    rw [ite_eq_right B.property, add_zero, componentSpace_nonzero_card B.val] at h
    exact h
  have hcount : A * ((spaceSize r : ℤ) - 1) = ((spaceSize m : ℤ) - 2) * C := by
    calc
      _ = ∑ B : AvoidingSpaces m r z, ∑ b ∈ I, if b ∈ B.val.val then (1 : ℤ) else 0 := by
        simp only [hBcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, A]
      _ = ∑ b ∈ I, avoidingIncidence (r := r) z b := by rw [Finset.sum_comm]; rfl
      _ = _ := by simp only [Finset.sum_congr rfl hinc, Finset.sum_const, nsmul_eq_mul, hcard]
  have hsum : (∑ B : AvoidingSpaces m r z, ∑ b ∈ I,
      if b ∈ B.val.val then f b else 0) = C * ∑ b ∈ I, f b := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← hinc b hb]
    unfold avoidingIncidence
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro B _
    split_ifs <;> simp
  have hs := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    (fun B _ => hS B)
  change (∑ _B : AvoidingSpaces m r z, S) < ∑ B : AvoidingSpaces m r z,
    ∑ b ∈ I, if b ∈ B.val.val then f b else 0 at hs
  rw [hsum] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  change A * S < C * ∑ b ∈ I, f b at hs
  have hM : 0 < (spaceSize m : ℤ) - 2 := by omega
  have hmul := mul_lt_mul_of_pos_left hs hM
  have hcount' := congrArg (fun q : ℤ => q * ∑ b ∈ I, f b) hcount
  apply (mul_lt_mul_iff_right₀ hA).mp
  nlinarith [hmul, hcount']

end
end APNLinearity.OddDimension

open scoped BigOperators

namespace APNLinearity.OddDimension
noncomputable section
open _root_.APNLinearity.Fourier EvenBound
attribute [local instance] Classical.propDecidable

/-- The pointwise Walsh comparison on an arbitrary component subspace. -/
theorem subspace_walsh_comparison {n r : ℕ} (F : VectorialFunction n)
    (B : ComponentSpaces n r) (a : BinarySpace n) (v p : ℤ)
    (hv : 0 < v) (hpv : v ≤ p) (hR : (spaceSize r : ℤ) = 2 * v)
    (hdiv : 2 * v ∣ (spaceSize n : ℤ)) (hp : 2 * v ∣ p - v) :
    v ^ 2 * (2 * p - v) ^ 2 ≤ ∑ b ∈ Finset.univ.erase 0,
      if b ∈ B.val then (walsh (component F b) a ^ 2 - p ^ 2) ^ 2 else 0 := by
  classical
  let e : BinarySpace r ≃ₗ[Bit] B.val := LinearEquiv.ofFinrankEq (R := Bit) (BinarySpace r) B.val (by
    simp [BinarySpace, Module.finrank_fintype_fun_eq_card, B.property])
  let L : BinarySpace r →ₗ[Bit] BinarySpace n := B.val.subtype.comp e.toLinearMap
  let K : VectorialMap n r := fun x => dualCoordinates L (F x)
  have he (b : BinarySpace r) : mapComponent K b = component F (e b).val := by
    funext x
    exact dot_dualCoordinates L b (F x)
  have h := full_walsh_comparison K a v p hv hpv hR hdiv hp
  simp only [he] at h
  rwa [sum_component_coordinates B e (fun b => (walsh (component F b) a ^ 2 - p ^ 2) ^ 2)] at h

/-- Expanding the shifted square and applying Parseval. -/
theorem shifted_fourth_expansion {n m : ℕ} (F : VectorialMap n m) (b : BinarySpace m) (p : ℤ) :
    (∑ a, (walsh (mapComponent F b) a ^ 2 - p ^ 2) ^ 2) =
      fourthMoment (mapComponent F b) - (spaceSize n : ℤ) ^ 3 +
        (spaceSize n : ℤ) * (p ^ 2 - spaceSize n) ^ 2 := by
  have hp := walsh_parseval n (mapComponent F b)
  have he (w : ℤ) : (w ^ 2 - p ^ 2) ^ 2 = w ^ 4 - 2 * p ^ 2 * w ^ 2 + p ^ 4 := by ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, card_binary, nsmul_eq_mul, hp, fourthMoment]
  ring

def excess {n : ℕ} (F : VectorialFunction n) (b : BinarySpace n) : ℤ :=
  fourthMoment (component F b) - (spaceSize n : ℤ) ^ 3

theorem subspace_excess_lower {n r : ℕ} (F : VectorialFunction n) (B : ComponentSpaces n r)
    (v p : ℤ) (hv : 0 < v) (hpv : v ≤ p) (hR : (spaceSize r : ℤ) = 2 * v)
    (hdiv : 2 * v ∣ (spaceSize n : ℤ)) (hp : 2 * v ∣ p - v) :
    (spaceSize n : ℤ) * (v ^ 2 * (2 * p - v) ^ 2 - (2 * v - 1) * (p ^ 2 - spaceSize n) ^ 2) ≤
      ∑ b ∈ Finset.univ.erase 0, if b ∈ B.val then excess F b else 0 := by
  classical
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ => subspace_walsh_comparison F B a v p hv hpv hR hdiv hp)
  simp only [Finset.sum_const, Finset.card_univ, card_binary, nsmul_eq_mul] at h
  rw [Finset.sum_comm] at h
  have he (b : BinarySpace n) :
      (∑ a, if b ∈ B.val then (walsh (component F b) a ^ 2 - p ^ 2) ^ 2 else 0) =
      (if b ∈ B.val then excess F b else 0) +
      (if b ∈ B.val then (1 : ℤ) else 0) *
        ((spaceSize n : ℤ) * (p ^ 2 - spaceSize n) ^ 2) := by
    split_ifs
    · have hcomponent : mapComponent F b = component F b := rfl
      simpa only [one_mul, excess, hcomponent] using shifted_fourth_expansion F b p
    · simp
  simp only [he, Finset.sum_add_distrib, ← Finset.sum_mul,
    componentSpace_nonzero_card B, hR] at h
  nlinarith only [h]

/-- The strict subspace bound on the excess fourth moments. -/
theorem subspace_excess_strict {n r : ℕ} (F : VectorialFunction n) (B : ComponentSpaces n r)
    (v p : ℤ) (hN : 32 ≤ spaceSize n) (hv : 32 ≤ v) (hpv : 3 * v ≤ p)
    (hclose : |(p : ℝ) - Real.sqrt (spaceSize n : ℝ)| < 1)
    (hR : (spaceSize r : ℤ) = 2 * v) (hdiv : 2 * v ∣ (spaceSize n : ℤ))
    (hp : 2 * v ∣ p - v) :
    5 * (spaceSize n : ℤ) ^ 2 * v * (v - 4) <
      2 * ∑ b ∈ Finset.univ.erase 0, if b ∈ B.val then excess F b else 0 := by
  classical
  have hNZ : (32 : ℤ) ≤ spaceSize n := by exact_mod_cast hN
  have hN0 : (0 : ℤ) < spaceSize n := by omega
  obtain ⟨h1, h2⟩ := nearest_moment_estimates (spaceSize n) p v
    (by exact_mod_cast hN) (by exact_mod_cast hv) (by exact_mod_cast hpv) hclose
  have h1Z : 5 * (spaceSize n : ℤ) < 2 * (2 * p - v) ^ 2 := by exact_mod_cast h1
  have h2Z : (p ^ 2 - (spaceSize n : ℤ)) ^ 2 < 5 * spaceSize n := by exact_mod_cast h2
  have hlow := subspace_excess_lower F B v p (by omega) (by omega) hR hdiv hp
  have hmul1 := mul_lt_mul_of_pos_left h1Z (show 0 < (spaceSize n : ℤ) * v ^ 2 by positivity)
  have hmul2 := mul_lt_mul_of_pos_left h2Z (show 0 < 2 * (spaceSize n : ℤ) * (2 * v - 1) from mul_pos (by positivity) (by omega))
  nlinarith only [hlow, hmul1, hmul2, sq_nonneg (spaceSize n : ℤ)]

theorem total_excess {n : ℕ} (F : VectorialFunction n) (hF : IsAPN F) :
    (∑ b ∈ Finset.univ.erase 0, excess F b) = (spaceSize n : ℤ) ^ 4 - (spaceSize n : ℤ) ^ 3 := by
  classical
  have hcard : ((Finset.univ.erase (0 : BinarySpace n)).card : ℤ) = (spaceSize n : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_binary,
      Nat.cast_sub (spaceSize_pos n)]
    norm_num
  simp only [excess, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard,
    Sidon.apn_fourth_moment n F hF]
  ring

/-- Isolating a component that attains the linearity in the APN fourth-moment identity. -/
theorem attaining_fourth_bound {n : ℕ} (hn : 1 ≤ n)
    (F : VectorialFunction n) (hF : IsAPN F) :
    ∃ b₀ : BinarySpace n, b₀ ≠ 0 ∧ linearity F ^ 4 ≤
      (spaceSize n : ℝ) ^ 4 - ((∑ b ∈ (Finset.univ.erase 0).erase b₀, excess F b : ℤ) : ℝ) := by
  classical
  obtain ⟨a, b, hb, hw⟩ := linearity_attained hn F
  have hfourth : linearity F ^ 4 ≤ (fourthMoment (component F b) : ℝ) := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun a => walsh (component F b) a ^ 4)
      (fun a _ => by positivity : ∀ a ∈ Finset.univ, (0 : ℤ) ≤ walsh (component F b) a ^ 4)
      (Finset.mem_univ a)
    have hr : (walsh (component F b) a : ℝ) ^ 4 ≤
        (fourthMoment (component F b) : ℝ) := by exact_mod_cast h
    rw [hw, natAbs_cast_real]
    simpa only [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs] using hr
  have he := Finset.sum_erase_add (Finset.univ.erase 0) (excess F)
    (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩)
  rw [total_excess F hF] at he
  rw [show excess F b = fourthMoment (component F b) - (spaceSize n : ℤ) ^ 3 from rfl] at he
  have heR := congrArg (fun z : ℤ => (z : ℝ)) he
  push_cast at heR
  refine ⟨b, hb, ?_⟩
  push_cast
  linarith

end
end APNLinearity.OddDimension

namespace APNLinearity.OddDimension

/-- The numerical factor in the averaged moment loss is at least `25/24`. -/
theorem averaged_loss (N v E : ℝ) (hN : 32 ≤ N) (hv : 32 ≤ v)
    (havg : (N - 2) * (5 * N ^ 2 * v * (v - 4)) < (2 * v - 1) * (2 * E)) :
    v * N ^ 3 < E := by
  have h1 : 15 * N ≤ 16 * (N - 2) := by linarith
  have h2 : 28 * (2 * v - 1) ≤ 63 * (v - 4) := by linarith
  have hprod := mul_le_mul h1 h2 (by linarith : 0 ≤ 28 * (2 * v - 1))
    (by linarith : 0 ≤ 16 * (N - 2))
  have hratio : 25 * (2 * (2 * v - 1) * N) ≤ 24 * (5 * (N - 2) * (v - 4)) := by
    nlinarith only [hprod]
  have hpos : 0 < 2 * (2 * v - 1) * N :=
    mul_pos (by linarith) (by linarith)
  have hstrict : 2 * (2 * v - 1) * N < 5 * (N - 2) * (v - 4) := by
    linarith only [hratio, hpos]
  have hm := mul_lt_mul_of_pos_right hstrict (show 0 < N ^ 2 * v by positivity)
  have hf : 0 < 2 * (2 * v - 1) := by linarith
  apply (mul_lt_mul_iff_right₀ hf).mp
  nlinarith only [hm, havg]

/-- The fourth-root comparison, expressed as a polynomial inequality. -/
theorem linearity_of_fourth_loss (N v L : ℝ) (hN : 0 < N) (_hv : 0 < v)
    (hvN : v ≤ N) (_hL : 0 ≤ L) (hfourth : L ^ 4 < N ^ 4 - v * N ^ 3) :
    L < N - v / 4 := by
  have ht : 0 ≤ N - v / 4 := by linarith
  have hc : 0 ≤ 96 * N ^ 2 - 16 * N * v + v ^ 2 := by
    nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hvN), sq_nonneg v]
  have hp := mul_nonneg (sq_nonneg v) hc
  have hbernoulli : N ^ 4 - v * N ^ 3 ≤ (N - v / 4) ^ 4 := by
    nlinarith only [hp]
  by_contra h
  have hpow := pow_le_pow_left₀ ht (le_of_not_gt h) 4
  linarith only [hfourth, hbernoulli, hpow]

end APNLinearity.OddDimension

open scoped BigOperators

namespace APNLinearity.OddDimension
noncomputable section
open _root_.APNLinearity.Fourier EvenBound
attribute [local instance] Classical.propDecidable

/-- Averaging the subspace excess bound after excluding a maximizing component. -/
theorem averaged_excess_strict {n r : ℕ} (hn : 5 ≤ n) (hr : r < n)
    (F : VectorialFunction n) (b₀ : BinarySpace n) (hb₀ : b₀ ≠ 0) (v p : ℤ)
    (hN : 32 ≤ spaceSize n) (hv : 32 ≤ v) (hpv : 3 * v ≤ p)
    (hclose : |(p : ℝ) - Real.sqrt (spaceSize n : ℝ)| < 1)
    (hR : (spaceSize r : ℤ) = 2 * v) (hdiv : 2 * v ∣ (spaceSize n : ℤ))
    (hp : 2 * v ∣ p - v) :
    ((spaceSize n : ℤ) - 2) * (5 * (spaceSize n : ℤ) ^ 2 * v * (v - 4)) <
      (2 * v - 1) * (2 * ∑ b ∈ (Finset.univ.erase 0).erase b₀, excess F b) := by
  have h := avoiding_subspace_average (by omega : 2 ≤ n) hr b₀ hb₀
    (fun b => 2 * excess F b) (5 * (spaceSize n : ℤ) ^ 2 * v * (v - 4)) (by
      intro B
      have hS := subspace_excess_strict F B.val v p hN hv hpv hclose hR hdiv hp
      have he := Finset.sum_erase_add (Finset.univ.erase 0)
        (fun b => if b ∈ B.val.val then excess F b else 0)
        (Finset.mem_erase.mpr ⟨hb₀, Finset.mem_univ b₀⟩)
      rw [ite_eq_right B.property, add_zero] at he
      rw [← he] at hS
      simpa only [Finset.mul_sum, mul_ite, mul_zero] using hS)
  simpa only [hR, ← Finset.mul_sum] using h

/-- The strict fourth-moment loss obtained from the avoiding-subspace average. -/
theorem odd_fourth_loss {n r : ℕ} (hn : 5 ≤ n) (hr : r < n)
    (F : VectorialFunction n) (hF : IsAPN F) (v p : ℤ)
    (hN : 32 ≤ spaceSize n) (hv : 32 ≤ v) (hpv : 3 * v ≤ p)
    (hclose : |(p : ℝ) - Real.sqrt (spaceSize n : ℝ)| < 1)
    (hR : (spaceSize r : ℤ) = 2 * v) (hdiv : 2 * v ∣ (spaceSize n : ℤ))
    (hp : 2 * v ∣ p - v) :
    (linearity F : ℝ) ^ 4 < (spaceSize n : ℝ) ^ 4 - (v : ℝ) * (spaceSize n : ℝ) ^ 3 := by
  obtain ⟨b₀, hb₀, hfourth⟩ := attaining_fourth_bound (by omega) F hF
  have havg := averaged_excess_strict hn hr F b₀ hb₀ v p hN hv hpv hclose hR hdiv hp
  let E : ℤ := ∑ b ∈ (Finset.univ.erase 0).erase b₀, excess F b
  have hE := averaged_loss (spaceSize n) v E
    (by exact_mod_cast hN) (by exact_mod_cast hv) (by exact_mod_cast havg)
  have hfourthR : (linearity F : ℝ) ^ 4 ≤ (spaceSize n : ℝ) ^ 4 - (E : ℝ) := by
    exact_mod_cast hfourth
  linarith only [hE, hfourthR]

theorem odd_linearity_strict {n p s : ℕ} (hn : 5 ≤ n) (ho : Odd n)
    (F : VectorialFunction n) (hF : IsAPN F)
    (hp : p = ⌊Real.sqrt (spaceSize n : ℝ)⌋₊ ∨ p = ⌈Real.sqrt (spaceSize n : ℝ)⌉₊)
    (hd : 2 ^ s ∣ p) (hnd : ¬ 2 ^ (s + 1) ∣ p) (hs : 5 ≤ s) :
    (linearity F : ℝ) < (spaceSize n : ℝ) - (2 : ℝ) ^ (s - 2) := by
  obtain ⟨hclose, hcong, hpv, hr, hvN, hv⟩ := odd_nearest_parameters hn ho hp hd hnd hs
  let v : ℤ := 2 ^ s
  have hN : 32 ≤ spaceSize n := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    norm_num at h
    exact h
  have hR : (spaceSize (s + 1) : ℤ) = 2 * v := by
    simp [spaceSize, v, pow_succ, mul_comm]
  have hdiv : 2 * v ∣ (spaceSize n : ℤ) := by
    rw [← hR]
    exact_mod_cast (pow_dvd_pow (2 : ℕ) hr.le)
  have hfourth := odd_fourth_loss hn hr F hF v p hN
    (by dsimp [v]; exact_mod_cast hv) (by dsimp [v]; exact_mod_cast hpv)
    (by exact_mod_cast hclose) hR hdiv hcong
  have hvR : (0 : ℝ) < v := by dsimp [v]; positivity
  have hvNR : (v : ℝ) ≤ (spaceSize n : ℝ) := by
    have h : (4 : ℝ) * (v : ℝ) ≤ spaceSize n := by
      dsimp [v]
      exact_mod_cast hvN
    linarith
  have hstrict := linearity_of_fourth_loss (spaceSize n) v (linearity F)
    (by exact_mod_cast spaceSize_pos n) hvR hvNR (linearity_nonneg F) hfourth
  have hquarter : (v : ℝ) / 4 = (2 : ℝ) ^ (s - 2) := by
    have hpow : (2 : ℝ) ^ s = (2 : ℝ) ^ (s - 2) * 4 := by
      calc
        _ = (2 : ℝ) ^ (s - 2 + 2) := by congr 1; omega
        _ = _ := by rw [pow_add]; norm_num
    dsimp [v]
    push_cast
    rw [hpow]
    ring
  rwa [hquarter] at hstrict

/-- The odd-dimensional linearity proposition, including the final even-integer rounding. -/
theorem odd_dimension_linearity_bound : ∀ (n : ℕ), 5 ≤ n → Odd n → ∀ (F : VectorialFunction n), IsAPN F →
    ∀ (p s : ℕ),
      (p = ⌊Real.sqrt (spaceSize n : ℝ)⌋₊ ∨ p = ⌈Real.sqrt (spaceSize n : ℝ)⌉₊) →
      2 ^ s ∣ p → ¬ 2 ^ (s + 1) ∣ p → 5 ≤ s →
      (linearity F : ℝ) ≤ (spaceSize n : ℝ) - (2 : ℝ) ^ (s - 2) - 2 := by
  intro n hn ho F hF p s hp hd hnd hs
  have hstrict := odd_linearity_strict hn ho F hF hp hd hnd hs
  have hlin : 2 * (nonlinearity F : ℝ) + linearity F = spaceSize n := by
    exact_mod_cast linearity_distance n (by omega) F
  have hpower : (2 : ℝ) ^ (s - 2) = 2 * ((2 ^ (s - 3) : ℕ) : ℝ) := by
    push_cast
    rw [show s - 2 = (s - 3) + 1 by omega, pow_succ]
    ring
  rw [hpower] at hstrict ⊢
  have ht : ((2 ^ (s - 3) : ℕ) : ℝ) < nonlinearity F := by linarith
  have htn : 2 ^ (s - 3) + 1 ≤ nonlinearity F := by
    have : 2 ^ (s - 3) < nonlinearity F := by exact_mod_cast ht
    omega
  have htR : ((2 ^ (s - 3) : ℕ) : ℝ) + 1 ≤ nonlinearity F := by exact_mod_cast htn
  linarith


end
end APNLinearity.OddDimension
