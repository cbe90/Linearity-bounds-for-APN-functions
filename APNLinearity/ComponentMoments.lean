module

public import APNLinearity.Isolation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.Counts
noncomputable section
open _root_.APNLinearity.Fourier

theorem cauchy_sum {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    (∑ i ∈ s, u i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, u i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) u
  simpa using h

theorem parseval_real {n : ℕ} (f : BooleanFunction n) :
    (∑ a, (walsh f a : ℝ) ^ 2) = (spaceSize n : ℝ) ^ 2 := by
  exact_mod_cast walsh_parseval n f

theorem fourth_real {n : ℕ} (f : BooleanFunction n) :
    (fourthMoment f : ℝ) = ∑ a, (walsh f a : ℝ) ^ 4 := by
  simp [fourthMoment]

theorem fourth_eq_kappa {n : ℕ} (f : BooleanFunction n) :
    (∑ a, (walsh f a : ℝ) ^ 4) = kappa f * (spaceSize n : ℝ) ^ 3 := by
  have hN : (spaceSize n : ℝ) ≠ 0 := by exact_mod_cast (spaceSize_pos n).ne'
  rw [kappa, div_mul_cancel₀ _ (pow_ne_zero _ hN), fourth_real]

theorem kappa_lower_bound : ∀ (n : ℕ) (f : BooleanFunction n), 1 ≤ kappa f := by
  intro n f
  have hN : (0 : ℝ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  have h := cauchy_sum Finset.univ (fun a => (walsh f a : ℝ) ^ 2)
  simp only [Finset.card_univ, card_binary, ← pow_mul] at h
  norm_num only [Nat.reduceMul] at h
  rw [parseval_real, fourth_eq_kappa] at h
  have hp : 0 < (spaceSize n : ℝ) ^ 4 := pow_pos hN 4
  have hh : (spaceSize n : ℝ) ^ 4 ≤ kappa f * (spaceSize n : ℝ) ^ 4 := by nlinarith [h]
  nlinarith

/-- The equality condition in Cauchy–Schwarz, after Parseval. -/
theorem square_deviations {n : ℕ} (f : BooleanFunction n) :
    (∑ a, ((walsh f a : ℝ) ^ 2 - spaceSize n) ^ 2) =
      (∑ a, (walsh f a : ℝ) ^ 4) - (spaceSize n : ℝ) ^ 3 := by
  calc
    _ = ∑ a, ((walsh f a : ℝ) ^ 4 - 2 * spaceSize n * (walsh f a : ℝ) ^ 2 +
        (spaceSize n : ℝ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, card_binary, nsmul_eq_mul, parseval_real]
      ring

theorem kappa_equality : ∀ (n : ℕ) (f : BooleanFunction n), kappa f = 1 ↔ IsBent f := by
  intro n f
  classical
  have hN : (0 : ℝ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  have hd := square_deviations f
  rw [fourth_eq_kappa] at hd
  constructor
  · intro hk a
    rw [hk] at hd
    have hz : (∑ a, ((walsh f a : ℝ) ^ 2 - spaceSize n) ^ 2) = 0 := by linarith
    have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg _)).1 hz a (Finset.mem_univ a)
    have he : (walsh f a : ℝ) ^ 2 = spaceSize n := by nlinarith
    exact_mod_cast he
  · intro hb
    have hh (a : BinarySpace n) : (walsh f a : ℝ) ^ 2 = spaceSize n := by exact_mod_cast hb a
    simp only [hh, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero] at hd
    have hp := pow_pos hN 3
    nlinarith

end
end APNLinearity.Counts

open scoped BigOperators

namespace APNLinearity.Counts
noncomputable section
open _root_.APNLinearity.Fourier Components

theorem plateaued_abs {n : ℕ} {f : BooleanFunction n} {amp : ℤ}
    (h : HasPlateauedMagnitude f amp) (a : BinarySpace n) : |walsh f a| ≤ amp := by
  rcases h.2 a with he | he | he <;> simp [he, abs_of_pos h.1, h.1.le]

theorem plateaued_abs_of_ne {n : ℕ} {f : BooleanFunction n} {amp : ℤ}
    (h : HasPlateauedMagnitude f amp) {a : BinarySpace n} (ha : walsh f a ≠ 0) : |walsh f a| = amp := by
  rcases h.2 a with he | he | he
  · exact False.elim (ha he)
  · simp [he, abs_of_pos h.1]
  · simp [he, abs_of_pos h.1]

theorem plateaued_kappa : ∀ (n : ℕ) (f : BooleanFunction n) (amplitude : ℤ), HasPlateauedMagnitude f amplitude →
    kappa f = (amplitude : ℝ) ^ 2 / (spaceSize n : ℝ) := by
  intro n f amp h
  have hN : (spaceSize n : ℝ) ≠ 0 := by exact_mod_cast (spaceSize_pos n).ne'
  have he (a : BinarySpace n) : walsh f a ^ 4 = amp ^ 2 * walsh f a ^ 2 := by
    rcases h.2 a with he | he | he <;> rw [he] <;> ring
  have hM : fourthMoment f = amp ^ 2 * (spaceSize n : ℤ) ^ 2 := by
    simp only [fourthMoment, he, ← Finset.mul_sum]
    rw [walsh_parseval n f]
  unfold kappa
  rw [hM]
  push_cast
  field_simp

theorem plateaued_square_lower {n : ℕ} {f : BooleanFunction n} {amp : ℤ}
    (h : HasPlateauedMagnitude f amp) : (spaceSize n : ℤ) ≤ amp ^ 2 := by
  have hh := kappa_lower_bound n f
  rw [plateaued_kappa n f amp h] at hh
  have hN : (0 : ℝ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  have he := (le_div_iff₀ hN).1 hh
  exact_mod_cast (by simpa using he : (spaceSize n : ℝ) ≤ (amp : ℝ) ^ 2)

theorem plateaued_bent_iff {n : ℕ} {f : BooleanFunction n} {amp : ℤ}
    (h : HasPlateauedMagnitude f amp) : IsBent f ↔ amp ^ 2 = (spaceSize n : ℤ) := by
  rw [← kappa_equality n f, plateaued_kappa n f amp h]
  have hN : (spaceSize n : ℝ) ≠ 0 := by exact_mod_cast (spaceSize_pos n).ne'
  rw [div_eq_one_iff_eq hN]
  exact_mod_cast Iff.rfl

theorem plateaued_square_gaps {n : ℕ} {f : BooleanFunction n} {amp : ℤ}
    (h : HasPlateauedMagnitude f amp) :
    (Odd n → 2 * (spaceSize n : ℤ) ≤ amp ^ 2) ∧
    (Even n → ¬ IsBent f → 4 * (spaceSize n : ℤ) ≤ amp ^ 2) := by
  obtain ⟨r, hr⟩ := plateaued_magnitude_power n f amp h
  have hp : amp ^ 2 = (2 : ℤ) ^ (2 * r) := by rw [hr, ← pow_mul]; congr 1; omega
  have hlo := plateaued_square_lower h
  rw [hp] at hlo
  have hn : n ≤ 2 * r := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 hlo
  constructor
  · rintro ⟨s, hs⟩
    have he : n + 1 ≤ 2 * r := by omega
    have hh := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).2 he
    simpa [hp, spaceSize, pow_succ, mul_comm] using hh
  · intro he hb
    have hne : n ≠ 2 * r := by
      intro hn'
      apply hb
      apply (plateaued_bent_iff h).2
      simp [hp, spaceSize, hn']
    obtain ⟨s, hs⟩ := he
    have he : n + 2 ≤ 2 * r := by omega
    have hh := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).2 he
    simpa [hp, spaceSize, pow_add, mul_comm] using hh

theorem plateaued_kappa_gaps : ∀ (n : ℕ) (f : BooleanFunction n), IsPlateaued f →
    (Odd n → 2 ≤ kappa f) ∧ (Even n → ¬ IsBent f → 4 ≤ kappa f) := by
  intro n f hf
  obtain ⟨amp, hamp⟩ := (integer_plateaued_magnitude _ _).2 hf
  have hN : (0 : ℝ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  rw [plateaued_kappa n f amp hamp]
  constructor
  · intro hn
    apply (le_div_iff₀ hN).2
    exact_mod_cast (plateaued_square_gaps hamp).1 hn
  · intro hn hb
    apply (le_div_iff₀ hN).2
    exact_mod_cast (plateaued_square_gaps hamp).2 hn hb

theorem apn_plateaued_kappa_upper : ∀ (n : ℕ), 4 ≤ n → ∀ (F : VectorialFunction n), IsAPN F →
    ∀ b, b ≠ 0 → IsPlateaued (component F b) →
      kappa (component F b) ≤ (spaceSize n : ℝ) / 4 := by
  intro n hn F hF b hb hf
  obtain ⟨amp, hamp⟩ := (integer_plateaued_magnitude _ _).2 hf
  obtain ⟨a, ha⟩ := exists_walsh_ne_zero (component F b)
  have h := plateaued_nonaffine_bound n (component F b) ((integer_plateaued_magnitude _ _).1 ⟨amp, hamp⟩)
    (no_affine_component n (by omega) F hF b hb) a
  have he : |(walsh (component F b) a : ℝ)| = (amp : ℝ) := by
    exact_mod_cast plateaued_abs_of_ne hamp ha
  rw [he] at h
  rw [plateaued_kappa n (component F b) amp hamp]
  have hN : (0 : ℝ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  apply (div_le_iff₀ hN).2
  have hampR : (0 : ℝ) < amp := by exact_mod_cast hamp.1
  nlinarith

end
end APNLinearity.Counts

open scoped BigOperators

namespace APNLinearity.Counts
noncomputable section

def nonplateauedIndices {n : ℕ} (F : VectorialFunction n) : Finset (BinarySpace n) := by
  classical
  exact Finset.univ.filter (fun b => b ≠ 0 ∧ ¬ IsPlateaued (component F b))

def plateauedIndices {n : ℕ} (F : VectorialFunction n) : Finset (BinarySpace n) := by
  classical
  exact Finset.univ.filter (fun b => b ≠ 0 ∧ IsPlateaued (component F b))

@[simp] theorem mem_nonplateauedIndices {n : ℕ} (F : VectorialFunction n) (b : BinarySpace n) :
    b ∈ nonplateauedIndices F ↔ b ≠ 0 ∧ ¬ IsPlateaued (component F b) := by
  classical
  simp [nonplateauedIndices]

@[simp] theorem mem_plateauedIndices {n : ℕ} (F : VectorialFunction n) (b : BinarySpace n) :
    b ∈ plateauedIndices F ↔ b ≠ 0 ∧ IsPlateaued (component F b) := by
  classical
  simp [plateauedIndices]

theorem nonplateaued_card {n : ℕ} (F : VectorialFunction n) :
    (nonplateauedIndices F).card = nonplateauedComponentCount F := by
  rw [nonplateauedComponentCount_eq_card]
  rfl

theorem component_partition {n : ℕ} (F : VectorialFunction n) :
    Disjoint (nonplateauedIndices F) (plateauedIndices F) ∧
      nonplateauedIndices F ∪ plateauedIndices F = Finset.univ.erase 0 := by
  classical
  constructor
  · apply Finset.disjoint_left.mpr
    intro b hb ht
    exact ((mem_nonplateauedIndices F b).1 hb).2 ((mem_plateauedIndices F b).1 ht).2
  · ext b
    simp only [Finset.mem_union, mem_nonplateauedIndices, mem_plateauedIndices,
      Finset.mem_erase, Finset.mem_univ, and_true]
    tauto

theorem component_sum_partition {n : ℕ} (F : VectorialFunction n) (u : BinarySpace n → ℝ) :
    (∑ b ∈ nonplateauedIndices F, u b) + (∑ b ∈ plateauedIndices F, u b) =
      ∑ b ∈ Finset.univ.erase 0, u b := by
  classical
  rw [← Finset.sum_union (component_partition F).1, (component_partition F).2]

theorem component_card_partition {n : ℕ} (F : VectorialFunction n) :
    (nonplateauedComponentCount F : ℝ) + ((plateauedIndices F).card : ℝ) = (spaceSize n : ℝ) - 1 := by
  classical
  have h := Finset.card_union_of_disjoint (component_partition F).1
  rw [(component_partition F).2] at h
  have he := Finset.card_erase_add_one (Finset.mem_univ (0 : BinarySpace n))
  rw [h, Finset.card_univ, card_binary, nonplateaued_card] at he
  have hh : (nonplateauedComponentCount F : ℝ) + ((plateauedIndices F).card : ℝ) + 1 = spaceSize n := by
    exact_mod_cast he
  linarith

theorem kappa_total : ∀ (n : ℕ) (F : VectorialFunction n), IsAPN F →
    (∑ b ∈ (Finset.univ.erase 0), kappa (component F b)) = 2 * ((spaceSize n : ℝ) - 1) := by
  intro n F hF
  classical
  have hN : (spaceSize n : ℝ) ≠ 0 := by exact_mod_cast (spaceSize_pos n).ne'
  simp only [kappa, ← Finset.sum_div, ← Int.cast_sum, Sidon.apn_fourth_moment n F hF]
  push_cast
  field_simp

attribute [local instance] Classical.propDecidable

theorem odd_excess_moment : ∀ (n : ℕ), 4 ≤ n → Odd n → ∀ (F : VectorialFunction n), IsAPN F →
    (∑ b ∈ (Finset.univ.filter (fun b => b ≠ 0 ∧ ¬ IsPlateaued (component F b))),
      (kappa (component F b) - 1)) +
    (∑ b ∈ (Finset.univ.filter (fun b => b ≠ 0 ∧ IsPlateaued (component F b))),
      (kappa (component F b) - 2)) = (nonplateauedComponentCount F : ℝ) := by
  intro n _hn _ho F hF
  classical
  change (∑ b ∈ nonplateauedIndices F, (kappa (component F b) - 1)) +
    (∑ b ∈ plateauedIndices F, (kappa (component F b) - 2)) = _
  have hs := component_sum_partition F (fun b => kappa (component F b))
  rw [kappa_total n F hF] at hs
  have hc := component_card_partition F
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, nonplateaued_card]
  linarith

theorem odd_excess_bounds {n : ℕ} (hn : 4 ≤ n) (ho : Odd n) (F : VectorialFunction n)
    (hF : IsAPN F) (b : BinarySpace n) (hb : b ≠ 0) :
    (¬ IsPlateaued (component F b) → kappa (component F b) - 1 ≤ nonplateauedComponentCount F) ∧
    (IsPlateaued (component F b) → kappa (component F b) - 2 ≤ nonplateauedComponentCount F) := by
  classical
  have hQ (b) (_hb : b ∈ nonplateauedIndices F) : 0 ≤ kappa (component F b) - 1 :=
    sub_nonneg.mpr (kappa_lower_bound n (component F b))
  have hT (b) (hb : b ∈ plateauedIndices F) : 0 ≤ kappa (component F b) - 2 :=
    sub_nonneg.mpr ((plateaued_kappa_gaps n (component F b) ((mem_plateauedIndices F b).1 hb).2).1 ho)
  have hs := odd_excess_moment n hn ho F hF
  change (∑ b ∈ nonplateauedIndices F, (kappa (component F b) - 1)) +
    (∑ b ∈ plateauedIndices F, (kappa (component F b) - 2)) = _ at hs
  have hQsum := Finset.sum_nonneg hQ
  have hTsum := Finset.sum_nonneg hT
  constructor
  · intro h
    have hh := Finset.single_le_sum hQ ((mem_nonplateauedIndices F b).2 ⟨hb, h⟩)
    linarith
  · intro h
    have hh := Finset.single_le_sum hT ((mem_plateauedIndices F b).2 ⟨hb, h⟩)
    linarith

end
end APNLinearity.Counts

open scoped BigOperators

namespace APNLinearity.Counts
noncomputable section
open _root_.APNLinearity.Fourier

/-- Cauchy–Schwarz on the Parseval mass outside the chosen coefficient. -/
theorem isolated_coefficient {n : ℕ} (f : BooleanFunction n) (a₀ : BinarySpace n) :
    ((walsh f a₀ : ℝ) ^ 2 - spaceSize n) ^ 2 ≤
      (spaceSize n : ℝ) ^ 2 * ((spaceSize n : ℝ) - 1) * (kappa f - 1) := by
  classical
  have hN : (0 : ℝ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  have h := cauchy_sum (Finset.univ.erase a₀) (fun a => (walsh f a : ℝ) ^ 2)
  have hcard : ((Finset.univ.erase a₀).card : ℝ) = (spaceSize n : ℝ) - 1 := by
    have he := Finset.card_erase_add_one (Finset.mem_univ a₀)
    rw [Finset.card_univ, card_binary] at he
    have heR : ((Finset.univ.erase a₀).card : ℝ) + 1 = spaceSize n := by exact_mod_cast he
    linarith
  have hs := Finset.sum_erase_add Finset.univ (fun a => (walsh f a : ℝ) ^ 2) (Finset.mem_univ a₀)
  have ht := Finset.sum_erase_add Finset.univ (fun a => (walsh f a : ℝ) ^ 4) (Finset.mem_univ a₀)
  rw [parseval_real] at hs
  rw [fourth_eq_kappa] at ht
  simp only [hcard, ← pow_mul] at h
  norm_num only [Nat.reduceMul] at h
  have hs' : (∑ a ∈ Finset.univ.erase a₀, (walsh f a : ℝ) ^ 2) =
      (spaceSize n : ℝ) ^ 2 - (walsh f a₀ : ℝ) ^ 2 := by linarith
  have ht' : (∑ a ∈ Finset.univ.erase a₀, (walsh f a : ℝ) ^ 4) =
      kappa f * (spaceSize n : ℝ) ^ 3 - (walsh f a₀ : ℝ) ^ 4 := by linarith
  rw [hs', ht'] at h
  have hh : (spaceSize n : ℝ) * ((walsh f a₀ : ℝ) ^ 2 - spaceSize n) ^ 2 ≤
      (spaceSize n : ℝ) * ((spaceSize n : ℝ) ^ 2 * ((spaceSize n : ℝ) - 1) * (kappa f - 1)) := by
    nlinarith [h]
  exact (mul_le_mul_iff_right₀ hN).mp hh

theorem square_root_bound (N q w : ℝ) (hN : 0 ≤ N) (hq : 0 ≤ q * (N - 1))
    (h : (w ^ 2 - N) ^ 2 ≤ N ^ 2 * q * (N - 1)) :
    w ^ 2 ≤ N * (1 + Real.sqrt (q * (N - 1))) := by
  have hs := Real.sq_sqrt hq
  have he : (N * Real.sqrt (q * (N - 1))) ^ 2 = N ^ 2 * q * (N - 1) := by
    rw [mul_pow, hs]
    ring
  have hh := le_of_sq_le_sq (h.trans_eq he.symm) (mul_nonneg hN (Real.sqrt_nonneg _))
  linarith

theorem odd_component_bound {n : ℕ} (hn : 4 ≤ n) (ho : Odd n) (F : VectorialFunction n)
    (hF : IsAPN F) (hq : 0 < nonplateauedComponentCount F) (b : BinarySpace n) (hb : b ≠ 0) (a : BinarySpace n) :
    (walsh (component F b) a : ℝ) ^ 2 ≤ (spaceSize n : ℝ) *
      (1 + Real.sqrt ((nonplateauedComponentCount F : ℝ) * ((spaceSize n : ℝ) - 1))) := by
  have hN : (0 : ℝ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  have hN4 : (4 : ℝ) ≤ spaceSize n := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    exact_mod_cast hh
  have hq1 : (1 : ℝ) ≤ nonplateauedComponentCount F := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ nonplateauedComponentCount F := by positivity
  have hrad : (0 : ℝ) ≤ (nonplateauedComponentCount F : ℝ) * ((spaceSize n : ℝ) - 1) :=
    mul_nonneg hq0 (by linarith)
  have he := odd_excess_bounds hn ho F hF b hb
  by_cases hp : IsPlateaued (component F b)
  · have hk2 := (plateaued_kappa_gaps n (component F b) hp).1 ho
    have hkN := apn_plateaued_kappa_upper n hn F hF b hb hp
    have hkq := he.2 hp
    have hprod := mul_le_mul hkN hkq (by linarith : 0 ≤ kappa (component F b) - 2)
      (by positivity : (0 : ℝ) ≤ (spaceSize n : ℝ) / 4)
    have hNq := mul_le_mul_of_nonneg_right hN4 hq0
    have hksq : (kappa (component F b) - 1) ^ 2 ≤
        (nonplateauedComponentCount F : ℝ) * ((spaceSize n : ℝ) - 1) := by nlinarith
    obtain ⟨amp, hamp⟩ := (integer_plateaued_magnitude _ _).2 hp
    have hkap := plateaued_kappa n (component F b) amp hamp
    have hampN : (amp : ℝ) ^ 2 = (spaceSize n : ℝ) * kappa (component F b) := by
      have hh := (eq_div_iff hN.ne').1 hkap
      linarith
    rcases hamp.2 a with hw | hw | hw
    · rw [hw]
      simp only [Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      positivity
    all_goals
      have hwN : (walsh (component F b) a : ℝ) ^ 2 =
          (spaceSize n : ℝ) * kappa (component F b) := by
        rw [hw]
        simpa using hampN
      apply square_root_bound _ _ _ hN.le hrad
      have hh := mul_le_mul_of_nonneg_left hksq (sq_nonneg (spaceSize n : ℝ))
      rw [hwN]
      nlinarith [hh]
  · apply square_root_bound _ _ _ hN.le hrad
    have hh := isolated_coefficient (component F b) a
    have ht := mul_le_mul_of_nonneg_left (he.1 hp)
      (mul_nonneg (sq_nonneg (spaceSize n : ℝ)) (by linarith : 0 ≤ (spaceSize n : ℝ) - 1))
    nlinarith [hh, ht]

theorem odd_count_bound (n : ℕ) (hn : 4 ≤ n) (ho : Odd n)
    (F : VectorialFunction n) (hF : IsAPN F) (hq : 0 < nonplateauedComponentCount F) :
    linearity F ^ 2 ≤ (spaceSize n : ℝ) *
      (1 + Real.sqrt ((nonplateauedComponentCount F : ℝ) * ((spaceSize n : ℝ) - 1))) := by
  obtain ⟨a, b, hb, he⟩ := linearity_attained (by omega : 1 ≤ n) F
  rw [he, natAbs_cast_real, sq_abs]
  exact odd_component_bound hn ho F hF hq b hb a

end
end APNLinearity.Counts
