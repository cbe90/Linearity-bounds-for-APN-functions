module

public import APNLinearity.ComponentMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.Counts
noncomputable section
open _root_.APNLinearity.Fourier

def errorSupport {n : ℕ} (F : VectorialFunction n) (b₀ a₀ : BinarySpace n) (c : Bit) : Finset (BinarySpace n) := by
  classical
  exact Finset.univ.filter (fun x => component F b₀ x + affineBoolean a₀ c x = 1)

@[simp] theorem mem_errorSupport {n : ℕ} (F : VectorialFunction n) (b₀ a₀ : BinarySpace n) (c : Bit) (x : BinarySpace n) :
    x ∈ errorSupport F b₀ a₀ c ↔ component F b₀ x + affineBoolean a₀ c x = 1 := by
  classical
  simp [errorSupport]

theorem errorSupport_card {n : ℕ} (F : VectorialFunction n) (b₀ a₀ : BinarySpace n) (c : Bit) :
    (errorSupport F b₀ a₀ c).card = hammingDistance (component F b₀) (affineBoolean a₀ c) := by
  rw [distance_eq_weight]
  rfl

theorem component_add {n : ℕ} (F : VectorialFunction n) (b d : BinarySpace n) :
    component F (b + d) = component F b + component F d := by
  funext x
  simp [component]

theorem plateaued_affine {n : ℕ} (f : BooleanFunction n) (amp : ℤ) (h : HasPlateauedMagnitude f amp)
    (a₀ : BinarySpace n) (c : Bit) : HasPlateauedMagnitude (f + affineBoolean a₀ c) amp := by
  refine ⟨h.1, ?_⟩
  intro a
  rw [walsh_affine_shift n f a a₀ c]
  rcases sign_cases c with hc | hc <;> rcases h.2 (a + a₀) with he | he | he <;>
    simp [hc, he]

theorem walsh_pairing {n : ℕ} (f h : BooleanFunction n) :
    (∑ a, walsh f a * walsh h a) = (spaceSize n : ℤ) * ∑ x, bitSign (f x + h x) := by
  rw [walsh_eq_transform f, walsh_eq_transform h, transform_pairing]
  simp only [transform_twice, sign_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem walsh_error_pairing {n : ℕ} (F : VectorialFunction n) (b b₀ a₀ : BinarySpace n) (c : Bit) :
    (∑ a, walsh (component F b) a *
      walsh (component F b + (component F b₀ + affineBoolean a₀ c)) a) =
      (spaceSize n : ℤ) * ((spaceSize n : ℤ) - 2 * (errorSupport F b₀ a₀ c).card) := by
  rw [walsh_pairing]
  have he (x) : component F b x + (component F b + (component F b₀ + affineBoolean a₀ c)) x =
      (component F b₀ + affineBoolean a₀ c) x := by
    simp only [Pi.add_apply, ← add_assoc, bit_add_self, zero_add]
  simp only [he]
  rw [sign_sum_weight]
  rfl

theorem twice_restricted {n : ℕ} (F : VectorialFunction n) (b b₀ a₀ a : BinarySpace n) (c : Bit) :
    2 * restrictedWalsh F (errorSupport F b₀ a₀ c) b a =
      walsh (component F b) a - walsh (component F b + (component F b₀ + affineBoolean a₀ c)) a := by
  classical
  let E := errorSupport F b₀ a₀ c
  have he (x : BinarySpace n) :
      bitSign (component F b x + binaryDot a x) -
        bitSign ((component F b + (component F b₀ + affineBoolean a₀ c)) x + binaryDot a x) =
        if x ∈ E then 2 * bitSign (component F b x + binaryDot a x) else 0 := by
    have hs := sign_eq_one_sub_twice (component F b₀ x + affineBoolean a₀ c x)
    simp only [Pi.add_apply, sign_add] at hs ⊢
    by_cases hx : x ∈ E
    · have hg := (mem_errorSupport F b₀ a₀ c x).1 hx
      rw [ite_eq_left hx]
      simp [hg] at hs
      rw [hs]
      ring
    · have hg : component F b₀ x + affineBoolean a₀ c x ≠ 1 :=
        fun hh => hx ((mem_errorSupport F b₀ a₀ c x).2 hh)
      rw [ite_eq_right hx]
      simp [hg] at hs
      rw [hs]
      ring
  symm
  calc
    _ = ∑ x, (bitSign (component F b x + binaryDot a x) -
        bitSign ((component F b + (component F b₀ + affineBoolean a₀ c)) x + binaryDot a x)) := by
      rw [Finset.sum_sub_distrib]
      rfl
    _ = ∑ x ∈ E, 2 * bitSign (component F b x + binaryDot a x) := by simp_rw [he]; simp
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem restricted_pair_shift {n : ℕ} (F : VectorialFunction n) (b b₀ a₀ a : BinarySpace n) (c : Bit) :
    restrictedWalsh F (errorSupport F b₀ a₀ c) (b + b₀) a =
      -bitSign c * restrictedWalsh F (errorSupport F b₀ a₀ c) b (a + a₀) := by
  classical
  unfold restrictedWalsh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hg := (mem_errorSupport F b₀ a₀ c x).1 hx
  have hf : component F b₀ x = affineBoolean a₀ c x + 1 := by
    have hh := congrArg (fun z : Bit => z + affineBoolean a₀ c x) hg
    rw [add_assoc, bit_add_self, add_zero] at hh
    exact hh.trans (add_comm _ _)
  rw [component_add, Pi.add_apply, hf]
  simp only [affineBoolean, dot_add_left, sign_add, sign_one]
  ring

theorem restricted_fourth_pair {n : ℕ} (F : VectorialFunction n) (b b₀ a₀ : BinarySpace n) (c : Bit) :
    restrictedFourth F (errorSupport F b₀ a₀ c) (b + b₀) =
      restrictedFourth F (errorSupport F b₀ a₀ c) b := by
  unfold restrictedFourth
  simp_rw [restricted_pair_shift]
  have hs : (-bitSign c) ^ 4 = 1 := by rcases sign_cases c with h | h <;> simp [h]
  simp only [mul_pow, hs, one_mul]
  exact sum_translate (fun a => restrictedWalsh F (errorSupport F b₀ a₀ c) b a ^ 4) a₀

end
end APNLinearity.Counts

open scoped BigOperators

namespace APNLinearity.Counts
noncomputable section
attribute [local instance 10] Classical.propDecidable
open SmallSupport

def outputPair {n : ℕ} (b₀ b : BinarySpace n) : Finset (BinarySpace n) := {b, b + b₀}

def GoodPair {n : ℕ} (F : VectorialFunction n) (P : Finset (BinarySpace n)) : Prop :=
  ∀ b ∈ P, b ≠ 0 ∧ IsPlateaued (component F b)

theorem plateauedPairCount_eq_card {n : ℕ} (F : VectorialFunction n) (b₀ : BinarySpace n) :
    plateauedPairCount F b₀ = ((outputPairs b₀).filter (GoodPair F)).card := by
  unfold plateauedPairCount
  apply congrArg Finset.card
  ext Q
  simp only [Finset.mem_filter, GoodPair]



@[simp] theorem mem_outputPair {n : ℕ} (b₀ b d : BinarySpace n) :
    d ∈ outputPair b₀ b ↔ d = b ∨ d = b + b₀ := by simp [outputPair]

@[simp] theorem outputPair_add {n : ℕ} (b₀ b : BinarySpace n) :
    outputPair b₀ (b + b₀) = outputPair b₀ b := by
  ext d
  simp [or_comm]

theorem goodPair_iff {n : ℕ} (F : VectorialFunction n) (b₀ b : BinarySpace n) :
    GoodPair F (outputPair b₀ b) ↔
      (b ≠ 0 ∧ IsPlateaued (component F b)) ∧
      (b + b₀ ≠ 0 ∧ IsPlateaued (component F (b + b₀))) := by
  simp [GoodPair, outputPair]

theorem outputPair_eq_of_mem {n : ℕ} {b₀ b d : BinarySpace n} (hd : d ∈ outputPair b₀ b) :
    outputPair b₀ d = outputPair b₀ b := by
  rcases (mem_outputPair b₀ b d).1 hd with rfl | rfl
  · rfl
  · exact outputPair_add _ _

theorem outputPair_injOn {n : ℕ} {b₀ : BinarySpace n} (P : PairRepresentatives b₀) :
    Set.InjOn (outputPair b₀) P.points := by
  intro b hb d hd he
  have hm : b ∈ outputPair b₀ d := by rw [← he]; simp
  rcases (mem_outputPair b₀ d b).1 hm with he | he
  · exact he
  · exact False.elim ((P.mem_add d).1 (he ▸ hb) hd)

theorem outputPairs_image {n : ℕ} {b₀ : BinarySpace n} (P : PairRepresentatives b₀) :
    P.points.image (outputPair b₀) = outputPairs b₀ := by
  classical
  ext Q
  constructor
  · intro h
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  · intro h
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
    by_cases hb : b ∈ P.points
    · exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    · exact Finset.mem_image.mpr ⟨b + b₀, (P.mem_add b).2 hb, outputPair_add _ _⟩

theorem outputPairs_card {n : ℕ} {b₀ : BinarySpace n} (P : PairRepresentatives b₀) :
    (outputPairs b₀).card = P.points.card := by
  classical
  rw [← outputPairs_image P, Finset.card_image_of_injOn (outputPair_injOn P)]

theorem good_representatives_card {n : ℕ} (F : VectorialFunction n) {b₀ : BinarySpace n}
    (P : PairRepresentatives b₀) :
    (P.points.filter (fun b => GoodPair F (outputPair b₀ b))).card = plateauedPairCount F b₀ := by
  classical
  rw [plateauedPairCount_eq_card]
  rw [← outputPairs_image P, Finset.filter_image, Finset.card_image_of_injOn]
  intro b hb d hd he
  exact outputPair_injOn P (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hd).1 he

theorem exists_zero_representatives {n : ℕ} (b₀ : BinarySpace n) (hb₀ : b₀ ≠ 0) :
    ∃ P : PairRepresentatives b₀, 0 ∈ P.points := by
  classical
  obtain ⟨a, ha⟩ := exists_dot_one hb₀
  let P : PairRepresentatives b₀ := {
    points := Finset.univ.filter (fun x => binaryDot a x = 0)
    mem_add := by
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, dot_add_right, ha]
      rcases bit_eq_zero_or_one (binaryDot a x) with hx | hx <;> simp [hx] }
  exact ⟨P, by simp [P]⟩

theorem nonplateaued_in_bad_pair {n : ℕ} (F : VectorialFunction n) (b₀ b : BinarySpace n)
    (hb₀ : b₀ ≠ 0) (hbad₀ : ¬ IsPlateaued (component F b₀))
    (hbad : ¬ GoodPair F (outputPair b₀ b)) :
    ∃ d ∈ outputPair b₀ b, d ∈ nonplateauedIndices F := by
  classical
  by_cases hb : b = 0
  · subst b
    exact ⟨b₀, by simp, (mem_nonplateauedIndices F b₀).2 ⟨hb₀, hbad₀⟩⟩
  by_cases hd : b + b₀ = 0
  · have he : b = b₀ := (binary_add_eq_zero_iff b b₀).1 hd
    subst b
    exact ⟨b₀, by simp, (mem_nonplateauedIndices F b₀).2 ⟨hb₀, hbad₀⟩⟩
  by_cases hp : IsPlateaued (component F b)
  · have hn : ¬ IsPlateaued (component F (b + b₀)) := by
      intro hh
      exact hbad ((goodPair_iff F b₀ b).2 ⟨⟨hb, hp⟩, ⟨hd, hh⟩⟩)
    exact ⟨b + b₀, by simp, (mem_nonplateauedIndices F (b + b₀)).2 ⟨hd, hn⟩⟩
  · exact ⟨b, by simp, (mem_nonplateauedIndices F b).2 ⟨hb, hp⟩⟩

theorem plateaued_pair_count_bound : ∀ (n : ℕ), 1 ≤ n → ∀ (F : VectorialFunction n) (b₀ : BinarySpace n),
    b₀ ≠ 0 → ¬ IsPlateaued (component F b₀) →
      (spaceSize n : ℝ) / 2 - (nonplateauedComponentCount F : ℝ) ≤
        (plateauedPairCount F b₀ : ℝ) := by
  intro n _hn F b₀ hb₀ hbad₀
  classical
  obtain ⟨P⟩ := exists_pair_representatives b₀ hb₀
  have hsub : ((outputPairs b₀).filter (fun Q => ¬ GoodPair F Q)) ⊆
      (nonplateauedIndices F).image (outputPair b₀) := by
    intro Q hQ
    obtain ⟨hm, hn⟩ := Finset.mem_filter.mp hQ
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨d, hd, hdQ⟩ := nonplateaued_in_bad_pair F b₀ b hb₀ hbad₀ hn
    exact Finset.mem_image.mpr ⟨d, hdQ, outputPair_eq_of_mem hd⟩
  have hbad : ((outputPairs b₀).filter (fun Q => ¬ GoodPair F Q)).card ≤ (nonplateauedIndices F).card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [nonplateaued_card] at hbad
  have hcard := Finset.card_filter_add_card_filter_not (s := outputPairs b₀) (GoodPair F)
  rw [← plateauedPairCount_eq_card, outputPairs_card P] at hcard
  have hP := P.card_pairs
  have hnat : spaceSize n ≤ 2 * (plateauedPairCount F b₀ + nonplateauedComponentCount F) := by omega
  have hr : (spaceSize n : ℝ) ≤ 2 * ((plateauedPairCount F b₀ : ℝ) + nonplateauedComponentCount F) := by
    exact_mod_cast hnat
  linarith

end
end APNLinearity.Counts

open scoped BigOperators

namespace APNLinearity.Counts
noncomputable section
open _root_.APNLinearity.Fourier Components

theorem plateaued_amplitude_gap {n : ℕ} {f h : BooleanFunction n} {amp amp' : ℤ}
    (hf : HasPlateauedMagnitude f amp) (hh : HasPlateauedMagnitude h amp') (hlt : amp < amp') :
    2 * amp ≤ amp' := by
  obtain ⟨r, hr⟩ := plateaued_magnitude_power n f amp hf
  obtain ⟨s, hs⟩ := plateaued_magnitude_power n h amp' hh
  have hrs : r < s := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 (by simpa [hr, hs] using hlt)
  have hp := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).2 (show r + 1 ≤ s by omega)
  simpa [hr, hs, pow_succ, mul_comm] using hp

/-- Parseval bounds the inner product using the larger spectrum's support. -/
theorem plateaued_pairing_le {n : ℕ} {f h : BooleanFunction n} {amp amp' : ℤ}
    (hf : HasPlateauedMagnitude f amp) (hh : HasPlateauedMagnitude h amp') :
    amp' * (∑ a, walsh f a * walsh h a) ≤ amp * (spaceSize n : ℤ) ^ 2 := by
  have he (a : BinarySpace n) : amp' * (walsh f a * walsh h a) ≤ amp * walsh h a ^ 2 := by
    have hu := abs_le.mp (plateaued_abs hf a)
    rcases hh.2 a with hv | hv | hv
    · simp [hv]
    · rw [hv]
      have ht := mul_le_mul_of_nonneg_right hu.2 (sq_nonneg amp')
      nlinarith [ht]
    · rw [hv]
      have ht := mul_le_mul_of_nonneg_right (show -walsh f a ≤ amp by linarith) (sq_nonneg amp')
      nlinarith [ht]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => he a)
  simp only [← Finset.mul_sum] at hs
  rw [walsh_parseval n h] at hs
  exact hs

theorem close_plateaued_not_lt {n : ℕ} {f h : BooleanFunction n} {amp amp' : ℤ}
    (hf : HasPlateauedMagnitude f amp) (hh : HasPlateauedMagnitude h amp')
    (hc : (spaceSize n : ℤ) ^ 2 < 2 * ∑ a, walsh f a * walsh h a) : ¬ amp < amp' := by
  intro hlt
  have hgap := plateaued_amplitude_gap hf hh hlt
  have hpair := plateaued_pairing_le hf hh
  have hpos : 0 ≤ ∑ a, walsh f a * walsh h a := by nlinarith [sq_nonneg (spaceSize n : ℤ)]
  have hmul := mul_le_mul_of_nonneg_right hgap hpos
  have hstrict := mul_lt_mul_of_pos_left hc hf.1
  nlinarith [hmul, hstrict]

theorem close_plateaued_magnitudes {n : ℕ} {f h : BooleanFunction n} {amp amp' : ℤ}
    (hf : HasPlateauedMagnitude f amp) (hh : HasPlateauedMagnitude h amp')
    (hc : (spaceSize n : ℤ) ^ 2 < 2 * ∑ a, walsh f a * walsh h a) : amp = amp' := by
  have h₁ := close_plateaued_not_lt hf hh hc
  have hc' : (spaceSize n : ℤ) ^ 2 < 2 * ∑ a, walsh h a * walsh f a := by
    simpa only [mul_comm] using hc
  have h₂ := close_plateaued_not_lt hh hf hc'
  omega

/-- The bent case has no zero Walsh coefficients; otherwise the next square is at least 4N. -/
theorem paired_fourth_pointwise (N amp u v T : ℤ) (hN : 0 < N)
    (hu : u = 0 ∨ u = amp ∨ u = -amp) (hv : v = 0 ∨ v = amp ∨ v = -amp)
    (hT : 2 * T = u - v) (hgap : 4 * N ≤ amp ^ 2 ∨ (u ^ 2 = N ∧ v ^ 2 = N)) :
    N * T ^ 2 ≤ T ^ 4 := by
  have hs := congrArg (fun z : ℤ => z ^ 2) hT
  have ht : T = 0 ∨ N ≤ T ^ 2 := by
    rcases hgap with hg | ⟨huN, hvN⟩
    · rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first | left; omega | right; nlinarith
    · rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first | omega | left; omega | right; nlinarith
  rcases ht with rfl | ht
  · simp
  · have hh := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg T)
    nlinarith [hh]

end
end APNLinearity.Counts

open scoped BigOperators

namespace APNLinearity.Counts
noncomputable section

theorem plateaued_pair_fourth : ∀ (n : ℕ), 4 ≤ n → Even n → ∀ (F : VectorialFunction n), IsAPN F →
    ∀ (b₀ a₀ : BinarySpace n) (c : Bit), b₀ ≠ 0 →
      let E := Finset.univ.filter (fun x => component F b₀ x + affineBoolean a₀ c x = 1)
      0 < E.card → (E.card : ℝ) < (spaceSize n : ℝ) / 4 →
        ∀ b, b ≠ 0 → b + b₀ ≠ 0 → IsPlateaued (component F b) →
          IsPlateaued (component F (b + b₀)) →
          (spaceSize n : ℤ) ^ 2 * (E.card : ℤ) ≤ restrictedFourth F E b := by
  intro n _hn he F _hF b₀ a₀ c _hb₀
  dsimp only
  intro _hpos hsmall b _hb _hbb hpl hpl'
  change (spaceSize n : ℤ) ^ 2 * ((errorSupport F b₀ a₀ c).card : ℤ) ≤
    restrictedFourth F (errorSupport F b₀ a₀ c) b
  change ((errorSupport F b₀ a₀ c).card : ℝ) < (spaceSize n : ℝ) / 4 at hsmall
  obtain ⟨amp, hamp⟩ := (Fourier.integer_plateaued_magnitude _ _).2 hpl
  obtain ⟨amp', hamp'⟩ := (Fourier.integer_plateaued_magnitude _ _).2 hpl'
  let f := component F b
  let g := component F b₀ + affineBoolean a₀ c
  have hfun : f + g = component F (b + b₀) + affineBoolean a₀ c := by
    rw [component_add, add_assoc]
  have hh : HasPlateauedMagnitude (f + g) amp' := by
    rw [hfun]
    exact plateaued_affine _ _ hamp' a₀ c
  have hN : (0 : ℤ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  have ht : 4 * ((errorSupport F b₀ a₀ c).card : ℤ) < spaceSize n := by
    have htR : 4 * ((errorSupport F b₀ a₀ c).card : ℝ) < spaceSize n := by linarith
    exact_mod_cast htR
  have hc : (spaceSize n : ℤ) ^ 2 < 2 * ∑ a, walsh f a * walsh (f + g) a := by
    rw [walsh_error_pairing]
    nlinarith [mul_pos hN (sub_pos.mpr ht)]
  have hampEq := close_plateaued_magnitudes hamp hh hc
  subst amp'
  have hpoint (a : BinarySpace n) : (spaceSize n : ℤ) * restrictedWalsh F (errorSupport F b₀ a₀ c) b a ^ 2 ≤
      restrictedWalsh F (errorSupport F b₀ a₀ c) b a ^ 4 := by
    apply paired_fourth_pointwise _ amp (walsh f a) (walsh (f + g) a) _ hN (hamp.2 a) (hh.2 a)
      (twice_restricted F b b₀ a₀ a c)
    by_cases hbf : IsBent f
    · right
      have hbfg : IsBent (f + g) := (plateaued_bent_iff hh).2 ((plateaued_bent_iff hamp).1 hbf)
      exact ⟨hbf a, hbfg a⟩
    · exact Or.inl ((plateaued_square_gaps hamp).2 he hbf)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  rw [← Finset.mul_sum, restricted_parseval n F (errorSupport F b₀ a₀ c) b] at hs
  change (spaceSize n : ℤ) * ((spaceSize n : ℤ) * (errorSupport F b₀ a₀ c).card) ≤ _ at hs
  simpa only [restrictedFourth, pow_two, mul_assoc] using hs

end
end APNLinearity.Counts
