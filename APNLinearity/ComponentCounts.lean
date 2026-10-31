module

public import APNLinearity.PairedComponents

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.Counts
noncomputable section

/-- Sum one fourth moment per output pair, retaining the exceptional pair. -/
theorem even_pair_sum {n : ℕ} (hn : 4 ≤ n) (he : Even n) (F : VectorialFunction n) (hF : IsAPN F)
    (b₀ a₀ : BinarySpace n) (c : Bit) (hb₀ : b₀ ≠ 0)
    (hpos : 0 < (errorSupport F b₀ a₀ c).card)
    (hsmall : ((errorSupport F b₀ a₀ c).card : ℝ) < (spaceSize n : ℝ) / 4) :
    let N : ℝ := spaceSize n
    let t : ℝ := (errorSupport F b₀ a₀ c).card
    let p : ℝ := plateauedPairCount F b₀
    p * N ^ 2 * t + (N / 2 - p - 1) * N * t ^ 2 + t ^ 4 ≤ N ^ 2 / 2 * (3 * t ^ 2 - 2 * t) := by
  classical
  dsimp only
  let E := errorSupport F b₀ a₀ c
  let N : ℝ := spaceSize n
  let t : ℝ := E.card
  let p : ℝ := plateauedPairCount F b₀
  obtain ⟨P, hP0⟩ := exists_zero_representatives b₀ hb₀
  have hpoint (b : BinarySpace n) :
      N * t ^ 2 + (if GoodPair F (outputPair b₀ b) then N ^ 2 * t - N * t ^ 2 else 0) +
        (if b = 0 then t ^ 4 - N * t ^ 2 else 0) ≤ (restrictedFourth F E b : ℝ) := by
    by_cases hz : b = 0
    · subst b
      have hg : ¬ GoodPair F (outputPair b₀ 0) := by
        intro h
        exact ((goodPair_iff F b₀ 0).1 h).1.1 rfl
      rw [ite_eq_right hg, ite_eq_left rfl]
      have hh : t ^ 4 ≤ (restrictedFourth F E 0 : ℝ) := by
        dsimp [t]
        exact_mod_cast exceptional_fourth n F E
      linarith
    · rw [ite_eq_right hz]
      by_cases hg : GoodPair F (outputPair b₀ b)
      · rw [ite_eq_left hg]
        obtain ⟨⟨hb, hp⟩, ⟨hbb, hpp⟩⟩ := (goodPair_iff F b₀ b).1 hg
        have hh : N ^ 2 * t ≤ (restrictedFourth F E b : ℝ) := by
          dsimp [N, t, E]
          exact_mod_cast plateaued_pair_fourth n hn he F hF b₀ a₀ c hb₀ hpos hsmall b hb hbb hp hpp
        linarith
      · rw [ite_eq_right hg]
        have hh : N * t ^ 2 ≤ (restrictedFourth F E b : ℝ) := by
          dsimp [N, t]
          exact_mod_cast restricted_baseline n F E b
        linarith
  have hs := Finset.sum_le_sum (s := P.points) (fun b _ => hpoint b)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
  have hgood : (∑ b ∈ P.points, if GoodPair F (outputPair b₀ b) then N ^ 2 * t - N * t ^ 2 else 0) =
      p * (N ^ 2 * t - N * t ^ 2) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, good_representatives_card]
    rfl
  have hzero : (∑ b ∈ P.points, if b = 0 then t ^ 4 - N * t ^ 2 else 0) = t ^ 4 - N * t ^ 2 := by
    simp [hP0]
  rw [hgood, hzero] at hs
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hcard : (P.points.card : ℝ) = N / 2 := by
    have hh : N = 2 * (P.points.card : ℝ) := by
      dsimp [N]
      exact_mod_cast P.card_pairs
    linarith
  rw [hcard] at hs
  have hpair : (∑ b, restrictedFourth F E b) = 2 * ∑ b ∈ P.points, restrictedFourth F E b := by
    rw [P.sum_pairs]
    simp only [E, restricted_fourth_pair, ← two_mul, ← Finset.mul_sum]
  have htotal : 2 * (∑ b ∈ P.points, (restrictedFourth F E b : ℝ)) = N ^ 2 * (3 * t ^ 2 - 2 * t) := by
    dsimp [N, t]
    exact_mod_cast hpair.symm.trans (restricted_fourth_total n F hF E)
  change p * N ^ 2 * t + (N / 2 - p - 1) * N * t ^ 2 + t ^ 4 ≤ N ^ 2 / 2 * (3 * t ^ 2 - 2 * t)
  nlinarith [hs, htotal]

theorem pair_count_upper (N t p : ℝ) (hN : 0 < N) (ht : 0 < t) (htN : t < N)
    (hs : p * N ^ 2 * t + (N / 2 - p - 1) * N * t ^ 2 + t ^ 4 ≤ N ^ 2 / 2 * (3 * t ^ 2 - 2 * t)) :
    p ≤ t - 1 + t ^ 2 / N := by
  have hd : 0 < N * t * (N - t) := mul_pos (mul_pos hN ht) (sub_pos.mpr htN)
  apply (mul_le_mul_iff_left₀ hd).mp
  calc
    p * (N * t * (N - t)) ≤ N ^ 2 * t * (t - 1) + N * t ^ 2 - t ^ 4 := by nlinarith [hs]
    _ = (t - 1 + t ^ 2 / N) * (N * t * (N - t)) := by field_simp; ring

theorem even_error_support_bound {n : ℕ} (hn : 4 ≤ n) (he : Even n) (F : VectorialFunction n) (hF : IsAPN F)
    (b₀ a₀ : BinarySpace n) (c : Bit) (hb₀ : b₀ ≠ 0) (hnp : ¬ IsPlateaued (component F b₀))
    (hpos : 0 < (errorSupport F b₀ a₀ c).card)
    (hsmall : ((errorSupport F b₀ a₀ c).card : ℝ) < (spaceSize n : ℝ) / 4) :
    let t : ℝ := (errorSupport F b₀ a₀ c).card
    (spaceSize n : ℝ) / 2 + 1 - t - t ^ 2 / (spaceSize n : ℝ) ≤ nonplateauedComponentCount F := by
  dsimp only
  have hN : (0 : ℝ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  have ht : (0 : ℝ) < (errorSupport F b₀ a₀ c).card := by exact_mod_cast hpos
  have hp := pair_count_upper (spaceSize n) (errorSupport F b₀ a₀ c).card (plateauedPairCount F b₀)
    hN ht (by linarith) (even_pair_sum hn he F hF b₀ a₀ c hb₀ hpos hsmall)
  have hcount := plateaued_pair_count_bound n (by omega) F b₀ hb₀ hnp
  linarith

end
end APNLinearity.Counts

namespace APNLinearity.Counts
noncomputable section
open _root_.APNLinearity.Fourier Components



theorem minimum_distance_real {n : ℕ} (hn : 1 ≤ n) (F : VectorialFunction n) :
    (nonlinearity F : ℝ) = ((spaceSize n : ℝ) - (linearity F : ℝ)) / 2 := by
  have h : 2 * (nonlinearity F : ℝ) + (linearity F : ℝ) = spaceSize n := by
    exact_mod_cast linearity_distance n hn F
  linarith

theorem even_count_distance : ∀ (n : ℕ), 4 ≤ n → Even n → ∀ (F : VectorialFunction n), IsAPN F →
    (spaceSize n : ℝ) / 2 < (linearity F : ℝ) →
      let t : ℝ := ((spaceSize n : ℝ) - (linearity F : ℝ)) / 2
      (spaceSize n : ℝ) / 2 + 1 - t - t ^ 2 / (spaceSize n : ℝ) ≤
        (nonplateauedComponentCount F : ℝ) := by
  intro n hn he F hF hlarge
  dsimp only
  classical
  obtain ⟨b₀, hb₀, a₀, c, hd⟩ := distance_attained n (by omega) F
  have hcard : (errorSupport F b₀ a₀ c).card = nonlinearity F := by rw [errorSupport_card, hd]
  have ht : ((errorSupport F b₀ a₀ c).card : ℝ) =
      ((spaceSize n : ℝ) - (linearity F : ℝ)) / 2 := by
    rw [hcard, minimum_distance_real (by omega : 1 ≤ n) F]
  have hL : (linearity F : ℝ) < spaceSize n := by
    exact_mod_cast Components.linearity_lt_size (by omega : 3 ≤ n) F hF
  have hpos : 0 < (errorSupport F b₀ a₀ c).card := by
    have hh : (0 : ℝ) < (errorSupport F b₀ a₀ c).card := by linarith
    exact_mod_cast hh
  have hsmall : ((errorSupport F b₀ a₀ c).card : ℝ) < (spaceSize n : ℝ) / 4 := by linarith
  have hnp : ¬ IsPlateaued (component F b₀) := by
    intro hp
    have hbound := plateaued_nonaffine_bound n (component F b₀) hp
      (no_affine_component n (by omega) F hF b₀ hb₀) a₀
    have hdist := distance_walsh n (component F b₀) a₀ c
    rw [hd] at hdist
    have hdistR : 2 * (nonlinearity F : ℝ) +
        ((bitSign c * walsh (component F b₀) a₀ : ℤ) : ℝ) = spaceSize n := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) hdist
      push_cast at h ⊢
      linarith
    have hlin := linearity_distance n (by omega) F
    have hs : ((bitSign c * walsh (component F b₀) a₀ : ℤ) : ℝ) = linearity F := by
      linarith
    have ha : bitSign c * walsh (component F b₀) a₀ ≤ |walsh (component F b₀) a₀| := by
      rcases sign_cases c with hc | hc
      · simpa [hc] using le_abs_self (walsh (component F b₀) a₀)
      · simpa [hc] using neg_le_abs (walsh (component F b₀) a₀)
    have haR : ((bitSign c * walsh (component F b₀) a₀ : ℤ) : ℝ) ≤
        |(walsh (component F b₀) a₀ : ℝ)| := by exact_mod_cast ha
    rw [hs] at haR
    linarith
  have h := even_error_support_bound hn he F hF b₀ a₀ c hb₀ hnp hpos hsmall
  dsimp only at h
  rw [ht] at h
  exact h

end
end APNLinearity.Counts

namespace APNLinearity.Counts
noncomputable section

theorem distance_expression_antitone {N t s : ℝ} (hN : 0 < N) (ht : 0 ≤ t) (hts : t ≤ s) :
    N / 2 + 1 - s - s ^ 2 / N ≤ N / 2 + 1 - t - t ^ 2 / N := by
  have hsq := pow_le_pow_left₀ ht hts 2
  have hdiv := div_le_div_of_nonneg_right hsq hN.le
  linarith

theorem even_count_bound : ∀ (n : ℕ), 4 ≤ n → Even n → ∀ (F : VectorialFunction n), IsAPN F →
    ∀ C : ℝ, 1 / 2 ≤ C → C < 1 →
      (nonplateauedComponentCount F : ℝ) ≤
        (4 * C - C ^ 2 - 1) / 4 * (spaceSize n : ℝ) + 1 →
        (linearity F : ℝ) ≤ C * (spaceSize n : ℝ) := by
  intro n hn he F hF C hC hC1 hq
  by_contra hb
  have hlarge : C * (spaceSize n : ℝ) < linearity F := lt_of_not_ge hb
  let N : ℝ := spaceSize n
  let t : ℝ := (N - linearity F) / 2
  let s : ℝ := (1 - C) * N / 2
  have hN : 0 < N := by dsimp [N]; exact_mod_cast spaceSize_pos n
  have hL : (linearity F : ℝ) < N := by
    dsimp [N]
    exact_mod_cast Components.linearity_lt_size (by omega : 3 ≤ n) F hF
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hts : t < s := by dsimp [s, t, N]; nlinarith
  have hhalf : (spaceSize n : ℝ) / 2 < linearity F := by
    have hh := mul_le_mul_of_nonneg_right hC hN.le
    dsimp [N] at hh
    linarith
  have hd := even_count_distance n hn he F hF hhalf
  change N / 2 + 1 - t - t ^ 2 / N ≤ nonplateauedComponentCount F at hd
  have hsq := pow_le_pow_left₀ ht hts.le 2
  have hdiv := div_le_div_of_nonneg_right hsq hN.le
  have hstrict : N / 2 + 1 - s - s ^ 2 / N < nonplateauedComponentCount F := by linarith
  have hcalc : N / 2 + 1 - s - s ^ 2 / N = (4 * C - C ^ 2 - 1) / 4 * N + 1 := by
    dsimp [s]
    field_simp
    ring
  rw [hcalc] at hstrict
  exact (not_lt_of_ge hq) hstrict

end
end APNLinearity.Counts
