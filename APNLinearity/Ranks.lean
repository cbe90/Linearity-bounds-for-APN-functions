module

public import APNLinearity.AffineWalsh

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.Spectrum
noncomputable section
open _root_.APNLinearity.Fourier

theorem sortedIndices_length {n : ℕ} (F : VectorialFunction n) :
    (sortedIndices F).length = spaceSize n * (spaceSize n - 1) := by
  rw [(sortedIndices_perm F).length_eq, Finset.length_toList, coefficientIndices_card]

theorem ranked_succ_eq_get {n : ℕ} (F : VectorialFunction n) (i : ℕ)
    (hi : i < (orderedWalshMagnitudes F).length) :
    kthLinearity F (i + 1) = ((orderedWalshMagnitudes F).get ⟨i, hi⟩ : ℝ) := by
  simp [kthLinearity, hi, List.get_eq_getElem]

theorem rank_selection {n : ℕ} (F : VectorialFunction n) (k : ℕ)
    (hk : k ≤ spaceSize n * (spaceSize n - 1)) :
    ∃ u : Fin k → IndexSpace n, Function.Injective u ∧
      (∀ i, u i ∈ nonzeroWalshIndices n) ∧
      (∀ i, ((walshAt F (u i)).natAbs : ℝ) = kthLinearity F (i.val + 1)) := by
  classical
  let u : Fin k → IndexSpace n := fun i =>
    (sortedIndices F).get ⟨i.val, by rw [sortedIndices_length]; omega⟩
  have hnd : (sortedIndices F).Nodup := (sortedIndices_perm F).nodup_iff.mpr (Finset.nodup_toList _)
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i j he
    have hh := hnd.injective_get he
    exact Fin.ext (congrArg (fun t : Fin (sortedIndices F).length => t.val) hh)
  · intro i
    exact Finset.mem_toList.mp ((sortedIndices_perm F).mem_iff.mp (List.get_mem _ _))
  · intro i
    rw [ranked_succ_eq_get F i.val (by rw [sortedSpectrum_length]; omega)]
    simp only [orderedWalshMagnitudes_eq_map, List.get_eq_getElem, List.getElem_map]
    rfl

theorem ranked_antitone {n : ℕ} (F : VectorialFunction n) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ spaceSize n * (spaceSize n - 1)) :
    kthLinearity F j ≤ kthLinearity F i := by
  have hi' : i - 1 < (orderedWalshMagnitudes F).length := by rw [sortedSpectrum_length]; omega
  have hj' : j - 1 < (orderedWalshMagnitudes F).length := by rw [sortedSpectrum_length]; omega
  have heI := ranked_succ_eq_get F (i - 1) hi'
  have heJ := ranked_succ_eq_get F (j - 1) hj'
  rw [Nat.sub_add_cancel hi] at heI
  rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at heJ
  rw [heI, heJ]
  exact_mod_cast (sortedSpectrum_pairwise F).rel_get_of_le (show (⟨i - 1, hi'⟩ : Fin _) ≤ ⟨j - 1, hj'⟩ by
    exact Nat.sub_le_sub_right hij 1)

theorem natAbs_sq_real (w : ℤ) : ((w.natAbs : ℕ) : ℝ) ^ 2 = (w : ℝ) ^ 2 := by
  have he : (w.natAbs : ℤ) ^ 2 = w ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
  have hr := congrArg (fun z : ℤ => (z : ℝ)) he
  simpa only [Int.cast_pow, Int.cast_natCast] using hr

theorem rank_square_sum_lower {n : ℕ} (F : VectorialFunction n) (k : ℕ)
    (_hk : 1 ≤ k) (hK : k ≤ spaceSize n * (spaceSize n - 1)) :
    (k : ℝ) * (kthLinearity F k : ℝ) ^ 2 ≤
      ∑ i ∈ Finset.range k, (kthLinearity F (i + 1) : ℝ) ^ 2 := by
  calc
    _ = ∑ _i ∈ Finset.range k, (kthLinearity F k : ℝ) ^ 2 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : kthLinearity F k ≤ kthLinearity F (i + 1) :=
        ranked_antitone F (by omega) (by have := Finset.mem_range.mp hi; omega) hK
      have hr : (kthLinearity F k : ℝ) ≤ kthLinearity F (i + 1) := by exact_mod_cast hn
      exact pow_le_pow_left₀ (kthLinearity_nonneg F k) hr 2

end
end APNLinearity.Spectrum

open scoped BigOperators

namespace APNLinearity.Spectrum
noncomputable section
open _root_.APNLinearity.Fourier

theorem ranked_partial_sums : ∀ (n : ℕ), 4 ≤ n → ∀ (F : VectorialFunction n), IsAPN F →
    ∀ k : ℕ, 1 ≤ k → k ≤ spaceSize n * (spaceSize n - 1) →
      (∑ i ∈ Finset.range k, (kthLinearity F (i + 1) : ℝ) ^ 2) ≤
        (spaceSize n : ℝ) ^ 2 + ((2 : ℝ) ^ (k - 1) - 1) * (spaceSize n : ℝ) := by
  intro n hn F hF k hk hK
  classical
  obtain ⟨u, hi, hm, hv⟩ := rank_selection F k hK
  let S := Finset.univ.image u
  let U := affineSpan Bit (S : Set (IndexSpace n))
  have hsub : S ⊆ Finset.univ.filter (fun z : IndexSpace n => z ∈ U ∧ z ≠ 0) := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    have hmem : u i ∈ U := subset_affineSpan Bit (S : Set (IndexSpace n)) hz
    have hne : u i ≠ 0 := by
      have hh : (u i).2 ≠ 0 := by simpa [nonzeroWalshIndices] using hm i
      exact fun he => hh (congrArg Prod.snd he)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem, hne⟩
  have hU : ∃ z, z ∈ U := by
    refine ⟨u ⟨0, by omega⟩, ?_⟩
    apply subset_affineSpan Bit (S : Set (IndexSpace n))
    exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
  have hr : Module.finrank Bit U.direction ≤ k - 1 := by
    rw [show U.direction = vectorSpan Bit (S : Set (IndexSpace n)) from direction_affineSpan _ _]
    exact finrank_vectorSpan_image_finset_le Bit u Finset.univ (by simp; omega)
  have hs : (∑ i ∈ Finset.range k, (kthLinearity F (i + 1) : ℝ) ^ 2) =
      ∑ z ∈ S, (walshAt F z : ℝ) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (kthLinearity F (i + 1) : ℝ) ^ 2) k]
    rw [Finset.sum_image (fun _ _ _ _ he => hi he)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hv i, natAbs_sq_real]
  rw [hs]
  have hsum : (∑ z ∈ S, (walshAt F z : ℝ) ^ 2) ≤
      ∑ z ∈ Finset.univ.filter (fun z : IndexSpace n => z ∈ U ∧ z ≠ 0), (walshAt F z : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => sq_nonneg _)
  have hbound := affine_walsh_bound n hn F hF U hU
  have hN : (0 : ℝ) ≤ spaceSize n := by positivity
  have hb : (∑ z ∈ S, (walshAt F z : ℝ) ^ 2) ≤
      (spaceSize n : ℝ) ^ 2 + ((2 : ℝ) ^ Module.finrank Bit U.direction - 1) * spaceSize n := by
    split_ifs at hbound <;> linarith
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
  have hh := mul_le_mul_of_nonneg_right (sub_le_sub_right hp 1) hN
  linarith

theorem rank_square_bound {n : ℕ} (hn : 4 ≤ n) (F : VectorialFunction n) (hF : IsAPN F)
    (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ spaceSize n * (spaceSize n - 1)) :
    (k : ℝ) * (kthLinearity F k : ℝ) ^ 2 ≤
      (spaceSize n : ℝ) ^ 2 + ((2 : ℝ) ^ (k - 1) - 1) * spaceSize n :=
  (rank_square_sum_lower F k hk hK).trans (ranked_partial_sums n hn F hF k hk hK)

end
end APNLinearity.Spectrum

open scoped BigOperators

namespace APNLinearity.Spectrum
noncomputable section
open _root_.APNLinearity.Fourier

theorem two_index_square_bound {n : ℕ} (hn : 4 ≤ n) (F : VectorialFunction n) (hF : IsAPN F)
    (u v : IndexSpace n) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    walshAt F u ^ 2 + walshAt F v ^ 2 + walshAt F (u + v) ^ 2 ≤
      (spaceSize n : ℤ) ^ 2 + 2 * spaceSize n := by
  classical
  let L : Submodule Bit (IndexSpace n) := Submodule.span Bit ({u, v} : Set (IndexSpace n))
  let U := L.toAffineSubspace
  have huL : u ∈ L := Submodule.subset_span (by simp)
  have hvL : v ∈ L := Submodule.subset_span (by simp)
  have hsum0 : u + v ≠ 0 := by
    intro he
    have hh := congrArg (fun z => z + v) he
    exact huv (by simpa using hh)
  have hsu : u + v ≠ u := by
    intro he
    exact hv (add_left_cancel (show u + v = u + 0 by simpa using he))
  have hsv : u + v ≠ v := by
    intro he
    exact hu (add_right_cancel (show u + v = 0 + v by simpa using he))
  have hsub : ({u, v, u + v} : Finset (IndexSpace n)) ⊆
      Finset.univ.filter (fun z => z ∈ U ∧ z ≠ 0) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huL, hu⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvL, hv⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, L.add_mem huL hvL, hsum0⟩
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun z => (walshAt F z : ℝ) ^ 2) hsub (fun z _ _ => sq_nonneg _)
  have hr : Module.finrank Bit L ≤ 2 := by
    have hh := finrank_span_finset_le_card (R := Bit) ({u, v} : Finset (IndexSpace n))
    have hset : (({u, v} : Finset (IndexSpace n)) : Set (IndexSpace n)) = {u, v} := by
      ext x
      simp
    unfold Set.finrank at hh
    rw [hset, Finset.card_pair huv] at hh
    exact hh
  have hb := affine_walsh_bound n hn F hF U ⟨0, L.zero_mem⟩
  rw [ite_eq_left (show (0 : IndexSpace n) ∈ U from L.zero_mem), Submodule.toAffineSubspace_direction] at hb
  have hp : (2 : ℝ) ^ Module.finrank Bit L ≤ 4 := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
    norm_num at hh ⊢
    exact hh
  have hpN := mul_le_mul_of_nonneg_right (sub_le_sub_right hp 2)
    (show (0 : ℝ) ≤ spaceSize n by positivity)
  have hsum : (∑ z ∈ ({u, v, u + v} : Finset (IndexSpace n)), (walshAt F z : ℝ) ^ 2) =
      (walshAt F u : ℝ) ^ 2 + (walshAt F v : ℝ) ^ 2 + (walshAt F (u + v) : ℝ) ^ 2 := by
    simp [huv, hsu.symm, hsv.symm, add_assoc]
  rw [hsum] at hs
  have hreal : (walshAt F u : ℝ) ^ 2 + (walshAt F v : ℝ) ^ 2 + (walshAt F (u + v) : ℝ) ^ 2 ≤
      (spaceSize n : ℝ) ^ 2 + 2 * spaceSize n := by linarith
  exact_mod_cast hreal

theorem sign_product_inequality (a b : Bit) : bitSign a + bitSign b - 1 ≤ bitSign a * bitSign b := by
  rcases bit_eq_zero_or_one a with rfl | rfl <;>
    rcases bit_eq_zero_or_one b with rfl | rfl <;> norm_num

theorem two_index_sign_bound {n : ℕ} (F : VectorialFunction n) (u v : IndexSpace n) :
    |walshAt F u| + |walshAt F v| - (spaceSize n : ℤ) ≤ |walshAt F (u + v)| := by
  obtain ⟨c, hc⟩ := exists_sign_abs (walshAt F u)
  obtain ⟨d, hd⟩ := exists_sign_abs (walshAt F v)
  have hp (x : BinarySpace n) :
      bitSign c * productCharacter u (x, F x) + bitSign d * productCharacter v (x, F x) - 1 ≤
        (bitSign c * bitSign d) * productCharacter (u + v) (x, F x) := by
    change bitSign c * bitSign (indexDot u (x, F x)) + bitSign d * bitSign (indexDot v (x, F x)) - 1 ≤
      (bitSign c * bitSign d) * bitSign (indexDot (u + v) (x, F x))
    rw [indexDot_add_left, sign_add]
    have hh := sign_product_inequality (c + indexDot u (x, F x)) (d + indexDot v (x, F x))
    simp only [sign_add] at hh
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hp x)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← walshAt_character, Finset.sum_const, Finset.card_univ, card_binary, nsmul_eq_mul, mul_one] at hs
  rw [hc, hd] at hs
  have ha : |(bitSign c * bitSign d) * walshAt F (u + v)| = |walshAt F (u + v)| := by
    rcases sign_cases c with he | he <;> rcases sign_cases d with hf | hf <;> simp [he, hf]
  exact hs.trans ((le_abs_self _).trans_eq ha)

/-- The paper's even-integer argument after the two inequalities (4.3) and (4.4). -/
theorem pair_minimum_bound (N a b w m : ℤ) (hN : 0 ≤ N) (hm : 0 ≤ m)
    (hma : m ≤ |a|) (hmb : m ≤ |b|) (heven : 2 ∣ m)
    (hsq : a ^ 2 + b ^ 2 + w ^ 2 ≤ N ^ 2 + 2 * N)
    (hsign : |a| + |b| - N ≤ |w|) : 3 * m ≤ 2 * N := by
  by_contra hbad
  have hstrict : 2 * N < 3 * m := by omega
  have hpos : 0 ≤ 2 * m - N := by omega
  have hwm : 2 * m - N ≤ |w| := by omega
  have ha2 := pow_le_pow_left₀ hm hma 2
  have hb2 := pow_le_pow_left₀ hm hmb 2
  have hw2 := pow_le_pow_left₀ hpos hwm 2
  rw [sq_abs] at ha2 hb2 hw2
  have hpoly : m * (3 * m - 2 * N) ≤ N := by nlinarith
  obtain ⟨t, ht⟩ := heven
  have hgap : 2 ≤ 3 * m - 2 * N := by omega
  have hmul := mul_le_mul_of_nonneg_left hgap hm
  nlinarith

end
end APNLinearity.Spectrum

open scoped BigOperators

namespace APNLinearity.Spectrum
noncomputable section
open _root_.APNLinearity.Fourier

theorem spaceSize_ge_sixteen {n : ℕ} (hn : 4 ≤ n) : 16 ≤ spaceSize n := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) hn
  norm_num at h
  exact h

theorem four_le_index_count {n : ℕ} (hn : 4 ≤ n) : 4 ≤ spaceSize n * (spaceSize n - 1) := by
  have hN := spaceSize_ge_sixteen hn
  have hm := Nat.le_mul_of_pos_right (spaceSize n) (show 0 < spaceSize n - 1 by omega)
  omega

theorem ranked_even {n : ℕ} (hn : 1 ≤ n) (F : VectorialFunction n) (k : ℕ)
    (hk : 1 ≤ k) (hK : k ≤ spaceSize n * (spaceSize n - 1)) :
    ∃ t : ℕ, kthLinearity F k = 2 * (t : ℝ) := by
  obtain ⟨u, _, hu⟩ := ranked_coefficient_attained F k hk hK
  have hdiv : 2 ∣ (walshAt F u).natAbs :=
    Int.natCast_dvd.mp (walsh_even n hn (component F u.2) u.1)
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨t, ?_⟩
  rw [hu, ht]
  push_cast
  rfl

theorem second_coefficient_bound (n : ℕ) (hn : 4 ≤ n)
    (F : VectorialFunction n) (hF : IsAPN F) :
    kthLinearity F 2 ≤ 2 * ((spaceSize n / 3 : ℕ) : ℝ) := by
  have hcount := four_le_index_count hn
  obtain ⟨s, hi, hm, hs⟩ := rank_selection F 2 (by omega)
  let u := s 0
  let v := s 1
  have hu : u ≠ 0 := by
    have hh : (s 0).2 ≠ 0 := by simpa [nonzeroWalshIndices] using hm 0
    exact fun he => hh (congrArg Prod.snd he)
  have hv : v ≠ 0 := by
    have hh : (s 1).2 ≠ 0 := by simpa [nonzeroWalshIndices] using hm 1
    exact fun he => hh (congrArg Prod.snd he)
  have huv : u ≠ v := by
    intro he
    have hh : (0 : Fin 2) = 1 := hi he
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  have hvalU : ((walshAt F u).natAbs : ℝ) = kthLinearity F 1 := hs 0
  have hvalV : ((walshAt F v).natAbs : ℝ) = kthLinearity F 2 := hs 1
  have hmon := ranked_antitone F (i := 1) (j := 2) (by omega) (by omega) (by omega)
  have hmN : (walshAt F v).natAbs ≤ (walshAt F u).natAbs := by
    exact_mod_cast (show ((walshAt F v).natAbs : ℝ) ≤ ((walshAt F u).natAbs : ℝ) by
      rw [hvalU, hvalV]; exact hmon)
  have hma : ((walshAt F v).natAbs : ℤ) ≤ |walshAt F u| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hmN
  have hmb : ((walshAt F v).natAbs : ℤ) ≤ |walshAt F v| := by
    rw [Int.natCast_natAbs]
  have heven : 2 ∣ (walshAt F v).natAbs :=
    Int.natCast_dvd.mp (walsh_even n (by omega) (component F v.2) v.1)
  have hh := pair_minimum_bound (spaceSize n) (walshAt F u) (walshAt F v)
    (walshAt F (u + v)) (walshAt F v).natAbs (by positivity) (by positivity)
    hma hmb (by exact_mod_cast heven)
    (two_index_square_bound hn F hF u v hu hv huv) (two_index_sign_bound F u v)
  have hNat : 3 * (walshAt F v).natAbs ≤ 2 * spaceSize n := by exact_mod_cast hh
  obtain ⟨t, ht⟩ := heven
  have hbound : (walshAt F v).natAbs ≤ 2 * (spaceSize n / 3) := by omega
  rw [← hvalV]
  exact_mod_cast hbound

theorem spaceSize_multiple_four {n : ℕ} (hn : 2 ≤ n) : ∃ q : ℕ, spaceSize n = 4 * q := by
  refine ⟨2 ^ (n - 2), ?_⟩
  unfold spaceSize
  conv_lhs => rw [show n = n - 2 + 2 by omega]
  rw [pow_add]
  ring

theorem fourth_coefficient_bound (n : ℕ) (hn : 4 ≤ n)
    (F : VectorialFunction n) (hF : IsAPN F) :
    kthLinearity F 4 ≤ (spaceSize n : ℝ) / 2 := by
  have hcount := four_le_index_count hn
  have hh := rank_square_bound hn F hF 4 (by omega) hcount
  norm_num at hh
  obtain ⟨q, hq⟩ := spaceSize_multiple_four (by omega : 2 ≤ n)
  obtain ⟨t, ht⟩ := ranked_even (by omega : 1 ≤ n) F 4 (by omega) hcount
  have hqR : (spaceSize n : ℝ) = 4 * (q : ℝ) := by exact_mod_cast hq
  have hle : t ≤ q := by
    by_contra he
    have hgap : q + 1 ≤ t := by omega
    have hgapR : (q : ℝ) + 1 ≤ t := by exact_mod_cast hgap
    rw [ht, hqR] at hh
    nlinarith [sq_nonneg ((t : ℝ) - (q : ℝ) - 1)]
  have hleR : (t : ℝ) ≤ q := by exact_mod_cast hle
  rw [ht, hqR]
  linarith

end
end APNLinearity.Spectrum

namespace APNLinearity.Spectrum
noncomputable section

theorem ranked_coefficient_bound {n : ℕ} (hn : 4 ≤ n) (F : VectorialFunction n) (hF : IsAPN F)
    (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ spaceSize n * (spaceSize n - 1)) :
    (kthLinearity F k : ℝ) ≤ (spaceSize n : ℝ) / Real.sqrt (k : ℝ) *
      Real.sqrt (1 + ((2 : ℝ) ^ (k - 1) - 1) / (spaceSize n : ℝ)) := by
  have hL := kthLinearity_nonneg F k
  have hN : (0 : ℝ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hQ : 0 ≤ (2 : ℝ) ^ (k - 1) - 1 := by
    have hh := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k - 1)
    linarith
  let t : ℝ := 1 + ((2 : ℝ) ^ (k - 1) - 1) / (spaceSize n : ℝ)
  have ht : 0 ≤ t := add_nonneg (by norm_num) (div_nonneg hQ hN.le)
  have he : (spaceSize n : ℝ) ^ 2 * t =
      (spaceSize n : ℝ) ^ 2 + ((2 : ℝ) ^ (k - 1) - 1) * spaceSize n := by
    dsimp [t]
    field_simp
  have hb := rank_square_bound hn F hF k hk hK
  have hs : ((kthLinearity F k : ℝ) * Real.sqrt (k : ℝ)) ^ 2 ≤
      ((spaceSize n : ℝ) * Real.sqrt t) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hkR.le, Real.sq_sqrt ht, he]
    nlinarith
  have hl := (sq_le_sq₀ (by positivity : 0 ≤ (kthLinearity F k : ℝ) * Real.sqrt (k : ℝ))
    (by positivity : 0 ≤ (spaceSize n : ℝ) * Real.sqrt t)).1 hs
  have hkS : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkR
  calc
    _ ≤ ((spaceSize n : ℝ) * Real.sqrt t) / Real.sqrt (k : ℝ) := (le_div_iff₀ hkS).2 hl
    _ = _ := by dsimp [t]; ring

theorem floor_third (N : ℕ) : ⌊(N : ℝ) / 3⌋₊ = N / 3 := by
  simpa using Nat.floor_div_natCast (N : ℝ) 3

theorem strict_floor_third (n : ℕ) :
    2 * (⌊(spaceSize n : ℝ) / 3⌋₊ : ℝ) < 2 * (spaceSize n : ℝ) / 3 := by
  have hnd : ¬ 3 ∣ spaceSize n := by
    intro h
    have hp : Nat.Prime 3 := by decide
    have hh : 3 ∣ 2 := hp.dvd_of_dvd_pow h
    norm_num at hh
  have hmod : spaceSize n % 3 ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have hlt : 3 * (spaceSize n / 3) < spaceSize n := by omega
  have hr : (3 : ℝ) * (spaceSize n / 3 : ℕ) < spaceSize n := by exact_mod_cast hlt
  rw [floor_third]
  linarith

end
end APNLinearity.Spectrum
