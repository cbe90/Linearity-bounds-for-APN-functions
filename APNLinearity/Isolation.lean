module

public import APNLinearity.Ranks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Topology

namespace APNLinearity.Spectrum
noncomputable section
open _root_.APNLinearity.Fourier Filter

theorem leading_pair_moment {n : ℕ} (hn : 4 ≤ n)
    (F : VectorialFunction n) (hF : IsAPN F) :
    kthLinearity F 1 ^ 2 + kthLinearity F 2 ^ 2 +
      max (kthLinearity F 1 + kthLinearity F 2 - spaceSize n) 0 ^ 2 ≤
        (spaceSize n : ℝ) ^ 2 + 2 * spaceSize n := by
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
  have hsign : |(walshAt F u : ℝ)| + |(walshAt F v : ℝ)| - spaceSize n ≤
      |(walshAt F (u + v) : ℝ)| := by exact_mod_cast two_index_sign_bound F u v
  have habsU : |(walshAt F u : ℝ)| = kthLinearity F 1 := by
    simpa only [natAbs_cast_real] using hvalU
  have habsV : |(walshAt F v : ℝ)| = kthLinearity F 2 := by
    simpa only [natAbs_cast_real] using hvalV
  rw [habsU, habsV] at hsign
  have hmax := max_le hsign (abs_nonneg (walshAt F (u + v) : ℝ))
  have hsq := pow_le_pow_left₀ (le_max_right
    (kthLinearity F 1 + kthLinearity F 2 - spaceSize n) 0) hmax 2
  rw [sq_abs] at hsq
  have hpair : (walshAt F u : ℝ) ^ 2 + (walshAt F v : ℝ) ^ 2 +
      (walshAt F (u + v) : ℝ) ^ 2 ≤ (spaceSize n : ℝ) ^ 2 + 2 * spaceSize n := by
    exact_mod_cast two_index_square_bound hn F hF u v hu hv huv
  have ha : kthLinearity F 1 ^ 2 = (walshAt F u : ℝ) ^ 2 := by
    rw [← habsU, sq_abs]
  have hb : kthLinearity F 2 ^ 2 = (walshAt F v : ℝ) ^ 2 := by
    rw [← habsV, sq_abs]
  nlinarith only [ha, hb, hsq, hpair]

theorem isolation_of_pair_moment (N A ε : ℝ) (hN : 0 < N)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hpair : ((1 - ε) * N) ^ 2 + A ^ 2 + max ((1 - ε) * N + A - N) 0 ^ 2 ≤
      N ^ 2 + 2 * N) :
    A / N ≤ ε / 2 + Real.sqrt (ε - 3 * ε ^ 2 / 4 + 1 / N) := by
  let q := ε - 3 * ε ^ 2 / 4 + 1 / N
  have hq : ε ^ 2 / 4 ≤ q := by
    have h := mul_nonneg hε0 (sub_nonneg.mpr hε1)
    have hNinv : 0 ≤ 1 / N := by positivity
    dsimp [q]
    nlinarith
  have hq0 : 0 ≤ q := by nlinarith [sq_nonneg ε]
  have hs := Real.sq_sqrt hq0
  have hs0 := Real.sqrt_nonneg q
  by_cases hx : A / N ≤ ε
  · have he : ε / 2 ≤ Real.sqrt q := by nlinarith
    change A / N ≤ ε / 2 + Real.sqrt q
    linarith
  · have hpos : 0 ≤ (1 - ε) * N + A - N := by
      have h := (lt_div_iff₀ hN).mp (lt_of_not_ge hx)
      nlinarith
    rw [max_eq_left hpos] at hpair
    have hscaled : (A / N - ε / 2) ^ 2 ≤ q := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hN)).mp
      have he : (A / N - ε / 2) ^ 2 * N ^ 2 = (A - ε * N / 2) ^ 2 := by
        field_simp
      have heq : q * N ^ 2 = ε * N ^ 2 - 3 * ε ^ 2 * N ^ 2 / 4 + N := by
        dsimp [q]
        field_simp
      rw [he, heq]
      nlinarith [hpair]
    change A / N ≤ ε / 2 + Real.sqrt q
    nlinarith

theorem walsh_isolation {n : ℕ} (hn : 4 ≤ n) (F : VectorialFunction n) (hF : IsAPN F)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hlin : (linearity F : ℝ) = (1 - ε) * spaceSize n) :
    (kthLinearity F 2 : ℝ) / spaceSize n ≤
      ε / 2 + Real.sqrt (ε - 3 * ε ^ 2 / 4 + 1 / (spaceSize n : ℝ)) := by
  have h := leading_pair_moment hn F hF
  rw [rank_one n (by omega) F, hlin] at h
  exact isolation_of_pair_moment _ _ ε (by exact_mod_cast spaceSize_pos n) hε0.le hε1.le h

end
end APNLinearity.Spectrum
