module

public import APNLinearity

public section

namespace APNLinearity

/-- The universal linearity bound and its even-dimensional refinement. -/
theorem linearity_upper_bounds {n : ℕ} (F : VectorialFunction n)
    (hn : 5 ≤ n) (hF : IsAPN F) :
    let N : ℝ := spaceSize n
    (linearity F ≤ N - 6) ∧
    (Even n →
      linearity F ≤ N - Real.sqrt N / 4 - 2) := by
  dsimp only
  refine ⟨EvenBound.linearity_le_sub_six (by omega) F hF, ?_⟩
  intro heven
  exact EvenBound.even_linearity_bound hn heven F hF

/-- The odd-dimensional bound from the exact power of two in a nearest integer to the square root. -/
theorem linearity_bound_of_odd_dimension_and_exact_two_power {n : ℕ}
    (F : VectorialFunction n)
    (hn : 5 ≤ n) (hodd : Odd n) (hF : IsAPN F)
    (p s : ℕ)
    (hp : p = ⌊Real.sqrt (spaceSize n : ℝ)⌋₊ ∨
      p = ⌈Real.sqrt (spaceSize n : ℝ)⌉₊)
    (hps : HasExactTwoPower p s)
    (hs : 5 ≤ s) :
    linearity F ≤ (spaceSize n : ℝ) - (2 : ℝ) ^ (s - 2) - 2 := by
  exact OddDimension.odd_dimension_linearity_bound n hn hodd F hF p s hp hps.1 hps.2 hs

/-- Bounds for ranked absolute Walsh coefficients, retaining multiplicities. -/
theorem ranked_walsh_coefficient_bounds {n : ℕ} (F : VectorialFunction n)
    (hn : 4 ≤ n) (hF : IsAPN F) :
    let N : ℝ := spaceSize n
    (∀ k : ℕ,
      (1 ≤ k ∧ (k : ℝ) ≤ N * (N - 1)) →
      kthLinearity F k ≤
        N / Real.sqrt (k : ℝ) *
          Real.sqrt (1 + ((2 : ℝ) ^ (k - 1) - 1) / N)) ∧
    (kthLinearity F 2 ≤ 2 * (⌊N / 3⌋₊ : ℝ)) ∧
    (2 * (⌊N / 3⌋₊ : ℝ) < 2 * N / 3) ∧
    (kthLinearity F 4 ≤ N / 2) := by
  dsimp only
  refine ⟨?_, ?_, Spectrum.strict_floor_third n, Spectrum.fourth_coefficient_bound n hn F hF⟩
  · intro k hk
    have hcount : ((spaceSize n * (spaceSize n - 1) : ℕ) : ℝ) =
        (spaceSize n : ℝ) * ((spaceSize n : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (spaceSize_pos n)]
      norm_num
    have hK : k ≤ spaceSize n * (spaceSize n - 1) := by
      exact_mod_cast hk.2.trans_eq hcount.symm
    exact Spectrum.ranked_coefficient_bound hn F hF k hk.1 hK
  · rw [Spectrum.floor_third]
    exact Spectrum.second_coefficient_bound n hn F hF

/-- The second Walsh magnitude when the linearity is near the space size. -/
theorem second_linearity_bound_of_near_maximal_linearity {n : ℕ}
    (F : VectorialFunction n)
    (hn : 4 ≤ n) (hF : IsAPN F)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hlin : linearity F = (1 - ε) * (spaceSize n : ℝ)) :
    kthLinearity F 2 / (spaceSize n : ℝ) ≤
      ε / 2 + Real.sqrt (ε - 3 * ε ^ 2 / 4 + 1 / (spaceSize n : ℝ)) := by
  exact Spectrum.walsh_isolation hn F hF ε hε.1 hε.2 hlin

/-- Linearity bounds from the number of nonplateaued nonzero components. -/
theorem linearity_bounds_of_nonplateaued_component_count {n : ℕ}
    (F : VectorialFunction n)
    (hn : 4 ≤ n) (hF : IsAPN F) :
    let N : ℝ := spaceSize n
    let q : ℕ := nonplateauedComponentCount F
    ((Odd n ∧ 0 < q) →
      linearity F ^ 2 ≤ N * (1 + Real.sqrt ((q : ℝ) * (N - 1)))) ∧
    (∀ C : ℝ,
      (Even n ∧ (1 : ℝ) / 2 ≤ C ∧ C < 1 ∧
        (q : ℝ) ≤ ((4 * C - C ^ 2 - 1) / 4) * N + 1) →
      linearity F ≤ C * N) := by
  dsimp only
  constructor
  · rintro ⟨hodd, hq⟩
    exact Counts.odd_count_bound n hn hodd F hF hq
  · rintro C ⟨heven, hC_lower, hC_upper, hq⟩
    exact Counts.even_count_bound n hn heven F hF C hC_lower hC_upper hq

end APNLinearity
