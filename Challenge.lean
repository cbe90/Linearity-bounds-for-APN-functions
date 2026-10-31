module

public import Mathlib

/-!
# Main statements of the article 

Christof Beierle and Lukas Kölsch, *Linearity bounds for APN functions*, 
https://arxiv.org/abs/2609.35689v2.

This file contains exactly five statements from the above article, each with one intentional
`sorry`. Completed proofs belong in the separate solution development.

| Declaration | Source |
| --- | --- |
| `APNLinearity.linearity_upper_bounds` | Theorem 1.1 |
| `APNLinearity.linearity_bound_of_odd_dimension_and_exact_two_power` | Proposition 3.7 |
| `APNLinearity.ranked_walsh_coefficient_bounds` | Theorem 1.2 |
| `APNLinearity.second_linearity_bound_of_near_maximal_linearity` | Equation (4.5), in Remark 4.2 |
| `APNLinearity.linearity_bounds_of_nonplateaued_component_count` | Theorem 1.3 |
-/

@[expose] public section

open scoped BigOperators

namespace APNLinearity

/-! ## Binary spaces, components, and the APN property -/

/-- The field with two elements, represented by integers modulo two. -/
abbrev Bit := ZMod 2

/-- The binary vector space 𝔽₂ⁿ, with coordinates indexed by `Fin n`. -/
abbrev BinarySpace (n : ℕ) := Fin n → Bit

/-- A Boolean function on 𝔽₂ⁿ. -/
abbrev BooleanFunction (n : ℕ) := BinarySpace n → Bit

/-- A vectorial function from 𝔽₂ⁿ to itself. -/
abbrev VectorialFunction (n : ℕ) := BinarySpace n → BinarySpace n

/-- The cardinality `N = 2 ^ n` of the input and output spaces. -/
def spaceSize (n : ℕ) : ℕ := 2 ^ n

/-- The usual dot product over 𝔽₂: `∑ i, a i * x i`, computed in `ZMod 2`. -/
def binaryDot {n : ℕ} (a x : BinarySpace n) : Bit :=
  ∑ i : Fin n, a i * x i

/-- The Boolean component `f_b(x) = b · F(x)`, including the zero index. -/
def component {n : ℕ} (F : VectorialFunction n) (b : BinarySpace n) :
    BooleanFunction n :=
  fun x => binaryDot b (F x)

/-- `F` is almost perfect nonlinear: for every nonzero direction `h` and every
output `y`, the equation `F(x + h) + F(x) = y` has at most two solutions. -/
def IsAPN {n : ℕ} (F : VectorialFunction n) : Prop :=
  ∀ h y : BinarySpace n,
    h ≠ 0 →
      let solutions : Finset (BinarySpace n) :=
        {x ∈ Finset.univ | F (x + h) + F x = y}
      solutions.card ≤ 2

/-! ## Walsh coefficients and their ordered magnitudes -/

/-- The sign character on 𝔽₂: zero gives `+1` and one gives `-1`, in ℤ.
This is the unambiguous meaning of `(-1)^t` for a bit `t`. -/
def bitSign (t : Bit) : ℤ :=
  if t = 0 then 1 else -1

/-- The Walsh transform
`W_f(a) = ∑ x ∈ 𝔽₂ⁿ, (-1)^(f(x) + a · x)`, valued in ℤ. -/
def walsh {n : ℕ} (f : BooleanFunction n) (a : BinarySpace n) : ℤ :=
  ∑ x : BinarySpace n, bitSign (f x + binaryDot a x)

/-- The admissible Walsh indices `(a,b)`: `a` is arbitrary and `b ≠ 0`.
This set has `N * (N - 1)` elements, where `N = 2 ^ n`. -/
def nonzeroWalshIndices (n : ℕ) : Finset (BinarySpace n × BinarySpace n) :=
  let allVectors : Finset (BinarySpace n) := Finset.univ
  let nonzeroVectors : Finset (BinarySpace n) :=
    {b ∈ allVectors | b ≠ 0}
  allVectors.product nonzeroVectors

/-- All absolute Walsh coefficients of nonzero components in nonincreasing
order, with multiplicity. -/
noncomputable def orderedWalshMagnitudes {n : ℕ} (F : VectorialFunction n) :
    List ℕ :=
  let indices : Multiset (BinarySpace n × BinarySpace n) :=
    (nonzeroWalshIndices n).val
  let magnitudes : Multiset ℕ :=
    indices.map (fun (a, b) => (walsh (component F b) a).natAbs)
  magnitudes.sort (fun x y => x ≥ y)

/-- The k-th largest absolute Walsh coefficient `𝓛_k(F)`, as a real number, 
for `1 ≤ k ≤ N * (N - 1)`. Returns zero for k outside this range. -/
noncomputable def kthLinearity {n : ℕ} (F : VectorialFunction n) (k : ℕ) : ℝ :=
  let magnitudes := orderedWalshMagnitudes F
  if k = 0 then
    0
  else if h : k - 1 < magnitudes.length then
    (magnitudes[k - 1] : ℝ)
  else
    0

/-- The linearity `𝓛(F) = 𝓛₁(F)`: the maximum of `|W_{b·F}(a)|` over
`a ∈ 𝔽₂ⁿ` and `b ≠ 0`. These indices form a nonempty set when `n ≥ 1`. -/
noncomputable def linearity {n : ℕ} (F : VectorialFunction n) : ℝ :=
  kthLinearity F 1

/-! ## Plateaued components and exact powers of two -/

/-- A Boolean function is plateaued if there is a single positive real
magnitude `λ` such that every Walsh coefficient is `0`, `λ`, or `-λ`.
The coefficient is cast from ℤ to ℝ. This definition includes affine Boolean
functions, as in the paper. -/
def IsPlateaued {n : ℕ} (f : BooleanFunction n) : Prop :=
  ∃ magnitude : ℝ, 0 < magnitude ∧ ∀ a : BinarySpace n,
    (walsh f a : ℝ) = 0 ∨ (walsh f a : ℝ) = magnitude ∨
      (walsh f a : ℝ) = -magnitude

/-- The number `q` of indices `b ≠ 0` for which `b · F` is not plateaued.-/
noncomputable def nonplateauedComponentCount {n : ℕ} (F : VectorialFunction n) : ℕ := 
  Set.ncard {b : BinarySpace n | b ≠ 0 ∧ ¬ IsPlateaued (component F b)}

/-- `2 ^ s` is the largest power of two dividing `p`: it divides `p`,
whereas `2 ^ (s + 1)` does not. In particular this condition excludes `p = 0`.-/
def HasExactTwoPower (p s : ℕ) : Prop :=
  2 ^ s ∣ p ∧ ¬ 2 ^ (s + 1) ∣ p



/-! ## Main results -/

/-- **Theorem 1.1.** If `F` is APN and `n ≥ 5`, then
`𝓛(F) ≤ N - 6`. In even dimension `n ≥ 5` one also has
`𝓛(F) ≤ N - √N / 4 - 2`, where `N = 2 ^ n`.
-/
theorem linearity_upper_bounds {n : ℕ} (F : VectorialFunction n)
    (hn : 5 ≤ n) (hF : IsAPN F) :
    let N : ℝ := spaceSize n
    (linearity F ≤ N - 6) ∧
    (Even n →
      linearity F ≤ N - Real.sqrt N / 4 - 2) := by
  sorry

/-- **Proposition 3.7.** Let `n ≥ 5` be odd and let `F` be APN. Choose
`p` to be either `⌊√N⌋` or `⌈√N⌉`, and let `2 ^ s` be the largest power of
two dividing `p`. If `s ≥ 5`, then `𝓛(F) ≤ N - 2^(s-2) - 2`.
-/
theorem linearity_bound_of_odd_dimension_and_exact_two_power {n : ℕ}
    (F : VectorialFunction n)
    (hn : 5 ≤ n) (hodd : Odd n) (hF : IsAPN F)
    (p s : ℕ)
    (hp : p = ⌊Real.sqrt (spaceSize n : ℝ)⌋₊ ∨
      p = ⌈Real.sqrt (spaceSize n : ℝ)⌉₊)
    (hps : HasExactTwoPower p s)
    (hs : 5 ≤ s) :
    linearity F ≤ (spaceSize n : ℝ) - (2 : ℝ) ^ (s - 2) - 2 := by
  sorry

/-- **Theorem 1.2.** For an APN function in dimension `n ≥ 4`, the `k`-th
largest absolute Walsh coefficient of a nonzero component, counted with
multiplicity, is at most
`N / √k * √(1 + (2^(k-1) - 1) / N)` for every valid rank, where `N = 2 ^ n`.
Also `𝓛₂(F) ≤ 2⌊N/3⌋ < 2N/3` and `𝓛₄(F) ≤ N/2`.
-/
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
  sorry

/-- **Inequality (4.5)** in Remark 4.2. If `F` is APN in dimension `n ≥ 4`
and `𝓛(F) = (1 - ε)N` with `0 < ε < 1`, then
`𝓛₂(F) / N ≤ ε/2 + √(ε - 3ε²/4 + 1/N)`, where `N = 2 ^ n`.
-/
theorem second_linearity_bound_of_near_maximal_linearity {n : ℕ}
    (F : VectorialFunction n)
    (hn : 4 ≤ n) (hF : IsAPN F)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hlin : linearity F = (1 - ε) * (spaceSize n : ℝ)) :
    kthLinearity F 2 / (spaceSize n : ℝ) ≤
      ε / 2 + Real.sqrt (ε - 3 * ε ^ 2 / 4 + 1 / (spaceSize n : ℝ)) := by
  sorry

/-- **Theorem 1.3.** Let `F` be APN in dimension `n ≥ 4`, and let `q`
count its nonplateaued nonzero components. Let `N = 2 ^ n`.
1. If `n` is odd and `q > 0`, then `𝓛(F)² ≤ N(1 + √(q(N-1)))`.
2. If `n` is even, then for every real `1/2 ≤ C < 1`, the hypothesis
   `q ≤ ((4C - C² - 1)/4)N + 1` implies `𝓛(F) ≤ CN`.
-/
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
  sorry

end APNLinearity
