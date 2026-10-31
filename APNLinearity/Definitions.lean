module

public import Mathlib

/-!
# Binary spaces and Walsh spectra
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

end APNLinearity
