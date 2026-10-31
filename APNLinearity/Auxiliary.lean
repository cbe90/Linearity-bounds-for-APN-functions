module

public import APNLinearity.Definitions

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace APNLinearity
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A binary map with an arbitrary output dimension. -/
abbrev VectorialMap (n m : ℕ) := BinarySpace n → BinarySpace m

/-- A component of a map with an arbitrary output dimension. -/
def mapComponent {n m : ℕ} (F : VectorialMap n m) (b : BinarySpace m) :
    BooleanFunction n := fun x => binaryDot b (F x)

/-- The derivative-fibre bound for maps to a general additive space. -/
def DerivativeBound {n : ℕ} {Y : Type*} [Add Y] (F : BinarySpace n → Y) : Prop := by
  classical
  exact ∀ h y, h ≠ 0 →
    (Finset.univ.filter (fun x => F (x + h) + F x = y)).card ≤ 2

theorem IsAPN.derivativeBound {n : ℕ} {F : VectorialFunction n}
    (hF : IsAPN F) : DerivativeBound F := by
  classical
  intro h y hh
  convert hF h y hh using 1; congr

def character {n : ℕ} (a x : BinarySpace n) : ℤ := bitSign (binaryDot a x)

def productCharacter {n m : ℕ} (a x : BinarySpace n × BinarySpace m) : ℤ :=
  bitSign (binaryDot a.1 x.1 + binaryDot a.2 x.2)

def walshAt {n : ℕ} (F : VectorialFunction n) (u : BinarySpace n × BinarySpace n) : ℤ :=
  walsh (component F u.2) u.1

def affineBoolean {n : ℕ} (a : BinarySpace n) (c : Bit) : BooleanFunction n :=
  fun x => binaryDot a x + c

def IsAffine {n : ℕ} (f : BooleanFunction n) : Prop :=
  ∃ a c, f = affineBoolean a c

def derivative {X Y : Type*} [Add X] [Add Y] (F : X → Y) (h x : X) : Y :=
  F (x + h) + F x

def weight {X : Type*} [Fintype X] (f : X → Bit) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x => f x = 1)).card

def hammingDistance {n : ℕ} (f g : BooleanFunction n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x => f x ≠ g x)).card

def IsBalanced {n : ℕ} (f : BooleanFunction n) : Prop := 2 * weight f = spaceSize n


/-- Uniqueness of sums of unordered pairs of DISTINCT elements. -/
def IsBinarySidon {G : Type*} [Add G] (A : Finset G) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≠ b → c ≠ d → a + b = c + d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def graph {n : ℕ} {Y : Type*} (F : BinarySpace n → Y) : Finset (BinarySpace n × Y) := by
  classical
  exact Finset.univ.image (fun x => (x, F x))

def restrictedGraph {n : ℕ} {Y : Type*} (E : Finset (BinarySpace n))
    (F : BinarySpace n → Y) : Finset (BinarySpace n × Y) := by
  classical
  exact E.image (fun x => (x, F x))

def partialGraph {n m : ℕ} (E : Finset (BinarySpace n))
    (H : {x : BinarySpace n // x ∉ E} → BinarySpace m) : Finset (BinarySpace n × BinarySpace m) := by
  classical
  exact Finset.univ.image (fun x => (x.val, H x))

def indicator {n : ℕ} (E : Finset (BinarySpace n)) : BooleanFunction n := by
  classical
  exact fun x => if x ∈ E then 1 else 0

def splitMap {n : ℕ} (g : BooleanFunction n) (H : VectorialMap n (n - 1)) :
    BinarySpace n → Bit × BinarySpace (n - 1) := fun x => (g x, H x)

/-- Sort INDICES. Equal coefficient values remain separate entries. -/
def sortedIndices {n : ℕ} (F : VectorialFunction n) : List (BinarySpace n × BinarySpace n) :=
  (nonzeroWalshIndices n).toList.mergeSort
    (fun u v => decide ((walshAt F v).natAbs ≤ (walshAt F u).natAbs))

/-- All distances to affine Boolean functions, including both constants. -/
def affineDistances {n : ℕ} (F : VectorialFunction n) : Finset ℕ := by
  classical
  exact ((nonzeroWalshIndices n) ×ˢ (Finset.univ : Finset Bit)).image
    (fun p => hammingDistance (component F p.1.2) (affineBoolean p.1.1 p.2))

/-- A total finite minimum; the empty case occurs only at dimension zero. -/
def nonlinearity {n : ℕ} (F : VectorialFunction n) : ℕ :=
  (affineDistances F).fold min (spaceSize n) id

def HasPlateauedMagnitude {n : ℕ} (f : BooleanFunction n) (amplitude : ℤ) : Prop :=
  0 < amplitude ∧ ∀ a, walsh f a = 0 ∨ walsh f a = amplitude ∨ walsh f a = -amplitude

/-- A Boolean function whose squared Walsh coefficients all equal the space size. -/
def IsBent {n : ℕ} (f : BooleanFunction n) : Prop :=
  ∀ a, walsh f a ^ 2 = (spaceSize n : ℤ)

def fourthMoment {n : ℕ} (f : BooleanFunction n) : ℤ := ∑ a, walsh f a ^ 4

def kappa {n : ℕ} (f : BooleanFunction n) : ℝ :=
  (fourthMoment f : ℝ) / (spaceSize n : ℝ) ^ 3

def fourier {n : ℕ} (u : BinarySpace n → ℝ) (a : BinarySpace n) : ℝ :=
  ∑ x, u x * (character a x : ℝ)

def characterSum {n : ℕ} (A : Finset (BinarySpace n)) (a : BinarySpace n) : ℤ :=
  ∑ x ∈ A, character a x

def productCharacterSum {n m : ℕ} (A : Finset (BinarySpace n × BinarySpace m))
    (a : BinarySpace n × BinarySpace m) : ℤ := ∑ x ∈ A, productCharacter a x

def outputPairs {n : ℕ} (b₀ : BinarySpace n) : Finset (Finset (BinarySpace n)) := by
  classical
  exact Finset.univ.image (fun b => {b, b + b₀})

def plateauedPairCount {n : ℕ} (F : VectorialFunction n) (b₀ : BinarySpace n) : ℕ := by
  classical
  exact ((outputPairs b₀).filter
    (fun P => ∀ b ∈ P, b ≠ 0 ∧ IsPlateaued (component F b))).card

def restrictedWalsh {n : ℕ} (F : VectorialFunction n) (E : Finset (BinarySpace n))
    (b a : BinarySpace n) : ℤ := ∑ x ∈ E, bitSign (component F b x + binaryDot a x)

/-- The Walsh sum on a subset, with arbitrary output dimension. -/
def partialWalsh {n m : ℕ} (D : Finset (BinarySpace n)) (K : VectorialMap n m)
    (b : BinarySpace m) (a : BinarySpace n) : ℤ :=
  ∑ x ∈ D, character b (K x) * character a x

def restrictedFourth {n : ℕ} (F : VectorialFunction n) (E : Finset (BinarySpace n))
    (b : BinarySpace n) : ℤ := ∑ a, restrictedWalsh F E b a ^ 4

def arithmeticMean {p : ℕ} (X : Fin p → ℤ) : ℝ := (∑ i, (X i : ℝ)) / p

def polynomialP (a T : ℤ) : ℤ := ((T + a) ^ 2 - 4) * ((T - a) ^ 2 - 4)

theorem nonplateauedComponentCount_eq_card {n : ℕ} (F : VectorialFunction n) :
    nonplateauedComponentCount F =
      (Finset.univ.filter (fun b => b ≠ 0 ∧ ¬ IsPlateaued (component F b))).card := by
  classical
  let S := Finset.univ.filter (fun b => b ≠ 0 ∧ ¬ IsPlateaued (component F b))
  have hS : {b : BinarySpace n | b ≠ 0 ∧ ¬ IsPlateaued (component F b)} = (S : Set _) := by
    ext b
    simp [S]
  rw [nonplateauedComponentCount, hS, Set.ncard_coe_finset]

theorem natAbs_cast_real (w : ℤ) : (w.natAbs : ℝ) = |(w : ℝ)| := by
  simpa only [Int.cast_abs, Int.cast_natCast] using
    congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs w)

theorem kthLinearity_nonneg {n : ℕ} (F : VectorialFunction n) (k : ℕ) :
    0 ≤ kthLinearity F k := by
  unfold kthLinearity
  dsimp only
  split_ifs <;> positivity

theorem linearity_nonneg {n : ℕ} (F : VectorialFunction n) : 0 ≤ linearity F :=
  kthLinearity_nonneg F 1

end
end APNLinearity
