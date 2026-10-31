module

public import APNLinearity.Components

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.SmallSupport
noncomputable section
open Sidon _root_.APNLinearity.Fourier

/-- One representative of each pair `{x,x+h}`. -/
structure PairRepresentatives {n : ℕ} (h : BinarySpace n) where
  points : Finset (BinarySpace n)
  mem_add (x : BinarySpace n) : x + h ∈ points ↔ x ∉ points

theorem exists_pair_representatives {n : ℕ} (h : BinarySpace n) (hh : h ≠ 0) :
    Nonempty (PairRepresentatives h) := by
  classical
  obtain ⟨a, ha⟩ := exists_dot_one hh
  refine ⟨⟨Finset.univ.filter (fun x => binaryDot a x = 0), ?_⟩⟩
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, dot_add_right, ha]
  rcases bit_eq_zero_or_one (binaryDot a x) with hx | hx <;> simp [hx]

namespace PairRepresentatives
variable {n : ℕ} {h : BinarySpace n} (P : PairRepresentatives h)

theorem sum_pairs {R : Type*} [AddCommMonoid R] (f : BinarySpace n → R) :
    (∑ x, f x) = ∑ x ∈ P.points, (f x + f (x + h)) := by
  classical
  have hi : Function.Injective (fun x : BinarySpace n => x + h) := add_left_injective h
  have hu : P.points ∪ P.points.image (fun x => x + h) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
    by_cases hx : x ∈ P.points
    · exact Or.inl hx
    · exact Or.inr ⟨x + h, (P.mem_add x).2 hx, binary_add_cancel_right x h⟩
  have hd : Disjoint P.points (P.points.image (fun x => x + h)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hm
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hm
    exact (P.mem_add y).1 hx hy
  rw [← hu, Finset.sum_union hd, Finset.sum_image (fun _ _ _ _ he => hi he),
    Finset.sum_add_distrib]

theorem card_pairs : spaceSize n = 2 * P.points.card := by
  have hh := P.sum_pairs (fun _ => (1 : ℕ))
  simpa [spaceSize, mul_comm] using hh

theorem card_pred (hn : 1 ≤ n) : P.points.card = spaceSize (n - 1) := by
  have hc := P.card_pairs
  have hp : spaceSize n = 2 * spaceSize (n - 1) := by
    conv_lhs => rw [show n = n - 1 + 1 by omega]
    simp [spaceSize, pow_succ, mul_comm]
  omega

theorem sum_derivatives {m : ℕ} (H : VectorialMap n m) :
    (∑ x, H x) = ∑ x ∈ P.points, derivative H h x := by
  rw [P.sum_pairs H]
  apply Finset.sum_congr rfl
  intro x _
  exact add_comm _ _

theorem weight_pairs (g : BooleanFunction n) :
    weight (derivative g h) = 2 * (P.points.filter (fun x => derivative g h x = 1)).card := by
  classical
  have he := P.sum_pairs (fun x => if derivative g h x = 1 then (1 : ℕ) else 0)
  simp only [derivative_pair, Finset.sum_add_distrib, ← Finset.sum_filter,
    Finset.sum_const, smul_eq_mul, mul_one] at he
  unfold weight
  omega

theorem representatives_distinct (x : BinarySpace n) (hx : x ∈ P.points)
    (y : BinarySpace n) (hy : y ∈ P.points) : y ≠ x + h := by
  rintro rfl
  exact (P.mem_add x).1 hy hx

theorem derivative_injOn {Y : Type*} [AddCommMonoid Y] (F : BinarySpace n → Y)
    (hF : DerivativeBound F) (hh : h ≠ 0) : Set.InjOn (derivative F h) P.points := by
  intro x hx y hy he
  rcases (apn_iff_collision F).1 hF h hh x y he with he | he
  · exact he.symm
  · exact (P.representatives_distinct x hx y hy he).elim

theorem fiber_two {m : ℕ} (H : VectorialMap n m) (hh : h ≠ 0)
    (hi : Set.InjOn (derivative H h) P.points)
    (ho : ∀ y, ∃ x ∈ P.points, derivative H h x = y) (y : BinarySpace m) :
    (Finset.univ.filter (fun x => derivative H h x = y)).card = 2 := by
  classical
  obtain ⟨r, hr, hrv⟩ := ho y
  have hne : r ≠ r + h := by
    intro he
    exact hh (add_left_cancel (show r + h = r + 0 by simpa using he.symm))
  have he : Finset.univ.filter (fun x => derivative H h x = y) = {r, r + h} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hm : x ∈ P.points
      · exact Or.inl (hi hm hr (hx.trans hrv.symm))
      · right
        have hx' := hi ((P.mem_add x).2 hm) hr
          ((derivative_pair H h x).trans (hx.trans hrv.symm))
        simpa using congrArg (fun z => z + h) hx'
    · rintro (rfl | rfl)
      · exact hrv
      · exact (derivative_pair H h r).trans hrv
  rw [he, Finset.card_pair hne]

end PairRepresentatives

theorem sum_binary_eq_zero {m : ℕ} (hm : 2 ≤ m) : (∑ y : BinarySpace m, y) = 0 := by
  classical
  ext i
  simp only [Finset.sum_apply, Pi.zero_apply]
  obtain ⟨j, hji⟩ : ∃ j : Fin m, j ≠ i := by
    by_cases hi : i = ⟨0, by omega⟩
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro he
      have := congrArg Fin.val (he.trans hi)
      change (1 : ℕ) = 0 at this
      omega
    · exact ⟨⟨0, by omega⟩, Ne.symm hi⟩
  let t : BinarySpace m := fun k => if k = j then 1 else 0
  have ht : t ≠ 0 := by
    intro he
    have := congrFun he j
    simp [t] at this
  apply Finset.sum_ninvolution (fun y => y + t)
  · intro y
    simp [t, Ne.symm hji]
  · intro y _ he
    exact ht (add_left_cancel (show y + t = y + 0 by simpa using he))
  · intro y
    exact Finset.mem_univ _
  · intro y
    exact binary_add_cancel_right y t

end
end APNLinearity.SmallSupport

open scoped BigOperators

namespace APNLinearity.SmallSupport
noncomputable section
open Sidon _root_.APNLinearity.Fourier

theorem derivative_H_injOn {n : ℕ} (g : BooleanFunction n) (H : VectorialMap n (n - 1))
    (hF : DerivativeBound (splitMap g H)) (h : BinarySpace n) (hh : h ≠ 0)
    (P : PairRepresentatives h) (T : Finset (BinarySpace n)) (hT : T ⊆ P.points)
    (hg : ∀ x ∈ T, derivative g h x = 0) : Set.InjOn (derivative H h) T := by
  intro x hx y hy he
  apply P.derivative_injOn (splitMap g H) hF hh (hT hx) (hT hy)
  apply Prod.ext
  · exact (hg x hx).trans (hg y hy).symm
  · exact he

theorem zero_derivative_sum : ∀ (n : ℕ), 3 ≤ n → ∀ (g : BooleanFunction n) (H : VectorialMap n (n - 1)),
    DerivativeBound (splitMap g H) → ∀ h, h ≠ 0 → (∀ x, derivative g h x = 0) →
      ∑ x, H x = 0 := by
  intro n hn g H hF h hh hg
  classical
  obtain ⟨P⟩ := exists_pair_representatives h hh
  have hi := derivative_H_injOn g H hF h hh P P.points (fun _ hx => hx) (fun x _ => hg x)
  have he : P.points.image (derivative H h) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injOn hi, P.card_pred (by omega), Finset.card_univ, card_binary]
  rw [P.sum_derivatives H, ← Finset.sum_image (f := fun z => z) hi, he]
  exact sum_binary_eq_zero (by omega)

theorem derivative_corrected {n m : ℕ} (g : BooleanFunction n) (H : VectorialMap n m)
    (σ : BinarySpace m) (h x : BinarySpace n) :
    derivative (fun z => H z + g z • σ) h x =
      derivative H h x + derivative g h x • σ := by
  simp only [derivative, add_smul]
  abel

/-- The unique changing pair replaces its value by the unique missing value. -/
theorem weight_two_derivative : ∀ (n : ℕ), 3 ≤ n → ∀ (g : BooleanFunction n) (H : VectorialMap n (n - 1)),
    DerivativeBound (splitMap g H) → ∀ h, h ≠ 0 → weight (derivative g h) = 2 →
      ∀ y : BinarySpace (n - 1),
        (Finset.univ.filter (fun x =>
          derivative (fun z => H z + g z • (∑ w, H w)) h x = y)).card = 2 := by
  intro n hn g H hF h hh hweight y
  classical
  obtain ⟨P⟩ := exists_pair_representatives h hh
  have hcard : (P.points.filter (fun x => derivative g h x = 1)).card = 1 := by
    have := P.weight_pairs g
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have ham : a ∈ P.points := by
    have : a ∈ P.points.filter (fun x => derivative g h x = 1) := by rw [ha]; simp
    exact (Finset.mem_filter.mp this).1
  have hag : derivative g h a = 1 := by
    have : a ∈ P.points.filter (fun x => derivative g h x = 1) := by rw [ha]; simp
    exact (Finset.mem_filter.mp this).2
  let T := P.points.erase a
  have hT : T ⊆ P.points := Finset.erase_subset _ _
  have hzero (x : BinarySpace n) (hx : x ∈ T) : derivative g h x = 0 := by
    rcases bit_eq_zero_or_one (derivative g h x) with he | he
    · exact he
    · have hm : x ∈ P.points.filter (fun z => derivative g h z = 1) :=
        Finset.mem_filter.mpr ⟨hT hx, he⟩
      rw [ha, Finset.mem_singleton] at hm
      exact ((Finset.mem_erase.mp hx).1 hm).elim
  have hi := derivative_H_injOn g H hF h hh P T hT hzero
  have htc : (Finset.univ : Finset (BinarySpace (n - 1))).card = T.card + 1 := by
    simp only [T, Finset.card_erase_of_mem ham, Finset.card_univ, card_binary,
      P.card_pred (by omega)]
    have := spaceSize_pos (n - 1)
    omega
  obtain ⟨r, ⟨_, hr⟩, hru⟩ := Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one
    hi (fun _ _ => Finset.mem_univ _) htc
  have himage : T.image (derivative H h) = Finset.univ.erase r := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hz he
      subst z
      exact hr hz
    · intro hz
      by_contra hm
      exact hz (hru z ⟨Finset.mem_univ _, hm⟩)
  have hsumT : (∑ x ∈ T, derivative H h x) = r := by
    rw [← Finset.sum_image (f := fun z => z) hi, himage]
    have he := Finset.sum_erase_add Finset.univ (fun z : BinarySpace (n - 1) => z) (Finset.mem_univ r)
    rw [sum_binary_eq_zero (by omega)] at he
    exact (binary_add_eq_zero_iff _ _).1 he
  let σ := ∑ x, H x
  have hsigma : σ = r + derivative H h a := by
    rw [show σ = ∑ x ∈ P.points, derivative H h x from P.sum_derivatives H,
      ← Finset.sum_erase_add P.points (derivative H h) ham, hsumT]
  let K : VectorialMap n (n - 1) := fun z => H z + g z • σ
  have hKa : derivative K h a = r := by
    rw [derivative_corrected, hag, one_smul, hsigma, add_comm r,
      binary_add_cancel_left]
  have hKT (x : BinarySpace n) (hx : x ∈ T) : derivative K h x = derivative H h x := by
    rw [derivative_corrected, hzero x hx, zero_smul, add_zero]
  have hKi : Set.InjOn (derivative K h) P.points := by
    intro x hx z hz he
    by_cases hxa : x = a
    · subst x
      by_cases hza : z = a
      · exact hza.symm
      · have hzT : z ∈ T := Finset.mem_erase.mpr ⟨hza, hz⟩
        rw [hKa, hKT z hzT] at he
        exact (hr (Finset.mem_image.mpr ⟨z, hzT, he.symm⟩)).elim
    · have hxT : x ∈ T := Finset.mem_erase.mpr ⟨hxa, hx⟩
      by_cases hza : z = a
      · subst z
        rw [hKT x hxT, hKa] at he
        exact (hr (Finset.mem_image.mpr ⟨x, hxT, he⟩)).elim
      · have hzT : z ∈ T := Finset.mem_erase.mpr ⟨hza, hz⟩
        rw [hKT x hxT, hKT z hzT] at he
        exact hi hxT hzT he
  have hKo (z : BinarySpace (n - 1)) : ∃ x ∈ P.points, derivative K h x = z := by
    by_cases hz : z = r
    · exact ⟨a, ham, hKa.trans hz.symm⟩
    · have hm : z ∈ T.image (derivative H h) := by rw [himage]; simp [hz]
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hm
      exact ⟨x, hT hx, (hKT x hx).trans he⟩
  exact P.fiber_two K hh hKi hKo y

end
end APNLinearity.SmallSupport

open scoped BigOperators

namespace APNLinearity.SmallSupport
noncomputable section
open _root_.APNLinearity.Fourier Sidon Components

theorem weight_zero_iff {n : ℕ} (g : BooleanFunction n) : weight g = 0 ↔ g = 0 := by
  classical
  constructor
  · intro hg
    have he : Finset.univ.filter (fun x => g x = 1) = ∅ := Finset.card_eq_zero.mp hg
    ext x
    rcases bit_eq_zero_or_one (g x) with hx | hx
    · exact hx
    · have hm : x ∈ Finset.univ.filter (fun x => g x = 1) := by simp [hx]
      rw [he] at hm
      exact (Finset.notMem_empty x hm).elim
  · rintro rfl
    simp [weight]

theorem weight_one_indicator {n : ℕ} (g : BooleanFunction n) (hg : weight g = 1) :
    ∃ a, g = indicator {a} := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hg
  refine ⟨a, ?_⟩
  have hm (x : BinarySpace n) : g x = 1 ↔ x = a := by
    have := Finset.ext_iff.mp ha x
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using this
  ext x
  by_cases hx : x = a
  · subst x
    simp [indicator, (hm a).2 rfl]
  · have hz : g x = 0 := (bit_eq_zero_or_one (g x)).resolve_right (mt (hm x).1 hx)
    simp [indicator, hx, hz]

theorem singleton_derivative_weight {n : ℕ} (a h : BinarySpace n) (hh : h ≠ 0) :
    weight (derivative (indicator {a}) h) = 2 := by
  classical
  have hne : a ≠ a + h := by
    intro he
    exact hh (add_left_cancel (show a + h = a + 0 by simpa using he.symm))
  have hmem (x : BinarySpace n) : x + h = a ↔ x = a + h := by
    constructor <;> intro he
    · simpa using congrArg (fun z => z + h) he
    · simp [he]
  have he : Finset.univ.filter (fun x => derivative (indicator {a}) h x = 1) = {a, a + h} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, derivative, indicator,
      Finset.mem_insert, Finset.mem_singleton, hmem]
    by_cases hx : x = a
    · subst x
      simp [hne]
    · by_cases hy : x = a + h
      · simp [hy, hne.symm]
      · simp [hx, hy]
  unfold weight
  rw [he, Finset.card_pair hne]

theorem exclude_distance_one : ∀ (n : ℕ), 3 ≤ n → ∀ (F : VectorialFunction n), IsAPN F →
    ∀ b, b ≠ 0 → ∀ a c,
      hammingDistance (component F b) (affineBoolean a c) ≠ 1 := by
  intro n hn F hF b hb a c hd
  classical
  obtain ⟨H, hH⟩ := Normalization.normalize_component n (by omega) F hF b hb a c
  let g := component F b + affineBoolean a c
  have hg : weight g = 1 := by rwa [distance_eq_weight] at hd
  obtain ⟨r, hr⟩ := weight_one_indicator g hg
  let K : VectorialMap n (n - 1) := fun z => H z + g z • (∑ w, H w)
  have hK : DerivativeBound K := by
    intro h y hh
    have hw : weight (derivative g h) = 2 := by rw [hr]; exact singleton_derivative_weight r h hh
    have he := weight_two_derivative n hn g H hH h hh hw y
    convert le_of_eq he using 1
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, K, derivative]
  exact projected_graph_obstruction n hn K ((apn_iff_sidon_graph n (n - 1) K).1 hK)

theorem linearity_le_sub_four : ∀ (n : ℕ), 3 ≤ n → ∀ (F : VectorialFunction n), IsAPN F →
    (linearity F : ℝ) ≤ (spaceSize n : ℝ) - 4 := by
  intro n hn F hF
  obtain ⟨b, hb, a, c, hd⟩ := distance_attained n (by omega) F
  have hz : hammingDistance (component F b) (affineBoolean a c) ≠ 0 := by
    intro hz
    rw [distance_eq_weight, weight_zero_iff] at hz
    have hf : component F b = affineBoolean a c := by
      ext x
      have he := congrFun hz x
      have := congrArg (fun z : Bit => z + affineBoolean a c x) he
      simpa [add_assoc] using this
    exact no_affine_component n hn F hF b hb ⟨a, c, hf⟩
  have ho := exclude_distance_one n hn F hF b hb a c
  have ht : 2 ≤ nonlinearity F := by omega
  have hlin := linearity_distance n (by omega) F
  have hlinR : 2 * (nonlinearity F : ℝ) + linearity F = spaceSize n := by exact_mod_cast hlin
  have hr : (2 : ℝ) ≤ nonlinearity F := by exact_mod_cast ht
  linarith

end
end APNLinearity.SmallSupport
