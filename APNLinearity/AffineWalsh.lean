module

public import APNLinearity.OddLinearity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.Spectrum
noncomputable section
open Sidon _root_.APNLinearity.Fourier
attribute [local instance] Classical.propDecidable

abbrev IndexSpace (n : ℕ) := BinarySpace n × BinarySpace n

def indexDot {n : ℕ} (u z : IndexSpace n) : Bit := binaryDot u.1 z.1 + binaryDot u.2 z.2

@[simp] theorem indexDot_add_left {n : ℕ} (u v z : IndexSpace n) :
    indexDot (u + v) z = indexDot u z + indexDot v z := by
  simp only [indexDot, Prod.fst_add, Prod.snd_add, dot_add_left]
  ring

@[simp] theorem indexDot_add_right {n : ℕ} (u z w : IndexSpace n) :
    indexDot u (z + w) = indexDot u z + indexDot u w := by
  simp only [indexDot, Prod.fst_add, Prod.snd_add, dot_add_right]
  ring

@[simp] theorem indexDot_zero_left {n : ℕ} (z : IndexSpace n) : indexDot 0 z = 0 := by
  simp [indexDot]

@[simp] theorem indexDot_zero_right {n : ℕ} (z : IndexSpace n) : indexDot z 0 = 0 := by
  simp [indexDot]

theorem indexDot_comm {n : ℕ} (u z : IndexSpace n) : indexDot u z = indexDot z u := by
  simp only [indexDot, dot_comm]

@[simp] theorem index_add_self {n : ℕ} (u : IndexSpace n) : u + u = 0 := by ext <;> simp

@[simp] theorem index_neg_eq {n : ℕ} (u : IndexSpace n) : -u = u := by
  exact neg_eq_of_add_eq_zero_left (index_add_self u)

@[simp] theorem index_sub_eq_add {n : ℕ} (u v : IndexSpace n) : u - v = u + v := by
  rw [sub_eq_add_neg, index_neg_eq]

@[simp] theorem index_add_cancel {n : ℕ} (u v : IndexSpace n) : u + v + v = u := by
  rw [add_assoc, index_add_self, add_zero]

def subspacePoints {n : ℕ} (L : Submodule Bit (IndexSpace n)) : Finset (IndexSpace n) := by
  classical
  exact Finset.univ.filter (fun u => u ∈ L)

@[simp] theorem mem_subspacePoints {n : ℕ} (L : Submodule Bit (IndexSpace n)) (u : IndexSpace n) :
    u ∈ subspacePoints L ↔ u ∈ L := by
  classical
  simp [subspacePoints]

theorem subspacePoints_card {n : ℕ} (L : Submodule Bit (IndexSpace n)) :
    (subspacePoints L).card = 2 ^ Module.finrank Bit L := by
  classical
  let : Fintype L := Fintype.ofFinite L
  have hc : (subspacePoints L).card = Fintype.card L :=
    (Fintype.card_subtype (fun u : IndexSpace n => u ∈ L)).symm
  rw [hc, Module.card_eq_pow_finrank (K := Bit), ZMod.card]

def annihilator {n : ℕ} (L : Submodule Bit (IndexSpace n)) : Submodule Bit (IndexSpace n) where
  carrier := {z | ∀ u ∈ L, indexDot u z = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy u hu; rw [indexDot_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' := by
    intro c x hx
    rcases bit_eq_zero_or_one c with rfl | rfl
    · intro u _
      simp
    · simpa using hx

theorem subspace_character_sum {n : ℕ} (L : Submodule Bit (IndexSpace n)) (z : IndexSpace n) :
    (∑ u ∈ subspacePoints L, productCharacter u z) =
      if z ∈ annihilator L then ((subspacePoints L).card : ℤ) else 0 := by
  classical
  by_cases hz : z ∈ annihilator L
  · rw [ite_eq_left hz]
    have hc (u : IndexSpace n) (hu : u ∈ subspacePoints L) : productCharacter u z = 1 := by
      change bitSign (indexDot u z) = 1
      rw [hz u ((mem_subspacePoints L u).1 hu), sign_zero]
    simp only [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, mul_one]
  · rw [ite_eq_right hz]
    have ht : ∃ t ∈ L, indexDot t z = 1 := by
      by_contra he
      apply hz
      intro t ht
      exact (bit_eq_zero_or_one _).resolve_right (fun hh => he ⟨t, ht, hh⟩)
    obtain ⟨t, ht, htz⟩ := ht
    have hsum : (∑ u ∈ subspacePoints L, productCharacter (u + t) z) =
        ∑ u ∈ subspacePoints L, productCharacter u z := by
      apply Finset.sum_bij (fun u _ => u + t)
      · intro u hu
        exact (mem_subspacePoints L _).2 (L.add_mem ((mem_subspacePoints L _).1 hu) ht)
      · intro u _ v _ he
        exact add_right_cancel he
      · intro u hu
        refine ⟨u + t, (mem_subspacePoints L _).2 (L.add_mem ((mem_subspacePoints L _).1 hu) ht), ?_⟩
        exact index_add_cancel u t
      · intro _ _
        rfl
    have hc (u : IndexSpace n) : productCharacter (u + t) z = -productCharacter u z := by
      change bitSign (indexDot (u + t) z) = -bitSign (indexDot u z)
      rw [indexDot_add_left, htz, sign_add, sign_one, mul_neg_one]
    simp only [hc, Finset.sum_neg_distrib] at hsum
    omega

theorem annihilator_card {n : ℕ} (L : Submodule Bit (IndexSpace n)) :
    (subspacePoints (annihilator L)).card * (subspacePoints L).card = spaceSize n ^ 2 := by
  classical
  have h : ((subspacePoints (annihilator L)).card : ℤ) * (subspacePoints L).card =
      (spaceSize n : ℤ) ^ 2 := by
    calc
      _ = ∑ z : IndexSpace n, ∑ u ∈ subspacePoints L, productCharacter u z := by
        simp_rw [subspace_character_sum]
        simp [subspacePoints, ← Finset.sum_filter]
      _ = ∑ u ∈ subspacePoints L, ∑ z : IndexSpace n, productCharacter u z := Finset.sum_comm
      _ = (spaceSize n : ℤ) ^ 2 := by
        have hc (u z : IndexSpace n) : productCharacter u z = productCharacter z u := by
          exact congrArg bitSign (indexDot_comm u z)
        have hs (u : IndexSpace n) : (∑ z : IndexSpace n, productCharacter u z) =
            if u = 0 then (spaceSize n : ℤ) * spaceSize n else 0 := by
          calc
            _ = ∑ z : IndexSpace n, productCharacter z u := Finset.sum_congr rfl (fun z _ => hc u z)
            _ = _ := product_orthogonality u
        simp_rw [hs]
        simp [pow_two]
  exact_mod_cast h

theorem annihilator_finrank {n : ℕ} (L : Submodule Bit (IndexSpace n)) :
    Module.finrank Bit (annihilator L) + Module.finrank Bit L = n + n := by
  have hc := annihilator_card L
  rw [subspacePoints_card, subspacePoints_card, ← pow_add] at hc
  simp only [spaceSize, pow_two, ← pow_add] at hc
  exact Nat.pow_right_injective (by decide) hc

def vertical (n : ℕ) : Submodule Bit (IndexSpace n) := (LinearMap.fst Bit (BinarySpace n) (BinarySpace n)).ker

@[simp] theorem mem_vertical {n : ℕ} (u : IndexSpace n) : u ∈ vertical n ↔ u.1 = 0 := Iff.rfl

theorem vertical_finrank (n : ℕ) : Module.finrank Bit (vertical n) = n := by
  let e : vertical n ≃ₗ[Bit] BinarySpace n :=
    { toFun := fun u => u.val.2
      invFun := fun y => ⟨(0, y), rfl⟩
      left_inv := by intro u; apply Subtype.ext; exact Prod.ext u.property.symm rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  simpa [BinarySpace, Module.finrank_fintype_fun_eq_card] using e.finrank_eq

theorem annihilator_vertical_card {n : ℕ} (L : Submodule Bit (IndexSpace n)) :
    spaceSize n ≤ (subspacePoints (annihilator L ⊓ vertical n)).card * (subspacePoints L).card := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (annihilator L) (vertical n)
  have hle := (annihilator L ⊔ vertical n).finrank_le
  have ha := annihilator_finrank L
  rw [vertical_finrank] at hd
  have hg : Module.finrank Bit (IndexSpace n) = n + n := by
    simp [IndexSpace, BinarySpace, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  rw [hg] at hle
  have hb : n ≤ Module.finrank Bit ↥(annihilator L ⊓ vertical n) + Module.finrank Bit L := by omega
  rw [subspacePoints_card, subspacePoints_card, ← pow_add]
  exact Nat.pow_le_pow_right (by decide) hb

end
end APNLinearity.Spectrum

open scoped BigOperators

namespace APNLinearity.Spectrum
noncomputable section
open Sidon _root_.APNLinearity.Fourier
attribute [local instance] Classical.propDecidable

def affinePoints {n : ℕ} (U : AffineSubspace Bit (IndexSpace n)) : Finset (IndexSpace n) := by
  classical
  exact Finset.univ.filter (fun u => u ∈ U)

@[simp] theorem mem_affinePoints {n : ℕ} (U : AffineSubspace Bit (IndexSpace n)) (u : IndexSpace n) :
    u ∈ affinePoints U ↔ u ∈ U := by
  classical
  simp [affinePoints]

def linearHull {n : ℕ} (U : AffineSubspace Bit (IndexSpace n)) : Submodule Bit (IndexSpace n) :=
  Submodule.span Bit (U : Set (IndexSpace n))

theorem affine_add_direction {n : ℕ} (U : AffineSubspace Bit (IndexSpace n))
    (p : IndexSpace n) (hp : p ∈ U) (x : IndexSpace n) : x + p ∈ U.direction ↔ x ∈ U := by
  have hh := U.vadd_mem_iff_mem_direction (x + p) hp
  simpa only [vadd_eq_add, index_add_cancel] using hh.symm

theorem affinePoints_image {n : ℕ} (U : AffineSubspace Bit (IndexSpace n))
    (p : IndexSpace n) (hp : p ∈ U) :
    affinePoints U = (subspacePoints U.direction).image (fun x => x + p) := by
  classical
  ext x
  rw [mem_affinePoints, Finset.mem_image]
  constructor
  · intro hx
    exact ⟨x + p, (mem_subspacePoints _ _).2 ((affine_add_direction U p hp x).2 hx),
      index_add_cancel x p⟩
  · rintro ⟨u, hu, rfl⟩
    exact (U.vadd_mem_iff_mem_direction u hp).2 ((mem_subspacePoints _ _).1 hu)

theorem affinePoints_card {n : ℕ} (U : AffineSubspace Bit (IndexSpace n))
    (hU : ∃ p, p ∈ U) : (affinePoints U).card = 2 ^ Module.finrank Bit U.direction := by
  classical
  obtain ⟨p, hp⟩ := hU
  rw [affinePoints_image U p hp, Finset.card_image_of_injective _ (add_left_injective p),
    subspacePoints_card]

theorem direction_le_linearHull {n : ℕ} (U : AffineSubspace Bit (IndexSpace n))
    (p : IndexSpace n) (hp : p ∈ U) : U.direction ≤ linearHull U := by
  intro x hx
  have hxU : x + p ∈ U := (U.vadd_mem_iff_mem_direction x hp).2 hx
  have hxL : x + p ∈ linearHull U := Submodule.subset_span hxU
  have hpL : p ∈ linearHull U := Submodule.subset_span hp
  simpa only [index_add_cancel] using (linearHull U).add_mem hxL hpL

theorem linearHull_eq_sup {n : ℕ} (U : AffineSubspace Bit (IndexSpace n))
    (p : IndexSpace n) (hp : p ∈ U) :
    linearHull U = U.direction ⊔ Submodule.span Bit {p} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    change x ∈ (U.direction ⊔ Submodule.span Bit ({p} : Set (IndexSpace n)))
    have hxd : x + p ∈ U.direction := (affine_add_direction U p hp x).2 hx
    have hsum := (U.direction ⊔ Submodule.span Bit {p}).add_mem
      (Submodule.mem_sup_left hxd) (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton p)))
    simpa only [index_add_cancel] using hsum
  · apply sup_le
    · exact direction_le_linearHull U p hp
    · apply Submodule.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact Submodule.subset_span hp

theorem linearHull_finrank {n : ℕ} (U : AffineSubspace Bit (IndexSpace n)) (hU : ∃ p, p ∈ U) :
    Module.finrank Bit (linearHull U) =
      if (0 : IndexSpace n) ∈ U then Module.finrank Bit U.direction else Module.finrank Bit U.direction + 1 := by
  by_cases h0 : (0 : IndexSpace n) ∈ U
  · rw [ite_eq_left h0, linearHull_eq_sup U 0 h0]
    rw [Submodule.span_zero_singleton, sup_bot_eq]
  · rw [ite_eq_right h0]
    obtain ⟨p, hp⟩ := hU
    have hpd : p ∉ U.direction := by
      intro hd
      have := (U.vadd_mem_iff_mem_direction p hp).2 hd
      rw [vadd_eq_add, index_add_self] at this
      exact h0 this
    rw [linearHull_eq_sup U p hp, Submodule.finrank_sup_span_singleton hpd]

theorem linearHull_card {n : ℕ} (U : AffineSubspace Bit (IndexSpace n)) (hU : ∃ p, p ∈ U) :
    (subspacePoints (linearHull U)).card =
      if (0 : IndexSpace n) ∈ U then (affinePoints U).card else 2 * (affinePoints U).card := by
  rw [subspacePoints_card, linearHull_finrank U hU, affinePoints_card U hU]
  split_ifs <;> simp [pow_succ, mul_comm]

theorem mem_annihilator_linearHull {n : ℕ} (U : AffineSubspace Bit (IndexSpace n)) (z : IndexSpace n) :
    z ∈ annihilator (linearHull U) ↔ ∀ u ∈ U, indexDot u z = 0 := by
  constructor
  · intro hz u hu
    exact hz u (Submodule.subset_span hu)
  · intro hz u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact hz x hx
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => rcases bit_eq_zero_or_one a with rfl | rfl <;> simp [hx]

theorem affine_character_sum {n : ℕ} (U : AffineSubspace Bit (IndexSpace n))
    (p : IndexSpace n) (hp : p ∈ U) (z : IndexSpace n) :
    (∑ u ∈ affinePoints U, productCharacter u z) =
      productCharacter p z * ∑ u ∈ subspacePoints U.direction, productCharacter u z := by
  classical
  rw [affinePoints_image U p hp, Finset.sum_image (fun _ _ _ _ he => add_right_cancel he), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  change bitSign (indexDot (u + p) z) = bitSign (indexDot p z) * bitSign (indexDot u z)
  rw [indexDot_add_left, sign_add, mul_comm]

/-- Display (4.1): only the annihilator of the linear span contributes positively. -/
theorem affine_character_bound {n : ℕ} (U : AffineSubspace Bit (IndexSpace n))
    (hU : ∃ p, p ∈ U) (z : IndexSpace n) :
    (∑ u ∈ affinePoints U, productCharacter u z) ≤
      if z ∈ annihilator (linearHull U) then ((affinePoints U).card : ℤ) else 0 := by
  classical
  obtain ⟨p, hp⟩ := hU
  by_cases hz : z ∈ annihilator (linearHull U)
  · rw [ite_eq_left hz]
    have he (u : IndexSpace n) (hu : u ∈ affinePoints U) : productCharacter u z = 1 := by
      change bitSign (indexDot u z) = 1
      rw [(mem_annihilator_linearHull U z).1 hz u ((mem_affinePoints U u).1 hu), sign_zero]
    simp only [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul, mul_one, le_refl]
  · rw [ite_eq_right hz, affine_character_sum U p hp z, subspace_character_sum]
    by_cases hd : z ∈ annihilator U.direction
    · rw [ite_eq_left hd]
      have hpz : indexDot p z = 1 := by
        apply (bit_eq_zero_or_one _).resolve_left
        intro he
        apply hz
        apply (mem_annihilator_linearHull U z).2
        intro u hu
        have hh := hd (u + p) ((affine_add_direction U p hp u).2 hu)
        rw [indexDot_add_left, he, add_zero] at hh
        exact hh
      change bitSign (indexDot p z) * _ ≤ 0
      rw [hpz, sign_one]
      omega
    · rw [ite_eq_right hd, mul_zero]

end
end APNLinearity.Spectrum

open scoped BigOperators

namespace APNLinearity.Spectrum
noncomputable section
open Sidon _root_.APNLinearity.Fourier
attribute [local instance] Classical.propDecidable

theorem walshAt_character {n : ℕ} (F : VectorialFunction n) (u : IndexSpace n) :
    walshAt F u = ∑ x, productCharacter u (x, F x) := by
  simp only [walshAt, walsh, component, productCharacter, add_comm]

theorem walshAt_square {n : ℕ} (F : VectorialFunction n) (u : IndexSpace n) :
    walshAt F u ^ 2 = ∑ h, ∑ x, productCharacter u (h, derivative F h x) := by
  rw [walshAt_character, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ x, ∑ h, productCharacter u (h, derivative F h x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← sum_translate (fun y => productCharacter u (x, F x) * productCharacter u (y, F y)) x]
      apply Finset.sum_congr rfl
      intro h _
      rw [← product_character_add]
      congr 1
      apply Prod.ext
      · simp [add_comm]
      · simp [derivative, add_comm]
    _ = _ := Finset.sum_comm

theorem walshAt_square_off_diagonal {n : ℕ} (F : VectorialFunction n) (u : IndexSpace n) :
    walshAt F u ^ 2 = (spaceSize n : ℤ) +
      ∑ h ∈ (Finset.univ.erase (0 : BinarySpace n)), ∑ x, productCharacter u (h, derivative F h x) := by
  classical
  have hs := Finset.sum_erase_add Finset.univ
    (fun h => ∑ x, productCharacter u (h, derivative F h x)) (Finset.mem_univ (0 : BinarySpace n))
  rw [← walshAt_square] at hs
  have hz : (∑ x, productCharacter u (0, derivative F 0 x)) = (spaceSize n : ℤ) := by
    simp [derivative, productCharacter, spaceSize]
  rw [hz] at hs
  omega

theorem affine_walsh_expansion {n : ℕ} (F : VectorialFunction n) (U : AffineSubspace Bit (IndexSpace n)) :
    (∑ u ∈ affinePoints U, walshAt F u ^ 2) =
      ((affinePoints U).card : ℤ) * spaceSize n +
        ∑ h ∈ (Finset.univ.erase (0 : BinarySpace n)), ∑ x,
          ∑ u ∈ affinePoints U, productCharacter u (h, derivative F h x) := by
  classical
  simp_rw [walshAt_square_off_diagonal]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_comm]

/-- Each graph-pair sum has at most two ordered representatives. -/
theorem derivative_sum_bound {n : ℕ} (F : VectorialFunction n) (hF : IsAPN F)
    (h : BinarySpace n) (hh : h ≠ 0) (a : BinarySpace n → ℤ) (ha : ∀ y, 0 ≤ a y) :
    (∑ x, a (derivative F h x)) ≤ 2 * ∑ y, a y := by
  classical
  have hp := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := derivative F h) (fun _ _ => Finset.mem_univ _) (fun x => a (derivative F h x))
  rw [← hp, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  have he : (∑ x ∈ Finset.univ.filter (fun x => derivative F h x = y), a (derivative F h x)) =
      ((Finset.univ.filter (fun x => derivative F h x = y)).card : ℤ) * a y := by
    calc
      _ = ∑ _x ∈ Finset.univ.filter (fun x => derivative F h x = y), a y := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = _ := by simp
  rw [he]
  have hc : (Finset.univ.filter (fun x => derivative F h x = y)).card ≤ 2 := by
    convert hF h y hh using 1
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, derivative]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (ha y)

def outsidePoints {n : ℕ} (H : Submodule Bit (IndexSpace n)) : Finset (IndexSpace n) := by
  classical
  exact Finset.univ.filter (fun u => u ∈ H ∧ u.1 ≠ 0)

theorem outsidePoints_card {n : ℕ} (H : Submodule Bit (IndexSpace n)) :
    (subspacePoints H).card = (subspacePoints (H ⊓ vertical n)).card + (outsidePoints H).card := by
  classical
  have he := Finset.card_filter_add_card_filter_not (s := subspacePoints H) (fun u : IndexSpace n => u.1 = 0)
  simpa [subspacePoints, outsidePoints, Finset.filter_filter] using he.symm

theorem sum_outside {n : ℕ} (H : Submodule Bit (IndexSpace n)) (c : ℤ) :
    (∑ h ∈ (Finset.univ.erase (0 : BinarySpace n)), ∑ y : BinarySpace n, if (h, y) ∈ H then c else 0) =
      c * (outsidePoints H).card := by
  classical
  have he : outsidePoints H =
      ((Finset.univ.erase (0 : BinarySpace n)) ×ˢ (Finset.univ : Finset (BinarySpace n))).filter (fun u => u ∈ H) := by
    ext u
    simp [outsidePoints, and_comm]
  rw [← Finset.sum_product (Finset.univ.erase (0 : BinarySpace n)) Finset.univ
    (fun u : IndexSpace n => if u ∈ H then c else 0), ← Finset.sum_filter, ← he]
  simp [mul_comm]

theorem affine_walsh_pair_bound {n : ℕ} (F : VectorialFunction n) (hF : IsAPN F)
    (U : AffineSubspace Bit (IndexSpace n)) (hU : ∃ p, p ∈ U) :
    (∑ u ∈ affinePoints U, walshAt F u ^ 2) ≤
      ((affinePoints U).card : ℤ) * spaceSize n +
        2 * (affinePoints U).card * (outsidePoints (annihilator (linearHull U))).card := by
  classical
  rw [affine_walsh_expansion]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ h ∈ (Finset.univ.erase (0 : BinarySpace n)),
        ∑ y : BinarySpace n, if (h, y) ∈ annihilator (linearHull U) then 2 * ((affinePoints U).card : ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro h hh
      calc
        _ ≤ ∑ x, if (h, derivative F h x) ∈ annihilator (linearHull U)
            then ((affinePoints U).card : ℤ) else 0 :=
          Finset.sum_le_sum (fun x _ => affine_character_bound U hU (h, derivative F h x))
        _ ≤ 2 * ∑ y : BinarySpace n, if (h, y) ∈ annihilator (linearHull U)
            then ((affinePoints U).card : ℤ) else 0 :=
          derivative_sum_bound F hF h (Finset.mem_erase.mp hh).1 _ (by intro y; split_ifs <;> positivity)
        _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; split_ifs <;> simp
    _ = _ := sum_outside _ _

end
end APNLinearity.Spectrum

open scoped BigOperators

namespace APNLinearity.Spectrum
noncomputable section
open Sidon _root_.APNLinearity.Fourier
attribute [local instance] Classical.propDecidable

theorem affine_walsh_bound_int {n : ℕ} (F : VectorialFunction n) (hF : IsAPN F)
    (U : AffineSubspace Bit (IndexSpace n)) (hU : ∃ p, p ∈ U) :
    (∑ u ∈ (affinePoints U).erase 0, walshAt F u ^ 2) ≤
      if (0 : IndexSpace n) ∈ U then
        (spaceSize n : ℤ) ^ 2 + (((affinePoints U).card : ℤ) - 2) * spaceSize n
      else (spaceSize n : ℤ) ^ 2 + (((affinePoints U).card : ℤ) - 1) * spaceSize n := by
  classical
  let L := linearHull U
  let H := annihilator L
  have hc : ((subspacePoints H).card : ℤ) * (subspacePoints L).card = (spaceSize n : ℤ) ^ 2 := by
    exact_mod_cast annihilator_card L
  have hi : (spaceSize n : ℤ) ≤
      ((subspacePoints (H ⊓ vertical n)).card : ℤ) * (subspacePoints L).card := by
    exact_mod_cast annihilator_vertical_card L
  have hsplit : ((subspacePoints H).card : ℤ) * (subspacePoints L).card =
      ((subspacePoints (H ⊓ vertical n)).card : ℤ) * (subspacePoints L).card +
      ((outsidePoints H).card : ℤ) * (subspacePoints L).card := by
    rw [outsidePoints_card H, Nat.cast_add, add_mul]
  have hoff : ((outsidePoints H).card : ℤ) * (subspacePoints L).card ≤
      (spaceSize n : ℤ) ^ 2 - spaceSize n := by linarith
  have hb := affine_walsh_pair_bound F hF U hU
  have hcard := linearHull_card U hU
  by_cases h0 : (0 : IndexSpace n) ∈ U
  · rw [ite_eq_left h0] at hcard ⊢
    change (subspacePoints L).card = (affinePoints U).card at hcard
    rw [hcard] at hoff
    have hsum := Finset.sum_erase_add (affinePoints U) (fun u => walshAt F u ^ 2)
      ((mem_affinePoints U 0).2 h0)
    have hzero : walshAt F 0 = (spaceSize n : ℤ) := by simp [walshAt, walsh_zero_component]
    rw [hzero] at hsum
    change _ ≤ ((affinePoints U).card : ℤ) * spaceSize n + 2 * (affinePoints U).card * (outsidePoints H).card at hb
    nlinarith
  · rw [ite_eq_right h0] at hcard ⊢
    change (subspacePoints L).card = 2 * (affinePoints U).card at hcard
    rw [hcard, Nat.cast_mul, Nat.cast_ofNat] at hoff
    rw [Finset.erase_eq_of_notMem (by simpa only [mem_affinePoints] using h0)]
    change _ ≤ ((affinePoints U).card : ℤ) * spaceSize n + 2 * (affinePoints U).card * (outsidePoints H).card at hb
    nlinarith

theorem affine_walsh_bound : ∀ (n : ℕ), 4 ≤ n → ∀ (F : VectorialFunction n), IsAPN F →
    ∀ U : AffineSubspace Bit (BinarySpace n × BinarySpace n), (∃ u, u ∈ U) →
      (∑ u ∈ (Finset.univ.filter (fun u => u ∈ U ∧ u ≠ 0)), (walshAt F u : ℝ) ^ 2) ≤
        if (0 : BinarySpace n × BinarySpace n) ∈ U then
          (spaceSize n : ℝ) ^ 2 +
            ((2 : ℝ) ^ Module.finrank Bit U.direction - 2) * (spaceSize n : ℝ)
        else (spaceSize n : ℝ) ^ 2 +
            ((2 : ℝ) ^ Module.finrank Bit U.direction - 1) * (spaceSize n : ℝ) := by
  intro n _ F hF U hU
  classical
  have h := affine_walsh_bound_int F hF U hU
  have he : (Finset.univ.filter (fun u : IndexSpace n => u ∈ U ∧ u ≠ 0)) =
      (affinePoints U).erase 0 := by
    ext u
    simp [affinePoints, and_comm]
  rw [he]
  have hc : ((affinePoints U).card : ℝ) = (2 : ℝ) ^ Module.finrank Bit U.direction := by
    exact_mod_cast affinePoints_card U hU
  by_cases h0 : (0 : IndexSpace n) ∈ U
  · rw [ite_eq_left h0] at h ⊢
    have hr : (∑ u ∈ (affinePoints U).erase 0, (walshAt F u : ℝ) ^ 2) ≤
        (spaceSize n : ℝ) ^ 2 + (((affinePoints U).card : ℝ) - 2) * spaceSize n := by exact_mod_cast h
    rwa [hc] at hr
  · rw [ite_eq_right h0] at h ⊢
    have hr : (∑ u ∈ (affinePoints U).erase 0, (walshAt F u : ℝ) ^ 2) ≤
        (spaceSize n : ℝ) ^ 2 + (((affinePoints U).card : ℝ) - 1) * spaceSize n := by exact_mod_cast h
    rwa [hc] at hr

end
end APNLinearity.Spectrum
