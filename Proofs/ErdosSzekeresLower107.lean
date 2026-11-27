module
/-
Copyright 2026 Ellweb3.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib

/-!
# The Erdős–Szekeres lower bound `2^(n-2) + 1 ≤ f(n)`

For every `n ≥ 3` and every `N ≤ 2^(n-2)` we build `N` points in the plane, no three on a line,
with no `n` points in convex position. This is the construction of Erdős and Szekeres,
*On some extremum problems in elementary geometry*, Ann. Univ. Sci. Budapest. Eötvös Sect. Math.
3–4 (1960/61), 53–62.

* A *cup* is a set of points whose triples, read from left to right, all turn left; a *cap* is a
  set whose triples all turn right.
* `exists_far`: a finite set `B` moved by `(s, s²)` for large `s` lies to the right of a finite
  set `A`, every chord from `A` to the moved `B` is steeper than every chord inside the moved `B`,
  and every chord from `A` to the moved `B` turns left after every chord inside `A`.
* Gluing two sets this way, a cup meeting `A` keeps at most one point outside `A`, and a cap
  meeting the moved `B` keeps at most one point of `A`.
* `exists_block`: for all `a b`, a set of `C(a+b, a)` points with no cup of more than `a + 1`
  points and no cap of more than `b + 1` points (the recursion `C(a+b,a) = C(a+b-1,a-1) +
  C(a+b-1,a)`).
* `exists_cup_cap_split`: the points of a convex polygon with distinct `x`-coordinates split
  into a cup and a cap that share the leftmost and the rightmost point.
* Gluing the blocks of sizes `C(n-2, 0), …, C(n-2, n-2)` one after another gives `2^(n-2)`
  points with no convex `n`-gon.
-/

@[expose] public section

noncomputable section

open Filter

namespace Erdos107Lower

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ### Orientation -/

/-- Twice the signed area of the triangle `a b c`: positive when `c` lies to the left of the
directed line `a → b`. -/
def ls (a b c : ℝ²) : ℝ := (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

lemma ls_swap12 (a b c : ℝ²) : ls b a c = -ls a b c := by unfold ls; ring
lemma ls_swap23 (a b c : ℝ²) : ls a c b = -ls a b c := by unfold ls; ring
lemma ls_cycle (a b c : ℝ²) : ls b c a = ls a b c := by unfold ls; ring

lemma ls_add (a b c t : ℝ²) : ls (a + t) (b + t) (c + t) = ls a b c := by
  unfold ls; simp only [PiLp.add_apply]; ring

/-- Points with pairwise distinct `x`-coordinates. -/
def XInj (S : Finset ℝ²) : Prop := ∀ p ∈ S, ∀ q ∈ S, p 0 = q 0 → p = q

/-- No three points of `S`, read from left to right, are collinear. -/
def GenPos (S : Finset ℝ²) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p 0 < q 0 → q 0 < r 0 → ls p q r ≠ 0

/-- A cup: every triple, read from left to right, turns left. -/
def IsCup (C : Finset ℝ²) : Prop :=
  ∀ p ∈ C, ∀ q ∈ C, ∀ r ∈ C, p 0 < q 0 → q 0 < r 0 → 0 < ls p q r

/-- A cap: every triple, read from left to right, turns right. -/
def IsCap (C : Finset ℝ²) : Prop :=
  ∀ p ∈ C, ∀ q ∈ C, ∀ r ∈ C, p 0 < q 0 → q 0 < r 0 → ls p q r < 0

/-- Every cup inside `S` has at most `k` points. -/
def CupBound (k : ℕ) (S : Finset ℝ²) : Prop := ∀ C ⊆ S, IsCup C → C.card ≤ k

/-- Every cap inside `S` has at most `k` points. -/
def CapBound (k : ℕ) (S : Finset ℝ²) : Prop := ∀ C ⊆ S, IsCap C → C.card ≤ k

/-- Every convex independent subset of `S` has at most `m` points. -/
def ConvBound (m : ℕ) (S : Finset ℝ²) : Prop :=
  ∀ P ⊆ S, (∀ a ∈ (P : Set ℝ²), a ∉ convexHull ℝ ((P : Set ℝ²) \ {a})) → P.card ≤ m

lemma IsCup.mono {C D : Finset ℝ²} (h : IsCup C) (hD : D ⊆ C) : IsCup D :=
  fun p hp q hq r hr => h p (hD hp) q (hD hq) r (hD hr)

lemma IsCap.mono {C D : Finset ℝ²} (h : IsCap C) (hD : D ⊆ C) : IsCap D :=
  fun p hp q hq r hr => h p (hD hp) q (hD hq) r (hD hr)

lemma XInj.mono {S T : Finset ℝ²} (h : XInj S) (hT : T ⊆ S) : XInj T :=
  fun p hp q hq => h p (hT hp) q (hT hq)

lemma GenPos.mono {S T : Finset ℝ²} (h : GenPos S) (hT : T ⊆ S) : GenPos T :=
  fun p hp q hq r hr => h p (hT hp) q (hT hq) r (hT hr)

/-! ### Translations -/

lemma mem_image_add {B : Finset ℝ²} {t x : ℝ²} (hx : x ∈ B.image (· + t)) : x - t ∈ B := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
  simpa using hb

lemma XInj.image_add {B : Finset ℝ²} (h : XInj B) (t : ℝ²) : XInj (B.image (· + t)) := by
  intro p hp q hq hpq
  have := h _ (mem_image_add hp) _ (mem_image_add hq) (by simp [PiLp.sub_apply, hpq])
  simpa using this

lemma GenPos.image_add {B : Finset ℝ²} (h : GenPos B) (t : ℝ²) : GenPos (B.image (· + t)) := by
  intro p hp q hq r hr hpq hqr
  have := h _ (mem_image_add hp) _ (mem_image_add hq) _ (mem_image_add hr)
    (by simp only [PiLp.sub_apply]; linarith) (by simp only [PiLp.sub_apply]; linarith)
  have e := ls_add (p - t) (q - t) (r - t) t
  simp only [sub_add_cancel] at e
  rw [e]; exact this

lemma card_image_sub (C : Finset ℝ²) (t : ℝ²) : (C.image (· - t)).card = C.card :=
  Finset.card_image_of_injective _ (sub_left_injective)

lemma isCup_image_sub {C : Finset ℝ²} (h : IsCup C) (t : ℝ²) : IsCup (C.image (· - t)) := by
  intro p hp q hq r hr hpq hqr
  obtain ⟨p, hp', rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨q, hq', rfl⟩ := Finset.mem_image.1 hq
  obtain ⟨r, hr', rfl⟩ := Finset.mem_image.1 hr
  simp only [PiLp.sub_apply] at hpq hqr
  have e := ls_add (p - t) (q - t) (r - t) t
  simp only [sub_add_cancel] at e
  rw [← e]; exact h p hp' q hq' r hr' (by linarith) (by linarith)

lemma isCap_image_sub {C : Finset ℝ²} (h : IsCap C) (t : ℝ²) : IsCap (C.image (· - t)) := by
  intro p hp q hq r hr hpq hqr
  obtain ⟨p, hp', rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨q, hq', rfl⟩ := Finset.mem_image.1 hq
  obtain ⟨r, hr', rfl⟩ := Finset.mem_image.1 hr
  simp only [PiLp.sub_apply] at hpq hqr
  have e := ls_add (p - t) (q - t) (r - t) t
  simp only [sub_add_cancel] at e
  rw [← e]; exact h p hp' q hq' r hr' (by linarith) (by linarith)

lemma image_sub_subset {C B : Finset ℝ²} {t : ℝ²} (hC : C ⊆ B.image (· + t)) :
    C.image (· - t) ⊆ B := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  exact mem_image_add (hC hy)

lemma CupBound.image_add {k : ℕ} {B : Finset ℝ²} (h : CupBound k B) (t : ℝ²) :
    CupBound k (B.image (· + t)) := by
  intro C hC hcup
  rw [← card_image_sub C t]
  exact h _ (image_sub_subset hC) (isCup_image_sub hcup t)

lemma CapBound.image_add {k : ℕ} {B : Finset ℝ²} (h : CapBound k B) (t : ℝ²) :
    CapBound k (B.image (· + t)) := by
  intro C hC hcap
  rw [← card_image_sub C t]
  exact h _ (image_sub_subset hC) (isCap_image_sub hcap t)

/-! ### Moving a set far up and to the right -/

/-- The point `(x, y)`. -/
def pt (x y : ℝ) : ℝ² := EuclideanSpace.single 0 x + EuclideanSpace.single 1 y

@[simp] lemma pt_zero (x y : ℝ) : pt x y 0 = x := by simp [pt]
@[simp] lemma pt_one (x y : ℝ) : pt x y 1 = y := by simp [pt]

lemma eventually_quad_lt {c : ℝ} (hc : 0 < c) (β γ : ℝ) :
    ∀ᶠ s : ℝ in atTop, β * s + γ < c * s ^ 2 := by
  filter_upwards [eventually_gt_atTop ((|β| + |γ|) / c + 1)] with s hs
  have h1 : 1 < s := by
    have : 0 ≤ (|β| + |γ|) / c := by positivity
    linarith
  have h2 : |β| + |γ| < c * s := by
    have : (|β| + |γ|) / c < s := by linarith
    rwa [div_lt_iff₀ hc, mul_comm] at this
  have hb := le_abs_self β
  have hg := le_abs_self γ
  have hb0 := abs_nonneg β
  have hg0 := abs_nonneg γ
  nlinarith

lemma eventually_imp {p : Prop} {q : ℝ → Prop} (h : p → ∀ᶠ s : ℝ in atTop, q s) :
    ∀ᶠ s : ℝ in atTop, p → q s := by
  by_cases hp : p
  · filter_upwards [h hp] with s hs _ using hs
  · exact Eventually.of_forall fun _ h' => absurd h' hp

/-- Moving `B` by `(s, s²)` for `s` large enough puts it to the right of `A`, makes every chord
from `A` to the moved `B` steeper than every chord inside the moved `B`, and makes it turn left
after every chord inside `A`. -/
lemma exists_far (A B : Finset ℝ²) : ∃ t : ℝ²,
    (∀ a ∈ A, ∀ b ∈ B, a 0 < b 0 + t 0) ∧
    (∀ a ∈ A, ∀ b ∈ B, ∀ b' ∈ B, b 0 < b' 0 → ls a (b + t) (b' + t) < 0) ∧
    (∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, a 0 < a' 0 → 0 < ls a a' (b + t)) := by
  have h1 : ∀ᶠ s : ℝ in atTop, ∀ a ∈ A, ∀ b ∈ B, a 0 < b 0 + s := by
    simp only [eventually_all_finset]
    intro a _ b _
    filter_upwards [eventually_gt_atTop (a 0 - b 0)] with s hs
    linarith
  have h2 : ∀ᶠ s : ℝ in atTop, ∀ a ∈ A, ∀ b ∈ B, ∀ b' ∈ B, b 0 < b' 0 →
      ls a (b + pt s (s ^ 2)) (b' + pt s (s ^ 2)) < 0 := by
    simp only [eventually_all_finset]
    intro a _ b _ b' _
    refine eventually_imp fun hbb' => ?_
    filter_upwards [eventually_quad_lt (sub_pos.2 hbb') (b' 1 - b 1)
      ((b 0 - a 0) * (b' 1 - b 1) - (b 1 - a 1) * (b' 0 - b 0))] with s hs
    have e : ls a (b + pt s (s ^ 2)) (b' + pt s (s ^ 2)) =
        (b' 1 - b 1) * s + ((b 0 - a 0) * (b' 1 - b 1) - (b 1 - a 1) * (b' 0 - b 0)) -
          (b' 0 - b 0) * s ^ 2 := by
      unfold ls; simp only [PiLp.add_apply, pt_zero, pt_one]; ring
    rw [e]; linarith
  have h3 : ∀ᶠ s : ℝ in atTop, ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, a 0 < a' 0 →
      0 < ls a a' (b + pt s (s ^ 2)) := by
    simp only [eventually_all_finset]
    intro a _ a' _ b _
    refine eventually_imp fun haa' => ?_
    filter_upwards [eventually_quad_lt (sub_pos.2 haa') (a' 1 - a 1)
      ((a' 1 - a 1) * (b 0 - a 0) - (a' 0 - a 0) * (b 1 - a 1))] with s hs
    have e : ls a a' (b + pt s (s ^ 2)) =
        (a' 0 - a 0) * s ^ 2 - ((a' 1 - a 1) * s +
          ((a' 1 - a 1) * (b 0 - a 0) - (a' 0 - a 0) * (b 1 - a 1))) := by
      unfold ls; simp only [PiLp.add_apply, pt_zero, pt_one]; ring
    rw [e]; linarith
  obtain ⟨s, hs1, hs2, hs3⟩ := (h1.and (h2.and h3)).exists
  exact ⟨pt s (s ^ 2), by simpa using hs1, hs2, hs3⟩

/-! ### Gluing -/

/-- `B` lies to the right of `A`, every chord from `A` to `B` is steeper than every chord inside
`B`, and turns left after every chord inside `A`. -/
def Far (A B : Finset ℝ²) : Prop :=
  (∀ a ∈ A, ∀ b ∈ B, a 0 < b 0) ∧
  (∀ a ∈ A, ∀ b ∈ B, ∀ b' ∈ B, b 0 < b' 0 → ls a b b' < 0) ∧
  (∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, a 0 < a' 0 → 0 < ls a a' b)

lemma exists_far_image (A B : Finset ℝ²) : ∃ t : ℝ², Far A (B.image (· + t)) := by
  obtain ⟨t, h1, h2, h3⟩ := exists_far A B
  refine ⟨t, ?_, ?_, ?_⟩
  · intro a ha x hx
    obtain ⟨b, hb0, rfl⟩ := Finset.mem_image.1 hx
    simpa using h1 a ha b hb0
  · intro a ha x hx x' hx' hxx'
    obtain ⟨b, hb0, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b', hb0', rfl⟩ := Finset.mem_image.1 hx'
    simp only [PiLp.add_apply] at hxx'
    exact h2 a ha b hb0 b' hb0' (by linarith)
  · intro a ha a' ha' x hx haa'
    obtain ⟨b, hb0, rfl⟩ := Finset.mem_image.1 hx
    exact h3 a ha a' ha' b hb0 haa'

lemma card_image_add (B : Finset ℝ²) (t : ℝ²) : (B.image (· + t)).card = B.card :=
  Finset.card_image_of_injective _ (add_left_injective t)

variable {A B : Finset ℝ²}

lemma Far.disjoint (h : Far A B) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro a ha hb
  exact lt_irrefl _ (h.1 a ha a hb)

lemma Far.card_union (h : Far A B) : (A ∪ B).card = A.card + B.card :=
  Finset.card_union_of_disjoint h.disjoint

lemma Far.xInj (h : Far A B) (hA : XInj A) (hB : XInj B) : XInj (A ∪ B) := by
  intro p hp q hq hpq
  rcases Finset.mem_union.1 hp with hp | hp <;> rcases Finset.mem_union.1 hq with hq | hq
  · exact hA p hp q hq hpq
  · exact absurd hpq (h.1 p hp q hq).ne
  · exact absurd hpq.symm (h.1 q hq p hp).ne
  · exact hB p hp q hq hpq

lemma Far.genPos (h : Far A B) (hA : GenPos A) (hB : GenPos B) : GenPos (A ∪ B) := by
  intro p hp q hq r hr hpq hqr
  rcases Finset.mem_union.1 hr with hr | hr
  · rcases Finset.mem_union.1 hq with hq | hq
    · rcases Finset.mem_union.1 hp with hp | hp
      · exact hA p hp q hq r hr hpq hqr
      · exact absurd (h.1 q hq p hp) (by linarith)
    · exact absurd (h.1 r hr q hq) (by linarith)
  · rcases Finset.mem_union.1 hq with hq | hq
    · rcases Finset.mem_union.1 hp with hp | hp
      · exact (h.2.2 p hp q hq r hr hpq).ne'
      · exact absurd (h.1 q hq p hp) (by linarith)
    · rcases Finset.mem_union.1 hp with hp | hp
      · exact (h.2.1 p hp q hq r hr hqr).ne
      · exact hB p hp q hq r hr hpq hqr

/-- A cup that meets `A` has at most one point outside `A`. -/
lemma Far.cup_sdiff (h : Far A B) (hB : XInj B) {C : Finset ℝ²} (hC : C ⊆ A ∪ B)
    (hcup : IsCup C) {a : ℝ²} (haC : a ∈ C) (haA : a ∈ A) : (C \ A).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro b hb b' hb'
  rw [Finset.mem_sdiff] at hb hb'
  have hbB : b ∈ B := (Finset.mem_union.1 (hC hb.1)).resolve_left hb.2
  have hbB' : b' ∈ B := (Finset.mem_union.1 (hC hb'.1)).resolve_left hb'.2
  by_contra hne
  rcases lt_trichotomy (b 0) (b' 0) with hlt | heq | hgt
  · exact absurd (hcup a haC b hb.1 b' hb'.1 (h.1 a haA b hbB) hlt)
      (not_lt.2 (h.2.1 a haA b hbB b' hbB' hlt).le)
  · exact hne (hB b hbB b' hbB' heq)
  · exact absurd (hcup a haC b' hb'.1 b hb.1 (h.1 a haA b' hbB') hgt)
      (not_lt.2 (h.2.1 a haA b' hbB' b hbB hgt).le)

/-- A cap that meets `B` has at most one point of `A`. -/
lemma Far.cap_inter (h : Far A B) (hA : XInj A) {C : Finset ℝ²} (hC : C ⊆ A ∪ B)
    (hcap : IsCap C) {b : ℝ²} (hbC : b ∈ C) (hbA : b ∉ A) : (C ∩ A).card ≤ 1 := by
  have hbB : b ∈ B := (Finset.mem_union.1 (hC hbC)).resolve_left hbA
  rw [Finset.card_le_one]
  intro a ha a' ha'
  rw [Finset.mem_inter] at ha ha'
  by_contra hne
  rcases lt_trichotomy (a 0) (a' 0) with hlt | heq | hgt
  · exact absurd (hcap a ha.1 a' ha'.1 b hbC hlt (h.1 a' ha'.2 b hbB))
      (not_lt.2 (h.2.2 a ha.2 a' ha'.2 b hbB hlt).le)
  · exact hne (hA a ha.2 a' ha'.2 heq)
  · exact absurd (hcap a' ha'.1 a ha.1 b hbC hgt (h.1 a ha.2 b hbB))
      (not_lt.2 (h.2.2 a' ha'.2 a ha.2 b hbB hgt).le)

lemma card_eq_inter_add_sdiff (C A : Finset ℝ²) : C.card = (C ∩ A).card + (C \ A).card :=
  (Finset.card_inter_add_card_sdiff C A).symm

lemma sdiff_subset_of_subset_union {C : Finset ℝ²} (hC : C ⊆ A ∪ B) : C \ A ⊆ B := by
  intro x hx
  rw [Finset.mem_sdiff] at hx
  exact (Finset.mem_union.1 (hC hx.1)).resolve_left hx.2

lemma Far.cupBound (h : Far A B) (hB : XInj B) {kA kB : ℕ} (hA' : CupBound kA A)
    (hB' : CupBound kB B) : CupBound (max (kA + 1) kB) (A ∪ B) := by
  intro C hC hcup
  by_cases hm : ∃ a ∈ C, a ∈ A
  · obtain ⟨a, haC, haA⟩ := hm
    have h1 := h.cup_sdiff hB hC hcup haC haA
    have h2 := hA' (C ∩ A) Finset.inter_subset_right (hcup.mono Finset.inter_subset_left)
    rw [card_eq_inter_add_sdiff C A]
    omega
  · push Not at hm
    have hCB : C ⊆ B := by
      intro x hx
      exact (Finset.mem_union.1 (hC hx)).resolve_left (hm x hx)
    have := hB' C hCB hcup
    omega

lemma Far.capBound (h : Far A B) (hA : XInj A) {lA lB : ℕ} (hA' : CapBound lA A)
    (hB' : CapBound lB B) : CapBound (max lA (lB + 1)) (A ∪ B) := by
  intro C hC hcap
  by_cases hm : ∃ b ∈ C, b ∉ A
  · obtain ⟨b, hbC, hbA⟩ := hm
    have h1 := h.cap_inter hA hC hcap hbC hbA
    have h2 := hB' (C \ A) (sdiff_subset_of_subset_union hC) (hcap.mono Finset.sdiff_subset)
    rw [card_eq_inter_add_sdiff C A]
    omega
  · push Not at hm
    have := hA' C (fun x hx => hm x hx) hcap
    omega

/-! ### Blocks with short cups and short caps -/

lemma single_props (p : ℝ²) (a b : ℕ) :
    XInj {p} ∧ GenPos {p} ∧ CupBound (a + 1) {p} ∧ CapBound (b + 1) {p} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy _; simp at hx hy; rw [hx, hy]
  · intro x hx y hy z hz hxy _; simp at hx hy; rw [hx, hy] at hxy; exact absurd hxy (lt_irrefl _)
  · intro C hC _; have := Finset.card_le_card hC; simp at this; omega
  · intro C hC _; have := Finset.card_le_card hC; simp at this; omega

/-- For all `a b`, there are `C(a+b, a)` points in general position, with distinct
`x`-coordinates, whose cups have at most `a + 1` points and whose caps have at most `b + 1`
points. -/
theorem exists_block : ∀ a b : ℕ, ∃ S : Finset ℝ², S.card = (a + b).choose a ∧ XInj S ∧
    GenPos S ∧ CupBound (a + 1) S ∧ CapBound (b + 1) S := by
  intro a
  induction a with
  | zero =>
    intro b
    obtain ⟨h1, h2, h3, h4⟩ := single_props 0 0 b
    exact ⟨{0}, by simp, h1, h2, h3, h4⟩
  | succ a iha =>
    intro b
    induction b with
    | zero =>
      obtain ⟨h1, h2, h3, h4⟩ := single_props 0 (a + 1) 0
      exact ⟨{0}, by simp, h1, h2, h3, h4⟩
    | succ b ihb =>
      obtain ⟨A, hAc, hAx, hAg, hAcup, hAcap⟩ := iha (b + 1)
      obtain ⟨B, hBc, hBx, hBg, hBcup, hBcap⟩ := ihb
      obtain ⟨t, ht⟩ := exists_far_image A B
      refine ⟨A ∪ B.image (· + t), ?_, ht.xInj hAx (hBx.image_add t),
        ht.genPos hAg (hBg.image_add t), ?_, ?_⟩
      · rw [ht.card_union, card_image_add, hAc, hBc]
        rw [show a + 1 + (b + 1) = (a + (b + 1)) + 1 by ring, Nat.choose_succ_succ]
        congr 2; ring
      · have := ht.cupBound (hBx.image_add t) hAcup (hBcup.image_add t)
        rwa [show max (a + 1 + 1) (a + 1 + 1) = a + 1 + 1 by simp] at this
      · have := ht.capBound hAx hAcap (hBcap.image_add t)
        rwa [show max (b + 1 + 1) (b + 1 + 1) = b + 1 + 1 by simp] at this

/-! ### A convex polygon is a cup and a cap -/

lemma combo_mem {X : Set ℝ²} {p r : ℝ²} (hp : p ∈ X) (hr : r ∈ X) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : (1 - t) • p + t • r ∈ convexHull ℝ X :=
  convex_convexHull ℝ X (subset_convexHull ℝ X hp) (subset_convexHull ℝ X hr) (by linarith) ht0
    (by ring)

lemma combo_apply (p r : ℝ²) (t : ℝ) (i : Fin 2) :
    ((1 - t) • p + t • r) i = (1 - t) * p i + t * r i := by
  simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- A point strictly between two points of a convex hull on a vertical line is in the hull. -/
lemma mem_hull_between {X : Set ℝ²} {A B q : ℝ²} (hA : A ∈ convexHull ℝ X)
    (hB : B ∈ convexHull ℝ X) (h0A : A 0 = q 0) (h0B : B 0 = q 0)
    (h1 : (A 1 - q 1) * (B 1 - q 1) < 0) : q ∈ convexHull ℝ X := by
  have hne : B 1 - A 1 ≠ 0 := by
    intro h
    have : B 1 = A 1 := by linarith
    rw [this] at h1
    nlinarith [sq_nonneg (A 1 - q 1)]
  set μ := (q 1 - A 1) / (B 1 - A 1) with hμ
  have hμ0 : 0 ≤ μ := by
    rcases lt_or_gt_of_ne hne with h | h
    · apply div_nonneg_of_nonpos _ h.le
      nlinarith
    · apply div_nonneg _ h.le
      nlinarith
  have hμ1 : μ ≤ 1 := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [hμ, div_le_one_of_neg h]; nlinarith
    · rw [hμ, div_le_one h]; nlinarith
  have hq : q = (1 - μ) • A + μ • B := by
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, combo_apply, h0A, h0B]; ring
    · simp only [Fin.mk_one, Fin.isValue, combo_apply, hμ]
      field_simp
      ring
  rw [hq]
  exact convex_convexHull ℝ X hA hB (by linarith) hμ0 (by ring)

/-- If `q` lies above the chord `p r` and below the line `L R`, or the other way round, and
`L ≤ p < q < r ≤ R` from left to right, then `q` is in the convex hull of `p, r, L, R`. -/
lemma mem_hull_of_sides {X : Set ℝ²} {p r L R q : ℝ²} (hp : p ∈ X) (hr : r ∈ X) (hL : L ∈ X)
    (hR : R ∈ X) (hLp : L 0 ≤ p 0) (hpq : p 0 < q 0) (hqr : q 0 < r 0) (hrR : r 0 ≤ R 0)
    (hside : ls p r q * ls L R q < 0) : q ∈ convexHull ℝ X := by
  have hpr : 0 < r 0 - p 0 := by linarith
  have hLR : 0 < R 0 - L 0 := by linarith
  set t := (q 0 - p 0) / (r 0 - p 0) with ht
  set s := (q 0 - L 0) / (R 0 - L 0) with hs
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hpr.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hpr]; linarith
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hLR.le
  have hs1 : s ≤ 1 := by rw [hs, div_le_one hLR]; linarith
  refine mem_hull_between (combo_mem hp hr ht0 ht1) (combo_mem hL hR hs0 hs1) ?_ ?_ ?_
  · rw [combo_apply, ht]; field_simp; ring
  · rw [combo_apply, hs]; field_simp; ring
  · have eA : ((1 - t) • p + t • r) 1 - q 1 = -ls p r q / (r 0 - p 0) := by
      rw [combo_apply, ht]; unfold ls; field_simp; ring
    have eB : ((1 - s) • L + s • R) 1 - q 1 = -ls L R q / (R 0 - L 0) := by
      rw [combo_apply, hs]; unfold ls; field_simp; ring
    rw [eA, eB, neg_div, neg_div, neg_mul_neg, div_mul_div_comm]
    exact div_neg_of_neg_of_pos hside (mul_pos hpr hLR)

/-- The points of a convex polygon with distinct `x`-coordinates split into a cup and a cap that
share the leftmost point `L` and the rightmost point `R`. -/
theorem exists_cup_cap_split {P : Finset ℝ²} (hx : XInj P) (hg : GenPos P)
    (hc : ∀ a ∈ (P : Set ℝ²), a ∉ convexHull ℝ ((P : Set ℝ²) \ {a})) (h2 : 2 ≤ P.card) :
    ∃ L ∈ P, ∃ R ∈ P, (∀ p ∈ P, L 0 ≤ p 0 ∧ p 0 ≤ R 0) ∧
      ∃ D U : Finset ℝ², D ⊆ P ∧ U ⊆ P ∧ L ∈ D ∧ R ∈ D ∧ L ∈ U ∧ R ∈ U ∧
        IsCup D ∧ IsCap U ∧ D.card + U.card = P.card + 2 := by
  classical
  have hne : P.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨L, hL, hLmin⟩ := Finset.exists_min_image P (fun p => p 0) hne
  obtain ⟨R, hR, hRmax⟩ := Finset.exists_max_image P (fun p => p 0) hne
  have hLR : L 0 < R 0 := by
    by_contra hle
    push Not at hle
    have hsub : P ⊆ {L} := by
      intro p hp
      have := hx p hp L hL (le_antisymm ((hRmax p hp).trans hle) (hLmin p hp))
      simp [this]
    have := Finset.card_le_card hsub
    simp at this; omega
  have hmid : ∀ p ∈ P, p ≠ L → p ≠ R → L 0 < p 0 ∧ p 0 < R 0 := by
    intro p hp hpL hpR
    refine ⟨lt_of_le_of_ne (hLmin p hp) fun h => hpL (hx p hp L hL h.symm),
      lt_of_le_of_ne (hRmax p hp) fun h => hpR (hx p hp R hR h)⟩
  have hside : ∀ p ∈ P, p ≠ L → p ≠ R → ls L R p ≠ 0 := by
    intro p hp hpL hpR
    obtain ⟨h1, h2⟩ := hmid p hp hpL hpR
    have := hg L hL p hp R hR h1 h2
    rw [ls_swap23 L p R]; exact neg_ne_zero.2 this
  have hLL : ls L R L = 0 := by unfold ls; ring
  have hRR : ls L R R = 0 := by unfold ls; ring
  have hLneR : L ≠ R := fun h => by rw [h] at hLR; exact lt_irrefl _ hLR
  set Fm := P.filter (fun p => ls L R p < 0) with hFm
  set Fp := P.filter (fun p => 0 < ls L R p) with hFp
  refine ⟨L, hL, R, hR, fun p hp => ⟨hLmin p hp, hRmax p hp⟩, insert L (insert R Fm),
    insert L (insert R Fp), ?_, ?_, by simp, by simp, by simp, by simp, ?_, ?_, ?_⟩
  · intro x hx'
    simp only [Finset.mem_insert, hFm, Finset.mem_filter] at hx'
    rcases hx' with rfl | rfl | ⟨h, _⟩ <;> assumption
  · intro x hx'
    simp only [Finset.mem_insert, hFp, Finset.mem_filter] at hx'
    rcases hx' with rfl | rfl | ⟨h, _⟩ <;> assumption
  · -- the lower points form a cup
    intro p hp q hq r hr hpq hqr
    have hmem : ∀ x ∈ insert L (insert R Fm), x ∈ P := by
      intro x hx'
      simp only [Finset.mem_insert, hFm, Finset.mem_filter] at hx'
      rcases hx' with rfl | rfl | ⟨h, _⟩ <;> assumption
    have hpP := hmem p hp
    have hrP := hmem r hr
    have hqL : q ≠ L := fun h => by
      have := hLmin p hpP; rw [h] at hpq; linarith
    have hqR : q ≠ R := fun h => by
      have := hRmax r hrP; rw [h] at hqr; linarith
    have hqF : q ∈ P ∧ ls L R q < 0 := by
      simp only [Finset.mem_insert, hqL, hqR, false_or, hFm, Finset.mem_filter] at hq
      exact hq
    by_contra hneg
    have hne' := hg p hpP q hqF.1 r hrP hpq hqr
    have hlt : ls p q r < 0 := lt_of_le_of_ne (not_lt.1 hneg) hne'
    have hX : ∀ x ∈ P, x ≠ q → x ∈ (P : Set ℝ²) \ {q} := fun x hx' hxq => ⟨hx', hxq⟩
    apply hc q hqF.1
    refine mem_hull_of_sides (hX p hpP (by rintro rfl; exact lt_irrefl _ hpq))
      (hX r hrP (by rintro rfl; exact lt_irrefl _ hqr)) (hX L hL hqL.symm) (hX R hR hqR.symm)
      (hLmin p hpP) hpq hqr (hRmax r hrP) ?_
    rw [ls_swap23]
    nlinarith [hqF.2]
  · -- the upper points form a cap
    intro p hp q hq r hr hpq hqr
    have hmem : ∀ x ∈ insert L (insert R Fp), x ∈ P := by
      intro x hx'
      simp only [Finset.mem_insert, hFp, Finset.mem_filter] at hx'
      rcases hx' with rfl | rfl | ⟨h, _⟩ <;> assumption
    have hpP := hmem p hp
    have hrP := hmem r hr
    have hqL : q ≠ L := fun h => by
      have := hLmin p hpP; rw [h] at hpq; linarith
    have hqR : q ≠ R := fun h => by
      have := hRmax r hrP; rw [h] at hqr; linarith
    have hqF : q ∈ P ∧ 0 < ls L R q := by
      simp only [Finset.mem_insert, hqL, hqR, false_or, hFp, Finset.mem_filter] at hq
      exact hq
    by_contra hneg
    have hne' := hg p hpP q hqF.1 r hrP hpq hqr
    have hlt : 0 < ls p q r := lt_of_le_of_ne (not_lt.1 hneg) hne'.symm
    have hX : ∀ x ∈ P, x ≠ q → x ∈ (P : Set ℝ²) \ {q} := fun x hx' hxq => ⟨hx', hxq⟩
    apply hc q hqF.1
    refine mem_hull_of_sides (hX p hpP (by rintro rfl; exact lt_irrefl _ hpq))
      (hX r hrP (by rintro rfl; exact lt_irrefl _ hqr)) (hX L hL hqL.symm) (hX R hR hqR.symm)
      (hLmin p hpP) hpq hqr (hRmax r hrP) ?_
    rw [ls_swap23]
    nlinarith [hqF.2]
  · -- counting
    have hLFm : L ∉ Fm := by simp [hFm, hLL]
    have hRFm : R ∉ Fm := by simp [hFm, hRR]
    have hLFp : L ∉ Fp := by simp [hFp, hLL]
    have hRFp : R ∉ Fp := by simp [hFp, hRR]
    have hD : (insert L (insert R Fm)).card = Fm.card + 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hLneR, hLFm]),
        Finset.card_insert_of_notMem hRFm]
    have hU : (insert L (insert R Fp)).card = Fp.card + 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hLneR, hLFp]),
        Finset.card_insert_of_notMem hRFp]
    have hsplit : P.filter (fun p => ¬ ls L R p < 0) = insert L (insert R Fp) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, hFp]
      constructor
      · rintro ⟨hxP, hx'⟩
        by_cases hxL : x = L
        · exact Or.inl hxL
        by_cases hxR : x = R
        · exact Or.inr (Or.inl hxR)
        exact Or.inr (Or.inr ⟨hxP, lt_of_le_of_ne (not_lt.1 hx') (hside x hxP hxL hxR).symm⟩)
      · rintro (rfl | rfl | ⟨hxP, hx'⟩)
        · exact ⟨hL, by simp [hLL]⟩
        · exact ⟨hR, by simp [hRR]⟩
        · exact ⟨hxP, not_lt.2 hx'.le⟩
    have hP := Finset.card_filter_add_card_filter_not (s := P) (fun p => ls L R p < 0)
    rw [hsplit, hU] at hP
    rw [hD, hU, ← hP, hFm]
    ring

/-! ### Convex polygons in glued sets -/

lemma card_add_two_le {S : Finset ℝ²} {k l : ℕ} (hx : XInj S) (hg : GenPos S)
    (hcup : CupBound k S) (hcap : CapBound l S) {P : Finset ℝ²} (hP : P ⊆ S)
    (hc : ∀ a ∈ (P : Set ℝ²), a ∉ convexHull ℝ ((P : Set ℝ²) \ {a})) (h2 : 2 ≤ P.card) :
    P.card + 2 ≤ k + l := by
  obtain ⟨L, -, R, -, -, D, U, hD, hU, -, -, -, -, hDc, hUc, hcard⟩ :=
    exists_cup_cap_split (hx.mono hP) (hg.mono hP) hc h2
  have := hcup D (hD.trans hP) hDc
  have := hcap U (hU.trans hP) hUc
  omega

lemma Far.convBound (h : Far A B) (hAx : XInj A) (hBx : XInj B) (hAg : GenPos A)
    (hBg : GenPos B) {M kA kB lB : ℕ} (hA : ConvBound M A) (hAcup : CupBound kA A)
    (hBcup : CupBound kB B) (hBcap : CapBound lB B) (h1 : kA + lB ≤ M) (h2 : kB + lB ≤ M + 2)
    (h3 : 1 ≤ M) : ConvBound M (A ∪ B) := by
  intro P hP hc
  by_cases hsmall : P.card ≤ 1
  · omega
  push Not at hsmall
  by_cases hmB : ∃ b ∈ P, b ∉ A
  · by_cases hmA : ∃ a ∈ P, a ∈ A
    · -- `P` meets both `A` and `B`
      obtain ⟨b, hbP, hbA⟩ := hmB
      obtain ⟨a, haP, haA⟩ := hmA
      have hbB : b ∈ B := (Finset.mem_union.1 (hP hbP)).resolve_left hbA
      obtain ⟨L, hLP, R, hRP, hLR, D, U, hD, hU, hLD, -, -, hRU, hDc, hUc, hcard⟩ :=
        exists_cup_cap_split ((h.xInj hAx hBx).mono hP) ((h.genPos hAg hBg).mono hP) hc hsmall
      have hLA : L ∈ A := by
        by_contra hLA
        have hLB : L ∈ B := (Finset.mem_union.1 (hP hLP)).resolve_left hLA
        have := h.1 a haA L hLB
        have := (hLR a haP).1
        linarith
      have hRA : R ∉ A := by
        intro hRA
        have := h.1 R hRA b hbB
        have := (hLR b hbP).2
        linarith
      have hD1 := h.cup_sdiff hBx (hD.trans hP) hDc hLD hLA
      have hD2 := hAcup (D ∩ A) Finset.inter_subset_right (hDc.mono Finset.inter_subset_left)
      have hU1 := h.cap_inter hAx (hU.trans hP) hUc hRU hRA
      have hU2 := hBcap (U \ A) (sdiff_subset_of_subset_union (hU.trans hP))
        (hUc.mono Finset.sdiff_subset)
      have eD := card_eq_inter_add_sdiff D A
      have eU := card_eq_inter_add_sdiff U A
      omega
    · -- `P` lies in `B`
      push Not at hmA
      have hPB : P ⊆ B := fun x hx => (Finset.mem_union.1 (hP hx)).resolve_left (hmA x hx)
      have := card_add_two_le hBx hBg hBcup hBcap hPB hc hsmall
      omega
  · -- `P` lies in `A`
    push Not at hmB
    exact hA P (fun x hx => hmB x hx) hc

/-! ### The construction -/

/-- Gluing the blocks of sizes `C(m, 0), …, C(m, j)`: the result has distinct `x`-coordinates,
is in general position, has cups of at most `j + 1` points, and has no `m + 2` points in convex
position. -/
theorem exists_assembly (m : ℕ) : ∀ j ≤ m, ∃ S : Finset ℝ², XInj S ∧ GenPos S ∧
    S.card = ∑ i ∈ Finset.range (j + 1), m.choose i ∧ CupBound (j + 1) S ∧ ConvBound (m + 1) S := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨S, hc, hx, hg, hcup, hcap⟩ := exists_block 0 m
    refine ⟨S, hx, hg, by simpa using hc, hcup, ?_⟩
    intro P hP hconv
    by_cases hsmall : P.card ≤ 1
    · omega
    have := card_add_two_le hx hg hcup hcap hP hconv (by omega)
    omega
  | succ j ih =>
    intro hj
    obtain ⟨A, hAx, hAg, hAc, hAcup, hAconv⟩ := ih (by omega)
    obtain ⟨B, hBc, hBx, hBg, hBcup, hBcap⟩ := exists_block (j + 1) (m - (j + 1))
    obtain ⟨t, ht⟩ := exists_far_image A B
    refine ⟨A ∪ B.image (· + t), ht.xInj hAx (hBx.image_add t),
      ht.genPos hAg (hBg.image_add t), ?_, ?_, ?_⟩
    · have e : j + 1 + (m - (j + 1)) = m := by omega
      rw [ht.card_union, card_image_add, hAc, hBc, e, Finset.sum_range_succ _ (j + 1)]
    · have := ht.cupBound (hBx.image_add t) hAcup (hBcup.image_add t)
      rwa [show max (j + 1 + 1) (j + 1 + 1) = j + 1 + 1 by simp] at this
    · exact ht.convBound hAx (hBx.image_add t) hAg (hBg.image_add t) hAconv hAcup
        (hBcup.image_add t) (hBcap.image_add t) (by omega) (by omega) (by omega)

lemma cross_eq_zero_of_collinear {a b c : ℝ²} (h : Collinear ℝ ({a, b, c} : Set ℝ²)) :
    ls a b c = 0 := by
  rw [collinear_iff_of_mem (by simp : a ∈ ({a, b, c} : Set ℝ²))] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨rb, hrb⟩ := hv b (by simp)
  obtain ⟨rc, hrc⟩ := hv c (by simp)
  have hb0 : b 0 = rb * v 0 + a 0 := by simpa using congrArg (fun w : ℝ² => w 0) hrb
  have hb1 : b 1 = rb * v 1 + a 1 := by simpa using congrArg (fun w : ℝ² => w 1) hrb
  have hc0 : c 0 = rc * v 0 + a 0 := by simpa using congrArg (fun w : ℝ² => w 0) hrc
  have hc1 : c 1 = rc * v 1 + a 1 := by simpa using congrArg (fun w : ℝ² => w 1) hrc
  unfold ls
  rw [hb0, hb1, hc0, hc1]
  ring

lemma ls_ne_zero {S : Finset ℝ²} (hx : XInj S) (hg : GenPos S) {x y z : ℝ²} (hxS : x ∈ S)
    (hyS : y ∈ S) (hzS : z ∈ S) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : ls x y z ≠ 0 := by
  have dxy : x 0 ≠ y 0 := fun h => hxy (hx x hxS y hyS h)
  have dyz : y 0 ≠ z 0 := fun h => hyz (hx y hyS z hzS h)
  have dxz : x 0 ≠ z 0 := fun h => hxz (hx x hxS z hzS h)
  intro h0
  rcases lt_or_gt_of_ne dxy with h1 | h1 <;> rcases lt_or_gt_of_ne dyz with h2 | h2 <;>
    rcases lt_or_gt_of_ne dxz with h3 | h3
  · exact hg x hxS y hyS z hzS h1 h2 h0
  · linarith
  · exact hg x hxS z hzS y hyS h3 h2 (by unfold ls at h0 ⊢; linear_combination -h0)
  · exact hg z hzS x hxS y hyS h3 h1 (by unfold ls at h0 ⊢; linear_combination h0)
  · exact hg y hyS x hxS z hzS h1 h3 (by unfold ls at h0 ⊢; linear_combination -h0)
  · exact hg y hyS z hzS x hxS h2 h3 (by unfold ls at h0 ⊢; linear_combination h0)
  · linarith
  · exact hg z hzS y hyS x hxS h2 h1 (by unfold ls at h0 ⊢; linear_combination -h0)

/-- **Erdős–Szekeres lower construction.** For `n ≥ 3` and `N ≤ 2^(n-2)` there are `N` points in
the plane, no three on a line, with no `n` of them in convex position. -/
theorem lower_construction (n : ℕ) (hn : 3 ≤ n) (N : ℕ) (hN : N ≤ 2 ^ (n - 2)) :
    ∃ pts : Finset ℝ², pts.card = N ∧
      (∀ x ∈ pts, ∀ y ∈ pts, ∀ z ∈ pts, x ≠ y → y ≠ z → x ≠ z →
        ¬ Collinear ℝ ({x, y, z} : Set ℝ²)) ∧
      ∀ S : Finset ℝ², S ⊆ pts →
        (∀ a ∈ (S : Set ℝ²), a ∉ convexHull ℝ ((S : Set ℝ²) \ {a})) → S.card < n := by
  obtain ⟨S, hx, hg, hc, -, hconv⟩ := exists_assembly (n - 2) (n - 2) le_rfl
  rw [Nat.sum_range_choose] at hc
  obtain ⟨pts, hsub, hcard⟩ := Finset.exists_subset_card_eq (s := S) (n := N) (by omega)
  refine ⟨pts, hcard, ?_, ?_⟩
  · intro x hxp y hyp z hzp hxy hyz hxz hcol
    exact ls_ne_zero hx hg (hsub hxp) (hsub hyp) (hsub hzp) hxy hyz hxz
      (cross_eq_zero_of_collinear hcol)
  · intro T hT hTc
    have := hconv T (hT.trans hsub) hTc
    omega

end Erdos107Lower
