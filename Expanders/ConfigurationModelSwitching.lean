/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.ConfigurationModel

/-!
# Switchings in the configuration model

A **switching** of a pairing `π` replaces two of its pairs `{p, u}`, `{x, y}` by `{p, x}`,
`{u, y}`. As a permutation this is conjugation by the transposition of `u` and `x`, so the
switching of a pairing is again a pairing. Switchings are the tool that compares the number of
pairings containing a prescribed pair with the number of all pairings in a class.

## Main results
* `ConfigurationModel.mul_card_filter_le_of_switch`: the double count. If every `π` in a class
  `T` that pairs `p` with `u` has at least `K` switchings landing in a class `T'`, then
  `K * #{π ∈ T | π p = u} ≤ #T'`.
* `ConfigurationModel.goodCount_le_card_good`: all but `2d(d + 1)` of the `n * d` points `x` are
  *good* for switching the pair `{a, b}`: the two new pairs `{a, x}` and `{b, π x}` are neither
  loops nor parallel to any other pair.
* `ConfigurationModel.switch_fst_ne`, `ConfigurationModel.switch_parallel_free`: a good switching
  creates no loop and no repeated edge.
* `ConfigurationModel.looplessOn_insert_card`, `ConfigurationModel.simpleOn_insert_card`:
  forbidding loops at one more point, or repeated edges at one more point, loses at most a
  proportion `d / K`, respectively `n d³ / K²`, of a class, where `K = n d - 2d(d + 1)`.
* `ConfigurationModel.switching_card_bound`: chaining these over all `n * d` points,

  `((K - d) * (K² - n d³)) ^ (n d) * #{pairings} ≤ (K * K²) ^ (n d) * #{simple pairings}`.

The last inequality is purely about natural numbers (with truncated subtraction) and holds for
all `n` and `d`. `Expanders/ConfigurationModelSimple.lean` turns it into a positive lower bound
for the proportion of simple pairings.

## Why this works
The naive bound "the next pair is bad with probability at most `C / (number of points left)`"
loses a factor polynomial in `n`. The chain used here instead removes one *point* at a time from
the set of points at which a defect is still allowed, and a defect at a fixed point `q` has
probability `O(1 / n)` in every class of the chain, uniformly: a loop at `q` is one of `d - 1`
events `π q = u`, each of probability at most `1 / K` by one switching; a repeated edge at `q` is
one of at most `n d³` events `π q = u ∧ π q' = u'`, each of probability at most `1 / K²` by two
switchings. There are `n d` points, so the total loss is a constant factor.
-/

open Finset

namespace ConfigurationModel

/-! ## Switchings of a permutation -/

section Switch

variable {α : Type*} [DecidableEq α]

/-- The **switching** of `π` at `u` and `x`: conjugate `π` by the transposition of `u` and `x`.
If `π` pairs `p` with `u` and `x` with `y`, the switching pairs `p` with `x` and `u` with `y`
and leaves every other pair alone. -/
def switch (π : Equiv.Perm α) (u x : α) : Equiv.Perm α :=
  Equiv.swap u x * π * Equiv.swap u x

theorem switch_apply (π : Equiv.Perm α) (u x z : α) :
    switch π u x z = Equiv.swap u x (π (Equiv.swap u x z)) :=
  rfl

/-- Switching twice at the same two points gives back the original permutation. -/
@[simp]
theorem switch_switch (π : Equiv.Perm α) (u x : α) : switch (switch π u x) u x = π := by
  ext z
  simp [switch_apply]

/-- If `π` pairs `p` with `u`, the switching at `u` and `x` pairs `p` with `x`. -/
theorem switch_apply_of_apply_eq {π : Equiv.Perm α} {p u x : α} (h : π p = u) (hpu : p ≠ u)
    (hpx : p ≠ x) : switch π u x p = x := by
  rw [switch_apply, Equiv.swap_apply_of_ne_of_ne hpu hpx, h, Equiv.swap_apply_left]

/-- **Double counting switchings.** Let `T`, `T'` be classes of permutations and `p ≠ u`.
If every `π ∈ T` with `π p = u` has a set `G` of at least `K` points `x ≠ p` whose switching
`switch π u x` lies in `T'`, then `K * #{π ∈ T | π p = u} ≤ #T'`.

The map `(π, x) ↦ switch π u x` is injective, because `x` is the partner of `p` in the
switching and switching again at `u` and `x` recovers `π`. -/
theorem mul_card_filter_le_of_switch [Fintype α] {T T' : Finset (Equiv.Perm α)} {p u : α}
    (hpu : p ≠ u) {K : ℕ}
    (h : ∀ π ∈ T, π p = u → ∃ G : Finset α, K ≤ #G ∧ ∀ x ∈ G, x ≠ p ∧ switch π u x ∈ T') :
    K * #{π ∈ T | π p = u} ≤ #T' := by
  classical
  let t : Equiv.Perm α → Finset α := fun π => {x | x ≠ p ∧ switch π u x ∈ T'}
  have hK : ∀ π ∈ ({π ∈ T | π p = u} : Finset (Equiv.Perm α)), K ≤ #(t π) := by
    intro π hπ
    obtain ⟨hπT, hπp⟩ := mem_filter.mp hπ
    obtain ⟨G, hG, hGt⟩ := h π hπT hπp
    exact hG.trans (card_le_card fun x hx => mem_filter.mpr ⟨mem_univ _, hGt x hx⟩)
  calc K * #{π ∈ T | π p = u}
      = ∑ _π ∈ ({π ∈ T | π p = u} : Finset (Equiv.Perm α)), K := by
        rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ π ∈ ({π ∈ T | π p = u} : Finset (Equiv.Perm α)), #(t π) := sum_le_sum hK
    _ = #(({π ∈ T | π p = u} : Finset (Equiv.Perm α)).sigma t) := (card_sigma _ _).symm
    _ ≤ #T' := by
      refine card_le_card_of_injOn (fun a => switch a.1 u a.2) ?_ ?_
      · rintro ⟨π, x⟩ ha
        obtain ⟨-, hx⟩ := mem_sigma.mp (mem_coe.mp ha)
        exact mem_coe.mpr (mem_filter.mp hx).2.2
      · rintro ⟨π₁, x₁⟩ h₁ ⟨π₂, x₂⟩ h₂ heq
        obtain ⟨hπ₁, hx₁⟩ := mem_sigma.mp (mem_coe.mp h₁)
        obtain ⟨hπ₂, hx₂⟩ := mem_sigma.mp (mem_coe.mp h₂)
        have hp₁ : π₁ p = u := (mem_filter.mp hπ₁).2
        have hp₂ : π₂ p = u := (mem_filter.mp hπ₂).2
        have hxp₁ : x₁ ≠ p := (mem_filter.mp hx₁).2.1
        have hxp₂ : x₂ ≠ p := (mem_filter.mp hx₂).2.1
        have heq' : switch π₁ u x₁ = switch π₂ u x₂ := heq
        have hx : x₁ = x₂ := by
          rw [← switch_apply_of_apply_eq hp₁ hpu hxp₁.symm, heq',
            switch_apply_of_apply_eq hp₂ hpu hxp₂.symm]
        subst hx
        have hπ : π₁ = π₂ := by rw [← switch_switch π₁ u x₁, heq', switch_switch]
        subst hπ
        rfl

end Switch

/-! ## Switchings of a pairing -/

variable {n d : ℕ} {π : Equiv.Perm (Fin n × Fin d)}

/-- The switching of a pairing is a pairing. -/
theorem isPairing_switch (hπ : IsPairing π) (u x : Fin n × Fin d) :
    IsPairing (switch π u x) := by
  refine ⟨fun z => ?_, fun z h => ?_⟩
  · simp [switch_apply, hπ.1]
  · rw [switch_apply, Equiv.swap_apply_eq_iff] at h
    exact hπ.2 _ h

section Apply

variable {a b x : Fin n × Fin d}

/-- After switching the pairs `{a, b}`, `{x, π x}`, the partner of `a` is `x`. -/
theorem switch_apply_left (hπ : IsPairing π) (hab : π a = b) (hxa : x ≠ a) :
    switch π b x a = x :=
  switch_apply_of_apply_eq hab (hab ▸ (hπ.2 a).symm) hxa.symm

/-- After switching the pairs `{a, b}`, `{x, π x}`, the partner of `x` is `a`. -/
theorem switch_apply_right (hπ : IsPairing π) (hab : π a = b) (hxa : x ≠ a) :
    switch π b x x = a := by
  have hba : π b = a := by rw [← hab, hπ.1]
  have hne : a ≠ b := hab ▸ (hπ.2 a).symm
  rw [switch_apply, Equiv.swap_apply_right, hba, Equiv.swap_apply_of_ne_of_ne hne hxa.symm]

private theorem apply_ne_of_ne (hab : π a = b) (hxa : x ≠ a) : π x ≠ b :=
  fun h => hxa (π.injective (h.trans hab.symm))

/-- After switching the pairs `{a, b}`, `{x, π x}`, the partner of `b` is `π x`. -/
theorem switch_apply_snd (hπ : IsPairing π) (hab : π a = b) (hxa : x ≠ a) :
    switch π b x b = π x := by
  rw [switch_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (apply_ne_of_ne hab hxa) (hπ.2 x)]

/-- After switching the pairs `{a, b}`, `{x, π x}`, the partner of `π x` is `b`. -/
theorem switch_apply_partner (hπ : IsPairing π) (hab : π a = b) (hxa : x ≠ a) :
    switch π b x (π x) = b := by
  rw [switch_apply, Equiv.swap_apply_of_ne_of_ne (apply_ne_of_ne hab hxa) (hπ.2 x), hπ.1,
    Equiv.swap_apply_right]

/-- Switching the pairs `{a, b}`, `{x, π x}` does not move the partner of any other point. -/
theorem switch_apply_of_ne (hπ : IsPairing π) (hab : π a = b) {z : Fin n × Fin d}
    (hza : z ≠ a) (hzb : z ≠ b) (hzx : z ≠ x) (hzy : z ≠ π x) : switch π b x z = π z := by
  rw [switch_apply, Equiv.swap_apply_of_ne_of_ne hzb hzx, Equiv.swap_apply_of_ne_of_ne ?_ ?_]
  · intro h
    exact hza (by rw [← hπ.1 z, h, ← hab, hπ.1])
  · intro h
    exact hzy (by rw [← h, hπ.1])

end Apply

/-! ## Good switchings -/

/-- The vertices *near* the point `a`: its own vertex and the vertices of the partners of the
points of that vertex. There are at most `d + 1` of them. -/
def near (π : Equiv.Perm (Fin n × Fin d)) (a : Fin n × Fin d) : Finset (Fin n) :=
  insert a.1 (univ.image fun i : Fin d => (π (a.1, i)).1)

theorem fst_mem_near (π : Equiv.Perm (Fin n × Fin d)) (a : Fin n × Fin d) : a.1 ∈ near π a :=
  mem_insert_self _ _

theorem fst_apply_mem_near (π : Equiv.Perm (Fin n × Fin d)) {a a' : Fin n × Fin d}
    (h : a'.1 = a.1) : (π a').1 ∈ near π a :=
  mem_insert_of_mem (mem_image.mpr ⟨a'.2, mem_univ _, by rw [← h]⟩)

theorem card_near_le (π : Equiv.Perm (Fin n × Fin d)) (a : Fin n × Fin d) :
    #(near π a) ≤ d + 1 := by
  refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
  exact card_image_le.trans (by simp)

/-- The points `x` that are **good** for switching the pair `{a, b}` of `π` with the pair
`{x, π x}`: the vertex of `x` is not near `a` and the vertex of `π x` is not near `b`. Then the
new pairs `{a, x}` and `{b, π x}` are neither loops nor parallel to any other pair. -/
def good (π : Equiv.Perm (Fin n × Fin d)) (a b : Fin n × Fin d) : Finset (Fin n × Fin d) :=
  {x | x.1 ∉ near π a ∧ (π x).1 ∉ near π b}

/-- A lower bound, uniform in the pairing and the pair, for the number of good switchings:
`n d - 2d(d + 1)` (truncated subtraction). -/
def goodCount (n d : ℕ) : ℕ := n * d - 2 * ((d + 1) * d)

theorem card_filter_fst_mem (s : Finset (Fin n)) :
    #{x : Fin n × Fin d | x.1 ∈ s} = #s * d := by
  have h : ({x : Fin n × Fin d | x.1 ∈ s} : Finset (Fin n × Fin d)) = s ×ˢ univ := by
    ext x
    simp
  rw [h, card_product, card_univ, Fintype.card_fin]

/-- All but at most `2d(d + 1)` points are good for switching a given pair. -/
theorem goodCount_le_card_good (π : Equiv.Perm (Fin n × Fin d)) (a b : Fin n × Fin d) :
    goodCount n d ≤ #(good π a b) := by
  have h1 : #{x : Fin n × Fin d | x.1 ∈ near π a} ≤ (d + 1) * d := by
    rw [card_filter_fst_mem]
    exact Nat.mul_le_mul_right _ (card_near_le π a)
  have h2 : #{x : Fin n × Fin d | (π x).1 ∈ near π b} ≤ (d + 1) * d := by
    calc #{x : Fin n × Fin d | (π x).1 ∈ near π b}
        ≤ #{y : Fin n × Fin d | y.1 ∈ near π b} :=
          card_le_card_of_injOn π (fun x hx => by simpa using hx) π.injective.injOn
      _ ≤ (d + 1) * d := by
          rw [card_filter_fst_mem]
          exact Nat.mul_le_mul_right _ (card_near_le π b)
  have hcover : (univ : Finset (Fin n × Fin d)) ⊆ good π a b ∪
      (({x : Fin n × Fin d | x.1 ∈ near π a} : Finset (Fin n × Fin d)) ∪
        ({x : Fin n × Fin d | (π x).1 ∈ near π b} : Finset (Fin n × Fin d))) := by
    intro x _
    simp only [good, mem_union, mem_filter, mem_univ, true_and]
    tauto
  have hle := (card_le_card hcover).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _))
  rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hle
  unfold goodCount
  omega

/-- For a good switching of the pairs `{a, b}`, `{x, π x}`, the four points lie in four
different vertices as soon as the two pairs are not loops; this lemma records the four
inequalities that hold without that assumption. -/
theorem fst_ne_of_mem_good (hπ : IsPairing π) {a b x : Fin n × Fin d} (hab : π a = b)
    (hx : x ∈ good π a b) :
    x.1 ≠ a.1 ∧ x.1 ≠ b.1 ∧ (π x).1 ≠ a.1 ∧ (π x).1 ≠ b.1 := by
  obtain ⟨-, h1, h2⟩ := mem_filter.mp hx
  have hba : π b = a := by rw [← hab, hπ.1]
  refine ⟨fun h => h1 ?_, fun h => h1 ?_, fun h => h2 ?_, fun h => h2 ?_⟩
  · rw [h]
    exact fst_mem_near π a
  · rw [h, ← hab]
    exact fst_apply_mem_near π rfl
  · rw [h, ← hba]
    exact fst_apply_mem_near π rfl
  · rw [h]
    exact fst_mem_near π b

/-- **A good switching creates no loop**: if `π` has no loop at `z`, neither has the switching. -/
theorem switch_fst_ne (hπ : IsPairing π) {a b x : Fin n × Fin d} (hab : π a = b)
    (hx : x ∈ good π a b) {z : Fin n × Fin d} (hz : (π z).1 ≠ z.1) :
    (switch π b x z).1 ≠ z.1 := by
  obtain ⟨hxa, -, -, hyb⟩ := fst_ne_of_mem_good hπ hab hx
  have hxa' : x ≠ a := fun h => hxa (h ▸ rfl)
  by_cases h1 : z = a
  · rw [h1, switch_apply_left hπ hab hxa']
    exact hxa
  by_cases h2 : z = b
  · rw [h2, switch_apply_snd hπ hab hxa']
    exact hyb
  by_cases h3 : z = x
  · rw [h3, switch_apply_right hπ hab hxa']
    exact hxa.symm
  by_cases h4 : z = π x
  · rw [h4, switch_apply_partner hπ hab hxa']
    exact hyb.symm
  · rw [switch_apply_of_ne hπ hab h1 h2 h3 h4]
    exact hz

private theorem ne_of_fst_eq_of_fst_ne {w' w t : Fin n × Fin d} (h1 : w'.1 = w.1)
    (ht : t.1 ≠ w.1) : w' ≠ t :=
  fun h => ht (by rw [← h, h1])

/-- **A good switching creates no repeated edge**: if `π` has no loops and no pair parallel to
the pair at `z`, then the switching has no pair parallel to its pair at `z`.

The four points `a`, `b`, `x`, `π x` of the switching lie in four different vertices, so two
points of a common vertex contain at most one of them, and the partner of that one avoids, by
goodness, the vertices of the partners of the other points of its vertex. -/
theorem switch_parallel_free (hπ : IsPairing π) (hloop : ∀ z, (π z).1 ≠ z.1)
    {a b x : Fin n × Fin d} (hab : π a = b) (hx : x ∈ good π a b) {z : Fin n × Fin d}
    (hz : ∀ z', z'.1 = z.1 → (π z').1 = (π z).1 → z' = z) :
    ∀ z', z'.1 = z.1 → (switch π b x z').1 = (switch π b x z).1 → z' = z := by
  obtain ⟨hxa, hxb, hya, hyb⟩ := fst_ne_of_mem_good hπ hab hx
  obtain ⟨-, hna, hnb⟩ := mem_filter.mp hx
  have hab' : a.1 ≠ b.1 := by
    have h := hloop a
    rw [hab] at h
    exact h.symm
  have hxy : (π x).1 ≠ x.1 := hloop x
  have hxa' : x ≠ a := fun h => hxa (h ▸ rfl)
  -- A point `w` of the switching and another point `w'` of its vertex have partners, in the
  -- switching, in different vertices.
  have key : ∀ w w' : Fin n × Fin d, (a = w ∨ b = w ∨ x = w ∨ π x = w) → w'.1 = w.1 → w' ≠ w →
      (switch π b x w').1 ≠ (switch π b x w).1 := by
    intro w w' hw h1 hne
    rcases hw with rfl | rfl | rfl | rfl
    · rw [switch_apply_of_ne hπ hab hne (ne_of_fst_eq_of_fst_ne h1 hab'.symm)
        (ne_of_fst_eq_of_fst_ne h1 hxa) (ne_of_fst_eq_of_fst_ne h1 hya),
        switch_apply_left hπ hab hxa']
      intro h
      exact hna (h ▸ fst_apply_mem_near π h1)
    · rw [switch_apply_of_ne hπ hab (ne_of_fst_eq_of_fst_ne h1 hab') hne
        (ne_of_fst_eq_of_fst_ne h1 hxb) (ne_of_fst_eq_of_fst_ne h1 hyb),
        switch_apply_snd hπ hab hxa']
      intro h
      exact hnb (h ▸ fst_apply_mem_near π h1)
    · rw [switch_apply_of_ne hπ hab (ne_of_fst_eq_of_fst_ne h1 hxa.symm)
        (ne_of_fst_eq_of_fst_ne h1 hxb.symm) hne (ne_of_fst_eq_of_fst_ne h1 hxy),
        switch_apply_right hπ hab hxa']
      intro h
      have hmem := fst_apply_mem_near π h
      rw [hπ.1, h1] at hmem
      exact hna hmem
    · rw [switch_apply_of_ne hπ hab (ne_of_fst_eq_of_fst_ne h1 hya.symm)
        (ne_of_fst_eq_of_fst_ne h1 hyb.symm) (ne_of_fst_eq_of_fst_ne h1 hxy.symm) hne,
        switch_apply_partner hπ hab hxa']
      intro h
      have hmem := fst_apply_mem_near π h
      rw [hπ.1, h1] at hmem
      exact hnb hmem
  intro z' h1 h2
  by_contra hne
  by_cases hzS : a = z ∨ b = z ∨ x = z ∨ π x = z
  · exact key z z' hzS h1 hne h2
  by_cases hzS' : a = z' ∨ b = z' ∨ x = z' ∨ π x = z'
  · exact key z' z hzS' h1.symm (Ne.symm hne) h2.symm
  · simp only [not_or] at hzS hzS'
    rw [switch_apply_of_ne hπ hab (Ne.symm hzS'.1) (Ne.symm hzS'.2.1) (Ne.symm hzS'.2.2.1)
        (Ne.symm hzS'.2.2.2),
      switch_apply_of_ne hπ hab (Ne.symm hzS.1) (Ne.symm hzS.2.1) (Ne.symm hzS.2.2.1)
        (Ne.symm hzS.2.2.2)] at h2
    exact hne (hz z' h1 h2)

/-! ## Classes of partially simple pairings -/

/-- The pairings with no loop at any point of `A`. -/
def looplessOn (A : Finset (Fin n × Fin d)) : Finset (Equiv.Perm (Fin n × Fin d)) :=
  {π ∈ pairings n d | ∀ z ∈ A, (π z).1 ≠ z.1}

/-- The pairings with no loop at all and with no pair parallel to the pair at any point
of `B`. -/
def simpleOn (B : Finset (Fin n × Fin d)) : Finset (Equiv.Perm (Fin n × Fin d)) :=
  {π ∈ pairings n d | (∀ z, (π z).1 ≠ z.1) ∧
    ∀ z ∈ B, ∀ z', z'.1 = z.1 → (π z').1 = (π z).1 → z' = z}

theorem mem_looplessOn {A : Finset (Fin n × Fin d)} :
    π ∈ looplessOn A ↔ IsPairing π ∧ ∀ z ∈ A, (π z).1 ≠ z.1 := by
  simp [looplessOn]

theorem mem_simpleOn {B : Finset (Fin n × Fin d)} :
    π ∈ simpleOn B ↔ IsPairing π ∧ (∀ z, (π z).1 ≠ z.1) ∧
      ∀ z ∈ B, ∀ z', z'.1 = z.1 → (π z').1 = (π z).1 → z' = z := by
  simp [simpleOn]

theorem looplessOn_empty : looplessOn (∅ : Finset (Fin n × Fin d)) = pairings n d := by
  ext π
  simp [mem_looplessOn]

theorem simpleOn_empty :
    simpleOn (∅ : Finset (Fin n × Fin d)) = looplessOn (univ : Finset (Fin n × Fin d)) := by
  ext π
  simp [mem_looplessOn, mem_simpleOn]

theorem simpleOn_univ :
    simpleOn (univ : Finset (Fin n × Fin d)) = simplePairings n d := by
  ext π
  rw [mem_simpleOn, mem_simplePairings, IsSimple]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact ⟨fun h p q hpq hπ => h q (mem_univ _) p hpq hπ, fun h z _ z' hz hπ => h z' z hz hπ⟩

/-- **One switching: a prescribed pair is rare among pairings with no loop on `A`.** -/
theorem goodCount_mul_card_looplessOn_filter_le (A : Finset (Fin n × Fin d))
    (q u : Fin n × Fin d) :
    goodCount n d * #{π ∈ looplessOn A | π q = u} ≤ #(looplessOn A) := by
  by_cases hqu : q = u
  · have hempty : ({π ∈ looplessOn A | π q = u} : Finset (Equiv.Perm (Fin n × Fin d))) = ∅ := by
      rw [filter_eq_empty_iff]
      intro π hπ h
      exact (mem_looplessOn.mp hπ).1.2 q (h.trans hqu.symm)
    simp [hempty]
  · refine mul_card_filter_le_of_switch hqu fun π hπ hπq =>
      ⟨good π q u, goodCount_le_card_good π q u, fun x hx => ?_⟩
    obtain ⟨hp, hA⟩ := mem_looplessOn.mp hπ
    have hne := fst_ne_of_mem_good hp hπq hx
    exact ⟨fun h => hne.1 (h ▸ rfl), mem_looplessOn.mpr ⟨isPairing_switch hp u x,
      fun z hz => switch_fst_ne hp hπq hx (hA z hz)⟩⟩

/-- **One switching: a prescribed pair is rare among pairings simple on `B`.** -/
theorem goodCount_mul_card_simpleOn_filter_le (B : Finset (Fin n × Fin d))
    (q u : Fin n × Fin d) :
    goodCount n d * #{π ∈ simpleOn B | π q = u} ≤ #(simpleOn B) := by
  by_cases hqu : q = u
  · have hempty : ({π ∈ simpleOn B | π q = u} : Finset (Equiv.Perm (Fin n × Fin d))) = ∅ := by
      rw [filter_eq_empty_iff]
      intro π hπ h
      exact (mem_simpleOn.mp hπ).1.2 q (h.trans hqu.symm)
    simp [hempty]
  · refine mul_card_filter_le_of_switch hqu fun π hπ hπq =>
      ⟨good π q u, goodCount_le_card_good π q u, fun x hx => ?_⟩
    obtain ⟨hp, hloop, hB⟩ := mem_simpleOn.mp hπ
    have hne := fst_ne_of_mem_good hp hπq hx
    exact ⟨fun h => hne.1 (h ▸ rfl), mem_simpleOn.mpr ⟨isPairing_switch hp u x,
      fun z => switch_fst_ne hp hπq hx (hloop z),
      fun z hz => switch_parallel_free hp hloop hπq hx (hB z hz)⟩⟩

/-- **A second switching: a second prescribed pair at the same vertex is rare** among the
pairings simple on `B` that contain a first prescribed pair `{q, u}`. The switching of the pair
at `q'` does not touch the pair `{q, u}`. -/
theorem goodCount_mul_card_simpleOn_filter_filter_le (B : Finset (Fin n × Fin d))
    {q q' : Fin n × Fin d} (hq : q'.1 = q.1) (hqq : q' ≠ q) (u u' : Fin n × Fin d) :
    goodCount n d * #{π ∈ {π ∈ simpleOn B | π q = u} | π q' = u'}
      ≤ #{π ∈ simpleOn B | π q = u} := by
  by_cases hqu : q' = u'
  · have hempty : ({π ∈ {π ∈ simpleOn B | π q = u} | π q' = u'} :
        Finset (Equiv.Perm (Fin n × Fin d))) = ∅ := by
      rw [filter_eq_empty_iff]
      intro π hπ h
      exact (mem_simpleOn.mp (mem_filter.mp hπ).1).1.2 q' (h.trans hqu.symm)
    simp [hempty]
  · refine mul_card_filter_le_of_switch hqu fun π hπ hπq' =>
      ⟨good π q' u', goodCount_le_card_good π q' u', fun x hx => ?_⟩
    obtain ⟨hπB, hπq⟩ := mem_filter.mp hπ
    obtain ⟨hp, hloop, hB⟩ := mem_simpleOn.mp hπB
    obtain ⟨hxa, -, -, -⟩ := fst_ne_of_mem_good hp hπq' hx
    obtain ⟨-, hna, -⟩ := mem_filter.mp hx
    refine ⟨fun h => hxa (h ▸ rfl), mem_filter.mpr ⟨mem_simpleOn.mpr
      ⟨isPairing_switch hp u' x, fun z => switch_fst_ne hp hπq' hx (hloop z),
        fun z hz => switch_parallel_free hp hloop hπq' hx (hB z hz)⟩, ?_⟩⟩
    have hxq : x ≠ q := fun h => hxa (by rw [h, hq])
    have hxu : x ≠ u := by
      intro h
      apply hna
      rw [h, ← hπq]
      exact fst_apply_mem_near π hq.symm
    have hu'u : u' ≠ u := by
      rw [← hπq, ← hπq']
      exact fun h => hqq (π.injective h)
    have hu'q : u' ≠ q := by
      intro h
      have hqq' : π q = q' := by rw [← h, ← hπq', hp.1]
      exact hloop q (by rw [hqq', hq])
    rw [switch_apply, Equiv.swap_apply_of_ne_of_ne hu'q.symm hxq.symm, hπq,
      Equiv.swap_apply_of_ne_of_ne hu'u.symm hxu.symm]

/-! ## The chain -/

/-- **Forbidding loops at one more point** loses at most a proportion `d / K` of the class. -/
theorem looplessOn_insert_card (A : Finset (Fin n × Fin d)) (q : Fin n × Fin d) :
    (goodCount n d - d) * #(looplessOn A) ≤ goodCount n d * #(looplessOn (insert q A)) := by
  have hsub : looplessOn (insert q A) ⊆ looplessOn A := fun π hπ => by
    rw [mem_looplessOn] at hπ ⊢
    exact ⟨hπ.1, fun z hz => hπ.2 z (mem_insert_of_mem hz)⟩
  have hdiff : looplessOn A \ looplessOn (insert q A) ⊆
      (univ : Finset (Fin d)).biUnion fun i => {π ∈ looplessOn A | π q = (q.1, i)} := by
    intro π hπ
    obtain ⟨hπA, hπn⟩ := mem_sdiff.mp hπ
    have hloop : (π q).1 = q.1 := by
      by_contra h
      refine hπn (mem_looplessOn.mpr ⟨(mem_looplessOn.mp hπA).1, fun z hz => ?_⟩)
      rcases mem_insert.mp hz with hzq | hz
      · rw [hzq]
        exact h
      · exact (mem_looplessOn.mp hπA).2 z hz
    exact mem_biUnion.mpr ⟨(π q).2, mem_univ _, mem_filter.mpr ⟨hπA, Prod.ext hloop rfl⟩⟩
  have hcard : goodCount n d * #(looplessOn A \ looplessOn (insert q A))
      ≤ d * #(looplessOn A) := by
    calc goodCount n d * #(looplessOn A \ looplessOn (insert q A))
        ≤ goodCount n d * ∑ i : Fin d, #{π ∈ looplessOn A | π q = (q.1, i)} :=
          Nat.mul_le_mul_left _ ((card_le_card hdiff).trans card_biUnion_le)
      _ = ∑ i : Fin d, goodCount n d * #{π ∈ looplessOn A | π q = (q.1, i)} := by
          rw [mul_sum]
      _ ≤ ∑ _i : Fin d, #(looplessOn A) :=
          sum_le_sum fun i _ => goodCount_mul_card_looplessOn_filter_le A q _
      _ = d * #(looplessOn A) := by simp
  have hsplit := card_sdiff_add_card_eq_card hsub
  have hmul : goodCount n d * #(looplessOn A)
      = goodCount n d * #(looplessOn A \ looplessOn (insert q A))
        + goodCount n d * #(looplessOn (insert q A)) := by
    rw [← Nat.mul_add, hsplit]
  rw [Nat.sub_mul]
  omega

/-- **Forbidding repeated edges at one more point** loses at most a proportion `n d³ / K²` of
the class. -/
theorem simpleOn_insert_card (B : Finset (Fin n × Fin d)) (q : Fin n × Fin d) :
    (goodCount n d ^ 2 - n * d * d * d) * #(simpleOn B)
      ≤ goodCount n d ^ 2 * #(simpleOn (insert q B)) := by
  have hsub : simpleOn (insert q B) ⊆ simpleOn B := fun π hπ => by
    rw [mem_simpleOn] at hπ ⊢
    exact ⟨hπ.1, hπ.2.1, fun z hz => hπ.2.2 z (mem_insert_of_mem hz)⟩
  -- The index set of the events `π q = u ∧ π q' = u'`: the point `u`, and the second
  -- coordinates of `q'` (a point of the vertex of `q`) and `u'` (a point of the vertex of `u`).
  let I : Finset ((Fin n × Fin d) × Fin d × Fin d) := {t | (q.1, t.2.1) ≠ q}
  have hdiff : simpleOn B \ simpleOn (insert q B) ⊆
      I.biUnion fun t =>
        {π ∈ {π ∈ simpleOn B | π q = t.1} | π (q.1, t.2.1) = (t.1.1, t.2.2)} := by
    intro π hπ
    obtain ⟨hπB, hπn⟩ := mem_sdiff.mp hπ
    obtain ⟨hp, hloop, hB⟩ := mem_simpleOn.mp hπB
    have hex : ∃ z', z'.1 = q.1 ∧ (π z').1 = (π q).1 ∧ z' ≠ q := by
      by_contra h
      push Not at h
      refine hπn (mem_simpleOn.mpr ⟨hp, hloop, fun z hz => ?_⟩)
      rcases mem_insert.mp hz with hzq | hz
      · rw [hzq]
        exact h
      · exact hB z hz
    obtain ⟨z', h1, h2, h3⟩ := hex
    have hz' : (q.1, z'.2) = z' := Prod.ext h1.symm rfl
    refine mem_biUnion.mpr ⟨(π q, z'.2, (π z').2), mem_filter.mpr ⟨mem_univ _, ?_⟩,
      mem_filter.mpr ⟨mem_filter.mpr ⟨hπB, rfl⟩, ?_⟩⟩
    · change (q.1, z'.2) ≠ q
      rw [hz']
      exact h3
    · change π (q.1, z'.2) = ((π q).1, (π z').2)
      rw [hz']
      exact Prod.ext h2 rfl
  have hI : #I ≤ n * d * d * d := by
    calc #I ≤ Fintype.card ((Fin n × Fin d) × Fin d × Fin d) := card_le_univ _
      _ = n * d * d * d := by simp [mul_assoc]
  have hterm : ∀ t ∈ I, goodCount n d ^ 2 *
      #{π ∈ {π ∈ simpleOn B | π q = t.1} | π (q.1, t.2.1) = (t.1.1, t.2.2)} ≤ #(simpleOn B) := by
    intro t ht
    have h1 := goodCount_mul_card_simpleOn_filter_filter_le B (q := q) (q' := (q.1, t.2.1)) rfl
      (mem_filter.mp ht).2 t.1 (t.1.1, t.2.2)
    have h2 := goodCount_mul_card_simpleOn_filter_le B q t.1
    calc goodCount n d ^ 2 *
          #{π ∈ {π ∈ simpleOn B | π q = t.1} | π (q.1, t.2.1) = (t.1.1, t.2.2)}
        = goodCount n d * (goodCount n d *
          #{π ∈ {π ∈ simpleOn B | π q = t.1} | π (q.1, t.2.1) = (t.1.1, t.2.2)}) := by ring
      _ ≤ goodCount n d * #{π ∈ simpleOn B | π q = t.1} := Nat.mul_le_mul_left _ h1
      _ ≤ #(simpleOn B) := h2
  have hcard : goodCount n d ^ 2 * #(simpleOn B \ simpleOn (insert q B))
      ≤ n * d * d * d * #(simpleOn B) := by
    calc goodCount n d ^ 2 * #(simpleOn B \ simpleOn (insert q B))
        ≤ goodCount n d ^ 2 * ∑ t ∈ I,
          #{π ∈ {π ∈ simpleOn B | π q = t.1} | π (q.1, t.2.1) = (t.1.1, t.2.2)} :=
          Nat.mul_le_mul_left _ ((card_le_card hdiff).trans card_biUnion_le)
      _ = ∑ t ∈ I, goodCount n d ^ 2 *
          #{π ∈ {π ∈ simpleOn B | π q = t.1} | π (q.1, t.2.1) = (t.1.1, t.2.2)} := by
          rw [mul_sum]
      _ ≤ ∑ _t ∈ I, #(simpleOn B) := sum_le_sum hterm
      _ = #I * #(simpleOn B) := by simp
      _ ≤ n * d * d * d * #(simpleOn B) := Nat.mul_le_mul_right _ hI
  have hsplit := card_sdiff_add_card_eq_card hsub
  have hmul : goodCount n d ^ 2 * #(simpleOn B)
      = goodCount n d ^ 2 * #(simpleOn B \ simpleOn (insert q B))
        + goodCount n d ^ 2 * #(simpleOn (insert q B)) := by
    rw [← Nat.mul_add, hsplit]
  rw [Nat.sub_mul]
  omega

/-- Chaining `looplessOn_insert_card` over the points of `A`. -/
theorem pow_mul_card_pairings_le (A : Finset (Fin n × Fin d)) :
    (goodCount n d - d) ^ #A * #(pairings n d) ≤ goodCount n d ^ #A * #(looplessOn A) := by
  induction A using Finset.induction_on with
  | empty => simp [looplessOn_empty]
  | insert q A hq ih =>
    rw [card_insert_of_notMem hq, pow_succ, pow_succ]
    calc (goodCount n d - d) ^ #A * (goodCount n d - d) * #(pairings n d)
        = (goodCount n d - d) * ((goodCount n d - d) ^ #A * #(pairings n d)) := by ring
      _ ≤ (goodCount n d - d) * (goodCount n d ^ #A * #(looplessOn A)) :=
          Nat.mul_le_mul_left _ ih
      _ = goodCount n d ^ #A * ((goodCount n d - d) * #(looplessOn A)) := by ring
      _ ≤ goodCount n d ^ #A * (goodCount n d * #(looplessOn (insert q A))) :=
          Nat.mul_le_mul_left _ (looplessOn_insert_card A q)
      _ = goodCount n d ^ #A * goodCount n d * #(looplessOn (insert q A)) := by ring

/-- Chaining `simpleOn_insert_card` over the points of `B`. -/
theorem pow_mul_card_looplessOn_le (B : Finset (Fin n × Fin d)) :
    (goodCount n d ^ 2 - n * d * d * d) ^ #B * #(looplessOn (univ : Finset (Fin n × Fin d)))
      ≤ (goodCount n d ^ 2) ^ #B * #(simpleOn B) := by
  induction B using Finset.induction_on with
  | empty => simp [simpleOn_empty]
  | insert q B hq ih =>
    rw [card_insert_of_notMem hq, pow_succ, pow_succ]
    calc (goodCount n d ^ 2 - n * d * d * d) ^ #B * (goodCount n d ^ 2 - n * d * d * d)
          * #(looplessOn (univ : Finset (Fin n × Fin d)))
        = (goodCount n d ^ 2 - n * d * d * d) * ((goodCount n d ^ 2 - n * d * d * d) ^ #B
          * #(looplessOn (univ : Finset (Fin n × Fin d)))) := by ring
      _ ≤ (goodCount n d ^ 2 - n * d * d * d) * ((goodCount n d ^ 2) ^ #B * #(simpleOn B)) :=
          Nat.mul_le_mul_left _ ih
      _ = (goodCount n d ^ 2) ^ #B
          * ((goodCount n d ^ 2 - n * d * d * d) * #(simpleOn B)) := by ring
      _ ≤ (goodCount n d ^ 2) ^ #B * (goodCount n d ^ 2 * #(simpleOn (insert q B))) :=
          Nat.mul_le_mul_left _ (simpleOn_insert_card B q)
      _ = (goodCount n d ^ 2) ^ #B * goodCount n d ^ 2 * #(simpleOn (insert q B)) := by ring

/-- **The switching bound.** With `K = n d - 2d(d + 1)`,

`((K - d) * (K² - n d³)) ^ (n d) * #{pairings} ≤ (K * K²) ^ (n d) * #{simple pairings}`.

All subtractions are truncated, so the statement is true, and trivial, when `n` is small. -/
theorem switching_card_bound (n d : ℕ) :
    ((goodCount n d - d) * (goodCount n d ^ 2 - n * d * d * d)) ^ (n * d) * #(pairings n d)
      ≤ (goodCount n d * goodCount n d ^ 2) ^ (n * d) * #(simplePairings n d) := by
  have h1 := pow_mul_card_pairings_le (univ : Finset (Fin n × Fin d))
  have h2 := pow_mul_card_looplessOn_le (univ : Finset (Fin n × Fin d))
  rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h1 h2
  rw [simpleOn_univ] at h2
  calc ((goodCount n d - d) * (goodCount n d ^ 2 - n * d * d * d)) ^ (n * d) * #(pairings n d)
      = (goodCount n d ^ 2 - n * d * d * d) ^ (n * d)
        * ((goodCount n d - d) ^ (n * d) * #(pairings n d)) := by rw [mul_pow]; ring
    _ ≤ (goodCount n d ^ 2 - n * d * d * d) ^ (n * d) * (goodCount n d ^ (n * d)
        * #(looplessOn (univ : Finset (Fin n × Fin d)))) := Nat.mul_le_mul_left _ h1
    _ = goodCount n d ^ (n * d) * ((goodCount n d ^ 2 - n * d * d * d) ^ (n * d)
        * #(looplessOn (univ : Finset (Fin n × Fin d)))) := by ring
    _ ≤ goodCount n d ^ (n * d) * ((goodCount n d ^ 2) ^ (n * d) * #(simplePairings n d)) :=
        Nat.mul_le_mul_left _ h2
    _ = (goodCount n d * goodCount n d ^ 2) ^ (n * d) * #(simplePairings n d) := by
        rw [mul_pow]; ring

end ConfigurationModel
