/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.CompleteComplex

/-!
# Rigidity in the negative regime: negative local expansion forces the complete complex

`trickling_down` and `IsLocalSpectralExpander` allow a negative bound `lam` on the second
eigenvalue of the random walk on the links, and the complete complex realises it
(`isLocalSpectralExpander_complete_fin5_two`). This file shows that, up to the choice of vertex
set, the complete complex is the *only* complex with negative local expansion. The engine is an
elementary fact about weighted graphs: if the random walk has second eigenvalue `lam < 0`, then
any two vertices of positive degree are joined by an edge of positive weight. Applied to the
links, this closes pairs up to triples, and an induction fills in every set of at most `d + 1`
vertices.

Throughout, `n = Fintype.card ι` is the number of available points, and a complex `K` "on all of
`ι`" means `∀ v, {v} ∈ K`.

## Definitions
* `PreAbstractSimplicialComplex.twoTriangles`: two triangles `{0, 1, 2}` and `{0, 1, 3}` sharing
  the edge `{0, 1}`, a complex on `Fin 4`. It shows that `lam < 0` cannot be relaxed to `lam ≤ 0`.

## Theorems
Weighted graphs (no sign condition on the weights):
* `WalkSecondEigenvalueLE.neg_two_mul_weight_le`: for distinct vertices `u, v` of positive degree,
  `−2 w(u, v) ≤ lam · (deg u + deg v)`. **Proved.**
* `WalkSecondEigenvalueLE.weight_pos_of_neg`: so if `lam < 0`, every two distinct vertices of
  positive degree are adjacent. **Proved.**
* `WalkSecondEigenvalueLE.neg_one_div_le_of_support`: the trace bound `lam ≥ −1/(N − 1)`, where
  the weights live on a set of `N ≥ 2` vertices, all of positive degree. **Proved.**

Rigidity:
* `IsTopWeight.mem_of_trickling_down_neg`, `IsTopWeight.eq_complete_of_trickling_down_neg`: under
  the hypotheses of `trickling_down_weighted` (dimension `d ≥ 2`, connected links of the faces of
  dimension at most `d − 3` and of `K` itself), if the link of every `(d − 2)`-face has some
  negative second-eigenvalue bound, then every set of at most `d + 1` vertices of `K` is a face.
  On all of `ι`, `K = complete ι d`. **Proved.**
* `mem_of_trickling_down_neg`, `eq_complete_of_trickling_down_neg`: the same for the counting
  weights of `trickling_down`. **Proved.**
* `IsLocalSpectralExpanderOf.mem_of_neg`, `IsLocalSpectralExpanderOf.eq_complete_of_neg`,
  `IsLocalSpectralExpander.mem_of_neg`, `IsLocalSpectralExpander.eq_complete_of_neg`: a
  `lam`-local-spectral expander with `lam < 0` is complete on its vertices, in every dimension
  `d ≥ 1` and with no connectivity hypothesis. **Proved.**

The complete complex:
* `walkSecondEigenvalueLE_complete_codimTwo_link_iff`: in `complete ι d` with `n ≥ d + 1`, the link
  of a `(d − 2)`-dimensional set has second eigenvalue exactly `−1/(n − d)`. **Proved.**
* `complete_isLocalSpectralExpander_iff`: `complete ι d` is a `lam`-local-spectral expander exactly
  when `lam ≥ −1/(n − 1)`. **Proved.**
* `trickling_down_hypotheses_neg_iff`: for `d ≥ 2` and `lam < 0`, a complex on all of `ι` meets the
  hypotheses of `trickling_down` with bound `lam` exactly when it is `complete ι d`, `n ≥ d + 1`
  and `lam ≥ −1/(n − d)`. **Proved.**
* `exists_neg_isLocalSpectralExpander_iff`: for `d ≥ 1`, a complex on all of `ι` is a
  `lam`-local-spectral expander for some `lam < 0` exactly when it is `complete ι d` and
  `n ≥ d + 1`. **Proved.**

Sharpness:
* `twoTriangles_sharp_at_zero`: `twoTriangles` is pure of dimension `2`, connected, on all of
  `Fin 4`, and both of its vertex links have second eigenvalue at most `0`; but `{2, 3}` is not a
  face, so it is not `complete (Fin 4) 2`. **Proved.**

## References
* V. L. Alev and L. C. Lau, *Improved analysis of higher order random walks and applications*,
  STOC 2020, arXiv:2001.02827, §1: "`λ₂(G) ≤ 0` only if `G` is a complete multi-partite graph,
  and more generally a `0`-local-expander is a weighted matroid complex". The graph statement is
  due to C. Godsil (Math StackExchange 2527245); the complex statement is from P. Brändén and
  J. Huh, *Lorentzian polynomials*, Ann. of Math. 2020.
* N. Anari, K. Liu, S. Oveis Gharan and C. Vinzant, *Log-concave polynomials II*,
  arXiv:1811.01816: matroid complexes are `0`-local spectral expanders.
* J. H. Smith, *Some properties of the spectrum of a graph* (1970): the second adjacency
  eigenvalue of a graph is negative exactly when the graph is complete.
* I. Oppenheim, *Local spectral expansion approach to high dimensional expanders, Part I*,
  arXiv:1407.8517: trickling down.
* L. C. Lau, CS860 lecture notes (Waterloo, 2022), *Higher order random walks*.

The strict-negative rigidity statement is not stated explicitly in these sources; it follows from
the `λ ≤ 0` characterisation (the complete `d`-complex is the independence complex of the uniform
matroid `U_{d+1,n}`), but the proof here is the elementary one above and is self-contained.
-/

open Finset

variable {ι : Type*} [Fintype ι]

/-! ### Weighted graphs with a negative second eigenvalue -/

/-- **The edge inequality.** If the random walk on a weighted graph `w` with symmetric weights and
no loops has second eigenvalue at most `lam`, then for distinct vertices `u, v` of positive degree,
`−2 w(u, v) ≤ lam · (deg u + deg v)`, where `deg u = Σ_x w(u, x)`.

The weights need not be nonnegative. The test function is `deg v` at `u`, `−deg u` at `v` and `0`
elsewhere: it has degree-weighted mean zero, quadratic form `−2 deg u deg v · w(u, v)` and
degree-weighted norm `deg u deg v (deg u + deg v)`. Positivity of both degrees is what allows
dividing by `deg u · deg v`; if either degree is `0` the test function says nothing. For `u = v`
the conclusion would read `0 ≤ 2 lam · deg u`, which is false when `lam < 0`, so `u ≠ v` is
needed. -/
theorem WalkSecondEigenvalueLE.neg_two_mul_weight_le {w : ι → ι → ℝ} {lam : ℝ}
    (h : WalkSecondEigenvalueLE w lam) (hsymm : ∀ u v, w u v = w v u) (hdiag : ∀ u, w u u = 0)
    {u v : ι} (huv : u ≠ v) (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) :
    -(2 * w u v) ≤ lam * ((∑ x, w u x) + ∑ x, w v x) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, a = ∑ x, w u x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ∑ x, w v x := ⟨_, rfl⟩
  rw [← ha] at hu ⊢
  rw [← hb] at hv ⊢
  -- the test function: `b` at `u`, `−a` at `v`, `0` elsewhere
  obtain ⟨f, hf⟩ : ∃ f : ι → ℝ, f = fun x => if x = u then b else if x = v then -a else 0 :=
    ⟨_, rfl⟩
  have hfu : f u = b := by rw [hf]; exact if_pos rfl
  have hfv : f v = -a := by rw [hf]; simp [huv.symm]
  have hf0 : ∀ x, x ≠ u ∧ x ≠ v → f x = 0 := fun x hx => by rw [hf]; simp [hx.1, hx.2]
  have hmean : ∑ x, (∑ y, w x y) * f x = 0 := by
    rw [Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) huv
      fun x _ hx => by rw [hf0 x hx, mul_zero], hfu, hfv, ← ha, ← hb]
    ring
  have hnorm : ∑ x, (∑ y, w x y) * f x ^ 2 = a * b * (a + b) := by
    rw [Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) huv
      fun x _ hx => by rw [hf0 x hx]; ring, hfu, hfv, ← ha, ← hb]
    ring
  have hrow : ∀ x, ∑ y, w x y * f x * f y = w x u * f x * f u + w x v * f x * f v := fun x =>
    Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) huv
      fun y _ hy => by rw [hf0 y hy, mul_zero]
  have hquad : ∑ x, ∑ y, w x y * f x * f y = a * b * (-(2 * w u v)) := by
    simp only [hrow]
    rw [Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) huv
      fun x _ hx => by rw [hf0 x hx]; ring, hfu, hfv, hdiag u, hdiag v, hsymm v u]
    ring
  have h1 := h f hmean
  rw [hquad, hnorm] at h1
  have hab : 0 < a * b := mul_pos hu hv
  refine le_of_mul_le_mul_left ?_ hab
  linarith

/-- **A negative second eigenvalue forces a complete graph.** If the random walk on a weighted
graph `w` with symmetric weights and no loops has second eigenvalue at most `lam < 0`, then any two
distinct vertices of positive degree are joined by an edge of positive weight: the graph is
complete on its vertices of positive degree. The weights need not be nonnegative.

The bound must be strictly negative: the path `u − x − v` with unit weights has second eigenvalue
`0`, and `w(u, v) = 0`. Vertices of degree `0` are not constrained (compare the docstring of
`WalkSecondEigenvalueLE`). -/
theorem WalkSecondEigenvalueLE.weight_pos_of_neg {w : ι → ι → ℝ} {lam : ℝ}
    (h : WalkSecondEigenvalueLE w lam) (hsymm : ∀ u v, w u v = w v u) (hdiag : ∀ u, w u u = 0)
    (hlam : lam < 0) {u v : ι} (huv : u ≠ v) (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) :
    0 < w u v := by
  have h1 := h.neg_two_mul_weight_le hsymm hdiag huv hu hv
  have h2 : lam * ((∑ x, w u x) + ∑ x, w v x) < 0 := mul_neg_of_neg_of_pos hlam (by linarith)
  linarith

/-- **The trace bound.** Let the weights of `w` (symmetric, no loops) live on a set `P` of at least
two vertices, each of positive degree: `w x y = 0` whenever `x ∉ P`. If the random walk has second
eigenvalue at most `lam`, then `lam ≥ −1/(#P − 1)`, the second eigenvalue of the complete graph on
`P`. The weights need not be nonnegative.

The proof sums `neg_two_mul_weight_le` over all ordered pairs of distinct vertices of `P`. The
subtraction `#P − 1` is taken in `ℝ`, and it is at least `1`. The hypothesis `2 ≤ #P` excludes
`P = ∅`, where every weight is `0`, every `lam` is allowed, and the formula would read
`−(1/(−1)) = 1`. (A one-element `P` cannot meet the other hypotheses: its vertex would have
degree `w x x = 0`.) -/
theorem WalkSecondEigenvalueLE.neg_one_div_le_of_support [DecidableEq ι] {w : ι → ι → ℝ}
    {lam : ℝ} (h : WalkSecondEigenvalueLE w lam) (hsymm : ∀ u v, w u v = w v u)
    (hdiag : ∀ u, w u u = 0) {P : Finset ι} (hP : 2 ≤ #P) (hpos : ∀ x ∈ P, 0 < ∑ y, w x y)
    (hout : ∀ x y, x ∉ P → w x y = 0) : -(1 / ((#P : ℝ) - 1)) ≤ lam := by
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ x ∈ P, ∑ y, w x y := ⟨_, rfl⟩
  have hdeg : ∀ u, ∑ v ∈ P, w u v = ∑ v, w u v := fun u =>
    Finset.sum_subset (subset_univ P) fun v _ hv => by rw [hsymm]; exact hout v u hv
  have hcardR : ∀ u ∈ P, ((#(P.erase u) : ℕ) : ℝ) = (#P : ℝ) - 1 := fun u hu => by
    rw [card_erase_of_mem hu, Nat.cast_sub (by omega), Nat.cast_one]
  -- summing the edge inequality over the vertices `v ≠ u` of `P`
  have key : ∀ u ∈ P, -(2 * ∑ y, w u y) ≤ lam * (((#P : ℝ) - 2) * ∑ y, w u y + D) := by
    intro u hu
    have h1 : ∀ v ∈ P.erase u, -(2 * w u v) ≤ lam * ((∑ y, w u y) + ∑ y, w v y) := fun v hv =>
      h.neg_two_mul_weight_le hsymm hdiag (Finset.ne_of_mem_erase hv).symm (hpos u hu)
        (hpos v (Finset.mem_of_mem_erase hv))
    have h2 := Finset.sum_le_sum h1
    have e1 : ∑ v ∈ P.erase u, -(2 * w u v) = -(2 * ∑ y, w u y) := by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_erase_eq_sub hu, hdiag, sub_zero,
        hdeg]
    have e2 : ∑ v ∈ P.erase u, lam * ((∑ y, w u y) + ∑ y, w v y) =
        lam * (((#P : ℝ) - 2) * ∑ y, w u y + D) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcardR u hu,
        Finset.sum_erase_eq_sub hu, ← hD]
      ring
    rw [e1, e2] at h2
    exact h2
  -- and then over `u ∈ P`
  have h3 := Finset.sum_le_sum key
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← hD, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← hD, Finset.sum_const, nsmul_eq_mul] at h3
  have hD0 : 0 < D := by
    rw [hD]
    obtain ⟨x, hx⟩ : P.Nonempty := card_pos.mp (by omega)
    exact Finset.sum_pos hpos ⟨x, hx⟩
  have hc : (1 : ℝ) ≤ (#P : ℝ) - 1 := by
    have : (2 : ℝ) ≤ #P := by exact_mod_cast hP
    linarith
  have h4 : (-1) * (2 * D) ≤ (lam * ((#P : ℝ) - 1)) * (2 * D) := by linarith
  have h5 := le_of_mul_le_mul_right h4 (by linarith)
  rw [neg_le, le_div_iff₀ (by linarith)]
  linarith

namespace PreAbstractSimplicialComplex

variable [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ}
  {lam : ℝ}

/-! ### Closing pairs to triples, and filling -/

/-- In the link of `τ`, any two vertices span an edge: whenever `u ≠ v` lie outside `τ` and
`τ ∪ {u}`, `τ ∪ {v}` are faces, so is `τ ∪ {u, v}`. -/
private def PairClosed (K : PreAbstractSimplicialComplex ι) (τ : Finset ι) : Prop :=
  ∀ u v, u ≠ v → u ∉ τ → v ∉ τ → insert u τ ∈ K → insert v τ ∈ K → insert u (insert v τ) ∈ K

/-- A vertex of the link of a set `τ` of dimension at most `d − 2` has positive degree in its
weighted graph. -/
private theorem IsTopWeight.sum_linkWeightOf_pos_of_insert_mem (hm : K.IsTopWeight d m)
    {τ : Finset ι} (hτ : #τ + 1 ≤ d) {u : ι} (hu : u ∉ τ) (huK : insert u τ ∈ K) :
    0 < ∑ x, linkWeightOf m τ u x := by
  rw [sum_linkWeightOf hm.card_eq_of_ne_zero, if_neg hu]
  have hc : (0 : ℝ) < (d : ℝ) - #τ := by
    have : ((#τ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hτ
    push_cast at this
    linarith
  obtain ⟨-, F, hF, hsub, hcard⟩ := hm.isPure _ huK
  exact mul_pos hc (hm.faceWeight_pos_iff.mpr ⟨F, hF, hcard, hsub⟩)

/-- A link with a negative second-eigenvalue bound is complete. -/
private theorem IsTopWeight.pairClosed_of_neg (hm : K.IsTopWeight d m) {τ : Finset ι}
    (hτ : #τ + 1 ≤ d) (hlam : lam < 0) (hw : WalkSecondEigenvalueLE (linkWeightOf m τ) lam) :
    PairClosed K τ := by
  intro u v huv hu hv huK hvK
  have hpos := hw.weight_pos_of_neg (linkWeightOf_symm m τ) (linkWeightOf_self m τ) hlam huv
    (hm.sum_linkWeightOf_pos_of_insert_mem hτ hu huK)
    (hm.sum_linkWeightOf_pos_of_insert_mem hτ hv hvK)
  obtain ⟨-, -, -, F, hF, -, hsub⟩ := hm.linkWeightOf_pos_iff.mp hpos
  exact K.mem_of_subset hF hsub (insert_nonempty _ _)

omit [Fintype ι] in
/-- If the link of `τ` is connected and the link of every face `τ ∪ {a}` is complete, then the
link of `τ` is complete: walk from `u` to `v` along the link of `τ`, keeping `τ ∪ {u, b}` a face
for the current vertex `b`. -/
private theorem pairClosed_of_isConnected_link {τ : Finset ι} (hconn : (K.link τ).IsConnected)
    (hQ : ∀ a, a ∉ τ → insert a τ ∈ K → PairClosed K (insert a τ)) : PairClosed K τ := by
  intro u v huv hu hv huK hvK
  have hvert : ∀ x, x ∉ τ → insert x τ ∈ K → x ∈ (K.link τ).vertices := fun x hx hxK =>
    mem_link.mpr ⟨singleton_nonempty x, disjoint_singleton_left.mpr hx, by
      rwa [singleton_union]⟩
  have hreach := hconn.preconnected ⟨u, hvert u hu huK⟩ ⟨v, hvert v hv hvK⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have key : ∀ b : (K.link τ).vertices,
      Relation.ReflTransGen ((K.link τ).oneSkeleton.induce (K.link τ).vertices).Adj
        ⟨u, hvert u hu huK⟩ b → (b : ι) = u ∨ insert u (insert (b : ι) τ) ∈ K := by
    intro b hb
    induction hb with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      have hadj := SimpleGraph.comap_adj.mp hbc
      rw [oneSkeleton, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨hne, hbc'⟩ := hadj
      have hpair : ({(b : ι), (c : ι)} : Finset ι) ∈ K.link τ :=
        hbc'.elim id fun h => by rwa [pair_comm]
      obtain ⟨-, hdisj, hmem⟩ := mem_link.mp hpair
      have hbτ : (b : ι) ∉ τ := disjoint_left.mp hdisj (mem_insert_self _ _)
      have hcτ : (c : ι) ∉ τ := disjoint_left.mp hdisj (by simp)
      have hmem' : insert (b : ι) (insert (c : ι) τ) ∈ K := by
        rwa [insert_union, singleton_union] at hmem
      by_cases hcu : (c : ι) = u
      · exact Or.inl hcu
      right
      by_cases hbu : (b : ι) = u
      · rwa [hbu] at hmem'
      have ih' := ih.resolve_left hbu
      have hbK : insert (b : ι) τ ∈ K :=
        K.mem_of_subset hmem' (insert_subset_insert _ (subset_insert _ _)) (insert_nonempty _ _)
      have h3 := hQ b hbτ hbK u c (Ne.symm hcu)
        (by rw [mem_insert, not_or]; exact ⟨Ne.symm hbu, hu⟩)
        (by rw [mem_insert, not_or]; exact ⟨Ne.symm hne, hcτ⟩) ih'
        (by rwa [insert_comm])
      refine K.mem_of_subset h3 ?_ (insert_nonempty _ _)
      exact insert_subset_insert _ (insert_subset_insert _ (subset_insert _ _))
  exact (key _ hreach).resolve_left huv.symm

omit [Fintype ι] in
/-- **Filling.** If the link of every face of dimension at most `d − 2` (and of `∅`) is complete,
then every nonempty set of at most `d + 1` vertices of `K` is a face. By strong induction on the
size of `s`: remove two points `u ≠ v` to get `τ`; then `τ ∪ {u}` and `τ ∪ {v}` are faces by
induction, and `s = τ ∪ {u, v}`. -/
private theorem mem_of_pairClosed
    (hQ : ∀ τ : Finset ι, (τ = ∅ ∨ τ ∈ K) → #τ + 1 ≤ d → PairClosed K τ) {s : Finset ι}
    (hs : s.Nonempty) (hsV : ∀ v ∈ s, {v} ∈ K) (hcard : #s ≤ d + 1) : s ∈ K := by
  obtain ⟨n, hn⟩ : ∃ n, #s = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rcases le_or_gt #s 1 with h1 | h1
    · obtain ⟨v, rfl⟩ := card_eq_one.mp (le_antisymm h1 (card_pos.mpr hs))
      exact hsV v (mem_singleton_self v)
    obtain ⟨u, v, hu, hv, huv⟩ := one_lt_card_iff.mp h1
    have hvu : v ∈ s.erase u := mem_erase.mpr ⟨huv.symm, hv⟩
    have huv' : u ∈ s.erase v := mem_erase.mpr ⟨huv, hu⟩
    have hsu : s.erase u ∈ K :=
      ih _ (by rw [← hn, card_erase_of_mem hu]; omega) ⟨v, hvu⟩
        (fun x hx => hsV x (mem_of_mem_erase hx))
        (by rw [card_erase_of_mem hu]; omega) rfl
    have hsv : s.erase v ∈ K :=
      ih _ (by rw [← hn, card_erase_of_mem hv]; omega) ⟨u, huv'⟩
        (fun x hx => hsV x (mem_of_mem_erase hx))
        (by rw [card_erase_of_mem hv]; omega) rfl
    set τ := (s.erase u).erase v with hτ
    have hτ' : τ = (s.erase v).erase u := erase_right_comm
    have hτK : τ = ∅ ∨ τ ∈ K := by
      rcases τ.eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · exact Or.inr (K.mem_of_subset hsu (erase_subset _ _) h)
    have hτcard : #τ + 1 ≤ d := by
      rw [hτ, card_erase_of_mem hvu, card_erase_of_mem hu]
      omega
    have hins_u : insert u τ = s.erase v := by rw [hτ', insert_erase huv']
    have hins_v : insert v τ = s.erase u := by rw [hτ, insert_erase hvu]
    have := hQ τ hτK hτcard u v huv
      (by rw [hτ', mem_erase]; exact fun h => h.1 rfl)
      (by rw [hτ, mem_erase]; exact fun h => h.1 rfl)
      (by rw [hins_u]; exact hsv) (by rw [hins_v]; exact hsu)
    rwa [hins_v, insert_erase hu] at this

omit [Fintype ι] [DecidableEq ι] in
private theorem eq_complete_of_forall_mem (hpure : K.IsPure d)
    (hmem : ∀ s : Finset ι, s.Nonempty → (∀ v ∈ s, {v} ∈ K) → #s ≤ d + 1 → s ∈ K)
    (hV : ∀ v, {v} ∈ K) : K = complete ι d :=
  SetLike.ext fun s => ⟨fun hs => mem_complete.mpr ⟨K.nonempty_of_mem hs, (hpure s hs).1⟩,
    fun hs => hmem s (mem_complete.mp hs).1 (fun v _ => hV v) (mem_complete.mp hs).2⟩

/-! ### Rigidity -/

/-- **Negative trickling down is rigid (weighted form).** Let `m` be a top weight of the
`d`-dimensional complex `K`, `d ≥ 2`, in which `K` itself and the link of every face of dimension
at most `d − 3` is connected (the connectivity hypothesis of `trickling_down_weighted`). If the
link of every `(d − 2)`-dimensional face has *some* negative bound on its second eigenvalue (the
bound may depend on the face), then every nonempty set `s` of at most `d + 1` vertices of `K` is a
face of `K`.

Proof: a link with a negative bound is a complete graph (`weight_pos_of_neg`), so pairs close up to
triples in the links of `(d − 2)`-faces; connectivity carries this down to the links of smaller
faces and to `K`; and then every set of at most `d + 1` vertices is filled in, two points at a time.

Degenerate cases:
* `d = 1` is excluded. Then no `σ` has `#σ + 2 ≤ d` and no face has `#σ + 1 = d` (faces are
  nonempty), so both hypotheses are vacuous, while a path is a pure `1`-dimensional complex that
  is not complete.
* `d = 0` is excluded as well, to match `trickling_down_weighted`; there the conclusion is
  trivial, since `s` is a single vertex.
* The vertices of `s` must be vertices of `K` (`hsV`), and `s = ∅` is not a face.
* The bound must be strictly negative: `twoTriangles_sharp_at_zero`. -/
theorem IsTopWeight.mem_of_trickling_down_neg (hm : K.IsTopWeight d m) (hd : 2 ≤ d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    (hneg : ∀ σ ∈ K, #σ + 1 = d → ∃ lam < 0, WalkSecondEigenvalueLE (linkWeightOf m σ) lam)
    {s : Finset ι} (hs : s.Nonempty) (hsV : ∀ v ∈ s, {v} ∈ K) (hcard : #s ≤ d + 1) : s ∈ K := by
  -- downward induction on `j = d − 1 − |τ|`
  have key : ∀ j : ℕ, ∀ τ : Finset ι, (τ = ∅ ∨ τ ∈ K) → #τ + 1 + j = d → PairClosed K τ := by
    intro j
    induction j with
    | zero =>
      intro τ hτ hc
      have hτK : τ ∈ K := hτ.resolve_left (by rintro rfl; rw [card_empty] at hc; omega)
      obtain ⟨lam, hlam, hw⟩ := hneg τ hτK (by omega)
      exact hm.pairClosed_of_neg (by omega) hlam hw
    | succ j ih =>
      intro τ hτ hc
      exact pairClosed_of_isConnected_link (hconn τ hτ (by omega)) fun a ha haK =>
        ih _ (Or.inr haK) (by rw [card_insert_of_notMem ha]; omega)
  refine mem_of_pairClosed (fun τ hτ hc => ?_) hs hsV hcard
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hc
  exact key j τ hτ hj.symm

/-- **Negative trickling down forces the complete complex (weighted form).** Under the hypotheses
of `IsTopWeight.mem_of_trickling_down_neg`, a complex in which every point of `ι` is a vertex is
the complete complex `complete ι d`. -/
theorem IsTopWeight.eq_complete_of_trickling_down_neg (hm : K.IsTopWeight d m) (hd : 2 ≤ d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    (hneg : ∀ σ ∈ K, #σ + 1 = d → ∃ lam < 0, WalkSecondEigenvalueLE (linkWeightOf m σ) lam)
    (hV : ∀ v, {v} ∈ K) : K = complete ι d :=
  eq_complete_of_forall_mem hm.isPure
    (fun _ hs hsV hcard => hm.mem_of_trickling_down_neg hd hconn hneg hs hsV hcard) hV

/-- **Negative local spectral expanders are complete (weighted form).** If `K`, with top weight
`m`, is a `lam`-local-spectral expander of dimension `d` with `lam < 0`, then every nonempty set
of at most `d + 1` vertices of `K` is a face. No connectivity hypothesis is needed: the definition
bounds every link of a face of dimension at most `d − 2`, and each of them is then a complete
graph.

`d ≥ 1` is part of the definition (`not_isLocalSpectralExpanderOf_zero`). For `d = 1` only `K`
itself is tested, and this is the statement that a weighted graph without isolated vertices whose
random walk has negative second eigenvalue is complete. -/
theorem IsLocalSpectralExpanderOf.mem_of_neg (h : K.IsLocalSpectralExpanderOf d m lam)
    (hlam : lam < 0) {s : Finset ι} (hs : s.Nonempty) (hsV : ∀ v ∈ s, {v} ∈ K)
    (hcard : #s ≤ d + 1) : s ∈ K :=
  mem_of_pairClosed (fun _ hτ hc => h.isTopWeight.pairClosed_of_neg hc hlam
    (h.walkSecondEigenvalueLE hτ hc)) hs hsV hcard

/-- A weighted `lam`-local-spectral expander with `lam < 0`, in which every point of `ι` is a
vertex, is the complete complex `complete ι d`. -/
theorem IsLocalSpectralExpanderOf.eq_complete_of_neg (h : K.IsLocalSpectralExpanderOf d m lam)
    (hlam : lam < 0) (hV : ∀ v, {v} ∈ K) : K = complete ι d :=
  eq_complete_of_forall_mem h.isTopWeight.isPure
    (fun _ hs hsV hcard => h.mem_of_neg hlam hs hsV hcard) hV

/-- **Negative trickling down is rigid.** The counting version of
`IsTopWeight.mem_of_trickling_down_neg`: under the hypotheses of `trickling_down` (`d ≥ 2`, `K`
pure, `K` and the links of faces of dimension at most `d − 3` connected), if the link of every
`(d − 2)`-dimensional face has some negative bound on its second eigenvalue, then every nonempty
set of at most `d + 1` vertices of `K` is a face. For `d = 1` the hypotheses are vacuous and the
conclusion fails for a path; for `d = 0` the conclusion is trivial. -/
theorem mem_of_trickling_down_neg (hd : 2 ≤ d) (hpure : K.IsPure d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    (hneg : ∀ σ ∈ K, #σ + 1 = d → ∃ lam < 0, WalkSecondEigenvalueLE (K.linkWeight d σ) lam)
    {s : Finset ι} (hs : s.Nonempty) (hsV : ∀ v ∈ s, {v} ∈ K) (hcard : #s ≤ d + 1) : s ∈ K := by
  obtain ⟨v, hv⟩ := hs
  have hm := K.isTopWeight_uniformWeight hpure ⟨{v}, hsV v hv⟩
  simp only [K.linkWeight_eq_linkWeightOf] at hneg
  exact hm.mem_of_trickling_down_neg hd hconn hneg ⟨v, hv⟩ hsV hcard

/-- **Negative trickling down forces the complete complex.** Under the hypotheses of
`mem_of_trickling_down_neg`, a complex in which every point of `ι` is a vertex is
`complete ι d`. -/
theorem eq_complete_of_trickling_down_neg (hd : 2 ≤ d) (hpure : K.IsPure d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    (hneg : ∀ σ ∈ K, #σ + 1 = d → ∃ lam < 0, WalkSecondEigenvalueLE (K.linkWeight d σ) lam)
    (hV : ∀ v, {v} ∈ K) : K = complete ι d :=
  eq_complete_of_forall_mem hpure
    (fun _ hs hsV hcard => mem_of_trickling_down_neg hd hpure hconn hneg hs hsV hcard) hV

/-- **Negative local spectral expanders are complete.** If `K` is a `lam`-local-spectral expander
of dimension `d` with `lam < 0`, every nonempty set of at most `d + 1` vertices of `K` is a face.
`d ≥ 1` is part of the definition; for `d = 1` this is the statement about graphs. -/
theorem IsLocalSpectralExpander.mem_of_neg (h : K.IsLocalSpectralExpander d lam) (hlam : lam < 0)
    {s : Finset ι} (hs : s.Nonempty) (hsV : ∀ v ∈ s, {v} ∈ K) (hcard : #s ≤ d + 1) : s ∈ K :=
  ((K.isLocalSpectralExpander_iff_isLocalSpectralExpanderOf).mp h).mem_of_neg hlam hs hsV hcard

/-- A `lam`-local-spectral expander with `lam < 0`, in which every point of `ι` is a vertex, is
the complete complex `complete ι d`. -/
theorem IsLocalSpectralExpander.eq_complete_of_neg (h : K.IsLocalSpectralExpander d lam)
    (hlam : lam < 0) (hV : ∀ v, {v} ∈ K) : K = complete ι d :=
  ((K.isLocalSpectralExpander_iff_isLocalSpectralExpanderOf).mp h).eq_complete_of_neg hlam hV

/-! ### The complete complex -/

/-- In the complete complex, the weighted graph of the link of a `(d − 2)`-dimensional set `σ` is
the complete graph on the points outside `σ`, with unit weights. -/
private theorem linkWeight_complete_of_card_add_one_eq {σ : Finset ι} (hσ : #σ + 1 = d)
    (u v : ι) :
    (complete ι d).linkWeight d σ u v = if u ≠ v ∧ u ∉ σ ∧ v ∉ σ then 1 else 0 := by
  unfold linkWeight
  split_ifs with h
  · have hu : u ∉ insert v σ := by rw [mem_insert, not_or]; exact ⟨h.1, h.2.1⟩
    have hcard : #(insert u (insert v σ)) = d + 1 := by
      rw [card_insert_of_notMem hu, card_insert_of_notMem h.2.2]; omega
    rw [topDegree_eq_one _ (mem_complete.mpr ⟨insert_nonempty _ _, hcard.le⟩) hcard, Nat.cast_one]
  · rfl

/-- Its degrees: `n − d` at a point outside `σ`, and `0` on `σ`. -/
private theorem sum_linkWeight_complete_of_card_add_one_eq {σ : Finset ι} (hσ : #σ + 1 = d)
    (u : ι) :
    ∑ v, (complete ι d).linkWeight d σ u v =
      if u ∈ σ then 0 else (Fintype.card ι : ℝ) - d := by
  simp only [linkWeight_complete_of_card_add_one_eq hσ]
  split_ifs with hu
  · exact sum_eq_zero fun v _ => if_neg fun h => h.2.1 hu
  · rw [sum_boole]
    have e : ({v | u ≠ v ∧ u ∉ σ ∧ v ∉ σ} : Finset ι) = (σᶜ).erase u := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_erase, mem_compl]
      exact ⟨fun h => ⟨Ne.symm h.1, h.2.2⟩, fun h => ⟨Ne.symm h.1, hu, h.2⟩⟩
    have hlt : #σ < Fintype.card ι :=
      (card_lt_card (ssubset_insert hu)).trans_le (card_le_univ _)
    rw [e, card_erase_of_mem (mem_compl.mpr hu), card_compl]
    have e1 : (Fintype.card ι - #σ - 1) + d = Fintype.card ι := by omega
    have e2 : ((Fintype.card ι - #σ - 1 : ℕ) : ℝ) + d = Fintype.card ι := by exact_mod_cast e1
    linarith

/-- The sum of `f u * f v` over ordered pairs of distinct elements of `T` is the square of the sum
minus the sum of the squares. -/
private theorem sum_sum_ite_ne_mul_of_mem (T : Finset ι) (f : ι → ℝ) :
    ∑ u, ∑ v, (if u ≠ v ∧ u ∈ T ∧ v ∈ T then f u * f v else 0) =
      (∑ v ∈ T, f v) ^ 2 - ∑ v ∈ T, f v ^ 2 := by
  have h : ∀ u, ∑ v, (if u ≠ v ∧ u ∈ T ∧ v ∈ T then f u * f v else 0) =
      if u ∈ T then f u * (∑ v ∈ T, f v) - f u ^ 2 else 0 := by
    intro u
    by_cases hu : u ∈ T
    · have e : ∀ v, (if u ≠ v ∧ u ∈ T ∧ v ∈ T then f u * f v else 0) =
          if v ∈ T.erase u then f u * f v else 0 := by
        intro v
        refine if_congr ?_ rfl rfl
        rw [Finset.mem_erase]
        exact ⟨fun h => ⟨h.1.symm, h.2.2⟩, fun h => ⟨h.1.symm, hu, h.2⟩⟩
      rw [if_pos hu, Finset.sum_congr rfl fun v _ => e v, Fintype.sum_ite_mem,
        Finset.sum_erase_eq_sub hu, Finset.mul_sum]
      ring
    · rw [if_neg hu]
      exact Finset.sum_eq_zero fun v _ => if_neg fun h => hu h.2.1
  rw [Finset.sum_congr rfl fun u _ => h u, Fintype.sum_ite_mem, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  ring

/-- **The links of `(d − 2)`-faces of the complete complex.** In `complete ι d` with
`n = Fintype.card ι ≥ d + 1`, the link of a set `σ` with `d − 1` elements is the complete graph on
the `n − d + 1` points outside `σ`, with unit weights; its random walk has second eigenvalue
exactly `−1/(n − d)`.

`#σ + 1 = d` forces `d ≥ 1`; for `d = 1` it says `σ = ∅`, and the link is `K` itself. The
subtraction `n − d` is taken in `ℝ` and is at least `1`. The hypothesis `n ≥ d + 1` is needed:
for `n ≤ d` the link has at most one point and every `lam` is allowed, whereas the right-hand side
reads `−(1/0) = 0 ≤ lam` for `n = d` (division by zero is `0` in Lean) and `1 ≤ lam` for
`n = d − 1`. -/
theorem walkSecondEigenvalueLE_complete_codimTwo_link_iff (hn : d + 1 ≤ Fintype.card ι)
    {σ : Finset ι} (hσ : #σ + 1 = d) :
    WalkSecondEigenvalueLE ((complete ι d).linkWeight d σ) lam ↔
      -(1 / ((Fintype.card ι : ℝ) - d)) ≤ lam := by
  have hc : (0 : ℝ) < (Fintype.card ι : ℝ) - d := by
    have : ((d + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    push_cast at this
    linarith
  have hdeg := sum_linkWeight_complete_of_card_add_one_eq (ι := ι) hσ
  constructor
  · intro h
    -- two points outside `σ`, and the edge inequality between them
    have h2 : 1 < #σᶜ := by rw [card_compl]; omega
    obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp h2
    rw [mem_compl] at hu hv
    have h1 := h.neg_two_mul_weight_le ((complete ι d).linkWeight_symm d σ)
      (fun x => if_neg fun h => h.1 rfl) huv (by rw [hdeg, if_neg hu]; exact hc)
      (by rw [hdeg, if_neg hv]; exact hc)
    rw [linkWeight_complete_of_card_add_one_eq hσ, if_pos ⟨huv, hu, hv⟩, hdeg, hdeg, if_neg hu,
      if_neg hv] at h1
    rw [neg_le, le_div_iff₀ hc]
    linarith
  · -- the quadratic form is `(Σ f)² − Σ f² = −Σ f²` on mean-zero `f`
    intro hle f hf
    have e : ∀ g : ι → ℝ, ∑ u, (if u ∈ σ then 0 else (Fintype.card ι : ℝ) - d) * g u =
        ((Fintype.card ι : ℝ) - d) * ∑ u ∈ σᶜ, g u := by
      intro g
      rw [mul_sum, ← Fintype.sum_ite_mem σᶜ]
      refine sum_congr rfl fun u _ => ?_
      by_cases hu : u ∈ σ <;> simp [hu]
    simp only [hdeg, e] at hf ⊢
    have hS1 : ∑ u ∈ σᶜ, f u = 0 := (mul_eq_zero.mp hf).resolve_left hc.ne'
    have hq : ∑ u, ∑ v, (complete ι d).linkWeight d σ u v * f u * f v =
        (∑ v ∈ σᶜ, f v) ^ 2 - ∑ v ∈ σᶜ, f v ^ 2 := by
      rw [← sum_sum_ite_ne_mul_of_mem]
      refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
      rw [linkWeight_complete_of_card_add_one_eq hσ]
      simp only [mem_compl]
      split_ifs <;> ring
    rw [hq, hS1]
    have hS2 : 0 ≤ ∑ v ∈ σᶜ, f v ^ 2 := sum_nonneg fun v _ => sq_nonneg _
    have h' : -1 ≤ lam * ((Fintype.card ι : ℝ) - d) := by
      rw [neg_le, le_div_iff₀ hc] at hle
      linarith
    nlinarith [mul_le_mul_of_nonneg_right h' hS2]

/-- The link of a set of dimension at most `d − 2` with fewer than `n` points is connected. -/
private theorem isConnected_link_complete_of_card_lt {σ : Finset ι} (hσ : #σ + 1 ≤ d)
    (hlt : #σ < Fintype.card ι) : ((complete ι d).link σ).IsConnected := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ σ := by
    by_contra h
    simp only [not_exists, not_not] at h
    rw [eq_univ_of_forall h, card_univ] at hlt
    omega
  exact isConnected_link_complete hσ hx

/-- **The hypotheses of trickling down, in the negative regime.** Let `d ≥ 2` and `lam < 0`, and
let `K` be a complex in which every point of `ι` is a vertex. Then `K` meets the hypotheses of
`trickling_down` with bound `lam` on the links of its `(d − 2)`-faces (purity, connectivity of `K`
and of the links of faces of dimension at most `d − 3`, and the eigenvalue bound) exactly when `K`
is the complete complex `complete ι d`, there are `n = Fintype.card ι ≥ d + 1` points, and
`lam ≥ −1/(n − d)`.

The subtraction `n − d` is taken in `ℝ`; on the right-hand side it is at least `1`. Every
hypothesis is needed: for `d = 1` the left-hand side holds for every pure `1`-dimensional complex
(a path, say); without `hV` the complete complex on a subset of `ι` would do; and for `lam = 0`
`twoTriangles` satisfies the left-hand side (`twoTriangles_sharp_at_zero`). -/
theorem trickling_down_hypotheses_neg_iff (hd : 2 ≤ d) (hV : ∀ v, {v} ∈ K) (hlam : lam < 0) :
    (K.IsPure d ∧ (∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected) ∧
      ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (K.linkWeight d σ) lam) ↔
    K = complete ι d ∧ d + 1 ≤ Fintype.card ι ∧ -(1 / ((Fintype.card ι : ℝ) - d)) ≤ lam := by
  constructor
  · rintro ⟨hpure, hconn, hloc⟩
    have hK := eq_complete_of_trickling_down_neg hd hpure hconn
      (fun σ hσ hc => ⟨lam, hlam, hloc σ hσ hc⟩) hV
    have hne : ∃ F, F ∈ K := by
      have h := hconn ∅ (Or.inl rfl) (by rw [card_empty]; omega)
      rw [link_empty] at h
      exact h.exists_mem
    obtain ⟨F, hF, hFcard⟩ := hpure.exists_card_eq hne
    have hn : d + 1 ≤ Fintype.card ι := by rw [← hFcard]; exact card_le_univ F
    obtain ⟨σ, hσF, hσcard⟩ := exists_subset_card_eq (s := F) (n := d - 1) (by omega)
    have hσK : σ ∈ K := K.mem_of_subset hF hσF (card_pos.mp (by omega))
    have h := hloc σ hσK (by omega)
    subst hK
    exact ⟨rfl, hn, (walkSecondEigenvalueLE_complete_codimTwo_link_iff hn (by omega)).mp h⟩
  · rintro ⟨rfl, hn, hle⟩
    exact ⟨isPure_complete hn,
      fun σ _ hσ => isConnected_link_complete_of_card_lt (by omega) (by omega),
      fun σ _ hσ => (walkSecondEigenvalueLE_complete_codimTwo_link_iff hn hσ).mpr hle⟩

/-- **The complete complex as a local spectral expander.** For `d ≥ 1` and
`n = Fintype.card ι ≥ d + 1`, the complete complex `complete ι d` is a `lam`-local-spectral
expander exactly when `lam ≥ −1/(n − 1)`.

The lower bound is the trace bound (`WalkSecondEigenvalueLE.neg_one_div_le_of_support`) for the
underlying graph, all of whose `n` vertices have positive degree. The upper bound is trickling
down from the links of the `(d − 2)`-faces (`walkSecondEigenvalueLE_complete_codimTwo_link_iff`),
which is exact here: `(−1/(n − d)) / (1 + (d − 1)/(n − d)) = −1/(n − 1)`; for `d = 1` there is
nothing to trickle down. The subtraction `n − 1` is taken in `ℝ` and is at least `d ≥ 1`. For
`d = 0` no complex is a local spectral expander (`not_isLocalSpectralExpander_zero`), and for
`n ≤ d` the complete complex has no `d`-dimensional face. -/
theorem complete_isLocalSpectralExpander_iff (hd : 1 ≤ d) (hn : d + 1 ≤ Fintype.card ι) :
    (complete ι d).IsLocalSpectralExpander d lam ↔ -(1 / ((Fintype.card ι : ℝ) - 1)) ≤ lam := by
  have hpure := isPure_complete (ι := ι) hn
  obtain ⟨x0⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hmem : ∀ x : ι, ({x} : Finset ι) ∈ complete ι d := fun x =>
    mem_complete.mpr ⟨singleton_nonempty x, by rw [card_singleton]; omega⟩
  have hm := (complete ι d).isTopWeight_uniformWeight hpure ⟨_, hmem x0⟩
  have hnR : ((d + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  push_cast at hnR
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  constructor
  · intro h
    have hw := h.walkSecondEigenvalueLE (Or.inl rfl) (by rw [card_empty]; omega)
    have := hw.neg_one_div_le_of_support ((complete ι d).linkWeight_symm d ∅)
      (fun x => if_neg fun h => h.1 rfl) (P := univ) (by rw [card_univ]; omega)
      (fun x _ => by
        rw [linkWeight_eq_linkWeightOf]
        exact hm.sum_linkWeightOf_pos_of_insert_mem (by rw [card_empty]; omega) (notMem_empty x)
          (by rw [insert_empty]; exact hmem x))
      (fun x y hx => absurd (mem_univ x) hx)
    rwa [card_univ] at this
  · intro hle
    rcases eq_or_lt_of_le hd with rfl | hd2
    · refine ⟨le_rfl, hpure, ⟨_, hmem x0⟩, fun σ _ hσ => ?_⟩
      refine (walkSecondEigenvalueLE_complete_codimTwo_link_iff hn (by omega)).mpr ?_
      simpa using hle
    · have hc : (0 : ℝ) < (Fintype.card ι : ℝ) - d := by linarith
      have hc1 : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by linarith
      have ht : 0 < 1 / ((Fintype.card ι : ℝ) - d) := one_div_pos.mpr hc
      have h := (complete ι d).isLocalSpectralExpander_of_trickling_down hd2 hpure
        (fun σ _ hσ => isConnected_link_complete_of_card_lt (by omega) (by omega))
        (lam := -(1 / ((Fintype.card ι : ℝ) - d)))
        (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (d : ℝ) - 1) ht.le])
        (fun σ _ hσ => (walkSecondEigenvalueLE_complete_codimTwo_link_iff hn hσ).mpr le_rfl)
      have e1 : 1 - ((d : ℝ) - 1) * -(1 / ((Fintype.card ι : ℝ) - d)) =
          ((Fintype.card ι : ℝ) - 1) / ((Fintype.card ι : ℝ) - d) := by
        field_simp
        ring
      have e : -(1 / ((Fintype.card ι : ℝ) - d)) /
          (1 - ((d : ℝ) - 1) * -(1 / ((Fintype.card ι : ℝ) - d))) =
            -(1 / ((Fintype.card ι : ℝ) - 1)) := by
        rw [e1]
        field_simp
      rw [e] at h
      exact ⟨h.1, h.2.1, h.2.2.1, fun σ hσ hc =>
        (h.2.2.2 σ hσ hc).mono ((complete ι d).linkWeight_nonneg d σ) hle⟩

/-- **Which complexes are negative local spectral expanders.** For `d ≥ 1`, a complex `K` in which
every point of `ι` is a vertex is a `lam`-local-spectral expander for some `lam < 0` exactly when
it is the complete complex `complete ι d` on `n = Fintype.card ι ≥ d + 1` points. The best such
`lam` is then `−1/(n − 1)` (`complete_isLocalSpectralExpander_iff`).

For `d = 0` the left-hand side is always false (`not_isLocalSpectralExpander_zero`) while the
right-hand side can hold, so `d ≥ 1` is needed. -/
theorem exists_neg_isLocalSpectralExpander_iff (hd : 1 ≤ d) (hV : ∀ v, {v} ∈ K) :
    (∃ lam < 0, K.IsLocalSpectralExpander d lam) ↔ K = complete ι d ∧ d + 1 ≤ Fintype.card ι := by
  constructor
  · rintro ⟨lam, hlam, h⟩
    obtain ⟨F, hF, hFcard⟩ := h.isPure.exists_card_eq h.exists_mem
    exact ⟨h.eq_complete_of_neg hlam hV, by rw [← hFcard]; exact card_le_univ F⟩
  · rintro ⟨rfl, hn⟩
    have hnR : ((d + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    push_cast at hnR
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hc1 : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by linarith
    exact ⟨-(1 / ((Fintype.card ι : ℝ) - 1)), neg_neg_of_pos (one_div_pos.mpr hc1),
      (complete_isLocalSpectralExpander_iff hd hn).mpr le_rfl⟩

/-! ### Sharpness: two triangles sharing an edge -/

/-- **Two triangles sharing an edge**: the complex on `Fin 4` whose faces are the nonempty subsets
of `{0, 1, 2}` and of `{0, 1, 3}`. It is pure of dimension `2` and connected, and its vertex links
have second eigenvalue at most `0` (the links of `0` and `1` are paths with two edges, whose
random walk has second eigenvalue `0`; those of `2` and `3` are single edges, with second
eigenvalue `−1`). But it is not the complete complex, since `{2, 3}` is not a face. -/
def twoTriangles : PreAbstractSimplicialComplex (Fin 4) where
  faces := {s | s.Nonempty ∧ (s ⊆ {0, 1, 2} ∨ s ⊆ {0, 1, 3})}
  isRelLowerSet_faces := by
    rintro s ⟨hne, hs⟩
    exact ⟨hne, fun t hts ht => ⟨ht, hs.imp hts.trans hts.trans⟩⟩

/-- The faces of `twoTriangles`, by definition. -/
theorem mem_twoTriangles {s : Finset (Fin 4)} :
    s ∈ twoTriangles ↔ s.Nonempty ∧ (s ⊆ {0, 1, 2} ∨ s ⊆ {0, 1, 3}) := Iff.rfl

/-- `twoTriangles` is pure of dimension `2`: every face lies in one of the two triangles. -/
theorem isPure_twoTriangles : twoTriangles.IsPure 2 := by
  intro σ hσ
  rcases (mem_twoTriangles.mp hσ).2 with h | h
  · exact ⟨(card_le_card h).trans (by decide), {0, 1, 2},
      mem_twoTriangles.mpr ⟨by decide, Or.inl subset_rfl⟩, h, by decide⟩
  · exact ⟨(card_le_card h).trans (by decide), {0, 1, 3},
      mem_twoTriangles.mpr ⟨by decide, Or.inr subset_rfl⟩, h, by decide⟩

/-- Every point of `Fin 4` is a vertex of `twoTriangles`. -/
theorem singleton_mem_twoTriangles (v : Fin 4) : {v} ∈ twoTriangles := by
  rw [mem_twoTriangles]
  fin_cases v <;> decide

/-- `twoTriangles` is connected: every vertex is joined to `0`. -/
theorem isConnected_twoTriangles : twoTriangles.IsConnected := by
  rw [IsConnected, SimpleGraph.connected_iff]
  have h0 : (0 : Fin 4) ∈ twoTriangles.vertices := singleton_mem_twoTriangles 0
  have hr : ∀ a : twoTriangles.vertices,
      (twoTriangles.oneSkeleton.induce twoTriangles.vertices).Reachable a ⟨0, h0⟩ := by
    rintro ⟨a, ha⟩
    by_cases hne : a = 0
    · subst hne
      rfl
    refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.induce_adj, oneSkeleton, SimpleGraph.fromRel_adj]
    refine ⟨hne, Or.inl ?_⟩
    show ({a, 0} : Finset (Fin 4)) ∈ twoTriangles
    rw [mem_twoTriangles]
    revert hne
    fin_cases a <;> decide
  exact ⟨fun a b => (hr a).trans (hr b).symm, ⟨⟨0, h0⟩⟩⟩

/-- The edge `{2, 3}` of the complete complex is missing from `twoTriangles`. -/
theorem pair_two_three_notMem_twoTriangles : ({2, 3} : Finset (Fin 4)) ∉ twoTriangles := by
  rw [mem_twoTriangles]
  decide

/-- The weighted graph of the link of a vertex `z` of `twoTriangles`: unit weight on `u v` exactly
when `{u, v, z}` is one of the two triangles. -/
private theorem linkWeight_twoTriangles (z u v : Fin 4) :
    twoTriangles.linkWeight 2 {z} u v =
      if u ≠ v ∧ u ≠ z ∧ v ≠ z ∧
          (({u, v, z} : Finset (Fin 4)) ⊆ {0, 1, 2} ∨ ({u, v, z} : Finset (Fin 4)) ⊆ {0, 1, 3})
        then 1 else 0 := by
  unfold linkWeight
  by_cases h : u ≠ v ∧ u ≠ z ∧ v ≠ z
  · rw [if_pos (by simpa using h)]
    have hcard : #({u, v, z} : Finset (Fin 4)) = 2 + 1 :=
      card_eq_three.mpr ⟨u, v, z, h.1, h.2.1, h.2.2, rfl⟩
    by_cases hK : ({u, v, z} : Finset (Fin 4)) ⊆ {0, 1, 2} ∨
        ({u, v, z} : Finset (Fin 4)) ⊆ {0, 1, 3}
    · rw [if_pos ⟨h.1, h.2.1, h.2.2, hK⟩,
        topDegree_eq_one _ (mem_twoTriangles.mpr ⟨insert_nonempty _ _, hK⟩) hcard, Nat.cast_one]
    · rw [if_neg fun h' => hK h'.2.2.2]
      have h0 : twoTriangles.topDegree 2 {u, v, z} = 0 := by
        by_contra h0
        obtain ⟨F, hF, hFcard, hsub⟩ := twoTriangles.topDegree_pos_iff.mp (Nat.pos_of_ne_zero h0)
        have hEq := eq_of_subset_of_card_le hsub (by omega)
        rw [← hEq] at hF
        exact hK (mem_twoTriangles.mp hF).2
      rw [h0, Nat.cast_zero]
  · rw [if_neg (by simpa using h), if_neg fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩]

/-- **The vertex links of `twoTriangles` have second eigenvalue at most `0`.** The link of `0` is
the path `2 − 1 − 3`: with degrees `1, 2, 1` the mean-zero condition is `2 f₁ + f₂ + f₃ = 0`, and
the quadratic form is `2 f₁ (f₂ + f₃) = −4 f₁² ≤ 0`. The link of `1` is the path `2 − 0 − 3`, and
the links of `2` and `3` are the single edge `0 − 1`, where the quadratic form is
`2 f₀ f₁ = −2 f₀² ≤ 0`. -/
theorem walkSecondEigenvalueLE_twoTriangles_link_singleton (z : Fin 4) :
    WalkSecondEigenvalueLE (twoTriangles.linkWeight 2 {z}) 0 := by
  intro f hf
  simp only [linkWeight_twoTriangles] at hf ⊢
  fin_cases z <;> simp only [Fin.sum_univ_four] at hf ⊢ <;> simp +decide at hf ⊢
  · have h3 : f 3 = -2 * f 1 - f 2 := by linarith
    rw [h3]
    nlinarith [sq_nonneg (f 1)]
  · have h3 : f 3 = -2 * f 0 - f 2 := by linarith
    rw [h3]
    nlinarith [sq_nonneg (f 0)]
  · have h1 : f 1 = -f 0 := by linarith
    rw [h1]
    nlinarith [sq_nonneg (f 0)]
  · have h1 : f 1 = -f 0 := by linarith
    rw [h1]
    nlinarith [sq_nonneg (f 0)]

/-- **Sharpness of `lam < 0`.** `twoTriangles` meets every hypothesis of
`eq_complete_of_trickling_down_neg` and of `trickling_down_hypotheses_neg_iff`, in dimension
`d = 2`, with the bound `lam = 0` in place of a negative one: it is pure, connected (for `d = 2`
the only link that must be connected is `K` itself, `σ = ∅`), every point of `Fin 4` is a vertex,
and the link of every vertex has second eigenvalue at most `0`. Yet it is not
`complete (Fin 4) 2`. So the strict inequality `lam < 0` cannot be weakened to `lam ≤ 0`. -/
theorem twoTriangles_sharp_at_zero :
    twoTriangles.IsPure 2 ∧
      (∀ σ : Finset (Fin 4), (σ = ∅ ∨ σ ∈ twoTriangles) → #σ + 2 ≤ 2 →
        (twoTriangles.link σ).IsConnected) ∧
      (∀ σ ∈ twoTriangles, #σ + 1 = 2 →
        WalkSecondEigenvalueLE (twoTriangles.linkWeight 2 σ) 0) ∧
      (∀ v, {v} ∈ twoTriangles) ∧ twoTriangles ≠ complete (Fin 4) 2 := by
  refine ⟨isPure_twoTriangles, fun σ _ hσ => ?_, fun σ _ hσ => ?_, singleton_mem_twoTriangles,
    fun h => pair_two_three_notMem_twoTriangles ?_⟩
  · rw [card_eq_zero.mp (by omega : #σ = 0), link_empty]
    exact isConnected_twoTriangles
  · obtain ⟨z, rfl⟩ := card_eq_one.mp (by omega : #σ = 1)
    exact walkSecondEigenvalueLE_twoTriangles_link_singleton z
  · rw [h, mem_complete]
    decide

end PreAbstractSimplicialComplex
