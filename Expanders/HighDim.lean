import Expanders.WeightedGraph

/-!
# High-dimensional expanders

Simplicial complexes, links, and the "every link is a spectral expander" definition of a
high-dimensional expander, built on Mathlib's `PreAbstractSimplicialComplex` (a collection of
nonempty finite sets closed under taking nonempty subsets).

## Definitions
* `PreAbstractSimplicialComplex.link`: the link of a face.
* `PreAbstractSimplicialComplex.IsPure`: all maximal faces have the same dimension `d`.
* `PreAbstractSimplicialComplex.oneSkeleton`, `IsConnected`: the underlying graph.
* `PreAbstractSimplicialComplex.linkWeight`: the weighted graph on the link of a face, each edge
  weighted by the number of top-dimensional faces through it.
* `PreAbstractSimplicialComplex.IsLocalSpectralExpander`: every link of a face of dimension at
  most `d − 2` (including the whole complex) has random-walk second eigenvalue at most `lam`.

## Theorems
* `link_empty`, `link_link`: basic calculus of links. **Proved.**
* `trickling_down`: Oppenheim's local-to-global theorem. **Stated, not yet proved.**
-/

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K : PreAbstractSimplicialComplex ι)

/-! ### Faces -/

omit [DecidableEq ι] in
theorem nonempty_of_mem {σ : Finset ι} (h : σ ∈ K) : σ.Nonempty :=
  (K.isRelLowerSet_faces h).1

omit [DecidableEq ι] in
/-- Faces are closed under taking nonempty subsets. -/
theorem mem_of_subset {σ τ : Finset ι} (h : σ ∈ K) (hτ : τ ⊆ σ) (hne : τ.Nonempty) : τ ∈ K :=
  (K.isRelLowerSet_faces h).2 hτ hne

/-! ### Links -/

/-- The **link** of `σ` in `K`: the faces `τ` disjoint from `σ` such that `τ ∪ σ` is again a
face. It is the neighbourhood of `σ`, viewed as a complex in its own right. -/
def link (σ : Finset ι) : PreAbstractSimplicialComplex ι where
  faces := {τ | τ.Nonempty ∧ Disjoint τ σ ∧ τ ∪ σ ∈ K}
  isRelLowerSet_faces := by
    rintro τ ⟨hne, hdisj, hmem⟩
    exact ⟨hne, fun ρ hρτ hρ => ⟨hρ, hdisj.mono_left hρτ,
      K.mem_of_subset hmem (union_subset_union_left hρτ) (hρ.mono subset_union_left)⟩⟩

variable {K} in
theorem mem_link {σ τ : Finset ι} :
    τ ∈ K.link σ ↔ τ.Nonempty ∧ Disjoint τ σ ∧ τ ∪ σ ∈ K := Iff.rfl

/-- The link of the empty set is the whole complex. -/
@[simp]
theorem link_empty : K.link ∅ = K := by
  refine SetLike.ext fun τ => ?_
  simp only [mem_link, disjoint_empty_right, union_empty, true_and, and_iff_right_iff_imp]
  exact K.nonempty_of_mem

/-- A link of a link is a link: `(K.link σ).link τ = K.link (σ ∪ τ)` for `τ` disjoint from `σ`. -/
theorem link_link {σ τ : Finset ι} (h : Disjoint τ σ) :
    (K.link σ).link τ = K.link (σ ∪ τ) := by
  refine SetLike.ext fun ρ => ?_
  simp only [mem_link]
  constructor
  · rintro ⟨hne, hρτ, -, hdisj, hmem⟩
    refine ⟨hne, disjoint_union_right.mpr ⟨(disjoint_union_left.mp hdisj).1, hρτ⟩, ?_⟩
    rwa [union_comm σ τ, ← union_assoc]
  · rintro ⟨hne, hdisj, hmem⟩
    rw [disjoint_union_right] at hdisj
    refine ⟨hne, hdisj.2, hne.mono subset_union_left,
      disjoint_union_left.mpr ⟨hdisj.1, h⟩, ?_⟩
    rwa [union_comm σ τ, ← union_assoc] at hmem

/-! ### Dimension, purity, connectivity -/

/-- `K` is **pure of dimension `d`**: every face has at most `d + 1` vertices and is contained
in a face with exactly `d + 1` vertices. -/
def IsPure (d : ℕ) : Prop :=
  ∀ σ ∈ K, #σ ≤ d + 1 ∧ ∃ τ ∈ K, σ ⊆ τ ∧ #τ = d + 1

/-- The vertices of `K`. -/
def vertices : Set ι := {v | {v} ∈ K}

/-- The underlying graph (1-skeleton) of `K`: distinct `u`, `v` are adjacent when `{u, v}` is a
face. -/
def oneSkeleton : SimpleGraph ι :=
  SimpleGraph.fromRel fun u v => ({u, v} : Finset ι) ∈ K

/-- `K` is **connected**: its underlying graph, on the vertices of `K`, is connected. -/
def IsConnected : Prop := (K.oneSkeleton.induce K.vertices).Connected

/-! ### Local spectral expansion -/

variable [Fintype ι]

open Classical in
/-- The number of `d`-dimensional faces of `K` containing the set `s`. -/
noncomputable def topDegree (d : ℕ) (s : Finset ι) : ℕ :=
  #{F : Finset ι | F ∈ K ∧ #F = d + 1 ∧ s ⊆ F}

/-- The **weighted graph of the link of `σ`** in a `d`-dimensional complex: two distinct
vertices `u, v` outside `σ` are joined with weight the number of `d`-dimensional faces
containing `σ ∪ {u, v}`. For `σ = ∅` this is the weighted underlying graph of `K` itself. -/
noncomputable def linkWeight (d : ℕ) (σ : Finset ι) (u v : ι) : ℝ :=
  if u ≠ v ∧ u ∉ σ ∧ v ∉ σ then (K.topDegree d (insert u (insert v σ)) : ℝ) else 0

theorem linkWeight_nonneg (d : ℕ) (σ : Finset ι) (u v : ι) : 0 ≤ K.linkWeight d σ u v := by
  unfold linkWeight
  split_ifs <;> positivity

theorem linkWeight_symm (d : ℕ) (σ : Finset ι) (u v : ι) :
    K.linkWeight d σ u v = K.linkWeight d σ v u := by
  unfold linkWeight
  rw [Finset.insert_comm u v σ]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h3, h2⟩

/-- `K` is a **`lam`-local-spectral expander** of dimension `d` (a *high-dimensional expander*,
in the one-sided sense): for every face `σ` of dimension at most `d − 2`, and for `σ = ∅`, the
random walk on the weighted graph of the link of `σ` has second eigenvalue at most `lam`. -/
def IsLocalSpectralExpander (d : ℕ) (lam : ℝ) : Prop :=
  ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
    WalkSecondEigenvalueLE (K.linkWeight d σ) lam

/-- **Trickling down (Oppenheim).** Let `K` be a pure `d`-dimensional complex, `d ≥ 2`, in which
`K` itself and every link of a face of dimension at most `d − 2` is connected. If the link of
every `(d − 2)`-dimensional face has second eigenvalue at most `lam`, where `(d − 1) · lam < 1`,
then the link of every face `σ` of dimension at most `d − 2` has second eigenvalue at most
`lam / (1 − (d − 1 − |σ|) · lam)`; taking `σ = ∅`, the underlying graph of `K` has second
eigenvalue at most `lam / (1 − (d − 1) · lam)`. Expansion of the smallest links forces expansion
everywhere.

Not yet proved. The proof is by induction on dimension; the inductive step localises the
quadratic form of a link to its vertex links (Garland's method) and solves a quadratic
inequality for the second eigenvalue. -/
theorem trickling_down {d : ℕ} (hd : 2 ≤ d) (hpure : K.IsPure d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d → (K.link σ).IsConnected)
    {lam : ℝ} (hlam : ((d : ℝ) - 1) * lam < 1)
    (hlocal : ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (K.linkWeight d σ) lam) :
    ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
      WalkSecondEigenvalueLE (K.linkWeight d σ) (lam / (1 - ((d : ℝ) - 1 - #σ) * lam)) := by
  sorry

/-- Trickling down, packaged: under the hypotheses of `trickling_down` with `lam ≥ 0`, the
complex is a `lam / (1 − (d − 1) lam)`-local-spectral expander.
(Depends on the unproved `trickling_down`.) -/
theorem isLocalSpectralExpander_of_trickling_down {d : ℕ} (hd : 2 ≤ d) (hpure : K.IsPure d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d → (K.link σ).IsConnected)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : ((d : ℝ) - 1) * lam < 1)
    (hlocal : ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (K.linkWeight d σ) lam) :
    K.IsLocalSpectralExpander d (lam / (1 - ((d : ℝ) - 1) * lam)) := by
  intro σ hσ hcard
  refine (K.trickling_down hd hpure hconn hlam hlocal σ hσ hcard).mono
    (K.linkWeight_nonneg d σ) ?_
  -- `lam / (1 − (d − 1 − |σ|) lam) ≤ lam / (1 − (d − 1) lam)` because `lam ≥ 0`.
  have hσ0 : (0 : ℝ) ≤ #σ := Nat.cast_nonneg _
  have h1 : 0 < 1 - ((d : ℝ) - 1) * lam := by linarith
  have h2 : 1 - ((d : ℝ) - 1) * lam ≤ 1 - ((d : ℝ) - 1 - #σ) * lam := by nlinarith
  exact div_le_div_of_nonneg_left hlam0 h1 h2

end PreAbstractSimplicialComplex
