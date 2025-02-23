import GlimpseOfLean.Library.Basic

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by {
  linarith
}

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by {
  linarith
}

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:

-- Definition of « u tends to l »
`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|l - l|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by {
  unfold seq_limit
  intros ε hε
  use 1
  intro n hn
  rw [h n]
  simp
  linarith
}


/- When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  unfold seq_limit at h
  rcases h (l/2) (by linarith) with ⟨N0, hN⟩
  use N0
  intros n hn
  have fact : |u n - l| ≤ l/2 := hN n (by linarith)
  rw [abs_le] at fact
  calc
    u n = u n - l + l/2 + l/2 := by ring
    _ ≥ -(l/2) + l/2 +l/2 := by rel [fact.1]
  linarith
}


/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by {
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n (by linarith)

  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]
}


/- Let's do something similar: the squeezing theorem. -/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  intro ε hε
  rcases hu (ε) (by linarith) with ⟨N1, hN1⟩
  rcases hw (ε) (by linarith) with ⟨N2, hN2⟩
  use max N1 N2
  intros n hn
  have : n ≥ N1 := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact1 : |u n - l| ≤ ε := hN1 n (by linarith)
  have fact2 : |w n - l| ≤ ε := hN2 n (by linarith)
  rw [abs_le] at fact1
  rw [abs_le] at fact2
  rw [abs_le]
  constructor
  calc
    -ε ≤ u n - l := by exact fact1.1
    _ ≤ v n - l := by rel [h n]
  calc
    v n - l ≤ w n - l := by rel [h' n]
    _ ≤ ε := by exact fact2.2
}



/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma uniq_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  unfold seq_limit
  intro hul
  intro hul'
  apply eq_of_abs_sub_le_all
  intro ε hε
  rcases hul (ε/2) (by linarith) with ⟨N1, hN1⟩
  rcases hul' (ε/2) (by linarith) with ⟨N2, hN2⟩
  have hn: N1 ≤ N2 ∨ N2 ≤ N1 := by exact Nat.le_total N1 N2
  obtain N1small | N2small := hn
  specialize hN1 N2
  specialize hN2 N2

  have fact1: |u N2 - l| ≤ ε / 2 := by exact hN1 N1small
  have fact2: |u N2 - l'| ≤ ε / 2 := by exact hN2 (Nat.le_refl N2)
  calc
    |l - l'| = |(l - u N2) + (u N2 - l')| := by ring
    _ ≤ |(l - u N2)| + |(u N2 - l')|:= by apply abs_add
    _ = |u N2 - l| + |u N2 - l'|:= by rw [abs_sub_comm (u N2) l]
    _ ≤ ε/2 + ε/2 := by rel [fact1, fact2]
  linarith

  specialize hN1 N1
  specialize hN2 N1

  have fact1: |u N1 - l'| ≤ ε / 2 := by exact hN2 N2small
  have fact2: |u N1 - l| ≤ ε / 2 := by exact hN1 (Nat.le_refl N1)
  calc
    |l - l'| = |(l - u N1) + (u N1 - l')| := by ring
    _ ≤ |(l - u N1)| + |(u N1 - l')|:= by apply abs_add
    _ = |u N1 - l| + |u N1 - l'|:= by rw [abs_sub_comm (u N1) l]
    _ ≤ ε/2 + ε/2 := by rel [fact1, fact2]
  linarith
}



/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  unfold is_seq_sup at h
  unfold non_decreasing at h'
  unfold seq_limit
  intro ε hε
  obtain ⟨hbound, hforε⟩ := h
  specialize hforε ε hε
  rcases hforε with ⟨N0, hn0⟩
  use N0
  intro n hn
  specialize h' N0 n
  have fact: u n ≥ M - ε :=
  calc
    u n ≥ u N0 := by rel [h' hn]
    _ ≥ M - ε := by rel [hn0]
  rw [abs_le]
  constructor
  linarith
  specialize hbound n
  calc
    u n - M ≤ M - M := by rel [hbound]
    _ = 0 := by ring
  linarith
}

/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}


/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

lemma extraction_max : extraction φ → ∀ N N', φ (N ⊔ N') ≥ N' := by{
  intro hφ
  intro N N'
  have fact: φ (N ⊔ N' ) ≥ N ⊔ N' := by apply id_le_extraction' hφ
  calc
    φ (N ⊔ N') ≥ N ⊔ N' := by rel [fact]
    _ ≥ N' := by exact Nat.le_max_right N N'
}


/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  intro hφ
  intro N N'
  use max (N' + 1) (N +1)
  have hφ': N < N + 1 → φ N < φ (N + 1) := by apply hφ N (N + 1)
  constructor
  calc
    (N' + 1) ⊔ (N + 1) ≥ N' + 1 := by exact Nat.le_max_left (N' + 1) (N + 1)
    _ ≥ N' := by linarith
  have fact: φ ((N' + 1) ⊔ (N + 1)) ≥ (N' + 1) ⊔ (N + 1) := by apply id_le_extraction' hφ
  calc
    φ ((N' + 1) ⊔ (N + 1)) ≥ (N + 1) := by apply extraction_max hφ (N' + 1) (N + 1)
    _ ≥ N := by linarith
}

/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.

`def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a`
-/


/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  intro hcluster
  unfold cluster_point at hcluster
  intros ε hε N
  rcases hcluster with ⟨φ, hφ⟩
  obtain ⟨hext, hseqlim⟩ := hφ
  unfold seq_limit at hseqlim
  specialize hseqlim ε hε
  rcases hseqlim with ⟨N0, hN0⟩
  use φ (max N N0)
  constructor
  calc
    φ (max N N0) = φ (max N0 N) := by rw [Nat.max_comm N N0]
    _ ≥ N := by exact extraction_max hext N0 N
  specialize hN0 (max N N0)
  exact hN0 (Nat.le_max_right N N0)
}


/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
  unfold seq_limit at h
  unfold seq_limit
  intros ε hε
  specialize h ε hε
  rcases h with ⟨N0, hN0⟩
  use N0
  intros n hn
  have fact: N0 ≤ φ n := calc
     φ n ≥ n := by exact id_le_extraction' hφ n
     _ ≥ N0 := by exact hn
  exact hN0 (φ n) fact
}

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  unfold cluster_point at ha
  rcases ha with ⟨φ, hφ⟩
  obtain ⟨hext, hseq⟩ := hφ
  have fact: seq_limit (u ∘ φ) l := by exact subseq_tendsto_of_tendsto' hl hext
  exact uniq_limit hseq fact
}

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  unfold seq_limit CauchySequence
  intro hl
  intro ε hε
  rcases hl with ⟨l, hseq⟩
  rcases hseq (ε/2) (by linarith) with ⟨N0, hN0⟩
  use N0
  intros p q hp hq
  have factp: |u p - l| ≤ ε/2 := by
    specialize hN0 p
    exact hN0 hp
  have factq: |- u q + l| ≤ ε/2 := by
    calc
      |- u q + l| = |l - (u q)|:= by ring
      _ = |(u q) - l| := by exact abs_sub_comm l (u q)
    specialize hN0 q
    exact hN0 hq
  calc
    |u p - u q| = |u p - l + (-u q + l)| := by ring
    _ ≤ |u p - l| + |- u q +l| := by apply abs_add (u p -l) (-u q +l)
    _ ≤ ε/2 + ε/2 := by rel [factp, factq]
    _ ≤ ε := by linarith
}

/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
{
  unfold seq_limit
  intro ε hε
  unfold CauchySequence at hu
  rcases hu (ε/2) (by linarith) with ⟨N0, hN0⟩
  have fact: ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| ≤ ε := by apply near_cluster hl
  specialize fact (ε/2) (by linarith)
  specialize fact N0
  rcases fact with ⟨n, hn⟩
  obtain ⟨nN0, hn⟩ := hn
  use N0
  intros m hm
  have fact: |u m - u n| ≤ ε / 2 := by exact hN0 m n hm nN0
  calc
    |u m - l| ≤ |u m - u n| + |u n - l| := by apply abs_sub_le
    _ ≤ ε/2 + ε/2 := by rel[fact, hn]
  linarith
}
