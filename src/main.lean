import topology.bounded_continuous_function

noncomputable theory
open set classical
local attribute [instance] prop_decidable

-- I will refactor this I promise!

variables {X : Type*} [metric_space X] [compact_space X]

-- We adopt the notation of bounded countinuous function from mathlib
local infixr ` →ᵇ ` : 25 := bounded_continuous_function

theorem max_bounded {f g : X → ℝ} 
(hf :  ∃ (C : ℝ), ∀ (x y : X), dist (f x) (f y) ≤ C) 
(hg :  ∃ (C : ℝ), ∀ (x y : X), dist (g x) (g y) ≤ C) :
∃ (C : ℝ), ∀ (x y : X), dist (max (f x) (g x)) (max (f y) (g y)) ≤ C := sorry

theorem min_bounded {f g : X → ℝ} 
(hf :  ∃ (C : ℝ), ∀ (x y : X), dist (f x) (f y) ≤ C) 
(hg :  ∃ (C : ℝ), ∀ (x y : X), dist (g x) (g y) ≤ C) :
∃ (C : ℝ), ∀ (x y : X), dist (min (f x) (g x)) (min (f y) (g y)) ≤ C := sorry

instance : has_sup (X →ᵇ ℝ) := 
⟨λ f g, ⟨λ x, max (f x) (g x), continuous.max f.2.1 g.2.1, max_bounded f.2.2 g.2.2⟩⟩

instance : has_inf (X →ᵇ ℝ) := 
⟨λ f g, ⟨λ x, min (f x) (g x), continuous.min f.2.1 g.2.1, min_bounded f.2.2 g.2.2⟩⟩

/- We define our own uniform convergence since I don't understand Lean's version 
with filters -/
def unif_converges_to {α} (F : ℕ → α → ℝ) (f : α → ℝ) :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : α, abs (f x - F n x) < ε

-- Closure₀ is the set of bounded continuous functions closed under inf and sup
def closure₀ (M₀ : set (X →ᵇ ℝ)) :=
  {h : X →ᵇ ℝ | ∃ f g ∈ M₀, h = f ⊔ g ∨ h = f ⊓ g}

-- Closure₁ is the closure of closure₀ under uniform convergence
def closure₁ (M₀ : set (X →ᵇ ℝ)) := 
  {h : X →ᵇ ℝ | ∃ (F : ℕ → (X →ᵇ ℝ)) 
    (H : ∀ i, F i ∈ closure₀ M₀), unif_converges_to (λ n, F n) h}

/- In Stone's proof, he also describes a closure₂ M₀ thats the closure of M₀ under 
all three operations. -/
def closure₂ (M₀ : set (X →ᵇ ℝ)) := 
  {h : X →ᵇ ℝ | (∃ f g ∈ M₀, h = f ⊔ g ∨ h = f ⊓ g) ∨ 
  ∃ (F : ℕ → X →ᵇ ℝ) (H : ∀ i, F i ∈ closure₀ M₀), unif_converges_to (λ n, F n) h}

attribute [reducible] closure₀ closure₁ closure₂

lemma closure₂_of_closure₂ (M₀ : set (X →ᵇ ℝ)) : 
closure₂ (closure₂ M₀) = closure₂ M₀ := sorry

lemma closure₂_of_univ : 
closure₂ (@univ (X →ᵇ ℝ)) = univ :=
begin
  ext f, split; intro hf,
    { exact mem_univ f },
    { left, refine ⟨f, f, hf, hf, or.inl _⟩,
      unfold has_sup.sup, 
      ext, simpa }
end

lemma closure₀_closed_with_sup {M₀ : set (X →ᵇ ℝ)} {f g} 
(hf : f ∈ closure₀ M₀) (hg : g ∈ closure₀ M₀) : f ⊔ g ∈ closure₀ M₀ := sorry

lemma closure₀_closed_with_inf {M₀ : set (X →ᵇ ℝ)} {f g} 
(hf : f ∈ closure₀ M₀) (hg : g ∈ closure₀ M₀) : f ⊓ g ∈ closure₀ M₀ := sorry

/-
It's easy to see that M₀ ⊆ closure₀ M₀ ⊆ closure₁ M₀ ⊆ closure₂ M₀.
In fact, closure₁ M₀ = closure₂ M₀

lemma closure_le_seq₀ {M₀ : set (X →ᵇ ℝ)} :
M₀ ⊆ closure₀ M₀ := sorry

lemma closure_le_seq₁ {M₀ : set (X →ᵇ ℝ)} :
closure₀ M₀ ⊆ closure₁ M₀ := sorry

lemma closure_le_seq₂ {M₀ : set (X →ᵇ ℝ)} :
closure₁ M₀ = closure₂ M₀ := sorry
-/

/-
The first lemma we need states that:

f ∈ closure₂ M₀ ↔ 
∀ x, y ∈ X, ∀ ε > 0, ∃ f' ∈ closure₀ M₀, such that 
|f(x) - f'(x)| < ε and |f(y) - f'(y)| < ε
-/

/- The forward direction is trivial -/
lemma dense_at_points_in_closure
{M₀ : set (X →ᵇ ℝ)} {f : X →ᵇ ℝ} (h : f ∈ closure₂ M₀) : 
∀ ε > 0, ∀ x y : X, ∃ (g : X →ᵇ ℝ) (H : g ∈ closure₀ M₀), 
abs (f x - g x) < ε ∧ abs (f y - g y) < ε := 
begin
  rcases h with ⟨g, h, hg, hh, h⟩; intros ε hε x y,
    { cases h with hlub hglb, 
        exact ⟨g ⊔ h, ⟨g, h, hg, hh, or.inl rfl⟩, by simpa [hlub, hε]⟩,
        exact ⟨g ⊓ h, ⟨g, h, hg, hh, or.inr rfl⟩, by simpa [hglb, hε]⟩ },
    { rcases h with ⟨F, hF, hlim⟩,
      cases hlim ε hε with N hN,
      exact ⟨F N, hF N, by simp [hN N (le_refl N)]⟩ }
end

/- To prove the reverse we fix x ∈ X and vary y. 

Since X is a compact space, We an use Heine-Borel on the entire space.

This is the lemma we'll use: compact.elim_finite_subcover -/

/-
So let us fix x ∈ X and given y ∈ X write the function g satisfying 
h : abs (f(x) - g(x)) < ε ∧ abs (f(y) -g(y)) < ε, f_y (the existence 
of which is guarenteed by our hypothesis), we define 
  S(y) := {z ∈ X | f(z) - f_y(z) < ε}
It's obvious that y ∈ S(y) by h.right so 
  X ⊆ ⋃ (y : X) S(y) ⇒ X = ⋃ (y : X) S(y)

Now as X is compact, there is a finite subcover of X so there exists 
points in X, y₁, ⋯, yₙ, such that 
  X = U i ∈ {1, ⋯, n}, S(yᵢ).

So now, by letting g_x := ⊔ i, f_yᵢ, we have ∀ z ∈ X, 
  g_x(z) ≥ f_yₖ(z) > f(z) - ε
for some k ∈ {1, ⋯, n}.

Now we will define T(x) := {z ∈ X | g_x(z) < f(z) + ε}. 
As ∀ yᵢ, f_yᵢ(x) < f(x) + ε by h.left, so is g_x(x) < f(x) + ε. 
Thus, x ∈ T(x) and X ⊆ ⋃ (x : X) T(x) and again as X is compact, there 
is x₁, ⋯, xₘ, such that 
  X = U i ∈ {1, ⋯, m}, S(xᵢ).

So, by letting h := ⊓ i, g_xᵢ, we have ∀ z ∈ X, h(z) ≤ g_xₖ(z) < f(z) + ε.
Now, as g_xᵢ(z) > f(z) - ε, for all i, so is h(z) > f(z) - ε and hence 
there is a function in closure₀ M₀ thats arbitarily close to f. 
-/

-- compact.elim_finite_subcover require semilattices which we will assume
instance : semilattice_sup_bot (X →ᵇ ℝ) := sorry
instance : semilattice_inf_top (X →ᵇ ℝ) := sorry

variables {M₀ : set (X →ᵇ ℝ)}

lemma le_finset_sup {I : finset X} (g : X → X →ᵇ ℝ) :
∀ i ∈ I, ∀ x : X, g i x ≤ (I.sup g) x := sorry

lemma finset_sup_lt {I : finset X} {g : X → X →ᵇ ℝ} {x} {r} 
(hlt : ∀ i ∈ I, g i x < r) : (I.sup g) x < r := sorry

lemma finset_sup_mem_closure₀ {I : finset X} {g : X → X →ᵇ ℝ} 
(hg : ∀ i, g i ∈ closure₀ M₀) : I.sup g ∈ closure₀ M₀ := sorry

lemma finset_inf_le {I : finset X} (g : X → X →ᵇ ℝ) :
∀ i ∈ I, ∀ x : X, (I.inf g) x ≤ g i x := sorry

lemma lt_finset_inf {I : finset X} {g : X → X →ᵇ ℝ} {x} {r} 
(hlt : ∀ i ∈ I, r < g i x) : r < (I.inf g) x := sorry

lemma finset_inf_mem_closure₀ {I : finset X} {g : X → X →ᵇ ℝ} 
(hg : ∀ i, g i ∈ closure₀ M₀) : I.inf g ∈ closure₀ M₀ := sorry

private lemma is_open_aux_set₀ {f : X →ᵇ ℝ} 
{g : X → X →ᵇ ℝ} {ε : ℝ} (hε : ε > 0) : 
∀ y : X, is_open {z : X | f z - (g y) z < ε} := sorry

private lemma is_open_aux_set₁ {f : X →ᵇ ℝ} 
{g : X → X →ᵇ ℝ} {ε : ℝ} (hε : ε > 0) : 
∀ x : X, is_open {z : X | g x z < f z + ε} := sorry

/- Given x ∈ X, we create a function thats greater than f(z) - ε at all z while 
smaller than f(x) + ε.
-/
lemma has_bcf_gt {f : X →ᵇ ℝ} (h : ∀ ε > 0, ∀ x y : X, ∃ (g : X →ᵇ ℝ) 
(H : g ∈ closure₀ M₀), abs (f x - g x) < ε ∧ abs (f y - g y) < ε) : 
∀ ε > 0, ∀ x : X, ∃ (g : X →ᵇ ℝ) 
(H : g ∈ closure₀ M₀), ∀ z : X, f z - ε < g z ∧ g x < f x + ε := 
begin
  intros ε hε x, choose g hg₀ hg₁ using h ε (by {norm_cast, exact hε}) x,
  let S : X → set X := λ y, {z | f z - g y z < ε}, 
  cases compact.elim_finite_subcover _inst_2.1 S 
    (is_open_aux_set₀ (by norm_cast; exact hε)) _ with I hI,
    { let p := I.sup g,
      refine ⟨p, finset_sup_mem_closure₀ hg₀, 
        λ z, ⟨_, finset_sup_lt (λ i hi, by linarith [(abs_lt.1 (hg₁ i).1).1])⟩⟩,
        suffices : ∃ i ∈ I, f z - ε < g i z,
            rcases this with ⟨i, hi₀, hi₁⟩,
            exact lt_of_lt_of_le hi₁ (le_finset_sup g i hi₀ z),
        have : z ∈ ⋃ (i : X) (H : i ∈ I), S i, exact hI (by trivial),
        cases mem_Union.1 this with i hi, cases mem_Union.1 hi with hi hz,
        rw mem_set_of_eq at hz, exact ⟨i, hi, by linarith⟩ },
    { intros y hy, exact mem_Union.2 ⟨y, (abs_lt.1 (hg₁ y).2).2⟩ }
end

/- We again use the same method obtaining a function arbitarily close to f -/
lemma has_bcf_close {f : X →ᵇ ℝ} (h : ∀ ε > 0, ∀ x y : X, ∃ (g : X →ᵇ ℝ) 
(H : g ∈ closure₀ M₀), abs (f x - g x) < ε ∧ abs (f y - g y) < ε) : 
∀ (ε : ℝ) (hε : 0 < ε), ∃ (g : X →ᵇ ℝ) 
(H : g ∈ closure₀ M₀), ∀ z : X, abs (f z - g z) < ε := 
begin
  intros ε hε, choose g hg₀ hg₁ using has_bcf_gt h ε hε,
  let S : X → set X := λ x, {z | g x z < f z + ε},
  cases compact.elim_finite_subcover _inst_2.1 S (is_open_aux_set₁ hε) _ with I hI,
    { let p := I.inf g, refine ⟨p, finset_inf_mem_closure₀ hg₀, λ z, _⟩, 
      rw abs_lt, refine ⟨_, _⟩,
        { rw neg_lt_sub_iff_lt_add,
          suffices : ∃ i ∈ I, g i z < f z + ε, 
            rcases this with ⟨i, hi₀, hi₁⟩,
            refine lt_of_le_of_lt (finset_inf_le g i hi₀ z) hi₁,             
          have : z ∈ ⋃ (i : X) (H : i ∈ I), S i, refine hI (by trivial),
          cases mem_Union.1 this with i hi, cases mem_Union.1 hi with hi hz,
          refine ⟨i, hi, hz⟩ },
        { suffices : ∀ i ∈ I, f z - ε < g i z, 
            exact sub_lt.2 (lt_finset_inf this),
          intros i hi, exact (hg₁ i z).1 } },
    { intros x hx, exact mem_Union.2 ⟨x, (hg₁ x x).2⟩ }
end

/- With that we conclude that there is some sequence of functions in closure₀ M₀ 
that is uniformly convergent towards f -/
lemma in_closure₂_of_dense_at_points {f : X →ᵇ ℝ}
(h : ∀ ε > 0, ∀ x y : X, ∃ (g : X →ᵇ ℝ) 
(H : g ∈ closure₀ M₀), abs (f x - g x) < ε ∧ abs (f y - g y) < ε) : 
f ∈ closure₂ M₀ := or.inr $
begin
  choose F hF₀ hF₁ using λ (n : ℕ), 
    has_bcf_close h (1 / (n + 1)) (nat.one_div_pos_of_nat),
  refine ⟨F, hF₀, λ ε hε, _⟩,
  cases exists_nat_gt (1 / ε) with N hN,
  refine ⟨N, λ n hn x, lt_of_lt_of_le (hF₁ n x) $ 
    one_div_le_of_one_div_le_of_pos hε $ le_trans (le_of_lt hN) _⟩,
  norm_cast, exact le_add_right hn,
end

/-
Finally, we can conclude that f can be constructed from M₀ using inf, sup 
and uniform convergence iff. for all pairs of points in X, (x, y), there is 
some sequence of functions in M₀ that converges pointwise to f(x) and f(y) at 
x and y.
-/
theorem in_closure₂_iff_dense_at_points 
{f : X →ᵇ ℝ} : f ∈ closure₂ M₀ ↔ ∀ ε > 0, ∀ x y : X,
∃ (g : X →ᵇ ℝ) (H : g ∈ closure₀ M₀), abs (f x - g x) < ε ∧ abs (f y - g y) < ε := 
⟨λ h, dense_at_points_in_closure h, λ h, in_closure₂_of_dense_at_points h⟩

/-
From this, two corollaries can be deduced immediately:

- If ∀ x, y ∈ X, a, b ∈ ℝ, ∃ f ∈ M₀, f(x) = a, f(y) = b, then 
  closure₂ M₀ = M (= @univ X →ᵇ ℝ)
where M is the set of all bounded continuous functions from X to ℝ.

- If f : ℕ → X →ᵇ ℝ is monotone and converges 
pointwise to g, then f converges uniformly to g.

The proof of the first corollary is trivial and the proof of the second 
follows by letting M₀ := {f n | n ∈ ℕ}.
-/

/-
Due to reasons commented from above, we will now consider pairs of points in 
X rather than functions. 

We define M₀' : X → X → ℝ × ℝ : x, y ↦ {(f(x), f(y)) | f ∈ M₀};
    (α, β) ⊔ (γ, δ) := (max α γ, max β δ);
and (α, β) ⊓ (γ, δ) := (min α γ, min β δ).

We also define a closure with respect to this inf, sup and limits of 
sequences in ℝ². 
-/

def boundary_points (M : set (X →ᵇ ℝ)) (x y : X) := 
  {z | ∃ (f : X →ᵇ ℝ) (hf : f ∈ closure₀ M), (f x, f y) = z}

lemma boundary_points_of_univ : ∀ x y : X, boundary_points univ x y = univ := sorry

-- We do not need to define inf and sup for tuples since matlib has it!
-- try : #eval (1, 4) ⊔ (2, 3)

-- Limit of sequences in ℝ²
def converges_to_R2 (s : ℕ → ℝ × ℝ) (x) := 
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (s n) x < ε

def closure' (S : set (ℝ × ℝ)) := 
  {z | (∃ r t ∈ S, r ⊔ t = z ∨ r ⊓ t = z) ∨ 
  ∃ (s : ℕ → ℝ × ℝ) (hs : ∀ n : ℕ, (s n) ∈ S), converges_to_R2 s z}

attribute [reducible] boundary_points closure'

lemma in_closure'_of_in_closoure₂ {f : X →ᵇ ℝ} (h : f ∈ closure₂ M₀) : 
∀ x y : X, (f x, f y) ∈ closure' (boundary_points M₀ x y) :=
begin
  intros x y, right,
  rw in_closure₂_iff_dense_at_points at h,
  choose F hF₀ hF₁ using λ (n : ℕ), 
    h (1 / (n + 1)) (nat.one_div_pos_of_nat) x y,
  refine ⟨λ n, (F n x, F n y), λ n, ⟨F n, hF₀ n, rfl⟩, λ ε hε, _⟩, 
  cases exists_nat_gt (1 / ε) with N hN,
  refine ⟨N, λ n hn, _⟩,
  suffices : abs (F n x - f x) < ε ∧ abs (F n y - f y) < ε,
    unfold dist, simp [this],
  split; rw abs_sub;
    try { refine lt_of_lt_of_le (hF₁ n).1 _ <|> refine lt_of_lt_of_le (hF₁ n).2 _ };
    refine one_div_le_of_one_div_le_of_pos hε (le_trans (le_of_lt hN) _);
    norm_cast; exact le_add_right hn
end

lemma bcf_pair_sup_eq_bcf_sup_pair {u v : X →ᵇ ℝ} {x y} : 
(u x, u y) ⊔ (v x, v y) = ((u ⊔ v) x, (u ⊔ v) y) := rfl

lemma bcf_pair_inf_eq_bcf_inf_pair {u v : X →ᵇ ℝ} {x y} : 
(u x, u y) ⊓ (v x, v y) = ((u ⊓ v) x, (u ⊓ v) y) := rfl

lemma in_closure₂_of_in_closure' {f : X →ᵇ ℝ} 
(h : ∀ x y : X, (f x, f y) ∈ closure' (boundary_points M₀ x y)) : f ∈ closure₂ M₀ :=
begin
  rw in_closure₂_iff_dense_at_points,
  intros ε hε x y,
  cases h x y with h' h',
    { rcases h' with ⟨r, t, ⟨u, hu₀, hu₁⟩, ⟨v, hv₀, hv₁⟩, hrt⟩,
      cases hrt,
        { refine ⟨u ⊔ v, closure₀_closed_with_sup hu₀ hv₀, _⟩,
          rw [←hu₁, ←hv₁, bcf_pair_sup_eq_bcf_sup_pair] at hrt,
          rw [(prod.mk.inj hrt).1, (prod.mk.inj hrt).2], simpa },
        { refine ⟨u ⊓ v, closure₀_closed_with_inf hu₀ hv₀, _⟩,
          rw [←hu₁, ←hv₁, bcf_pair_inf_eq_bcf_inf_pair] at hrt,
          rw [(prod.mk.inj hrt).1, (prod.mk.inj hrt).2], simpa } },
    { rcases h' with ⟨s, hs₀, hs₁⟩,
      cases hs₁ ε hε with N hN, 
      rcases hs₀ N with ⟨g, hg₀, hg₁⟩,
      refine ⟨g, hg₀, _⟩,
      have := hN N (le_refl N),
      rw ←hg₁ at this, unfold dist at this, simp at this,
      split; rw abs_sub; simp only [this] }
end

lemma in_closure₂_iff_in_closure' {f : X →ᵇ ℝ} : 
f ∈ closure₂ M₀ ↔ ∀ x y : X, (f x, f y) ∈ closure' (boundary_points M₀ x y) :=
⟨λ h, in_closure'_of_in_closoure₂ h, λ h, in_closure₂_of_in_closure' h⟩

/- 
With this, we can formulate the relation between M₀ and M₀'(x, y) formally, i.e.
if M₀, M₁ ⊆ M, 
  hM : M₀ = closure₂ M₀ and M₁ = closure₂ M₁
  hb : ∀ x, y ∈ X, M₀*(x, y) = M₁*(x, y)
then M₀ = M₁.
-/
lemma boundary_points_eq_of_eq (M₀ M₁ : set (X →ᵇ ℝ)) (h : M₀ = M₁) : 
∀ x y : X, boundary_points M₀ x y = boundary_points M₁ x y := 
λ x y, by rw h

lemma eq_of_boundary_points_eq (M₀ M₁ : set (X →ᵇ ℝ))
(h : ∀ x y : X, boundary_points M₀ x y = boundary_points M₁ x y)
(hM₀ : M₀ = closure₂ M₀) (hM₁ : M₁ = closure₂ M₁) : M₀ = M₁ := 
begin
  ext f, split; intro hf;
  { try {rw hM₀ <|> rw hM₁}, try {rw hM₀ at hf <|> rw hM₁ at hf},
    rw in_closure₂_iff_in_closure' at *, 
    intros x y, try {rw ←h x y <|> rw h x y},
    exact hf x y }
end

theorem eq_iff_boundary_points_eq (M₀ M₁ : set (X →ᵇ ℝ))
(hM₀ : M₀ = closure₂ M₀) (hM₁ : M₁ = closure₂ M₁) : 
M₀ = M₁ ↔ ∀ x y : X, boundary_points M₀ x y = boundary_points M₁ x y := 
⟨λ h, boundary_points_eq_of_eq M₀ M₁ h, λ h, eq_of_boundary_points_eq M₀ M₁ h hM₀ hM₁⟩

/-
Now that we've reformulated the problem such that it considers points in ℝ² 
rather than all bounded continuous functions, the question now becomes, 
under what condition, is the boundary points of closure₂ M₀ equal to ℝ².
-/
theorem func_dense_iff_boundary_points_dense (M₀ : set (X →ᵇ ℝ)) :
closure₂ M₀ = univ ↔ ∀ x y, boundary_points (closure₂ M₀) x y = univ := 
begin
  have := eq_iff_boundary_points_eq (closure₂ M₀) univ
    (closure₂_of_closure₂ M₀).symm (closure₂_of_univ).symm,
  split, 
    { intros h x y,
      rw this at h, rw (h x y),
      exact boundary_points_of_univ x y },
    { intro h, rw this, intros x y, rw h x y, 
      exact (boundary_points_of_univ x y).symm }
end