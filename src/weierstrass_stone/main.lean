import topology.bounded_continuous_function
import weierstrass_stone.definitions

noncomputable theory
open set 

variables {X : Type*} [metric_space X] [compact_space X]

/- We have some API regarding bdd continuous functions in mathlib! -/
#check bounded_continuous_function X ℝ

theorem max_bounded {f g : X → ℝ} 
(hf :  ∃ (C : ℝ), ∀ (x y : X), dist (f x) (f y) ≤ C) 
(hg :  ∃ (C : ℝ), ∀ (x y : X), dist (g x) (g y) ≤ C) :
∃ (C : ℝ), ∀ (x y : X), dist (max (f x) (g x)) (max (f y) (g y)) ≤ C := sorry

theorem min_bounded {f g : X → ℝ} 
(hf :  ∃ (C : ℝ), ∀ (x y : X), dist (f x) (f y) ≤ C) 
(hg :  ∃ (C : ℝ), ∀ (x y : X), dist (g x) (g y) ≤ C) :
∃ (C : ℝ), ∀ (x y : X), dist (min (f x) (g x)) (min (f y) (g y)) ≤ C := sorry

instance : has_sup (bounded_continuous_function X ℝ) := 
⟨λ f g, ⟨λ x, max (f x) (g x), continuous.max f.2.1 g.2.1, max_bounded f.2.2 g.2.2⟩⟩

instance : has_inf (bounded_continuous_function X ℝ) := 
⟨λ f g, ⟨λ x, min (f x) (g x), continuous.min f.2.1 g.2.1, min_bounded f.2.2 g.2.2⟩⟩

/- We define our own uniform convergence since I don't understand Lean's version 
with filters -/
def unif_converges_to {α} (F : ℕ → α → ℝ) (f : α → ℝ) :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : α, abs (f x - F n x) < ε

-- Closure₀ is the set of bounded continuous functions closed under inf and sup
def closure₀ (M₀ : set (bounded_continuous_function X ℝ)) :=
  {h : (bounded_continuous_function X ℝ) | ∃ f g ∈ M₀, h = f ⊔ g ∨ h = f ⊓ g}

-- Closure₁ is the closure of closure₀ under uniform convergence
def closure₁ (M₀ : set (bounded_continuous_function X ℝ)) := 
  {h : (bounded_continuous_function X ℝ) | 
  ∃ (F : ℕ → (bounded_continuous_function X ℝ)) 
    (H : ∀ i, F i ∈ closure₀ M₀), unif_converges_to (λ n, F n) h}

/- In Stone's proof, he also describes a closure₂ M₀ thats the closure of M₀ under 
all three operations. -/
def closure₂ (M₀ : set (bounded_continuous_function X ℝ)) := 
  {h : (bounded_continuous_function X ℝ) | 
  (∃ f g ∈ M₀, h = f ⊔ g ∨ h = f ⊓ g) ∨ 
  ∃ (F : ℕ → (bounded_continuous_function X ℝ)) 
    (H : ∀ i, F i ∈ closure₀ M₀), unif_converges_to (λ n, F n) h}

attribute [reducible] closure₀ closure₁ closure₂

/-
It's easy to see that M₀ ⊆ closure₀ M₀ ⊆ closure₁ M₀ ⊆ closure₂ M₀.
In fact, closure₁ M₀ = closure₂ M₀
-/
lemma closure_le_seq₀ {M₀ : set (bounded_continuous_function X ℝ)} :
M₀ ⊆ closure₀ M₀ := sorry

lemma closure_le_seq₁ {M₀ : set (bounded_continuous_function X ℝ)} :
closure₀ M₀ ⊆ closure₁ M₀ := sorry

lemma closure_le_seq₂ {M₀ : set (bounded_continuous_function X ℝ)} :
closure₁ M₀ = closure₂ M₀ := sorry

/-
The first lemma we need states that:

f ∈ closure₂ M₀ ↔ 
∀ x, y ∈ X, ∀ ε > 0, ∃ f' ∈ closure₀ M₀, such that 
|f(x) - f'(x)| < ε and |f(y) - f'(y)| < ε
-/

/- The forward direction is trivial -/
lemma dense_at_points_in_closure
{M₀ : set (bounded_continuous_function X ℝ)}
{f : bounded_continuous_function X ℝ} 
(h : f ∈ closure₂ M₀) : ∀ x y : X, ∀ ε > 0, 
∃ (g : bounded_continuous_function X ℝ) (H : g ∈ closure₀ M₀), 
abs (f x - g x) < ε ∧ abs (f y - g y) < ε := 
begin
  rcases h with ⟨g, h, hg, hh, h⟩; intros x y ε hε,
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

#check compact.elim_finite_subcover

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

#check finset.sup

instance : semilattice_sup_bot (bounded_continuous_function X ℝ) := sorry

example {M₀ : set (bounded_continuous_function X ℝ)}
{f : bounded_continuous_function X ℝ}
(h : ∀ ε > 0, ∀ x y : X, ∃ (g : bounded_continuous_function X ℝ) 
(H : g ∈ closure₀ M₀), abs (f y - g y) < ε) : 
∀ x : X, ∀ ε > 0, ∃ g : X → ℝ, ∀ z : X, g z < f z + ε := 
begin
  intros x ε hε,
  choose g hg₀ hg₁ using h ε (by {norm_cast, exact hε}) x,
  let S : X → set X := λ y, {z | f z - g y z < ε},
  have hc := _inst_2.1, 
  cases compact.elim_finite_subcover hc S _ _ with I hI,
    { let h := I.sup g,
      refine ⟨h, λ z, _⟩,
      suffices : ∀ i, g i z < f z + ε,
        sorry,
      sorry },
    { sorry },
    intros y hy, exact mem_Union.2 ⟨y, (abs_lt.1 $ hg₁ y).2⟩,
end

example {M₀ : set (bounded_continuous_function X ℝ)}
{f : bounded_continuous_function X ℝ}
(h : ∀ ε > 0, ∀ x y : X, ∃ (g : bounded_continuous_function X ℝ) 
(H : g ∈ closure₀ M₀), abs (f y - g y) < ε) : 
∀ x : X, ∀ ε > 0, ∃ g : X → ℝ, ∀ z : X, g z < f z + ε := sorry

lemma in_closure₂_of_dense_at_points 
{M₀ : set (bounded_continuous_function X ℝ)}
{f : bounded_continuous_function X ℝ}
(h : ∀ x y : X, ∀ ε > 0, ∃ (g : bounded_continuous_function X ℝ) (H : g ∈ closure₀ M₀), 
abs (f x - g x) < ε ∧ abs (f y - g y) < ε) : 
f ∈ closure₂ M₀ := 
begin
  sorry
end

theorem in_closure₂_iff_dense_at_points 
{M₀ : set (bounded_continuous_function X ℝ)}
{f : bounded_continuous_function X ℝ} : 
f ∈ closure₂ M₀ ↔ ∀ x y : X, ∀ ε > 0, 
∃ (g : bounded_continuous_function X ℝ) (H : g ∈ closure₀ M₀), 
abs (f x - g x) < ε ∧ abs (f y - g y) < ε := sorry
