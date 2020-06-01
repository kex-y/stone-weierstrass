import definitions ralgebra

noncomputable theory
open set classical
local attribute [instance] prop_decidable

variables {X : Type*} [metric_space X] [compact_space X]

-- We adopt the notation of bounded countinuous function from mathlib
local infixr ` →ᵇ ` : 25 := bounded_continuous_function

/- This file contains all the non-proven propositions used by main.lean

Most of these lemmas are rather trivial. I aim to present a text proof alongside the 
less trivial propositions. -/

-- compact.elim_finite_subcover require semilattices which we will assume
instance : semilattice_sup_bot (X →ᵇ ℝ) := sorry
instance : semilattice_inf_top (X →ᵇ ℝ) := sorry

variables {M₀ : set (X →ᵇ ℝ)}

-- The following 10 propositions are trivial
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

lemma is_open_aux_set₀ {f : X →ᵇ ℝ} 
{g : X → X →ᵇ ℝ} {ε : ℝ} (hε : ε > 0) : 
∀ y : X, is_open {z : X | f z - (g y) z < ε} := sorry

lemma is_open_aux_set₁ {f : X →ᵇ ℝ} 
{g : X → X →ᵇ ℝ} {ε : ℝ} (hε : ε > 0) : 
∀ x : X, is_open {z : X | g x z < f z + ε} := sorry

lemma neg_inf_eq_sup {f g h : X →ᵇ ℝ} : f = g ⊔ h ↔ -f = -g ⊓ -h := sorry
lemma neg_sup_eq_inf {f g h : X →ᵇ ℝ} : f = g ⊓ h ↔ -f = -g ⊔ -h := sorry

/- Follows by choosing the same δ from hF -/
lemma neg_unif_converges_to {f : X →ᵇ ℝ} {F : ℕ → (X →ᵇ ℝ)} 
(hF : unif_converges_to (λ n, F n) f) : unif_converges_to (λ n, -F n) (-f) := sorry

/- The forward direction is true by mem_univ, the backwards is true by defining the function 
such that ∀ z ∈ ℝ², f : X →ᵇ ℝ, (u : X) ↦ z.1 if u = x, else z.2 -/
lemma boundary_points_of_univ : ∀ x y : X, boundary_points univ x y = univ := sorry

/- This is true since M₀' is a subalgebra ⇒ 1 ∈ M₀'.carrier and 
∀ μ ∈ ℝ, ∀ f ∈ M₀'.carrier, μf ∈ M₀'.carrier ⇒ r • 1 ∈ M₀'.carrier -/
lemma subalgebra_closed_under_smul' {M₀' : subalgebra ℝ (X →ᵇ ℝ)} :
∀ (α : ℝ) {x}, x ∈ M₀'.carrier → α • x ∈ M₀'.carrier := sorry

-- The following 4 propositions are trivial
lemma closure₂_of_closure₂ (M₀ : set (X →ᵇ ℝ)) : 
closure₂ (closure₂ M₀) = closure₂ M₀ := sorry

lemma closure₀_closed_with_sup {M₀ : set (X →ᵇ ℝ)} {f g} 
(hf : f ∈ closure₀ M₀) (hg : g ∈ closure₀ M₀) : f ⊔ g ∈ closure₀ M₀ := sorry

lemma closure₀_closed_with_inf {M₀ : set (X →ᵇ ℝ)} {f g} 
(hf : f ∈ closure₀ M₀) (hg : g ∈ closure₀ M₀) : f ⊓ g ∈ closure₀ M₀ := sorry

lemma closure_le_seq₁ {M₀ : set (X →ᵇ ℝ)} :
closure₀ M₀ ⊆ closure₂ M₀ := sorry

/- To prove `closure₂_subalgebra` we need to first show that `closure₂ M₀'.carrier` 
forms a subring. The is easily shown since M₀'.carrier ⊆ closure₂ M₀'.carrier and 
closure₂ M₀'.carrier is closed.

We also need to show `range_le'` but this also follows directly from M₀'.carrier 
⊆ closure₂ M₀'.carrier. -/
def closure₂_subalgebra (M₀' : subalgebra ℝ (X →ᵇ ℝ)) : subalgebra ℝ (X →ᵇ ℝ) := 
{ carrier := closure₂ M₀'.carrier,
  subring := sorry,
  range_le' := sorry}

/- This is the trivial subalgebra -/
def univ_subalgebra : subalgebra ℝ (X →ᵇ ℝ) := 
{ carrier := univ,
  subring := sorry,
  range_le' := sorry }
