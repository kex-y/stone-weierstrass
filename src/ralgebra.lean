import topology.bounded_continuous_function

noncomputable theory
open set classical
local attribute [instance] prop_decidable

variables {X : Type*} [metric_space X] [compact_space X]

-- We adopt the notation of bounded countinuous function from mathlib
local infixr ` →ᵇ ` : 25 := bounded_continuous_function

-- We now need it to consider both ℝ² and X →ᵇ ℝ (BCF) as algebras. 
instance R_R2_scalar_mul : has_scalar ℝ (ℝ × ℝ) := ⟨λ β x, (β * x.1, β * x.2)⟩

-- We define the natural ring homomorphism from ℝ to ℝ² : β ↦ (β, β)
def R_to_R2_hom : ℝ →+* ℝ × ℝ := 
⟨λ β, (β, β), rfl, λ x y, rfl, rfl, λ x y, rfl⟩

instance : algebra ℝ (ℝ × ℝ) := 
{ commutes' := λ r x, by simp [mul_comm],
  smul_def' := λ r x, rfl,
  .. R_R2_scalar_mul, .. R_to_R2_hom }

/- While we find an algebra already constructed for BCF, it requires 
normed_algebra ℝ ℝ, so we will prove that here.

As ℝ over ℝ is already an R-algebra, we just have to prove the isometry part 
which is true by definition. -/
instance : normed_algebra ℝ ℝ := ⟨λ x, rfl⟩

/- The idea is to first prove that if M₀ is a subalgebra of BCF then its 
boundary points form a subalgebra of ℝ². -/

lemma subalgebra_nonempty (S : subalgebra ℝ (ℝ × ℝ)) : 
∃ x, x ∈ S.carrier := ⟨1, S.2.2.1⟩

lemma subalgebra_closed_under_plus {S : subalgebra ℝ (ℝ × ℝ)} :
∀ (x y), x ∈ S.carrier → y ∈ S.carrier → x + y ∈ S.carrier := S.2.1.1.2

lemma subalgebra_closed_under_mul {S : subalgebra ℝ (ℝ × ℝ)} :
∀ (x y), x ∈ S.carrier → y ∈ S.carrier → x * y ∈ S.carrier := S.2.2.2

-- This should be true since a subalgebra is an algebra so it's closed under smul
lemma subalgebra_closed_under_smul {S : subalgebra ℝ (ℝ × ℝ)} :
∀ (α : ℝ) {x}, x ∈ S.carrier → α • x ∈ S.carrier := sorry

lemma non_zero_fst {S : subalgebra ℝ (ℝ × ℝ)} {β} 
(h : ((β, 0) : ℝ × ℝ) ∈ S.carrier) (hβ : β ≠ 0) : 
∀ γ, ((γ, 0) : ℝ × ℝ) ∈ S.carrier := λ γ,
begin
  convert subalgebra_closed_under_smul (γ / β) h,
  exact ((eq_div_iff hβ).mp rfl).symm, simp only [mul_zero]
end

lemma non_zero_snd {S : subalgebra ℝ (ℝ × ℝ)} {β} 
(h : ((0, β) : ℝ × ℝ) ∈ S.carrier) (hβ : β ≠ 0) : 
∀ γ, ((0, γ) : ℝ × ℝ) ∈ S.carrier := λ γ,
begin
  convert subalgebra_closed_under_smul (γ / β) h,
  simp only [mul_zero], exact ((eq_div_iff hβ).mp rfl).symm
end

lemma non_zero_fst_snd {S : subalgebra ℝ (ℝ × ℝ)} {β γ} 
(h₀ : (β : ℝ × ℝ) ∈ S.carrier) (hβ : β.1 ≠ 0) 
(h₁ : (γ : ℝ × ℝ) ∈ S.carrier) (hγ : γ.2 ≠ 0) 
(hβγ : β ≠ γ) : ∀ δ, δ ∈ S.carrier := λ δ,
begin
  -- The proof of this considers if β.1 ≠ β.2, β and β² are linearly independent
  -- and hence spans the entire space of ℝ²
  sorry
end

lemma non_zero_eq {S : subalgebra ℝ (ℝ × ℝ)} {β} 
(h : (β : ℝ × ℝ) ∈ S.carrier) (hβ : β.1 = β.2) (hnz : β ≠ 0): 
∀ γ, ((γ, γ) : ℝ × ℝ) ∈ S.carrier := λ γ,
begin
  have : β.1 ≠ 0 ∨ β.2 ≠ 0,
    by_contra hn, push_neg at hn, 
    refine hnz (prod.ext hn.1 hn.2),
  cases this; convert subalgebra_closed_under_smul (γ / β.1) h;
    try { rw ←hβ at * }; exact (div_eq_iff this).mp rfl
end

/- We prove by considering all cases that a subalgebra of ℝ² must be a set 
of one of the indicated forms. -/
theorem subalgebra_of_R2 (S : subalgebra ℝ (ℝ × ℝ)) :
S.carrier = {(0, 0)} ∨
S.carrier = {p | ∃ x : ℝ, p = (x, 0)} ∨
S.carrier = {p | ∃ y : ℝ, p = (0, y)} ∨
S.carrier = {p | ∃ z : ℝ, p = (z, z)} ∨ 
S.carrier = univ :=
begin
  by_cases (∀ s : ℝ × ℝ, s ∈ S.carrier → s.1 = s.2),
    { cases em (∀ s : ℝ × ℝ, s ∈ S.carrier → s = 0) with hz hnz,
      cases subalgebra_nonempty S with s hs,
      left, ext, split; intro hx,
        { exact hz _ hx },
        { cases subalgebra_nonempty S with s hs, finish [hz _ hs] },
      push_neg at hnz, cases hnz with s hs,
      iterate 3 { right }, left, ext, split; intro hx,
        { refine ⟨x.1, _⟩, apply prod.ext, refl, rw h x hx },
        { cases hx with z hz, rw hz, exact non_zero_eq hs.1 (h s hs.1) hs.2 z} },
    { push_neg at h, rcases h with ⟨s, hs₀, hs₁⟩,
      by_cases (s.1 = 0), rw h at hs₁,
      cases em (∃ (t : ℝ × ℝ) (ht : t ∈ S.carrier) (ht' : t ≠ s), t.1 ≠ 0) with ht ht,
        { rcases ht with ⟨t, ht₀, ht₁, ht₂⟩, iterate 4 { right },
          ext, split; intro hx,
            exact mem_univ x, exact non_zero_fst_snd ht₀ ht₂ hs₀ hs₁.symm ht₁ x },
        { push_neg at ht, iterate 2 { right }, left, 
          ext, split; intro hx,
            cases em (x = s) with hxs hnxs,
            refine ⟨s.2, _⟩, rw [hxs, ←h], simp only [prod.mk.eta],
            refine ⟨x.2, _⟩, rw ←(ht x hx hnxs), simp only [prod.mk.eta],
            cases hx with p hp, rw hp, 
            refine non_zero_snd _ hs₁.symm p, rw ←h, simp only [prod.mk.eta, hs₀] },
      cases em (∃ (t : ℝ × ℝ) (ht : t ∈ S.carrier) (ht' : t ≠ s), t.2 ≠ 0) with ht ht,
        { rcases ht with ⟨t, ht₀, ht₁, ht₂⟩,
          iterate 4 { right }, ext, split; intro hx,
            exact mem_univ x, exact non_zero_fst_snd hs₀ h ht₀ ht₂ ht₁.symm x },
        { push_neg at ht,
          right, left, ext, split; intro hx,
            cases em (x = s) with hxs hnxs,
            cases em (x.2 = 0) with hz hnz,
            refine ⟨x.1, _⟩, rw ←hz, simp only [prod.mk.eta, hs₀],
            exfalso, have hndouble : s + s ≠ s, 
              suffices : s ≠ 0, simpa only [add_right_eq_self, ne.def],
              intro hs, cases hs, apply h, simp only [],
            have := ht (s + s) (subalgebra_closed_under_plus s s hs₀ hs₀) hndouble,
            have : s.2 = 0, simp at this, linarith [this],
            apply hnz, rwa hxs,
            refine ⟨x.1, _⟩, rw ←(ht x hx hnxs), simp only [prod.mk.eta, hs₀],
            cases hx with p hp, rw hp,
            cases em (s.2 = 0) with hsnd hsnd,
            refine non_zero_fst _ h p,
            rw ←hsnd, simp only [prod.mk.eta, hs₀],
            exfalso, have hndouble : s + s ≠ s, 
              suffices : s ≠ 0, simpa only [add_right_eq_self, ne.def],
              intro hs, cases hs, apply h, simp only [],
            have := ht (s + s) (subalgebra_closed_under_plus s s hs₀ hs₀) hndouble,
            have : s.2 = 0, simp at this, linarith [this],
            contradiction } }
end