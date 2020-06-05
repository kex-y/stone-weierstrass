# Introduction

I have chosen to do the second subproject - *The Weierstass approximation* theorem for my first year project.

In this project, I have decided to investigate a generalisation of the approximation theorem - *The Stone-Weierstrass theorem* by formalising it in an interactive theorem prover - *Lean*. I will also discuss some immediate result of this theorem one of which is of course the Weierstass approximation theorem.

## The Stone-Weierstass Theorem

The Stone-Weierstass theorem is a general theorem regarding the density of bounded continuous functions on some arbitary space in particular, in its most common form, the compact Hausdorff spaces; however, it has also been generalised to noncompact Tychonoff spaces. In this project, I have decided to take a look at a version of this regarding bounded continuous functions from a compact metric space to the real numbers. 

Stone first prove this theorem in 1937 while a simplified proof was also presented by him in 1948. We shall follow his second proof with some more modern mathematical technics.

## Concepts

Before diving into the the main proof itself, I would first like to introduce some concepts that are not in the first year curriculum. 

### Compact Metric Space

We call a metric space `X` compact if and only if every open cover of `X` admits a finite subcover.

### R-Algebra

While many literatures will use algebras over a field during their proof of the Stone-Weierstrass theorem, we will discover that, in fact, an commutative algebras over a ring (or just R-algebras) suffices. Nonetheless, as we are considering algebras over the real numbers, in the end it does not really matter which one we use. I have decided to use R-algebras as it was easier to work with in Lean.

We define an R-algebra as an mathematical object consisting of a ring R, a semi-ring A, some scalar multiplication `•` that maps an element of R and an element of A to an element of A, and a homomorphism `φ` from R to A such that, for 

- `r • a = φ(r) × a`
- `φ(r) × a = a × φ(r)`

are satisfied for all `r` in R, `a` in A.

We call a subset of an R-algebra a subalgebra if it is closed under the induced operations carried from the R-algebra and we call it a unital subalgebra if and only if it contains the multiplicative identity `1`.

## Definitions

Throughout this presentation I will also be using some definitons.

We will define two lattice operations on the set of bounded continuous functions from X to the reals where X is a compact metric space with the supremum of two functions being their max and the infimum being their min.

It is not hard to see that these two operations are well defined as the max and min of two bounded continuous functions are bounded and continuous.

We will also define the concept of seperates points, boundary points, closure and closure'.

Given a subset M<sub>0</sub> of the bounded continuous functions from X to the reals, we say M<sub>0</sub> seperate points if and only if for all distinct x, y in X there exists some f in M<sub>0</sub> f(x) != f(y). 
We define the boundary points of M<sub>0</sub> as this particular set of points in ℝ<sup>2</sup>. (point to the set)

We define the closure of M<sub>0</sub> as its closure under uniform convergence to the limit, that is to say, a function is in the closure if and only if there is a sequence of functions in M<sub>0</sub> uniformly converging to it. It is not difficult to see that the closure of M<sub>0</sub> is a superset of M<sub>0</sub> as each function uniformly converges to itself.

Lastly, given the boundary points of M<sub>0</sub>, we define the closure' of the boundary points as the closure of M<sub>0</sub> under sequenctial convergence in ℝ<sup>2</sup>.

# Core

Finally we can start talking about the main proof and my formalisation process.

## Lemma 1

The main proof itself relies on two central lemmas which are:

(Read Poster ...)

So let us fix x ∈ X and given y ∈ X write the function satisfying |f(x) - g(x)| < ε ∧ |f(y) - g(y)| < ε, g_y (the existence of which is guarenteed by our hypothesis) 

We then define the set  S(y) := {z ∈ X | f(z) - g_y(z) < ε}. It's obvious that y ∈ S(y) since |f(y) - g_y(y)| < ε by construction, so 

-  X ⊆ ⋃ (y : X) S(y) ⇒ X = ⋃ (y : X) S(y)


Now as X is compact, the cover admits finite subcover of X so there exists points in X, y₁, ⋯, yₙ, such that X = U i ∈ {1, ⋯, n}, S(yᵢ).

So now, by letting p_x := ⊔ i, g_yᵢ, we have ∀ z ∈ X, p_x(z) ≥ g_yₖ(z) > f(z) - ε for some k ∈ {1, ⋯, n} as p_x is greater than any individual g_y.

Now we will define T(x) := {z ∈ X | p_x(z) < f(z) + ε}. As ∀ yᵢ, g_yᵢ(x) < f(x) + ε by h.left, so is p_x(x) < f(x) + ε. Thus, x ∈ T(x) and X ⊆ ⋃ (x : X) T(x) and again as X is compact, there is x₁, ⋯, xₘ, such that   X = U i ∈ {1, ⋯, m}, S(xᵢ). So, by letting h := ⊓ i, g_xᵢ, we have ∀ z ∈ X, h(z) ≤ g_xₖ(z) < f(z) + ε.

Now, as g_xᵢ(z) > f(z) - ε, for all i, so is h(z) > f(z) - ε and hence there is a function in closure₀ M₀ thats arbitarily close to f. 

This was formalised in Lean and is represented by `in_closure₂_iff_dense_at_points` which can be found in `main.lean` in my GitHub repository.

## Lemma 2

Now, before even make sense of lemma 2, we need to make sure ℝ<sup>2</sup> can in fact be an R-algebra over ℝ. 

It is trivial that ℝ form a ring and ℝ<sup>2</sup> a semi ring so it suffices to define the scalar multiplication and homomorphism between the two. These were defined to be 
```
instance R_R2_scalar_mul : 
has_scalar ℝ (ℝ × ℝ) := ⟨λ β x, (β * x.1, β * x.2)⟩

def R_to_R2_hom : ℝ →+* ℝ × ℝ := 
⟨λ β, (β, β), rfl, λ x y, rfl, rfl, λ x y, rfl⟩
```
and it is rather obvious that this satisfy the axioms required. This was formalised in `ralgebra.lean`. 

Now for lemma 2 itself, the whole proof was rather tedious involving using the law of the excluded middle on multiple propositions multiple times. For those who are interested, the formalisation in Lean is named `subalgebra_of_R2` and can be found also in `ralgebra.lean`.

... write more about how I proved the theorem

# Immediate Results

As such a powerful theorem, there are some incredible results we can deduce rightaway. 

## Approximation Theorem

As promised ealier, we shall discuss the Weierstrass approximation theorem.

...

## Trigonometric Polynomials