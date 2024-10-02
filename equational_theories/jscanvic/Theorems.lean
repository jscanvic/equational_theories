import equational_theories.Magma
import equational_theories.Equations
import Mathlib.Tactic.TypeStar

-- x² = x ∘ x
notation:1024 x:1024 "²" => x ∘ x

theorem Equation387_implies_Equation43 (G: Type*) [Magma G] (h: Equation387 G) : Equation43 G := by
  intro x y
  calc
    x ∘ y = y² ∘ x          := h x y    ▸ rfl
    _     = x² ∘ y²         := h y² x   ▸ rfl
    _     = (x² ∘ x) ∘ y²   := h x x    ▸ rfl
    _     = (x²)² ∘ y²      := h x² x   ▸ rfl
    _     = y² ∘ x²         := h y² x²  ▸ rfl
    _     = x² ∘ y          := h x² y   ▸ rfl
    _     = y ∘ x           := h y x    ▸ rfl

-- Theorem. A magma satisfying Eq. 43 does not necessarily satisfy Eq. 387.
theorem Equation43_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation387 G := by
  -- Proof. It amounts to showing that a certain magma satisfies Eq. 43 but not
  -- Eq. 387, which is what we do for the additive magma of natural numbers.
  let G := Nat
  let M: Magma G := Magma.mk fun x y => x + y
  exists G
  exists M
  -- Let's first show that it satisfies Eq. 43.
  apply And.intro
  .
    intro x y
    calc x ∘ y
      _ = x + y   := rfl
      _ = y + x   := by rw [Nat.add_comm]
      _ = y ∘ x   := rfl
  -- Now, let's show that it does not satisfy Eq. 387.
  .
    -- Let's assume by contradiction that it does in fact satisfy Eq. 387.
    intro hc
    -- Applying this equation to x = 0 and y = 1 gives 1 = 2,
    have : 1 = 2 := hc 0 1
    -- which is a contradiction.
    contradiction
