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
