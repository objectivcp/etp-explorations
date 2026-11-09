import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41955_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41955 : Equation41955 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41955 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41955 X4 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41955 sK0 sK0 X0 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l5 sK1 sK2]
  have l7 : ∀ X2 X0 sK0 : G, (X2 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X2 X0 sK0
    conv => enter [1]; rw [h41955 X2 X0 (sK0 ◇ sK0) (X2 ◇ X2)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 (X2 ◇ X2) X2]
  have l8 : ∀ X2 X0 sK0 : G, (X2 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X2 X0 sK0
    conv => enter [1]; rw [l7 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X0]
  have l9 : ∀ sK0 X2 X0 : G, (sK0 ◇ sK0) = (X2 ◇ X0) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← l8 X2 X0 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42220 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42220 G := by
  have l0 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))]
  have l1 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK3) = (sK0 ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [h41 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [← l1 w x y]
  conv => enter [1]; rw [l0 w z y]

theorem Equation4512_42220_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42220 : Equation42220 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42220 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42220 X4 X1 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X1]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ X1) X0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ (X1 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42220 sK0 sK0 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l1 sK0 (X1 ◇ X1) X0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK2 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK2 sK1]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42263 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42263 G := by
  have l0 : ∀ sK4 sK2 sK3 : G, (sK4 ◇ sK4) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK4)))) := by
    intro sK4 sK2 sK3
    conv => enter [1]; rw [h41 sK4 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK4)))]
  have l1 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ sK4) = (sK1 ◇ sK0) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [h41 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l1 u x y]
  conv => enter [1]; rw [l0 u z w]

@[equational_result]
theorem Equation42263_implies_Equation41 (G : Type*) [Magma G] (h42263 : Equation42263 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42263 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42263 X5 X6 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation41929 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41929 G := by
  have l0 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ sK0) = (sK2 ◇ sK1) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK2 sK1]
  have l1 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]
  conv => enter [1]; rw [l1 z w y x]

theorem Equation4512_41929_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41929 : Equation41929 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41929 X1 X2 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41929 X0 X1 X1 X1]
  have l1 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [h41929 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
  have l2 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l3 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [h41929 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← l0 (sK1 ◇ sK2) X0 X1]
  have l4 : ∀ X0 X1 X4 : G, ((X0 ◇ X1) ◇ X4) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l2 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [← l0 X4 X1 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X4 X1 sK1 sK2 : G, (X4 ◇ X1) = ((sK1 ◇ sK2) ◇ X4) := by
    intro X4 X1 sK1 sK2
    conv => enter [1]; rw [← l4 X4 X1 X4]
    conv => enter [1]; rw [l3 (X4 ◇ X1) X4 sK1 sK2]
  have l6 : ∀ X1 X0 sK1 sK2 X2 X3 : G, (X1 ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X1 X0 sK1 sK2 X2 X3
    conv => enter [1]; rw [h41929 X1 X0 X2 X3]
    conv => enter [1]; rw [l3 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [l5 (sK1 ◇ sK2) sK2 sK1 sK2]
  have l8 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l6 X1 X0 sK1 sK2 X1 X1]
    conv => enter [1]; rw [l5 (sK1 ◇ sK2) (X0 ◇ (X1 ◇ (X1 ◇ X1))) sK1 sK2]
  have l9 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ X0) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [← l8 X1 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42195 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42195 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK0) = (sK2 ◇ sK3) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK2 sK3]
  have l1 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [← l0 y w x]
  conv => enter [1]; rw [l1 y w z x]

theorem Equation4512_42195_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42195 : Equation42195 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42195 sK0 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h42195 sK1 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h42195 X0 X1 X2 X2]
    conv => enter [1]; rw [← h42195 X2 X0 X2 (X1 ◇ X2)]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ sK2) = (X1 ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l1 sK1 sK2 X1 sK1]
    conv => enter [1]; rw [l2 X1 X1 ((sK1 ◇ sK2) ◇ sK1)]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l0 sK0 X1 sK0]
    conv => enter [1]; rw [l2 X1 X1 ((sK0 ◇ sK0) ◇ sK0)]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l4 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l5 y z x]

@[equational_result]
theorem Equation41_implies_Equation42204 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42204 G := by
  have l0 : ∀ sK4 sK1 sK3 sK0 : G, (sK4 ◇ sK1) = (sK3 ◇ sK0) := by
    intro sK4 sK1 sK3 sK0
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK3 sK0]
  have l1 : ∀ sK4 sK1 sK2 sK3 : G, (sK4 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK4 sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y w u]
  conv => enter [1]; rw [l1 w u z x]

@[equational_result]
theorem Equation42204_implies_Equation41 (G : Type*) [Magma G] (h42204 : Equation42204 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42204 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42204 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 X0 X3 : G, (sK0 ◇ sK0) = (X0 ◇ X3) := by
    intro sK0 X0 X3
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← h42204 X0 X3 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41943 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41943 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK0) = (sK3 ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y w]
  conv => enter [1]; rw [l0 x w y z]

theorem Equation4512_41943_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41943 : Equation41943 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41943 X1 X2 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41943 X0 X1 X1 X1]
  have l2 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X4) = (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41943 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41943 sK0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = (X0 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h41943 X0 sK0 sK0 X1]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41943 X0 (sK0 ◇ sK0) sK0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l6 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X0 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41943 X0 X1 X2 X3]
  have l7 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l6 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l5 X0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1))]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 X1 sK0]
    conv => enter [1]; rw [← h41943 (sK0 ◇ sK0) X1 sK0 sK0]
  have l10 : ∀ X2 X4 X1 : G, (X2 ◇ X4) = (X1 ◇ X4) := by
    intro X2 X4 X1
    conv => enter [1]; rw [l2 X2 X4 X2 X1 X2]
    conv => enter [1]; rw [← h41943 X1 X4 X2 (X2 ◇ X2)]
  have l11 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l7 X1 X2 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X3)) X4]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0) (X0 ◇ sK0)]
    conv => enter [1]; rw [← l8 X0 sK0 sK0]
  have l13 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ X4)) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l11 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [← l1 X4 X1 (X0 ◇ (X0 ◇ X0))]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l15 sK0 sK0 X1]
    conv => enter [1]; rw [l13 sK0 X1 (sK0 ◇ sK0)]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l16 sK0 X1]
  have l18 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l18 y z x]

@[equational_result]
theorem Equation41_implies_Equation42208 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42208 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK0) = (sK3 ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l1 x y w]
  conv => enter [1]; rw [l0 x w z y]

theorem Equation4512_42208_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42208 : Equation42208 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42208 sK0 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h42208 X1 X2 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h42208 X0 X1 X2 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X1 X0]
    conv => enter [1]; rw [← l1 ((sK0 ◇ sK0) ◇ X0) X1 X1]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = ((X1 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42208 sK0 X1 X0 sK0]
    conv => enter [1]; rw [← l1 (X1 ◇ (sK0 ◇ sK0)) X0 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l5 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK0) X0]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 sK0 X1]
    conv => enter [1]; rw [← l1 X1 (sK0 ◇ sK0) sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l1 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0 X1 X0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) X0 sK0]
  have l11 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (X0 ◇ (X1 ◇ sK0)))]
    conv => enter [1]; rw [← h42208 X1 X0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation41_implies_Equation42243 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42243 G := by
  have l0 : ∀ sK4 sK1 sK2 sK3 : G, (sK4 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK4 sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))]
  have l1 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ sK1) = (sK4 ◇ sK0) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l1 x y u]
  conv => enter [1]; rw [l0 x u z w]

@[equational_result]
theorem Equation42243_implies_Equation41 (G : Type*) [Magma G] (h42243 : Equation42243 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42243 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42243 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 X1 X3 : G, (sK0 ◇ sK0) = (X1 ◇ X3) := by
    intro sK0 X1 X3
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ (sK0 ◇ (X1 ◇ sK0)))]
    conv => enter [1]; rw [← h42243 X1 X3 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41952 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41952 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ sK1) = (sK3 ◇ sK0) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y w]
  conv => enter [1]; rw [l0 w x y z]

theorem Equation4512_41952_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41952 : Equation41952 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41952 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ X4) = (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [h41952 X3 X4 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X3 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h41952 X0 X1 X2 X3]
  have l3 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [l2 X1 X2 X3 X0 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l4 : ∀ X3 X4 X2 : G, (X3 ◇ X4) = ((X2 ◇ X3) ◇ X4) := by
    intro X3 X4 X2
    conv => enter [1]; rw [l1 X3 X4 X3 X3 X2]
    conv => enter [1]; rw [← h41952 (X2 ◇ X3) X4 X3 X3]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0]
    conv => enter [1]; rw [← h41952 (sK0 ◇ sK0) X0 sK0 sK0]
  have l6 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l3 X1 X2 X3 X0 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ X0)) X4]
  have l7 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l6 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X3 ◇ X0) X4]
  have l8 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ X4)) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l7 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [← h41952 X4 X1 X0 (X0 ◇ X0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ X2 sK2 sK1 X0 X1 : G, (X2 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 sK2 sK1 X0 X1
    conv => enter [1]; rw [h41952 X2 sK2 X0 X1]
    conv => enter [1, 2]; rw [l4 sK2 (X0 ◇ (X1 ◇ X2)) sK1]
  have l11 : ∀ X2 sK2 X0 X1 sK1 : G, (X2 ◇ sK2) = ((X0 ◇ (X1 ◇ X2)) ◇ (sK1 ◇ sK2)) := by
    intro X2 sK2 X0 X1 sK1
    conv => enter [1]; rw [l10 X2 sK2 sK1 X0 X1]
    conv => enter [1]; rw [l8 sK2 (sK1 ◇ sK2) (X0 ◇ (X1 ◇ X2))]
  have l12 : ∀ X2 sK2 X0 X1 sK1 : G, (X2 ◇ sK2) = (X0 ◇ ((X1 ◇ X2) ◇ (sK1 ◇ sK2))) := by
    intro X2 sK2 X0 X1 sK1
    conv => enter [1]; rw [l11 X2 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X2) (sK1 ◇ sK2)]
  have l13 : ∀ X2 sK2 sK1 X1 : G, (X2 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro X2 sK2 sK1 X1
    conv => enter [1]; rw [l12 X2 sK2 X2 X1 sK1]
    conv => enter [1]; rw [l8 X2 (X1 ◇ X2) (sK1 ◇ sK2)]
  have l14 : ∀ X2 sK2 X1 : G, (X2 ◇ sK2) = (X2 ◇ X1) := by
    intro X2 sK2 X1
    conv => enter [1]; rw [l13 X2 sK2 X2 X1]
    conv => enter [1]; rw [l8 (X2 ◇ sK2) X1 X2]
  have l15 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l14 sK1 sK2 (sK2 ◇ X0)]
    conv => enter [1]; rw [h4512 sK1 sK2 X0]
  have l16 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l4 X0 X1 sK1]
    conv => enter [1, 1]; rw [l14 sK1 X0 sK2]
  have l17 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l16 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l15 sK1 sK2 X1]
  have l18 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK0]
  intro x y z
  conv => enter [1]; rw [← l18 y z x]

@[equational_result]
theorem Equation41_implies_Equation42217 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42217 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK0) = (sK0 ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [← l1 w x y]
  conv => enter [1]; rw [l0 w x z y]

theorem Equation4512_42217_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42217 : Equation42217 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42217 sK0 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X2 X1 X3 X0 X4 : G, (X2 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X0))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X2 X1 X3 X0 X4
    conv => enter [1]; rw [h4512 X2 (X2 ◇ (X1 ◇ (X3 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h42217 X0 X1 X2 X3]
  have l2 : ∀ X2 X1 X3 X0 X4 : G, (X2 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X0))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X2 X1 X3 X0 X4
    conv => enter [1]; rw [l1 X2 X1 X3 X0 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l0 sK0 X1 sK0]
    conv => enter [1]; rw [← h42217 (sK0 ◇ sK0) X1 sK0 sK0]
  have l4 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X2 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l2 X2 X1 X3 X0 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ (X3 ◇ X0)) X4]
  have l5 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X2 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X0) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l4 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X3 ◇ X0) X4]
  have l6 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ X4)) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l5 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [← h42217 X4 X1 X0 (X0 ◇ X0)]
  have l7 : ∀ X2 X0 sK0 X1 : G, (X2 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 sK0 X1
    conv => enter [1]; rw [h42217 X2 X0 sK0 X1]
    conv => enter [1, 2]; rw [l3 sK0 (X0 ◇ (X1 ◇ X2))]
  have l8 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ sK0)) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [l7 X2 X0 sK0 X1]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) (X0 ◇ (X1 ◇ X2))]
  have l9 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ X0) = (X0 ◇ ((X1 ◇ X2) ◇ (sK0 ◇ sK0))) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [l8 X2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X2) (sK0 ◇ sK0)]
  have l10 : ∀ X2 X0 sK0 X1 : G, (X2 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X2 X0 sK0 X1
    conv => enter [1]; rw [l9 X2 X0 X1 sK0]
    conv => enter [1]; rw [l6 X0 (X1 ◇ X2) (sK0 ◇ sK0)]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l10 X2 X0 X2 X1]
    conv => enter [1]; rw [l6 (X2 ◇ X2) X1 X2]
  have l12 : ∀ sK0 X2 X0 : G, (sK0 ◇ sK0) = (X2 ◇ X0) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l11 sK0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ X2)))]
    conv => enter [1]; rw [← h42217 X2 X0 sK0 sK0]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1]
    conv => enter [1]; rw [l12 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42244 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42244 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ sK3 sK0 : G, (sK3 ◇ sK0) = (sK0 ◇ sK3) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [l0 y x z w]

theorem Equation4512_42244_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42244 : Equation42244 G) : Equation41 G := by
  have l0 : ∀ X4 X5 X1 X0 X2 X3 : G, ((X4 ◇ (X5 ◇ (X1 ◇ X0))) ◇ X4) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := by
    intro X4 X5 X1 X0 X2 X3
    conv => enter [1]; rw [h42244 (X4 ◇ (X5 ◇ (X1 ◇ X0))) X4 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h42244 X0 X1 X4 X5]
  have l1 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h42244 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X3 X2 X4 X0 X1 : G, (X3 ◇ X2) = (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X2 X4 X0 X1
    conv => enter [1]; rw [h42244 X3 X2 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = ((X2 ◇ X3) ◇ X1) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l2 X3 X2 X3 X3 X1]
    conv => enter [1]; rw [← h42244 (X2 ◇ X3) X1 X3 X3]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1 X2 X2]
    conv => enter [1]; rw [← h42244 (X1 ◇ X2) X0 X2 X2]
  have l5 : ∀ X1 X0 X4 X5 : G, (X1 ◇ X0) = ((X4 ◇ (X5 ◇ (X1 ◇ X0))) ◇ X4) := by
    intro X1 X0 X4 X5
    conv => enter [1]; rw [h42244 X1 X0 X1 X1]
    conv => enter [1]; rw [← l0 X4 X5 X1 X0 X1 X1]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l4 X2 X0 X1]
    conv => enter [1]; rw [← l3 X2 X1 X0]
  have l7 : ∀ X1 X0 X4 X5 : G, (X1 ◇ X0) = (X4 ◇ ((X5 ◇ (X1 ◇ X0)) ◇ X4)) := by
    intro X1 X0 X4 X5
    conv => enter [1]; rw [l5 X1 X0 X4 X5]
    conv => enter [1]; rw [← h4512 X4 (X5 ◇ (X1 ◇ X0)) X4]
  have l8 : ∀ X1 X0 X4 : G, (X1 ◇ X0) = (X4 ◇ X4) := by
    intro X1 X0 X4
    conv => enter [1]; rw [l7 X1 X0 X4 X1]
    conv => enter [1]; rw [l6 X4 (X1 ◇ (X1 ◇ X0)) X4]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1]; rw [l8 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42259 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42259 G := by
  have l0 : ∀ sK4 sK1 sK2 sK3 : G, (sK4 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK4 sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))]
  have l1 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l1 u x y]
  conv => enter [1]; rw [l0 u x z w]

@[equational_result]
theorem Equation42259_implies_Equation41 (G : Type*) [Magma G] (h42259 : Equation42259 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42259 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42259 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = (X2 ◇ X3) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ X2)))]
    conv => enter [1]; rw [← h42259 X2 X3 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41956 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41956 G := by
  have l0 : ∀ sK4 sK1 sK2 sK3 : G, (sK4 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK4 sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))]
  have l1 : ∀ sK4 sK1 sK0 sK2 : G, (sK4 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK4 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l1 x y w u]
  conv => enter [1]; rw [l0 w u y z]

theorem Equation4512_41956_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41956 : Equation41956 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X5 ◇ X1) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41956 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41956 X5 X1 X0 X0 X0]
  have l1 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41956 sK0 sK0 X0 X1 X2]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l1 sK0 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ X2))]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l5 sK1 sK2]
  have l7 : ∀ X4 X0 sK0 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X4 X0 sK0
    conv => enter [1]; rw [h41956 X4 X0 (sK0 ◇ sK0) X4 (X4 ◇ X4)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 X4 X4 X4]
  have l8 : ∀ X4 X0 sK0 : G, (X4 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X4 X0 sK0
    conv => enter [1]; rw [l7 X4 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X0]
  have l9 : ∀ sK0 X4 X0 : G, (sK0 ◇ sK0) = (X4 ◇ X0) := by
    intro sK0 X4 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← l8 X4 X0 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42221 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42221 G := by
  have l0 : ∀ sK4 sK1 sK2 sK3 : G, (sK4 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK4 sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))]
  have l1 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ sK1) = (sK0 ◇ sK3) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l1 x y w u]
  conv => enter [1]; rw [l0 w u z y]

theorem Equation4512_42221_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42221 : Equation42221 G) : Equation41 G := by
  have l0 : ∀ X2 X0 X1 X5 : G, (X2 ◇ (X0 ◇ X1)) = (X5 ◇ X2) := by
    intro X2 X0 X1 X5
    conv => enter [1, 2]; rw [h42221 X0 X1 X2 X2 X2]
    conv => enter [1]; rw [← h42221 X5 X2 X2 X1 (X2 ◇ X2)]
  have l1 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X5 ◇ X1) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42221 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42221 X5 X1 X0 X0 X0]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0 sK1]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ sK0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 sK0 X1 X0]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← l4 sK0 X1 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

@[equational_result]
theorem Equation41_implies_Equation42248 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42248 G := by
  have l0 : ∀ sK4 sK1 sK2 sK3 : G, (sK4 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK4 sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))]
  have l1 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ sK1) = (sK0 ◇ sK4) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK4 sK4 sK1]
    conv => enter [1]; rw [h41 sK4 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [← l1 y u x]
  conv => enter [1]; rw [l0 y u z w]

theorem Equation4512_42248_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42248 : Equation42248 G) : Equation41 G := by
  have l0 : ∀ X2 X0 X1 X5 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X5 ◇ X3) := by
    intro X2 X0 X1 X5 X3
    conv => enter [1, 2]; rw [h42248 X0 X1 X2 X3 X2]
    conv => enter [1]; rw [← h42248 X5 X3 X2 X2 (X1 ◇ X2)]
  have l1 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X5 ◇ X1) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42248 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42248 X5 X1 X0 X0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l5 : ∀ X0 X1 X6 X4 : G, (X0 ◇ X1) = (X6 ◇ X4) := by
    intro X0 X1 X6 X4
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X4 ◇ X0)) X0 X1]
    conv => enter [1]; rw [← h42248 X6 X4 X0 X0 X0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l5 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42264 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42264 G := by
  have l0 : ∀ sK5 sK2 sK3 sK4 : G, (sK5 ◇ sK2) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK5 ◇ sK2)))) := by
    intro sK5 sK2 sK3 sK4
    conv => enter [1]; rw [← h41 sK5 sK5 sK2]
    conv => enter [1]; rw [h41 sK5 sK3 (sK3 ◇ (sK4 ◇ (sK5 ◇ sK2)))]
  have l1 : ∀ sK0 sK1 sK5 sK2 : G, (sK0 ◇ sK1) = (sK5 ◇ sK2) := by
    intro sK0 sK1 sK5 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK5 sK2]
  intro x y z w u v
  conv => enter [1]; rw [l1 x y u v]
  conv => enter [1]; rw [l0 u v z w]

@[equational_result]
theorem Equation42264_implies_Equation41 (G : Type*) [Magma G] (h42264 : Equation42264 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X6 X7 : G, (X0 ◇ X1) = (X6 ◇ X7) := by
    intro X0 X1 X6 X7
    conv => enter [1]; rw [h42264 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42264 X6 X7 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation308_implies_Equation3254 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation3254 G := by
  intro x y
  conv => enter [1]; rw [h308 x (x ◇ y)]

theorem Equation3254_4512_implies_Equation308 (G : Type*) [Magma G] (h3254 : Equation3254 G) (h4512 : Equation4512 G) : Equation308 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h3254 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h3254 X0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h3254 sK0 sK0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h3254 X0 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) X0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3254 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation308_implies_Equation3257 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation3257 G := by
  intro x y z
  conv => enter [1]; rw [h308 x (y ◇ z)]

theorem Equation3257_4512_implies_Equation308 (G : Type*) [Magma G] (h3257 : Equation3257 G) (h4512 : Equation4512 G) : Equation308 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3257 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3257 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h3257 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 X0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation308_implies_Equation41530 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation41530 G := by
  intro x y
  conv => enter [1]; rw [h308 x (x ◇ (x ◇ y))]

theorem Equation4512_41530_implies_Equation308 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41530 : Equation41530 G) : Equation308 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41530 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41530 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l12 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 X0 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation308_implies_Equation41532 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation41532 G := by
  intro x y
  conv => enter [1]; rw [h308 x (x ◇ (y ◇ y))]

theorem Equation4512_41532_implies_Equation308 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41532 : Equation41532 G) : Equation308 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41532 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41532 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l6 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l3 sK0 X0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X0))]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l9 sK0 (X0 ◇ X0)]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 sK1]
  have l15 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 (sK1 ◇ (sK1 ◇ (X0 ◇ X0))) sK1]
    conv => enter [1, 2]; rw [← h41532 sK1 X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1 X0]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK1 ◇ (X0 ◇ X0))]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [← l15 sK0 (X0 ◇ X0) sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation308_implies_Equation41533 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation41533 G := by
  intro x y z
  conv => enter [1]; rw [h308 x (x ◇ (y ◇ z))]

theorem Equation4512_41533_implies_Equation308 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41533 : Equation41533 G) : Equation308 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41533 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41533 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41533 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l6 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))]
  have l10 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l12 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41533 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [← l10 X0 X3 X0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l11 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← l12 (sK0 ◇ sK0) X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l14 sK0 X0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation308_implies_Equation41535 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation41535 G := by
  intro x y
  conv => enter [1]; rw [h308 x (y ◇ (x ◇ y))]

theorem Equation4512_41535_implies_Equation308 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41535 : Equation41535 G) : Equation308 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41535 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41535 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41535 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41535 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41535 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ X0))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41535 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l13 sK0 sK0]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK0 sK1 (X0 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l18 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l14 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1, 2]; rw [← l16 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l21 sK0]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) sK1]
    conv => enter [1, 2]; rw [← h41535 (sK0 ◇ sK1) X0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l18 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l23 sK0 sK1 X0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l25 sK0 sK1 X0]
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l17 sK0 sK1 sK0]
    conv => enter [1]; rw [← l26 sK0 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l31 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l33 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2]; rw [← l32 sK0 sK1]
  have l35 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l36 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l35 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l37 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l36 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l33 sK0 X0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41535 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l34 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1, 2]; rw [← l37 sK0 (sK0 ◇ sK0) sK1]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l41 sK0 sK1]
  have l43 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l44 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l45 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l44 sK0 sK1 X0]
    conv => enter [1]; rw [← l31 sK0 (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) sK1]
  have l46 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l45 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l49 x y]

@[equational_result]
theorem Equation308_implies_Equation41536 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation41536 G := by
  intro x y z
  conv => enter [1]; rw [h308 x (y ◇ (x ◇ z))]

theorem Equation4512_41536_implies_Equation308 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41536 : Equation41536 G) : Equation308 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h41536 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41536 X0 X1 X2]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41536 sK0 X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ X1)))]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ (sK0 ◇ X1))]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0 sK0]
  have l7 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l5 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X2)) X3]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l0 sK0 sK0]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l7 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l9 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41536 X0 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l11 X0 X3 X0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← l13 (sK0 ◇ sK0) X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation308_implies_Equation41539 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation41539 G := by
  intro x y z
  conv => enter [1]; rw [h308 x (y ◇ (y ◇ z))]

theorem Equation4512_41539_implies_Equation308 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41539 : Equation41539 G) : Equation308 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41539 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41539 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l3 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l7 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l7 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41539 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l8 sK0 sK0]
  have l11 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41539 X0 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l9 X0 X3 X0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← l11 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation308_implies_Equation41541 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation41541 G := by
  intro x y z
  conv => enter [1]; rw [h308 x (y ◇ (z ◇ y))]

theorem Equation4512_41541_implies_Equation308 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41541 : Equation41541 G) : Equation308 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41541 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X1))) X3]
    conv => enter [1, 1]; rw [← h41541 X0 X1 X2]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41541 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ sK1)]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X1)) X3]
  have l7 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l7 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l11 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h41541 X0 (X1 ◇ (X2 ◇ X1)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0 X1 X2]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l11 X0 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X1) (sK0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l14 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X1 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK0 sK1 (X0 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 X0 X0 sK0]
    conv => enter [1]; rw [← l8 X0 (sK0 ◇ sK0) X0 X0]
  have l17 : ∀ sK0 X1 sK1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 X1 sK1 X0
    conv => enter [1, 1]; rw [l9 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ (sK0 ◇ sK1)) X1]
  have l18 : ∀ sK0 X1 sK1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l17 sK0 X1 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l19 : ∀ sK0 X1 sK1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((X0 ◇ ((sK0 ◇ sK1) ◇ X0)) ◇ X1)) := by
    intro sK0 X1 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) X1]
  have l20 : ∀ sK0 X1 sK1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l19 sK0 X1 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 ((sK0 ◇ sK1) ◇ X0) X1]
  have l21 : ∀ sK0 X1 sK1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l20 sK0 X1 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) X0 X1]
  have l22 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l18 sK0 (X0 ◇ X1) sK0 X0]
    conv => enter [1]; rw [← l21 sK0 X1 sK0 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l16 X0 sK0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [l22 sK0 (X0 ◇ (sK0 ◇ sK0)) (X0 ◇ X0)]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [l22 sK0 X0 X0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l26 x y]

@[equational_result]
theorem Equation308_implies_Equation41542 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation41542 G := by
  intro x y z
  conv => enter [1]; rw [h308 x (y ◇ (z ◇ z))]

theorem Equation4512_41542_implies_Equation308 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41542 : Equation41542 G) : Equation308 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h41542 X0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41542 X0 (X0 ◇ X0) X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41542 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ X0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK1]
  have l9 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation308_implies_Equation41543 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation41543 G := by
  intro x y z w
  conv => enter [1]; rw [h308 x (y ◇ (z ◇ w))]

theorem Equation4512_41543_implies_Equation308 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41543 : Equation41543 G) : Equation308 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41543 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ X1)]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ X1)]
  have l2 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l1 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation310_implies_Equation3262 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation3262 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h310 sK0 sK1]
    conv => enter [1, 2]; rw [h310 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3262_4512_implies_Equation310 (G : Type*) [Magma G] (h3262 : Equation3262 G) (h4512 : Equation4512 G) : Equation310 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3262 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h3262 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3262 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK1) sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3262 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK1) sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation310_4512_implies_Equation3263 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation3263 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1 sK0]
  have l3 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l2 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l4 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X2 X1 sK0
    conv => enter [1, 1]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l5 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [h310 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l5 X0 X1 sK0]
  have l7 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [l4 X0 X2 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l8 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l3 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l9 : ∀ X0 X2 X1 sK0 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l7 X0 X2 X1 sK0]
  have l10 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← l8 X0 sK0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h310 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [l6 X0 X1 sK0]
  have l13 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l0 X1 X0 X0]
    conv => enter [1, 2]; rw [l6 X0 X0 sK0]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l13 X1 X0 sK0]
    conv => enter [1]; rw [l10 X1 X0 sK0 X0]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l12 X0 sK0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l15 X0 X1 X0]
  have l17 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [← l16 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l18 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l17 sK1 sK2 X0]
    conv => enter [1]; rw [← l16 sK1 X0]
  have l19 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l16 sK1 sK2]
    conv => enter [1]; rw [← l18 sK1 sK2 X0]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l19 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l21 x y z]

@[equational_result]
theorem Equation3263_implies_Equation310 (G : Type*) [Magma G] (h3263 : Equation3263 G) : Equation310 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3263 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3263 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation310_implies_Equation3266 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation3266 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [h310 X0 sK2]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 X0]
    conv => enter [1, 2]; rw [l1 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation3266_implies_Equation310 (G : Type*) [Magma G] (h3266 : Equation3266 G) : Equation310 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3266 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h3266 X0 (X1 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation310_4512_implies_Equation41545 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation41545 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h310 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h310 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation4512_41545_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41545 : Equation41545 G) : Equation310 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41545 sK0 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h41545 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h41545 X0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41545 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41545 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41545 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (X0 ◇ X1)))]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41545 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ X0)))]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h41545 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l14 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41545 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41545 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l19 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l13 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l20 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ sK1)]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)))]
  have l22 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l25 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l19 X0]
    conv => enter [1, 2]; rw [← h41545 X0 X0]
  have l26 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l26 sK0]
  have l28 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [l3 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l29 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l28 sK1]
  have l30 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1, 2]; rw [← l29 sK1]
  have l31 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l22 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l31 sK0]
  have l33 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1, 2]; rw [← l32 sK0]
  have l34 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l25 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l35 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l34 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1]
    conv => enter [1]; rw [l37 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
  have l40 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))))]
  have l41 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l40 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l35 sK1 X0]
  have l42 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l41 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l39 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l25 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l44 sK0 sK1]
  have l46 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0) X0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l46 sK0 (sK1 ◇ sK1) sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l50 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 (sK0 ◇ sK0)]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1, 2]; rw [← l50 sK0 (sK0 ◇ sK0) sK1]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1, 2]; rw [← l27 sK0]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0]
    conv => enter [1, 2]; rw [← l33 sK0]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l54 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l55 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l56 x y]

theorem Equation310_4512_implies_Equation41546 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation41546 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [l0 X0 X1 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK2) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [h310 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 sK2]
  have l4 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) sK2 X0]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK2) = ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 sK2 sK2]
    conv => enter [1, 2]; rw [h310 sK2 sK0]
  have l6 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [← l5 sK0 sK2]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
    conv => enter [1]; rw [← l6 sK0 sK2]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l7 sK0 sK2]
  have l9 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l8 sK0 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h310 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_41546_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41546 : Equation41546 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41546 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41546 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ X0))]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 X0]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l6 : ∀ sK0 X1 sK1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK0 X1 sK1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ sK0) ◇ X0) X1]
  have l7 : ∀ sK0 X1 sK1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l6 sK0 X1 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l7 sK0 X1 sK0 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41546 X0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l8 sK0 (X0 ◇ (X0 ◇ X0))]
  have l11 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))]
    conv => enter [1]; rw [← h41546 (sK1 ◇ sK1) (sK1 ◇ sK1) sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1]; rw [l10 (sK1 ◇ sK1) sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation310_4512_implies_Equation41549 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation41549 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [← h310 (X0 ◇ X1) X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l4 X0 X2 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X1]
    conv => enter [1]; rw [← l5 X0 X1 X1]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← l7 X0 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l0 x y x]
  conv => enter [1]; rw [l3 x y x]
  conv => enter [1]; rw [← l9 x y z]

theorem Equation4512_41549_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41549 : Equation41549 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41549 X0 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41549 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41549 (sK1 ◇ sK1) sK1 X0]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1, 2, 2]; rw [l0 sK1 X0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41549 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l4 sK1 sK1]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l6 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X2)) X3]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l10 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l9 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l11 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41549 X0 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l10 X0 X3 X0 X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l7 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 X0]
    conv => enter [1]; rw [← l11 (sK1 ◇ sK1) X0]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [← l14 sK1 X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l15 sK1 X0]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1]; rw [← l18 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l19 x y]

@[equational_result]
theorem Equation310_implies_Equation41552 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation41552 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h310 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y x z]

theorem Equation4512_41552_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41552 : Equation41552 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h41552 X0 X1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h41552 X0 (X0 ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h41552 X1 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41552 (X0 ◇ X0) X1 X0]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h41552 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l4 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X1 ◇ X1))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h41552 sK1 X0 X1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ (X1 ◇ X1)))]
  have l5 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X1 ◇ X1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l5 sK1 sK1 sK1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← l1 X0 X0]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation310_4512_implies_Equation41556 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation41556 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [h310 X0 sK0]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1 sK0]
  have l4 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l3 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l5 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X2 X1 sK0
    conv => enter [1, 1]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l6 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [h310 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l6 X0 X1 sK0]
  have l9 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [l5 X0 X2 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l10 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l4 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l11 : ∀ X0 X2 X1 sK0 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l9 X0 X2 X1 sK0]
  have l12 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← l10 X0 sK0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [l8 X0 X1 sK0]
  have l14 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l0 X1 X0 X0]
    conv => enter [1, 2]; rw [l8 X0 X0 sK0]
  have l15 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l14 X1 X0 sK0]
    conv => enter [1]; rw [l12 X1 X0 sK0 X0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l11 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l13 X0 sK0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l16 X0 X1 X0]
  have l18 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0))]
  have l19 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l17 sK1 (sK0 ◇ sK2)]
  have l20 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [← l17 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l21 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) = (sK1 ◇ sK1) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l17 sK1 X0]
  have l22 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l17 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l21 sK1 sK0 sK2 X0]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← l22 sK1 sK0 sK2 X0]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l22 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l23 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l19 X0 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l24 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l26 x y z]

theorem Equation4512_41556_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41556 : Equation41556 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41556 sK1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h41556 X0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l1 sK1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation310_implies_Equation41558 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation41558 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h310 sK1 sK1]
    conv => enter [1, 2]; rw [h310 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h310 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_41558_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41558 : Equation41558 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h41558 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h41558 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1]
    conv => enter [1]; rw [← h41558 (sK1 ◇ sK1) sK1]
  have l4 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 sK1]
    conv => enter [1, 2]; rw [← h41558 (sK1 ◇ sK1) sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41558 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l3 sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l4 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l6 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1]
    conv => enter [1]; rw [← l7 sK1]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l11 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l11 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l13 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41558 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK1]
  have l14 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l13 X0 sK1]
    conv => enter [1, 2]; rw [← l12 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l14 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l15 X0 sK1]
    conv => enter [1, 2]; rw [← l5 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation310_4512_implies_Equation41559 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation41559 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [h310 X0 sK0]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1 sK0]
  have l4 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l3 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l5 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X2 X1 sK0
    conv => enter [1, 1]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l6 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [h310 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l6 X0 X1 sK0]
  have l8 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [l5 X0 X2 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l9 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l4 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l10 : ∀ X0 X2 X1 sK0 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l8 X0 X2 X1 sK0]
  have l11 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← l9 X0 sK0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [l7 X0 X1 sK0]
  have l13 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l0 X1 X0 X0]
    conv => enter [1, 2]; rw [l7 X0 X0 sK0]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l13 X1 X0 sK0]
    conv => enter [1]; rw [l11 X1 X0 sK0 X0]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l12 X0 sK0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l15 X0 X1 X0]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l16 sK1 sK2]
    conv => enter [1]; rw [l16 sK1 (sK1 ◇ sK2)]
  have l18 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l16 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l17 sK1 sK2]
    conv => enter [1]; rw [← l18 sK0 sK0 sK1 sK2]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h310 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

theorem Equation4512_41559_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41559 : Equation41559 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h41559 X1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41559 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41559 X0 X0 X1]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41559 (sK1 ◇ sK1) sK1 X0]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ X0))]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 (sK1 ◇ X0)]
  have l5 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK1 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation310_4512_implies_Equation41561 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation41561 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [h310 X0 sK0]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1 sK0]
  have l4 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l3 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l5 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X2 X1 sK0
    conv => enter [1, 1]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l6 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [h310 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l6 X0 X1 sK0]
  have l9 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [l5 X0 X2 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l10 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l4 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l11 : ∀ X0 X2 X1 sK0 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l9 X0 X2 X1 sK0]
  have l12 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← l10 X0 sK0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [l8 X0 X1 sK0]
  have l14 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l0 X1 X0 X0]
    conv => enter [1, 2]; rw [l8 X0 X0 sK0]
  have l15 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l14 X1 X0 sK0]
    conv => enter [1]; rw [l12 X1 X0 sK0 X0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l11 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l13 X0 sK0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l16 X0 X1 X0]
  have l18 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))]
  have l19 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l17 sK1 (sK2 ◇ sK1)]
  have l20 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [← l17 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l21 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK1 ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK2 X0]
    conv => enter [1]; rw [← l17 sK1 X0]
  have l22 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l17 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l21 sK1 sK2 X0]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← l22 sK1 sK2 X0]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l22 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l23 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l19 X0 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l24 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l26 x y z]

theorem Equation4512_41561_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41561 : Equation41561 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41561 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41561 X0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation310_implies_Equation41562 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation41562 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h310 X0 sK1]
    conv => enter [1, 2]; rw [h310 sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h310 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4512_41562_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41562 : Equation41562 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h41562 X1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X0)]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41562 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (X0 ◇ X0))]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41562 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h41562 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h41562 (sK0 ◇ (sK1 ◇ sK1)) sK0 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41562 (sK0 ◇ sK0) sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l8 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK1)) sK1 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0]
  have l11 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l7 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l14 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l11 sK0 X0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41562 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l14 sK0 ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l19 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41562 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK0 ◇ sK0)]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41562 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h41562 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 sK0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l22 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l21 X0 sK0]
    conv => enter [1, 2]; rw [← l18 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0)]
  have l25 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1 sK1 sK1]
    conv => enter [1]; rw [← l24 sK1 sK1]
  have l26 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l25 sK1]
    conv => enter [1]; rw [l0 sK1 sK1]
  have l27 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l26 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l28 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [l22 (sK1 ◇ sK1) sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l31 x y]

theorem Equation310_4512_implies_Equation41563 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation41563 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK1]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [h310 X0 sK1]
  have l3 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h310 X0 sK1]
    conv => enter [1]; rw [l1 X0 X1 sK1]
  have l4 : ∀ X0 sK1 X2 X1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2)) := by
    intro X0 sK1 X2 X1
    conv => enter [1, 1]; rw [l3 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK1 ◇ sK1)) X2]
  have l5 : ∀ X0 X2 X1 sK1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2)) := by
    intro X0 X2 X1 sK1
    conv => enter [1, 1]; rw [l1 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK1 ◇ sK1)) X2]
  have l6 : ∀ X0 X1 sK1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1, 1]; rw [h310 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l6 X0 X1 sK1]
  have l9 : ∀ X0 X2 X1 sK1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2))) := by
    intro X0 X2 X1 sK1
    conv => enter [1]; rw [l5 X0 X2 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK1 ◇ sK1) X2]
  have l10 : ∀ X0 sK1 X2 X1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2))) := by
    intro X0 sK1 X2 X1
    conv => enter [1]; rw [l4 X0 sK1 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK1 ◇ sK1) X2]
  have l11 : ∀ X0 X2 X1 sK1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2))) := by
    intro X0 X2 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l9 X0 X2 X1 sK1]
  have l12 : ∀ X0 X1 sK1 X2 : G, (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2))) = (X0 ◇ ((sK1 ◇ sK1) ◇ X2)) := by
    intro X0 X1 sK1 X2
    conv => enter [1]; rw [← l10 X0 sK1 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X2]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 X0 sK1]
    conv => enter [1]; rw [← l13 sK1 X0]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l14 sK1 X0]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h310 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l17 : ∀ sK1 X0 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1, 1]; rw [l16 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l18 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ X1) sK1]
    conv => enter [1, 2]; rw [l8 X0 X1 sK1]
  have l19 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l0 X1 X0 X0]
    conv => enter [1, 2]; rw [l8 X0 X0 sK1]
  have l20 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 sK1 X0]
    conv => enter [1]; rw [l8 X0 X0 sK1]
  have l21 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l19 X1 X0 sK1]
    conv => enter [1]; rw [l12 X1 X0 sK1 X0]
  have l22 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l11 X0 X1 X0 sK1]
    conv => enter [1]; rw [← l18 X0 sK1 X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l22 X0 X1 X0]
  have l24 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l20 (sK1 ◇ X0) sK1]
    conv => enter [1, 2]; rw [← l15 sK1 X0]
  have l25 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l24 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 ((sK1 ◇ sK1) ◇ X0)]
  have l26 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0 X0 sK1]
    conv => enter [1]; rw [← l25 sK1 X0]
  have l27 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l26 sK1 X0]
  have l28 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l27 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l29 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0 sK1]
    conv => enter [1]; rw [l28 sK1 X0]
  have l30 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [← l23 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
  have l31 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ sK2) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l30 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← l23 sK2 X0]
  have l32 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l23 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l31 sK2 sK3 sK0 X0]
  have l33 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l32 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l34 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l7 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
    conv => enter [1]; rw [← l17 sK1 (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) sK2 sK3 sK0]
  have l35 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l29 sK1 (sK1 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK1))]
    conv => enter [1]; rw [← l34 sK1 sK2 sK3 sK0 sK1]
  have l36 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l33 sK1 sK2 sK3 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  intro x y z w
  conv => enter [1]; rw [l36 x y z w]

theorem Equation4512_41563_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41563 : Equation41563 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h41563 X1 sK1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41563 X1 X0 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41563 X0 X0 X1 X1]
  have l3 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41563 (sK1 ◇ sK1) sK1 X0 X1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (X0 ◇ X1))]
  have l4 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l3 sK1 X0 X1]
    conv => enter [1, 2]; rw [l0 sK1 (X0 ◇ X1)]
  have l5 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK1 sK1 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation310_implies_Equation41569 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation41569 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [h310 X0 sK1]
  have l2 : ∀ X0 sK2 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l0 X0 sK2 X0]
    conv => enter [1, 2]; rw [l1 sK2 X0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h310 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_41569_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41569 : Equation41569 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41569 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h41569 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h41569 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h41569 (sK0 ◇ (sK1 ◇ sK1)) sK0 sK0]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41569 (sK1 ◇ sK1) sK1 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l6 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l4 sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l6 sK1]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41569 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l8 X0 sK1]
    conv => enter [1, 2]; rw [← l7 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation310_4512_implies_Equation41570 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation41570 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [h310 X0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h310 (sK1 ◇ sK2) sK0]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
  have l5 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h310 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_41570_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41570 : Equation41570 G) : Equation310 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41570 X2 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h41570 (X0 ◇ (X1 ◇ X0)) X1 X0]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X2 X1 : G, (X2 ◇ X2) = (X2 ◇ (X1 ◇ X1)) := by
    intro X2 X1
    conv => enter [1]; rw [l1 X2 X1 X2]
    conv => enter [1, 2]; rw [← h41570 X1 X2 (X1 ◇ X2)]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation310_4512_implies_Equation41573 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation41573 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1 sK0]
  have l3 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l2 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l4 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X2 X1 sK0
    conv => enter [1, 1]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l5 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [h310 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l5 X0 X1 sK0]
  have l8 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [l4 X0 X2 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l9 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l3 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l10 : ∀ X0 X2 X1 sK0 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l8 X0 X2 X1 sK0]
  have l11 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← l9 X0 sK0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [l7 X0 X1 sK0]
  have l13 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l0 X1 X0 X0]
    conv => enter [1, 2]; rw [l7 X0 X0 sK0]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l13 X1 X0 sK0]
    conv => enter [1]; rw [l11 X1 X0 sK0 X0]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l12 X0 sK0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l15 X0 X1 X0]
  have l17 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0))]
  have l18 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [← l16 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
  have l19 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ sK2) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l18 sK2 sK1 X0]
    conv => enter [1]; rw [← l16 sK2 X0]
  have l20 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l16 sK2 sK1]
    conv => enter [1]; rw [← l19 sK2 sK1 X0]
  have l21 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l20 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l17 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← l21 sK1 sK2 X0]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l21 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) X0]
  have l24 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l21 sK1 sK2 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l22 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l24 X0 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l26 x y z]

theorem Equation4512_41573_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41573 : Equation41573 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h41573 sK1 X0 X1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l2 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h41573 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41573 (sK1 ◇ sK1) sK1 sK1]
  have l4 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← h41573 (sK1 ◇ sK1) sK1 sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41573 X0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l3 sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l4 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l6 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1]
    conv => enter [1]; rw [← l7 sK1]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l11 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l11 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l13 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41573 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK1]
  have l14 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l13 X0 sK1]
    conv => enter [1, 2]; rw [← l12 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l14 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l15 X0 sK1]
    conv => enter [1, 2]; rw [← l5 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation310_implies_Equation41574 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation41574 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h310 X0 sK0]
    conv => enter [1]; rw [h310 X0 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← h310 sK2 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 X0]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_41574_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41574 : Equation41574 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41574 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h41574 X0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l0 sK1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation310_4512_implies_Equation41575 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation41575 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK1]
  have l2 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h310 X0 sK1]
    conv => enter [1]; rw [l1 X0 X1 sK1]
  have l3 : ∀ X0 sK1 X2 X1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2)) := by
    intro X0 sK1 X2 X1
    conv => enter [1, 1]; rw [l2 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK1 ◇ sK1)) X2]
  have l4 : ∀ X0 X2 X1 sK1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2)) := by
    intro X0 X2 X1 sK1
    conv => enter [1, 1]; rw [l1 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK1 ◇ sK1)) X2]
  have l5 : ∀ X0 X1 sK1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1, 1]; rw [h310 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l6 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l5 X0 X1 sK1]
  have l7 : ∀ X0 X2 X1 sK1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2))) := by
    intro X0 X2 X1 sK1
    conv => enter [1]; rw [l4 X0 X2 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK1 ◇ sK1) X2]
  have l8 : ∀ X0 sK1 X2 X1 : G, ((X0 ◇ (sK1 ◇ sK1)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2))) := by
    intro X0 sK1 X2 X1
    conv => enter [1]; rw [l3 X0 sK1 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK1 ◇ sK1) X2]
  have l9 : ∀ X0 X2 X1 sK1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2))) := by
    intro X0 X2 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l7 X0 X2 X1 sK1]
  have l10 : ∀ X0 X1 sK1 X2 : G, (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2))) = (X0 ◇ ((sK1 ◇ sK1) ◇ X2)) := by
    intro X0 X1 sK1 X2
    conv => enter [1]; rw [← l8 X0 sK1 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X2]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h310 sK1 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
  have l12 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X1) sK1]
    conv => enter [1, 2]; rw [l6 X0 X1 sK1]
  have l13 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l0 X1 X0 X0]
    conv => enter [1, 2]; rw [l6 X0 X0 sK1]
  have l14 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l13 X1 X0 sK1]
    conv => enter [1]; rw [l10 X1 X0 sK1 X0]
  have l15 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l9 X0 X1 X0 sK1]
    conv => enter [1]; rw [← l12 X0 sK1 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l15 X0 X1 X0]
  have l17 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ (sK3 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1, 1]; rw [← l16 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK3 sK3 X0]
  have l18 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ sK3) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l17 sK3 sK0 X0]
    conv => enter [1]; rw [← l16 sK3 X0]
  have l19 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l16 sK3 sK0]
    conv => enter [1]; rw [← l18 sK3 sK0 X0]
  have l20 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l19 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l21 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l20 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) X0]
  have l22 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l21 sK1 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l22 x y z w]

theorem Equation4512_41575_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41575 : Equation41575 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41575 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41575 X0 X1 X1 X1]
  have l2 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41575 (sK1 ◇ sK1) sK1 X0 X1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ X1))]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41575 sK1 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l2 sK1 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation310_implies_Equation41579 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation41579 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  have l1 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK1]
  have l2 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [← h310 X0 sK1]
    conv => enter [1]; rw [l0 X0 sK3 sK0]
  have l3 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l1 X0 sK2 X0]
    conv => enter [1, 2]; rw [l2 sK2 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_41579_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41579 : Equation41579 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41579 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41579 X0 X1 (X1 ◇ X1) X1]
  have l2 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41579 (sK1 ◇ sK1) sK1 X0 X1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X1 ◇ X1))]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41579 sK1 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l2 sK1 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation312_implies_Equation3268 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation3268 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [h312 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3268_4512_implies_Equation312 (G : Type*) [Magma G] (h3268 : Equation3268 G) (h4512 : Equation4512 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3268 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h3268 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← h3268 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [h3268 (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [← h3268 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation312_implies_Equation3288 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation3288 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [h312 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation3288_4512_implies_Equation312 (G : Type*) [Magma G] (h3288 : Equation3288 G) (h4512 : Equation4512 G) : Equation312 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3288 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h3288 (X0 ◇ X0) X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h3288 X0 X0 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3288 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h3288 (sK0 ◇ sK0) X0 X0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← l3 X0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3288 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation312_implies_Equation41581 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation41581 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h312 sK0 sK0]
    conv => enter [1, 2]; rw [h312 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_41581_implies_Equation312 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41581 : Equation41581 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41581 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41581 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1, 2]; rw [← h41581 X0 X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation312_implies_Equation41591 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation41591 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h312 sK0 sK0]
    conv => enter [1, 2]; rw [h312 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_41591_implies_Equation312 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41591 : Equation41591 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h41591 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41591 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l3 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ sK0) X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) sK0 X0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ X0)]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41591 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41591 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l14 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2]; rw [← l17 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK1]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← l13 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l21 sK1 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l23 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l24 x y]

@[equational_result]
theorem Equation312_implies_Equation41601 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation41601 G := by
  have l0 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h312 sK0 sK0]
    conv => enter [1, 2]; rw [h312 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

end Semigroup5
