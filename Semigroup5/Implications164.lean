import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41981_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41981 : Equation41981 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41981 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41981 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l0 sK0 X1]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) (sK0 ◇ X1) X0]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h41981 sK0 sK0 X1 X2]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X2))) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 X2]
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ (sK0 ◇ X2))]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X2))) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X2)]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l6 sK0 X2]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (sK0 ◇ X2)]
  have l8 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l7 sK0 X2]
    conv => enter [1]; rw [← l3 sK0 X2 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l8 sK0 X2]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) X2]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation41982 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41982 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l0 z y x]

theorem Equation4512_41982_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41982 : Equation41982 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h41982 X0 X1 X2]
    conv => enter [1]; rw [← h41982 (X2 ◇ X0) X2 X1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ X0))]
    conv => enter [1]; rw [← h41982 X0 sK0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41982 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l2 sK0 X0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X2 X0 X2]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [← h41982 X0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l7 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41982 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l13 sK0 X0 X1]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1, 2]; rw [l7 X1 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0 sK0]
    conv => enter [1]; rw [← l15 sK0 X0 sK0]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41982 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l16 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l18 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l17 X0 X1 sK0]
    conv => enter [1]; rw [← l13 sK0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [← l18 y z x]

@[equational_result]
theorem Equation41_implies_Equation41984 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41984 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK2)]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l2 z y]
  conv => enter [1]; rw [l0 z y]

theorem Equation4512_41984_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41984 : Equation41984 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41984 X0 X1 X0]
    conv => enter [1]; rw [← h41984 X2 X1 X0]
  have l1 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (sK2 ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l0 X0 (sK2 ◇ X1) sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X1) = (X1 ◇ (sK2 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h41984 X0 X1 sK2]
    conv => enter [1, 2, 2, 2]; rw [l0 sK2 sK2 sK1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l4 X0 X1 sK2 sK1]
    conv => enter [1]; rw [l1 X1 sK2 (X1 ◇ (sK1 ◇ sK2)) sK1]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 X1]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l8 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l6 sK1 sK2 (sK1 ◇ sK2)]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation41985 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41985 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z y w]

theorem Equation4512_41985_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41985 : Equation41985 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41985 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41985 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ (X1 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h41985 sK0 sK0 X1 X2]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l3 sK0 X1 X2]
    conv => enter [1]; rw [l2 sK0 X1 (sK0 ◇ (X1 ◇ X2))]
  have l5 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l4 sK0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ X2)]
  have l6 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l5 sK0 X1 X2]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (X1 ◇ X2)]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l8 sK1 sK2]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l9 sK1 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation41986 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41986 G := by
  have l0 : ∀ sK3 sK2 sK0 sK1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ sK1)]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z y w x]

theorem Equation4512_41986_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41986 : Equation41986 G) : Equation41 G := by
  have l0 : ∀ X2 X1 X3 X0 X4 X5 : G, ((X2 ◇ (X1 ◇ (X3 ◇ X0))) ◇ X4) = (X4 ◇ (X5 ◇ (X4 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X3 X0 X4 X5
    conv => enter [1]; rw [h41986 (X2 ◇ (X1 ◇ (X3 ◇ X0))) X4 X5 X1]
    conv => enter [1, 2, 2, 2]; rw [← h41986 X0 X1 X2 X3]
  have l1 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h41986 X2 X3 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [h41986 X4 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41986 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X0)))]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X4 ◇ X0)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l3 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 (X4 ◇ X0)]
  have l5 : ∀ X2 X3 X1 : G, (X2 ◇ X3) = ((X1 ◇ X2) ◇ X3) := by
    intro X2 X3 X1
    conv => enter [1]; rw [l1 X2 X3 X2 X2 X1]
    conv => enter [1]; rw [← h41986 (X1 ◇ X2) X3 X2 X2]
  have l6 : ∀ X2 X1 X3 X0 X4 : G, ((X2 ◇ (X1 ◇ (X3 ◇ X0))) ◇ X4) = (X1 ◇ X4) := by
    intro X2 X1 X3 X0 X4
    conv => enter [1]; rw [l0 X2 X1 X3 X0 X4 X2]
    conv => enter [1]; rw [← h41986 X1 X4 X2 X0]
  have l7 : ∀ X0 X1 X2 X4 : G, (X0 ◇ (X1 ◇ X2)) = ((X4 ◇ X0) ◇ X1) := by
    intro X0 X1 X2 X4
    conv => enter [1]; rw [l4 X0 X1 X2 X0 X4]
    conv => enter [1]; rw [← l2 (X4 ◇ X0) X1 X2 X0 X2]
  have l8 : ∀ X1 X4 X2 X3 X0 : G, (X1 ◇ X4) = (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) := by
    intro X1 X4 X2 X3 X0
    conv => enter [1]; rw [← l6 X2 X1 X3 X0 X4]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ (X3 ◇ X0)) X4]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X0]
    conv => enter [1]; rw [← l7 X0 X1 X2 X0]
  have l10 : ∀ X1 X4 X2 X3 X0 : G, (X1 ◇ X4) = (X2 ◇ (X1 ◇ ((X3 ◇ X0) ◇ X4))) := by
    intro X1 X4 X2 X3 X0
    conv => enter [1]; rw [l8 X1 X4 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X3 ◇ X0) X4]
  have l11 : ∀ X1 X4 X2 : G, (X1 ◇ X4) = (X2 ◇ X1) := by
    intro X1 X4 X2
    conv => enter [1]; rw [l10 X1 X4 X2 X1 X1]
    conv => enter [1]; rw [← l9 X2 X1 ((X1 ◇ X1) ◇ X4)]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation41988 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41988 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK2 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ sK3)]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z y w]

theorem Equation4512_41988_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41988 : Equation41988 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41988 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41988 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ (X2 ◇ X1)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h41988 sK0 sK0 X1 X2]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
  have l7 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ X1))) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l3 sK0 X1 X2]
    conv => enter [1]; rw [l2 sK0 X1 (sK0 ◇ (X2 ◇ X1))]
  have l8 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X2 ◇ X1))) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l7 sK0 X2 X1]
    conv => enter [1]; rw [l0 sK0 (X2 ◇ X1)]
  have l9 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ X1)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l8 sK0 X2 X1]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (X2 ◇ X1)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2 X0 sK1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41988 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l12 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 X1 (sK0 ◇ sK0)]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l13 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 X1]
  have l15 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l14 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [← l16 y z x]

@[equational_result]
theorem Equation41_implies_Equation41989 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41989 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK0 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK2]
  have l4 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK0 sK2 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]
  conv => enter [1]; rw [l0 z y w]

theorem Equation4512_41989_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41989 : Equation41989 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41989 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41989 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ (X2 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h41989 sK0 sK0 X1 X2]
  have l4 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ X2))) := by
    intro sK0 X2
    conv => enter [1]; rw [l3 sK0 sK0 X2]
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ (X2 ◇ X2))]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X2 ◇ X2))) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 X2]
    conv => enter [1]; rw [l0 sK0 (X2 ◇ X2)]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (X2 ◇ X2)]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation41990 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41990 G := by
  have l0 : ∀ sK4 sK3 sK1 sK0 : G, (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK4 sK4 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK1 ◇ sK0)]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]
  conv => enter [1]; rw [l0 z y w u]

theorem Equation4512_41990_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41990 : Equation41990 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41990 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41990 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41990 sK0 sK0 X1 X2 X3]
  have l4 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ X3))) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l3 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ (X2 ◇ X3))]
  have l5 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X2 ◇ X3))) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l4 sK0 X2 X3]
    conv => enter [1]; rw [l0 sK0 (X2 ◇ X3)]
  have l6 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ X3)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l5 sK0 X2 X3]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (X2 ◇ X3)]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l8 sK1 sK2]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l9 sK1 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation41991 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41991 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x y (z ◇ (z ◇ (x ◇ x)))]

theorem Equation4512_41991_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41991 : Equation41991 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41991 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41991 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41991 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ (X0 ◇ X0)))]
  have l4 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l0 sK0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41991 X0 sK0 X1]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41991 X0 sK0 X1]
  have l6 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41991 X0 sK2 X1]
  have l7 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [← l6 sK1 sK2 sK1 X0]
    conv => enter [1]; rw [← h41991 X0 (sK1 ◇ sK2) sK1]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41991 X0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l5 sK0 X0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 sK0 X0]
    conv => enter [1, 2]; rw [← h41991 X0 (sK0 ◇ sK0) sK0]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h41991 X0 X2 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1, 2, 2]; rw [l9 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h41991 (sK0 ◇ sK0) X0 sK0]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41991 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l13 sK0 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41991 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [l13 sK0 (X0 ◇ X0)]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l15 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l2 X0 sK0 sK0]
  have l17 : ∀ X1 sK0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l14 X1 sK0 X1]
    conv => enter [1]; rw [← h41991 X1 sK0 X1]
  have l18 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h41991 sK2 X0 sK1]
    conv => enter [1, 2, 2]; rw [l7 sK1 sK2 sK2]
  have l19 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l18 sK2 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l20 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l21 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l16 X1 X0 sK0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 X0 X1 sK0]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = (sK0 ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1, 2]; rw [← l17 X1 sK0]
    conv => enter [1]; rw [l22 X0 X1 sK0]
  have l24 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ (X1 ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l16 X1 X0 sK0]
    conv => enter [1]; rw [l23 X0 X1 sK0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l19 sK2 sK0 sK1]
  have l26 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l16 sK2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
  have l27 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l26 sK2 sK0 sK1]
    conv => enter [1]; rw [← l2 (sK1 ◇ sK2) sK0 sK0]
  have l28 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l17 sK2 sK0]
    conv => enter [1]; rw [l27 sK2 sK0 sK1]
  have l29 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l28 sK2 sK0 sK1]
  have l30 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ sK0) ◇ X0) = (sK2 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [← l28 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK2 sK0 X0]
  have l31 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ sK0) ◇ X0) = (sK0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l30 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l10 sK2 sK0 X0]
  have l32 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l29 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK2) sK0]
  have l33 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ X0) = (((sK1 ◇ sK2) ◇ sK0) ◇ X0) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [l24 sK2 X0 sK0]
    conv => enter [1]; rw [← l31 sK1 sK2 sK0 X0]
  have l34 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [← l16 sK1 (sK1 ◇ sK2) sK0]
  have l35 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [l33 sK2 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK0 X0]
  have l36 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l35 sK2 X0 sK1 sK0]
    conv => enter [1]; rw [l10 (sK1 ◇ sK2) sK0 X0]
  have l37 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l36 sK2 X0 sK2 sK1]
    conv => enter [1]; rw [← l24 (sK1 ◇ sK2) X0 sK2]
  have l38 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [h41991 X1 sK2 X0]
    conv => enter [1]; rw [l37 sK2 (X0 ◇ (X0 ◇ (X1 ◇ X1))) sK1]
  have l39 : ∀ X1 sK2 sK1 : G, (X1 ◇ sK2) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X1 sK2 sK1
    conv => enter [1]; rw [l38 X1 sK2 sK1 X1]
    conv => enter [1]; rw [← h41991 X1 (sK1 ◇ sK2) X1]
  have l40 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l39 sK1 sK2 sK1]
    conv => enter [1]; rw [← l34 sK1 sK2 sK0]
  have l41 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l19 sK2 sK0 sK1]
    conv => enter [1]; rw [← l24 (sK1 ◇ sK2) (sK1 ◇ sK2) sK0]
  have l42 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l28 sK2 sK0 sK1]
    conv => enter [1]; rw [l41 sK2 sK0 sK1]
  have l43 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l40 sK1 sK2 sK1]
    conv => enter [1]; rw [l42 sK1 sK2 sK1]
  have l44 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41991 sK0 sK0 X0]
    conv => enter [1]; rw [← l24 X0 (X0 ◇ (sK0 ◇ sK0)) sK0]
  have l45 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l44 sK0 X0]
    conv => enter [1, 2]; rw [l17 X0 sK0]
  have l46 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l16 X0 X0 sK0]
    conv => enter [1]; rw [← l45 sK0 X0]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l43 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l47 x y z]

@[equational_result]
theorem Equation41_implies_Equation41994 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41994 G := by
  have l0 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK3 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z x w y]

theorem Equation4512_41994_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41994 : Equation41994 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41994 X1 X2 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41994 X0 X1 X1 X1]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ (X0 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41994 X0 X1 X2 X3]
  have l2 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (X1 ◇ (X0 ◇ X2)))]
    conv => enter [1, 2]; rw [← h41994 X0 sK0 X1 X2]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41994 X0 (sK0 ◇ sK0) X0 X0]
    conv => enter [1]; rw [l2 sK0 X0 X0 X0]
  have l4 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l1 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 X0]
    conv => enter [1]; rw [← l3 X0 sK0]
  have l6 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = (X4 ◇ X0) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l4 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← l0 X4 X0 X1]
  have l7 : ∀ X4 X0 X1 : G, (X4 ◇ X0) = (X4 ◇ X1) := by
    intro X4 X0 X1
    conv => enter [1]; rw [l0 X4 X0 (X4 ◇ (X4 ◇ (X1 ◇ X4)))]
    conv => enter [1]; rw [l6 X0 X4 X1 X4 X4]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation41995 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41995 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l0 z y x]

theorem Equation4512_41995_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41995 : Equation41995 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h41995 X0 sK0 sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41995 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41995 X1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (((sK0 ◇ sK0) ◇ X0) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [← l3 ((sK0 ◇ sK0) ◇ X0) sK0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l1 sK0 X0]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 sK0]
  have l7 : ∀ X1 sK0 X0 : G, ((X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l5 sK0 (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))]
    conv => enter [1, 2]; rw [← h41995 X0 (sK0 ◇ sK0) X1]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h41995 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l9 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41995 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l5 sK0 (X0 ◇ X1)]
  have l10 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l9 X1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l8 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((X1 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l7 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) sK0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ X0) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l11 X0 sK0]
    conv => enter [1]; rw [← l6 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 sK0]
  have l16 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 ((sK0 ◇ sK0) ◇ X0) X1 sK0]
    conv => enter [1]; rw [← l14 sK0 X0 X1]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l15 X0 sK0]
    conv => enter [1]; rw [← l6 X0 sK0]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l16 sK0 X0 X1]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l18 sK0 X0 X1]
    conv => enter [1, 2]; rw [l17 X0 sK0]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1]
    conv => enter [1]; rw [← l6 X0 sK0]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41995 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l17 X0 sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41995 sK0 X0 sK0]
    conv => enter [1]; rw [← l21 sK0 X0 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l22 sK0 X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l20 sK0 sK0 X0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41995 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK0 X0]
  have l26 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l24 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0 sK0]
  have l28 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l25 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [l17 X1 sK0]
  have l29 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l28 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l24 sK0 X1]
  have l30 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 X1]
    conv => enter [1, 2]; rw [l17 X1 sK0]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0 sK0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← l31 sK0 X0]
  have l33 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41995 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l32 sK0 (sK0 ◇ (X1 ◇ X0))]
  have l34 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l33 X0 X1 sK0]
    conv => enter [1]; rw [← l27 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l34 y z x]

@[equational_result]
theorem Equation41_implies_Equation41997 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41997 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l0 z y]

theorem Equation4512_41997_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41997 : Equation41997 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41997 X0 X1 X0]
    conv => enter [1]; rw [← h41997 X2 X1 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X1) X0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41997 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 sK0 sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation41998 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41998 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK3 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK3 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z y w]

theorem Equation4512_41998_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41998 : Equation41998 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41998 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41998 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 (sK0 ◇ X1) sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h41998 sK0 sK0 X1 X2]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l3 sK0 X1 X2]
    conv => enter [1]; rw [l1 sK0 X1 (X1 ◇ (sK0 ◇ X2))]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 X2]
    conv => enter [1, 2]; rw [l2 sK0 sK0 X2]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42001 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42001 G := by
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [h41 z y (z ◇ (z ◇ (z ◇ z)))]

theorem Equation4512_42001_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42001 : Equation42001 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42001 X0 X1 X0]
    conv => enter [1]; rw [← h42001 X2 X1 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X1) X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42001 X0 X1 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42002 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42002 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_42002_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42002 : Equation42002 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42002 X2 X3 X1 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42002 X0 X1 X1 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42002 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42002 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l11 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l10 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42003 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42003 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK1]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK1)]
  have l3 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [← l1 sK1 sK3 sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK3 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l3 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w x y]

theorem Equation4512_42003_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42003 : Equation42003 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42003 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ (X3 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h42003 X0 X1 X2 X3]
  have l2 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [l1 X1 X2 X3 X0 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0]
    conv => enter [1]; rw [← h42003 (sK0 ◇ sK0) X0 sK0 sK0]
  have l4 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l2 X1 X2 X3 X0 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ (X3 ◇ X0)) X4]
  have l5 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l4 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X3 ◇ X0) X4]
  have l6 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ X4)) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l5 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [← h42003 X4 X1 X0 (X0 ◇ X0)]
  have l7 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h42003 X1 X2 sK0 X0]
    conv => enter [1, 2, 2]; rw [l3 sK0 (X0 ◇ X1)]
  have l8 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (((sK0 ◇ sK0) ◇ (X0 ◇ X1)) ◇ sK0) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l7 X1 X2 sK0 X0]
    conv => enter [1]; rw [l6 X2 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1))]
  have l9 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ sK0)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l8 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X1) sK0]
  have l10 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l9 X1 X2 sK0 X0]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) (X0 ◇ X1) sK0]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X1 ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l10 X1 X2 X1 X0]
    conv => enter [1]; rw [l6 X1 X0 X1]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ X0)))]
    conv => enter [1]; rw [← h42003 X0 sK0 sK0 sK0]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42005 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42005 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l1 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ sK3) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK3]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK3)]
  have l3 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1, 2]; rw [l1 sK0 sK3 sK3 sK3]
    conv => enter [1, 2]; rw [l2 sK3 sK3 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l3 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_42005_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42005 : Equation42005 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42005 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42005 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X1) X0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42005 X0 X1 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [l1 X0 sK0 sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation42006 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42006 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK3 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK3
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK3]
  have l4 : ∀ sK0 sK3 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 sK0 sK3 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_42006_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42006 : Equation42006 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42006 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42006 X2 X1 X0 X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ X1)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h42006 sK0 sK0 X1 X2]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l3 sK0 X1 X2]
    conv => enter [1]; rw [l2 sK0 X1 (X1 ◇ (X2 ◇ X2))]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l5 sK1 sK2]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42006 X0 X1 (sK0 ◇ sK0) (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 (X0 ◇ X0) X0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 sK0 X1]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X1) (sK0 ◇ sK0) sK0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← l8 sK0 X1 (sK0 ◇ sK0)]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42007 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42007 G := by
  have l0 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ sK0) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 sK0]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ sK0)]
  have l3 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK4 sK4]
    conv => enter [1, 2]; rw [l2 sK4 sK4 sK4 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l3 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l0 z w u y]

theorem Equation4512_42007_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42007 : Equation42007 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42007 X2 X3 X1 X1 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h42007 X0 X1 X1 X2 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42007 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42007 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l11 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l10 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42008 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42008 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h41 sK1 sK3 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [l0 z w x y]

theorem Equation4512_42008_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42008 : Equation42008 G) : Equation41 G := by
  have l0 : ∀ X2 X0 X3 X4 X1 : G, ((X2 ◇ (X0 ◇ X0)) ◇ X3) = (X3 ◇ (X4 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X3 X4 X1
    conv => enter [1]; rw [h42008 (X2 ◇ (X0 ◇ X0)) X3 X4 X1]
    conv => enter [1, 2, 2]; rw [← h42008 X0 X1 (X2 ◇ (X0 ◇ X0)) X2]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ X4) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [h42008 X3 X4 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l2 : ∀ X3 X4 X0 : G, (X3 ◇ X4) = (X4 ◇ (X3 ◇ X0)) := by
    intro X3 X4 X0
    conv => enter [1]; rw [l1 X3 X4 X0 X3 X3]
    conv => enter [1, 2]; rw [← h42008 X3 X0 X3 X3]
  have l3 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ X1))) = (X2 ◇ ((X0 ◇ X0) ◇ X3)) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l0 X2 X0 X3 X4 X1]
    conv => enter [1]; rw [← h4512 X2 (X0 ◇ X0) X3]
  have l4 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ X2) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [l3 X3 X4 X0 X1 X2]
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X2 X3]
  have l5 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X2)) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [l4 X3 X4 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l6 : ∀ X0 X3 X4 X1 : G, (X0 ◇ X0) = (X3 ◇ (X4 ◇ (X0 ◇ X1))) := by
    intro X0 X3 X4 X1
    conv => enter [1]; rw [l2 X0 X0 X0]
    conv => enter [1]; rw [← l5 X3 X4 X0 X1 X0]
  have l7 : ∀ X0 X4 X3 : G, (X0 ◇ X0) = (X4 ◇ X3) := by
    intro X0 X4 X3
    conv => enter [1]; rw [l6 X0 X3 X4 X0]
    conv => enter [1]; rw [← l2 X4 X3 (X0 ◇ X0)]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l7 sK1 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42010 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42010 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK1 ◇ sK3))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l1 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w x y]

theorem Equation4512_42010_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42010 : Equation42010 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 X2 X4 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X3 X2 X4
    conv => enter [1]; rw [h42010 (X0 ◇ X1) X3 X2 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X2 X4 X3 X0 X1 : G, (X2 ◇ X4) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X2 X4 X3 X0 X1
    conv => enter [1]; rw [h42010 X2 X4 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = ((X0 ◇ X1) ◇ X3) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l1 X1 X3 X1 X1 X0]
    conv => enter [1]; rw [← l0 X0 X1 X3 X1 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 X0 X1]
  have l4 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ X2) = (X2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ sK2)))) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [h42010 X1 X2 sK2 X0]
    conv => enter [1, 2]; rw [l2 sK2 (X0 ◇ (X1 ◇ sK2)) sK1]
  have l5 : ∀ sK1 sK2 X0 X1 X2 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = (X2 ◇ sK2) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [← l2 sK2 (X0 ◇ (X1 ◇ (X2 ◇ X0))) sK1]
    conv => enter [1]; rw [← h42010 X2 sK2 X0 X1]
  have l6 : ∀ X2 sK2 sK1 : G, (X2 ◇ sK2) = (X2 ◇ (sK1 ◇ sK2)) := by
    intro X2 sK2 sK1
    conv => enter [1]; rw [← l5 sK1 sK2 X2 X2 X2]
    conv => enter [1]; rw [← h42010 X2 (sK1 ◇ sK2) X2 X2]
  have l7 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ X2) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [l4 X1 X2 sK1 sK2 X0]
    conv => enter [1]; rw [← l3 (sK1 ◇ sK2) (X0 ◇ (X1 ◇ sK2)) X2]
  have l8 : ∀ X1 X2 X0 sK2 : G, (X1 ◇ X2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro X1 X2 X0 sK2
    conv => enter [1]; rw [l7 X1 X2 X1 sK2 X0]
    conv => enter [1]; rw [← l3 X0 (X1 ◇ sK2) (X1 ◇ sK2)]
  have l9 : ∀ X1 X2 sK2 : G, (X1 ◇ X2) = (X1 ◇ sK2) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l8 X1 X2 X1 sK2]
    conv => enter [1]; rw [← l3 X1 sK2 X1]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2 (sK2 ◇ X0)]
    conv => enter [1]; rw [h4512 sK1 sK2 X0]
  have l11 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l10 sK1 sK2 X0]
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [← l11 sK1 sK2 X0]
  have l13 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l2 X0 X1 sK1]
    conv => enter [1, 1]; rw [l9 sK1 X0 sK2]
  have l14 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l13 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l12 sK1 sK2 X1]
  intro x y z
  conv => enter [1]; rw [l14 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42011 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42011 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w x y]

theorem Equation4512_42011_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42011 : Equation42011 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42011 X2 X3 X1 (X0 ◇ X2)]
    conv => enter [1, 2]; rw [← h42011 X0 X1 (X0 ◇ X2) X2]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42011 X0 (sK0 ◇ sK0) sK0 X1]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h42011 X0 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l2 X0 sK0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42011 X0 X1 X0 X0]
    conv => enter [1]; rw [← l1 X2 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [← l1 (X1 ◇ X2) X0 sK0 sK0]
    conv => enter [1]; rw [← h4512 X1 X2 X0]
  have l6 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ sK0) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [l5 X0 sK0 X1 X2]
  have l7 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ sK2) = (sK2 ◇ (X1 ◇ X2)) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 sK1 sK2 X1 X2]
  have l8 : ∀ sK1 sK2 X2 sK0 : G, (sK1 ◇ sK2) = (X2 ◇ sK0) := by
    intro sK1 sK2 X2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1 X2]
    conv => enter [1]; rw [← l6 X2 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42012 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42012 G := by
  have l0 : ∀ sK4 sK1 sK2 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l0 z w x u y]

theorem Equation4512_42012_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42012 : Equation42012 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42012 X2 X3 X1 X2 (X0 ◇ X2)]
    conv => enter [1, 2]; rw [← h42012 X0 X1 X2 X2 X2]
  have l1 : ∀ X3 X5 X0 X1 X2 X4 : G, (X3 ◇ X5) = (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X3 X5 X0 X1 X2 X4
    conv => enter [1]; rw [h42012 X3 X5 (X0 ◇ X1) X2 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l2 : ∀ X3 X5 X2 : G, (X3 ◇ X5) = (X2 ◇ X5) := by
    intro X3 X5 X2
    conv => enter [1]; rw [l1 X3 X5 X3 X3 X2 X3]
    conv => enter [1]; rw [← h42012 X2 X5 X3 X3 (X3 ◇ X3)]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l2 sK2 sK2 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l9 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X1]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l11 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation42013 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42013 G := by
  have l0 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w y x]

theorem Equation4512_42013_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42013 : Equation42013 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42013 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42013 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h42013 sK0 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42013 (sK0 ◇ sK0) X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 X0]
  have l4 : ∀ X0 sK0 X1 X2 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h42013 (X0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42013 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l8 sK0 (X0 ◇ (X1 ◇ X0))]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
    conv => enter [1]; rw [← h42013 X0 (sK0 ◇ sK0) sK0 sK0]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l10 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42015 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42015 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l1 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_42015_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42015 : Equation42015 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42015 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42015 X2 X1 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h42015 X0 X1 sK0 X2]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l2 X0 X1 sK0 X2]
    conv => enter [1]; rw [← l1 sK0 (X2 ◇ (sK0 ◇ sK0)) X1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42016 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42016 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_42016_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42016 : Equation42016 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42016 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42016 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h42016 sK0 sK0 X1 X2]
  have l4 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ X2))) := by
    intro sK0 X2
    conv => enter [1]; rw [l3 sK0 sK0 X2]
    conv => enter [1]; rw [l1 sK0 sK0 (X2 ◇ (sK0 ◇ X2))]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 X2]
    conv => enter [1, 2]; rw [← l2 sK0 X2 X2]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42017 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42017 G := by
  have l0 : ∀ sK4 sK1 sK3 sK0 : G, (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK4 sK1 sK3 sK0
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l0 z w y u]

theorem Equation4512_42017_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42017 : Equation42017 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42017 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42017 X2 X1 X0 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 (sK0 ◇ X1) sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h42017 sK0 sK0 X1 X2 X3]
  have l4 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ X3))) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l3 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l1 sK0 sK0 (X2 ◇ (sK0 ◇ X3))]
  have l5 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X3)) := by
    intro sK0 X3
    conv => enter [1]; rw [l4 sK0 sK0 X3]
    conv => enter [1, 2]; rw [l2 sK0 sK0 X3]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42018 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42018 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK3 ◇ sK1))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK1]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l1 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w x y]

theorem Equation4512_42018_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42018 : Equation42018 G) : Equation41 G := by
  have l0 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ X4) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h42018 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ X4) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [h42018 X3 X4 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
  have l2 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X2 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h42018 X0 X1 X2 X3]
  have l3 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [l2 X1 X2 X3 X0 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l4 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ X4) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [l1 X3 X4 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l3 X1 X2 X3 X0 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X3 ◇ (X2 ◇ X0)) X4]
  have l6 : ∀ X3 X4 X1 : G, (X3 ◇ X4) = ((X1 ◇ X3) ◇ X4) := by
    intro X3 X4 X1
    conv => enter [1]; rw [l4 X3 X4 X3 X1 X3]
    conv => enter [1]; rw [← l0 (X1 ◇ X3) X4 X3 X1 X3]
  have l7 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X3 (X2 ◇ X0) X4]
  have l8 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X0 X4]
  have l9 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ X4)) = ((X0 ◇ X4) ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l8 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [← h42018 (X0 ◇ X4) X1 X0 X0]
  have l10 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ X4)) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l9 X0 X1 X4]
    conv => enter [1]; rw [← l6 X4 X1 X0]
  have l11 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ X2) = (X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h42018 X1 X2 X0 X4]
    conv => enter [1, 2]; rw [l6 X0 (X4 ◇ (X0 ◇ X1)) X3]
  have l12 : ∀ X1 X2 X4 X0 X3 : G, (X1 ◇ X2) = ((X4 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) := by
    intro X1 X2 X4 X0 X3
    conv => enter [1]; rw [l11 X1 X2 X3 X0 X4]
    conv => enter [1]; rw [l10 X2 (X3 ◇ X0) (X4 ◇ (X0 ◇ X1))]
  have l13 : ∀ X1 X2 X4 X0 X3 : G, (X1 ◇ X2) = (X4 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X0))) := by
    intro X1 X2 X4 X0 X3
    conv => enter [1]; rw [l12 X1 X2 X4 X0 X3]
    conv => enter [1]; rw [← h4512 X4 (X0 ◇ X1) (X3 ◇ X0)]
  have l14 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = ((X3 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l13 X1 X2 X1 X0 X3]
    conv => enter [1]; rw [l10 X1 (X0 ◇ X1) (X3 ◇ X0)]
  have l15 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l14 X1 X2 X3 X0]
    conv => enter [1]; rw [← h4512 X3 X0 (X0 ◇ X1)]
  have l16 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l15 X1 X2 X1 X0]
    conv => enter [1]; rw [l10 X1 X0 (X0 ◇ X1)]
  have l17 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l16 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X0 X1 X0]
  have l18 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ X1) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l17 X1 X2 X0]
    conv => enter [1]; rw [l10 X0 X1 X0]
  have l19 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK0]
    conv => enter [1]; rw [l18 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l19 y z x]

@[equational_result]
theorem Equation41_implies_Equation42020 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42020 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3)))]
  have l1 : ∀ sK3 sK0 : G, (sK3 ◇ sK3) = (sK0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [h41 sK3 sK0 (sK3 ◇ sK3)]
  have l2 : ∀ sK3 sK0 : G, (sK3 ◇ sK3) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h41 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l2 z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_42020_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42020 : Equation42020 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42020 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42020 X2 X1 X0 X0]
  have l1 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (sK2 ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l0 X0 (sK2 ◇ X1) sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ X0 X1 sK2 X2 sK1 : G, (X0 ◇ X1) = (X1 ◇ (sK2 ◇ (X2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK2 X2 sK1
    conv => enter [1]; rw [h42020 X0 X1 sK2 X2]
    conv => enter [1, 2, 2, 2]; rw [l0 sK2 sK2 sK1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ X0 X1 sK1 sK2 X2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (X2 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2 X2
    conv => enter [1]; rw [l4 X0 X1 sK2 X2 sK1]
    conv => enter [1]; rw [l1 X1 sK2 (X2 ◇ (sK1 ◇ sK2)) sK1]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 X0]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l8 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l6 sK1 sK2 (sK1 ◇ sK2)]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42021 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42021 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l1 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_42021_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42021 : Equation42021 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42021 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42021 X2 X1 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42021 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation42022 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42022 G := by
  have l0 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ (sK4 ◇ sK0))) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK4 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ (sK4 ◇ sK0))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK1 ◇ (sK4 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ sK0) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK4 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l0 z w u y]

theorem Equation4512_42022_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42022 : Equation42022 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42022 X2 X3 X1 X2 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h42022 X0 X1 X2 X1 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42022 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42022 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l11 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l10 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42023 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42023 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w x y]

theorem Equation4512_42023_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42023 : Equation42023 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42023 X2 X3 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ X4) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [h42023 X3 X4 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
  have l2 : ∀ X3 X4 X0 : G, (X3 ◇ X4) = (X4 ◇ (X3 ◇ X0)) := by
    intro X3 X4 X0
    conv => enter [1]; rw [l1 X3 X4 X0 X3 X3]
    conv => enter [1, 2]; rw [← h42023 X3 X0 X3 X3]
  have l3 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [l0 X2 X3 X4 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X2 X3 X4 : G, (X2 ◇ X3) = (X4 ◇ X3) := by
    intro X2 X3 X4
    conv => enter [1]; rw [l3 X2 X3 X4 X2 X2]
    conv => enter [1]; rw [← l2 X4 X3 (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l6 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation41_implies_Equation42025 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42025 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK3))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK3)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ (sK0 ◇ sK3))]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_42025_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42025 : Equation42025 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42025 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42025 X2 X1 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h42025 X0 X1 sK0 X2]
    conv => enter [1, 2, 2, 2]; rw [l0 X2 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l2 X0 X1 sK0 X2]
    conv => enter [1]; rw [← l1 sK0 (X2 ◇ (sK0 ◇ sK0)) X1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42026 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42026 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l3 : ∀ sK0 sK3 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_42026_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42026 : Equation42026 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42026 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42026 X2 X1 X0 X0]
  have l1 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (sK2 ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l0 X0 (sK2 ◇ X1) sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ X0 X1 X2 sK2 sK1 : G, (X0 ◇ X1) = (X1 ◇ (X2 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK2 sK1
    conv => enter [1]; rw [h42026 X0 X1 X2 sK2]
    conv => enter [1, 2, 2, 2]; rw [l0 sK2 sK2 sK1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l4 X0 X1 X0 sK2 sK1]
    conv => enter [1, 2]; rw [l1 X0 sK2 (sK1 ◇ sK2) sK1]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 (sK1 ◇ sK2)]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l8 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l6 sK1 sK2 X1]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42027 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42027 G := by
  have l0 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]
  conv => enter [1]; rw [l0 z w u y]

theorem Equation4512_42027_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42027 : Equation42027 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42027 X2 X3 X1 X2 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h42027 X0 X1 X2 X2 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42027 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42027 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l11 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l10 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42028 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42028 G := by
  have l0 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ sK2))]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]
  conv => enter [1]; rw [l0 z w u x y]

theorem Equation4512_42028_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42028 : Equation42028 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X4 X5 X0 X1 X2 X3 : G, (X4 ◇ X5) = (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X4 X5 X0 X1 X2 X3
    conv => enter [1]; rw [h42028 X4 X5 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l2 : ∀ X1 X2 X3 X4 X0 X5 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5)) = ((X0 ◇ X1) ◇ X5) := by
    intro X1 X2 X3 X4 X0 X5
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X0))) X5]
    conv => enter [1, 1]; rw [← h42028 X0 X1 X2 X3 X4]
  have l3 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h42028 X0 (sK0 ◇ sK0) sK0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ (X2 ◇ X0))]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h42028 X0 sK0 (sK0 ◇ sK0) X0 X0]
    conv => enter [1]; rw [← l3 X0 sK0 X0 X0]
  have l5 : ∀ X1 X2 X3 X4 X0 X5 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5)) = (X0 ◇ (X1 ◇ X5)) := by
    intro X1 X2 X3 X4 X0 X5
    conv => enter [1]; rw [l2 X1 X2 X3 X4 X0 X5]
    conv => enter [1]; rw [← h4512 X0 X1 X5]
  have l6 : ∀ X4 X5 X3 : G, (X4 ◇ X5) = ((X3 ◇ X4) ◇ X5) := by
    intro X4 X5 X3
    conv => enter [1]; rw [l1 X4 X5 X4 X4 X4 X3]
    conv => enter [1]; rw [← h42028 (X3 ◇ X4) X5 X4 X4 X4]
  have l7 : ∀ X0 X1 X5 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X5)) = (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X5))) := by
    intro X0 X1 X5 X2 X3 X4
    conv => enter [1]; rw [← l5 X1 X2 X3 X4 X0 X5]
    conv => enter [1, 2]; rw [← h4512 X2 (X3 ◇ (X4 ◇ X0)) X5]
  have l8 : ∀ X0 X1 X5 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X5)) = (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X0) ◇ X5)))) := by
    intro X0 X1 X5 X2 X3 X4
    conv => enter [1]; rw [l7 X0 X1 X5 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X3 (X4 ◇ X0) X5]
  have l9 : ∀ X0 X1 X5 : G, (X0 ◇ (X1 ◇ X5)) = (X5 ◇ X1) := by
    intro X0 X1 X5
    conv => enter [1]; rw [l8 X0 X1 X5 X0 X0 X0]
    conv => enter [1]; rw [← h42028 X5 X1 X0 X0 (X0 ◇ X0)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = ((sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 (sK0 ◇ X0) X1 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [l0 sK0 X0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1]; rw [l9 X1 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← l4 X0 sK0]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l16 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ X0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l15 sK0 X0 X1]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l16 X1 sK0 X0]
    conv => enter [1]; rw [← l16 sK0 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l17 y z x]

@[equational_result]
theorem Equation41_implies_Equation42030 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42030 G := by
  have l0 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4)))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ (sK0 ◇ sK4))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4)))]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ sK4))]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]
  conv => enter [1]; rw [l0 z w u y]

theorem Equation4512_42030_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42030 : Equation42030 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42030 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42030 X2 X1 X0 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h42030 sK0 sK0 X1 X2 X3]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ sK0 X2 X3 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X3 ◇ X1))) := by
    intro sK0 X2 X3 X1
    conv => enter [1]; rw [l2 sK0 X1 X2 X3]
    conv => enter [1]; rw [l1 sK0 X1 (X2 ◇ (X3 ◇ X1))]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42030 X0 X1 (sK0 ◇ sK0) X0 X0]
    conv => enter [1, 2]; rw [← l5 sK0 X0 X0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42031 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42031 G := by
  have l0 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ sK1))]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]
  conv => enter [1]; rw [l0 z w u y]

theorem Equation4512_42031_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42031 : Equation42031 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42031 X2 X3 X1 (X2 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h42031 X0 X1 (X2 ◇ X2) X2 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42031 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42031 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l11 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l10 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42032 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42032 G := by
  have l0 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ sK0)]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK0]
  have l3 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ sK0) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [h41 sK0 sK4 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK0]
    conv => enter [1]; rw [l3 sK0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l0 z w u y]

theorem Equation4512_42032_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42032 : Equation42032 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42032 X2 X3 X1 X2 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h42032 X0 X1 X2 (X2 ◇ X2) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42032 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42032 X2 X1 X0 X0 X0]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0 sK1]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 sK0 X1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l3 sK1 sK2 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation41_implies_Equation42033 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42033 G := by
  have l0 : ∀ sK5 sK2 sK0 sK1 sK4 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 sK4
    conv => enter [1]; rw [← h41 sK5 sK5 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h41 sK5 sK4 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z w u v
  conv => enter [1]; rw [l1 x y z w u v]
  conv => enter [1]; rw [l0 z w u v y]

theorem Equation4512_42033_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42033 : Equation42033 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42033 X2 X3 X1 X2 X2 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h42033 X0 X1 X2 X2 X2 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42033 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42033 X2 X1 X0 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l11 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l10 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42034 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42034 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0]
  have l5 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_42034_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42034 : Equation42034 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h42034 sK0 (sK0 ◇ X1) X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l1 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42034 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l2 sK0 X1 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK0]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X1 X0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l5 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 X1 sK0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42034 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42036 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42036 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation42036_implies_Equation41 (G : Type*) [Magma G] (h42036 : Equation42036 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42036 X0 X1 X0]
    conv => enter [1]; rw [← h42036 X0 X2 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42036 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42037 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42037 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK1 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation42037_implies_Equation41 (G : Type*) [Magma G] (h42037 : Equation42037 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42037 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42037 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42037 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42038 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42038 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42038_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42038 : Equation42038 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42038 (X0 ◇ (X1 ◇ X0)) X0 X2]
    conv => enter [1, 2, 2]; rw [← h42038 X0 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h42038 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 sK1]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42038 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42038 X0 X1 X0]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ X1)]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [← l3 (sK1 ◇ sK2) sK1 sK1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0]
    conv => enter [1, 2]; rw [← l3 (X1 ◇ X0) (X0 ◇ X1) X0]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [← l3 (sK1 ◇ sK2) sK1 sK1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l3 (X1 ◇ X0) (X0 ◇ X1) X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ X1)]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← l3 X0 (X0 ◇ X1) X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← l3 (X1 ◇ X0) X0 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1]; rw [← l3 X0 X0 X1]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [l15 (sK1 ◇ sK2) sK1]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42038 X0 X1 sK0]
    conv => enter [1]; rw [l15 sK0 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l18 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [← l15 (sK1 ◇ sK2) X0]
  have l19 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK1]
    conv => enter [1]; rw [l17 (sK1 ◇ sK2) sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l19 y z x]

@[equational_result]
theorem Equation41_implies_Equation42040 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42040 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42040_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42040 : Equation42040 G) : Equation41 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42040 X2 X0 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h42040 X0 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h42040 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h42040 X0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ X1)]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X2) (X2 ◇ (X0 ◇ X1))]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X2 ◇ (X0 ◇ X1))]
  have l5 : ∀ X2 X0 : G, (X2 ◇ X0) = (X0 ◇ (X2 ◇ X0)) := by
    intro X2 X0
    conv => enter [1]; rw [l4 X2 X0 X2]
    conv => enter [1, 2]; rw [← h42040 X2 X0 X2]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [← l5 sK2 sK1]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42040 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 sK0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 X0 sK0]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l5 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l5 sK1 sK2]
  have l10 : ∀ X0 sK2 sK1 : G, (X0 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h42040 X0 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK1 sK2]
  have l11 : ∀ X0 sK2 : G, (X0 ◇ X0) = (X0 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l2 X0 (X0 ◇ sK2)]
    conv => enter [1]; rw [← l10 X0 sK2 X0]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [l8 (sK1 ◇ sK2) sK0]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK0]
    conv => enter [1]; rw [l5 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [← l12 sK1 sK2 sK0]
  have l14 : ∀ X0 sK2 sK1 : G, (X0 ◇ sK2) = (sK1 ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h42040 X0 sK2 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK1 sK2]
  have l15 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ sK2) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h42040 X0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l14 X0 sK2 sK1]
  have l16 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l11 X0 sK2]
    conv => enter [1]; rw [← l15 X0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l13 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

@[equational_result]
theorem Equation41_implies_Equation42041 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42041 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42041_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42041 : Equation42041 G) : Equation41 G := by
  have l0 : ∀ X1 sK1 X2 sK2 X0 : G, (X1 ◇ sK1) = (X2 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro X1 sK1 X2 sK2 X0
    conv => enter [1]; rw [h42041 X1 sK1 X2 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42041 X2 X0 X3 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h42041 X0 X1 X2 X2]
  have l2 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h42041 sK1 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h42041 X0 X0 X2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h42041 X0 X1 X0 X0]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l3 sK1 sK1 ((sK1 ◇ sK2) ◇ sK1)]
  have l5 : ∀ X1 sK1 sK2 : G, (X1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [l0 X1 sK1 X1 sK2 X1]
    conv => enter [1]; rw [← h42041 X1 (sK1 ◇ sK2) X1 X1]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 X0 X0 (sK1 ◇ X0)]
    conv => enter [1]; rw [← h42041 X0 sK1 X0 X0]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK1 sK2]
  have l8 : ∀ X0 X1 sK1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ (sK1 ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1, 1]; rw [l6 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 sK1 X1]
  have l9 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l3 sK1 X0 X1]
    conv => enter [1]; rw [← l8 X0 X1 sK1]
  have l10 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l9 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 X0 X0]
    conv => enter [1]; rw [← l10 sK1 X0 X0]
  have l12 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l11 X0 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 sK2]
  have l13 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ sK2) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l12 X0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

@[equational_result]
theorem Equation41_implies_Equation42042 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42042 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation42042_implies_Equation41 (G : Type*) [Magma G] (h42042 : Equation42042 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42042 X0 X1 X0]
    conv => enter [1]; rw [← h42042 X0 X2 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42042 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42044 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42044 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41 sK2 sK0 (sK0 ◇ (sK2 ◇ sK2))]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z x]

@[equational_result]
theorem Equation42044_implies_Equation41 (G : Type*) [Magma G] (h42044 : Equation42044 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42044 X0 X1 X0]
    conv => enter [1]; rw [← h42044 X0 X2 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42044 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42045 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42045 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42045_implies_Equation41 (G : Type*) [Magma G] (h42045 : Equation42045 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42045 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42045 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42045 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42046 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42046 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK1]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l0 sK1 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK1 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation42046_implies_Equation41 (G : Type*) [Magma G] (h42046 : Equation42046 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42046 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42046 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42046 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42048 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42048 G := by
  have l0 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ sK3) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK3]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ sK3)]
  have l3 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK1 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK1 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l3 sK1 sK0 sK3]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation42048_implies_Equation41 (G : Type*) [Magma G] (h42048 : Equation42048 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42048 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42048 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42048 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42049 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42049 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [h41 sK0 sK3 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK0]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

@[equational_result]
theorem Equation42049_implies_Equation41 (G : Type*) [Magma G] (h42049 : Equation42049 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42049 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42049 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42049 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42050 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42050 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ sK0) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 sK0]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK1 ◇ sK0)]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK2 sK2]
    conv => enter [1, 2]; rw [l2 sK2 sK2 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l3 sK2 sK1 sK0]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

@[equational_result]
theorem Equation42050_implies_Equation41 (G : Type*) [Magma G] (h42050 : Equation42050 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42050 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42050 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42050 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42051 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42051 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41 sK0 sK2 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l1 x z y]

theorem Equation4512_42051_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42051 : Equation42051 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42051 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h42051 X0 X1 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42051 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h4512 X2 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X3]
    conv => enter [1, 1]; rw [← h42051 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42051 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42051 X0 X1 X0]
  have l6 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l3 X2 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK0]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = (X3 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X0)) (X2 ◇ (X0 ◇ X1))]
  have l9 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3)) = (X1 ◇ X3) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l6 X2 X0 X1 X3]
    conv => enter [1]; rw [← l5 X1 X3 X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1, 2]; rw [← l5 (sK0 ◇ sK0) sK0 sK0]
  have l11 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← l5 (X1 ◇ (X0 ◇ X0)) (X2 ◇ (X0 ◇ X1)) X0]
  have l12 : ∀ X0 X1 X3 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3) = (X1 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l5 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X3 X0]
    conv => enter [1]; rw [l9 X0 X0 X1 X3]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) sK0 sK0]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [← l5 (X1 ◇ (X0 ◇ X0)) (X2 ◇ (X0 ◇ X1)) X0]
  have l15 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X3)) := by
    intro X1 X3 X0
    conv => enter [1]; rw [← l12 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X0)) X3]
  have l16 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) (X2 ◇ (X0 ◇ X1))]
  have l17 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = ((X1 ◇ (X0 ◇ X0)) ◇ X3) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l15 X1 X3 X0]
    conv => enter [1]; rw [← l5 (X1 ◇ (X0 ◇ X0)) X3 X0]
  have l18 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l16 X0 X1 X2]
    conv => enter [1]; rw [← l5 (X0 ◇ X0) (X2 ◇ (X0 ◇ X1)) X1]
  have l19 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ X3)) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l17 X1 X3 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X3]
  have l20 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X0 (X2 ◇ (X0 ◇ X1))]
  have l21 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l19 X1 X3 X0]
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X3 X1]
  have l22 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 X0 X1 X2]
    conv => enter [1, 2]; rw [← l5 X2 (X0 ◇ X1) X0]
  have l23 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l21 X1 X3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l24 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l22 X0 X1 X2]
    conv => enter [1]; rw [← l5 X2 (X0 ◇ X1) X0]
  have l25 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X0 ◇ X3) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l23 X1 X3 X0]
    conv => enter [1]; rw [← l5 X0 X3 X0]
  have l26 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [← l24 X0 X1 X2]
  have l27 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l26 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
  have l28 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l27 X0 X1 X2]
    conv => enter [1]; rw [← l5 (X1 ◇ (X0 ◇ X0)) X2 X0]
  have l29 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l28 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l30 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l29 X0 X1 X2]
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X2 X1]
  have l31 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l30 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l32 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l31 X0 X1 X2]
    conv => enter [1]; rw [← l5 X0 X2 X0]
  have l33 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l25 sK2 sK2 sK1]
  have l34 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l25 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l33 sK1 sK2]
  have l35 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l34 sK1 sK2]
    conv => enter [1]; rw [l25 sK1 (sK1 ◇ sK2) X0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l32 (sK0 ◇ sK0) sK0 X0]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l35 sK1 sK2 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l37 x y z]

@[equational_result]
theorem Equation41_implies_Equation42053 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42053 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

end Semigroup5
