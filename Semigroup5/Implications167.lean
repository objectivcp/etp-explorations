import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation42285_implies_Equation41 (G : Type*) [Magma G] (h42285 : Equation42285 G) : Equation41 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h42285 X0 X2 X0 X0 X0]
    conv => enter [1]; rw [← h42285 X0 X1 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42285 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42287 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42287 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 sK4 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK0 ◇ sK4)) := by
    intro sK2 sK3 sK0 sK4
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK0 ◇ sK4)]
  have l2 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0 sK4]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation42287_implies_Equation41 (G : Type*) [Magma G] (h42287 : Equation42287 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42287 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42287 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42287 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42288 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42288 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK0 ◇ sK1)]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0 sK1]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation42288_implies_Equation41 (G : Type*) [Magma G] (h42288 : Equation42288 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42288 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42288 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42288 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42289 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42289 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK0]
  have l2 : ∀ sK0 sK4 sK1 sK2 : G, (sK0 ◇ sK0) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK1 sK2
    conv => enter [1]; rw [h41 sK0 sK4 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK1]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 sK4 sK1 sK2]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation42289_implies_Equation41 (G : Type*) [Magma G] (h42289 : Equation42289 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42289 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42289 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42289 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42289 X0 X1 sK1 X0 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation41_implies_Equation42290 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42290 G := by
  have l0 : ∀ X1 X2 sK3 sK4 : G, (X1 ◇ X2) = (sK3 ◇ sK4) := by
    intro X1 X2 sK3 sK4
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK3 sK4]
  have l1 : ∀ sK3 sK4 sK0 sK1 : G, (sK3 ◇ sK4) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK3 (sK0 ◇ sK1)]
  have l2 : ∀ sK3 sK4 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK2 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l1 sK3 sK4 sK0 sK1]
  have l3 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK5 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l2 sK3 sK4 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l3 x y z w u v]

@[equational_result]
theorem Equation42290_implies_Equation41 (G : Type*) [Magma G] (h42290 : Equation42290 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42290 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42290 X0 X2 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42290 X0 X1 sK0 X0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42291 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42291 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h41 sK2 sK0 (sK2 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [h41 sK1 sK3 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l1 x z w y]

theorem Equation4512_42291_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42291 : Equation42291 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42291 (X0 ◇ X0) X1 X2 X0]
    conv => enter [1, 2]; rw [← h42291 X0 (X0 ◇ X0) X0 X1]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42291 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42291 X0 X1 X0 X0]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X0]
    conv => enter [1]; rw [← l3 X2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0]
    conv => enter [1, 2]; rw [← l2 X0 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l2 X0 X0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← l6 sK1 X0]
  have l9 : ∀ sK1 X0 X1 X2 sK2 : G, (sK1 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 X1 X2 sK2
    conv => enter [1]; rw [h42291 sK1 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK1 sK2]
  have l10 : ∀ sK1 X0 X2 sK2 : G, (sK1 ◇ X0) = (X2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 X2 sK2
    conv => enter [1]; rw [l9 sK1 X0 sK1 X2 sK2]
    conv => enter [1]; rw [← l2 X2 (X0 ◇ (sK1 ◇ sK2)) sK1]
  have l11 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l10 sK1 X0 sK1 sK2]
    conv => enter [1]; rw [← l2 X0 (sK1 ◇ sK2) sK1]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2 X0]
    conv => enter [1]; rw [l11 sK1 X0 sK2]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42293 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42293 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK3]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42293_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42293 : Equation42293 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X1 X0 X4 : G, (X2 ◇ X3) = ((X1 ◇ (X0 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X1))) := by
    intro X2 X3 X1 X0 X4
    conv => enter [1]; rw [h42293 X2 X3 (X1 ◇ (X0 ◇ X3)) X4]
    conv => enter [1, 2, 2]; rw [← h42293 X0 X1 X3 X2]
  have l1 : ∀ X2 X3 X1 X0 X4 : G, (X2 ◇ X3) = (X1 ◇ ((X0 ◇ X3) ◇ (X4 ◇ (X0 ◇ X1)))) := by
    intro X2 X3 X1 X0 X4
    conv => enter [1]; rw [l0 X2 X3 X1 X0 X4]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X3) (X4 ◇ (X0 ◇ X1))]
  have l2 : ∀ X2 X3 X0 X4 : G, (X2 ◇ X3) = (X0 ◇ X4) := by
    intro X2 X3 X0 X4
    conv => enter [1]; rw [l1 X2 X3 X2 X0 X4]
    conv => enter [1]; rw [← h42293 X0 X4 X2 (X0 ◇ X3)]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation42294 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42294 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42294_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42294 : Equation42294 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42294 sK0 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42294 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X1 ◇ (X0 ◇ X4)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42294 X0 X1 X0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 X0]
    conv => enter [1]; rw [← l2 X0 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) X0 X0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42294 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l5 y z x]

@[equational_result]
theorem Equation41_implies_Equation42295 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42295 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 sK0]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42295_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42295 : Equation42295 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X0 ◇ X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h42295 X0 X1 (X2 ◇ X3) X4 X5]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X1 ◇ (X0 ◇ X5)))]
  have l1 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X1 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X4 X0]
    conv => enter [1]; rw [← h42295 X1 X4 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42296 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42296 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42296_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42296 : Equation42296 G) : Equation41 G := by
  have l0 : ∀ sK2 X0 sK1 X1 X2 : G, ((sK2 ◇ X0) ◇ sK1) = (X1 ◇ (X2 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 sK1 X1 X2
    conv => enter [1]; rw [h42296 (sK2 ◇ X0) sK1 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42296 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42296 X0 X1 X0 X0]
  have l3 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ (X2 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)))) = (sK2 ◇ (X0 ◇ sK1)) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK2 X0 sK1 X1 X2]
    conv => enter [1]; rw [← h4512 sK2 X0 sK1]
  have l4 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ (X2 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)))) = (X0 ◇ sK1) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [l3 X1 X2 sK1 sK2 X0]
    conv => enter [1]; rw [← l2 X0 sK1 sK2]
  have l5 : ∀ X2 sK1 sK2 X0 : G, (X2 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) = (X0 ◇ sK1) := by
    intro X2 sK1 sK2 X0
    conv => enter [1, 2]; rw [l2 sK1 ((sK1 ◇ sK2) ◇ X0) X2]
    conv => enter [1]; rw [l4 X2 X2 sK1 sK2 X0]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 sK2 X0]
  have l7 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
  have l8 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l9 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X1 ◇ sK1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l2 X1 sK1 X0]
  have l10 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X1 ◇ sK1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l2 X0 X1 (sK1 ◇ X0)]
    conv => enter [1]; rw [l9 sK1 X0 X0 X1]
  have l11 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X0 ◇ X1) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l10 X2 X1 X2]
    conv => enter [1]; rw [← l10 X0 X1 X2]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l7 sK1 sK0 sK0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ sK1) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 X0]
    conv => enter [1]; rw [← l13 sK0 X1 X0]
  intro x y z
  conv => enter [1]; rw [← l14 y z x]

@[equational_result]
theorem Equation41_implies_Equation42298 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42298 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK3]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42298_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42298 : Equation42298 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42298 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42298 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = (sK0 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h42298 X0 X1 sK0 X2]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0 X0]
    conv => enter [1]; rw [l1 sK0 X0 (X1 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X1]
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
theorem Equation41_implies_Equation42299 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42299 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42299_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42299 : Equation42299 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42299 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42299 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0 sK1]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h42299 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 X1]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l8 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [l2 sK0 X1 (sK0 ◇ sK0)]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l9 X0 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [← l5 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l10 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l11 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l13 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [← l14 y z x]

@[equational_result]
theorem Equation41_implies_Equation42300 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42300 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42300_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42300 : Equation42300 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42300 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42300 X2 X1 X0 X0 X0]
  have l1 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h42300 sK0 sK0 X1 X2 X3]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X3))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [l1 sK0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X3]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l5 sK1 sK2]
  have l7 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [h42300 X0 X1 X2 X3 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 X1 X1 X0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l7 X0 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42301 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42301 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK1]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42301_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42301 : Equation42301 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ X1) = (sK0 ◇ (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42301 (sK0 ◇ X0) X1 sK0 X2]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X0 X1 X2 X4
    conv => enter [1]; rw [h42301 X3 (X0 ◇ X1) X2 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X4 X2 X3 X0 X1 : G, (X4 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X4 X2 X3 X0 X1
    conv => enter [1]; rw [h42301 X4 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ X3 X1 X0 : G, (X3 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := by
    intro X3 X1 X0
    conv => enter [1]; rw [l2 X3 X1 X3 X3 X0]
    conv => enter [1]; rw [← l1 X3 X0 X1 X3 X3]
  have l4 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l0 sK0 X0 X1 X2]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← l3 sK0 (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1]; rw [← l5 sK0 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1]; rw [← l3 sK0 X1 X0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42301 X0 X1 sK0 X0]
    conv => enter [1]; rw [l8 sK0 (X0 ◇ (X1 ◇ (sK0 ◇ X0))) sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42303 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42303 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK3) = (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [h41 sK3 sK0 (sK2 ◇ (sK3 ◇ sK3))]
  have l1 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK3) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [h41 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z w y]

theorem Equation4512_42303_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42303 : Equation42303 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42303 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42303 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h42303 X0 X1 (sK0 ◇ sK0) X2]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l5 X0 X1 sK0 X2]
    conv => enter [1, 2, 2]; rw [← l2 sK0 X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l2 sK0 X0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42304 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42304 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42304_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42304 : Equation42304 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42304 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42304 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h42304 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 X2]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 X1]
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l6 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l2 sK0 X0]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42305 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42305 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ sK0) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 sK0]
  have l2 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK4 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ (sK4 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK4 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42305_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42305 : Equation42305 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X1 X0 : G, (X2 ◇ X3) = (X1 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X1 X0
    conv => enter [1]; rw [h42305 X2 X3 X1 X2 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h42305 X0 X1 X2 X3 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42305 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42305 X2 X1 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0 X1]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0) sK1 sK2]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ sK1) sK1 sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42306 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42306 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ sK1)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_42306_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42306 : Equation42306 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ X1) = (X2 ◇ (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42306 (sK0 ◇ X0) X1 X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK2 X0 X1 X2 sK1 : G, ((sK2 ◇ X0) ◇ X1) = (X2 ◇ (sK1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 X1 X2 sK1
    conv => enter [1]; rw [h42306 (sK2 ◇ X0) X1 X2 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l3 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42306 (sK0 ◇ X0) X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l4 : ∀ X3 X0 X1 X4 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X0 X1 X4 X2
    conv => enter [1]; rw [h42306 X3 (X0 ◇ X1) X4 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42306 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X1 ◇ (X4 ◇ X0)))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42306 X0 X1 X0 X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← l4 X0 X1 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK2 X0 X1 X2 sK1 : G, (sK2 ◇ (X0 ◇ X1)) = (X2 ◇ (sK1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 X1 X2 sK1
    conv => enter [1]; rw [h4512 sK2 X0 X1]
    conv => enter [1]; rw [l2 sK2 X0 X1 X2 sK1]
  have l9 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l1 sK0 X0 X1 X2]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X1 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [← l6 X1 sK0 X0]
  have l11 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ (X0 ◇ X1)) = (sK1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l8 sK2 X0 X1 sK2 sK1]
    conv => enter [1]; rw [← l6 sK1 (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) sK2]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l6 X1 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l14 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l11 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← l6 X1 ((sK1 ◇ sK2) ◇ X0) sK1]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1]; rw [← l6 X1 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l17 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [← l14 sK2 X0 X1 sK1]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l15 sK0 X0 X1]
  have l19 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ X0) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 sK2]
    conv => enter [1]; rw [← l17 sK1 sK2 X0 X1]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← l18 sK0 X0 X1]
  have l21 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1]; rw [l19 (sK0 ◇ sK0) X0 sK1 sK2]
  have l22 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l21 X0 X1 sK1 sK2 X0]
    conv => enter [1]; rw [l19 (sK1 ◇ sK2) (X0 ◇ X0) sK1 sK2]
  have l23 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l22 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l16 (sK1 ◇ sK2) (sK1 ◇ sK2) sK0]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l23 X0 X1 X0 X0 sK0]
    conv => enter [1]; rw [l16 (X0 ◇ X0) sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l24 y z x]

@[equational_result]
theorem Equation41_implies_Equation42308 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42308 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ sK3)]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0 sK3]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_42308_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42308 : Equation42308 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42308 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42308 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h42308 X0 X1 (sK0 ◇ sK0) X2]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 X2]
  have l6 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l5 X0 X1 sK0 X2]
    conv => enter [1, 2, 2]; rw [← l2 sK0 X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l2 sK0 X0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42309 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42309 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [h41 sK0 sK3 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_42309_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42309 : Equation42309 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42309 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42309 X2 X1 X0 X0]
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
  have l4 : ∀ X0 X1 X2 sK2 sK1 : G, (X0 ◇ X1) = (X2 ◇ (sK2 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK2 sK1
    conv => enter [1]; rw [h42309 X0 X1 X2 sK2]
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
    conv => enter [1]; rw [l4 X0 X1 X0 sK2 sK1]
    conv => enter [1]; rw [l1 X0 sK2 (X1 ◇ (sK1 ◇ sK2)) sK1]
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
theorem Equation41_implies_Equation42310 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42310 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK1 ◇ sK0)]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

theorem Equation4512_42310_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42310 : Equation42310 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42310 X2 X3 X4 X1 (X3 ◇ X2)]
    conv => enter [1, 2]; rw [← h42310 X0 X1 X1 X3 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42310 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42310 X2 X1 X0 X0 X0]
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
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42310 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2 X2 (X3 ◇ (X2 ◇ X2))]
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
theorem Equation41_implies_Equation42311 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42311 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK0 ◇ sK2)]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

theorem Equation4512_42311_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42311 : Equation42311 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ sK0) = (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [h42311 X1 sK0 X2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l2 : ∀ X2 X3 X1 X4 X0 X5 : G, (X2 ◇ ((X3 ◇ (X1 ◇ (X4 ◇ X0))) ◇ X5)) = ((X0 ◇ X1) ◇ X5) := by
    intro X2 X3 X1 X4 X0 X5
    conv => enter [1]; rw [h4512 X2 (X3 ◇ (X1 ◇ (X4 ◇ X0))) X5]
    conv => enter [1, 1]; rw [← h42311 X0 X1 X2 X3 X4]
  have l3 : ∀ X2 X3 X1 X4 X0 X5 : G, (X2 ◇ ((X3 ◇ (X1 ◇ (X4 ◇ X0))) ◇ X5)) = (X0 ◇ (X1 ◇ X5)) := by
    intro X2 X3 X1 X4 X0 X5
    conv => enter [1]; rw [l2 X2 X3 X1 X4 X0 X5]
    conv => enter [1]; rw [← h4512 X0 X1 X5]
  have l4 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [l1 X1 sK0 X1 X1]
    conv => enter [1]; rw [← h42311 X1 (sK0 ◇ sK0) X1 sK0 X1]
  have l5 : ∀ X0 X1 X5 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X5)) = (X2 ◇ (X3 ◇ ((X1 ◇ (X4 ◇ X0)) ◇ X5))) := by
    intro X0 X1 X5 X2 X3 X4
    conv => enter [1]; rw [← l3 X2 X3 X1 X4 X0 X5]
    conv => enter [1, 2]; rw [← h4512 X3 (X1 ◇ (X4 ◇ X0)) X5]
  have l6 : ∀ X0 X1 X5 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X5)) = (X2 ◇ (X3 ◇ (X1 ◇ ((X4 ◇ X0) ◇ X5)))) := by
    intro X0 X1 X5 X2 X3 X4
    conv => enter [1]; rw [l5 X0 X1 X5 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X4 ◇ X0) X5]
  have l7 : ∀ X0 X1 X5 : G, (X0 ◇ (X1 ◇ X5)) = (X5 ◇ X1) := by
    intro X0 X1 X5
    conv => enter [1]; rw [l6 X0 X1 X5 X0 X0 X0]
    conv => enter [1]; rw [← h42311 X5 X1 X0 X0 (X0 ◇ X0)]
  have l8 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l4 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← h4512 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
  have l10 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l9 sK1 sK2 sK0]
    conv => enter [1]; rw [← l4 (sK1 ◇ sK2) sK0]
  have l11 : ∀ sK0 X0 X1 X2 sK2 : G, (sK0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 X1 X2 sK2
    conv => enter [1]; rw [h42311 sK0 X0 X1 X2 (sK0 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK0 sK2 sK0]
  have l12 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) sK0 X0]
    conv => enter [1, 1]; rw [← l10 sK0 sK2 sK1]
  have l13 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
  have l14 : ∀ sK2 X0 sK0 : G, (sK2 ◇ X0) = (sK0 ◇ X0) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h42311 sK2 X0 sK2 sK2 sK0]
    conv => enter [1]; rw [← l11 sK0 X0 sK2 sK2 sK2]
  have l15 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) = (X0 ◇ sK2) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l7 sK0 sK2 X0]
  have l16 : ∀ X0 sK0 sK2 : G, (X0 ◇ sK0) = (X0 ◇ sK2) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l7 (X0 ◇ sK2) sK0 X0]
    conv => enter [1]; rw [l15 X0 sK2 sK0 X0]
  have l17 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l14 sK2 X0 sK0]
  have l18 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ sK0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l17 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 X0]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2 sK1]
    conv => enter [1]; rw [← l18 sK1 sK2 sK1 sK1]
  have l20 : ∀ X1 X2 X0 sK1 sK2 : G, (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ X0) := by
    intro X1 X2 X0 sK1 sK2
    conv => enter [1, 2, 2, 2]; rw [l19 sK1 sK2]
    conv => enter [1]; rw [← h42311 sK1 X0 X1 X2 (sK1 ◇ sK2)]
  have l21 : ∀ sK1 X0 sK2 X2 : G, (sK1 ◇ X0) = ((X0 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro sK1 X0 sK2 X2
    conv => enter [1]; rw [← l20 sK1 X2 X0 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 X2 (X0 ◇ (sK1 ◇ sK2))]
  have l22 : ∀ sK1 X0 sK2 X2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK1 X0 sK2 X2
    conv => enter [1]; rw [l21 sK1 X0 sK2 X2]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK2) X2]
  have l23 : ∀ X2 sK1 sK2 X0 : G, (X2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ X0) := by
    intro X2 sK1 sK2 X0
    conv => enter [1]; rw [← l7 X0 (sK1 ◇ sK2) X2]
    conv => enter [1]; rw [← l22 sK1 X0 sK2 X2]
  have l24 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((X0 ◇ sK0) ◇ X1) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1, 1]; rw [l18 sK1 sK2 X0 sK0]
  have l25 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l24 sK1 sK2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l26 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X1 ◇ sK0) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l25 sK1 sK2 X0 X1 sK0]
    conv => enter [1]; rw [l7 X0 sK0 X1]
  have l27 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ X0) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l26 X1 X1 X0 X1 sK0]
    conv => enter [1]; rw [l7 (X1 ◇ X1) X0 X1]
  have l28 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ sK0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← l23 X0 sK1 sK2 sK2]
    conv => enter [1]; rw [l27 X0 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [l28 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42313 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42313 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 sK4 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK0 ◇ sK4)) := by
    intro sK2 sK3 sK0 sK4
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK0 ◇ sK4)]
  have l2 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0 sK4]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

theorem Equation4512_42313_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42313 : Equation42313 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42313 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42313 X2 X1 X0 X0 X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ X1)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 X1]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l3 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK0 ◇ (X3 ◇ X1)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h42313 sK0 sK0 X1 X2 X3]
  have l4 : ∀ sK0 X1 X3 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X3 ◇ X1))) := by
    intro sK0 X1 X3
    conv => enter [1]; rw [l3 sK0 X1 sK0 X3]
    conv => enter [1, 2]; rw [← l2 sK0 (X3 ◇ X1) sK0]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l5 sK1 sK2]
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ sK0) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l1 X0 (X1 ◇ X2) X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0 X2 X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42313 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l7 X0 X0 (X1 ◇ (X0 ◇ X0)) sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42314 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42314 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK0 ◇ sK1)]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0 sK1]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

theorem Equation4512_42314_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42314 : Equation42314 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42314 X2 X3 X4 (X2 ◇ X3) X1]
    conv => enter [1, 2]; rw [← h42314 X0 X1 (X2 ◇ X3) X3 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42314 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42314 X2 X1 X0 X0 X0]
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
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42314 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2 X2 (X3 ◇ (X2 ◇ X2))]
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
theorem Equation41_implies_Equation42315 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42315 G := by
  have l0 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK1 (sK3 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK0]
  have l2 : ∀ sK0 sK4 sK1 sK3 : G, (sK0 ◇ sK0) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK1 sK3
    conv => enter [1]; rw [h41 sK0 sK4 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK1]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 sK4 sK1 sK3]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

theorem Equation4512_42315_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42315 : Equation42315 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42315 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42315 X2 X1 X0 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (sK2 ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l0 X0 (sK2 ◇ X1) sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 X1]
  have l3 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK0 ◇ (X3 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h42315 sK0 sK0 X1 X2 X3]
  have l4 : ∀ sK0 X1 X3 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X3 ◇ X3))) := by
    intro sK0 X1 X3
    conv => enter [1]; rw [l3 sK0 X1 sK0 X3]
    conv => enter [1, 2]; rw [← l1 sK0 (X3 ◇ X3) sK0]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l5 sK1 sK2]
  have l7 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 X0 sK2]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK0) sK2 sK2 sK1]
  have l8 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK2 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l6 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation41_implies_Equation42316 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42316 G := by
  have l0 : ∀ X1 X2 sK3 sK4 : G, (X1 ◇ X2) = (sK3 ◇ sK4) := by
    intro X1 X2 sK3 sK4
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK3 sK4]
  have l1 : ∀ sK3 sK4 sK0 sK1 : G, (sK3 ◇ sK4) = (sK4 ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK4 (sK0 ◇ sK1)]
  have l2 : ∀ sK3 sK4 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK4 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK2 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l1 sK3 sK4 sK0 sK1]
  have l3 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK4 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK5 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l2 sK3 sK4 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l3 x y z w u v]

theorem Equation4512_42316_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42316 : Equation42316 G) : Equation41 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ X1)) = (X2 ◇ X3) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h42316 X0 X1 X4 X3 X4 X4]
    conv => enter [1]; rw [← h42316 X2 X3 X4 X4 X1 (X4 ◇ X4)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42316 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42316 X2 X1 X0 X0 X0 X0]
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
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42316 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 (X1 ◇ (X0 ◇ X0)) X2 X3]
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
theorem Equation41_implies_Equation42317 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42317 G := by
  have l0 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK3 ◇ (sK1 ◇ sK1))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h41 sK3 sK0 (sK3 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h41 sK1 sK3 (sK3 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l0 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l1 x z w]

@[equational_result]
theorem Equation42317_implies_Equation41 (G : Type*) [Magma G] (h42317 : Equation42317 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42317 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42317 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42317 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42319 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42319 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK3]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42319_implies_Equation41 (G : Type*) [Magma G] (h42319 : Equation42319 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42319 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42319 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42319 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42320 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42320 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42320_implies_Equation41 (G : Type*) [Magma G] (h42320 : Equation42320 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42320 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42320 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42320 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42321 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42321 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 sK0]
  have l2 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42321_implies_Equation41 (G : Type*) [Magma G] (h42321 : Equation42321 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42321 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42321 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42321 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42322 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42322 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42322_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42322 : Equation42322 G) : Equation41 G := by
  have l0 : ∀ X4 X3 X2 X0 X1 : G, (X4 ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X4 X3 X2 X0 X1
    conv => enter [1]; rw [h42322 X4 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l1 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42322 sK0 sK0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK0)))]
  have l2 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l1 sK0 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 sK0 X1 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) X1 sK0 X1 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42322 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l3 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

@[equational_result]
theorem Equation41_implies_Equation42324 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42324 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK3]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42324_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42324 : Equation42324 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42324 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42324 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = (sK0 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h42324 X0 X1 sK0 X2]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
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
theorem Equation41_implies_Equation42325 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42325 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42325_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42325 : Equation42325 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42325 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42325 X2 X1 X0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 (sK0 ◇ X1) sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h42325 X0 X1 X2 sK0]
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
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1]; rw [l1 X2 sK0 (X2 ◇ (sK0 ◇ sK0))]
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
theorem Equation41_implies_Equation42326 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42326 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  have l2 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42326_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42326 : Equation42326 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42326 X2 X3 X4 X3 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42326 X0 X1 X3 X4 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42326 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42326 X2 X1 X0 X0 X0]
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
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42326 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2 X2 (X2 ◇ (X3 ◇ X2))]
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
theorem Equation41_implies_Equation42327 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42327 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK1]
  have l2 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK3 ◇ sK1))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42327_implies_Equation41 (G : Type*) [Magma G] (h42327 : Equation42327 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42327 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42327 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42327 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42329 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42329 G := by
  have l0 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (sK0 ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [h41 sK3 sK0 (sK3 ◇ (sK3 ◇ sK3))]
  have l1 : ∀ sK3 sK0 : G, (sK3 ◇ sK3) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h41 sK3 sK3 (sK3 ◇ (sK3 ◇ sK3))]
    conv => enter [1, 2]; rw [l0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z w]

@[equational_result]
theorem Equation42329_implies_Equation41 (G : Type*) [Magma G] (h42329 : Equation42329 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42329 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42329 X2 X3 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42330 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42330 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42330_implies_Equation41 (G : Type*) [Magma G] (h42330 : Equation42330 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42330 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42330 X2 X3 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42331 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42331 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ sK0) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 sK0]
  have l2 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK4 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ (sK4 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK4 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42331_implies_Equation41 (G : Type*) [Magma G] (h42331 : Equation42331 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42331 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42331 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42332 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42332 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK1]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK1)]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l1 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [← l0 sK1 sK3 sK0]
    conv => enter [1, 2]; rw [l3 sK1 sK3 sK0 sK3]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l4 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation42332_implies_Equation41 (G : Type*) [Magma G] (h42332 : Equation42332 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42332 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42332 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42332 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42334 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42334 G := by
  have l0 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ sK3) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK3]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK3)]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l1 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK0
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK3 sK3]
    conv => enter [1, 2]; rw [l3 sK3 sK3 sK0 sK3]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l4 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation42334_implies_Equation41 (G : Type*) [Magma G] (h42334 : Equation42334 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42334 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42334 X2 X3 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42335 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42335 G := by
  have l0 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK0 (sK3 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK3 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [h41 sK0 sK3 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation42335_implies_Equation41 (G : Type*) [Magma G] (h42335 : Equation42335 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42335 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42335 X2 X3 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42336 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42336 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ sK0) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 sK0]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ sK0)]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK1 sK0]
  have l4 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK4 sK4]
    conv => enter [1, 2]; rw [l3 sK4 sK4 sK1 sK4 sK0]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l4 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

@[equational_result]
theorem Equation42336_implies_Equation41 (G : Type*) [Magma G] (h42336 : Equation42336 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42336 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42336 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42337 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42337 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK2) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK2]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK0 ◇ sK2)]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK0]
  have l4 : ∀ sK4 sK0 sK2 sK1 : G, (sK4 ◇ (sK0 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK2)))) := by
    intro sK4 sK0 sK2 sK1
    conv => enter [1, 2]; rw [← l0 sK2 sK4 sK0]
    conv => enter [1, 2]; rw [l3 sK2 sK4 sK1 sK4 sK0]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK0]
    conv => enter [1]; rw [l4 sK4 sK0 sK2 sK1]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

@[equational_result]
theorem Equation42337_implies_Equation41 (G : Type*) [Magma G] (h42337 : Equation42337 G) : Equation41 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h42337 X0 X2 X0 X0 X0]
    conv => enter [1]; rw [← h42337 X0 X1 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42337 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42339 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42339 G := by
  have l0 : ∀ sK2 sK3 sK0 sK4 : G, (sK2 ◇ sK3) = (sK0 ◇ sK4) := by
    intro sK2 sK3 sK0 sK4
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK4]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK0 ◇ sK4)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK0 ◇ sK4)]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK0]
  have l4 : ∀ sK4 sK0 sK1 : G, (sK4 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK4)))) := by
    intro sK4 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK4 sK4 sK4]
    conv => enter [1, 2]; rw [l3 sK4 sK4 sK1 sK4 sK0]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK0]
    conv => enter [1]; rw [l4 sK4 sK0 sK1]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

@[equational_result]
theorem Equation42339_implies_Equation41 (G : Type*) [Magma G] (h42339 : Equation42339 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42339 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42339 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42340 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42340 G := by
  have l0 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ sK3) = (sK0 ◇ sK1) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK1]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK4 sK0 sK1 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK3 sK4 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK0 ◇ sK1)]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK0 sK1]
  have l4 : ∀ sK4 sK0 sK1 : G, (sK4 ◇ (sK0 ◇ sK1)) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK4 sK4]
    conv => enter [1, 2]; rw [l3 sK4 sK4 sK1 sK4 sK0]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK0 sK1]
    conv => enter [1]; rw [l4 sK4 sK0 sK1]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

@[equational_result]
theorem Equation42340_implies_Equation41 (G : Type*) [Magma G] (h42340 : Equation42340 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42340 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42340 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42341 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42341 G := by
  have l0 : ∀ sK4 sK0 sK1 : G, (sK4 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK4 ◇ (sK0 ◇ sK0))) := by
    intro sK4 sK0 sK1
    conv => enter [1]; rw [← h41 sK4 sK4 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK4 sK1 (sK4 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK0]
  have l2 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ sK0) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [h41 sK0 sK4 (sK4 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK4 sK0 sK1]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation42341_implies_Equation41 (G : Type*) [Magma G] (h42341 : Equation42341 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42341 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42341 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42342 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42342 G := by
  have l0 : ∀ sK3 sK4 sK0 sK1 : G, (sK3 ◇ sK4) = (sK0 ◇ sK1) := by
    intro sK3 sK4 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK0 sK1]
  have l1 : ∀ X1 X2 sK3 sK4 : G, (X1 ◇ X2) = (sK3 ◇ sK4) := by
    intro X1 X2 sK3 sK4
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK3 sK4]
  have l2 : ∀ sK3 sK4 sK5 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK5 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 (sK0 ◇ sK1)]
  have l3 : ∀ sK3 sK4 sK2 sK5 sK0 sK1 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK5 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK2 sK5 sK0 sK1
    conv => enter [1]; rw [l1 sK3 sK4 sK2 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l2 sK3 sK4 sK5 sK0 sK1]
  have l4 : ∀ sK5 sK0 sK1 sK2 : G, (sK5 ◇ (sK0 ◇ sK1)) = (sK5 ◇ (sK2 ◇ (sK5 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK5 sK5]
    conv => enter [1, 2]; rw [l3 sK5 sK5 sK2 sK5 sK0 sK1]
  have l5 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK5 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l2 sK3 sK4 sK5 sK0 sK1]
    conv => enter [1]; rw [l4 sK5 sK0 sK1 sK2]
  intro x y z w u v
  conv => enter [1]; rw [l5 x y z w u v]

@[equational_result]
theorem Equation42342_implies_Equation41 (G : Type*) [Magma G] (h42342 : Equation42342 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42342 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42342 X2 X3 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42343 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42343 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h41 sK1 sK3 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l1 x z w]

theorem Equation4512_42343_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42343 : Equation42343 G) : Equation41 G := by
  have l0 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← h42343 sK0 (sK0 ◇ X2) X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l1 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [h42343 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 X2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42343 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42345 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42345 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK3]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42345_implies_Equation41 (G : Type*) [Magma G] (h42345 : Equation42345 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42345 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42345 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42345 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42346 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42346 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42346_implies_Equation41 (G : Type*) [Magma G] (h42346 : Equation42346 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42346 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42346 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42346 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42347 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42347 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 sK0]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42347_implies_Equation41 (G : Type*) [Magma G] (h42347 : Equation42347 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42347 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42347 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42347 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42348 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42348 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42348_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42348 : Equation42348 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42348 X0 sK0 X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X3 X2 X4 X0 X1 : G, (X3 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))))) := by
    intro X3 X2 X4 X0 X1
    conv => enter [1]; rw [h42348 X3 X2 X4 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ X3))]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42348 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X4 ◇ (X1 ◇ X0)))]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42348 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X1 ◇ X0))]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (X1 ◇ X0)]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42348 X0 X1 X0 X0]
  have l7 : ∀ X3 X2 X4 X0 X1 : G, (X3 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X3 X2 X4 X0 X1
    conv => enter [1]; rw [l2 X3 X2 X4 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1]; rw [← l1 (X1 ◇ X0) sK0 sK0]
  have l9 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l7 X3 X2 X3 X0 X1]
    conv => enter [1]; rw [← l6 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X3]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X1 X0 sK0]
  have l11 : ∀ X3 X2 X1 X0 : G, (X3 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X2 X1 X0
    conv => enter [1]; rw [l9 X3 X2 X0 X1]
    conv => enter [1]; rw [← l6 X1 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 sK0]
    conv => enter [1]; rw [← l6 X0 sK0 X1]
  have l13 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l11 X3 X2 X1 X0]
    conv => enter [1]; rw [← l6 X0 (X1 ◇ (X2 ◇ X3)) X1]
  have l14 : ∀ X1 X2 X3 : G, (X1 ◇ (X2 ◇ X3)) = (X3 ◇ X2) := by
    intro X1 X2 X3
    conv => enter [1, 2]; rw [l6 X2 X3 X1]
    conv => enter [1]; rw [← l13 X3 X2 X1 X1]
  have l15 : ∀ X3 X2 X1 sK0 : G, (X3 ◇ X2) = (X1 ◇ sK0) := by
    intro X3 X2 X1 sK0
    conv => enter [1]; rw [← l14 X1 X2 X3]
    conv => enter [1]; rw [l12 X1 (X2 ◇ X3) sK0]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l16 y z x]

@[equational_result]
theorem Equation41_implies_Equation42350 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42350 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK3]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42350_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42350 : Equation42350 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42350 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42350 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = (sK0 ◇ (X2 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h42350 X0 X1 sK0 X2]
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
    conv => enter [1]; rw [l1 sK0 X2 (X2 ◇ (sK0 ◇ sK0))]
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
theorem Equation41_implies_Equation42351 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42351 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42351_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42351 : Equation42351 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42351 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42351 X2 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X1) X0]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h42351 X0 X1 X2 sK0]
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
    conv => enter [1]; rw [l4 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
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
theorem Equation41_implies_Equation42352 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42352 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42352_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42352 : Equation42352 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42352 X2 X3 X4 X3 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42352 X0 X1 X3 X3 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42352 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42352 X2 X1 X0 X0 X0]
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
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42352 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2 X2 (X2 ◇ (X3 ◇ X2))]
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
theorem Equation41_implies_Equation42353 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42353 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK1]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42353_implies_Equation41 (G : Type*) [Magma G] (h42353 : Equation42353 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42353 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42353 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42353 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42355 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42355 G := by
  have l0 : ∀ sK3 sK0 : G, (sK3 ◇ sK3) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h41 sK3 sK0 (sK0 ◇ (sK3 ◇ sK3))]
  have l1 : ∀ sK3 sK0 : G, (sK3 ◇ sK3) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h41 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z w]

@[equational_result]
theorem Equation42355_implies_Equation41 (G : Type*) [Magma G] (h42355 : Equation42355 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42355 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42355 X2 X3 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42356 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42356 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42356_implies_Equation41 (G : Type*) [Magma G] (h42356 : Equation42356 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42356 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42356 X2 X3 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42357 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42357 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ sK0) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 sK0]
  have l2 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK4 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK4 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK4 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42357_implies_Equation41 (G : Type*) [Magma G] (h42357 : Equation42357 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42357 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42357 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42358 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42358 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation42358_implies_Equation41 (G : Type*) [Magma G] (h42358 : Equation42358 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42358 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42358 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42358 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42360 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42360 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation42360_implies_Equation41 (G : Type*) [Magma G] (h42360 : Equation42360 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42360 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42360 X2 X3 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42361 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42361 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK3 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation42361_implies_Equation41 (G : Type*) [Magma G] (h42361 : Equation42361 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42361 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42361 X2 X3 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42362 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42362 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation42362_implies_Equation41 (G : Type*) [Magma G] (h42362 : Equation42362 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42362 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42362 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42363 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42363 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation42363_implies_Equation41 (G : Type*) [Magma G] (h42363 : Equation42363 G) : Equation41 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h42363 X0 X2 X0 X0 X0]
    conv => enter [1]; rw [← h42363 X0 X1 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42363 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42365 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42365 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK4)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation42365_implies_Equation41 (G : Type*) [Magma G] (h42365 : Equation42365 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42365 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42365 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42366 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42366 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation42366_implies_Equation41 (G : Type*) [Magma G] (h42366 : Equation42366 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42366 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42366 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42367 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42367 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK0]
  have l2 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ sK0) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [h41 sK0 sK4 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK1 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation42367_implies_Equation41 (G : Type*) [Magma G] (h42367 : Equation42367 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42367 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42367 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42368 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42368 G := by
  have l0 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y z w u v]

@[equational_result]
theorem Equation42368_implies_Equation41 (G : Type*) [Magma G] (h42368 : Equation42368 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42368 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42368 X2 X3 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42369 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42369 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK2 ◇ sK2))]
  have l1 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [h41 sK2 sK4 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l1 x z w u]

theorem Equation4512_42369_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42369 : Equation42369 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 sK0 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X3) := by
    intro X0 X1 X2 sK0 X3
    conv => enter [1]; rw [← h42369 sK0 (sK0 ◇ X3) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 X3]
  have l1 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X3) := by
    intro sK0 X3
    conv => enter [1]; rw [h42369 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK0 X3]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42369 X0 X1 (sK0 ◇ sK0) X0 X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42371 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42371 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ sK3) = (sK2 ◇ sK4) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 sK4]
  have l2 : ∀ sK2 sK3 sK0 sK4 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK2 ◇ sK4)) := by
    intro sK2 sK3 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4]
  have l3 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK4))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0 sK4]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42371_implies_Equation41 (G : Type*) [Magma G] (h42371 : Equation42371 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42371 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42371 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42371 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42372 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42372 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK2 ◇ sK1) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 sK1]
  have l2 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0 sK1]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42372_implies_Equation41 (G : Type*) [Magma G] (h42372 : Equation42372 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42372 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42372 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42372 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42373 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42373 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 sK0]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42373_implies_Equation41 (G : Type*) [Magma G] (h42373 : Equation42373 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42373 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42373 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42373 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42374 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42374 G := by
  have l0 : ∀ X1 X2 sK3 sK4 : G, (X1 ◇ X2) = (sK3 ◇ sK4) := by
    intro X1 X2 sK3 sK4
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK3 sK4]
  have l1 : ∀ sK3 sK4 sK1 : G, (sK3 ◇ sK4) = (sK3 ◇ sK1) := by
    intro sK3 sK4 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK3 sK1]
  have l2 : ∀ sK3 sK4 sK0 sK1 : G, (sK3 ◇ sK4) = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK3 sK4 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK0 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l1 sK3 sK4 sK1]
  have l3 : ∀ sK3 sK4 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro sK3 sK4 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK2 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l2 sK3 sK4 sK0 sK1]
  have l4 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK5 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l3 sK3 sK4 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l4 x y z w u v]

@[equational_result]
theorem Equation42374_implies_Equation41 (G : Type*) [Magma G] (h42374 : Equation42374 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42374 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42374 X0 X2 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42374 X0 X1 sK0 X0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42375 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42375 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 : G, (sK2 ◇ sK3) = (sK3 ◇ sK2) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK2]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42375_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42375 : Equation42375 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X1 X0 X4 X5 X6 X7 : G, ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X4) = (X5 ◇ (X6 ◇ (X7 ◇ (X0 ◇ X1)))) := by
    intro X2 X3 X1 X0 X4 X5 X6 X7
    conv => enter [1]; rw [h42375 (X2 ◇ (X3 ◇ (X1 ◇ X0))) X4 X5 X6 X7]
    conv => enter [1, 2, 2, 2]; rw [← h42375 X0 X1 X4 X2 X3]
  have l1 : ∀ X2 X0 X1 X3 X4 X5 : G, (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1 X3 X4 X5
    conv => enter [1]; rw [h42375 X2 (X0 ◇ X1) X3 X4 X5]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h42375 X0 X1 (X2 ◇ X3) X4 X5]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X5 ◇ (X1 ◇ X0)))]
  have l3 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0 X5]
    conv => enter [1]; rw [← h42375 (X1 ◇ X0) X5 X0 X0 X0]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1 X2 X2 X2]
    conv => enter [1]; rw [← h42375 (X1 ◇ X2) X0 X2 X2 X2]
  have l5 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ X0) = ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X4) := by
    intro X1 X0 X2 X3 X4
    conv => enter [1]; rw [h42375 X1 X0 X1 X1 X1]
    conv => enter [1]; rw [← l0 X2 X3 X1 X0 X4 X1 X1 X1]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l4 X2 X0 X1]
    conv => enter [1]; rw [← l3 X2 X1 X0]
  have l7 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ X0) = (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X4)) := by
    intro X1 X0 X2 X3 X4
    conv => enter [1]; rw [l5 X1 X0 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X2 (X3 ◇ (X1 ◇ X0)) X4]
  have l8 : ∀ X1 X0 X2 X4 : G, (X1 ◇ X0) = (X2 ◇ X4) := by
    intro X1 X0 X2 X4
    conv => enter [1]; rw [l7 X1 X0 X2 X1 X4]
    conv => enter [1]; rw [l6 X2 (X1 ◇ (X1 ◇ X0)) X4]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42377 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42377 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ sK3) = (sK3 ◇ sK4) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK4]
  have l2 : ∀ sK2 sK3 sK0 sK4 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK3 ◇ sK4)) := by
    intro sK2 sK3 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4]
  have l3 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0 sK4]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42377_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42377 : Equation42377 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42377 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42377 X2 X1 X0 X0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 X1 sK0 X2 X3 : G, (X0 ◇ X1) = (sK0 ◇ (X2 ◇ (X3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 X2 X3
    conv => enter [1]; rw [h42377 X0 X1 sK0 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X0 X1 sK0 X3 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 X3
    conv => enter [1]; rw [l2 X0 X1 sK0 X0 X3]
    conv => enter [1]; rw [l1 sK0 X0 (X3 ◇ (sK0 ◇ sK0))]
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
theorem Equation41_implies_Equation42378 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42378 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK3 ◇ sK1) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK1]
  have l2 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0 sK1]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42378_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42378 : Equation42378 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42378 X2 X3 X4 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h42378 X0 X1 (X1 ◇ X2) X2 X3]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42378 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42378 X2 X1 X0 X0 X0]
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
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42378 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2 X2 (X2 ◇ (X3 ◇ X2))]
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
theorem Equation41_implies_Equation42379 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42379 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  have l2 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42379_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42379 : Equation42379 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42379 X2 X3 X4 X2 (X1 ◇ X3)]
    conv => enter [1, 2]; rw [← h42379 X0 X1 X2 (X1 ◇ X3) X3]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42379 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42379 X2 X1 X0 X0 X0]
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
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42379 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2 X2 (X2 ◇ (X3 ◇ X2))]
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
theorem Equation41_implies_Equation42380 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42380 G := by
  have l0 : ∀ X1 X2 sK3 sK4 : G, (X1 ◇ X2) = (sK3 ◇ sK4) := by
    intro X1 X2 sK3 sK4
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK3 sK4]
  have l1 : ∀ sK3 sK4 sK1 : G, (sK3 ◇ sK4) = (sK4 ◇ sK1) := by
    intro sK3 sK4 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK4 sK1]
  have l2 : ∀ sK3 sK4 sK0 sK1 : G, (sK3 ◇ sK4) = (sK0 ◇ (sK4 ◇ sK1)) := by
    intro sK3 sK4 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK0 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l1 sK3 sK4 sK1]
  have l3 : ∀ sK3 sK4 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK0 ◇ (sK4 ◇ sK1))) := by
    intro sK3 sK4 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK2 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l2 sK3 sK4 sK0 sK1]
  have l4 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK4 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK5 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l3 sK3 sK4 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l4 x y z w u v]

theorem Equation4512_42380_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42380 : Equation42380 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42380 X2 X3 X4 X2 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42380 X0 X1 X2 X2 X3 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42380 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42380 X2 X1 X0 X0 X0 X0]
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
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42380 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← l0 X2 X3 X0 X0 (X0 ◇ (X1 ◇ X0))]
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
theorem Equation41_implies_Equation42381 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42381 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ sK3) = (sK4 ◇ sK2) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 sK2]
  have l2 : ∀ sK2 sK3 sK0 sK4 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK4 ◇ sK2)) := by
    intro sK2 sK3 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4]
  have l3 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK2))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0 sK4]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK4 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42381_implies_Equation41 (G : Type*) [Magma G] (h42381 : Equation42381 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42381 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42381 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42381 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42383 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42383 G := by
  have l0 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ sK4) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK4))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [h41 sK4 sK1 (sK0 ◇ (sK4 ◇ sK4))]
  have l1 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ sK4) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK4 ◇ sK4)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [h41 sK4 sK4 (sK4 ◇ sK4)]
    conv => enter [1, 2]; rw [l0 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z w u]

@[equational_result]
theorem Equation42383_implies_Equation41 (G : Type*) [Magma G] (h42383 : Equation42383 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42383 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42383 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42384 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42384 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 sK1 : G, (sK2 ◇ sK3) = (sK4 ◇ sK1) := by
    intro sK2 sK3 sK4 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 sK1]
  have l2 : ∀ sK2 sK3 sK0 sK4 sK1 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK4 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK4 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4 sK1]
  have l3 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK1))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0 sK4 sK1]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK4 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42384_implies_Equation41 (G : Type*) [Magma G] (h42384 : Equation42384 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42384 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42384 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42385 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42385 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ sK0) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 sK0]
  have l2 : ∀ sK2 sK3 sK0 sK4 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK4 ◇ sK0)) := by
    intro sK2 sK3 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0 sK4]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK4 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42385_implies_Equation41 (G : Type*) [Magma G] (h42385 : Equation42385 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42385 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42385 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42386 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42386 G := by
  have l0 : ∀ X1 X2 sK3 sK4 : G, (X1 ◇ X2) = (sK3 ◇ sK4) := by
    intro X1 X2 sK3 sK4
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK3 sK4]
  have l1 : ∀ sK3 sK4 sK5 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ sK1) := by
    intro sK3 sK4 sK5 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 sK1]
  have l2 : ∀ sK3 sK4 sK0 sK5 sK1 : G, (sK3 ◇ sK4) = (sK0 ◇ (sK5 ◇ sK1)) := by
    intro sK3 sK4 sK0 sK5 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK0 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l1 sK3 sK4 sK5 sK1]
  have l3 : ∀ sK3 sK4 sK2 sK0 sK5 sK1 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK0 ◇ (sK5 ◇ sK1))) := by
    intro sK3 sK4 sK2 sK0 sK5 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK2 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l2 sK3 sK4 sK0 sK5 sK1]
  have l4 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK5 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK5 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l3 sK3 sK4 sK2 sK0 sK5 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l4 x y z w u v]

@[equational_result]
theorem Equation42386_implies_Equation41 (G : Type*) [Magma G] (h42386 : Equation42386 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42386 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42386 X2 X3 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42387 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42387 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation42387_implies_Equation41 (G : Type*) [Magma G] (h42387 : Equation42387 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42387 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42387 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42387 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42389 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42389 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK4)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation42389_implies_Equation41 (G : Type*) [Magma G] (h42389 : Equation42389 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42389 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42389 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42390 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42390 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ sK1) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 sK1]
  have l2 : ∀ sK1 sK4 sK0 : G, (sK1 ◇ sK1) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK4 sK0
    conv => enter [1]; rw [h41 sK1 sK4 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK1 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK1]
    conv => enter [1]; rw [l2 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation42390_implies_Equation41 (G : Type*) [Magma G] (h42390 : Equation42390 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42390 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42390 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42391 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42391 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation42391_implies_Equation41 (G : Type*) [Magma G] (h42391 : Equation42391 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42391 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42391 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42392 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42392 G := by
  have l0 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y z w u v]

@[equational_result]
theorem Equation42392_implies_Equation41 (G : Type*) [Magma G] (h42392 : Equation42392 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42392 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42392 X2 X3 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42393 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42393 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation42393_implies_Equation41 (G : Type*) [Magma G] (h42393 : Equation42393 G) : Equation41 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h42393 X0 X2 X0 X0 X0]
    conv => enter [1]; rw [← h42393 X0 X1 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42393 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42395 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42395 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK4)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation42395_implies_Equation41 (G : Type*) [Magma G] (h42395 : Equation42395 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42395 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42395 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42396 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42396 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation42396_implies_Equation41 (G : Type*) [Magma G] (h42396 : Equation42396 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42396 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42396 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42397 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42397 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK0]
  have l2 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ sK0) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [h41 sK0 sK4 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK1 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation42397_implies_Equation41 (G : Type*) [Magma G] (h42397 : Equation42397 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42397 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h42397 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42398 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42398 G := by
  have l0 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y z w u v]

@[equational_result]
theorem Equation42398_implies_Equation41 (G : Type*) [Magma G] (h42398 : Equation42398 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42398 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42398 X2 X3 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42399 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42399 G := by
  have l0 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3)))]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y z w u v]

@[equational_result]
theorem Equation42399_implies_Equation41 (G : Type*) [Magma G] (h42399 : Equation42399 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42399 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42399 X0 X2 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42399 X0 X1 sK0 X0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42401 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42401 G := by
  have l0 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK5)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK5)))]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y z w u v]

@[equational_result]
theorem Equation42401_implies_Equation41 (G : Type*) [Magma G] (h42401 : Equation42401 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42401 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42401 X2 X3 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42402 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42402 G := by
  have l0 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y z w u v]

@[equational_result]
theorem Equation42402_implies_Equation41 (G : Type*) [Magma G] (h42402 : Equation42402 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42402 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42402 X2 X3 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42403 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42403 G := by
  have l0 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y z w u v]

@[equational_result]
theorem Equation42403_implies_Equation41 (G : Type*) [Magma G] (h42403 : Equation42403 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42403 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42403 X2 X3 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

end Semigroup5
