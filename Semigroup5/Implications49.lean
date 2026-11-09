import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54215_implies_Equation54186 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation54186 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54215 X0 sK1 sK1]
  have l1 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l2 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 X0 X1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l5 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [← h54215 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l7 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l5 sK1 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l9 : ∀ sK2 sK1 X1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1]; rw [← l7 X1 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l9 sK2 sK1 sK0 sK0]
  have l12 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4512_54215_implies_Equation54240 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation54240 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54215 X0 sK1 sK1]
  have l1 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 X0 X1]
  have l3 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [← h54215 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l5 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l3 sK1 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l5 X1 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_54215_implies_Equation54162 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation54162 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54215 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54215 X0 X1 X0]
    conv => enter [1]; rw [← h54215 X3 X1 X0]
  have l2 : ∀ X2 X0 X3 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ X3)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h4512 X2 (X0 ◇ X0) X3]
    conv => enter [1, 1]; rw [h54215 X2 X0 X1]
  have l3 : ∀ X2 X0 X3 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ X3)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l2 X2 X0 X3 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) X3]
  have l4 : ∀ X2 X0 X3 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l3 X2 X0 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l5 : ∀ X2 X0 X3 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l4 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) = (X2 ◇ (X0 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l5 X2 X0 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l1 x y (((x ◇ y) ◇ (x ◇ y)) ◇ ((x ◇ y) ◇ (x ◇ y)))]
  conv => enter [1]; rw [← h4512 ((x ◇ y) ◇ (x ◇ y)) ((x ◇ y) ◇ (x ◇ y)) (y ◇ y)]
  conv => enter [1, 2]; rw [h54215 ((x ◇ y) ◇ (x ◇ y)) y x]
  conv => enter [1]; rw [← h4512 (x ◇ y) (x ◇ y) (y ◇ (y ◇ (x ◇ y)))]
  conv => enter [1]; rw [← l0 x (x ◇ y) y y]
  conv => enter [1, 2]; rw [← h4512 x y (x ◇ y)]
  conv => enter [1]; rw [l6 x y y x]

theorem Equation4512_54215_implies_Equation54199 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation54199 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54215 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54215 X0 X1 X0]
    conv => enter [1]; rw [← h54215 X3 X1 X0]
  have l2 : ∀ X2 X0 X3 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ X3)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h4512 X2 (X0 ◇ X0) X3]
    conv => enter [1, 1]; rw [h54215 X2 X0 X1]
  have l3 : ∀ X2 X0 X3 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ X3)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l2 X2 X0 X3 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) X3]
  have l4 : ∀ X2 X0 X3 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l3 X2 X0 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l5 : ∀ X2 X0 X3 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l4 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) = (X2 ◇ (X0 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l5 X2 X0 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X1)]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 (X3 ◇ X1) X3]
    conv => enter [1]; rw [← l7 X2 (X3 ◇ X1) X1 X1]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ (X3 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X3 X1 (X3 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l9 x y x x]
  conv => enter [1, 2]; rw [h4512 x y (x ◇ y)]
  conv => enter [1]; rw [l7 x (x ◇ y) x x]
  conv => enter [1]; rw [l6 x (x ◇ y) y y]

theorem Equation4512_54215_implies_Equation54202 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation54202 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54215 X0 sK0 sK0]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [← h54215 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l5 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK1 sK0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l2 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l5 X1 sK1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y y]

theorem Equation4512_54215_implies_Equation54209 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation54209 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h54215 X0 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x x]

theorem Equation4512_54215_implies_Equation54165 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation54165 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54215 X0 sK1 sK1]
  have l1 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l0 sK1 X0]
    conv => enter [1]; rw [l0 sK1 X1]
  have l2 : ∀ X0 sK1 X1 X2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l3 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l2 X0 sK1 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK1 sK0]
  have l4 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l3 sK0 sK1 X1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y x]

theorem Equation4512_54215_implies_Equation54175 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation54175 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54215 X0 sK1 sK1]
  have l3 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l3 sK1 X0 X1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l2 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l8 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [← h54215 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l9 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [← l1 sK1 (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l8 sK1 X0 X1 sK0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l11 : ∀ sK1 X1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 sK0
    conv => enter [1, 2]; rw [l4 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [l9 sK1 sK1 X1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l13 : ∀ sK1 X1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l11 sK1 X1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1 sK1 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation4512_54215_implies_Equation53850 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation53850 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54215 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54215 X0 X1 X0]
    conv => enter [1]; rw [← h54215 X3 X1 X0]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x z z]
  conv => enter [1]; rw [h4512 x x (z ◇ (z ◇ x))]
  conv => enter [1]; rw [l5 (x ◇ x) z x y]

theorem Equation4512_54215_implies_Equation53842 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation53842 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54215 X0 sK0 sK0]
  have l1 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l2 sK2 sK0 X0 sK2]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_54215_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation53809 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h54215 X0 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y x]

theorem Equation4512_54215_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation53812 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54215 X0 sK0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_54215_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation53832 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54215 X0 sK0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0 sK1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_54215_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation53815 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54215 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54215 X0 X1 X0]
    conv => enter [1]; rw [← h54215 X3 X1 X0]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
  intro x y
  conv => enter [1]; rw [l0 x x y y]
  conv => enter [1]; rw [h4512 x x (y ◇ (y ◇ x))]
  conv => enter [1]; rw [l5 (x ◇ x) y x x]

theorem Equation4512_54215_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation53835 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54215 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54215 X0 X1 X0]
    conv => enter [1]; rw [← h54215 X3 X1 X0]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
  intro x y
  conv => enter [1]; rw [l0 x x y y]
  conv => enter [1]; rw [h4512 x x (y ◇ (y ◇ x))]
  conv => enter [1]; rw [l5 (x ◇ x) y x y]

theorem Equation4512_54215_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54215 : Equation54215 G) : Equation53822 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54215 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X1]
  have l2 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_53879_implies_Equation53874 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53874 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53879 X0 X1 X0]
    conv => enter [1]; rw [← h53879 X0 X2 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK2]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← l3 sK1 sK2 X0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l6 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53879 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 (X0 ◇ X0)]
  have l7 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53879 X0 X1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK2 (X0 ◇ X0)]
  have l8 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l6 X0 X0 sK1 sK2]
    conv => enter [1]; rw [l7 X0 X0 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_53879_implies_Equation53888 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53888 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53879 X0 X1 X0]
    conv => enter [1]; rw [← h53879 X0 X2 X0]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l0 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ sK1) X0]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l2 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l4 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0]
    conv => enter [1]; rw [← l3 sK2 sK1 X0]
  have l5 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l4 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l6 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h53879 X0 X1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l4 sK2 sK1 (X0 ◇ X0)]
  have l7 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1]; rw [h53879 X0 X1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l5 sK0 sK2 sK1 (X0 ◇ X0)]
  have l8 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [← l6 X0 X0 sK2 sK1]
    conv => enter [1]; rw [l7 X0 X0 sK0 sK2 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l8 sK0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation53879_implies_Equation4268 (G : Type*) [Magma G] (h53879 : Equation53879 G) : Equation4268 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53879 sK0 sK1 sK0]
    conv => enter [1]; rw [← h53879 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation53879_implies_Equation53864 (G : Type*) [Magma G] (h53879 : Equation53879 G) : Equation53864 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53879 X0 X1 X0]
    conv => enter [1]; rw [← h53879 X0 X2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y (y ◇ z)]

@[equational_result]
theorem Equation53879_implies_Equation53866 (G : Type*) [Magma G] (h53879 : Equation53879 G) : Equation53866 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53879 X0 X1 X0]
    conv => enter [1]; rw [← h53879 X0 X2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y (z ◇ y)]

theorem Equation4512_53879_implies_Equation53873 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53873 G := by
  have l0 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53879 X0 X1 X0]
    conv => enter [1]; rw [← h53879 X0 X2 X0]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h53879 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l1 sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53879 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) = (sK1 ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [h53879 sK1 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (X0 ◇ (sK1 ◇ sK1)) X1]
  have l6 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l5 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l7 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK1 X1 X2 X0 : G, (sK1 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2)) = ((sK1 ◇ (sK1 ◇ X0)) ◇ X2) := by
    intro sK1 X1 X2 X0
    conv => enter [1]; rw [h4512 sK1 (X1 ◇ (sK1 ◇ sK1)) X2]
    conv => enter [1, 1]; rw [← h53879 sK1 X0 X1]
  have l9 : ∀ sK1 X1 X2 X0 : G, (sK1 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2)) = (sK1 ◇ ((sK1 ◇ X0) ◇ X2)) := by
    intro sK1 X1 X2 X0
    conv => enter [1]; rw [l8 sK1 X1 X2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ X0) X2]
  have l10 : ∀ sK1 X1 X2 X0 : G, (sK1 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2)) = (sK1 ◇ (sK1 ◇ (X0 ◇ X2))) := by
    intro sK1 X1 X2 X0
    conv => enter [1]; rw [l9 sK1 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X2]
  have l11 : ∀ sK1 X1 X2 X0 : G, (sK1 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X2)) := by
    intro sK1 X1 X2 X0
    conv => enter [1]; rw [l10 sK1 X1 X2 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ X2)]
  have l12 : ∀ sK1 X0 X2 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X2)) = (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2))) := by
    intro sK1 X0 X2 X1
    conv => enter [1]; rw [← l11 sK1 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK1 ◇ sK1) X2]
  have l13 : ∀ sK1 X0 X2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X2)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l12 sK1 X0 X2 sK1]
    conv => enter [1]; rw [← l6 sK1 X2 sK1]
  have l14 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h53879 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2, 2]; rw [← l4 sK1]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l14 sK1 X0 sK1]
    conv => enter [1]; rw [l13 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [← l15 sK1 X0]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l16 sK1 X0]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ sK1) X0]
  have l18 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h53879 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l17 sK1 (X0 ◇ X0)]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l18 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation4512_53879_implies_Equation53872 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53872 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53879 X0 X1 X0]
    conv => enter [1]; rw [← h53879 X0 X2 X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [← l3 sK1 sK0 X0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l6 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h53879 X0 X1 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK1 sK0 (X0 ◇ X0)]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53879 X0 X1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 (X0 ◇ X0)]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l6 X0 X0 sK1 sK0]
    conv => enter [1]; rw [l7 X0 X0 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_53879_implies_Equation53862 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53862 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53879 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_53879_implies_Equation53869 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53869 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53879 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 x y y]

@[equational_result]
theorem Equation53879_implies_Equation53863 (G : Type*) [Magma G] (h53879 : Equation53879 G) : Equation53863 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53879 X0 X1 X0]
    conv => enter [1]; rw [← h53879 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (y ◇ y)]

@[equational_result]
theorem Equation53879_implies_Equation53860 (G : Type*) [Magma G] (h53879 : Equation53879 G) : Equation53860 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53879 X0 X1 X0]
    conv => enter [1]; rw [← h53879 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ y)]

theorem Equation4512_53879_implies_Equation53817 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53817 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h53879 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h53879 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h53879 sK0 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53879 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53879 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [h53879 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l5 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h53879 sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53879 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK0 (X0 ◇ X0)]
  have l10 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK0 ◇ X0)) ◇ X2) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h4512 sK0 (X1 ◇ (sK0 ◇ sK0)) X2]
    conv => enter [1, 1]; rw [← h53879 sK0 X0 X1]
  have l11 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) = (sK0 ◇ ((sK0 ◇ X0) ◇ X2)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l10 sK0 X1 X2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ X0) X2]
  have l12 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) = (sK0 ◇ (sK0 ◇ (X0 ◇ X2))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l11 sK0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X2]
  have l13 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l12 sK0 X1 X2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X2)]
  have l14 : ∀ sK0 X0 X2 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [← l13 sK0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l15 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l14 sK0 X0 X2 sK0]
    conv => enter [1]; rw [← l6 sK0 X2 sK0]
  have l16 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l8 sK0 X2]
    conv => enter [1]; rw [← l15 sK0 X0 X2]
  have l17 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X0 sK1 sK2]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 X0 sK0 sK0]
  have l19 : ∀ sK0 X0 X2 X1 : G, ((sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro sK0 X0 X2 X1
    conv => enter [1, 1]; rw [l1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X1 X2]
  have l20 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l16 sK0 sK0 X2]
    conv => enter [1]; rw [← l19 sK0 X0 X2 sK0]
  have l21 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l20 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X2]
  have l22 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l21 sK0 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l18 sK0 sK0]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

@[equational_result]
theorem Equation53879_implies_Equation53811 (G : Type*) [Magma G] (h53879 : Equation53879 G) : Equation53811 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53879 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53879 sK0 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation53879_implies_Equation53809 (G : Type*) [Magma G] (h53879 : Equation53879 G) : Equation53809 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53879 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53879 sK0 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation53879_implies_Equation53812 (G : Type*) [Magma G] (h53879 : Equation53879 G) : Equation53812 G := by
  intro x y
  conv => enter [1]; rw [h53879 x x y]

theorem Equation4512_53879_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53879 sK0 X0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53879 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X0 sK1]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 X0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_53879_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53815 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h53879 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h53879 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53879 sK0 X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53879 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53879 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h53879 sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53879 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l6 sK0 (X0 ◇ X0)]
  have l8 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X0 sK1]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0 sK0]
  have l10 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) = (((sK0 ◇ sK0) ◇ X0) ◇ X2) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h4512 sK0 (X1 ◇ (sK0 ◇ sK0)) X2]
    conv => enter [1, 1]; rw [l1 sK0 X1 X0]
  have l11 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l10 sK0 X1 X2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X2]
  have l12 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l11 sK0 X1 X2 sK0]
  have l13 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l12 sK0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l14 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l13 sK0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l9 sK0 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation4512_53879_implies_Equation53816 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53816 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h53879 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53879 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53879 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [← h53879 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l1 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [← l5 sK1 X0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l6 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53879 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_53879_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53879 : Equation53879 G) : Equation53808 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h53879 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53879 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h53879 sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_54275_implies_Equation4280 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation4280 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54275 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (X1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK0]
  have l12 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h54275 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ sK2)]
  have l13 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l9 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l14 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l15 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l14 sK2 X1 X0]
    conv => enter [1]; rw [l9 sK2 (X1 ◇ sK2)]
  have l16 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l13 sK2 X1 X0]
    conv => enter [1, 2]; rw [l9 sK2 (X1 ◇ sK2)]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l11 sK0 X1 X0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ sK0)]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l10 X0 sK0]
  have l19 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54275 X0 sK2 sK2]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l21 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l16 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54275 X0 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h54275 X1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l19 sK2 X0]
  have l26 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l19 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l27 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l19 sK2 sK1]
    conv => enter [1]; rw [l26 sK2 X0 X1]
  have l28 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l25 X1 X0 sK2]
    conv => enter [1]; rw [l21 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l29 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l28 X1 X0 sK2]
  have l30 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [← l9 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l29 sK2 X1 X0]
  have l31 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [← l30 sK2 X1 X0]
    conv => enter [1]; rw [l9 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l32 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l31 X1 X0 sK2]
    conv => enter [1]; rw [l15 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l33 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l32 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l34 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l33 X1 X0 sK2]
    conv => enter [1, 2]; rw [l9 sK2 (sK2 ◇ sK2)]
  have l35 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l34 X1 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l36 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l35 X1 X0 sK2]
    conv => enter [1]; rw [l12 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2]
  have l37 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l36 X1 X0 sK2]
  have l38 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l9 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l37 sK2 X1 X0]
  have l39 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l27 sK1 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l38 sK2 X1 X0]
  have l40 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1, 2, 2]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← h54275 X1 X0 (sK0 ◇ sK0)]
  have l41 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l39 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1 sK1]
  have l42 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l41 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l43 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l42 sK1 sK2 sK0]
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l44 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l43 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK0 sK0]
  have l45 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l46 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l45 sK1 sK2 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l47 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l46 sK1 sK2 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l47 x x y z]

theorem Equation4512_54275_implies_Equation54167 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation54167 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h54275 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ sK2)]
  have l2 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l0 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l3 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l4 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l3 sK2 X1 X0]
    conv => enter [1]; rw [l0 sK2 (X1 ◇ sK2)]
  have l5 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l2 sK2 X1 X0]
    conv => enter [1, 2]; rw [l0 sK2 (X1 ◇ sK2)]
  have l6 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54275 X0 sK2 sK2]
  have l7 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l5 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))]
  have l8 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h54275 X1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l6 sK2 X0]
  have l9 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l6 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l10 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l8 X1 X0 sK2]
    conv => enter [1]; rw [l7 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l11 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l10 X1 X0 sK2]
  have l12 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [← l0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l11 sK2 X1 X0]
  have l13 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [← l12 sK2 X1 X0]
    conv => enter [1]; rw [l0 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l14 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l13 X1 X0 sK2]
    conv => enter [1]; rw [l4 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l15 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l14 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l16 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l15 X1 X0 sK2]
    conv => enter [1, 2]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l17 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l16 X1 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l18 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l17 X1 X0 sK2]
    conv => enter [1]; rw [l1 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2]
  have l19 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l18 X1 X0 sK2]
  have l20 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l19 sK2 X1 X0]
  have l21 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l9 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l20 sK2 X1 X0]
  have l22 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h54275 (X0 ◇ X1) sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l23 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l22 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l21 sK2 sK0 sK1]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l21 sK2 sK0 (sK2 ◇ sK2)]
  have l25 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 X0]
  intro x y z
  conv => enter [1]; rw [← l25 x z x y]

theorem Equation4512_54275_implies_Equation54215 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation54215 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54275 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK1 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l6 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [← l3 sK0 sK2]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l3 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 X0]
  have l8 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 sK2]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK2]
    conv => enter [1]; rw [← h54275 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 sK2]
  have l10 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1, 1]; rw [← l3 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l11 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← l9 sK0 sK2 X0]
    conv => enter [1]; rw [← l10 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l6 sK2 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l8 sK1 sK0 sK2]
  have l13 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l12 sK2 sK0 sK2]
    conv => enter [1]; rw [l11 sK2 sK2 sK0]
  have l14 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1, 2, 2]; rw [l7 sK2 sK0 X0]
    conv => enter [1]; rw [← h54275 X1 X0 (sK0 ◇ sK0)]
  have l15 : ∀ X1 X0 sK2 sK0 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK2 sK0
    conv => enter [1]; rw [← l14 sK0 sK2 X1 X0]
    conv => enter [1]; rw [← l10 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK2 sK0 X1 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l13 sK2 sK0]
    conv => enter [1]; rw [← l15 X1 X0 sK2 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK1)]
  have l19 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l16 sK2 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK1 sK0]
  have l21 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l19 sK2 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l21 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l22 y z x]

theorem Equation4512_54275_implies_Equation54181 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation54181 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK2 ◇ sK2)]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK2)) X0]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l4 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l5 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h54275 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ sK2)]
  have l6 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l3 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l7 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l8 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l7 sK2 X1 X0]
    conv => enter [1]; rw [l3 sK2 (X1 ◇ sK2)]
  have l9 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l6 sK2 X1 X0]
    conv => enter [1, 2]; rw [l3 sK2 (X1 ◇ sK2)]
  have l10 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54275 X0 sK2 sK2]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l12 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l9 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))]
  have l13 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l10 sK2 X0]
    conv => enter [1]; rw [l10 sK2 X1]
  have l14 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h54275 X1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l10 sK2 X0]
  have l15 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l10 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l16 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l14 X1 X0 sK2]
    conv => enter [1]; rw [l12 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l17 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l16 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l18 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l17 X1 X0 sK2]
    conv => enter [1, 2]; rw [l3 sK2 (sK2 ◇ sK2)]
  have l19 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l18 X1 X0 sK2]
    conv => enter [1]; rw [l3 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l20 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l19 X1 X0 sK2]
    conv => enter [1]; rw [l8 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l21 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l20 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l22 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l21 X1 X0 sK2]
    conv => enter [1, 2]; rw [l3 sK2 (sK2 ◇ sK2)]
  have l23 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l22 X1 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l24 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l23 X1 X0 sK2]
    conv => enter [1]; rw [l5 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2]
  have l25 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l24 X1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l26 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l25 X1 X0 sK2]
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ sK2)]
  have l27 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l26 X1 X0 sK2]
    conv => enter [1]; rw [← l15 sK2 sK2 (sK2 ◇ sK2)]
  have l28 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l29 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l11 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 X0 X1]
  have l30 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l11 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 X0]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l30 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l30 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l30 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l2 sK0 sK2 (sK0 ◇ sK0)]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l33 sK0 sK1 sK1]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ sK0) sK2]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l36 sK0 sK1 sK2]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ X0 sK2 X1 X2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 X2
    conv => enter [1]; rw [l13 X0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK2)]
  have l40 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1, 2]; rw [l13 sK2 sK2 X0]
  have l41 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l40 sK0 sK2 sK0]
    conv => enter [1]; rw [← l15 sK2 sK0 sK0]
  have l42 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [l39 X0 sK2 X1 X0]
    conv => enter [1, 2]; rw [l13 X0 sK2 sK0]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← l41 sK0 sK2]
  have l44 : ∀ sK0 sK2 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l42 sK0 sK2 X1 sK0]
  have l45 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
  have l46 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l13 sK0 sK2 sK2]
    conv => enter [1]; rw [← l4 sK0 sK2]
  have l47 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l45 sK1 sK0 sK2]
    conv => enter [1]; rw [← l46 sK0 sK2]
  have l48 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l47 sK1 sK0 sK2]
    conv => enter [1]; rw [← l44 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l48 z x y]
  conv => enter [1]; rw [l35 z x]

theorem Equation4512_54275_implies_Equation54211 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation54211 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X1]
  have l4 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l3 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l5 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l4 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l3 X0 sK0 sK1]
  have l6 : ∀ sK1 sK0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l5 sK1 sK0 X1 sK1]
  have l7 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [← h54275 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l3 (sK0 ◇ sK0) sK0 sK1]
  have l8 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l3 X0 sK0 sK1]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0 sK1]
    conv => enter [1]; rw [← l7 X0 sK0 sK1 sK1]
  have l10 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l8 X0 sK0 X0 sK1]
  have l11 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [l6 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ sK0)) X1]
  have l12 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) := by
    intro sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [l10 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) X1]
  have l13 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l10 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l11 sK1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l16 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l13 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l11 sK1 sK0 (X0 ◇ X1) X1]
  have l17 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l12 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) X0 X1]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  have l19 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l16 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← l11 sK1 sK0 (X0 ◇ X1) X0]
  have l20 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l11 sK1 sK0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l17 sK1 sK0 X1 X0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l22 : ∀ sK1 sK0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l19 sK1 sK0 sK1 X1]
    conv => enter [1]; rw [l20 sK1 sK0 sK1 X1]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l25 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l26 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l22 sK1 sK0 X0]
    conv => enter [1]; rw [l25 sK1 sK0 X0]
  have l27 : ∀ X0 sK0 X1 sK1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1)) := by
    intro X0 sK0 X1 sK1
    conv => enter [1, 1]; rw [h54275 X0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X1]
  have l28 : ∀ X0 sK0 X1 sK1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l27 X0 sK0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l29 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l26 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1)]
    conv => enter [1]; rw [← l28 X0 sK0 X1 sK1]
  have l30 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l29 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l31 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l30 sK1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l31 x y y]

theorem Equation4512_54275_implies_Equation54179 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation54179 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h54275 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ sK2)]
  have l3 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l1 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l4 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l5 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l4 sK2 X1 X0]
    conv => enter [1]; rw [l1 sK2 (X1 ◇ sK2)]
  have l6 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l3 sK2 X1 X0]
    conv => enter [1, 2]; rw [l1 sK2 (X1 ◇ sK2)]
  have l7 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54275 X0 sK2 sK2]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54275 X0 sK1 sK1]
  have l9 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l6 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))]
  have l10 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l7 sK2 X0]
    conv => enter [1]; rw [l7 sK2 X1]
  have l11 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h54275 X1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l7 sK2 X0]
  have l12 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l7 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l13 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l11 X1 X0 sK2]
    conv => enter [1]; rw [l9 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l14 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l13 X1 X0 sK2]
  have l15 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [← l1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l14 sK2 X1 X0]
  have l16 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [← l15 sK2 X1 X0]
    conv => enter [1]; rw [l1 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l17 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l16 X1 X0 sK2]
    conv => enter [1]; rw [l5 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l18 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l17 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l19 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l18 X1 X0 sK2]
    conv => enter [1, 2]; rw [l1 sK2 (sK2 ◇ sK2)]
  have l20 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l19 X1 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l21 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l20 X1 X0 sK2]
    conv => enter [1]; rw [l2 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2]
  have l22 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l21 X1 X0 sK2]
  have l23 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l22 sK2 X1 X0]
  have l24 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l12 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l23 sK2 X1 X0]
  have l25 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l8 sK1 X0]
    conv => enter [1]; rw [l8 sK1 X1]
  have l26 : ∀ X0 sK2 X1 X2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 X2
    conv => enter [1]; rw [l10 X0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK2)]
  have l27 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l10 (sK1 ◇ sK1) sK2 X0]
  have l28 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l26 X0 sK2 X1 X0]
    conv => enter [1, 2]; rw [l10 X0 sK2 sK1]
  have l29 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l28 sK1 sK2 X1 sK1]
  have l30 : ∀ X0 sK1 X1 X2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 X2
    conv => enter [1]; rw [l25 X0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l31 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l30 X0 sK1 X1 X0]
    conv => enter [1, 2]; rw [l25 X0 sK1 sK0]
  have l32 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l31 sK0 sK1 X1 sK0]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l34 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l24 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l33 sK1 sK0]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l34 sK2 sK1 sK0]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [← l27 sK1 sK2 (sK2 ◇ sK2)]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 sK2]
    conv => enter [1]; rw [← l29 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l37 x y z]
  conv => enter [1]; rw [l29 y z x]

theorem Equation4512_54275_implies_Equation54176 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation54176 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK2]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54275 X0 sK1 sK1]
  have l2 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l1 sK1 X0]
    conv => enter [1]; rw [l1 sK1 X1]
  have l3 : ∀ X0 sK1 X1 X2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 X2
    conv => enter [1]; rw [l2 X0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l4 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l3 X0 sK1 X1 X0]
    conv => enter [1, 2]; rw [l2 X0 sK1 sK0]
  have l5 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l4 sK0 sK1 X1 sK0]
  have l6 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [← h54275 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK1) sK1 sK0]
  have l7 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 1]; rw [l2 X0 sK1 sK0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1]; rw [← l6 X0 sK1 sK0 sK0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l7 X0 sK1 X0 sK0]
  have l10 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l11 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2)]
  have l12 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l11 sK1 sK0 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_54275_implies_Equation54208 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation54208 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54275 X0 sK1 sK1]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK1 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK0]
  have l7 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h54275 X1 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [← l7 X0 sK0 sK1 sK0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 X0 X0]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 sK0 sK1 X0 X0]
  have l12 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← h54275 (sK0 ◇ (sK1 ◇ sK1)) X1 X0]
    conv => enter [1]; rw [← l11 sK0 sK1 (X1 ◇ X1)]
  have l13 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X1))) = (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [← h54275 X2 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1
    conv => enter [1]; rw [l14 sK0 sK0 sK0]
    conv => enter [1]; rw [← l13 X1 sK0 sK0 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK0]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 X0]
  intro x y
  conv => enter [1]; rw [l17 x y y]
  conv => enter [1]; rw [← l3 y x y]

theorem Equation4512_54275_implies_Equation54171 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation54171 G := by
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
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK0)]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54275 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l6 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h54275 X0 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ sK1)]
  have l7 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (X1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ (X1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK1]
  have l8 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (X1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (X1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK1]
  have l9 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (X1 ◇ X1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l8 sK1 X1 X0]
    conv => enter [1]; rw [l3 sK1 (X1 ◇ sK1)]
  have l10 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l7 sK1 X1 X0]
    conv => enter [1, 2]; rw [l3 sK1 (X1 ◇ sK1)]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54275 X0 sK1 sK1]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l13 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l10 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (X1 ◇ sK1))]
  have l14 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l11 sK1 X0]
    conv => enter [1]; rw [l11 sK1 X1]
  have l15 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h54275 X1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l11 sK1 X0]
  have l16 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l11 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l17 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l15 X1 X0 sK1]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l18 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l17 X1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l19 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l18 X1 X0 sK1]
    conv => enter [1, 2]; rw [l3 sK1 (sK1 ◇ sK1)]
  have l20 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l19 X1 X0 sK1]
    conv => enter [1]; rw [l3 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l21 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l20 X1 X0 sK1]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l22 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l21 X1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l23 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l22 X1 X0 sK1]
    conv => enter [1, 2]; rw [l3 sK1 (sK1 ◇ sK1)]
  have l24 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l23 X1 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l25 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l24 X1 X0 sK1]
    conv => enter [1]; rw [l6 (sK1 ◇ sK1) (sK1 ◇ sK1) sK1]
  have l26 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l25 X1 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l27 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l26 X1 X0 sK1]
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ sK1)]
  have l28 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l27 X1 X0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK1 (sK1 ◇ sK1)]
  have l29 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 (sK1 ◇ sK1)]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l12 sK0 (sK1 ◇ sK1)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l5 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l33 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [l29 sK0 X0 X1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 (sK0 ◇ sK0) sK1]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l38 : ∀ X0 sK1 X1 X2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 X2
    conv => enter [1]; rw [l14 X0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l39 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l38 X0 sK1 X1 X0]
    conv => enter [1, 2]; rw [l14 X0 sK1 sK0]
  have l40 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l39 sK0 sK1 X1 sK0]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ sK1)]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l42 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l43 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1 sK0]
    conv => enter [1]; rw [l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 X0]
  have l49 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l48 sK1 sK0 sK0]
    conv => enter [1]; rw [l40 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l48 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l48 x y y]
  conv => enter [1]; rw [l49 y x x]

@[equational_result]
theorem Equation54275_implies_Equation54164 (G : Type*) [Magma G] (h54275 : Equation54275 G) : Equation54164 G := by
  intro x y
  conv => enter [1]; rw [h54275 x y x]

theorem Equation4512_54275_implies_Equation53824 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53824 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X1]
  have l2 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0 X1]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54275 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK0) sK0 sK0]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l1 X0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l5 X0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1, 2]; rw [l6 X0 sK0 X0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l10 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l8 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)]
  have l11 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK2]
    conv => enter [1]; rw [← l9 sK0 sK2 (sK0 ◇ sK2)]
  have l12 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK2]
  have l13 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l6 X0 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l14 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l12 sK0 sK2]
    conv => enter [1]; rw [l13 sK0 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_54275_implies_Equation53817 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53817 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X1]
  have l2 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0 X1]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54275 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK0) sK0 sK0]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l1 X0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l5 X0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1, 2]; rw [l6 X0 sK0 X0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l10 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h54275 X1 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X1]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l9 sK0 (X0 ◇ X1) X1]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l11 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l15 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l10 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← l9 sK0 (X0 ◇ X1) X0]
  have l17 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l14 sK0 X1 X0]
  have l18 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l15 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l16 sK0 sK0 X1]
    conv => enter [1]; rw [l17 sK0 sK0 X1]
  have l20 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l16 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← l18 X1 X0 sK0]
  have l21 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro sK0 X2 X0 X1
    conv => enter [1, 1]; rw [l20 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l22 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [← l21 sK0 X2 X0 X1]
  have l23 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l22 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l19 sK0 X2]
  intro x y z
  conv => enter [1]; rw [← l23 x y z x]

theorem Equation4512_54275_implies_Equation53830 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53830 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l3 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l7 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l8 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h54275 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ sK2)]
  have l9 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l6 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l10 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l11 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l10 sK2 X1 X0]
    conv => enter [1]; rw [l6 sK2 (X1 ◇ sK2)]
  have l12 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l9 sK2 X1 X0]
    conv => enter [1, 2]; rw [l6 sK2 (X1 ◇ sK2)]
  have l13 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54275 X0 sK2 sK2]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l15 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l12 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))]
  have l16 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l13 sK2 X0]
    conv => enter [1]; rw [l13 sK2 X1]
  have l17 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h54275 X1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l13 sK2 X0]
  have l18 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l13 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l19 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l17 X1 X0 sK2]
    conv => enter [1]; rw [l15 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l20 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l19 X1 X0 sK2]
  have l21 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [← l6 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l20 sK2 X1 X0]
  have l22 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [← l21 sK2 X1 X0]
    conv => enter [1]; rw [l6 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l23 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l22 X1 X0 sK2]
    conv => enter [1]; rw [l11 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l24 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l23 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l25 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l24 X1 X0 sK2]
    conv => enter [1, 2]; rw [l6 sK2 (sK2 ◇ sK2)]
  have l26 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l25 X1 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l27 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l26 X1 X0 sK2]
    conv => enter [1]; rw [l8 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2]
  have l28 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l27 X1 X0 sK2]
  have l29 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l6 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l28 sK2 X1 X0]
  have l30 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l18 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l29 sK2 X1 X0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l14 sK0 X0]
  have l32 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l33 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l32 sK0 X0 X1]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l3 sK0]
    conv => enter [1]; rw [l31 sK0 X0]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l33 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l34 sK0 sK0]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1]; rw [← l30 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l38 : ∀ X0 sK2 X1 X2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 X2
    conv => enter [1]; rw [l16 X0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK2)]
  have l39 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK2]
    conv => enter [1, 2]; rw [l16 sK2 sK2 X0]
  have l40 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l39 sK0 sK2 sK0]
    conv => enter [1]; rw [← l18 sK2 sK0 sK0]
  have l41 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [l38 X0 sK2 X1 X0]
    conv => enter [1, 2]; rw [l16 X0 sK2 sK0]
  have l42 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l37 sK0 sK2]
    conv => enter [1]; rw [← l40 sK0 sK2]
  have l43 : ∀ sK0 sK2 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l41 sK0 sK2 X1 sK0]
  have l44 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l16 sK0 sK2 sK2]
    conv => enter [1]; rw [← l7 sK0 sK2]
  have l45 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l16 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l46 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l45 sK1 sK0 sK2]
    conv => enter [1]; rw [← l13 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l47 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0 sK2]
    conv => enter [1]; rw [← l44 sK0 sK2]
  have l48 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l46 sK1 sK0 sK2]
    conv => enter [1]; rw [← l37 sK0 sK2]
  have l49 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l43 sK0 sK2 sK0]
    conv => enter [1]; rw [← l47 sK0 sK2]
  have l50 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l49 sK0 sK2]
    conv => enter [1]; rw [← l48 sK1 sK0 sK2]
  have l51 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54275 X0 sK0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l43 sK0 sK2 (sK2 ◇ sK2)]
  have l52 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l43 sK0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l51 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l52 x z x]
  conv => enter [1]; rw [l50 x z y]

theorem Equation4512_54275_implies_Equation53820 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53820 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54275 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (X1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK0]
  have l12 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h54275 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ sK2)]
  have l13 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l9 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l14 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l15 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l14 sK2 X1 X0]
    conv => enter [1]; rw [l9 sK2 (X1 ◇ sK2)]
  have l16 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l13 sK2 X1 X0]
    conv => enter [1, 2]; rw [l9 sK2 (X1 ◇ sK2)]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l11 sK0 X1 X0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ sK0)]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l10 X0 sK0]
  have l19 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54275 X0 sK2 sK2]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l21 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l16 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54275 X0 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h54275 X1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l19 sK2 X0]
  have l26 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l19 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l27 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l19 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l28 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l19 sK2 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l27 sK0 sK2 sK2]
  have l29 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l19 sK2 sK1]
    conv => enter [1]; rw [l26 sK2 X0 X1]
  have l30 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l25 X1 X0 sK2]
    conv => enter [1]; rw [l21 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l19 sK2 sK1]
    conv => enter [1]; rw [l28 sK2 sK0]
    conv => enter [1, 2]; rw [l19 sK2 sK1]
  have l32 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l30 X1 X0 sK2]
  have l33 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [← l9 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l32 sK2 X1 X0]
  have l34 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [← l33 sK2 X1 X0]
    conv => enter [1]; rw [l9 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l35 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l34 X1 X0 sK2]
    conv => enter [1]; rw [l15 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l36 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l35 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l37 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l36 X1 X0 sK2]
    conv => enter [1, 2]; rw [l9 sK2 (sK2 ◇ sK2)]
  have l38 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l37 X1 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l39 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l38 X1 X0 sK2]
    conv => enter [1]; rw [l12 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2]
  have l40 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l39 X1 X0 sK2]
  have l41 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l9 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l40 sK2 X1 X0]
  have l42 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l29 sK1 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l41 sK2 X1 X0]
  have l43 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1, 2, 2]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← h54275 X1 X0 (sK0 ◇ sK0)]
  have l44 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l42 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1 sK1]
  have l45 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l46 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l45 sK1 sK2 sK0]
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l47 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l46 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK0 sK0]
  have l48 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l47 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l49 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l48 sK1 sK2 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l50 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l49 sK1 sK2 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l50 x x y z]
  conv => enter [1]; rw [l31 y z x]

theorem Equation4512_54275_implies_Equation53826 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53826 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54275 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l9 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h54275 X0 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ sK1)]
  have l10 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (X1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l5 sK1 (sK1 ◇ (X1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK1]
  have l11 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (X1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (X1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK1]
  have l12 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (X1 ◇ X1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l11 sK1 X1 X0]
    conv => enter [1]; rw [l5 sK1 (X1 ◇ sK1)]
  have l13 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l10 sK1 X1 X0]
    conv => enter [1, 2]; rw [l5 sK1 (X1 ◇ sK1)]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l8 X0 sK0]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54275 X0 sK1 sK1]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l17 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l13 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (X1 ◇ sK1))]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54275 X0 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l15 sK1 X0]
    conv => enter [1]; rw [l15 sK1 X1]
  have l22 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h54275 X1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l15 sK1 X0]
  have l23 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l15 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l24 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l22 X1 X0 sK1]
    conv => enter [1]; rw [l17 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l25 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l24 X1 X0 sK1]
  have l26 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1, 2]; rw [← l5 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l25 sK1 X1 X0]
  have l27 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [← l26 sK1 X1 X0]
    conv => enter [1]; rw [l5 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l28 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l27 X1 X0 sK1]
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l29 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l28 X1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l30 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l29 X1 X0 sK1]
    conv => enter [1, 2]; rw [l5 sK1 (sK1 ◇ sK1)]
  have l31 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l30 X1 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l32 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l31 X1 X0 sK1]
    conv => enter [1]; rw [l9 (sK1 ◇ sK1) (sK1 ◇ sK1) sK1]
  have l33 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l32 X1 X0 sK1]
  have l34 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l5 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l33 sK1 X1 X0]
  have l35 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l23 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l34 sK1 X1 X0]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l16 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l36 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l37 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l38 sK0 sK1]
  have l40 : ∀ X0 sK1 X1 X2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 X2
    conv => enter [1]; rw [l21 X0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l21 sK1 sK1 X0]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1 sK0]
    conv => enter [1]; rw [← l23 sK1 sK0 sK0]
  have l43 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l40 X0 sK1 X1 X0]
    conv => enter [1, 2]; rw [l21 X0 sK1 sK0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1]
  have l45 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l43 sK0 sK1 X1 sK0]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1]
    conv => enter [1, 2]; rw [l21 sK1 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1, 2]; rw [← l44 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l50 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l50 x y x]
  conv => enter [1]; rw [l45 x y y]

@[equational_result]
theorem Equation54275_implies_Equation53833 (G : Type*) [Magma G] (h54275 : Equation54275 G) : Equation53833 G := by
  intro x y
  conv => enter [1]; rw [h54275 x x y]

theorem Equation4512_54275_implies_Equation53840 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53840 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54275 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l8 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h54275 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ sK2)]
  have l9 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l5 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l10 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ (X1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK2]
  have l11 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l10 sK2 X1 X0]
    conv => enter [1]; rw [l5 sK2 (X1 ◇ sK2)]
  have l12 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l9 sK2 X1 X0]
    conv => enter [1, 2]; rw [l5 sK2 (X1 ◇ sK2)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l7 X0 sK0]
  have l14 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54275 X0 sK2 sK2]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l16 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l12 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (X1 ◇ sK2))]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54275 X0 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← l14 sK2 X0]
    conv => enter [1]; rw [l14 sK2 X1]
  have l21 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h54275 X1 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l14 sK2 X0]
  have l22 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l14 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l23 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l21 X1 X0 sK2]
    conv => enter [1]; rw [l16 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l24 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l23 X1 X0 sK2]
  have l25 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [← l5 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l24 sK2 X1 X0]
  have l26 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [← l25 sK2 X1 X0]
    conv => enter [1]; rw [l5 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l27 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l26 X1 X0 sK2]
    conv => enter [1]; rw [l11 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l28 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l27 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l29 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l28 X1 X0 sK2]
    conv => enter [1, 2]; rw [l5 sK2 (sK2 ◇ sK2)]
  have l30 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l29 X1 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l31 : ∀ X1 X0 sK2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l30 X1 X0 sK2]
    conv => enter [1]; rw [l8 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2]
  have l32 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [← l31 X1 X0 sK2]
  have l33 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l5 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l32 sK2 X1 X0]
  have l34 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l22 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l33 sK2 X1 X0]
  have l35 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l15 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (sK0 ◇ sK0)]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l35 sK1 sK0 sK0]
  have l37 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l36 sK0 sK0]
    conv => enter [1]; rw [← l34 sK2 sK0 (sK0 ◇ sK0)]
  have l38 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l37 sK0 sK2]
  have l39 : ∀ X0 sK2 X1 X2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 X2
    conv => enter [1]; rw [l20 X0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK2)]
  have l40 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1, 2]; rw [l20 sK2 sK2 X0]
  have l41 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l40 sK1 sK2 sK1]
    conv => enter [1]; rw [← l22 sK2 sK1 sK1]
  have l42 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l39 X0 sK2 X1 X0]
    conv => enter [1, 2]; rw [l20 X0 sK2 sK1]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK2]
    conv => enter [1]; rw [← l41 sK1 sK2]
  have l44 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l42 sK1 sK2 X1 sK1]
  have l45 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l20 sK1 sK2 sK2]
    conv => enter [1]; rw [← l6 sK1 sK2]
  have l46 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l45 sK1 sK2]
    conv => enter [1]; rw [← l43 sK0 sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l46 sK1 sK2 sK0]
  have l48 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l44 sK1 sK2 sK1]
  have l49 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l48 sK0 sK1 sK2]
  have l50 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l49 sK1 sK2 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l50 x x y z]
  conv => enter [1]; rw [l44 y z y]

theorem Equation4512_54275_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l10 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l10 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l14 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1 sK1]
  have l18 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h54275 X0 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ sK1)]
  have l19 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (X1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l13 sK1 (sK1 ◇ (X1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK1]
  have l20 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (X1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (X1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK1]
  have l21 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (X1 ◇ X1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l20 sK1 X1 X0]
    conv => enter [1]; rw [l13 sK1 (X1 ◇ sK1)]
  have l22 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l19 sK1 X1 X0]
    conv => enter [1, 2]; rw [l13 sK1 (X1 ◇ sK1)]
  have l23 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54275 X0 sK1 sK1]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l25 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l22 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (X1 ◇ sK1))]
  have l26 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l23 sK1 X0]
    conv => enter [1]; rw [l23 sK1 X1]
  have l27 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h54275 X1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l23 sK1 X0]
  have l28 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l23 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l29 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l27 X1 X0 sK1]
    conv => enter [1]; rw [l25 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l30 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l29 X1 X0 sK1]
  have l31 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1, 2]; rw [← l13 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l30 sK1 X1 X0]
  have l32 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [← l31 sK1 X1 X0]
    conv => enter [1]; rw [l13 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l33 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l32 X1 X0 sK1]
    conv => enter [1]; rw [l21 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l34 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l33 X1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l35 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l34 X1 X0 sK1]
    conv => enter [1, 2]; rw [l13 sK1 (sK1 ◇ sK1)]
  have l36 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l35 X1 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l37 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l36 X1 X0 sK1]
    conv => enter [1]; rw [l18 (sK1 ◇ sK1) (sK1 ◇ sK1) sK1]
  have l38 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l37 X1 X0 sK1]
  have l39 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l13 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l38 sK1 X1 X0]
  have l40 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l28 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l39 sK1 X1 X0]
  have l41 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l24 sK0 X0]
    conv => enter [1]; rw [l24 sK0 X1]
  have l42 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l24 sK0 X0]
  have l43 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l24 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l44 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l43 sK0 X0 X1]
  have l45 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l10 sK0]
    conv => enter [1]; rw [l42 sK0 X0]
  have l46 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l45 sK0 sK0]
  have l47 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l46 sK0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0]
    conv => enter [1]; rw [← l40 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l49 : ∀ X0 sK1 X1 X2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 X2
    conv => enter [1]; rw [l26 X0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l50 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1, 2]; rw [l26 sK1 sK1 X0]
  have l51 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l26 (sK0 ◇ sK0) sK1 X0]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1 sK0]
    conv => enter [1]; rw [← l28 sK1 (sK0 ◇ sK0) sK0]
  have l53 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l49 X0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← l51 sK0 sK1 X0]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l52 sK0 sK1]
  have l55 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l51 sK0 sK1 sK0]
    conv => enter [1]; rw [l53 sK0 sK1 X1 sK0]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l26 sK0 sK1 sK1]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l56 sK0 sK1]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l59 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [l61 sK0 sK1]
  have l63 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 sK0]
    conv => enter [1]; rw [l41 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l64 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [l63 sK0 X0]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l64 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l65 x y]
  conv => enter [1]; rw [l57 x y]

theorem Equation4512_54275_implies_Equation53823 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53823 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X1]
  have l2 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0 X1]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54275 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK0) sK0 sK0]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l1 X0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l5 X0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1, 2]; rw [l6 X0 sK0 X0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l6 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 X0]
  intro x y
  conv => enter [1]; rw [l14 x y y]

theorem Equation4512_54275_implies_Equation53836 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53836 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54275 X0 sK1 sK1]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l0 sK1 X0]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 sK1]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1, 2]; rw [l2 sK1 sK1]
  have l6 : ∀ X0 sK1 X1 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h54275 X1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l5 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK1)) X1]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 sK1]
    conv => enter [1]; rw [← l6 X0 sK1 sK1]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 X0]
    conv => enter [1, 2]; rw [← l7 sK1 X0 X0]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← l7 sK1 X0 X0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l12 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  intro x y
  conv => enter [1]; rw [l12 x y y]
  conv => enter [1]; rw [← l2 y y]

theorem Equation4512_54275_implies_Equation53816 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53816 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l12 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l13 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l12 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l13 sK1]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l14 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l16 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (X1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (X1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54275 X0 X1 sK1]
  have l17 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ sK1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l16 sK1 X1 X0]
    conv => enter [1]; rw [← l8 sK1 (X1 ◇ sK1)]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54275 X0 sK1 sK1]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l20 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← l18 sK1 X0]
    conv => enter [1]; rw [l18 sK1 X1]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l18 sK1 X0]
  have l22 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l10 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l18 sK1 X0]
  have l23 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1, 2, 2]; rw [l18 sK1 X0]
    conv => enter [1]; rw [← h54275 X1 X0 (sK1 ◇ sK1)]
  have l24 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l18 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l25 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l24 sK1 X0 X1]
  have l26 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [← l23 sK1 X1 X0]
    conv => enter [1]; rw [l10 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← l13 sK1]
    conv => enter [1]; rw [l22 sK1 X0]
  have l28 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l17 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l26 X1 X0 sK1]
  have l29 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l25 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l27 sK1 sK1]
  have l30 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l15 sK1 sK1]
    conv => enter [1]; rw [l28 sK1 X1 X0]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l29 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l32 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1, 2]; rw [l11 sK1]
    conv => enter [1]; rw [l30 sK1 X1 X0]
  have l33 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l32 sK1 X1 X0]
  have l34 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l31 sK1]
    conv => enter [1]; rw [l33 sK1 X1 X0]
  have l35 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l19 sK0 X0]
    conv => enter [1]; rw [l19 sK0 X1]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l19 sK0 (sK1 ◇ sK1)]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l36 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l37 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l38 sK0 sK1]
  have l40 : ∀ X0 sK1 X1 X2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 X2
    conv => enter [1]; rw [l20 X0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l41 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l40 X0 sK1 X1 X0]
    conv => enter [1, 2]; rw [l20 X0 sK1 sK1]
  have l42 : ∀ sK1 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l41 sK1 sK1 X1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK1)]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ sK1)]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← l21 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l45 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [l39 sK1 sK0]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l47 sK0 sK1]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [← l48 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l52 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l52 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [l53 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [l54 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l55 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [l56 sK0 sK1]
  have l58 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [l57 sK0 sK1]
  have l59 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l35 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l60 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l59 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l35 X0 sK0 sK0]
  have l61 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l60 sK0 sK0 X1]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l58 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l62 x y]
  conv => enter [1]; rw [l50 y x]

theorem Equation4512_54275_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54275 : Equation54275 G) : Equation53808 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54275 X0 sK0 sK0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l1 sK0 X0]
    conv => enter [1]; rw [l1 sK0 X1]
  have l3 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l2 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l3 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l2 X0 sK0 sK0]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 sK0 X1]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54275 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK0) sK0 sK0]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l2 X0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← l6 X0 sK0 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2]; rw [l7 X0 sK0 X0]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ sK1)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

end Semigroup5
