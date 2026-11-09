import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_4725_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4725 : Equation4725 G) : Equation4696 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4725 X0 X0 X1]
    conv => enter [1]; rw [← h4725 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4725 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0))]
  have l6 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation43_4512_4725_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4725 : Equation4725 G) : Equation4698 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4725 X0 X0 X1]
    conv => enter [1]; rw [← h4725 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4725 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))]
  have l6 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation43_4512_4725_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4725 : Equation4725 G) : Equation4699 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l1 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) X1]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X1]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4725 X0 X0 X1]
    conv => enter [1]; rw [← h4725 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4725 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0))]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation43_4512_4725_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4725 : Equation4725 G) : Equation4704 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4725 X0 X0 X1]
    conv => enter [1]; rw [← h4725 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4725 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))]
  have l6 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation43_4512_4725_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4725 : Equation4725 G) : Equation4705 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
  have l1 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) X1]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X1]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4725 X0 X0 X1]
    conv => enter [1]; rw [← h4725 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4725 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0))]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation43_4512_4725_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4725 : Equation4725 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l4 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4725 X0 X0 X1]
    conv => enter [1]; rw [← h4725 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l8 : ∀ sK1 sK2 sK3 sK0 X0 : G, sK1 = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4725 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0))]
  have l9 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4725 X0 X1 X2]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l10 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l9 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l11 : ∀ sK1 sK2 sK3 sK0 X0 : G, sK1 = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)]
  have l12 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1]; rw [l10 X3 X0 X3 X3]
    conv => enter [1]; rw [l7 X0 ((X3 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X3)]
  have l13 : ∀ sK1 sK2 sK3 sK0 X0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0))]
  have l14 : ∀ sK1 sK2 sK3 sK0 X0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [l12 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)]
  have l15 : ∀ sK1 sK2 sK3 sK0 X0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)]
  have l16 : ∀ sK1 X0 : G, sK1 = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 sK1 sK1 sK1 X0]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  intro x y z w
  conv => enter [1]; rw [l16 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4725_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4725 : Equation4725 G) : Equation4724 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4725 X0 X0 X1]
    conv => enter [1]; rw [← h4725 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4725 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))]
  have l6 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation43_4512_4725_implies_Equation4728 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4725 : Equation4725 G) : Equation4728 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l4 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4725 X0 X0 X1]
    conv => enter [1]; rw [← h4725 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4725 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0))]
  have l9 : ∀ sK1 sK2 X0 : G, sK1 = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4725 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))]
  have l10 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4725 X0 X1 X2]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l11 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l10 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l12 : ∀ sK1 sK2 X0 : G, sK1 = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK1 ◇ (sK2 ◇ sK2)) ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)]
  have l14 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1]; rw [l11 X3 X0 X3 X3]
    conv => enter [1]; rw [l7 X0 ((X3 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X3)]
  have l15 : ∀ sK1 sK2 X0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0))]
  have l17 : ∀ sK1 sK2 X0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l14 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)]
  have l18 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l16 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l14 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)]
  have l19 : ∀ sK1 sK2 X0 : G, sK1 = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l17 sK1 sK2 X0]
    conv => enter [1]; rw [l14 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l14 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)]
  have l21 : ∀ sK1 X0 : G, sK1 = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1 sK1 X0]
    conv => enter [1]; rw [l14 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l22 : ∀ sK0 X0 : G, sK0 = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l14 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
  intro x y z
  conv => enter [1]; rw [l22 x y]
  conv => enter [1]; rw [l21 y (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

theorem Equation43_4512_4724_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4724 : Equation4724 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [h43 X1 (X0 ◇ X2)]
  have l10 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l11 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
  have l14 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X3 X2]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ X2)]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4724 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h4724 X1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l19 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h4724 X2 (X0 ◇ X1)]
  have l20 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4724 X0 X1]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4724 X0 X2]
    conv => enter [1]; rw [← l9 X0 X1 (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4724 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l22 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
  have l24 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l20 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X1))) X2]
  have l25 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l6 (X0 ◇ X1) (X0 ◇ X1) X0 X1]
    conv => enter [1]; rw [l19 X2 X0 X1]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l13 X1 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l18 X1 X0]
  have l27 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1 X0]
    conv => enter [1, 2]; rw [← l21 X1 X0 X0]
  have l28 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l24 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X1)) X2]
  have l29 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [l17 X0 (X0 ◇ X1) X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l25 X2 X0 X1]
  have l30 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l17 X1 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l26 X1 X0]
  have l31 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l28 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l32 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [l13 X0 X1 (X0 ◇ X1) (X0 ◇ X1)]
    conv => enter [1]; rw [l29 X2 X0 X1]
  have l33 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l6 (X0 ◇ (X0 ◇ X0)) X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l30 X1 X0]
  have l34 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l31 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l35 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l8 X1 (X0 ◇ X1) X0 X1]
    conv => enter [1]; rw [l32 X2 X0 X1]
  have l36 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l6 (X0 ◇ (X0 ◇ X0)) X0 X0 X0]
    conv => enter [1]; rw [l33 X1 X0]
  have l37 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [l27 X1 X0]
    conv => enter [1]; rw [l35 X2 X0 X1]
  have l38 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l17 X0 X0 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l36 X1 X0]
  have l39 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [l27 X0 X1]
    conv => enter [1]; rw [l37 X2 X0 X1]
  have l40 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l6 (X0 ◇ X0) X0 X0 X0]
    conv => enter [1]; rw [l38 X1 X0]
  have l41 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l27 X1 X0]
    conv => enter [1]; rw [l39 X2 X0 X1]
  have l42 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l34 ((X0 ◇ X0) ◇ (X0 ◇ X0)) X1 X0]
    conv => enter [1]; rw [l40 X1 X0]
  have l43 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [l27 X0 X1]
    conv => enter [1]; rw [l41 X2 X0 X1]
  have l44 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 (X0 ◇ X0) (X0 ◇ X0) X1]
    conv => enter [1]; rw [l42 X0 X1]
  have l45 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [l27 X1 X0]
    conv => enter [1]; rw [l43 X2 X0 X1]
  have l46 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l44 X0 X1]
  have l47 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l27 X0 X1]
    conv => enter [1]; rw [l45 X2 X0 X1]
  have l48 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l46 X0 X1]
  have l49 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l47 X0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l48 X0 X1]
  intro x y
  conv => enter [1]; rw [l49 x y]

theorem Equation43_4512_4724_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4724 : Equation4724 G) : Equation4696 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l7 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l15 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l21 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X0]
    conv => enter [1]; rw [l21 sK0 sK1 X0]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [l20 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l25 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X0]
  have l27 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
  have l28 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X1]
  have l29 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l28 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X1]
  have l30 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l29 sK0 sK1 X0 X1]
  have l31 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l32 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l33 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l32 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l34 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l31 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l35 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l33 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l27 sK0 sK1 X1 X0]
  have l36 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l34 X0 X1 X2 X3]
  have l37 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0 X1]
    conv => enter [1]; rw [l35 sK0 sK1 X0 X1]
  have l38 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l36 X0 X1 X2 X3]
  have l39 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l40 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l41 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4724 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h4724 X1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l42 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4724 (X1 ◇ X0) X2]
    conv => enter [1, 2]; rw [l0 X1 X0 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
  have l43 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4724 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l44 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4724 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))]
  have l45 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4724 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l46 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4724 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l47 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l46 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X1))) X2]
  have l48 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l45 X0 X2 X1]
    conv => enter [1]; rw [← l1 X0 X2 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))]
  have l49 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l50 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l51 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l42 X1 X0 X2]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) (X1 ◇ X0)]
  have l52 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l41 X1 X0]
  have l53 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l47 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X1)) X2]
  have l54 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [l38 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l55 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l56 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l51 X1 X0 X2]
    conv => enter [1]; rw [l40 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) X1 X0]
  have l57 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [l52 X1 X0]
  have l58 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l53 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l59 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [l40 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l60 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l37 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l61 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l56 X1 X0 X1]
    conv => enter [1, 2]; rw [← l48 X1 X0 X1]
  have l62 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l38 (X0 ◇ (X0 ◇ X0)) X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l57 X1 X0]
  have l63 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l58 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l64 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [l38 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l65 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [l38 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l66 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l38 (X0 ◇ (X0 ◇ X0)) X0 X0 X0]
    conv => enter [1]; rw [l62 X1 X0]
  have l67 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))]
  have l68 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [l39 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l69 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l38 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [l66 X1 X0]
  have l70 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1, 2]; rw [← l61 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l71 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))]
  have l72 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l63 X1 ((X0 ◇ (X0 ◇ X0)) ◇ X0) X0]
    conv => enter [1]; rw [l69 X1 X0]
  have l73 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l74 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l72 X1 X0]
  have l75 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l73 sK0 sK1]
    conv => enter [1, 2]; rw [← l70 sK0 sK1]
  have l76 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l61 X0 X0]
    conv => enter [1]; rw [l74 X1 X0]
  have l77 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK0]
  have l78 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l61 X0 X0]
    conv => enter [1]; rw [l76 X1 X0]
  have l79 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l77 sK0 sK1]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l79 sK0 sK1]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l82 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 1]; rw [← l77 sK0 sK1]
    conv => enter [1, 2]; rw [← l77 sK0 sK1]
  have l83 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [← l82 sK0 sK1]
  have l84 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [l1 X0 sK0 sK0]
  have l85 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l84 X0 sK0 sK1]
    conv => enter [1]; rw [← l61 X0 sK0]
  have l86 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2, 2]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [← h4724 X0 (sK0 ◇ sK1)]
  have l87 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l61 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l86 X0 sK0 sK1]
  have l88 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l78 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l87 X0 X0 X0]
  have l89 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l90 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l89 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l91 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l90 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l85 X0 sK0 sK1]
  have l92 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1]; rw [← l91 sK0 sK1 X0]
  have l93 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l92 sK0 sK1 X0]
  have l94 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l93 sK0 sK1 X0]
    conv => enter [1, 1]; rw [← l77 sK0 sK1]
  have l95 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l88 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l96 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l95 sK0 sK1]
    conv => enter [1]; rw [l94 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l97 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l96 sK0 sK1]
    conv => enter [1]; rw [l85 sK0 sK0 sK1]
  have l98 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l88 sK0]
    conv => enter [1]; rw [← l97 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l98 x y]

theorem Equation43_4512_4724_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4724 : Equation4724 G) : Equation4698 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK1 ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK1 ◇ sK1)]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l8 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [l12 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l18 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X0]
    conv => enter [1]; rw [l18 sK1 sK0 X0]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [l17 sK0 sK1]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X0]
  have l22 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X1]
  have l24 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l23 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1]
  have l25 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l24 sK0 sK1 X0 X1]
  have l26 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l27 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) ◇ X1) = ((X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1]
  have l28 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l27 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l29 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l26 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l30 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l28 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l22 sK0 sK1 X1 X0]
  have l31 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l29 X0 X1 X2 X3]
  have l32 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 X1]
    conv => enter [1]; rw [l30 sK0 sK1 X0 X1]
  have l33 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l31 X0 X1 X2 X3]
  have l34 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l35 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l36 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l37 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4724 (X1 ◇ X0) X2]
    conv => enter [1, 2]; rw [l0 X1 X0 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
  have l38 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4724 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l39 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4724 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))]
  have l40 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4724 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l41 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l40 X0 X2 X1]
    conv => enter [1]; rw [← l1 X0 X2 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))]
  have l42 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l43 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l44 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l37 X1 X0 X2]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) (X1 ◇ X0)]
  have l45 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l46 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l47 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l44 X1 X0 X2]
    conv => enter [1]; rw [l35 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) X1 X0]
  have l48 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [l35 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l49 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l50 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l47 X1 X0 X1]
    conv => enter [1, 2]; rw [← l41 X1 X0 X1]
  have l51 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l52 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l53 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))]
  have l54 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [l34 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l55 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1, 2]; rw [← l50 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l56 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l19 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))]
  have l57 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l58 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1, 2]; rw [← l55 sK0 sK1]
  have l59 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) sK0]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l10 sK0 sK1]
    conv => enter [1, 1]; rw [← l59 sK0 sK1]
    conv => enter [1, 2]; rw [← l59 sK0 sK1]
  have l61 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l36 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l59 sK0 sK1]
  have l62 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l61 X0 sK0 sK1]
    conv => enter [1]; rw [← l50 X0 sK0]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l59 sK0 sK1]
    conv => enter [1]; rw [← l60 sK1 sK0]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [l62 (sK1 ◇ sK1) sK0 sK1]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l64 sK0 sK1]
  have l66 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [l65 sK0 sK1]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l59 sK0 sK1]
    conv => enter [1, 2]; rw [l66 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l59 sK0 sK1]
    conv => enter [1, 2]; rw [l68 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [l69 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l70 x y]

theorem Equation43_4512_4724_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4724 : Equation4724 G) : Equation4699 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK1 ◇ sK2)]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l9 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2]
  have l15 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [l12 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l18 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l15 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l19 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) X0]
    conv => enter [1]; rw [l18 sK1 sK2 sK0 X0]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 1]; rw [l17 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l20 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) X0]
  have l22 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK2))]
  have l23 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) X1]
  have l24 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l23 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X1]
  have l25 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) X0 X1]
    conv => enter [1]; rw [l24 sK0 sK1 sK2 X0 X1]
  have l26 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l27 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ X1) = ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1]
  have l28 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l27 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l29 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l26 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l30 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l22 sK0 sK1 sK2 X1 X0]
  have l31 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l29 X0 X1 X2 X3]
  have l32 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 X1]
    conv => enter [1]; rw [l30 sK0 sK1 sK2 X0 X1]
  have l33 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l31 X0 X1 X2 X3]
  have l34 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l35 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l36 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l37 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4724 (X1 ◇ X0) X2]
    conv => enter [1, 2]; rw [l0 X1 X0 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
  have l38 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4724 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l39 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4724 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))]
  have l40 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4724 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l41 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l40 X0 X2 X1]
    conv => enter [1]; rw [← l1 X0 X2 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))]
  have l42 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 sK1 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l43 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l44 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l37 X1 X0 X2]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) (X1 ◇ X0)]
  have l45 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1 sK2]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l46 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l47 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l44 X1 X0 X2]
    conv => enter [1]; rw [l35 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) X1 X0]
  have l48 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0 sK1 sK2]
    conv => enter [1]; rw [l35 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l49 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 sK1 sK2]
    conv => enter [1]; rw [l32 sK0 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l50 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l47 X1 X0 X1]
    conv => enter [1, 2]; rw [← l41 X1 X0 X1]
  have l51 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l48 sK0 sK1 sK2]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l52 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 sK1 sK2]
    conv => enter [1]; rw [l33 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l53 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK0 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))]
  have l54 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
    conv => enter [1]; rw [l34 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l55 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l50 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l56 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l54 sK0 sK1 sK2]
    conv => enter [1]; rw [← l19 sK1 sK2 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))]
  have l57 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l56 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l58 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l55 sK0 sK1 sK2]
  have l59 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l58 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) sK0]
  have l60 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l10 sK0 sK1 sK2]
    conv => enter [1, 1]; rw [← l59 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l59 sK0 sK1 sK2]
  have l61 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l36 sK0 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l59 sK0 sK1 sK2]
  have l62 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ sK0) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l61 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l50 X0 sK0]
  have l63 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l59 sK0 sK1 sK2]
    conv => enter [1]; rw [← l60 sK1 sK2 sK0]
  have l64 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 sK0 sK1 sK2]
    conv => enter [1]; rw [l62 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l65 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l64 sK0 sK1 sK2]
  have l66 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
    conv => enter [1]; rw [l65 sK0 sK1 sK2]
  have l67 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l59 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l66 sK0 sK1 sK2]
  have l68 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l66 sK0 sK1 sK2]
    conv => enter [1]; rw [l67 sK0 sK1 sK2]
  have l69 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l59 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l68 sK0 sK1 sK2]
  have l70 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l66 sK0 sK1 sK2]
    conv => enter [1]; rw [l69 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l70 x y z]

theorem Equation43_4512_4724_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4724 : Equation4724 G) : Equation4704 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4724 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h4724 X1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4724 (X1 ◇ X0) X2]
    conv => enter [1, 2]; rw [l0 X1 X0 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4724 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4724 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X1))) X2]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [← l1 X0 X2 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l8 X1 X0 X2]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) (X1 ◇ X0)]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l7 X1 X0]
  have l15 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l11 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X1)) X2]
  have l16 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l13 X1 X0 X2]
    conv => enter [1]; rw [l6 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [l14 X1 X0]
  have l18 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0 X1]
    conv => enter [1, 2]; rw [← l12 X1 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l5 (X0 ◇ (X0 ◇ X0)) X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l17 X1 X0]
  have l21 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l18 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 (X0 ◇ (X0 ◇ X0)) X0 X0 X0]
    conv => enter [1]; rw [l20 X1 X0]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [l22 X1 X0]
  have l24 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 ((X0 ◇ (X0 ◇ X0)) ◇ X0) X0]
    conv => enter [1]; rw [l23 X1 X0]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l24 X1 X0]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l19 X0 X0]
    conv => enter [1]; rw [l25 X1 X0]
  have l27 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l19 X0 X0]
    conv => enter [1]; rw [l26 X1 X0]
  have l28 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l27 X2 (X0 ◇ X1)]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1 X0]
    conv => enter [1]; rw [l27 X0 X1]
  have l30 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l27 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4724 X1 (X0 ◇ X0)]
  have l31 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l5 (X0 ◇ X0) (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [l30 X1 X0]
  have l32 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l19 X0 X1]
    conv => enter [1]; rw [l28 X2 X0 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l29 X1 (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))]
    conv => enter [1]; rw [l31 X1 X0]
  have l34 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l29 X2 X1]
    conv => enter [1]; rw [l32 X2 X2 X1]
  have l35 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [l33 X0 X1]
  have l36 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l34 X0 ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l35 X0 X1]
  intro x y
  conv => enter [1]; rw [l36 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

theorem Equation43_4512_4724_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4724 : Equation4724 G) : Equation4705 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4724 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h4724 X1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4724 (X1 ◇ X0) X2]
    conv => enter [1, 2]; rw [l0 X1 X0 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4724 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4724 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X1))) X2]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [← l1 X0 X2 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l8 X1 X0 X2]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) (X1 ◇ X0)]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l7 X1 X0]
  have l15 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l11 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X1)) X2]
  have l16 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l13 X1 X0 X2]
    conv => enter [1]; rw [l6 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [l14 X1 X0]
  have l18 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0 X1]
    conv => enter [1, 2]; rw [← l12 X1 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l5 (X0 ◇ (X0 ◇ X0)) X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l17 X1 X0]
  have l21 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l18 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 (X0 ◇ (X0 ◇ X0)) X0 X0 X0]
    conv => enter [1]; rw [l20 X1 X0]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [l22 X1 X0]
  have l24 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 ((X0 ◇ (X0 ◇ X0)) ◇ X0) X0]
    conv => enter [1]; rw [l23 X1 X0]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l24 X1 X0]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l19 X0 X0]
    conv => enter [1]; rw [l25 X1 X0]
  have l27 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l19 X0 X0]
    conv => enter [1]; rw [l26 X1 X0]
  have l28 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l27 X2 (X0 ◇ X1)]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1 X0]
    conv => enter [1]; rw [l27 X0 X1]
  have l30 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l27 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4724 X1 (X0 ◇ X0)]
  have l31 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l5 (X0 ◇ X0) (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [l30 X1 X0]
  have l32 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l19 X0 X1]
    conv => enter [1]; rw [l28 X2 X0 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l29 X1 (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))]
    conv => enter [1]; rw [l31 X1 X0]
  have l34 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l29 X2 X1]
    conv => enter [1]; rw [l32 X2 X2 X1]
  have l35 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [l33 X0 X1]
  have l36 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l34 X0 ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l35 X0 X1]
  intro x y z
  conv => enter [1]; rw [l36 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4724_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4724 : Equation4724 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l9 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l9 X0 X1 X2 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X1 X0 ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [← h4724 X2 (X1 ◇ X0)]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [← h4724 X1 X0]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4724 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))))]
  have l15 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4724 X0 X2]
    conv => enter [1]; rw [l3 X1 X0 (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4724 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l16 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
  have l18 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l14 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l11 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l13 X1 X0]
  have l20 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l6 (X1 ◇ X0) (X1 ◇ X0) X1 X0]
    conv => enter [1]; rw [l12 X2 X0 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1 X0]
    conv => enter [1, 2]; rw [← l15 X0 X1 X0]
  have l22 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))))]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l19 X1 X0]
  have l24 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l1 (X1 ◇ X0) (X1 ◇ X0) X0]
    conv => enter [1]; rw [l20 X2 X0 X1]
  have l25 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l21 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l21 X0 X1]
    conv => enter [1]; rw [l23 X1 X0]
  have l27 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [l21 X2 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))))]
    conv => enter [1]; rw [l24 X2 X0 X1]
  have l28 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l25 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l21 X0 X1]
    conv => enter [1]; rw [l26 X1 X0]
  have l30 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l21 X1 (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l27 X2 X0 X1]
  have l31 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l32 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l21 X0 X1]
    conv => enter [1]; rw [l29 X1 X0]
  have l33 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l7 X0 (X1 ◇ X0) X1 X0]
    conv => enter [1]; rw [l30 X2 X0 X1]
  have l34 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l31 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l21 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l35 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l32 X0 X1]
    conv => enter [1]; rw [l33 X2 X0 X1]
  have l36 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l32 X0 X1]
    conv => enter [1]; rw [l35 X2 X0 X1]
  have l37 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l32 X0 X2]
    conv => enter [1]; rw [l36 X2 X0 X2]
  have l38 : ∀ sK1 X0 sK2 sK3 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1, 1]; rw [l34 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) X0]
  have l39 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = (sK1 ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l37 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)]
    conv => enter [1]; rw [← l38 sK1 X0 sK2 sK3 sK0]
  have l40 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l37 sK1 sK1]
    conv => enter [1]; rw [← l39 sK1 sK2 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l40 x y z w]

theorem Equation43_4512_4724_implies_Equation4725 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4724 : Equation4724 G) : Equation4725 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4724 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h4724 X1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4724 (X1 ◇ X0) X2]
    conv => enter [1, 2]; rw [l0 X1 X0 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4724 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4724 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X1))) X2]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [← l1 X0 X2 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l8 X1 X0 X2]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) (X1 ◇ X0)]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l7 X1 X0]
  have l15 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l11 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X1)) X2]
  have l16 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l13 X1 X0 X2]
    conv => enter [1]; rw [l6 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [l14 X1 X0]
  have l18 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0 X1]
    conv => enter [1, 2]; rw [← l12 X1 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l5 (X0 ◇ (X0 ◇ X0)) X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l17 X1 X0]
  have l21 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l18 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 (X0 ◇ (X0 ◇ X0)) X0 X0 X0]
    conv => enter [1]; rw [l20 X1 X0]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [l22 X1 X0]
  have l24 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 ((X0 ◇ (X0 ◇ X0)) ◇ X0) X0]
    conv => enter [1]; rw [l23 X1 X0]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l24 X1 X0]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l19 X0 X0]
    conv => enter [1]; rw [l25 X1 X0]
  have l27 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l19 X0 X0]
    conv => enter [1]; rw [l26 X1 X0]
  have l28 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l27 X2 (X0 ◇ X1)]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1 X0]
    conv => enter [1]; rw [l27 X0 X1]
  have l30 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l27 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4724 X1 (X0 ◇ X0)]
  have l31 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l5 (X0 ◇ X0) (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [l30 X1 X0]
  have l32 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l19 X0 X1]
    conv => enter [1]; rw [l28 X2 X0 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l29 X1 (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))]
    conv => enter [1]; rw [l31 X1 X0]
  have l34 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l29 X2 X1]
    conv => enter [1]; rw [l32 X2 X2 X1]
  have l35 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [l33 X0 X1]
  have l36 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l34 X0 ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l35 X0 X1]
  intro x y z
  conv => enter [1]; rw [l36 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4709_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4709 : Equation4709 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4709 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4709 X1 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1, 1]; rw [h4709 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
  have l3 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4709 X0 X1 X2 X3]
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l3 X4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l5 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X4 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l6 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l4 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l7 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l8 : ∀ X4 X0 : G, (X4 ◇ X0) = X0 := by
    intro X4 X0
    conv => enter [1]; rw [l6 X4 X0 X4 X4 X4]
    conv => enter [1]; rw [l1 X0 ((X4 ◇ (X4 ◇ X4)) ◇ X4)]
  have l9 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l7 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X4)]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation43_4512_4709_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4709 : Equation4709 G) : Equation4696 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X0]
  have l14 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X1]
  have l16 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l15 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l17 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l16 sK0 sK1 X0 X1]
  have l18 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l19 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X1]
  have l20 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l19 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l21 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l22 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l20 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l14 sK0 sK1 X1 X0]
  have l23 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l21 X0 X1 X2 X3]
  have l24 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l22 sK0 sK1 X0 X1]
  have l25 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l23 X0 X1 X2 X3]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4709 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4709 X1 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l27 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4709 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
  have l28 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) = (X4 ◇ X0) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 2]; rw [← h4709 X0 X1 X2 X3]
  have l29 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h4709 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l30 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l29 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l31 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l28 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l32 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l27 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l17 sK0 sK1 sK0 (X0 ◇ X1)]
  have l33 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l30 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l24 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l34 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l31 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l35 : ∀ sK0 X0 X1 sK1 : G, sK0 = (sK0 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l32 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ X1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l36 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l33 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l25 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (X0 ◇ (X1 ◇ X2))]
  have l37 : ∀ X4 X0 : G, (X4 ◇ X0) = X0 := by
    intro X4 X0
    conv => enter [1]; rw [l34 X4 X0 X4 X4 X4]
    conv => enter [1]; rw [l26 X0 ((X4 ◇ (X4 ◇ X4)) ◇ X4)]
  have l38 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l35 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (X0 ◇ X1)]
  have l39 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l36 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l13 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l40 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = sK0 := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l37 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))))) (X0 ◇ X1)]
    conv => enter [1]; rw [← l38 sK0 X0 X0 X1]
  have l41 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l39 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l37 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l42 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l41 sK0 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [l37 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (X0 ◇ (X1 ◇ X2))]
  have l43 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [← l37 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← l42 sK0 sK1 X0 X1 X2]
  have l44 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [l43 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [l37 sK0 sK1]
  have l45 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X2 sK0 sK1
    conv => enter [1, 2]; rw [← l37 X1 X2]
    conv => enter [1]; rw [l44 X1 X1 X2 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l40 sK0 sK0 sK0]
    conv => enter [1]; rw [l45 sK0 sK0 sK0 sK1]
  have l47 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l37 sK0 sK0]
    conv => enter [1, 2]; rw [l46 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l47 x y]

theorem Equation43_4512_4709_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4709 : Equation4709 G) : Equation4698 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X0]
  have l13 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l14 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1]
  have l15 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l14 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1]
  have l16 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l15 sK0 sK1 X0 X1]
  have l17 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l18 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1]
  have l19 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l20 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l21 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l19 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l13 sK0 sK1 X1 X0]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
  have l23 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l21 sK0 sK1 X0 X1]
  have l24 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l22 X0 X1 X2 X3]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4709 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4709 X1 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l26 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4709 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l27 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) = (X4 ◇ X0) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 2]; rw [← h4709 X0 X1 X2 X3]
  have l28 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h4709 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l29 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l28 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l30 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l27 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l31 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l26 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l16 sK0 sK1 sK0 (X0 ◇ X1)]
  have l32 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l29 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l23 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l33 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l30 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l34 : ∀ sK0 X0 X1 sK1 : G, sK0 = (sK0 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l31 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ X1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l35 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l32 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l24 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (X0 ◇ (X1 ◇ X2))]
  have l36 : ∀ X4 X0 : G, (X4 ◇ X0) = X0 := by
    intro X4 X0
    conv => enter [1]; rw [l33 X4 X0 X4 X4 X4]
    conv => enter [1]; rw [l25 X0 ((X4 ◇ (X4 ◇ X4)) ◇ X4)]
  have l37 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l34 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (X0 ◇ X1)]
  have l38 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l35 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l12 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l39 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = sK0 := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l36 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ X0))))) (X0 ◇ X1)]
    conv => enter [1]; rw [← l37 sK0 X0 X0 X1]
  have l40 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l38 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l36 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l41 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l40 sK0 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [l36 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (X0 ◇ (X1 ◇ X2))]
  have l42 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [← l36 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← l41 sK0 sK1 X0 X1 X2]
  have l43 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [l42 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l36 sK0 (sK1 ◇ sK1)]
  have l44 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK0 sK1
    conv => enter [1, 2]; rw [← l36 X1 X2]
    conv => enter [1]; rw [l43 X1 X1 X2 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l39 sK0 sK0 sK0]
    conv => enter [1]; rw [l44 sK0 sK0 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l36 sK0 sK0]
    conv => enter [1, 2]; rw [l45 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l46 x y]

theorem Equation43_4512_4709_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4709 : Equation4709 G) : Equation4699 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK1 ◇ sK2)]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 1]; rw [l10 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) X0]
  have l13 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l14 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X1]
  have l15 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1]
  have l16 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l15 sK0 sK1 sK2 X0 X1]
  have l17 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l18 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X1]
  have l19 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l20 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l21 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 X1 X0]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
  have l23 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X0 X1]
  have l24 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l22 X0 X1 X2 X3]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4709 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4709 X1 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l26 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4709 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
  have l27 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) = (X4 ◇ X0) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 2]; rw [← h4709 X0 X1 X2 X3]
  have l28 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h4709 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l29 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l30 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l27 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l31 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2 sK0 (X0 ◇ X1)]
  have l32 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l29 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [l23 sK0 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l33 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l30 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l34 : ∀ sK0 X0 X1 sK1 sK2 : G, sK0 = (sK0 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ X1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l35 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l32 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [l24 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (X0 ◇ (X1 ◇ X2))]
  have l36 : ∀ X4 X0 : G, (X4 ◇ X0) = X0 := by
    intro X4 X0
    conv => enter [1]; rw [l33 X4 X0 X4 X4 X4]
    conv => enter [1]; rw [l25 X0 ((X4 ◇ (X4 ◇ X4)) ◇ X4)]
  have l37 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l34 sK0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 (X0 ◇ X1)]
  have l38 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l35 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l39 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = sK0 := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l36 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ X0))))) (X0 ◇ X1)]
    conv => enter [1]; rw [← l37 sK0 X0 X0 X0 X1]
  have l40 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l38 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [l36 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l41 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l40 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1, 2]; rw [l36 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (X0 ◇ (X1 ◇ X2))]
  have l42 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [← l36 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← l41 sK0 sK1 sK2 X0 X1 X2]
  have l43 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l42 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1, 2, 2, 2]; rw [l36 sK0 (sK1 ◇ sK2)]
  have l44 : ∀ X1 X2 sK0 sK1 sK2 : G, (X1 ◇ X2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 X2 sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l36 X1 X2]
    conv => enter [1]; rw [l43 X1 X1 X2 sK0 sK1 sK2]
  have l45 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l39 sK0 sK0 sK0]
    conv => enter [1]; rw [l44 sK0 sK0 sK0 sK1 sK2]
  have l46 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l36 sK0 sK0]
    conv => enter [1, 2]; rw [l45 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l46 x y z]

theorem Equation43_4512_4709_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4709 : Equation4709 G) : Equation4704 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X0]
  have l11 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X1]
  have l13 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X1]
  have l14 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l13 sK0 sK1 X0 X1]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l16 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X1]
  have l17 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l16 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l18 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l19 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l17 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l11 sK0 sK1 X1 X0]
  have l20 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
  have l21 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l19 sK0 sK1 X0 X1]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4709 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4709 X1 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l24 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4709 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l25 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) = (X4 ◇ X0) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 2]; rw [← h4709 X0 X1 X2 X3]
  have l26 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h4709 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l27 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l26 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l28 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l25 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l29 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l24 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK0 (X0 ◇ X1)]
  have l30 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l27 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l21 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l31 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l28 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l32 : ∀ sK0 X0 X1 sK1 : G, sK0 = (sK0 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l29 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ X1) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l33 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l30 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l22 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (X0 ◇ (X1 ◇ X2))]
  have l34 : ∀ X4 X0 : G, (X4 ◇ X0) = X0 := by
    intro X4 X0
    conv => enter [1]; rw [l31 X4 X0 X4 X4 X4]
    conv => enter [1]; rw [l23 X0 ((X4 ◇ (X4 ◇ X4)) ◇ X4)]
  have l35 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l32 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (X0 ◇ X1)]
  have l36 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l33 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l10 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l37 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = sK0 := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l34 (sK0 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X0))))) (X0 ◇ X1)]
    conv => enter [1]; rw [← l35 sK0 X0 X0 X1]
  have l38 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l36 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l34 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l39 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l38 sK0 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [l34 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (X0 ◇ (X1 ◇ X2))]
  have l40 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [← l34 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← l39 sK0 sK1 X0 X1 X2]
  have l41 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [l40 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l34 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l42 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK0 sK1
    conv => enter [1, 2]; rw [← l34 X1 X2]
    conv => enter [1]; rw [l41 X1 X1 X2 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l37 sK0 sK0 sK0]
    conv => enter [1]; rw [l42 sK0 sK0 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l34 sK0 sK0]
    conv => enter [1, 2]; rw [l43 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l44 x y]

theorem Equation43_4512_4709_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4709 : Equation4709 G) : Equation4705 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) (sK1 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 1]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) X0]
  have l11 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l12 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X1]
  have l13 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X1]
  have l14 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0 X1]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l16 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X1]
  have l17 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l16 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l18 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l19 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l17 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2 X1 X0]
  have l20 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
  have l21 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0 X1]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4709 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4709 X1 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l24 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4709 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
  have l25 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) = (X4 ◇ X0) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 2]; rw [← h4709 X0 X1 X2 X3]
  have l26 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h4709 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l27 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l28 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l25 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l29 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l24 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 sK0 (X0 ◇ X1)]
  have l30 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l27 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [l21 sK0 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l31 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l28 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l32 : ∀ sK0 X0 X1 sK1 sK2 : G, sK0 = (sK0 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ X1) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l33 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l30 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [l22 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (X0 ◇ (X1 ◇ X2))]
  have l34 : ∀ X4 X0 : G, (X4 ◇ X0) = X0 := by
    intro X4 X0
    conv => enter [1]; rw [l31 X4 X0 X4 X4 X4]
    conv => enter [1]; rw [l23 X0 ((X4 ◇ (X4 ◇ X4)) ◇ X4)]
  have l35 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l32 sK0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 (X0 ◇ X1)]
  have l36 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l33 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [l10 sK0 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l37 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = sK0 := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l34 (sK0 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X0))))) (X0 ◇ X1)]
    conv => enter [1]; rw [← l35 sK0 X0 X0 X0 X1]
  have l38 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l36 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [l34 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l39 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l38 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1, 2]; rw [l34 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) (X0 ◇ (X1 ◇ X2))]
  have l40 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [← l34 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← l39 sK0 sK1 sK2 X0 X1 X2]
  have l41 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l40 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l34 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l42 : ∀ X1 X2 sK0 sK1 sK2 : G, (X1 ◇ X2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X1 X2 sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l34 X1 X2]
    conv => enter [1]; rw [l41 X1 X1 X2 sK0 sK1 sK2]
  have l43 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l37 sK0 sK0 sK0]
    conv => enter [1]; rw [l42 sK0 sK0 sK0 sK1 sK2]
  have l44 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l34 sK0 sK0]
    conv => enter [1, 2]; rw [l43 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l44 x y z]

theorem Equation43_4512_4709_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4709 : Equation4709 G) : Equation4724 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 X0 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l4 sK1 X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) = (((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X0]
  have l12 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l13 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = ((X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X1]
  have l14 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l16 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l14 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l7 sK0 sK1 X1 X0]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l18 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l16 sK0 sK1 X0 X1]
  have l19 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4709 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4709 X1 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l21 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) = (X4 ◇ X0) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 2]; rw [← h4709 X0 X1 X2 X3]
  have l22 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h4709 sK1 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ X2))))]
  have l23 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h4709 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l24 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l23 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l25 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l22 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (X0 ◇ (X1 ◇ X2))) (sK1 ◇ sK1)]
  have l26 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l21 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l27 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l24 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l18 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l28 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l25 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l5 sK1 (sK1 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l29 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l26 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l30 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l27 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l19 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (X0 ◇ (X1 ◇ X2))]
  have l31 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = (sK1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l28 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l1 sK1 (X0 ◇ (X1 ◇ X2)) (sK1 ◇ (sK1 ◇ sK1))]
  have l32 : ∀ X4 X0 : G, (X4 ◇ X0) = X0 := by
    intro X4 X0
    conv => enter [1]; rw [l29 X4 X0 X4 X4 X4]
    conv => enter [1]; rw [l20 X0 ((X4 ◇ (X4 ◇ X4)) ◇ X4)]
  have l33 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l30 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l11 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l34 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l31 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l6 sK1 (X0 ◇ (X1 ◇ X2))]
  have l35 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l33 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l32 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))))]
  have l36 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ sK1) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [← l32 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← l34 sK1 X0 X1 X2]
  have l37 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l35 sK0 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [l32 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (X0 ◇ (X1 ◇ X2))]
  have l38 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ X2)) = sK1 := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [l36 X0 X1 X2 sK1]
    conv => enter [1]; rw [l32 sK1 sK1]
  have l39 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [← l32 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← l37 sK0 sK1 X0 X1 X2]
  have l40 : ∀ X1 X2 sK1 : G, (X1 ◇ X2) = sK1 := by
    intro X1 X2 sK1
    conv => enter [1, 2]; rw [← l32 X1 X2]
    conv => enter [1]; rw [l38 X1 X1 X2 sK1]
  have l41 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [l39 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2]; rw [l32 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l42 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK0 sK1
    conv => enter [1, 2]; rw [← l32 X1 X2]
    conv => enter [1]; rw [l41 X1 X1 X2 sK0 sK1]
  have l43 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l40 sK1 sK1 sK1]
    conv => enter [1]; rw [l42 sK1 sK1 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l43 sK1 sK0]
    conv => enter [1]; rw [h43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l32 sK1 sK0]
    conv => enter [1]; rw [← l44 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l45 x y]

theorem Equation43_4512_4705_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4705 : Equation4705 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4705 X0 X1 X1]
    conv => enter [1]; rw [← h4705 X1 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4705 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4705 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l4 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l3 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l6 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l4 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l7 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l8 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1]; rw [l6 X3 X0 X3 X3]
    conv => enter [1]; rw [l1 X0 ((X3 ◇ (X3 ◇ X3)) ◇ X3)]
  have l9 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l7 X0 X3 X0 X0]
    conv => enter [1]; rw [l1 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X3)]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation43_4512_4705_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4705 : Equation4705 G) : Equation4696 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X1]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4705 X0 X1 X1]
    conv => enter [1]; rw [← h4705 X1 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4705 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l8 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4705 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l9 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l8 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l10 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l11 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l9 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l12 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l13 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1]; rw [l11 X3 X0 X3 X3]
    conv => enter [1]; rw [l6 X0 ((X3 ◇ (X3 ◇ X3)) ◇ X3)]
  have l14 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l15 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l16 : ∀ sK0 X0 : G, sK0 = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 sK0 X0]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) X0]
  intro x y
  conv => enter [1]; rw [l16 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation43_4512_4705_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4705 : Equation4705 G) : Equation4698 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4705 X0 X1 X1]
    conv => enter [1]; rw [← h4705 X1 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4705 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l8 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4705 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l9 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l8 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l10 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l11 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l9 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l12 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l13 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1]; rw [l11 X3 X0 X3 X3]
    conv => enter [1]; rw [l6 X0 ((X3 ◇ (X3 ◇ X3)) ◇ X3)]
  have l14 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l15 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l16 : ∀ sK0 X0 : G, sK0 = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 sK0 X0]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) X0]
  intro x y
  conv => enter [1]; rw [l16 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

theorem Equation43_4512_4705_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4705 : Equation4705 G) : Equation4699 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X1]
  have l4 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4705 X0 X1 X1]
    conv => enter [1]; rw [← h4705 X1 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4705 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l8 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4705 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l9 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l8 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l11 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l9 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l10 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l0 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l13 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1]; rw [l11 X3 X0 X3 X3]
    conv => enter [1]; rw [l6 X0 ((X3 ◇ (X3 ◇ X3)) ◇ X3)]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l12 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l16 : ∀ sK0 X0 : G, sK0 = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) X0]
  intro x y z
  conv => enter [1]; rw [l16 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

theorem Equation43_4512_4705_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4705 : Equation4705 G) : Equation4704 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X1]
  have l6 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1]
  have l7 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l9 X0 X1 X2 X3]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4705 X0 X1 X1]
    conv => enter [1]; rw [← h4705 X1 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l12 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4705 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l13 : ∀ sK1 X0 : G, sK1 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4705 sK1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l14 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4705 X0 X1 X2]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l15 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l14 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l16 : ∀ sK1 X0 : G, sK1 = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))]
  have l17 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK0 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l18 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l15 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l19 : ∀ sK1 X0 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l16 sK1 X0]
    conv => enter [1]; rw [l10 (sK1 ◇ sK1) (sK1 ◇ sK1) sK1 X0]
  have l20 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK0 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l21 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1]; rw [l18 X3 X0 X3 X3]
    conv => enter [1]; rw [l11 X0 ((X3 ◇ (X3 ◇ X3)) ◇ X3)]
  have l22 : ∀ sK1 X0 : G, sK1 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
  have l23 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l24 : ∀ sK1 X0 : G, sK1 = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l22 sK1 X0]
    conv => enter [1]; rw [l21 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ sK1) ◇ X0)]
  have l25 : ∀ sK0 sK1 X0 : G, sK0 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [l21 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l26 : ∀ sK1 X0 : G, sK1 = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [l24 sK1 X0]
    conv => enter [1]; rw [l21 (sK1 ◇ sK1) X0]
  have l27 : ∀ sK0 X0 : G, sK0 = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 sK0 X0]
    conv => enter [1]; rw [l21 (sK0 ◇ (sK0 ◇ sK0)) X0]
  intro x y
  conv => enter [1]; rw [l27 x y]
  conv => enter [1]; rw [l26 y (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

theorem Equation43_4512_4705_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4705 : Equation4705 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l3 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l1 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l2 X2 X0 X1]
  have l6 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l7 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l6 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4705 X0 X1 X1]
    conv => enter [1]; rw [← h4705 X1 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l11 : ∀ sK0 sK3 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK3 ◇ X0) ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h4705 sK0 sK3 X0]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK3 (sK3 ◇ X0)]
  have l12 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4705 X0 X1 X2]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l13 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l12 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l14 : ∀ sK0 sK3 X0 : G, sK0 = ((sK3 ◇ sK0) ◇ ((sK3 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l11 sK0 sK3 X0]
    conv => enter [1]; rw [l4 sK0 sK0 (sK3 ◇ X0) (sK3 ◇ sK0)]
  have l15 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l13 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l16 : ∀ sK0 sK3 X0 : G, sK0 = ((sK3 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK3 ◇ X0))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l14 sK0 sK3 X0]
    conv => enter [1]; rw [l5 (sK3 ◇ sK0) (sK3 ◇ X0) (sK0 ◇ sK0)]
  have l17 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1]; rw [l15 X3 X0 X3 X3]
    conv => enter [1]; rw [l10 X0 ((X3 ◇ (X3 ◇ X3)) ◇ X3)]
  have l18 : ∀ sK0 sK3 X0 : G, sK0 = ((sK3 ◇ sK0) ◇ (sK3 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l16 sK0 sK3 X0]
    conv => enter [1]; rw [l9 (sK3 ◇ sK0) (sK0 ◇ sK0) sK3 X0]
  have l19 : ∀ sK0 sK3 X0 : G, sK0 = (sK3 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l18 sK0 sK3 X0]
    conv => enter [1]; rw [l17 (sK3 ◇ sK0) (sK3 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l20 : ∀ sK0 X0 : G, sK0 = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 sK0 X0]
    conv => enter [1]; rw [l17 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l21 : ∀ sK0 X0 : G, sK0 = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [l17 (sK0 ◇ sK0) X0]
  have l22 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l22 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4704_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4704 : Equation4704 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l9 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l9 X0 X1 X2 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
  have l12 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X3 X2]
  have l13 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ X2)]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
  have l16 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [h4704 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h4704 (X0 ◇ (X0 ◇ X0)) X0]
  have l17 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l16 X0]
    conv => enter [1]; rw [l6 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0)) X0 (X0 ◇ X0)]
  have l18 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l17 X0]
    conv => enter [1]; rw [l15 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
  have l19 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l18 X0]
    conv => enter [1]; rw [l11 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
  have l20 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l19 X0]
    conv => enter [1, 2]; rw [l6 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0)) X0 (X0 ◇ X0)]
  have l21 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0
    conv => enter [1]; rw [l20 X0]
    conv => enter [1, 2]; rw [l15 X0 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
  have l22 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) := by
    intro X0
    conv => enter [1]; rw [l21 X0]
    conv => enter [1, 2, 2]; rw [l6 (X0 ◇ X0) (X0 ◇ X0) X0 (X0 ◇ X0)]
  have l23 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l22 X0]
    conv => enter [1]; rw [← h4704 X0 (X0 ◇ X0)]
  have l24 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l23 X0]
    conv => enter [1]; rw [← h4704 X1 X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l23 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l26 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l23 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X0) X1]
  have l27 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l26 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l29 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l27 X1 X0]
    conv => enter [1]; rw [l24 X0 X1]
  have l30 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1]; rw [l24 X0 X1]
  have l31 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l30 X0 X1]
    conv => enter [1]; rw [l29 X0 X1]
  intro x y
  conv => enter [1]; rw [l31 x y]

end CommutativeSemigroup5
