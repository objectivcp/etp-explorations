import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation5_implies_Equation5388 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5388 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2, 2]; rw [h5 (sK0 ◇ sK0) sK2]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (z ◇ (x ◇ x)))) y]

theorem Equation4512_5388_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5388 : Equation5388 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5388 X0 (X1 ◇ X2) X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5388 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5392 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5392 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK0) sK2]
    conv => enter [1, 2, 2]; rw [h5 (sK1 ◇ sK0) sK2]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (z ◇ (y ◇ x)))) y]

theorem Equation4512_5392_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5392 : Equation5392 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)))) = X0 := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [← h5392 X0 sK0 sK1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h5392 (X1 ◇ (X1 ◇ (X2 ◇ X0))) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h5392 X0 X2 X1]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ X0)))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ X0)))]
    conv => enter [1]; rw [← h5392 X0 sK1 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)))) = X0 := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5392 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l5 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h5392 (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h5392 sK0 sK1 X0]
  have l6 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (sK1 ◇ X0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro X1 sK1 X0 sK0
    conv => enter [1]; rw [← l2 sK1 sK0 (X1 ◇ (X1 ◇ (X1 ◇ (sK1 ◇ X0))))]
    conv => enter [1, 2, 2, 2]; rw [← h5392 X0 sK1 X1]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5392 (sK1 ◇ sK0) X0 X0]
    conv => enter [1, 2, 2, 2]; rw [l5 X0 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l6 X0 sK1 (sK1 ◇ sK0) sK0]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l10 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK1 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h4512 X0 sK0 X1]
    conv => enter [1, 1]; rw [l9 X0 sK0 sK1]
  have l11 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l9 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l12 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l9 (sK1 ◇ sK0) sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK0]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0 sK1]
  have l15 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l16 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l10 (sK1 ◇ sK0) sK0 (sK1 ◇ sK0) sK1]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation5_implies_Equation5396 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5396 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2, 2]; rw [h5 sK0 sK2]
    conv => enter [1, 2, 2, 2]; rw [h5 sK0 sK2]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (z ◇ (z ◇ x)))) y]

theorem Equation4512_5396_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5396 : Equation5396 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5396 X0 (X1 ◇ X2) X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5396 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5400 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5400 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK1) sK3]
    conv => enter [1, 2, 2]; rw [h5 (sK0 ◇ sK1) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (z ◇ (w ◇ x)))) y]

theorem Equation4512_5400_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5400 : Equation5400 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5400 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5400 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5405 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5405 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK1)) sK3]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK1 ◇ sK1)) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (w ◇ (x ◇ x)))) y]

theorem Equation4512_5405_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5405 : Equation5405 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5405 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5405 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5410 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5410 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK1)) sK3]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK2 ◇ sK1)) sK3]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (w ◇ (y ◇ x)))) y]

theorem Equation4512_5410_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5410 : Equation5410 G) : Equation5 G := by
  have l0 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X3 := by
    intro X2 X4 X0 X1 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h5410 X3 X2 X4 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0))))]
    conv => enter [1]; rw [← h5410 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X1 X1 X1 X0]
    conv => enter [1]; rw [l2 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5415 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5415 G := by
  have l0 : ∀ sK1 sK0 sK3 : G, sK1 = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h5 sK1 sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ (sK3 ◇ sK1)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ sK1)) sK3]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK3 ◇ sK1)) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (w ◇ (z ◇ x)))) y]

theorem Equation4512_5415_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5415 : Equation5415 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5415 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5415 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5420 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5420 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK0 ◇ sK1)) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (w ◇ (w ◇ x)))) y]

theorem Equation4512_5420_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5420 : Equation5420 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5420 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5420 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5425 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5425 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, sK2 = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK1]
  have l1 : ∀ sK1 sK0 sK2 sK4 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK4 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK4
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK2)) sK4]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK0 ◇ sK2)) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK4 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK4]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ (w ◇ (u ◇ x)))) y]

theorem Equation4512_5425_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5425 : Equation5425 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X0))))]
    conv => enter [1]; rw [← h5425 X0 (X1 ◇ X2) X3 X4 X5]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5425 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5431 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5431 G := by
  have l0 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1, 2]; rw [h5 sK1 sK1]
  have l1 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1]; rw [l1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (x ◇ (x ◇ x)))) y]

theorem Equation4512_5431_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5431 : Equation5431 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5431 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5431 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5436 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5436 G := by
  have l0 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (x ◇ (y ◇ x)))) y]

theorem Equation4512_5436_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5436 : Equation5436 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h5436 (X1 ◇ X0) X0 X1 X1]
    conv => enter [1, 2]; rw [← h5436 X0 X1 X1 (X1 ◇ X0)]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h5436 X0 X1 X2 X3]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = (X0 ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X2) X0]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X0 X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l2 X1 X0 X0]
    conv => enter [1]; rw [l3 X1 X2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0 X0]
    conv => enter [1]; rw [l4 X1 X1 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l2 X0 X0 X0]
    conv => enter [1]; rw [l5 X0 X0]
  have l7 : ∀ sK0 X0 X1 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h5436 sK0 sK0 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l0 sK1 sK0]
  have l8 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l7 sK0 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l2 sK0 sK0 (sK1 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation5_implies_Equation5441 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5441 G := by
  have l0 : ∀ sK1 sK3 : G, sK1 = (sK1 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK3
    conv => enter [1]; rw [h5 sK1 sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK3 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK3 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3]
    conv => enter [1]; rw [l1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (x ◇ (z ◇ x)))) y]

theorem Equation4512_5441_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5441 : Equation5441 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5441 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5441 X0 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0 X1 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5446 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5446 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (x ◇ (w ◇ x)))) y]

theorem Equation4512_5446_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5446 : Equation5446 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h5446 sK0 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5446 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5446 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X1 X0]
  have l3 : ∀ sK0 X1 sK1 : G, sK0 = (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l0 sK0 sK0 X1 sK1]
    conv => enter [1]; rw [l2 sK0 (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation5451 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5451 G := by
  have l0 : ∀ sK2 sK0 : G, sK2 = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK2]
  have l1 : ∀ sK2 sK0 sK4 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 sK4 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK2)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (x ◇ (u ◇ x)))) y]

theorem Equation4512_5451_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5451 : Equation5451 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 X5 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X5 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0 X5
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ (X5 ◇ X0))))]
    conv => enter [1]; rw [← h5451 X0 (X1 ◇ X2) X3 X4 X5]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5451 X0 X1 X1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 X1 X1 (X1 ◇ X0) X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5457 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5457 G := by
  have l0 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK2]
  have l1 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK2]
    conv => enter [1]; rw [l1 sK2 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (y ◇ (x ◇ x)))) y]

theorem Equation4512_5457_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5457 : Equation5457 G) : Equation5 G := by
  have l0 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))))) = X4 := by
    intro X3 X0 X1 X2 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X4)))]
    conv => enter [1]; rw [← h5457 X4 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5457 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X1 X1 X1 X0]
    conv => enter [1]; rw [l2 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5462 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5462 G := by
  have l0 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1, 2]; rw [h5 sK1 sK2]
  have l1 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK2]
    conv => enter [1]; rw [l1 sK2 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (y ◇ (y ◇ x)))) y]

theorem Equation4512_5462_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5462 : Equation5462 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5462 sK0 sK1 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5462 sK0 sK1 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation5467 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5467 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, sK1 = (sK2 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [h5 sK1 sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ sK1) sK2]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK3 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK3]
    conv => enter [1]; rw [l1 sK2 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (y ◇ (z ◇ x)))) y]

theorem Equation4512_5467_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5467 : Equation5467 G) : Equation5 G := by
  have l0 : ∀ X2 X3 X0 X1 X4 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X4 := by
    intro X2 X3 X0 X1 X4
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h5467 X4 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5467 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X0]
  have l3 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1, 2]; rw [← l0 X3 X3 X3 X3 X0]
    conv => enter [1]; rw [l2 X3 X3 X3 X3 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5472 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5472 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, sK1 = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
  have l1 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (y ◇ (w ◇ x)))) y]

theorem Equation4512_5472_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5472 : Equation5472 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h5472 sK0 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h5472 (sK1 ◇ (sK1 ◇ sK0)) X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← h5472 sK0 sK1 X0 sK1]
  have l2 : ∀ sK1 X0 sK0 X1 X2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ sK0))) := by
    intro sK1 X0 sK0 X1 X2
    conv => enter [1]; rw [h5472 (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))) X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h5472 sK0 X0 X2 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5472 sK0 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK1]
  have l4 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h5472 sK0 X0 X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 X0 sK1 X1 : G, sK0 = (X0 ◇ (sK1 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l4 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 X1 sK0 (sK1 ◇ sK0) X0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h5472 (sK1 ◇ sK0) X0 X1 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l8 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l2 sK1 X1 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation5_implies_Equation5477 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5477 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, sK2 = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK3]
  have l1 : ∀ sK3 sK0 sK2 sK4 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2 sK4 sK1
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ sK2)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK3 sK0 : G, sK2 = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK2 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w y u]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (y ◇ (u ◇ x)))) y]

theorem Equation4512_5477_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5477 : Equation5477 G) : Equation5 G := by
  have l0 : ∀ X3 X4 X5 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X5 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := by
    intro X3 X4 X5 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h5477 X2 X3 X4 X5 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 : G, (X1 ◇ X2) = X2 := by
    intro X1 X2
    conv => enter [1, 2]; rw [h5477 X2 X1 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5483 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5483 G := by
  have l0 : ∀ sK1 sK3 : G, sK1 = (sK3 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK1 ◇ sK1)))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [h5 (sK3 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ (sK1 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3]
    conv => enter [1]; rw [l1 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (z ◇ (x ◇ x)))) y]

theorem Equation4512_5483_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5483 : Equation5483 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5483 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5483 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5488 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5488 G := by
  have l0 : ∀ sK1 sK3 sK2 : G, sK1 = (sK3 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK3 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK2 sK1 sK0 : G, (sK3 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK2 ◇ sK1)))) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [h5 (sK3 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ (sK2 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK3 sK2]
    conv => enter [1]; rw [l1 sK3 sK2 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (z ◇ (y ◇ x)))) y]

theorem Equation4512_5488_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5488 : Equation5488 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5488 X0 X2 X1 X2]
    conv => enter [1]; rw [← h5488 (X2 ◇ X0) X1 X2 X1]
  have l1 : ∀ sK0 X0 X1 X2 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h5488 sK0 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [l0 X0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (sK1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h5488 (sK1 ◇ sK0) sK1 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation5493 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5493 G := by
  have l0 : ∀ sK1 sK3 : G, sK1 = (sK3 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK3
    conv => enter [1]; rw [h5 sK1 sK3]
    conv => enter [1, 2]; rw [h5 sK1 sK3]
  have l1 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK1)))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [h5 (sK3 ◇ (sK3 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ (sK3 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3]
    conv => enter [1]; rw [l1 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (z ◇ (z ◇ x)))) y]

theorem Equation4512_5493_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5493 : Equation5493 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X3 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X3 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5493 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5493 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5498 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5498 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (z ◇ (w ◇ x)))) y]

theorem Equation4512_5498_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5498 : Equation5498 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X3 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X3 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5498 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5498 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5503 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5503 G := by
  have l0 : ∀ sK2 sK4 sK0 : G, sK2 = (sK4 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK4 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK4]
  have l1 : ∀ sK4 sK0 sK2 sK1 : G, (sK4 ◇ (sK0 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK2)))) := by
    intro sK4 sK0 sK2 sK1
    conv => enter [1]; rw [h5 (sK4 ◇ (sK0 ◇ sK2)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK4 ◇ (sK0 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK4 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK4 sK0]
    conv => enter [1]; rw [l1 sK4 sK0 sK2 sK1]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (z ◇ (u ◇ x)))) y]

theorem Equation4512_5503_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5503 : Equation5503 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X3 ◇ (X5 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X3 ◇ (X5 ◇ X0))))]
    conv => enter [1]; rw [← h5503 X0 (X1 ◇ X2) X3 X4 X5]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5503 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5509 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5509 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (w ◇ (x ◇ x)))) y]

theorem Equation4512_5509_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5509 : Equation5509 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5509 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5509 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5514 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5514 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK1) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (w ◇ (y ◇ x)))) y]

theorem Equation4512_5514_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5514 : Equation5514 G) : Equation5 G := by
  have l0 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))))) = X4 := by
    intro X3 X0 X1 X2 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X4)))]
    conv => enter [1]; rw [← h5514 X4 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0))))]
    conv => enter [1]; rw [← h5514 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X0]
  have l3 : ∀ X2 X0 : G, (X2 ◇ X0) = X0 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l0 X2 X2 X2 X2 X0]
    conv => enter [1]; rw [l2 X2 X2 X2 X2 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5519 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5519 G := by
  have l0 : ∀ sK1 sK0 sK3 : G, sK1 = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h5 sK1 sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ (sK3 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK0 sK3 sK1
    conv => enter [1, 2]; rw [h5 (sK3 ◇ sK1) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK3 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (w ◇ (z ◇ x)))) y]

theorem Equation4512_5519_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5519 : Equation5519 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X4 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5519 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5519 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5524 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5524 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1, 2, 2]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK3]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (w ◇ (w ◇ x)))) y]

theorem Equation4512_5524_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5524 : Equation5524 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X4 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5524 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5524 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5529 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5529 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, sK2 = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK1]
  have l1 : ∀ sK1 sK0 sK2 sK4 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK4
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK2) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK4]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (w ◇ (u ◇ x)))) y]

theorem Equation4512_5529_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5529 : Equation5529 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ (X5 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X4 ◇ (X5 ◇ X0))))]
    conv => enter [1]; rw [← h5529 X0 (X1 ◇ X2) X3 X4 X5]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5529 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5535 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5535 G := by
  have l0 : ∀ sK2 sK0 : G, sK2 = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h5 sK2 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK2) sK0]
  have l1 : ∀ sK0 sK2 sK4 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK4 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK2 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (u ◇ (x ◇ x)))) y]

theorem Equation4512_5535_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5535 : Equation5535 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5535 X0 (X1 ◇ X2) X3 X4 X5]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5535 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5541 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5541 G := by
  have l0 : ∀ sK2 sK0 sK3 : G, sK2 = (sK0 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [h5 sK2 sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ sK2) sK0]
  have l1 : ∀ sK0 sK3 sK2 sK4 sK1 : G, (sK0 ◇ (sK3 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK3 sK2 sK4 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ sK2)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK0 sK3 : G, sK2 = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [l0 sK2 sK0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 sK2 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u y]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (u ◇ (y ◇ x)))) y]

theorem Equation4512_5541_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5541 : Equation5541 G) : Equation5 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 X5 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))))) = X5 := by
    intro X4 X0 X1 X2 X3 X5
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5)))]
    conv => enter [1]; rw [← h5541 X5 X4 (X0 ◇ X1) X2 X3]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ ((X1 ◇ X2) ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X5 ◇ ((X1 ◇ X2) ◇ X0))))]
    conv => enter [1]; rw [← h5541 X0 (X1 ◇ X2) X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X1 ◇ (X2 ◇ X0))))))) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X2 X0 : G, (X2 ◇ X0) = X0 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l0 X2 X2 X2 X2 X2 X0]
    conv => enter [1]; rw [l2 X2 X2 X2 X2 X2 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5547 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5547 G := by
  have l0 : ∀ sK2 sK0 sK4 : G, sK2 = (sK0 ◇ (sK4 ◇ sK2)) := by
    intro sK2 sK0 sK4
    conv => enter [1]; rw [h5 sK2 sK4]
    conv => enter [1]; rw [h5 (sK4 ◇ sK2) sK0]
  have l1 : ∀ sK0 sK4 sK2 sK1 : G, (sK0 ◇ (sK4 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK4 ◇ sK2)))) := by
    intro sK0 sK4 sK2 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK4 ◇ sK2)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK4 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK4 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK0 sK4]
    conv => enter [1]; rw [l1 sK0 sK4 sK2 sK1]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (u ◇ (z ◇ x)))) y]

theorem Equation4512_5547_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5547 : Equation5547 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X5 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5547 X0 (X1 ◇ X2) X3 X4 X5]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5547 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5553 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5553 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, sK2 = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 sK2 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK2) sK0]
  have l1 : ∀ sK0 sK1 sK2 sK4 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 sK4
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK4]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (u ◇ (w ◇ x)))) y]

theorem Equation4512_5553_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5553 : Equation5553 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X5 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5553 X0 (X1 ◇ X2) X3 X4 X5]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5553 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5559 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5559 G := by
  have l0 : ∀ sK2 sK0 : G, sK2 = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1, 2]; rw [h5 sK2 sK0]
  have l1 : ∀ sK0 sK2 sK4 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK4 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK2)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) sK4]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK2 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (u ◇ (u ◇ x)))) y]

theorem Equation4512_5559_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5559 : Equation5559 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X5 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X5 ◇ (X5 ◇ X0))))]
    conv => enter [1]; rw [← h5559 X0 (X1 ◇ X2) X3 X4 X5]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5559 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5565 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5565 G := by
  have l0 : ∀ sK3 sK0 sK1 : G, sK3 = (sK0 ◇ (sK1 ◇ sK3)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h5 sK3 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK3) sK0]
  have l1 : ∀ sK0 sK1 sK3 sK5 sK2 : G, (sK0 ◇ (sK1 ◇ sK3)) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK0 sK1 sK3 sK5 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK3)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) sK5]
  have l2 : ∀ sK3 sK5 sK2 sK0 sK1 : G, sK3 = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK3 sK5 sK2]
  intro x y z w u v
  conv => enter [1]; rw [l2 x z w u v]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ (u ◇ (v ◇ x)))) y]

theorem Equation4512_5565_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5565 : Equation5565 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X6 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X6 ◇ X0)))))) = X0 := by
    intro X1 X2 X3 X4 X5 X6 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X5 ◇ (X6 ◇ X0))))]
    conv => enter [1]; rw [← h5565 X0 (X1 ◇ X2) X3 X4 X5 X6]
  have l1 : ∀ X6 X0 : G, (X6 ◇ X0) = X0 := by
    intro X6 X0
    conv => enter [1, 2]; rw [h5565 X0 X6 X6 X6 X6 X6]
    conv => enter [1]; rw [l0 X6 X6 X6 X6 X6 X6 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation10_4512_implies_Equation49 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation49 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1, 2]; rw [h10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation49_4512_implies_Equation10 (G : Type*) [Magma G] (h49 : Equation49 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h49 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h49 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h49 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation10_4512_implies_Equation52 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation52 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1]; rw [h10 (sK0 ◇ sK0) sK1]
    conv => enter [1, 1]; rw [l2 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation52_4512_implies_Equation10 (G : Type*) [Magma G] (h52 : Equation52 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h52 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h52 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h52 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h52 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation10_4512_implies_Equation55 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation55 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation55_4512_implies_Equation10 (G : Type*) [Magma G] (h55 : Equation55 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h55 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h55 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h55 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h55 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l3 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation10_4512_implies_Equation58 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation58 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation58_4512_implies_Equation10 (G : Type*) [Magma G] (h58 : Equation58 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h58 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h58 X0 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h58 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation10_implies_Equation413 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation413 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 1]; rw [← h10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation413_4512_implies_Equation10 (G : Type*) [Magma G] (h413 : Equation413 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h413 sK0 sK1]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h413 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l3 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h413 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK0 (sK1 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation10_4512_implies_Equation416 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation416 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1]; rw [h10 (sK0 ◇ sK0) sK1]
    conv => enter [1, 1]; rw [l2 sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation416_4512_implies_Equation10 (G : Type*) [Magma G] (h416 : Equation416 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h416 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h416 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) X0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h416 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l10 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l7 sK1 sK0 sK0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l11 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ X0) sK0]
  have l15 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h416 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK0]
  have l16 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l14 sK0 (X0 ◇ sK0)]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l12 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation10_4512_implies_Equation422 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation422 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h10 (sK1 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation422_4512_implies_Equation10 (G : Type*) [Magma G] (h422 : Equation422 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h422 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h422 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h422 (sK1 ◇ sK0) sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h422 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation10_implies_Equation426 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation426 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK0]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← h10 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation426_4512_implies_Equation10 (G : Type*) [Magma G] (h426 : Equation426 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h426 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h426 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h426 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation10_implies_Equation432 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation432 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 sK2]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← h10 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation432_4512_implies_Equation10 (G : Type*) [Magma G] (h432 : Equation432 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h432 (X1 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h432 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h432 (sK1 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h432 sK0 (sK1 ◇ sK0) sK1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h432 X0 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation10_4512_implies_Equation439 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation439 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation439_4512_implies_Equation10 (G : Type*) [Magma G] (h439 : Equation439 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h439 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h439 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h439 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h439 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2, 2]; rw [l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [← h439 X0 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l6 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h439 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 (sK1 ◇ sK0) sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation10_4512_implies_Equation442 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation442 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK0)) sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation442_4512_implies_Equation10 (G : Type*) [Magma G] (h442 : Equation442 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h442 (X1 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h442 X0 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h442 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation10_4512_implies_Equation446 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation446 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ sK0) sK2]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l2 sK2 sK0]
    conv => enter [1, 2]; rw [l3 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l4 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK0)) sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation446_4512_implies_Equation10 (G : Type*) [Magma G] (h446 : Equation446 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h446 (X0 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h446 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h446 X0 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h446 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation10_4512_implies_Equation450 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation450 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK0)) sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation450_4512_implies_Equation10 (G : Type*) [Magma G] (h450 : Equation450 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h450 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h450 X0 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h450 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [← h450 sK0 sK1 sK0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h450 X1 X0 (X0 ◇ X1)]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation10_4512_implies_Equation454 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation454 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [h10 (sK2 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK0)) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l4 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h10 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK2 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation454_4512_implies_Equation10 (G : Type*) [Magma G] (h454 : Equation454 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h454 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h454 X0 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h454 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [← h454 sK0 sK1 sK1]
  have l3 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h454 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l1 X0 (sK1 ◇ sK0)]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h454 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation10_4512_implies_Equation458 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation458 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h10 sK1 sK0]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK1) sK1]
  have l2 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1, 2]; rw [l1 sK3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ sK1)) sK1]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l2 sK2 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation458_4512_implies_Equation10 (G : Type*) [Magma G] (h458 : Equation458 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h458 (X1 ◇ X0) X0 X1 X1]
    conv => enter [1, 2]; rw [← h458 X0 X1 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h458 sK0 (X0 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation10_4512_implies_Equation4697 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4697 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 1]; rw [← h10 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0]
    conv => enter [1, 2]; rw [h10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_4697_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4697 : Equation4697 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4697 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [h4697 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) X0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) X0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) X0]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l6 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ X0) sK0]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4697 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l8 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 (sK1 ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation10_4512_implies_Equation4700 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4700 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1]; rw [h10 (sK0 ◇ sK0) sK1]
    conv => enter [1, 1]; rw [l2 sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_4700_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4700 : Equation4700 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4700 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4700 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) X0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) X0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) X0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4700 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) X0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l12 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) X0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0 sK0]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l16 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ X0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l15 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ X0) sK0]
  have l18 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4700 sK0 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l11 sK0]
  have l19 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1, 2]; rw [← l17 sK0 (X0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 (X0 ◇ sK0)]
  have l21 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation10_4512_implies_Equation4703 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4703 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h10 (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_4703_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4703 : Equation4703 G) : Equation10 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
    conv => enter [1]; rw [← h4703 X2 (X0 ◇ X1)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4703 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 X0 X1]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4703 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)))]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4703 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← l6 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))]
  have l10 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4703 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l9 sK1 sK0 X0]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (((sK1 ◇ sK0) ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 ((sK1 ◇ sK0) ◇ sK0) sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2, 2]; rw [← l8 sK0 sK1]
  have l12 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4703 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 (((sK1 ◇ sK0) ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0 sK0]
    conv => enter [1]; rw [← l17 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l20 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l12 X0]
    conv => enter [1]; rw [← h4703 X0 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l23 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l12 X0]
    conv => enter [1]; rw [l20 X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← l23 X0]
    conv => enter [1]; rw [l2 X0 X1 X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l23 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l24 X0 X1]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l25 X1 X0]
    conv => enter [1]; rw [l26 X0 X1]
  have l28 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l27 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l29 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l29 x y]

theorem Equation10_4512_implies_Equation4706 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4706 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_4706_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4706 : Equation4706 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4706 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4706 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4706 sK0 X0 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 (X0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation10_4512_implies_Equation4710 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4710 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK0]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← h10 sK0 sK0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  intro x y
  conv => enter [1]; rw [← l3 x]
  conv => enter [1, 2]; rw [l2 x y]

theorem Equation4512_4710_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4710 : Equation4710 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4710 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4710 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4710 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l12 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0 sK0]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l16 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l15 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ X0) sK0]
  have l18 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4710 sK0 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l11 sK0]
  have l19 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l11 sK0]
  have l21 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation10_4512_implies_Equation4713 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4713 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h10 sK0 sK1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_4713_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4713 : Equation4713 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4713 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4713 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4713 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))))]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4713 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) X0]
  have l16 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l15 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) X0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l18 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l16 sK0 X0 sK1]
    conv => enter [1]; rw [← l13 sK0 (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0) sK1]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 sK0]
  have l20 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l18 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0 sK0]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ X0) sK0]
  have l22 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4713 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l19 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l24 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l25 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation10_4512_implies_Equation4716 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4716 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 sK2]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← h10 sK0 sK2]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_4716_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4716 : Equation4716 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4716 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4716 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4716 sK0 X0 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation10_4512_implies_Equation4720 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4720 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ sK0) sK1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2]; rw [l4 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation4512_4720_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4720 : Equation4720 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4720 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4720 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← h4720 X2 (X0 ◇ X1)]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4720 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4720 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4720 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l4 X2 X0 X1]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) X0]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) X0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) X0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) X0]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) X0]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK0) X0]
  have l16 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l15 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1]
  have l18 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0) X0]
  have l19 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l18 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l19 sK1 sK0 X0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l20 sK1 sK0 X0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK0]
  have l23 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l22 sK0 sK1]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l22 sK0 sK1]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l26 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4720 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l25 sK1 sK0]
  have l27 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l21 sK1 sK0 sK1]
  have l28 : ∀ sK1 : G, sK1 = (sK1 ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1 sK1]
    conv => enter [1, 2]; rw [← l23 sK1 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l28 sK1]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l31 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
  have l32 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4720 X0 X0]
    conv => enter [1]; rw [l8 X0 X0 X0]
  have l33 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l32 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4720 X0 (X0 ◇ X0)]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l32 (sK0 ◇ sK0)]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1, 2]; rw [l32 sK0]
  have l36 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l32 X0]
    conv => enter [1]; rw [l33 X0]
  have l37 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l35 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1 (sK1 ◇ sK0)]
  have l39 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l36 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l36 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l40 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← l39 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l36 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l42 sK1 sK0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l43 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l46 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l45 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l46 x y]

theorem Equation10_4512_implies_Equation4723 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4723 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h10 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_4723_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4723 : Equation4723 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h4723 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h4723 X0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) X2]
    conv => enter [1, 1]; rw [← h4723 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X0))) X2]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X0)) X2]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [← l9 X0]
  have l11 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [l10 X0]
    conv => enter [1]; rw [← h4723 X0 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l10 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l16 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l10 X0]
    conv => enter [1]; rw [l11 X0]
  have l17 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l15 X0 X0]
    conv => enter [1]; rw [l16 X0]
  have l18 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1]; rw [l17 X0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l17 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l17 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l14 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1, 2]; rw [l18 (sK1 ◇ sK0)]
  have l23 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l18 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l25 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4723 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l21 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l27 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l28 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1 (sK1 ◇ sK0)]
  have l29 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l29 x y]

theorem Equation10_4512_implies_Equation4726 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4726 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h10 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK0)) sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_4726_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4726 : Equation4726 G) : Equation10 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h4726 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4726 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4726 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4726 (sK1 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4726 (sK1 ◇ sK0) sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4726 sK0 sK0 sK0]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK0]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4726 (sK0 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 sK1 sK0]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l11 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0))))]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l12 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0 sK0 sK0]
    conv => enter [1, 2, 2]; rw [← h4726 sK0 sK0 sK0]
  have l15 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l14 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l17 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4726 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X0]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4726 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2]; rw [l17 (sK1 ◇ sK0)]
  have l19 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l20 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l21 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation10_4512_implies_Equation4730 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4730 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) sK0]
  have l3 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ sK0) sK2]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l5 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l3 sK2 sK0]
    conv => enter [1, 2]; rw [l4 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l5 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK0)) sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_4730_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4730 : Equation4730 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h4730 (X1 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1, 2, 2]; rw [← h4730 X0 (X1 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) ((X1 ◇ (X0 ◇ X0)) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 ((X1 ◇ (X0 ◇ X0)) ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X0) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4730 X0 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h4730 X0 (X1 ◇ (X0 ◇ X0)) X1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l9 X0 X0]
    conv => enter [1]; rw [← h4730 X0 X0 X0]
  have l12 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← l9 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (X0 ◇ sK0))]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1]; rw [← l10 sK1 sK0 (X0 ◇ sK0)]
  have l14 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0 X0]
    conv => enter [1]; rw [l11 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l14 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l16 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4730 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l13 sK1 sK0 sK0]
  have l17 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l16 sK0 X0 sK1]
    conv => enter [1]; rw [← l15 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l18 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l19 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation10_4512_implies_Equation4734 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4734 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) sK0]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h10 (sK1 ◇ sK0) sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l4 : ∀ sK1 sK2 sK0 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h10 sK1 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK0)) sK1]
  have l5 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1, 1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1 X0]
  have l6 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [← l5 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) sK2 sK0]
  have l10 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1, 2]; rw [l10 sK1 sK0 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4512_4734_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4734 : Equation4734 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [← h4734 X0 sK0 sK1]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4734 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l3 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
  have l5 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 1]; rw [← l3 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) X1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l3 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l5 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) X1]
  have l8 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l7 X0 X1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4734 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← l11 sK0 sK1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l16 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l17 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X1]
    conv => enter [1, 1]; rw [← l14 sK0 sK1 X0]
  have l18 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l17 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l16 sK1 sK0 X0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4734 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK0 sK1]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0 (sK1 ◇ sK0)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1, 2]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4734 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l21 sK1 sK0]
  have l24 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l25 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l23 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l24 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l26 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l25 sK1 sK0 X0]
    conv => enter [1]; rw [← l24 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l22 sK0 sK1]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l30 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4734 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l29 sK1 sK0]
  have l31 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1]; rw [← l13 sK0 sK1 ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l31 sK0 sK1 X0]
    conv => enter [1]; rw [← l28 sK0 sK1 (X0 ◇ (sK1 ◇ sK0))]
  have l33 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l32 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l34 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l33 sK1 sK0 X0]
    conv => enter [1]; rw [← l24 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0 sK1]
    conv => enter [1]; rw [← l34 sK1 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1 sK0 sK0]
  have l38 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0 sK0]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [l40 sK1 sK0]
  have l42 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4734 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l41 sK1 sK0]
  have l43 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l44 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l32 sK0 sK1 sK0]
  have l45 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l46 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4734 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l38 sK0 sK1]
  have l47 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (X0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l46 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (X0 ◇ sK0)))]
  have l48 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l47 sK0 sK1 X0]
    conv => enter [1]; rw [← l45 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (X0 ◇ sK0))) sK1]
  have l49 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (X0 ◇ sK0))]
  have l50 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l49 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 sK0 (X0 ◇ sK0) sK0 sK1]
  have l51 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l44 sK0 sK0]
    conv => enter [1]; rw [l50 sK0 sK0 X0]
  have l52 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l41 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l52 x y]

theorem Equation10_4512_implies_Equation4738 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4738 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [h10 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [h10 (sK2 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK0)) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l5 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) sK0]
  have l6 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h10 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_4738_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4738 : Equation4738 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4738 (sK1 ◇ sK0) sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4738 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4738 (sK1 ◇ sK0) X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4738 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l12 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4738 (sK1 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 sK1 sK0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1]; rw [← l13 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l15 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l9 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [← l11 sK0 sK1]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l22 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ X1) = ((sK1 ◇ sK0) ◇ ((X0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [l15 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0)) X1]
  have l23 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ X1) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l22 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK0) X1]
  have l24 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2]; rw [l10 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [← h4738 X0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l25 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2]; rw [l21 sK1 sK0 X0]
    conv => enter [1]; rw [l24 X0 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l25 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l25 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← l23 sK1 sK0 sK0 sK0]
  have l29 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l25 sK0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l28 sK1 sK0]
  have l30 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l31 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) X0]
  have l32 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l31 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0 sK0]
    conv => enter [1]; rw [← l30 sK0 (sK0 ◇ X0) sK0]
  have l34 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l34 x y]

theorem Equation10_4512_implies_Equation4742 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4742 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h10 sK1 sK0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) sK1]
  have l2 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 2]; rw [h10 (sK3 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ sK1)) (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l5 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK1) sK1]
  have l6 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h10 sK1 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK3 sK0 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_4742_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4742 : Equation4742 G) : Equation10 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X4 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h4742 X4 (X0 ◇ X1) X2 X3]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4742 (sK1 ◇ sK0) sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4742 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l4 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4742 (sK1 ◇ sK0) X0 X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 sK1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l6 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l4 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← l5 sK1 sK0 (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← l5 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4742 sK0 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 sK0]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4742 X0 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X0 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation10_4512_implies_Equation4747 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4747 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h10 sK0 sK0]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
    conv => enter [1, 1, 2]; rw [← h10 sK0 sK0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 1]; rw [l3 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_4747_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4747 : Equation4747 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4747 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4747 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4747 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation10_4512_implies_Equation4750 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4750 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1, 2]; rw [h10 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_4750_implies_Equation10 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4750 : Equation4750 G) : Equation10 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4750 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4750 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))))]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK0 (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4750 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation10_4512_implies_Equation4753 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation4753 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l3 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1, 2]; rw [h10 sK0 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
    conv => enter [1, 1]; rw [← l3 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

end Semigroup5
