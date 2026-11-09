import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup4

@[equational_result]
theorem Equation310_implies_Equation3258 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation3258 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y x]

@[equational_result]
theorem Equation310_implies_Equation4270 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation4270 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h310 X0 sK0]
    conv => enter [1, 2]; rw [h310 sK0 sK1]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← h310 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h310 sK0 sK1]
    conv => enter [1]; rw [l1 sK0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation310_implies_Equation307 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h310 x x]

theorem Equation315_4512_implies_Equation3281 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation3281 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h315 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h315 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h315 (sK1 ◇ sK0) sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h315 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation315_4512_implies_Equation3284 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation3284 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [h315 (sK2 ◇ sK0) sK1]
  have l3 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h315 sK0 sK2]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [l3 sK2 sK0]
  have l5 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [l5 sK2 sK0]
  have l7 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 sK0 sK2 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation315_implies_Equation3278 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation3278 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation315_4512_implies_Equation3255 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation3255 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h315 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h315 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h315 (sK1 ◇ sK0) sK0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h315 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h315 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h315 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation315_implies_Equation4275 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [← h315 x x]
  conv => enter [1]; rw [h315 x y]

@[equational_result]
theorem Equation315_implies_Equation307 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h315 x x]

@[equational_result]
theorem Equation311_implies_Equation4271 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4271 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h311 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h311 sK0 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 x y z]

@[equational_result]
theorem Equation311_implies_Equation4287 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4287 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK0 sK1]
    conv => enter [1]; rw [h311 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation4315 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4315 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK2]
    conv => enter [1]; rw [h311 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation4339 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4339 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK2]
    conv => enter [1]; rw [h311 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation4340 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4340 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK1]
    conv => enter [1]; rw [h311 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation3267 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1]; rw [h311 x y (z ◇ w)]

@[equational_result]
theorem Equation311_implies_Equation309 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h311 x y x]

@[equational_result]
theorem Equation311_implies_Equation3260 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3260 G := by
  intro x y z
  conv => enter [1]; rw [h311 x y (x ◇ z)]

@[equational_result]
theorem Equation311_implies_Equation3265 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3265 G := by
  intro x y z
  conv => enter [1]; rw [h311 x y (z ◇ y)]

@[equational_result]
theorem Equation311_implies_Equation310 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation310 G := by
  intro x y
  conv => enter [1]; rw [h311 x y y]

@[equational_result]
theorem Equation311_implies_Equation3263 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3263 G := by
  intro x y z
  conv => enter [1]; rw [h311 x y (y ◇ z)]

@[equational_result]
theorem Equation311_implies_Equation3259 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3259 G := by
  intro x y
  conv => enter [1]; rw [h311 x y (x ◇ y)]

@[equational_result]
theorem Equation311_implies_Equation3264 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3264 G := by
  intro x y z
  conv => enter [1]; rw [h311 x y (z ◇ x)]

@[equational_result]
theorem Equation311_implies_Equation308 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h311 x x y]

@[equational_result]
theorem Equation311_implies_Equation3261 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation3261 G := by
  intro x y
  conv => enter [1]; rw [h311 x y (y ◇ x)]

@[equational_result]
theorem Equation311_implies_Equation4286 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4286 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK0 sK1]
    conv => enter [1]; rw [h311 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation4318 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4318 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK0]
    conv => enter [1]; rw [h311 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation4358 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4358 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK1 sK2]
    conv => enter [1]; rw [h311 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation4288 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4288 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h311 sK0 sK0 sK1]
    conv => enter [1]; rw [h311 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation311_implies_Equation4314 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4314 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h311 sK0 sK1 sK0]
    conv => enter [1]; rw [h311 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation311_implies_Equation4283 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4283 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h311 sK0 sK0 sK1]
    conv => enter [1]; rw [h311 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation311_implies_Equation4284 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation4284 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h311 sK0 sK0 sK1]
    conv => enter [1]; rw [h311 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation318_implies_Equation4278 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4278 G := by
  intro x y z
  conv => enter [1]; rw [← h318 x x x]
  conv => enter [1]; rw [h318 x y z]

@[equational_result]
theorem Equation318_implies_Equation4287 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4287 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h318 sK1 X0 sK0]
    conv => enter [1]; rw [h318 sK1 X1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h318 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h318 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y x z]

@[equational_result]
theorem Equation318_implies_Equation4300 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4300 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h318 sK1 sK2 sK0]
    conv => enter [1]; rw [h318 sK1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation318_implies_Equation4330 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4330 G := by
  have l0 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h318 sK0 sK2 sK1]
    conv => enter [1]; rw [h318 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y x z]

@[equational_result]
theorem Equation318_implies_Equation4340 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4340 G := by
  intro x y z
  conv => enter [1]; rw [← h318 y x y]
  conv => enter [1]; rw [h318 y x z]

@[equational_result]
theorem Equation318_implies_Equation3300 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3300 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h318 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [h318 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation318_implies_Equation309 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h318 x x y]

@[equational_result]
theorem Equation318_implies_Equation3274 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3274 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h318 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation318_implies_Equation3292 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3292 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h318 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation318_implies_Equation315 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation315 G := by
  intro x y
  conv => enter [1]; rw [h318 x y y]

@[equational_result]
theorem Equation318_implies_Equation3296 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3296 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h318 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation318_implies_Equation3264 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3264 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h318 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation318_implies_Equation3271 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3271 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h318 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation318_implies_Equation312 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h318 x y x]

@[equational_result]
theorem Equation318_implies_Equation3261 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation3261 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h318 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h318 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation318_implies_Equation4296 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4296 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h318 sK1 sK0 sK0]
    conv => enter [1]; rw [h318 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation318_implies_Equation4327 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4327 G := by
  intro x y z
  conv => enter [1]; rw [← h318 x x y]
  conv => enter [1]; rw [h318 x z x]

@[equational_result]
theorem Equation318_implies_Equation4362 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4362 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h318 sK2 X0 sK1]
    conv => enter [1]; rw [h318 sK2 X1 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h318 sK2 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [h318 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z y]

@[equational_result]
theorem Equation318_implies_Equation4304 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4304 G := by
  intro x y z
  conv => enter [1]; rw [← h318 y x x]
  conv => enter [1]; rw [h318 y z y]

@[equational_result]
theorem Equation318_implies_Equation4291 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4291 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h318 sK1 X0 sK0]
    conv => enter [1]; rw [h318 sK1 X1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x x y y]

@[equational_result]
theorem Equation318_implies_Equation4320 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4320 G := by
  intro x y
  conv => enter [1]; rw [← h318 x x y]
  conv => enter [1]; rw [h318 x y x]

@[equational_result]
theorem Equation318_implies_Equation4284 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [← h318 y x x]
  conv => enter [1]; rw [h318 y x y]

@[equational_result]
theorem Equation313_implies_Equation3259 (G : Type*) [Magma G] (h313 : Equation313 G) : Equation3259 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 sK0 sK0]
    conv => enter [1, 2]; rw [h313 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation313_implies_Equation4273 (G : Type*) [Magma G] (h313 : Equation313 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [← h313 x x]
  conv => enter [1]; rw [h313 x y]

@[equational_result]
theorem Equation313_implies_Equation307 (G : Type*) [Magma G] (h313 : Equation313 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h313 x x]

theorem Equation313_4512_implies_Equation3271 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation3271 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h313 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h313 sK0 sK0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [h313 sK1 sK1]
    conv => enter [1, 2]; rw [h313 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h313 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h313 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h313 (sK0 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← h313 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h313 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation314_implies_Equation311 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation311 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x x y z]

@[equational_result]
theorem Equation314_implies_Equation318 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation318 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h314 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation314_implies_Equation4274 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [← h314 x x x]
  conv => enter [1]; rw [h314 x y z]

@[equational_result]
theorem Equation314_implies_Equation4295 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4295 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK0 sK1]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l3 sK2 sK0 sK1]
    conv => enter [1]; rw [h314 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y y z]

@[equational_result]
theorem Equation314_implies_Equation4303 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4303 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK0 sK1]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation314_implies_Equation4344 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4344 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l2 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ sK1) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h314 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [← h314 y x y]
  conv => enter [1]; rw [l2 y y x z]

@[equational_result]
theorem Equation314_implies_Equation4345 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4345 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l2 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [h314 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← h314 y x y]
  conv => enter [1]; rw [l2 y y z x]

@[equational_result]
theorem Equation314_implies_Equation3277 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3277 G := by
  intro x y z w
  conv => enter [1]; rw [h314 x y (z ◇ w)]

@[equational_result]
theorem Equation314_implies_Equation3291 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3291 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h314 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [h314 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation314_implies_Equation313 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h314 x y y]

@[equational_result]
theorem Equation314_implies_Equation319 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation319 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h314 sK2 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z y]

@[equational_result]
theorem Equation314_implies_Equation3273 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3273 G := by
  intro x y z
  conv => enter [1]; rw [h314 x y (y ◇ z)]

@[equational_result]
theorem Equation314_implies_Equation3290 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3290 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h314 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation314_implies_Equation3275 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3275 G := by
  intro x y z
  conv => enter [1]; rw [h314 x y (z ◇ y)]

@[equational_result]
theorem Equation314_implies_Equation3289 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3289 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h314 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation314_implies_Equation4364 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4364 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h314 X1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h314 X0 X1 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0 X1]
    conv => enter [1]; rw [← h314 X1 X0 X1]
  have l2 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h314 sK1 X0 sK2]
    conv => enter [1]; rw [h314 sK1 X1 sK2]
  have l3 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l2 (sK1 ◇ sK2) sK1 sK2 sK0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l3 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [h314 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z y]

@[equational_result]
theorem Equation314_implies_Equation316 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation316 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h314 y y y]

@[equational_result]
theorem Equation314_implies_Equation317 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation317 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation314_implies_Equation320 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation320 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h314 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h314 sK2 X0 sK2]
  have l3 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l2 X0 X0 sK2]
    conv => enter [1]; rw [← h314 sK2 X0 sK2]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x z]
  conv => enter [1]; rw [h314 z y z]

@[equational_result]
theorem Equation314_implies_Equation3270 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3270 G := by
  intro x y z
  conv => enter [1]; rw [h314 x y (x ◇ z)]

@[equational_result]
theorem Equation314_implies_Equation3272 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3272 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h314 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [h314 sK1 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation314_implies_Equation3276 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3276 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h314 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h314 sK2 X0 sK2]
  have l3 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l2 X0 X0 sK2]
    conv => enter [1]; rw [← h314 sK2 X0 sK2]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h314 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [h314 sK2 sK0 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [l5 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation314_implies_Equation3279 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3279 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h314 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation314_implies_Equation3280 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3280 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h314 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation314_implies_Equation3283 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3283 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h314 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation314_implies_Equation3285 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3285 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK1 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation314_implies_Equation3293 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3293 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h314 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [h314 sK1 sK2 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation314_implies_Equation3298 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3298 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h314 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h314 sK2 X0 sK2]
  have l3 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l2 X0 X0 sK2]
    conv => enter [1]; rw [← h314 sK2 X0 sK2]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h314 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [h314 sK2 sK2 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [l5 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation314_implies_Equation40 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation40 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation314_implies_Equation3269 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3269 G := by
  intro x y
  conv => enter [1]; rw [h314 x y (x ◇ y)]

@[equational_result]
theorem Equation314_implies_Equation3282 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3282 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h314 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [h314 sK1 sK1 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l5 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation314_implies_Equation3294 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3294 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK2 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h314 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation314_implies_Equation3297 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation3297 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h314 sK2 sK2 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h314 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation314_implies_Equation4301 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4301 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK0 sK1]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation314_implies_Equation4331 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4331 G := by
  intro x y z
  conv => enter [1]; rw [← h314 y x x]
  conv => enter [1]; rw [h314 y z y]

@[equational_result]
theorem Equation314_implies_Equation4305 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4305 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK0 sK1]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation314_implies_Equation4325 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4325 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h314 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h314 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h314 sK2 X0 sK2]
  have l2 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1]
    conv => enter [1]; rw [h314 sK1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 z x y x]
  conv => enter [1]; rw [h314 z y z]

@[equational_result]
theorem Equation314_implies_Equation4369 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4369 G := by
  have l0 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h314 sK1 sK2 sK0]
    conv => enter [1]; rw [h314 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z z]

@[equational_result]
theorem Equation314_implies_Equation4279 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4279 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h314 sK2 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← h314 x x x]
  conv => enter [1]; rw [l2 x y z y]

@[equational_result]
theorem Equation314_implies_Equation4299 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4299 G := by
  intro x y z
  conv => enter [1]; rw [← h314 x x y]
  conv => enter [1]; rw [h314 x z x]

@[equational_result]
theorem Equation314_implies_Equation4297 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4297 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h314 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h314 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h314 sK2 X0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1]; rw [h314 z y z]

@[equational_result]
theorem Equation314_implies_Equation4277 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4277 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← h314 x x x]
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation314_implies_Equation4280 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4280 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h314 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h314 sK2 X0 sK2]
  have l3 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l2 X0 X0 sK2]
    conv => enter [1]; rw [← h314 sK2 X0 sK2]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← h314 x x x]
  conv => enter [1]; rw [l4 x z]
  conv => enter [1]; rw [h314 z y z]

@[equational_result]
theorem Equation314_implies_Equation4293 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4293 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h314 sK0 sK0 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK0 sK1]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation314_implies_Equation4321 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4321 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h314 sK0 sK1 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK1]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h314 sK0 sK1 sK1]
    conv => enter [1]; rw [h314 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h314 sK0 sK1 sK1]
  have l2 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l2 X0 X0 sK1 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 X0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l3 sK1 sK1 sK0]
    conv => enter [1]; rw [h314 sK1 X0 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y y]

@[equational_result]
theorem Equation314_implies_Equation4343 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4343 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← h314 y x y]
  conv => enter [1]; rw [l4 y x]
  conv => enter [1]; rw [h314 x y x]

@[equational_result]
theorem Equation314_implies_Equation4290 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [← h314 x x y]
  conv => enter [1]; rw [h314 x y x]

@[equational_result]
theorem Equation314_implies_Equation4276 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation4276 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← h314 x x x]
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h314 y y y]

@[equational_result]
theorem Equation315_implies_Equation3261 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation3261 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1, 2]; rw [h315 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation310_4512_implies_Equation3261 (G : Type*) [Magma G] (h310 : Equation310 G) (h4512 : Equation4512 G) : Equation3261 G := by
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
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h310 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h310 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [l6 X0 X1 sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l11 sK0]
    conv => enter [1]; rw [← l6 X0 sK0 sK0]
  have l15 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l0 X1 X0 X0]
    conv => enter [1, 2]; rw [l6 X0 X0 sK0]
  have l16 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l15 X1 X0 sK0]
    conv => enter [1]; rw [l10 X1 X0 sK0 X0]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l13 X0 sK0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l17 X0 X1 X0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK1 sK0]
    conv => enter [1]; rw [← h310 sK1 sK0]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ sK1) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0 X0]
    conv => enter [1]; rw [← l18 sK1 X0]
  have l22 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l21 sK1 sK0 X0]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l22 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l24 x y]

@[equational_result]
theorem Equation316_implies_Equation320 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation320 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK2 X0]
  have l1 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h316 sK2 sK2]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK2]
  have l3 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l2 X0 X1 sK2]
    conv => enter [1, 2, 2]; rw [l0 sK2 sK0]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  have l5 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l3 sK2 X1 sK2 sK0]
  have l6 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l5 sK2 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK2]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 X1 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation316_implies_Equation3272 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation3272 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l1 : ∀ X1 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (sK1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK1]
  have l2 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [← l1 X1 sK1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h316 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation316_implies_Equation3276 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation3276 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK2 X0]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h316 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  have l3 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h316 sK2 sK2]
  have l4 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK2]
  have l5 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l4 X0 X1 sK2]
    conv => enter [1, 2, 2]; rw [l0 sK2 sK0]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l3 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  have l7 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l5 sK2 X1 sK2 sK0]
  have l8 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l7 sK2 X1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 X1 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation316_implies_Equation3293 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation3293 G := by
  have l0 : ∀ X1 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK1]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 sK0 X1]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h316 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 X0 sK0]
    conv => enter [1, 2]; rw [l2 X0 sK0]
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation316_implies_Equation3298 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation3298 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h316 sK2 sK2]
    conv => enter [1]; rw [h316 sK2 X0]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l0 sK2 X0]
    conv => enter [1, 2]; rw [h316 X0 sK2]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h316 sK2 sK2]
    conv => enter [1]; rw [l1 sK2 X0]
    conv => enter [1, 2]; rw [← h316 sK2 sK2]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [h316 sK0 sK2]
    conv => enter [1]; rw [← h316 sK2 sK2]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1]
    conv => enter [1, 2]; rw [h316 sK2 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [l4 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation316_implies_Equation40 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation40 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation316_implies_Equation3282 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation3282 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h316 sK0 sK1]
    conv => enter [1]; rw [← h316 sK1 sK1]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h316 sK1 sK1]
    conv => enter [1, 2]; rw [h316 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation316_implies_Equation310 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation310 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h316 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation316_implies_Equation312 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation312 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h316 X0 sK0]
    conv => enter [1]; rw [← h316 sK0 sK0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation316_implies_Equation4280 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation4280 G := by
  have l0 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l0 X1 sK0]
    conv => enter [1]; rw [← h316 sK0 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [h316 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1]
    conv => enter [1, 2]; rw [← h316 sK0 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h316 sK2 sK0]
    conv => enter [1, 2]; rw [← h316 sK0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← h316 x x]
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation316_implies_Equation4343 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation4343 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h316 sK1 sK1]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h316 X0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l4 y x]
  conv => enter [1]; rw [l3 y x]

@[equational_result]
theorem Equation316_implies_Equation4276 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation4276 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h316 sK1 sK1]
    conv => enter [1]; rw [h316 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation316_4512_implies_Equation317 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation317 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation316_4512_implies_Equation3279 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3279 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l10 x y (x ◇ y)]

theorem Equation316_4512_implies_Equation3280 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3280 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [l10 x y (x ◇ z)]

theorem Equation316_4512_implies_Equation3283 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3283 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 X1 X2]
    conv => enter [1, 1]; rw [h316 X1 X0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l3 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l1 X2 sK0]
    conv => enter [1]; rw [l4 X2 X2 sK0]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l8 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l7 X1 X2 X0]
    conv => enter [1]; rw [l4 X0 (X0 ◇ X2) sK0]
  have l9 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l8 X1 X2 sK0 X1]
    conv => enter [1]; rw [← l6 sK0 (X1 ◇ X2)]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation316_4512_implies_Equation3285 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3285 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [l10 x y (z ◇ y)]

theorem Equation316_4512_implies_Equation315 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation315 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l10 x y x]

theorem Equation316_4512_implies_Equation308 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l10 x x y]

theorem Equation316_4512_implies_Equation4277 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4277 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l1 sK0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h316 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X1]
    conv => enter [1, 2]; rw [← h316 sK0 sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l4 X0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h316 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 X0 X0]
    conv => enter [1]; rw [← l8 sK0 X0 X0]
  have l10 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l9 X0 sK0]
    conv => enter [1]; rw [l5 X0 X0 sK0]
  have l12 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1]; rw [l5 X1 (X1 ◇ X2) sK0]
  have l13 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l12 X0 X2 sK0 sK0]
  have l14 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l13 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [← h316 x x]
  conv => enter [1]; rw [l14 x y z]

theorem Equation316_4512_implies_Equation4293 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation4293 G := by
  have l0 : ∀ X0 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X2
    conv => enter [1]; rw [← h316 X0 X0]
    conv => enter [1]; rw [h316 X0 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l1 X2 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l1 sK1 X0]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l5 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X2)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← l2 X1 X1 X2]
    conv => enter [1]; rw [l4 X1 sK0 sK1]
  have l6 : ∀ sK0 sK1 X1 X0 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ X1) = (sK0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ X0) X1]
  have l7 : ∀ sK0 sK1 X1 X0 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ X1) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X1]
    conv => enter [1]; rw [l7 sK0 sK1 X1 X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 sK0 sK1 X0 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 (sK0 ◇ sK1) sK1 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l13 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l4 X0 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← l14 sK0 sK1 X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 X0]
  have l18 : ∀ X0 X1 sK0 sK1 : G, ((X0 ◇ X0) ◇ X1) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 1]; rw [l13 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X1]
  have l19 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l17 sK0 sK1 X1]
    conv => enter [1]; rw [← l18 X0 X1 sK0 sK1]
  have l20 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l19 sK0 sK1 X0 X1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation317_implies_Equation316 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h317 x y y]

@[equational_result]
theorem Equation317_implies_Equation3270 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation3270 G := by
  have l0 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK0 sK2]
  have l1 : ∀ sK0 sK2 X1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [← h317 sK0 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK2]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h317 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 X1]
    conv => enter [1, 2]; rw [← h317 sK0 sK0 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [h317 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation317_implies_Equation3269 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation3269 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h317 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h317 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 X1]
    conv => enter [1, 2]; rw [← h317 sK0 sK0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [h317 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation317_implies_Equation3297 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation3297 G := by
  have l0 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK2 sK1]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h317 sK0 X0 X0]
  have l2 : ∀ sK2 sK1 X1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 X1 sK0
    conv => enter [1]; rw [← h317 sK2 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h317 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h317 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation317_implies_Equation3263 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation3263 G := by
  have l0 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← h317 sK1 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 X1 sK1 sK2]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h317 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 X1]
    conv => enter [1, 2]; rw [← h317 sK0 sK0 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1, 2]; rw [h317 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation317_implies_Equation3296 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation3296 G := by
  have l0 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK2 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← h317 sK0 X0 sK0]
  have l2 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [← h317 sK2 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h317 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h317 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation317_implies_Equation4299 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation4299 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h317 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h317 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation317_implies_Equation4297 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation4297 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h317 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h317 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation317_implies_Equation4288 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation4288 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h317 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h317 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation317_implies_Equation4304 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation4304 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h317 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h317 sK1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation317_implies_Equation4284 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation4284 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h317 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h317 sK1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation317_implies_Equation4290 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation4290 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h317 X0 X1 X1]
    conv => enter [1, 2]; rw [h317 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h317 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h317 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation320_implies_Equation316 (G : Type*) [Magma G] (h320 : Equation320 G) : Equation316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h320 sK0 sK0 sK0]
    conv => enter [1]; rw [← h320 sK1 sK0 sK0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h320 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation319_implies_Equation313 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h319 x y x]

@[equational_result]
theorem Equation319_implies_Equation309 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h319 x x y]

@[equational_result]
theorem Equation319_implies_Equation3290 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation3290 G := by
  have l0 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK2 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← h319 sK0 X0 sK0]
  have l2 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [← h319 sK2 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h319 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h319 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation319_implies_Equation316 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h319 x y y]

@[equational_result]
theorem Equation319_implies_Equation3265 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation3265 G := by
  have l0 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK1 sK2]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h319 sK0 X0 X0]
  have l2 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [← h319 sK1 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h319 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [h319 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation319_implies_Equation3274 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation3274 G := by
  have l0 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK0 sK2]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 X0]
    conv => enter [1, 2]; rw [← h319 sK0 sK0 X0]
  have l2 : ∀ sK0 sK2 X1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [← h319 sK0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h319 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h319 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation319_implies_Equation3294 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation3294 G := by
  have l0 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK2 sK1]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h319 sK0 X0 X0]
  have l2 : ∀ sK2 sK1 X1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 X1 sK0
    conv => enter [1]; rw [← h319 sK2 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h319 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h319 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation319_implies_Equation4331 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation4331 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h319 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h319 sK1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation319_implies_Equation4325 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation4325 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h319 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h319 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation319_implies_Equation4318 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation4318 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h319 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h319 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation319_implies_Equation4327 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation4327 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h319 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h319 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation319_implies_Equation4279 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation4279 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h319 sK1 sK1 sK2]
    conv => enter [1]; rw [h319 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

@[equational_result]
theorem Equation319_implies_Equation4314 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation4314 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h319 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h319 sK1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation319_implies_Equation4320 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation4320 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h319 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h319 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation319_implies_Equation4321 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation4321 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h319 sK0 sK0 sK1]
    conv => enter [1]; rw [h319 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation319_4512_implies_Equation3273 (G : Type*) [Magma G] (h319 : Equation319 G) (h4512 : Equation4512 G) : Equation3273 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h319 X0 X0 X0]
    conv => enter [1]; rw [← h319 X1 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h319 X1 X1 X2]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l1 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 X0 X0 sK0]
    conv => enter [1]; rw [l2 X0 X0 sK0]
  have l5 : ∀ sK0 X2 X3 X4 : G, (sK0 ◇ sK0) = (X2 ◇ ((X3 ◇ X2) ◇ X4)) := by
    intro sK0 X2 X3 X4
    conv => enter [1]; rw [l4 sK0 X4]
    conv => enter [1]; rw [← l3 X2 X3 X4 sK0]
  have l6 : ∀ sK0 X2 X3 X4 : G, (sK0 ◇ sK0) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro sK0 X2 X3 X4
    conv => enter [1]; rw [l5 sK0 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X2 X4]
  intro x y z
  conv => enter [1]; rw [l6 x y x z]

theorem Equation319_4512_implies_Equation3260 (G : Type*) [Magma G] (h319 : Equation319 G) (h4512 : Equation4512 G) : Equation3260 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h319 X0 X0 X0]
    conv => enter [1]; rw [← h319 X1 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h319 X1 X1 X2]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l1 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 X0 X0 sK0]
    conv => enter [1]; rw [l2 X0 X0 sK0]
  have l5 : ∀ sK0 X2 X3 X4 : G, (sK0 ◇ sK0) = (X2 ◇ ((X3 ◇ X2) ◇ X4)) := by
    intro sK0 X2 X3 X4
    conv => enter [1]; rw [l4 sK0 X4]
    conv => enter [1]; rw [← l3 X2 X3 X4 sK0]
  have l6 : ∀ sK0 X2 X3 X4 : G, (sK0 ◇ sK0) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro sK0 X2 X3 X4
    conv => enter [1]; rw [l5 sK0 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X2 X4]
  intro x y z
  conv => enter [1]; rw [l6 x x y z]

theorem Equation319_4512_implies_Equation3292 (G : Type*) [Magma G] (h319 : Equation319 G) (h4512 : Equation4512 G) : Equation3292 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h319 X0 X0 X0]
    conv => enter [1]; rw [← h319 X1 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h319 X1 X1 X2]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l1 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 X0 X0 sK0]
    conv => enter [1]; rw [l2 X0 X0 sK0]
  have l5 : ∀ sK0 X2 X3 X4 : G, (sK0 ◇ sK0) = (X2 ◇ ((X3 ◇ X2) ◇ X4)) := by
    intro sK0 X2 X3 X4
    conv => enter [1]; rw [l4 sK0 X4]
    conv => enter [1]; rw [← l3 X2 X3 X4 sK0]
  have l6 : ∀ sK0 X2 X3 X4 : G, (sK0 ◇ sK0) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro sK0 X2 X3 X4
    conv => enter [1]; rw [l5 sK0 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X2 X4]
  intro x y z
  conv => enter [1]; rw [l6 x y z x]

theorem Equation319_4512_implies_Equation4301 (G : Type*) [Magma G] (h319 : Equation319 G) (h4512 : Equation4512 G) : Equation4301 G := by
  have l0 : ∀ X1 X2 sK2 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro X1 X2 sK2 sK0
    conv => enter [1]; rw [← h319 X1 X1 X2]
    conv => enter [1]; rw [h319 X1 sK2 sK0]
  have l1 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK2 sK0]
  have l2 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [← h319 sK2 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 X1 sK2 sK0]
  have l3 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h319 X0 sK2 sK0]
  have l4 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l5 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l2 sK2 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK2 sK1 X0]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ sK1)]
  have l7 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l2 sK2 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK2 sK1 X0]
  have l8 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK1) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l7 sK2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l3 (sK0 ◇ (sK0 ◇ sK1)) sK1 sK2 sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l8 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation319_4512_implies_Equation4305 (G : Type*) [Magma G] (h319 : Equation319 G) (h4512 : Equation4512 G) : Equation4305 G := by
  have l0 : ∀ X1 X2 sK2 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X1 X2 sK2 sK1
    conv => enter [1]; rw [← h319 X1 X1 X2]
    conv => enter [1]; rw [h319 X1 sK2 sK1]
  have l1 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK2 sK1]
  have l2 : ∀ sK2 sK1 X1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X1
    conv => enter [1]; rw [← h319 sK2 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 X1 sK2 sK1]
  have l3 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h319 X0 sK2 sK1]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK2) sK1]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1 sK2]
    conv => enter [1]; rw [l5 sK2 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l6 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation319_4512_implies_Equation4286 (G : Type*) [Magma G] (h319 : Equation319 G) (h4512 : Equation4512 G) : Equation4286 G := by
  have l0 : ∀ X1 X2 sK0 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro X1 X2 sK0 sK2
    conv => enter [1]; rw [← h319 X1 X1 X2]
    conv => enter [1]; rw [h319 X1 sK0 sK2]
  have l1 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK0 sK2]
  have l2 : ∀ sK0 sK2 X1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [← h319 sK0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 X1 sK0 sK2]
  have l3 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h319 X0 sK0 sK2]
  have l4 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l5 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 sK2 sK1 X0]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l5 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ sK1)]
  have l7 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK2 sK0]
    conv => enter [1]; rw [l6 sK0 sK2 sK1 X0]
  have l8 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l7 sK0 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l3 (sK0 ◇ (sK0 ◇ sK1)) sK1 sK0 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l8 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation319_4512_implies_Equation4296 (G : Type*) [Magma G] (h319 : Equation319 G) (h4512 : Equation4512 G) : Equation4296 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h319 X1 X1 X2]
    conv => enter [1]; rw [h319 X1 sK1 sK2]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h319 X0 sK1 sK2]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

theorem Equation319_4512_implies_Equation4291 (G : Type*) [Magma G] (h319 : Equation319 G) (h4512 : Equation4512 G) : Equation4291 G := by
  have l0 : ∀ X1 X2 sK1 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK1 sK0
    conv => enter [1]; rw [← h319 X1 X1 X2]
    conv => enter [1]; rw [h319 X1 sK1 sK0]
  have l1 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h319 X0 sK1 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation319_4512_implies_Equation4283 (G : Type*) [Magma G] (h319 : Equation319 G) (h4512 : Equation4512 G) : Equation4283 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h319 X1 X1 X2]
    conv => enter [1]; rw [h319 X1 sK0 sK1]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h319 X0 X1 X1]
    conv => enter [1, 2]; rw [h319 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← h319 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 X1 sK0 sK1]
  have l3 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h319 X0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation322_implies_Equation38 (G : Type*) [Magma G] (h322 : Equation322 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h322 X0 X1]
    conv => enter [1]; rw [← h322 X0 X2]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h322 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation336_implies_Equation39 (G : Type*) [Magma G] (h336 : Equation336 G) : Equation39 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h336 sK0 sK0]
    conv => enter [1]; rw [← h336 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation323_implies_Equation3306 (G : Type*) [Magma G] (h323 : Equation323 G) : Equation3306 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h323 sK0 sK1]
    conv => enter [1, 2]; rw [h323 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation323_implies_Equation307 (G : Type*) [Magma G] (h323 : Equation323 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h323 x x]

@[equational_result]
theorem Equation326_implies_Equation3319 (G : Type*) [Magma G] (h326 : Equation326 G) : Equation3319 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h326 sK0 sK1]
    conv => enter [1, 2]; rw [h326 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation326_implies_Equation307 (G : Type*) [Magma G] (h326 : Equation326 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h326 x x]

@[equational_result]
theorem Equation325_implies_Equation3316 (G : Type*) [Magma G] (h325 : Equation325 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 sK0 sK1]
    conv => enter [1, 2]; rw [h325 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation325_implies_Equation307 (G : Type*) [Magma G] (h325 : Equation325 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h325 x x]

theorem Equation333_4512_implies_Equation3316 (G : Type*) [Magma G] (h333 : Equation333 G) (h4512 : Equation4512 G) : Equation3316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h333 X0 X1]
    conv => enter [1]; rw [h333 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h333 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h333 X0 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [h333 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation333_implies_Equation307 (G : Type*) [Magma G] (h333 : Equation333 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h333 x x]

@[equational_result]
theorem Equation327_implies_Equation3317 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3317 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (x ◇ z)]

@[equational_result]
theorem Equation327_implies_Equation3320 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3320 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (y ◇ z)]

@[equational_result]
theorem Equation327_implies_Equation3321 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3321 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (z ◇ x)]

@[equational_result]
theorem Equation327_implies_Equation3323 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3323 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (z ◇ z)]

@[equational_result]
theorem Equation327_implies_Equation325 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation325 G := by
  intro x y
  conv => enter [1]; rw [h327 x y x]

@[equational_result]
theorem Equation327_implies_Equation3318 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3318 G := by
  intro x y
  conv => enter [1]; rw [h327 x y (y ◇ x)]

@[equational_result]
theorem Equation327_implies_Equation3322 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3322 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (z ◇ y)]

@[equational_result]
theorem Equation327_implies_Equation3315 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3315 G := by
  intro x y
  conv => enter [1]; rw [h327 x y (x ◇ x)]

@[equational_result]
theorem Equation327_implies_Equation4315 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation4315 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h327 sK0 sK1 sK2]
    conv => enter [1]; rw [h327 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

@[equational_result]
theorem Equation327_implies_Equation4339 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation4339 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h327 sK0 sK1 sK2]
    conv => enter [1]; rw [h327 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

@[equational_result]
theorem Equation327_implies_Equation326 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation326 G := by
  intro x y
  conv => enter [1]; rw [h327 x y y]

@[equational_result]
theorem Equation327_implies_Equation308 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h327 x x y]

@[equational_result]
theorem Equation327_implies_Equation4314 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation4314 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h327 sK0 sK1 sK0]
    conv => enter [1]; rw [h327 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation343_implies_Equation3363 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation3363 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation343_implies_Equation3380 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation3380 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation343_implies_Equation3397 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation3397 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation343_implies_Equation3414 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation3414 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation343_implies_Equation333 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation333 G := by
  intro x y
  conv => enter [1]; rw [h343 x y y]

@[equational_result]
theorem Equation343_implies_Equation3326 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation343_implies_Equation3343 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation3343 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h343 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation343_implies_Equation3353 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation3353 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h343 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation343_implies_Equation4300 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation4300 G := by
  intro x y z
  conv => enter [1]; rw [← h343 x y x]
  conv => enter [1]; rw [h343 x y z]

@[equational_result]
theorem Equation343_implies_Equation4330 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation4330 G := by
  intro x y z
  conv => enter [1]; rw [← h343 y x x]
  conv => enter [1]; rw [h343 y x z]

@[equational_result]
theorem Equation343_implies_Equation323 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation323 G := by
  intro x y
  conv => enter [1]; rw [h343 x y x]

@[equational_result]
theorem Equation343_implies_Equation312 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h343 x x y]

@[equational_result]
theorem Equation343_implies_Equation4291 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation4291 G := by
  intro x y
  conv => enter [1]; rw [← h343 x y x]
  conv => enter [1]; rw [h343 x y y]

@[equational_result]
theorem Equation329_implies_Equation3312 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3312 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h329 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation329_implies_Equation3330 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3330 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK1]
    conv => enter [1]; rw [h329 sK0 (sK1 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation329_implies_Equation3334 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3334 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h329 sK2 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation329_implies_Equation3322 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3322 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK2]
    conv => enter [1]; rw [h329 sK0 (sK2 ◇ sK1) sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation329_implies_Equation3326 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK0]
    conv => enter [1]; rw [h329 sK0 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation329_implies_Equation3309 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3309 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h329 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h329 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation329_implies_Equation4287 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation4287 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h329 sK0 (sK2 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h329 sK0 sK1 sK2]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h329 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h329 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l2 x z y]

@[equational_result]
theorem Equation329_implies_Equation4340 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation4340 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h329 sK0 sK1 sK2]
    conv => enter [1]; rw [h329 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 x z y]

@[equational_result]
theorem Equation329_implies_Equation323 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation323 G := by
  intro x y
  conv => enter [1]; rw [h329 x y x]

@[equational_result]
theorem Equation329_implies_Equation326 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation326 G := by
  intro x y
  conv => enter [1]; rw [h329 x y y]

@[equational_result]
theorem Equation329_implies_Equation3316 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h329 sK0 sK1 sK0]
    conv => enter [1]; rw [h329 sK0 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation329_implies_Equation309 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h329 x x y]

@[equational_result]
theorem Equation329_implies_Equation3264 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3264 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK0 sK2]
    conv => enter [1]; rw [h329 sK0 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation329_implies_Equation3261 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3261 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h329 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [h329 sK1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation329_implies_Equation4284 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [← h329 x y x]
  conv => enter [1]; rw [h329 x y y]

@[equational_result]
theorem Equation332_implies_Equation3342 (G : Type*) [Magma G] (h332 : Equation332 G) : Equation3342 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h332 sK0 sK1]
    conv => enter [1, 2]; rw [h332 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation332_implies_Equation326 (G : Type*) [Magma G] (h332 : Equation332 G) : Equation326 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h332 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h332 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h332 sK1 sK1]
    conv => enter [1]; rw [← l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h332 sK1 X0]
    conv => enter [1]; rw [l1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h332 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK1 (X0 ◇ X0)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [← h332 X0 sK1]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [h332 sK1 X0]
    conv => enter [1]; rw [l4 X0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h332 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation332_4512_implies_Equation43 (G : Type*) [Magma G] (h332 : Equation332 G) (h4512 : Equation4512 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h332 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h332 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h332 X0 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h332 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h332 X0 X1]
    conv => enter [1]; rw [l3 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h332 X0 X1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h332 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation332_implies_Equation4343 (G : Type*) [Magma G] (h332 : Equation332 G) : Equation4343 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h332 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h332 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h332 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h332 sK0 X0]
    conv => enter [1]; rw [l1 X0 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h332 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 (sK1 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h332 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h332 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation335_4512_implies_Equation3355 (G : Type*) [Magma G] (h335 : Equation335 G) (h4512 : Equation4512 G) : Equation3355 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h335 (sK1 ◇ sK0) sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [h335 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h335 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 1]; rw [← h335 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h335 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK1)]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h335 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h335 sK0 sK1]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation335_4512_implies_Equation323 (G : Type*) [Magma G] (h335 : Equation335 G) (h4512 : Equation4512 G) : Equation323 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 sK1]
    conv => enter [1, 2]; rw [h335 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h335 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← h335 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation335_4512_implies_Equation43 (G : Type*) [Magma G] (h335 : Equation335 G) (h4512 : Equation4512 G) : Equation43 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h335 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h335 sK1 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h335 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK1)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h335 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 sK1]
    conv => enter [1]; rw [← l17 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation335_4512_implies_Equation4293 (G : Type*) [Magma G] (h335 : Equation335 G) (h4512 : Equation4512 G) : Equation4293 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 sK0]
    conv => enter [1, 2]; rw [h335 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h335 (sK1 ◇ sK0) sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h335 (sK0 ◇ sK1) sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h335 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h335 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 1]; rw [h335 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h335 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l16 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l17 x y]
  conv => enter [1]; rw [h335 x y]

@[equational_result]
theorem Equation333_implies_Equation3353 (G : Type*) [Magma G] (h333 : Equation333 G) : Equation3353 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h333 sK0 sK1]
    conv => enter [1, 2]; rw [h333 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation325_4512_implies_Equation3315 (G : Type*) [Magma G] (h325 : Equation325 G) (h4512 : Equation4512 G) : Equation3315 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h325 (sK0 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation335_implies_Equation3343 (G : Type*) [Magma G] (h335 : Equation335 G) : Equation3343 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 sK1]
    conv => enter [1, 2]; rw [h335 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation332_4512_implies_Equation3318 (G : Type*) [Magma G] (h332 : Equation332 G) (h4512 : Equation4512 G) : Equation3318 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h332 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h332 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h332 X0 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h332 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h332 X0 X1]
    conv => enter [1]; rw [l3 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h332 X0 X1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h332 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation412_implies_Equation3 (G : Type*) [Magma G] (h412 : Equation412 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h412 X0 X0]
    conv => enter [1]; rw [← h412 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation463_4512_implies_Equation3 (G : Type*) [Magma G] (h463 : Equation463 G) (h4512 : Equation4512 G) : Equation3 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h463 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 X2 : G, (X0 ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h463 X2 X0]
    conv => enter [1]; rw [l0 X0 X0 X2]
  intro x
  conv => enter [1]; rw [← l1 x x]

@[equational_result]
theorem Equation413_implies_Equation411 (G : Type*) [Magma G] (h413 : Equation413 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h413 x x]

@[equational_result]
theorem Equation426_implies_Equation411 (G : Type*) [Magma G] (h426 : Equation426 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h426 x x]

@[equational_result]
theorem Equation414_implies_Equation411 (G : Type*) [Magma G] (h414 : Equation414 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h414 x x]

@[equational_result]
theorem Equation500_implies_Equation411 (G : Type*) [Magma G] (h500 : Equation500 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h500 x x]

@[equational_result]
theorem Equation416_implies_Equation411 (G : Type*) [Magma G] (h416 : Equation416 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h416 x x]

@[equational_result]
theorem Equation417_implies_Equation411 (G : Type*) [Magma G] (h417 : Equation417 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h417 x x]

@[equational_result]
theorem Equation473_implies_Equation411 (G : Type*) [Magma G] (h473 : Equation473 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h473 x x]

@[equational_result]
theorem Equation418_implies_Equation48 (G : Type*) [Magma G] (h418 : Equation418 G) : Equation48 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h418 X0 X0 X0]
    conv => enter [1]; rw [← h418 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h418 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [l0 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation418_implies_Equation417 (G : Type*) [Magma G] (h418 : Equation418 G) : Equation417 G := by
  intro x y
  conv => enter [1]; rw [h418 x y y]

@[equational_result]
theorem Equation418_implies_Equation416 (G : Type*) [Magma G] (h418 : Equation418 G) : Equation416 G := by
  intro x y
  conv => enter [1]; rw [h418 x y x]

theorem Equation483_4512_implies_Equation62 (G : Type*) [Magma G] (h483 : Equation483 G) (h4512 : Equation4512 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h483 (X0 ◇ X0) X1 X0]
    conv => enter [1, 2]; rw [← h483 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 X1 X2]
  have l2 : ∀ X2 X1 X3 X0 : G, (X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1)))) = X1 := by
    intro X2 X1 X3 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h483 X1 X2 X3]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 X1 X0 X2 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (X2 ◇ sK0))) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [h483 (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h483 sK0 (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) X1]
  have l5 : ∀ sK0 X1 X0 X2 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)))) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l4 sK0 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 sK0 (X1 ◇ (sK0 ◇ sK0)) (X2 ◇ sK0)]
  have l6 : ∀ sK0 X1 : G, sK0 = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l2 sK0 sK0 (X1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l5 sK0 X1 sK0 sK0]
  have l7 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation483_4512_implies_Equation473 (G : Type*) [Magma G] (h483 : Equation483 G) (h4512 : Equation4512 G) : Equation473 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h483 (X0 ◇ X0) X1 X0]
    conv => enter [1, 2]; rw [← h483 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 X1 X2]
  have l2 : ∀ X2 X1 X3 X0 : G, (X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1)))) = X1 := by
    intro X2 X1 X3 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h483 X1 X2 X3]
  have l3 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h483 (sK1 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l1 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0 sK1]
  have l5 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h483 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l1 (sK0 ◇ sK0) (sK0 ◇ sK0) sK1]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK0 sK1]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l6 sK0 X0 sK1]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l8 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (X0 ◇ (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h483 ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))]
  have l9 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l8 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (X1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK1]
    conv => enter [1]; rw [← l9 sK1 sK0 sK1 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK0 sK1]
  have l15 : ∀ sK0 X1 X0 X2 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (X2 ◇ sK0))) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [h483 (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h483 sK0 (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) X1]
  have l16 : ∀ sK0 X1 X0 X2 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)))) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l15 sK0 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 sK0 (X1 ◇ (sK0 ◇ sK0)) (X2 ◇ sK0)]
  have l17 : ∀ sK0 X1 : G, sK0 = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l2 sK0 sK0 (X1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l16 sK0 X1 sK0 sK0]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 (sK0 ◇ sK0) sK1]
  have l19 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l19 x]
  conv => enter [1]; rw [l14 x y]

theorem Equation483_4512_implies_Equation416 (G : Type*) [Magma G] (h483 : Equation483 G) (h4512 : Equation4512 G) : Equation416 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h483 (X0 ◇ X0) X1 X0]
    conv => enter [1, 2]; rw [← h483 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 X1 X2]
  have l2 : ∀ X2 X1 X3 X0 : G, (X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1)))) = X1 := by
    intro X2 X1 X3 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h483 X1 X2 X3]
  have l3 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h483 (sK1 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l1 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [l1 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l5 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (X0 ◇ (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h483 ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))]
  have l6 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l5 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (X1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK1]
    conv => enter [1]; rw [← l6 sK1 sK0 sK1 sK1]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l8 sK1 sK0 sK0]
  have l10 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h483 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 (sK0 ◇ sK0) sK1]
  have l11 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l10 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l12 x y]
  conv => enter [1]; rw [l9 y x]

@[equational_result]
theorem Equation419_implies_Equation411 (G : Type*) [Magma G] (h419 : Equation419 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h419 x x]

@[equational_result]
theorem Equation436_implies_Equation411 (G : Type*) [Magma G] (h436 : Equation436 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h436 x x]

@[equational_result]
theorem Equation420_implies_Equation411 (G : Type*) [Magma G] (h420 : Equation420 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h420 x x]

@[equational_result]
theorem Equation510_implies_Equation411 (G : Type*) [Magma G] (h510 : Equation510 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h510 x x]

@[equational_result]
theorem Equation422_implies_Equation413 (G : Type*) [Magma G] (h422 : Equation422 G) : Equation413 G := by
  intro x y
  conv => enter [1]; rw [h422 x x y]

@[equational_result]
theorem Equation422_implies_Equation416 (G : Type*) [Magma G] (h422 : Equation422 G) : Equation416 G := by
  intro x y
  conv => enter [1]; rw [h422 x y x]

@[equational_result]
theorem Equation422_implies_Equation419 (G : Type*) [Magma G] (h422 : Equation422 G) : Equation419 G := by
  intro x y
  conv => enter [1]; rw [h422 x y y]

@[equational_result]
theorem Equation446_implies_Equation416 (G : Type*) [Magma G] (h446 : Equation446 G) : Equation416 G := by
  intro x y
  conv => enter [1]; rw [h446 x x y]

@[equational_result]
theorem Equation446_implies_Equation426 (G : Type*) [Magma G] (h446 : Equation446 G) : Equation426 G := by
  intro x y
  conv => enter [1]; rw [h446 x y x]

@[equational_result]
theorem Equation446_implies_Equation436 (G : Type*) [Magma G] (h446 : Equation446 G) : Equation436 G := by
  intro x y
  conv => enter [1]; rw [h446 x y y]

@[equational_result]
theorem Equation427_implies_Equation411 (G : Type*) [Magma G] (h427 : Equation427 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h427 x x]

@[equational_result]
theorem Equation466_implies_Equation411 (G : Type*) [Magma G] (h466 : Equation466 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h466 x x]

@[equational_result]
theorem Equation428_implies_Equation9 (G : Type*) [Magma G] (h428 : Equation428 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h428 X0 X0 X0]
    conv => enter [1]; rw [← h428 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h428 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation469_4512_implies_Equation13 (G : Type*) [Magma G] (h469 : Equation469 G) (h4512 : Equation4512 G) : Equation13 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X2)))]
    conv => enter [1]; rw [← h469 X2 (X0 ◇ X1) X3]
  have l1 : ∀ sK0 X0 X1 : G, sK0 = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h469 sK0 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l2 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← h469 sK0 sK0 sK0]
  have l3 : ∀ X0 X2 : G, (X0 ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h469 X2 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X2 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation429_implies_Equation411 (G : Type*) [Magma G] (h429 : Equation429 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h429 x x]

@[equational_result]
theorem Equation430_implies_Equation8 (G : Type*) [Magma G] (h430 : Equation430 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h430 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h430 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation503_4512_implies_Equation8 (G : Type*) [Magma G] (h503 : Equation503 G) (h4512 : Equation4512 G) : Equation8 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h503 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h503 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2]; rw [← l5 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h503 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ X0)))]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0))) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK0 ◇ X0))]
    conv => enter [1]; rw [← h503 X0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (sK0 ◇ X0))]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l12 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h503 sK0 sK0]
    conv => enter [1, 2, 2, 2]; rw [l11 sK0 sK0]
  have l13 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1, 2, 2]; rw [l11 sK0 sK0]
  intro x
  conv => enter [1]; rw [l13 x]

@[equational_result]
theorem Equation432_implies_Equation413 (G : Type*) [Magma G] (h432 : Equation432 G) : Equation413 G := by
  intro x y
  conv => enter [1]; rw [h432 x x y]

@[equational_result]
theorem Equation432_implies_Equation426 (G : Type*) [Magma G] (h432 : Equation432 G) : Equation426 G := by
  intro x y
  conv => enter [1]; rw [h432 x y x]

@[equational_result]
theorem Equation432_implies_Equation429 (G : Type*) [Magma G] (h432 : Equation432 G) : Equation429 G := by
  intro x y
  conv => enter [1]; rw [h432 x y y]

theorem Equation433_4512_implies_Equation430 (G : Type*) [Magma G] (h433 : Equation433 G) (h4512 : Equation4512 G) : Equation430 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h433 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h433 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X0 X2]
    conv => enter [1]; rw [← h433 X1 (X2 ◇ X0) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l2 X1 X2 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h433 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x (y ◇ (x ◇ (y ◇ y)))]

theorem Equation433_4512_implies_Equation427 (G : Type*) [Magma G] (h433 : Equation433 G) (h4512 : Equation4512 G) : Equation427 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h433 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h433 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X0 X2]
    conv => enter [1]; rw [← h433 X1 (X2 ◇ X0) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l2 X1 X2 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h433 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x (y ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation433_implies_Equation10 (G : Type*) [Magma G] (h433 : Equation433 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h433 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h433 X1 (X0 ◇ X1) (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation541_implies_Equation503 (G : Type*) [Magma G] (h541 : Equation541 G) : Equation503 G := by
  intro x y
  conv => enter [1]; rw [h541 x y y]

@[equational_result]
theorem Equation541_implies_Equation466 (G : Type*) [Magma G] (h541 : Equation541 G) : Equation466 G := by
  intro x y
  conv => enter [1]; rw [h541 x y x]

theorem Equation541_4512_implies_Equation10 (G : Type*) [Magma G] (h541 : Equation541 G) (h4512 : Equation4512 G) : Equation10 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h541 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h541 X0 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h541 sK0 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l0 X0 sK0]
  have l4 : ∀ X1 X3 X0 X2 : G, (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := by
    intro X1 X3 X0 X2
    conv => enter [1, 2, 2]; rw [l1 X0 (X1 ◇ X2) X2]
    conv => enter [1]; rw [← h541 X2 X1 X3]
  have l5 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ ((X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h541 (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 X1 sK1]
  have l6 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l5 X1 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l7 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l6 X1 sK0 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [l0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l8 : ∀ sK0 X1 sK1 : G, sK0 = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← l4 sK0 sK0 X1 sK0]
    conv => enter [1]; rw [← l7 X1 sK0 sK1 sK0]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h541 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK0 X0 sK1]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [l0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l11 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l10 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0 sK0]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation434_4512_implies_Equation430 (G : Type*) [Magma G] (h434 : Equation434 G) (h4512 : Equation4512 G) : Equation430 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h434 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h434 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h434 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h434 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x (y ◇ (x ◇ (y ◇ y)))]

end Semigroup4
