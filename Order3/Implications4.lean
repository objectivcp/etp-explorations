import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation231_364_implies_Equation5 (G : Type*) [Magma G] (h231 : Equation231 G) (h364 : Equation364 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h231 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h364 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h364 X0 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation108_308_implies_Equation4 (G : Type*) [Magma G] (h108 : Equation108 G) (h308 : Equation308 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h108 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h308 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h308 X0 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation231_360_implies_Equation2 (G : Type*) [Magma G] (h231 : Equation231 G) (h360 : Equation360 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h360 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation108_312_implies_Equation2 (G : Type*) [Magma G] (h108 : Equation108 G) (h312 : Equation312 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h108 X1 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h312 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation231_280_implies_Equation5 (G : Type*) [Magma G] (h231 : Equation231 G) (h280 : Equation280 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h280 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1, 1]; rw [h231 X1 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l1 X1]
    conv => enter [1]; rw [← h231 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation50_108_implies_Equation4 (G : Type*) [Magma G] (h50 : Equation50 G) (h108 : Equation108 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h50 X1 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1, 2]; rw [h108 X1 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 X1]
    conv => enter [1]; rw [← h108 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation231_264_implies_Equation283 (G : Type*) [Magma G] (h231 : Equation231 G) (h264 : Equation264 G) : Equation283 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h231 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h264 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation75_108_implies_Equation56 (G : Type*) [Magma G] (h75 : Equation75 G) (h108 : Equation108 G) : Equation56 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h108 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation221_367_implies_Equation5 (G : Type*) [Magma G] (h221 : Equation221 G) (h367 : Equation367 G) : Equation5 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h367 X1 X0]
    conv => enter [1]; rw [h367 X1 X2]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h367 X2 X1]
    conv => enter [1, 1]; rw [h367 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, (((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X1) = X1 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l0 X0 (X1 ◇ (X2 ◇ X2)) X2]
    conv => enter [1]; rw [← h221 X1 (X2 ◇ X2)]
  have l3 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l1 X1 X1 (X1 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l2 X1 X1 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h367 X0 X1]
    conv => enter [1]; rw [l3 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l3 X1]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation105_310_implies_Equation4 (G : Type*) [Magma G] (h105 : Equation105 G) (h310 : Equation310 G) : Equation4 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← h310 X1 X0]
    conv => enter [1]; rw [h310 X1 X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h310 X2 X1]
    conv => enter [1, 2]; rw [h310 X1 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [l0 ((X2 ◇ X2) ◇ X1) X0 X2]
    conv => enter [1]; rw [← h105 X1 (X2 ◇ X2)]
  have l3 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l1 X1 ((X1 ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [l2 X1 X1 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [l3 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation221_364_implies_Equation211 (G : Type*) [Magma G] (h221 : Equation221 G) (h364 : Equation364 G) : Equation211 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h364 X0 X1]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← h364 (X0 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← l1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h221 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation105_308_implies_Equation107 (G : Type*) [Magma G] (h105 : Equation105 G) (h308 : Equation308 G) : Equation107 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h308 X0 X1]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← h308 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← l1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h105 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation221_360_implies_Equation2 (G : Type*) [Magma G] (h221 : Equation221 G) (h360 : Equation360 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h360 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h360 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l1 X0 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation105_312_implies_Equation2 (G : Type*) [Magma G] (h105 : Equation105 G) (h312 : Equation312 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h312 X0 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← h105 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h312 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l1 X0 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation221_280_implies_Equation257 (G : Type*) [Magma G] (h221 : Equation221 G) (h280 : Equation280 G) : Equation257 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h280 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h280 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← l0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ X1) X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 X2 : G, ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ X0) ◇ X1)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l4 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l4 (X0 ◇ X0) X0 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [l5 X0]
    conv => enter [1, 2, 2]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X1]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2, 1]; rw [l5 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h221 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 x y]
  conv => enter [1, 1, 1]; rw [← l5 x]

theorem Equation50_105_implies_Equation52 (G : Type*) [Magma G] (h50 : Equation50 G) (h105 : Equation105 G) : Equation52 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h50 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h50 (X1 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h50 X2 (X1 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l4 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l4 X0 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [l5 X0]
    conv => enter [1, 1, 1]; rw [l5 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1]
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1, 2]; rw [l5 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 x y]
  conv => enter [1, 2, 2]; rw [← l5 x]

theorem Equation221_264_implies_Equation14 (G : Type*) [Magma G] (h221 : Equation221 G) (h264 : Equation264 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l1 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ X0) ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l2 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation221_264_implies_Equation66 (G : Type*) [Magma G] (h221 : Equation221 G) (h264 : Equation264 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ X2) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 (X1 ◇ X2) X2]
  have l4 : ∀ X1 X2 X0 : G, (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 1, 2]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h221 X2 (X1 ◇ X2)]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [l3 X1 X2 X0]
    conv => enter [1]; rw [l5 X2]
  have l8 : ∀ X2 : G, (X2 ◇ X2) = X2 := by
    intro X2
    conv => enter [1, 1]; rw [← l7 X2 X2 X2]
    conv => enter [1]; rw [l4 X2 X2 X2]
  intro x y
  conv => enter [1]; rw [← l6 y x]
  conv => enter [1, 2, 2]; rw [← l8 y]

theorem Equation221_264_implies_Equation115 (G : Type*) [Magma G] (h221 : Equation221 G) (h264 : Equation264 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ X2) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 (X1 ◇ X2) X2]
  have l4 : ∀ X1 X2 X0 : G, (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 1, 2]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h221 X2 (X1 ◇ X2)]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [l3 X1 X2 X0]
    conv => enter [1]; rw [l5 X2]
  have l8 : ∀ X2 : G, (X2 ◇ X2) = X2 := by
    intro X2
    conv => enter [1, 1]; rw [← l7 X2 X2 X2]
    conv => enter [1]; rw [l4 X2 X2 X2]
  intro x y
  conv => enter [1]; rw [← l8 x]
  conv => enter [1]; rw [← l6 y (x ◇ x)]

theorem Equation221_264_implies_Equation219 (G : Type*) [Magma G] (h221 : Equation221 G) (h264 : Equation264 G) : Equation219 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 ((X0 ◇ X2) ◇ X2) X2]
    conv => enter [1, 2]; rw [← h264 X0 X2]
  have l5 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ X2) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [l0 (X1 ◇ X2) X2]
  have l6 : ∀ X1 X2 X0 : G, (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 1, 2]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h221 X2 (X1 ◇ X2)]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l3 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ X0) ◇ X0)]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l7 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [l7 X0]
  have l10 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1]; rw [l7 X2]
  have l11 : ∀ X2 : G, (X2 ◇ X2) = X2 := by
    intro X2
    conv => enter [1, 1]; rw [← l10 X2 X2 X2]
    conv => enter [1]; rw [l6 X2 X2 X2]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l7 X1]
  have l13 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [← l8 X0 ((X0 ◇ X2) ◇ X2)]
    conv => enter [1]; rw [l4 X0 X0 X2]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l8 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l13 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l12 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1]; rw [← l15 y (x ◇ x)]
  conv => enter [1]; rw [← l14 (y ◇ (x ◇ x)) y]

theorem Equation221_264_implies_Equation335 (G : Type*) [Magma G] (h221 : Equation221 G) (h264 : Equation264 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 ((X0 ◇ X2) ◇ X2) X2]
    conv => enter [1, 2]; rw [← h264 X0 X2]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l3 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [l5 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l5 X1]
  have l9 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [← l6 X0 ((X0 ◇ X2) ◇ X2)]
    conv => enter [1]; rw [l4 X0 X0 X2]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l8 (X1 ◇ X0) X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l9 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l6 (X1 ◇ (X1 ◇ X0)) X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l13 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l10 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X1]
    conv => enter [1, 2]; rw [l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [l11 ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 2, 2]; rw [l11 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 2, 2]; rw [l12 X1 (X0 ◇ (X0 ◇ X1))]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l12 X0 X1]
    conv => enter [1]; rw [← l18 X1 X0]
  intro x y
  conv => enter [1]; rw [l19 x y]
  conv => enter [1, 2]; rw [← l11 y x]

theorem Equation221_264_implies_Equation384 (G : Type*) [Magma G] (h221 : Equation221 G) (h264 : Equation264 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 ((X0 ◇ X2) ◇ X2) X2]
    conv => enter [1, 2]; rw [← h264 X0 X2]
  have l4 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ X0) ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X2) ◇ X2)]
    conv => enter [1]; rw [l3 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation221_264_implies_Equation124 (G : Type*) [Magma G] (h221 : Equation221 G) (h264 : Equation264 G) : Equation124 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 ((X0 ◇ X2) ◇ X2) X2]
    conv => enter [1, 2]; rw [← h264 X0 X2]
  have l4 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ X0) ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X2) ◇ X2)]
    conv => enter [1]; rw [l3 X0 X0 X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l6 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 2, 2]; rw [← l5 x y]
  conv => enter [1, 2]; rw [← l7 (y ◇ x) x]

theorem Equation221_264_implies_Equation206 (G : Type*) [Magma G] (h221 : Equation221 G) (h264 : Equation264 G) : Equation206 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 ((X0 ◇ X2) ◇ X2) X2]
    conv => enter [1, 2]; rw [← h264 X0 X2]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l3 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [l5 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l5 X1]
  have l9 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [← l6 X0 ((X0 ◇ X2) ◇ X2)]
    conv => enter [1]; rw [l4 X0 X0 X2]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l8 (X1 ◇ X0) X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l9 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l6 (X1 ◇ (X1 ◇ X0)) X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l13 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l10 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X1]
    conv => enter [1, 2]; rw [l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [l11 ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 2, 2]; rw [l11 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 2, 2]; rw [l12 X1 (X0 ◇ (X0 ◇ X1))]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l12 X0 X1]
    conv => enter [1]; rw [← l18 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]
  conv => enter [1, 2]; rw [l19 x y]
  conv => enter [1]; rw [← l11 (x ◇ (x ◇ y)) y]

theorem Equation221_264_implies_Equation313 (G : Type*) [Magma G] (h221 : Equation221 G) (h264 : Equation264 G) : Equation313 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ X2) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 (X1 ◇ X2) X2]
  have l4 : ∀ X1 X2 X0 : G, (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 1, 2]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h221 X2 (X1 ◇ X2)]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [l3 X1 X2 X0]
    conv => enter [1]; rw [l5 X2]
  have l8 : ∀ X2 : G, (X2 ◇ X2) = X2 := by
    intro X2
    conv => enter [1, 1]; rw [← l7 X2 X2 X2]
    conv => enter [1]; rw [l4 X2 X2 X2]
  intro x y
  conv => enter [1]; rw [l8 x]
  conv => enter [1]; rw [← l6 y x]

theorem Equation75_105_implies_Equation14 (G : Type*) [Magma G] (h75 : Equation75 G) (h105 : Equation105 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l5 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l5 X1]
  have l9 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l6 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l4 X2 X2 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l9 X0 X1]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l10 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x y]
  conv => enter [1]; rw [← l10 y (x ◇ y)]

theorem Equation75_105_implies_Equation66 (G : Type*) [Magma G] (h75 : Equation75 G) (h105 : Equation105 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l5 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [l0 (X2 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h105 X2 (X2 ◇ X1)]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ (X0 ◇ X0))]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l7 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l7 X0]
  have l10 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [l7 X2]
  have l11 : ∀ X2 : G, (X2 ◇ X2) = X2 := by
    intro X2
    conv => enter [1, 2]; rw [← l10 X2 X2 X2]
    conv => enter [1]; rw [l6 X2 X2 X2]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l7 X1]
  have l13 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l8 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l4 X2 X2 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l13 X0 X1]
    conv => enter [1]; rw [l12 (X0 ◇ X1) X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l13 X0 X1]
  have l16 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l15 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l16 X0 X1]
    conv => enter [1]; rw [l8 ((X0 ◇ X1) ◇ X1) X1]
  have l18 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l17 X0 X1]
  have l19 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l14 (((X1 ◇ X0) ◇ X0) ◇ X1) X1]
    conv => enter [1, 1]; rw [l18 X1 X0]
  have l20 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1]; rw [l15 X0 (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))]
  have l21 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = (((((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1, 1, 1]; rw [l15 X1 (((X1 ◇ X0) ◇ X0) ◇ X1)]
  have l22 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1, 1, 1]; rw [l16 ((X1 ◇ X0) ◇ X0) X1]
  have l23 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l16 X1 X0]
    conv => enter [1]; rw [← l22 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1, 1]; rw [l23 y x]
  conv => enter [1, 1, 1, 1, 1]; rw [← l11 y]
  conv => enter [1, 1, 1]; rw [← l15 x (y ◇ y)]
  conv => enter [1]; rw [← l15 y (x ◇ (y ◇ y))]

theorem Equation75_105_implies_Equation115 (G : Type*) [Magma G] (h75 : Equation75 G) (h105 : Equation105 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l5 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [l0 (X2 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h105 X2 (X2 ◇ X1)]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ (X0 ◇ X0))]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l7 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l7 X0]
  have l10 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [l7 X2]
  have l11 : ∀ X2 : G, (X2 ◇ X2) = X2 := by
    intro X2
    conv => enter [1, 2]; rw [← l10 X2 X2 X2]
    conv => enter [1]; rw [l6 X2 X2 X2]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l7 X1]
  have l13 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l8 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l4 X2 X2 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l13 X0 X1]
  have l15 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l14 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1]; rw [← l15 (x ◇ x) y]
  conv => enter [1]; rw [← l14 y ((x ◇ x) ◇ y)]

theorem Equation75_105_implies_Equation219 (G : Type*) [Magma G] (h75 : Equation75 G) (h105 : Equation105 G) : Equation219 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l3 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 (X2 ◇ X1) X2]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h105 X2 (X2 ◇ X1)]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [l5 X2]
  have l8 : ∀ X2 : G, (X2 ◇ X2) = X2 := by
    intro X2
    conv => enter [1, 2]; rw [← l7 X2 X2 X2]
    conv => enter [1]; rw [l4 X2 X2 X2]
  intro x y
  conv => enter [1]; rw [← l8 x]
  conv => enter [1]; rw [← l6 y (x ◇ x)]

theorem Equation75_105_implies_Equation335 (G : Type*) [Magma G] (h75 : Equation75 G) (h105 : Equation105 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l5 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X2 X2 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation75_105_implies_Equation384 (G : Type*) [Magma G] (h75 : Equation75 G) (h105 : Equation105 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l5 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l5 X1]
  have l9 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l6 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l4 X2 X2 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l8 (X0 ◇ X1) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l9 X0 X1]
  have l12 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l11 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [l6 ((X0 ◇ X1) ◇ X1) X1]
  have l14 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l10 (((X1 ◇ X0) ◇ X0) ◇ X1) X1]
    conv => enter [1, 1]; rw [l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [l11 X0 (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))]
  have l17 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = (((((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 1, 1]; rw [l11 X1 (((X1 ◇ X0) ◇ X0) ◇ X1)]
  have l18 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 1, 1]; rw [l12 ((X1 ◇ X0) ◇ X0) X1]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [← l18 X1 X0]
  intro x y
  conv => enter [1]; rw [l19 x y]
  conv => enter [1, 1]; rw [← l11 y x]

theorem Equation75_105_implies_Equation124 (G : Type*) [Magma G] (h75 : Equation75 G) (h105 : Equation105 G) : Equation124 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l5 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l5 X1]
  have l9 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l6 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l4 X2 X2 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l8 (X0 ◇ X1) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l9 X0 X1]
  have l12 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l11 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [l6 ((X0 ◇ X1) ◇ X1) X1]
  have l14 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l10 (((X1 ◇ X0) ◇ X0) ◇ X1) X1]
    conv => enter [1, 1]; rw [l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [l11 X0 (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))]
  have l17 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = (((((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 1, 1]; rw [l11 X1 (((X1 ◇ X0) ◇ X0) ◇ X1)]
  have l18 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 1, 1]; rw [l12 ((X1 ◇ X0) ◇ X0) X1]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [← l18 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]
  conv => enter [1, 1]; rw [l19 y x]
  conv => enter [1]; rw [← l11 y ((y ◇ x) ◇ x)]

theorem Equation75_105_implies_Equation206 (G : Type*) [Magma G] (h75 : Equation75 G) (h105 : Equation105 G) : Equation206 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l5 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X2 X2 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 1, 1]; rw [← l5 x y]
  conv => enter [1, 1]; rw [← l7 x (x ◇ y)]

theorem Equation75_105_implies_Equation313 (G : Type*) [Magma G] (h75 : Equation75 G) (h105 : Equation105 G) : Equation313 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [l0 (X2 ◇ X1) X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h105 X2 (X2 ◇ X1)]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l6 X0]
  have l8 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l6 X2]
  have l9 : ∀ X2 : G, (X2 ◇ X2) = X2 := by
    intro X2
    conv => enter [1, 2]; rw [← l8 X2 X2 X2]
    conv => enter [1]; rw [l5 X2 X2 X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l6 X1]
  intro x y
  conv => enter [1]; rw [l9 x]
  conv => enter [1]; rw [← l10 y x]

theorem Equation219_359_implies_Equation14 (G : Type*) [Magma G] (h219 : Equation219 G) (h359 : Equation359 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h219 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h359 (X0 ◇ X0)]
    conv => enter [1]; rw [← h219 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h359 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h219 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l3 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation219_359_implies_Equation66 (G : Type*) [Magma G] (h219 : Equation219 G) (h359 : Equation359 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h219 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h359 (X0 ◇ X0)]
    conv => enter [1]; rw [← h219 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h359 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h219 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l3 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]
  conv => enter [1, 2, 2]; rw [← l3 y]

theorem Equation219_359_implies_Equation115 (G : Type*) [Magma G] (h219 : Equation219 G) (h359 : Equation359 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h219 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h359 (X0 ◇ X0)]
    conv => enter [1]; rw [← h219 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h359 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h219 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l3 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x]
  conv => enter [1]; rw [← l6 y (x ◇ x)]

theorem Equation219_359_implies_Equation313 (G : Type*) [Magma G] (h219 : Equation219 G) (h359 : Equation359 G) : Equation313 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h219 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h359 (X0 ◇ X0)]
    conv => enter [1]; rw [← h219 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h359 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h219 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l3 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x]
  conv => enter [1]; rw [← l6 y x]

theorem Equation115_307_implies_Equation14 (G : Type*) [Magma G] (h115 : Equation115 G) (h307 : Equation307 G) : Equation14 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h307 (X0 ◇ X0)]
    conv => enter [1]; rw [← h115 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h307 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h115 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h115 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation115_307_implies_Equation66 (G : Type*) [Magma G] (h115 : Equation115 G) (h307 : Equation307 G) : Equation66 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h307 (X0 ◇ X0)]
    conv => enter [1]; rw [← h115 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h307 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h115 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h115 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2, 2]; rw [← l2 y]

theorem Equation115_307_implies_Equation219 (G : Type*) [Magma G] (h115 : Equation115 G) (h307 : Equation307 G) : Equation219 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h115 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h115 X1 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h307 (X0 ◇ X0)]
    conv => enter [1]; rw [← h115 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h307 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h115 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l3 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x]
  conv => enter [1]; rw [← l6 y (x ◇ x)]

theorem Equation219_255_implies_Equation14 (G : Type*) [Magma G] (h219 : Equation219 G) (h255 : Equation255 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h219 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h219 X0 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h219 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h255 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l3 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation47_115_implies_Equation14 (G : Type*) [Magma G] (h47 : Equation47 G) (h115 : Equation115 G) : Equation14 G := by
  have l0 : ∀ X0 : G, (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h47 (X0 ◇ X0)]
    conv => enter [1]; rw [← h115 X0 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h115 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h47 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h115 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation219_221_231_implies_Equation2 (G : Type*) [Magma G] (h219 : Equation219 G) (h221 : Equation221 G) (h231 : Equation231 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h219 X0 (X1 ◇ ((X0 ◇ X0) ◇ X1))]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h231 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h219 X0 (X1 ◇ (X1 ◇ X1))]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h221 X0 (X0 ◇ X0)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l3 X1]
    conv => enter [1]; rw [← h231 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [l3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 1]; rw [← l3 X0]
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l3 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation105_108_115_implies_Equation2 (G : Type*) [Magma G] (h105 : Equation105 G) (h108 : Equation108 G) (h115 : Equation115 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h105 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h115 X0 ((X1 ◇ (X0 ◇ X0)) ◇ X1)]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h108 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h115 X0 ((X1 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h105 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l3 X1]
    conv => enter [1]; rw [← h108 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [l3 X0]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1, 2]; rw [← l3 X0]
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation211_364_367_implies_Equation5 (G : Type*) [Magma G] (h211 : Equation211 G) (h364 : Equation364 G) (h367 : Equation367 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h211 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h364 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h211 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1]; rw [← h364 (X0 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← l0 X0]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h367 X2 X1]
    conv => enter [1, 1]; rw [h367 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h211 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h367 (X0 ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← l0 X0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0 X0 X0]
    conv => enter [1]; rw [← h211 X0 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [l7 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X1]
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l7 X1]
  intro x y
  conv => enter [1]; rw [← l9 y x]

theorem Equation107_308_310_implies_Equation4 (G : Type*) [Magma G] (h107 : Equation107 G) (h308 : Equation308 G) (h310 : Equation310 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h107 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h308 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h107 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2]; rw [← h308 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← l0 X0]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h310 X2 X1]
    conv => enter [1, 2]; rw [h310 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h107 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h310 (X0 ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [← l0 X0]
  have l6 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l3 X2 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2]; rw [← l2 X1 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0 X0 X0]
    conv => enter [1]; rw [← h107 X0 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [l7 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l7 X1]
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l7 X1]
  intro x y
  conv => enter [1]; rw [← l9 x y]

theorem Equation211_283_implies_Equation5 (G : Type*) [Magma G] (h211 : Equation211 G) (h283 : Equation283 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h211 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h283 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation56_107_implies_Equation4 (G : Type*) [Magma G] (h56 : Equation56 G) (h107 : Equation107 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h107 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h56 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h56 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation211_231_359_implies_Equation5 (G : Type*) [Magma G] (h211 : Equation211 G) (h231 : Equation231 G) (h359 : Equation359 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h211 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h359 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h359 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation107_108_307_implies_Equation4 (G : Type*) [Magma G] (h107 : Equation107 G) (h108 : Equation108 G) (h307 : Equation307 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h107 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h307 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h307 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation211_231_255_implies_Equation5 (G : Type*) [Magma G] (h211 : Equation211 G) (h231 : Equation231 G) (h255 : Equation255 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h211 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h255 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation47_107_108_implies_Equation4 (G : Type*) [Magma G] (h47 : Equation47 G) (h107 : Equation107 G) (h108 : Equation108 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h47 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h107 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h47 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation211_219_implies_Equation2 (G : Type*) [Magma G] (h211 : Equation211 G) (h219 : Equation219 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h219 X0 X1]
    conv => enter [1]; rw [← h211 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation107_115_implies_Equation2 (G : Type*) [Magma G] (h107 : Equation107 G) (h115 : Equation115 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h115 X0 X1]
    conv => enter [1]; rw [← h107 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation209_359_implies_Equation3 (G : Type*) [Magma G] (h209 : Equation209 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h359 X0]
    conv => enter [1, 2, 2]; rw [← h359 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l0 X0 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation117_307_implies_Equation3 (G : Type*) [Magma G] (h117 : Equation117 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h307 X0]
    conv => enter [1, 1, 1]; rw [← h307 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l0 X0 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation209_283_implies_Equation231 (G : Type*) [Magma G] (h209 : Equation209 G) (h283 : Equation283 G) : Equation231 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h283 X0 X1]
    conv => enter [1]; rw [← h209 X0 ((X1 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [← l0 ((X0 ◇ X0) ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [l1 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h283 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation209_283_implies_Equation151 (G : Type*) [Magma G] (h209 : Equation209 G) (h283 : Equation283 G) : Equation151 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h283 X0 X1]
    conv => enter [1]; rw [← h209 X0 ((X1 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [← l0 ((X0 ◇ X0) ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [l1 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h283 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation56_117_implies_Equation108 (G : Type*) [Magma G] (h56 : Equation56 G) (h117 : Equation117 G) : Equation108 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h56 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X1 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [← l0 (X0 ◇ X0) ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [l1 (X0 ◇ X0) X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h56 X0 (X0 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h56 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation56_117_implies_Equation151 (G : Type*) [Magma G] (h56 : Equation56 G) (h117 : Equation117 G) : Equation151 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h56 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X1 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [← l0 (X0 ◇ X0) ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [l1 (X0 ◇ X0) X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h56 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l3 x]

theorem Equation209_280_implies_Equation211 (G : Type*) [Magma G] (h209 : Equation209 G) (h280 : Equation280 G) : Equation211 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h280 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h280 X0 X1]
    conv => enter [1]; rw [← h209 X0 ((X1 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l0 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h280 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l3 X1 (X0 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l4 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [h209 x x]
  conv => enter [1, 1, 2]; rw [l6 x y]

theorem Equation209_280_implies_Equation40 (G : Type*) [Magma G] (h209 : Equation209 G) (h280 : Equation280 G) : Equation40 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h280 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h280 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h280 X0 X1]
    conv => enter [1]; rw [← h209 X0 ((X1 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l0 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h280 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l3 X1 (X0 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l4 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation50_117_implies_Equation107 (G : Type*) [Magma G] (h50 : Equation50 G) (h117 : Equation117 G) : Equation107 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h50 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h50 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l3 (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 (X0 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l4 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [h117 x x]
  conv => enter [1, 2, 1]; rw [l6 x y]

theorem Equation50_117_implies_Equation40 (G : Type*) [Magma G] (h50 : Equation50 G) (h117 : Equation117 G) : Equation40 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h50 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h50 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l3 (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 (X0 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l4 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation209_231_255_implies_Equation283 (G : Type*) [Magma G] (h209 : Equation209 G) (h231 : Equation231 G) (h255 : Equation255 G) : Equation283 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2, 2]; rw [h255 X0]
    conv => enter [1, 1]; rw [h255 X0]
    conv => enter [1]; rw [l0 ((X0 ◇ X0) ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [h231 x y]
  conv => enter [1, 1]; rw [l1 y]

theorem Equation47_108_117_implies_Equation56 (G : Type*) [Magma G] (h47 : Equation47 G) (h108 : Equation108 G) (h117 : Equation117 G) : Equation56 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1, 1]; rw [h47 X0]
    conv => enter [1, 2]; rw [h47 X0]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X0 ◇ X0))]
  intro x y
  conv => enter [1]; rw [h108 x y]
  conv => enter [1, 2]; rw [l1 y]

theorem Equation209_221_implies_Equation2 (G : Type*) [Magma G] (h209 : Equation209 G) (h221 : Equation221 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h209 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation105_117_implies_Equation2 (G : Type*) [Magma G] (h105 : Equation105 G) (h117 : Equation117 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h117 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation203_209_219_implies_Equation231 (G : Type*) [Magma G] (h203 : Equation203 G) (h209 : Equation209 G) (h219 : Equation219 G) : Equation231 G := by
  have l0 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h209 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 1, 2]; rw [← h203 sK1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h219 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X1 ◇ (X0 ◇ X0))]
  have l3 : ∀ X0 sK1 : G, ((X0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 1, 2]; rw [h219 sK1 X0]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 1]; rw [← h203 sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (((X0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h209 (X0 ◇ (sK1 ◇ sK1)) (X0 ◇ sK1)]
    conv => enter [1, 1, 2]; rw [l3 X0 sK1]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l5 X0 sK1]
    conv => enter [1, 1]; rw [← h219 sK1 X0]
  have l7 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h209 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 1, 2]; rw [← l4 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 1]; rw [h219 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l7 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h209 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 1, 2]; rw [← l8 sK1]
  have l10 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h209 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1, 1, 2]; rw [← l9 sK1]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1, 1]; rw [← l8 sK1]
  have l12 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [← l2 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 1]; rw [← l0 sK1]
  have l13 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h209 ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) sK1]
    conv => enter [1, 1, 2]; rw [← l12 sK1]
  have l14 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 1]; rw [h219 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l13 sK1]
  have l15 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h203 sK1]
    conv => enter [1]; rw [l14 sK1]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 1]; rw [← l15 sK1]
    conv => enter [1, 2, 2]; rw [← l15 sK1]
  have l17 : ∀ sK1 : G, (sK1 ◇ sK1) = (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1]
    conv => enter [1]; rw [← l6 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  have l18 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2, 2]; rw [l17 sK1]
    conv => enter [1, 1]; rw [l17 sK1]
    conv => enter [1]; rw [l1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
  have l19 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1]; rw [l18 sK1]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h219 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1, 2]; rw [← l19 sK1]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0))]
    conv => enter [1, 1]; rw [← h209 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0))]
    conv => enter [1, 1]; rw [← l21 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [← h209 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l23 x y]

theorem Equation99_115_117_implies_Equation108 (G : Type*) [Magma G] (h99 : Equation99 G) (h115 : Equation115 G) (h117 : Equation117 G) : Equation108 G := by
  have l0 : ∀ sK1 : G, sK1 = (((sK1 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h117 sK1 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← h99 sK1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h115 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X0) ◇ X1)]
  have l3 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ (sK1 ◇ X0)) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 1]; rw [h115 sK1 X0]
    conv => enter [1]; rw [← h117 X0 ((sK1 ◇ sK1) ◇ X0)]
  have l4 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [← l3 sK1 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [← h99 sK1]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ X0) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h117 ((sK1 ◇ sK1) ◇ X0) (sK1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l3 sK1 X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ X0) ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1, 2]; rw [← h115 sK1 X0]
  have l7 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h117 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) sK1]
    conv => enter [1, 2, 1]; rw [← l4 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [h115 sK1 ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1]; rw [← l7 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h117 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2, 1]; rw [← l8 sK1]
  have l10 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h117 ((sK1 ◇ sK1) ◇ sK1) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 1]; rw [← l9 sK1]
  have l11 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1, 2]; rw [← l8 sK1]
  have l12 : ∀ sK1 : G, (sK1 ◇ sK1) = (((((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [← l2 ((sK1 ◇ sK1) ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK1]
  have l13 : ∀ sK1 : G, ((((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h117 ((((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2, 1]; rw [← l12 sK1]
  have l14 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [h115 ((sK1 ◇ sK1) ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l13 sK1]
  have l15 : ∀ sK1 : G, sK1 = ((((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h99 sK1]
    conv => enter [1]; rw [l14 sK1]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [← l1 (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l15 sK1]
    conv => enter [1, 1, 1]; rw [← l15 sK1]
  have l17 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1]
    conv => enter [1]; rw [← l6 sK1 (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))]
  have l18 : ∀ sK1 : G, (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1, 1, 1]; rw [l17 sK1]
    conv => enter [1, 2]; rw [l17 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))]
  have l19 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (((sK1 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1]; rw [l18 sK1]
  have l20 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h115 ((sK1 ◇ sK1) ◇ sK1) X0]
    conv => enter [1, 2, 1]; rw [← l19 sK1]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)]
    conv => enter [1, 2]; rw [← h117 sK0 ((sK1 ◇ sK1) ◇ sK1)]
  have l22 : ∀ sK0 sK1 : G, sK0 = ((((sK1 ◇ sK1) ◇ sK1) ◇ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l21 sK1 sK0]
    conv => enter [1, 1, 1]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 1]; rw [← h117 sK0 ((sK1 ◇ sK1) ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l23 x y]

theorem Equation209_211_264_implies_Equation4 (G : Type*) [Magma G] (h209 : Equation209 G) (h211 : Equation211 G) (h264 : Equation264 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h211 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h211 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← h209 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h211 (X0 ◇ ((X1 ◇ X1) ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h209 X0 (X1 ◇ X1)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← l3 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← l3 X1 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2, 2]; rw [← l3 X0 X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l11 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1, 2]; rw [l3 X0 X0]
    conv => enter [1]; rw [l4 X0 X0]
    conv => enter [1, 2, 2]; rw [← l3 X0 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l10 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X1 X0]
    conv => enter [1]; rw [l7 X0 X0]
  have l13 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [← l1 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1, 2]; rw [l7 X0 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← l3 (X0 ◇ (X1 ◇ (X0 ◇ X1))) (X1 ◇ X0)]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 2]; rw [← l9 X1 X0]
  have l16 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 1]; rw [l15 X0 X0]
    conv => enter [1]; rw [← l13 X0]
  have l17 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [← l16 X0]
    conv => enter [1]; rw [← h209 X0 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l17 X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l19 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l17 X0]
    conv => enter [1]; rw [← l11 X0]
    conv => enter [1]; rw [l17 X0]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l19 X1]
    conv => enter [1]; rw [l18 X0 X1]
  intro x y
  conv => enter [1]; rw [← l20 x y]

theorem Equation75_107_117_implies_Equation5 (G : Type*) [Magma G] (h75 : Equation75 G) (h107 : Equation107 G) (h117 : Equation117 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h107 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h107 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X1 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h117 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h107 ((X0 ◇ (X1 ◇ X1)) ◇ X0) X1]
    conv => enter [1, 2]; rw [← h117 X0 (X1 ◇ X1)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← l3 (X1 ◇ X0) ((X1 ◇ X0) ◇ X1)]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X1 ◇ X0)]
  have l8 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1]; rw [← l3 X1 (X1 ◇ X0)]
  have l9 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 1, 1]; rw [← l3 X0 X1]
  have l10 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l5 X0 X2]
  have l11 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [l3 X0 X0]
    conv => enter [1]; rw [l4 X0 X0]
    conv => enter [1, 1, 1]; rw [← l3 X0 X0]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 (((X0 ◇ X0) ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [l7 X0 X0]
  have l13 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l1 X0 (((X0 ◇ X0) ◇ X0) ◇ X0)]
    conv => enter [1, 1]; rw [l7 X0 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← l3 (((X1 ◇ X0) ◇ X1) ◇ X0) (X0 ◇ X1)]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 1]; rw [← l9 X0 X1]
  have l16 : ∀ X0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2]; rw [l15 X0 X0]
    conv => enter [1]; rw [← l13 X0]
  have l17 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [← l16 X0]
    conv => enter [1]; rw [← h117 X0 X0]
  have l18 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l17 X0]
    conv => enter [1]; rw [l12 X1 X0]
  have l19 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l17 X0]
    conv => enter [1]; rw [← l11 X0]
    conv => enter [1]; rw [l17 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l19 X1]
    conv => enter [1]; rw [l18 X1 X0]
  intro x y
  conv => enter [1]; rw [← l20 y x]

theorem Equation209_211_231_implies_Equation2 (G : Type*) [Magma G] (h209 : Equation209 G) (h211 : Equation211 G) (h231 : Equation231 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h211 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h231 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X1 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h231 X1 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h211 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 (X1 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l1 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation107_108_117_implies_Equation2 (G : Type*) [Magma G] (h107 : Equation107 G) (h108 : Equation108 G) (h117 : Equation117 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h107 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X1 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h108 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X1 ◇ X1) ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h108 X1 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h107 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 ((X1 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation205_364_367_implies_Equation5 (G : Type*) [Magma G] (h205 : Equation205 G) (h364 : Equation364 G) (h367 : Equation367 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h205 (X1 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h364 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h367 X1 X0]
    conv => enter [1]; rw [h367 X1 X2]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h367 X2 X1]
    conv => enter [1, 1]; rw [h367 X1 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ X1)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h205 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [l1 X1 ((X1 ◇ X1) ◇ X2) X0]
  have l4 : ∀ X1 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X1
    conv => enter [1]; rw [l3 X1 X1 X1]
    conv => enter [1]; rw [← l2 (X1 ◇ X1) X1 ((X1 ◇ X1) ◇ X1)]
  have l5 : ∀ X4 X3 X0 X1 X2 : G, ((X4 ◇ X4) ◇ X3) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [l1 X4 X3 X2]
    conv => enter [1, 1]; rw [l2 X2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [h367 (X0 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l4 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1, 1]; rw [← h364 (X0 ◇ X0) X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 1]; rw [← l4 X0]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 1]; rw [← l9 X0 X1]
  have l11 : ∀ X3 X4 X0 X1 X2 X5 X6 : G, ((X3 ◇ X3) ◇ X4) = (((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X5) ◇ X6) ◇ X4) := by
    intro X3 X4 X0 X1 X2 X5 X6
    conv => enter [1]; rw [l5 X3 X4 X2 X5 X6]
    conv => enter [1, 1, 1, 1]; rw [l10 X2 X0 X1]
  have l12 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X3) = (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l6 X3 X2]
    conv => enter [1, 1]; rw [l10 X2 X0 X1]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0 X0 X0]
    conv => enter [1]; rw [← h205 X0 X0]
  have l14 : ∀ X0 X1 X2 X3 : G, (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [← l13 X3]
    conv => enter [1]; rw [← l12 X3 X0 X1 X2]
    conv => enter [1]; rw [l13 X3]
  have l15 : ∀ X3 X4 X0 X1 X2 X5 X6 : G, ((X3 ◇ X3) ◇ X4) = (((((X0 ◇ X1) ◇ X2) ◇ X5) ◇ X6) ◇ X4) := by
    intro X3 X4 X0 X1 X2 X5 X6
    conv => enter [1]; rw [l11 X3 X4 X0 X1 X2 X5 X6]
    conv => enter [1, 1, 1, 1, 1, 2]; rw [l13 X1]
  have l16 : ∀ X0 X1 X2 X3 : G, (((X0 ◇ X1) ◇ X2) ◇ X3) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 1, 1, 2]; rw [← l13 X1]
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
  have l17 : ∀ X3 X4 X0 X1 X2 X5 X6 : G, (X3 ◇ X4) = (((((X0 ◇ X1) ◇ X2) ◇ X5) ◇ X6) ◇ X4) := by
    intro X3 X4 X0 X1 X2 X5 X6
    conv => enter [1, 1]; rw [← l13 X3]
    conv => enter [1]; rw [l15 X3 X4 X0 X1 X2 X5 X6]
  have l18 : ∀ X3 X4 : G, (X3 ◇ X4) = X4 := by
    intro X3 X4
    conv => enter [1]; rw [l17 X3 X4 X3 X3 X3 X3 X3]
    conv => enter [1]; rw [l16 ((X3 ◇ X3) ◇ X3) X3 X3 X4]
  intro x y
  conv => enter [1]; rw [← l18 y x]

theorem Equation104_308_310_implies_Equation4 (G : Type*) [Magma G] (h104 : Equation104 G) (h308 : Equation308 G) (h310 : Equation310 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h104 (X0 ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h308 X0 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← h310 X1 X0]
    conv => enter [1]; rw [h310 X1 X2]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h310 X2 X1]
    conv => enter [1, 2]; rw [h310 X1 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h104 (X1 ◇ X1) X2]
    conv => enter [1, 2]; rw [l1 (X2 ◇ (X1 ◇ X1)) X1 X0]
  have l4 : ∀ X1 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X1
    conv => enter [1]; rw [l3 X1 X1 X1]
    conv => enter [1]; rw [← l2 (X1 ◇ X1) (X1 ◇ (X1 ◇ X1)) X1]
  have l5 : ∀ X3 X4 X2 X1 X0 : G, (X3 ◇ (X4 ◇ X4)) = (X3 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X3 X4 X2 X1 X0
    conv => enter [1]; rw [l1 X3 X4 X2]
    conv => enter [1, 2]; rw [l2 X2 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [h310 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← l4 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← h308 (X0 ◇ X0) X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← l4 X0]
  have l10 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l2 X2 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2]; rw [← l9 X1 X0]
  have l11 : ∀ X4 X3 X6 X5 X2 X1 X0 : G, (X4 ◇ (X3 ◇ X3)) = (X4 ◇ (X6 ◇ (X5 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))))) := by
    intro X4 X3 X6 X5 X2 X1 X0
    conv => enter [1]; rw [l5 X4 X3 X6 X5 X2]
    conv => enter [1, 2, 2, 2]; rw [l10 X2 X1 X0]
  have l12 : ∀ X3 X2 X1 X0 : G, (X3 ◇ X3) = ((X3 ◇ X3) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X3 X2 X1 X0
    conv => enter [1]; rw [l6 X3 X2]
    conv => enter [1, 2]; rw [l10 X2 X1 X0]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l10 X0 X0 X0]
    conv => enter [1]; rw [← h104 X0 X0]
  have l14 : ∀ X3 X2 X1 X0 : G, (X3 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) = X3 := by
    intro X3 X2 X1 X0
    conv => enter [1, 1]; rw [← l13 X3]
    conv => enter [1]; rw [← l12 X3 X2 X1 X0]
    conv => enter [1]; rw [l13 X3]
  have l15 : ∀ X4 X3 X6 X5 X2 X1 X0 : G, (X4 ◇ (X3 ◇ X3)) = (X4 ◇ (X6 ◇ (X5 ◇ (X2 ◇ (X1 ◇ X0))))) := by
    intro X4 X3 X6 X5 X2 X1 X0
    conv => enter [1]; rw [l11 X4 X3 X6 X5 X2 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 1]; rw [l13 X1]
  have l16 : ∀ X3 X2 X1 X0 : G, (X3 ◇ (X2 ◇ (X1 ◇ X0))) = X3 := by
    intro X3 X2 X1 X0
    conv => enter [1, 2, 2, 1]; rw [← l13 X1]
    conv => enter [1]; rw [l14 X3 X2 X1 X0]
  have l17 : ∀ X4 X3 X6 X5 X2 X1 X0 : G, (X4 ◇ X3) = (X4 ◇ (X6 ◇ (X5 ◇ (X2 ◇ (X1 ◇ X0))))) := by
    intro X4 X3 X6 X5 X2 X1 X0
    conv => enter [1, 2]; rw [← l13 X3]
    conv => enter [1]; rw [l15 X4 X3 X6 X5 X2 X1 X0]
  have l18 : ∀ X4 X3 : G, (X4 ◇ X3) = X4 := by
    intro X4 X3
    conv => enter [1]; rw [l17 X4 X3 X4 X4 X4 X4 X4]
    conv => enter [1]; rw [l16 X4 X4 X4 (X4 ◇ (X4 ◇ X4))]
  intro x y
  conv => enter [1]; rw [← l18 x y]

theorem Equation205_280_implies_Equation28 (G : Type*) [Magma G] (h205 : Equation205 G) (h280 : Equation280 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 1]; rw [← l1 (X0 ◇ X0) X1]
  have l3 : ∀ X0 X1 X2 : G, ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [← h280 ((X0 ◇ X0) ◇ X1) X0]
  have l5 : ∀ X0 X1 X2 : G, ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ X0) ◇ X1)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l5 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l5 (X0 ◇ X0) X0 X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l6 X0]
    conv => enter [1]; rw [← h280 X1 X0]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation205_280_implies_Equation333 (G : Type*) [Magma G] (h205 : Equation205 G) (h280 : Equation280 G) : Equation333 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h205 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h280 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← h280 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 1]; rw [← l1 (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 X2 : G, ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [← h280 ((X0 ◇ X0) ◇ X1) X0]
  have l7 : ∀ X0 X1 X2 : G, ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ X0) ◇ X1)]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l7 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l7 (X0 ◇ X0) X0 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X0]
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2, 1]; rw [l8 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation205_280_implies_Equation208 (G : Type*) [Magma G] (h205 : Equation205 G) (h280 : Equation280 G) : Equation208 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h205 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h280 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← h280 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 1]; rw [← l1 (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 X2 : G, ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 1]; rw [← h280 ((X0 ◇ X0) ◇ X1) X0]
  have l7 : ∀ X0 X1 X2 : G, ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h280 X2 ((X0 ◇ X0) ◇ X1)]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l7 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l7 (X0 ◇ X0) X0 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l8 X0]
    conv => enter [1]; rw [← h280 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X0]
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2, 1]; rw [l8 X0]
  intro x y
  conv => enter [1]; rw [← l9 y x]
  conv => enter [1, 1]; rw [l10 y x]

theorem Equation50_104_implies_Equation9 (G : Type*) [Magma G] (h50 : Equation50 G) (h104 : Equation104 G) : Equation9 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h50 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← l1 X1 (X0 ◇ X0)]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h50 X2 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 (X1 ◇ (X0 ◇ X0)) X1 X0]
    conv => enter [1, 2]; rw [← h50 (X1 ◇ (X0 ◇ X0)) X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h50 X2 (X1 ◇ (X0 ◇ X0))]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l5 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l5 X0 X0 (X0 ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l6 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation50_104_implies_Equation377 (G : Type*) [Magma G] (h50 : Equation50 G) (h104 : Equation104 G) : Equation377 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h104 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h50 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h50 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h50 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← l1 X1 (X0 ◇ X0)]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h50 X2 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 (X1 ◇ (X0 ◇ X0)) X1 X0]
    conv => enter [1, 2]; rw [← h50 (X1 ◇ (X0 ◇ X0)) X0]
  have l7 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l6 X1 X0]
    conv => enter [1]; rw [← h50 X2 (X1 ◇ (X0 ◇ X0))]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l7 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l7 X0 X0 (X0 ◇ X0)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l8 X0]
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1, 2]; rw [l8 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation50_104_implies_Equation101 (G : Type*) [Magma G] (h50 : Equation50 G) (h104 : Equation104 G) : Equation101 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h104 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h50 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h50 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h50 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← l1 X1 (X0 ◇ X0)]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h50 X2 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 (X1 ◇ (X0 ◇ X0)) X1 X0]
    conv => enter [1, 2]; rw [← h50 (X1 ◇ (X0 ◇ X0)) X0]
  have l7 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l6 X1 X0]
    conv => enter [1]; rw [← h50 X2 (X1 ◇ (X0 ◇ X0))]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l7 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l7 X0 X0 (X0 ◇ X0)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l8 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l8 X0]
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1, 2]; rw [l8 X0]
  intro x y
  conv => enter [1]; rw [← l9 x y]
  conv => enter [1, 2]; rw [l10 x y]

theorem Equation205_231_359_implies_Equation5 (G : Type*) [Magma G] (h205 : Equation205 G) (h231 : Equation231 G) (h359 : Equation359 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h359 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h359 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h359 X0]
    conv => enter [1]; rw [l3 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [l3 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l4 X0]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation104_108_307_implies_Equation4 (G : Type*) [Magma G] (h104 : Equation104 G) (h108 : Equation108 G) (h307 : Equation307 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h307 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h307 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h307 X0]
    conv => enter [1]; rw [l3 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h104 (X0 ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [l3 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l4 X0]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation205_219_implies_Equation2 (G : Type*) [Magma G] (h205 : Equation205 G) (h219 : Equation219 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h219 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h205 X1 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation104_115_implies_Equation2 (G : Type*) [Magma G] (h104 : Equation104 G) (h115 : Equation115 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h115 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h115 X1 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h104 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h115 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation205_211_264_implies_Equation4 (G : Type*) [Magma G] (h205 : Equation205 G) (h211 : Equation211 G) (h264 : Equation264 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h211 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h211 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h211 ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← h264 X0 (X1 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h264 X0 (X0 ◇ (X1 ◇ X1))]
  have l4 : ∀ X0 X1 : G, ((((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l5 X0 X0]
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l5 X0 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X1]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation75_104_107_implies_Equation5 (G : Type*) [Magma G] (h75 : Equation75 G) (h104 : Equation104 G) (h107 : Equation107 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h107 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h107 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) = (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h107 ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) X1]
    conv => enter [1, 2]; rw [← h75 X0 (X1 ◇ X1)]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h75 X0 ((X1 ◇ X1) ◇ X0)]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h75 X0 ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0))]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l5 X0 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l6 X1]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation205_209_255_implies_Equation9 (G : Type*) [Magma G] (h205 : Equation205 G) (h209 : Equation209 G) (h255 : Equation255 G) : Equation9 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h209 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [l0 X0]
  have l5 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h209 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [l0 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h255 X0]
    conv => enter [1]; rw [← l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l7 X0]
    conv => enter [1]; rw [← h255 X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [l8 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l9 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x y]

theorem Equation205_209_255_implies_Equation377 (G : Type*) [Magma G] (h205 : Equation205 G) (h209 : Equation209 G) (h255 : Equation255 G) : Equation377 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h209 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [l0 X0]
  have l6 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h209 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [l0 X0]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h255 X0]
    conv => enter [1]; rw [← l6 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l7 X0]
  have l9 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l8 X0]
    conv => enter [1]; rw [← h255 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l8 X0]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l12 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation205_209_255_implies_Equation101 (G : Type*) [Magma G] (h205 : Equation205 G) (h209 : Equation209 G) (h255 : Equation255 G) : Equation101 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h209 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [l0 X0]
  have l6 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h209 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [l0 X0]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [h255 X0]
    conv => enter [1]; rw [← l6 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l7 X0]
  have l9 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l8 X0]
    conv => enter [1]; rw [← h255 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l8 X0]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l12 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l12 x y]
  conv => enter [1, 2]; rw [l13 x y]

theorem Equation47_104_117_implies_Equation28 (G : Type*) [Magma G] (h47 : Equation47 G) (h104 : Equation104 G) (h117 : Equation117 G) : Equation28 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X1 ◇ X0) ◇ X0)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [h117 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X0]
  have l6 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h47 X0]
    conv => enter [1]; rw [← l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l7 X0]
    conv => enter [1]; rw [← h47 X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [l8 X0]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l9 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  intro x y
  conv => enter [1]; rw [← l11 y x]

theorem Equation47_104_117_implies_Equation333 (G : Type*) [Magma G] (h47 : Equation47 G) (h104 : Equation104 G) (h117 : Equation117 G) : Equation333 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [h117 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X0]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h47 X0]
    conv => enter [1]; rw [← l6 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l7 X0]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l8 X0]
    conv => enter [1]; rw [← h47 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l8 X0]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l10 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l12 ((X1 ◇ X0) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation47_104_117_implies_Equation208 (G : Type*) [Magma G] (h47 : Equation47 G) (h104 : Equation104 G) (h117 : Equation117 G) : Equation208 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [h117 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X0]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h47 X0]
    conv => enter [1]; rw [← l6 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [l7 X0]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l8 X0]
    conv => enter [1]; rw [← h47 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l8 X0]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l10 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l12 ((X1 ◇ X0) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l12 y x]
  conv => enter [1, 1]; rw [l13 y x]

theorem Equation205_209_231_implies_Equation2 (G : Type*) [Magma G] (h205 : Equation205 G) (h209 : Equation209 G) (h231 : Equation231 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h231 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1, 2]; rw [← h231 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h231 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l3 X0 X2]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation104_108_117_implies_Equation2 (G : Type*) [Magma G] (h104 : Equation104 G) (h108 : Equation108 G) (h117 : Equation117 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h108 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X1 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h104 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h108 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h108 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l3 X0 X2]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation151_283_implies_Equation231 (G : Type*) [Magma G] (h151 : Equation151 G) (h283 : Equation283 G) : Equation231 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation56_151_implies_Equation108 (G : Type*) [Magma G] (h56 : Equation56 G) (h151 : Equation151 G) : Equation108 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h56 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation151_280_implies_Equation28 (G : Type*) [Magma G] (h151 : Equation151 G) (h280 : Equation280 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h280 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation50_151_implies_Equation9 (G : Type*) [Magma G] (h50 : Equation50 G) (h151 : Equation151 G) : Equation9 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h50 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation151_264_273_implies_Equation47 (G : Type*) [Magma G] (h151 : Equation151 G) (h264 : Equation264 G) (h273 : Equation273 G) : Equation47 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h264 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h273 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 1, 1]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h264 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 1, 1]; rw [← h273 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h273 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← l1 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h264 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 1, 1]; rw [← l3 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h264 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 1, 1]; rw [← l5 sK0]
  have l7 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h264 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0]
  intro x
  conv => enter [1]; rw [l7 x]

theorem Equation53_75_151_implies_Equation255 (G : Type*) [Magma G] (h53 : Equation53 G) (h75 : Equation75 G) (h151 : Equation151 G) : Equation255 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h75 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) = (((sK0 ◇ sK0) ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h75 (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h53 ((sK0 ◇ sK0) ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53 ((sK0 ◇ sK0) ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h75 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l6 : ∀ sK0 : G, (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h75 (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l5 sK0]
  have l7 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h75 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0]
  intro x
  conv => enter [1]; rw [l7 x]

theorem Equation151_261_implies_Equation3 (G : Type*) [Magma G] (h151 : Equation151 G) (h261 : Equation261 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h261 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h151 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l2 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h261 X0 ((X0 ◇ X0) ◇ X0)]
  have l3 : ∀ X0 : G, ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1, 1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← l0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h261 X0 X0]
    conv => enter [1]; rw [l3 X0]
  intro x
  conv => enter [1]; rw [← l4 x]

theorem Equation65_151_implies_Equation3 (G : Type*) [Magma G] (h65 : Equation65 G) (h151 : Equation151 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h65 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h151 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l2 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h65 X0 (X0 ◇ (X0 ◇ X0))]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1, 2, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h65 X0 X0]
    conv => enter [1]; rw [l3 X0]
  intro x
  conv => enter [1]; rw [← l4 x]

theorem Equation151_231_implies_Equation283 (G : Type*) [Magma G] (h151 : Equation151 G) (h231 : Equation231 G) : Equation283 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation108_151_implies_Equation56 (G : Type*) [Magma G] (h108 : Equation108 G) (h151 : Equation151 G) : Equation56 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation151_219_implies_Equation14 (G : Type*) [Magma G] (h151 : Equation151 G) (h219 : Equation219 G) : Equation14 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h219 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h219 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h219 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l2 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation115_151_implies_Equation14 (G : Type*) [Magma G] (h115 : Equation115 G) (h151 : Equation151 G) : Equation14 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h115 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h115 X0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h115 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation212_231_264_implies_Equation56 (G : Type*) [Magma G] (h212 : Equation212 G) (h231 : Equation231 G) (h264 : Equation264 G) : Equation56 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h212 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation75_108_127_implies_Equation283 (G : Type*) [Magma G] (h75 : Equation75 G) (h108 : Equation108 G) (h127 : Equation127 G) : Equation283 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h127 X1 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h127 X0 X1]
  have l2 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation151_212_221_255_implies_Equation14 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h221 : Equation221 G) (h255 : Equation255 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h212 (X1 ◇ ((X0 ◇ X0) ◇ X1)) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l0 X0 X0]
    conv => enter [1, 1, 2]; rw [l0 X0 X0]
    conv => enter [1, 2]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X0 ◇ X1)) X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l3 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h221 X0 X2]
    conv => enter [1]; rw [l7 X0 (X2 ◇ (X0 ◇ X2)) X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0]
    conv => enter [1]; rw [l7 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0)) X1]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [← l9 X0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← l10 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X1]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2, 1]; rw [l11 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l11 X1]
  intro x y
  conv => enter [1]; rw [← l13 y x]

theorem Equation151_212_221_255_implies_Equation332 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h221 : Equation221 G) (h255 : Equation255 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h212 (X1 ◇ ((X0 ◇ X0) ◇ X1)) X0]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h255 (X0 ◇ X0)]
    conv => enter [1]; rw [← h212 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l0 X0 X0]
    conv => enter [1, 1, 2]; rw [l0 X0 X0]
    conv => enter [1, 2]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X0 ◇ X1)) X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l3 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h221 X0 X2]
    conv => enter [1]; rw [l7 X0 (X2 ◇ (X0 ◇ X2)) X1]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X2) ◇ X1)) = ((X2 ◇ X2) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 (X0 ◇ X2) (X2 ◇ X2)]
    conv => enter [1, 2]; rw [l0 X0 X2]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0]
    conv => enter [1]; rw [l7 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0)) X1]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [← l10 X0 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← l11 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l12 X1]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2, 1]; rw [l12 X1]
  have l14 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1, 1]; rw [← l12 X2]
    conv => enter [1]; rw [← l9 X1 X0 X2]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X1 X0]
    conv => enter [1]; rw [l12 X1]
  have l16 : ∀ X0 X2 : G, (X0 ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [l14 X0 X2 X0]
    conv => enter [1]; rw [l15 X0 (X2 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l16 x y]
  conv => enter [1, 2]; rw [← l12 x]

end Order3
