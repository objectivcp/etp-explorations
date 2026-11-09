import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace OneVariable

@[equational_result]
theorem Equation3_implies_Equation8 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation23 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation4380 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation4380 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation307 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation359 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation151 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1]; rw [h3 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation3659 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation3659 G := by
  intro x
  conv => enter [1]; rw [h3 (x ◇ x)]

@[equational_result]
theorem Equation3_implies_Equation3456 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation3456 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation3862 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation3862 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation3253 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation3253 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation4065 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation4065 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation99 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation203 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation203 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation47 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation47 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation255 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation255 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation411 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation411 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation3050 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation3050 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation614 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation614 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation2847 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation2847 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation1020 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation1020 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation2441 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation2441 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation1223 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation1223 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation2238 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation2238 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation817 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation817 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1]; rw [h3 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation2644 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation2644 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1]; rw [h3 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation1629 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation1629 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation1832 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation1832 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1]; rw [l0 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation1426 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation1426 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation2035 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation2035 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1]; rw [l0 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l2 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation8_implies_Equation3862 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation3862 G := by
  intro x
  conv => enter [1, 1]; rw [h8 x]

@[equational_result]
theorem Equation8_implies_Equation3253 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation3253 G := by
  intro x
  conv => enter [1, 2]; rw [h8 x]

@[equational_result]
theorem Equation8_implies_Equation411 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation411 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2, 2]; rw [h8 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation8_implies_Equation1020 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation1020 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2, 1]; rw [h8 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation8_implies_Equation1832 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation1832 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 1]; rw [h8 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation23_implies_Equation3456 (G : Type*) [Magma G] (h23 : Equation23 G) : Equation3456 G := by
  intro x
  conv => enter [1, 2]; rw [h23 x]

@[equational_result]
theorem Equation23_implies_Equation4065 (G : Type*) [Magma G] (h23 : Equation23 G) : Equation4065 G := by
  intro x
  conv => enter [1, 1]; rw [h23 x]

@[equational_result]
theorem Equation23_implies_Equation3050 (G : Type*) [Magma G] (h23 : Equation23 G) : Equation3050 G := by
  have l0 : ∀ sK0 : G, sK0 = ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1, 1]; rw [h23 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation23_implies_Equation2441 (G : Type*) [Magma G] (h23 : Equation23 G) : Equation2441 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1, 2]; rw [h23 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation23_implies_Equation1629 (G : Type*) [Magma G] (h23 : Equation23 G) : Equation1629 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 2]; rw [h23 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation307_implies_Equation3253 (G : Type*) [Magma G] (h307 : Equation307 G) : Equation3253 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation359_implies_Equation4065 (G : Type*) [Magma G] (h359 : Equation359 G) : Equation4065 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h359 sK0]
    conv => enter [1, 1]; rw [h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_23_implies_Equation4380 (G : Type*) [Magma G] (h8 : Equation8 G) (h23 : Equation23 G) : Equation4380 G := by
  intro x
  conv => enter [1]; rw [← h8 x]
  conv => enter [1]; rw [h23 x]

theorem Equation8_23_implies_Equation614 (G : Type*) [Magma G] (h8 : Equation8 G) (h23 : Equation23 G) : Equation614 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2, 2]; rw [h23 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_23_implies_Equation2847 (G : Type*) [Magma G] (h8 : Equation8 G) (h23 : Equation23 G) : Equation2847 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1, 1]; rw [h8 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_23_implies_Equation1223 (G : Type*) [Magma G] (h8 : Equation8 G) (h23 : Equation23 G) : Equation1223 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2, 1]; rw [h23 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_23_implies_Equation2238 (G : Type*) [Magma G] (h8 : Equation8 G) (h23 : Equation23 G) : Equation2238 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1, 2]; rw [h8 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_23_implies_Equation1426 (G : Type*) [Magma G] (h8 : Equation8 G) (h23 : Equation23 G) : Equation1426 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 2]; rw [h8 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_23_implies_Equation2035 (G : Type*) [Magma G] (h8 : Equation8 G) (h23 : Equation23 G) : Equation2035 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 1]; rw [h23 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_47_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h47 : Equation47 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h8 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation23_255_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h23 X0]
    conv => enter [1]; rw [← h255 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation8_151_implies_Equation359 (G : Type*) [Magma G] (h8 : Equation8 G) (h151 : Equation151 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_151_implies_Equation99 (G : Type*) [Magma G] (h8 : Equation8 G) (h151 : Equation151 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation8_151_implies_Equation1223 (G : Type*) [Magma G] (h8 : Equation8 G) (h151 : Equation151 G) : Equation1223 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

theorem Equation8_151_implies_Equation1629 (G : Type*) [Magma G] (h8 : Equation8 G) (h151 : Equation151 G) : Equation1629 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation8_151_implies_Equation2035 (G : Type*) [Magma G] (h8 : Equation8 G) (h151 : Equation151 G) : Equation2035 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation23_151_implies_Equation307 (G : Type*) [Magma G] (h23 : Equation23 G) (h151 : Equation151 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h23 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_151_implies_Equation203 (G : Type*) [Magma G] (h23 : Equation23 G) (h151 : Equation151 G) : Equation203 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h23 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation23_151_implies_Equation2238 (G : Type*) [Magma G] (h23 : Equation23 G) (h151 : Equation151 G) : Equation2238 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h23 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

theorem Equation23_151_implies_Equation1832 (G : Type*) [Magma G] (h23 : Equation23 G) (h151 : Equation151 G) : Equation1832 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h23 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation23_151_implies_Equation1426 (G : Type*) [Magma G] (h23 : Equation23 G) (h151 : Equation151 G) : Equation1426 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h23 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation8_203_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation23_99_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h99 : Equation99 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h23 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation8_307_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_359_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_359_implies_Equation99 (G : Type*) [Magma G] (h8 : Equation8 G) (h359 : Equation359 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2]; rw [h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_359_implies_Equation1223 (G : Type*) [Magma G] (h8 : Equation8 G) (h359 : Equation359 G) : Equation1223 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h359 sK0]
    conv => enter [1, 1]; rw [h359 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation23_307_implies_Equation203 (G : Type*) [Magma G] (h23 : Equation23 G) (h307 : Equation307 G) : Equation203 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1]; rw [h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_307_implies_Equation2238 (G : Type*) [Magma G] (h23 : Equation23 G) (h307 : Equation307 G) : Equation2238 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [h307 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation8_1426_implies_Equation23 (G : Type*) [Magma G] (h8 : Equation8 G) (h1426 : Equation1426 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h1426 sK0]
    conv => enter [1, 2]; rw [← h8 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_2035_implies_Equation8 (G : Type*) [Magma G] (h23 : Equation23 G) (h2035 : Equation2035 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h2035 sK0]
    conv => enter [1, 1]; rw [← h23 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_2238_implies_Equation23 (G : Type*) [Magma G] (h8 : Equation8 G) (h2238 : Equation2238 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h8 X0]
    conv => enter [1]; rw [← h2238 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation23_1223_implies_Equation8 (G : Type*) [Magma G] (h23 : Equation23 G) (h1223 : Equation1223 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 1]; rw [h23 X0]
    conv => enter [1]; rw [← h1223 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation8_2847_implies_Equation23 (G : Type*) [Magma G] (h8 : Equation8 G) (h2847 : Equation2847 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h2847 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation23_614_implies_Equation8 (G : Type*) [Magma G] (h23 : Equation23 G) (h614 : Equation614 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h23 X0]
    conv => enter [1]; rw [← h614 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation8_3456_implies_Equation614 (G : Type*) [Magma G] (h8 : Equation8 G) (h3456 : Equation3456 G) : Equation614 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2]; rw [h3456 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_3862_implies_Equation2847 (G : Type*) [Magma G] (h23 : Equation23 G) (h3862 : Equation3862 G) : Equation2847 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1]; rw [h3862 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_3659_implies_Equation817 (G : Type*) [Magma G] (h8 : Equation8 G) (h3659 : Equation3659 G) : Equation817 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2]; rw [h3659 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_3659_implies_Equation2644 (G : Type*) [Magma G] (h23 : Equation23 G) (h3659 : Equation3659 G) : Equation2644 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1]; rw [h3659 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_4065_implies_Equation1223 (G : Type*) [Magma G] (h8 : Equation8 G) (h4065 : Equation4065 G) : Equation1223 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2]; rw [h4065 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_3253_implies_Equation2238 (G : Type*) [Magma G] (h23 : Equation23 G) (h3253 : Equation3253 G) : Equation2238 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1]; rw [h3253 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_4380_implies_Equation23 (G : Type*) [Magma G] (h8 : Equation8 G) (h4380 : Equation4380 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_4380_implies_Equation8 (G : Type*) [Magma G] (h23 : Equation23 G) (h4380 : Equation4380 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1]; rw [← h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation47_307_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h307 X0]
    conv => enter [1]; rw [← h47 X0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation255_359_implies_Equation3 (G : Type*) [Magma G] (h255 : Equation255 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h359 X0]
    conv => enter [1]; rw [← h255 X0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation47_359_implies_Equation614 (G : Type*) [Magma G] (h47 : Equation47 G) (h359 : Equation359 G) : Equation614 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h47 sK0]
    conv => enter [1, 2, 2]; rw [h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation255_307_implies_Equation2847 (G : Type*) [Magma G] (h255 : Equation255 G) (h307 : Equation307 G) : Equation2847 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h255 sK0]
    conv => enter [1, 1, 1]; rw [h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation47_411_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h411 : Equation411 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h47 X0]
    conv => enter [1]; rw [← h411 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation255_3050_implies_Equation3 (G : Type*) [Magma G] (h255 : Equation255 G) (h3050 : Equation3050 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h255 X0]
    conv => enter [1]; rw [← h3050 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation47_2238_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h2238 : Equation2238 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h2238 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation255_1223_implies_Equation3 (G : Type*) [Magma G] (h255 : Equation255 G) (h1223 : Equation1223 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h255 X0]
    conv => enter [1]; rw [← h1223 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation47_3253_implies_Equation3 (G : Type*) [Magma G] (h47 : Equation47 G) (h3253 : Equation3253 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h47 sK0]
    conv => enter [1]; rw [← h3253 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation255_4065_implies_Equation3 (G : Type*) [Magma G] (h255 : Equation255 G) (h4065 : Equation4065 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h255 sK0]
    conv => enter [1]; rw [← h4065 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation47_4380_implies_Equation99 (G : Type*) [Magma G] (h47 : Equation47 G) (h4380 : Equation4380 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h47 sK0]
    conv => enter [1, 2]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation255_4380_implies_Equation203 (G : Type*) [Magma G] (h255 : Equation255 G) (h4380 : Equation4380 G) : Equation203 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h4380 X0]
    conv => enter [1]; rw [← h255 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation99_307_implies_Equation1020 (G : Type*) [Magma G] (h99 : Equation99 G) (h307 : Equation307 G) : Equation1020 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h99 sK0]
    conv => enter [1, 2, 1]; rw [h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation203_359_implies_Equation2441 (G : Type*) [Magma G] (h203 : Equation203 G) (h359 : Equation359 G) : Equation2441 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h203 sK0]
    conv => enter [1, 1, 2]; rw [h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation99_359_implies_Equation8 (G : Type*) [Magma G] (h99 : Equation99 G) (h359 : Equation359 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h359 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation203_307_implies_Equation23 (G : Type*) [Magma G] (h203 : Equation203 G) (h307 : Equation307 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h307 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation99_614_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h614 : Equation614 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h99 X0]
    conv => enter [1]; rw [← h614 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation203_2847_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h2847 : Equation2847 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h203 X0]
    conv => enter [1]; rw [← h2847 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation99_2441_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h2441 : Equation2441 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h99 X0]
    conv => enter [1]; rw [← h2441 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation203_1020_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h1020 : Equation1020 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h203 X0]
    conv => enter [1]; rw [← h1020 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation99_3456_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h3456 : Equation3456 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h99 sK0]
    conv => enter [1]; rw [← h3456 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation203_3862_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h3862 : Equation3862 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h203 sK0]
    conv => enter [1]; rw [← h3862 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation99_4380_implies_Equation47 (G : Type*) [Magma G] (h99 : Equation99 G) (h4380 : Equation4380 G) : Equation47 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4380 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation203_4380_implies_Equation255 (G : Type*) [Magma G] (h203 : Equation203 G) (h4380 : Equation4380 G) : Equation255 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h203 sK0]
    conv => enter [1, 1]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_307_implies_Equation23 (G : Type*) [Magma G] (h151 : Equation151 G) (h307 : Equation307 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [h307 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_359_implies_Equation8 (G : Type*) [Magma G] (h151 : Equation151 G) (h359 : Equation359 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [h359 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_817_implies_Equation3 (G : Type*) [Magma G] (h151 : Equation151 G) (h817 : Equation817 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h817 X0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation151_2644_implies_Equation3 (G : Type*) [Magma G] (h151 : Equation151 G) (h2644 : Equation2644 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h2644 X0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation151_1426_implies_Equation3456 (G : Type*) [Magma G] (h151 : Equation151 G) (h1426 : Equation1426 G) : Equation3456 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1426 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
    conv => enter [1, 2, 2]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_2035_implies_Equation3862 (G : Type*) [Magma G] (h151 : Equation151 G) (h2035 : Equation2035 G) : Equation3862 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h2035 (sK0 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← h151 sK0]
    conv => enter [1, 2]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_1629_implies_Equation3253 (G : Type*) [Magma G] (h151 : Equation151 G) (h1629 : Equation1629 G) : Equation3253 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h1629 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
    conv => enter [1, 2, 1]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_1832_implies_Equation4065 (G : Type*) [Magma G] (h151 : Equation151 G) (h1832 : Equation1832 G) : Equation4065 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h1832 (sK0 ◇ sK0)]
    conv => enter [1, 1, 2]; rw [← h151 sK0]
    conv => enter [1, 2]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_3253_implies_Equation1629 (G : Type*) [Magma G] (h151 : Equation151 G) (h3253 : Equation3253 G) : Equation1629 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [h3253 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_4065_implies_Equation1832 (G : Type*) [Magma G] (h151 : Equation151 G) (h4065 : Equation4065 G) : Equation1832 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [h4065 (sK0 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_3456_implies_Equation1426 (G : Type*) [Magma G] (h151 : Equation151 G) (h3456 : Equation3456 G) : Equation1426 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [h3456 (sK0 ◇ sK0)]
    conv => enter [1, 2, 1]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_3862_implies_Equation2035 (G : Type*) [Magma G] (h151 : Equation151 G) (h3862 : Equation3862 G) : Equation2035 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [h3862 (sK0 ◇ sK0)]
    conv => enter [1, 1, 2]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation151_3659_implies_Equation3 (G : Type*) [Magma G] (h151 : Equation151 G) (h3659 : Equation3659 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h3659 X0]
    conv => enter [1]; rw [← h151 X0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h151 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation307_359_implies_Equation4380 (G : Type*) [Magma G] (h307 : Equation307 G) (h359 : Equation359 G) : Equation4380 G := by
  intro x
  conv => enter [1]; rw [← h307 x]
  conv => enter [1]; rw [h359 x]

theorem Equation307_359_implies_Equation3456 (G : Type*) [Magma G] (h307 : Equation307 G) (h359 : Equation359 G) : Equation3456 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation307_359_implies_Equation3862 (G : Type*) [Magma G] (h307 : Equation307 G) (h359 : Equation359 G) : Equation3862 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h359 sK0]
    conv => enter [1, 1]; rw [h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation307_411_implies_Equation3 (G : Type*) [Magma G] (h307 : Equation307 G) (h411 : Equation411 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h411 sK0]
    conv => enter [1, 2, 2]; rw [← h307 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 2]; rw [← h307 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

theorem Equation359_3050_implies_Equation3 (G : Type*) [Magma G] (h359 : Equation359 G) (h3050 : Equation3050 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3050 sK0]
    conv => enter [1, 1, 1]; rw [← h359 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 1]; rw [← h359 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

theorem Equation307_1020_implies_Equation99 (G : Type*) [Magma G] (h307 : Equation307 G) (h1020 : Equation1020 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1020 sK0]
    conv => enter [1, 2, 1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation359_2441_implies_Equation203 (G : Type*) [Magma G] (h359 : Equation359 G) (h2441 : Equation2441 G) : Equation203 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h2441 sK0]
    conv => enter [1, 1, 2]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation307_1426_implies_Equation23 (G : Type*) [Magma G] (h307 : Equation307 G) (h1426 : Equation1426 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1426 sK0]
    conv => enter [1, 2]; rw [← h307 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h307 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation307_1426_implies_Equation151 (G : Type*) [Magma G] (h307 : Equation307 G) (h1426 : Equation1426 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1426 sK0]
    conv => enter [1, 2]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation359_2035_implies_Equation8 (G : Type*) [Magma G] (h359 : Equation359 G) (h2035 : Equation2035 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h2035 sK0]
    conv => enter [1, 1]; rw [← h359 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h359 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation359_2035_implies_Equation151 (G : Type*) [Magma G] (h359 : Equation359 G) (h2035 : Equation2035 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h2035 sK0]
    conv => enter [1, 1]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation307_1832_implies_Equation23 (G : Type*) [Magma G] (h307 : Equation307 G) (h1832 : Equation1832 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1832 sK0]
    conv => enter [1, 1]; rw [← h307 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h307 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation307_1832_implies_Equation151 (G : Type*) [Magma G] (h307 : Equation307 G) (h1832 : Equation1832 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1832 sK0]
    conv => enter [1, 1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation359_1629_implies_Equation8 (G : Type*) [Magma G] (h359 : Equation359 G) (h1629 : Equation1629 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1629 sK0]
    conv => enter [1, 2]; rw [← h359 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h359 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation359_1629_implies_Equation151 (G : Type*) [Magma G] (h359 : Equation359 G) (h1629 : Equation1629 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1629 sK0]
    conv => enter [1, 2]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation307_2238_implies_Equation23 (G : Type*) [Magma G] (h307 : Equation307 G) (h2238 : Equation2238 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h2238 sK0]
    conv => enter [1, 1, 2]; rw [← h307 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation359_1223_implies_Equation8 (G : Type*) [Magma G] (h359 : Equation359 G) (h1223 : Equation1223 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1223 sK0]
    conv => enter [1, 2, 1]; rw [← h359 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 2]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation307_2847_implies_Equation255 (G : Type*) [Magma G] (h307 : Equation307 G) (h2847 : Equation2847 G) : Equation255 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h2847 sK0]
    conv => enter [1, 1, 1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation359_614_implies_Equation47 (G : Type*) [Magma G] (h359 : Equation359 G) (h614 : Equation614 G) : Equation47 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h614 sK0]
    conv => enter [1, 2, 2]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation307_3862_implies_Equation4380 (G : Type*) [Magma G] (h307 : Equation307 G) (h3862 : Equation3862 G) : Equation4380 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3862 sK0]
    conv => enter [1, 1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [← h307 x]
  conv => enter [1]; rw [l0 x]

theorem Equation307_3862_implies_Equation359 (G : Type*) [Magma G] (h307 : Equation307 G) (h3862 : Equation3862 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3862 sK0]
    conv => enter [1, 1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation359_3456_implies_Equation4380 (G : Type*) [Magma G] (h359 : Equation359 G) (h3456 : Equation3456 G) : Equation4380 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3456 sK0]
    conv => enter [1, 2]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [h359 x]

theorem Equation359_3456_implies_Equation307 (G : Type*) [Magma G] (h359 : Equation359 G) (h3456 : Equation3456 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3456 sK0]
    conv => enter [1, 2]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation307_4380_implies_Equation359 (G : Type*) [Magma G] (h307 : Equation307 G) (h4380 : Equation4380 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation359_4380_implies_Equation307 (G : Type*) [Magma G] (h359 : Equation359 G) (h4380 : Equation4380 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h359 sK0]
    conv => enter [1]; rw [← h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation411_3253_implies_Equation8 (G : Type*) [Magma G] (h411 : Equation411 G) (h3253 : Equation3253 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h3253 X0]
    conv => enter [1]; rw [← h411 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation3050_4065_implies_Equation23 (G : Type*) [Magma G] (h3050 : Equation3050 G) (h4065 : Equation4065 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h4065 X0]
    conv => enter [1]; rw [← h3050 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation411_4380_implies_Equation614 (G : Type*) [Magma G] (h411 : Equation411 G) (h4380 : Equation4380 G) : Equation614 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h411 sK0]
    conv => enter [1, 2, 2]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation3050_4380_implies_Equation2847 (G : Type*) [Magma G] (h3050 : Equation3050 G) (h4380 : Equation4380 G) : Equation2847 G := by
  have l0 : ∀ X0 : G, (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h4380 X0]
    conv => enter [1]; rw [← h3050 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation614_3456_implies_Equation8 (G : Type*) [Magma G] (h614 : Equation614 G) (h3456 : Equation3456 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h3456 X0]
    conv => enter [1]; rw [← h614 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation2847_3862_implies_Equation23 (G : Type*) [Magma G] (h2847 : Equation2847 G) (h3862 : Equation3862 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h3862 X0]
    conv => enter [1]; rw [← h2847 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation614_4380_implies_Equation411 (G : Type*) [Magma G] (h614 : Equation614 G) (h4380 : Equation4380 G) : Equation411 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4380 X0]
    conv => enter [1]; rw [← h614 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation2847_4380_implies_Equation3050 (G : Type*) [Magma G] (h2847 : Equation2847 G) (h4380 : Equation4380 G) : Equation3050 G := by
  have l0 : ∀ sK0 : G, sK0 = ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h2847 sK0]
    conv => enter [1, 1, 1]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation817_3659_implies_Equation8 (G : Type*) [Magma G] (h817 : Equation817 G) (h3659 : Equation3659 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h3659 X0]
    conv => enter [1]; rw [← h817 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation2644_3659_implies_Equation23 (G : Type*) [Magma G] (h2644 : Equation2644 G) (h3659 : Equation3659 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h3659 X0]
    conv => enter [1]; rw [← h2644 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation1020_3862_implies_Equation8 (G : Type*) [Magma G] (h1020 : Equation1020 G) (h3862 : Equation3862 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h3862 X0]
    conv => enter [1]; rw [← h1020 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation2441_3456_implies_Equation23 (G : Type*) [Magma G] (h2441 : Equation2441 G) (h3456 : Equation3456 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h3456 X0]
    conv => enter [1]; rw [← h2441 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation1020_4380_implies_Equation1223 (G : Type*) [Magma G] (h1020 : Equation1020 G) (h4380 : Equation4380 G) : Equation1223 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1020 sK0]
    conv => enter [1, 2, 1]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation2441_4380_implies_Equation2238 (G : Type*) [Magma G] (h2441 : Equation2441 G) (h4380 : Equation4380 G) : Equation2238 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h4380 X0]
    conv => enter [1]; rw [← h2441 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation1223_4065_implies_Equation8 (G : Type*) [Magma G] (h1223 : Equation1223 G) (h4065 : Equation4065 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4065 X0]
    conv => enter [1]; rw [← h1223 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation2238_3253_implies_Equation23 (G : Type*) [Magma G] (h2238 : Equation2238 G) (h3253 : Equation3253 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h3253 X0]
    conv => enter [1]; rw [← h2238 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation1223_4380_implies_Equation1020 (G : Type*) [Magma G] (h1223 : Equation1223 G) (h4380 : Equation4380 G) : Equation1020 G := by
  have l0 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 1]; rw [h4380 X0]
    conv => enter [1]; rw [← h1223 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation2238_4380_implies_Equation2441 (G : Type*) [Magma G] (h2238 : Equation2238 G) (h4380 : Equation4380 G) : Equation2441 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h2238 sK0]
    conv => enter [1, 1, 2]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation1426_4380_implies_Equation1629 (G : Type*) [Magma G] (h1426 : Equation1426 G) (h4380 : Equation4380 G) : Equation1629 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1426 sK0]
    conv => enter [1, 2]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation2035_4380_implies_Equation1832 (G : Type*) [Magma G] (h2035 : Equation2035 G) (h4380 : Equation4380 G) : Equation1832 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h4380 X0]
    conv => enter [1]; rw [← h2035 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation1629_4380_implies_Equation1426 (G : Type*) [Magma G] (h1629 : Equation1629 G) (h4380 : Equation4380 G) : Equation1426 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4380 X0]
    conv => enter [1]; rw [← h1629 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation1832_4380_implies_Equation2035 (G : Type*) [Magma G] (h1832 : Equation1832 G) (h4380 : Equation4380 G) : Equation2035 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h1832 sK0]
    conv => enter [1, 1]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation3253_4380_implies_Equation3456 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h4380 : Equation4380 G) : Equation3456 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1, 2]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation4065_4380_implies_Equation3862 (G : Type*) [Magma G] (h4065 : Equation4065 G) (h4380 : Equation4380 G) : Equation3862 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4065 X0]
    conv => enter [1, 1]; rw [← h4380 X0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation3456_4380_implies_Equation3253 (G : Type*) [Magma G] (h3456 : Equation3456 G) (h4380 : Equation4380 G) : Equation3253 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h3456 X0]
    conv => enter [1, 2]; rw [← h4380 X0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation3862_4380_implies_Equation4065 (G : Type*) [Magma G] (h3862 : Equation3862 G) (h4380 : Equation4380 G) : Equation4065 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3862 sK0]
    conv => enter [1, 1]; rw [h4380 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

end OneVariable
