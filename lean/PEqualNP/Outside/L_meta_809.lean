import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_809 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 9 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 4), (0, 7), (1, 2), (2, 3), (3, 4), (3, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : Bool, x = ![a0, a1, a2, a3, a4, a5, a6, a7] :=
      ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, by funext i; fin_cases i <;> rfl⟩
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> cases a7 <;> decide
