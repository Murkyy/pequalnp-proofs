import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_940

set_option maxHeartbeats 4000000 in
theorem c1 : (∀ C1 : PEqualNP.CircuitLowerBounds.Circuit, C1 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 15]⟩], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C1 ∧ C1.size = 12 ∧ (∀ x1 : Fin 8 → Bool, (C1.eval (List.ofFn x1) = true ↔ ∃ u1 v1 : Fin 8, (u1.val, v1.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x1 u1 = true ∧ x1 v1 = true))) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : Bool, x = ![a0, a1, a2, a3, a4, a5, a6, a7] :=
      ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, by funext i; fin_cases i <;> rfl⟩
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> cases a7 <;> decide

set_option maxHeartbeats 4000000 in
theorem c2 : (∀ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 15]⟩], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C2 ∧ C2.size = 12 ∧ (∀ x2 : Fin 8 → Bool, (C2.eval (List.ofFn x2) = true ↔ ∃ u2 v2 : Fin 8, (u2.val, v2.val) ∈ ([(0, 1), (1, 7), (2, 3), (2, 4), (3, 4), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x2 u2 = true ∧ x2 v2 = true))) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : Bool, x = ![a0, a1, a2, a3, a4, a5, a6, a7] :=
      ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, by funext i; fin_cases i <;> rfl⟩
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> cases a7 <;> decide

set_option maxHeartbeats 4000000 in
theorem c3 : (∀ C3 : PEqualNP.CircuitLowerBounds.Circuit, C3 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 15]⟩], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C3 ∧ C3.size = 12 ∧ (∀ x3 : Fin 8 → Bool, (C3.eval (List.ofFn x3) = true ↔ ∃ u3 v3 : Fin 8, (u3.val, v3.val) ∈ ([(0, 1), (2, 3), (2, 6), (3, 6), (4, 5), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x3 u3 = true ∧ x3 v3 = true))) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : Bool, x = ![a0, a1, a2, a3, a4, a5, a6, a7] :=
      ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, by funext i; fin_cases i <;> rfl⟩
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> cases a7 <;> decide

end PEqualNP.Outside.L_meta_940

theorem PEqualNP.Outside.L_meta_940 : (∀ C1 : PEqualNP.CircuitLowerBounds.Circuit, C1 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 15]⟩], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C1 ∧ C1.size = 12 ∧ (∀ x1 : Fin 8 → Bool, (C1.eval (List.ofFn x1) = true ↔ ∃ u1 v1 : Fin 8, (u1.val, v1.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x1 u1 = true ∧ x1 v1 = true))) ∧ (∀ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 15]⟩], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C2 ∧ C2.size = 12 ∧ (∀ x2 : Fin 8 → Bool, (C2.eval (List.ofFn x2) = true ↔ ∃ u2 v2 : Fin 8, (u2.val, v2.val) ∈ ([(0, 1), (1, 7), (2, 3), (2, 4), (3, 4), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x2 u2 = true ∧ x2 v2 = true))) ∧ (∀ C3 : PEqualNP.CircuitLowerBounds.Circuit, C3 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 15]⟩], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C3 ∧ C3.size = 12 ∧ (∀ x3 : Fin 8 → Bool, (C3.eval (List.ofFn x3) = true ↔ ∃ u3 v3 : Fin 8, (u3.val, v3.val) ∈ ([(0, 1), (2, 3), (2, 6), (3, 6), (4, 5), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x3 u3 = true ∧ x3 v3 = true))) :=
  ⟨PEqualNP.Outside.L_meta_940.c1, PEqualNP.Outside.L_meta_940.c2, PEqualNP.Outside.L_meta_940.c3⟩
