import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_54666 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (325102 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 21]⟩], 22⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
