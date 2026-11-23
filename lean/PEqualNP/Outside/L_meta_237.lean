import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.LMeta237Aux

/-- The binary gate that reads the same wires as g and computes the same value: the first
input wire becomes the left argument, the second the right, and a gate with fewer than two
inputs ignores what it does not read. -/
def toBinaryGate (g : Gate) : BinaryGate :=
  match g.inputs with
  | [] => { op := fun _ _ => g.op.eval [], left := 0, right := 0 }
  | [a] => { op := fun p _ => g.op.eval [p], left := a, right := 0 }
  | a :: b :: _ => { op := fun p q => g.op.eval [p, q], left := a, right := b }

/-- One gate step computes the same wire value in both bases, as long as the gate reads at most
two wires. -/
theorem gate_step (g : Gate) (h : g.inputs.length ≤ 2) (w : List Bool) :
    (toBinaryGate g).op (w.getD (toBinaryGate g).left false) (w.getD (toBinaryGate g).right false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  cases g with
  | mk op inputs =>
    match inputs with
    | [] => rfl
    | [a] => rfl
    | [a, b] => rfl
    | a :: b :: c :: t =>
      simp only [List.length_cons] at h
      omega

/-- The two wire lists are the same, gate by gate. -/
theorem foldl_map_eq (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ x : List Bool,
    List.foldl
      (fun w (g : BinaryGate) => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x
      (gs.map toBinaryGate) =
    List.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x gs := by
  induction gs with
  | nil => intro x; rfl
  | cons g gs ih =>
    intro x
    simp only [List.map_cons, List.foldl_cons]
    rw [gate_step g (h g (by simp)) x]
    exact ih (fun g' hg' => h g' (List.mem_cons.mpr (Or.inr hg'))) _

/-- The circuit over the full binary basis that reads the same wires in the same order. -/
def toBinary (C : Circuit) : BinaryCircuit := ⟨C.gates.map toBinaryGate, C.output⟩

theorem toBinary_output (C : Circuit) : (toBinary C).output = C.output := rfl

theorem toBinary_size (C : Circuit) : (toBinary C).size = C.size := by
  show (C.gates.map toBinaryGate).length = C.gates.length
  rw [List.length_map]

theorem toBinary_wires (C : Circuit) (hf : FanInTwo C) (x : List Bool) :
    (toBinary C).wires x = C.wires x :=
  foldl_map_eq C.gates (fun g hg => (hf g hg).2) x

theorem toBinary_eval (C : Circuit) (hf : FanInTwo C) (x : List Bool) :
    (toBinary C).eval x = C.eval x := by
  show ((toBinary C).wires x).getD (toBinary C).output false = (C.wires x).getD C.output false
  rw [toBinary_output, toBinary_wires C hf x]

end PEqualNP.Outside.LMeta237Aux

theorem PEqualNP.Outside.L_meta_237 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
      PEqualNP.MetaComplexity.HasCircuitSize n f s →
        PEqualNP.MetaComplexity.HasBinarySize n f s := by
  intro n f s h
  obtain ⟨C, hf, hsize, heval⟩ := h
  refine ⟨PEqualNP.Outside.LMeta237Aux.toBinary C, ?_, ?_⟩
  · rw [PEqualNP.Outside.LMeta237Aux.toBinary_size]
    exact hsize
  · intro x
    rw [PEqualNP.Outside.LMeta237Aux.toBinary_eval C hf (List.ofFn x), heval x]
