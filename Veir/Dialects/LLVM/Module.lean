module

public import Veir.Interpreter.Calls
public import Veir.Dialects.LLVM.OpInfo
import all Veir.Interpreter.Memory

/-!
# The memory of a module

`MemoryState.ofModule M heapLimit` gives each function of `M` a 1-byte object and each global
an object of its initial bytes, and records the symbol of each object. In a memory reachable
from it (`MemoryState.SymbolsAgree`), `llvm.mlir.addressof @s` returns the start of the object
of `s`, and `globalAt?` of that pointer is `s`.
-/

public section

namespace Veir

/-- Add an object of `size` bytes for the symbol `s` at the next base. -/
@[expose]
def MemoryState.addSymbol (mem : MemoryState) (s : String) (size : Nat) : MemoryState :=
  { mem with
    objects := mem.objects.push { base := mem.nextBase.toUInt64, size, symbol := some s }
    globals := mem.globals.insert s mem.objects.size }

/-- Write the bytes `init`, not poison, from `base`. -/
@[expose]
def MemoryState.fillBytes (mem : MemoryState) (base : UInt64) (init : ByteArray) : MemoryState :=
  let bytes := (List.range init.size).foldl
    (fun bs i => bs.insert (base + i.toUInt64) (⟨init[i]!, 0⟩ : MemoryByte)) mem.bytes
  { mem with bytes }

/-- The memory of a module: one 1-byte object per function and one object per global, globals
    filled with their initial bytes. -/
@[expose]
def MemoryState.ofModule {ctx : WfIRContext OpCode} (M : ModuleEnv ctx) (heapLimit : Nat) :
    MemoryState :=
  let m₀ : MemoryState := { MemoryState.empty with heapLimit }
  let m₁ := M.functions.keys.foldl (fun m s => m.addSymbol s 1) m₀
  M.globals.foldl (fun m g =>
    let base := m.nextBase.toUInt64
    (m.addSymbol g.1 (max 1 g.2.size)).fillBytes base g.2) m₁

/-- Every symbol of the memory names an object that records it. -/
def MemoryState.SymbolsRecorded (mem : MemoryState) : Prop :=
  ∀ s i, mem.globals[s]? = some i → ∃ o : MemoryObject, mem.objects[i]? = some o ∧ o.symbol = some s

/-- `mem` is reachable from `mem₀` as far as symbols go: the same symbol table, and every object
    of `mem₀` is still there with its base and symbol. -/
def MemoryState.SymbolsAgree (mem₀ mem : MemoryState) : Prop :=
  mem.globals = mem₀.globals ∧
    ∀ (i : Nat) (o : MemoryObject), mem₀.objects[i]? = some o → ∃ o' : MemoryObject, mem.objects[i]? = some o' ∧ o'.base = o.base ∧
      o'.symbol = o.symbol

theorem MemoryState.SymbolsAgree.refl (mem : MemoryState) : mem.SymbolsAgree mem :=
  ⟨rfl, fun _ o h => ⟨o, h, rfl, rfl⟩⟩

theorem MemoryState.SymbolsAgree.trans {m₁ m₂ m₃ : MemoryState} (h₁ : m₁.SymbolsAgree m₂)
    (h₂ : m₂.SymbolsAgree m₃) : m₁.SymbolsAgree m₃ := by
  refine ⟨h₂.1.trans h₁.1, fun i o h => ?_⟩
  obtain ⟨o', h', hb, hs⟩ := h₁.2 i o h
  obtain ⟨o'', h'', hb', hs'⟩ := h₂.2 i o' h'
  exact ⟨o'', h'', hb'.trans hb, hs'.trans hs⟩

theorem MemoryState.symbolsRecorded_addSymbol {mem : MemoryState} (h : mem.SymbolsRecorded)
    (s : String) (size : Nat) : (mem.addSymbol s size).SymbolsRecorded := by
  intro s' i hi
  simp only [addSymbol, Std.HashMap.getElem?_insert] at hi ⊢
  split at hi
  · rename_i heq
    simp only [beq_iff_eq] at heq
    subst heq
    cases hi
    exact ⟨{ base := mem.nextBase.toUInt64, size, symbol := some s }, by simp, rfl⟩
  · obtain ⟨o, ho, hs⟩ := h s' i hi
    refine ⟨o, ?_, hs⟩
    rw [Array.getElem?_push]
    have : i < mem.objects.size := by
      rcases Array.getElem?_eq_some_iff.mp ho with ⟨hlt, _⟩; exact hlt
    simp [Nat.ne_of_lt this, ho]

theorem MemoryState.symbolsRecorded_fillBytes {mem : MemoryState} (h : mem.SymbolsRecorded)
    (base : UInt64) (init : ByteArray) : (mem.fillBytes base init).SymbolsRecorded := h

theorem MemoryState.symbolsRecorded_empty (l : Nat) :
    ({ MemoryState.empty with heapLimit := l } : MemoryState).SymbolsRecorded := by
  intro s i hi; simp [MemoryState.empty] at hi

theorem MemoryState.symbolsRecorded_ofModule {ctx : WfIRContext OpCode} (M : ModuleEnv ctx)
    (l : Nat) : (MemoryState.ofModule M l).SymbolsRecorded := by
  unfold ofModule
  dsimp only
  have h₁ : ∀ (ks : List String) (m : MemoryState), m.SymbolsRecorded →
      (ks.foldl (fun m s => m.addSymbol s 1) m).SymbolsRecorded := by
    intro ks; induction ks with
    | nil => intro m h; exact h
    | cons k ks ih => intro m h; exact ih _ (symbolsRecorded_addSymbol h k 1)
  have h₂ : ∀ (gs : List (String × ByteArray)) (m : MemoryState), m.SymbolsRecorded →
      (gs.foldl (fun m g => (m.addSymbol g.1 (max 1 g.2.size)).fillBytes m.nextBase.toUInt64 g.2)
        m).SymbolsRecorded := by
    intro gs; induction gs with
    | nil => intro m h; exact h
    | cons g gs ih =>
      intro m h
      exact ih _ (symbolsRecorded_fillBytes (symbolsRecorded_addSymbol h _ _) _ _)
  exact h₂ _ _ (h₁ _ _ (symbolsRecorded_empty l))

theorem MemoryState.contains_ofModule {ctx : WfIRContext OpCode} (M : ModuleEnv ctx) (l : Nat)
    {s : String} (hs : s ∈ M.functions) : s ∈ (MemoryState.ofModule M l).globals := by
  unfold ofModule
  dsimp only
  have h₁ : ∀ (ks : List String) (m : MemoryState), (s ∈ ks ∨ s ∈ m.globals) →
      s ∈ (ks.foldl (fun m s => m.addSymbol s 1) m).globals := by
    intro ks; induction ks with
    | nil => intro m h; simpa using h
    | cons k ks ih =>
      intro m h
      apply ih
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · right; simp [addSymbol]
        · left; exact h
      · right; simp [addSymbol, h]
  have h₂ : ∀ (gs : List (String × ByteArray)) (m : MemoryState), s ∈ m.globals →
      s ∈ (gs.foldl (fun m g => (m.addSymbol g.1 (max 1 g.2.size)).fillBytes m.nextBase.toUInt64 g.2)
        m).globals := by
    intro gs; induction gs with
    | nil => intro m h; exact h
    | cons g gs ih =>
      intro m h
      apply ih
      simp [addSymbol, fillBytes, h]
  exact h₂ _ _ (h₁ _ _ (.inl (Std.HashMap.mem_keys.mpr hs)))

/-- In a memory reachable from one where every symbol is recorded (such as
    `MemoryState.ofModule M l`), `llvm.mlir.addressof @s` of a symbol `s` of the memory returns
    the start of the object of `s`, and `globalAt?` of that pointer is `s`. -/
theorem interpretOp_addressof {mem₀ mem : MemoryState} (hrec : mem₀.SymbolsRecorded)
    (hagree : mem₀.SymbolsAgree mem) {s : String} (hs : s ∈ mem₀.globals)
    (properties : propertiesOf (Llvm.mlir__addressof)) (hname : properties.global_name.value = s)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (layout : DataLayout) :
    ∃ p : Data.Pointer,
      Llvm.interpretOp' .mlir__addressof properties resultTypes operands blockOperands mem layout =
        .ok (#[.addr (.val p)], mem, none) ∧
      p.object = mem₀.globals[s] ∧ mem.globalAt? p = some s := by
  have hi : mem₀.globals[s]? = some mem₀.globals[s] := Std.HashMap.getElem?_eq_some_getElem hs
  generalize mem₀.globals[s] = i at hi ⊢
  obtain ⟨o, ho, hos⟩ := hrec s i hi
  obtain ⟨o', ho', -, hos'⟩ := hagree.2 i o ho
  refine ⟨⟨i, o'.base⟩, ?_, ?_, ?_⟩
  · have hp : mem.pointerToGlobal s = some ⟨i, o'.base⟩ := by
      simp [MemoryState.pointerToGlobal, hagree.1, hi, ho']
    simp only [Llvm.interpretOp', hname, hp]; rfl
  · rfl
  · simp [MemoryState.globalAt?, ho', hos', hos]

/-- For the memory of a module: for a function `s` of `M` and a memory reachable from
    `MemoryState.ofModule M l`, `llvm.mlir.addressof @s` returns the start of the object of `s`,
    and `globalAt?` of it is `s`. -/
theorem interpretOp_addressof_ofModule {ctx : WfIRContext OpCode} (M : ModuleEnv ctx) (l : Nat)
    {mem : MemoryState} (hagree : (MemoryState.ofModule M l).SymbolsAgree mem)
    {s : String} (hs : s ∈ M.functions)
    (properties : propertiesOf (Llvm.mlir__addressof)) (hname : properties.global_name.value = s)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (layout : DataLayout) :
    ∃ p : Data.Pointer,
      Llvm.interpretOp' .mlir__addressof properties resultTypes operands blockOperands mem layout =
        .ok (#[.addr (.val p)], mem, none) ∧ mem.globalAt? p = some s := by
  obtain ⟨p, h₁, -, h₃⟩ := interpretOp_addressof (MemoryState.symbolsRecorded_ofModule M l) hagree
    (MemoryState.contains_ofModule M l hs) properties hname resultTypes operands blockOperands layout
  exact ⟨p, h₁, h₃⟩

end Veir
