module
public import Veir.Interpreter.Basic
import all Veir.Interpreter.Memory
import all Veir.Interpreter.Basic

/-!
# Allocation, loads and stores

Allocation (`MemoryState.alloc_spec`, `MemoryState.alloc_fail_iff`), the frame lemmas of loads and
stores, and the liveness of heap and stack objects across a return.
-/

public section
namespace Veir
open Veir.Data

theorem MemoryState.le_nextBase_aux (l : List MemoryObject) (init : Nat) :
    init ≤ l.foldl (fun past obj => max past (obj.base.toNat + obj.size + 1)) init ∧
    ∀ o ∈ l, o.base.toNat + o.size + 1 ≤
      l.foldl (fun past obj => max past (obj.base.toNat + obj.size + 1)) init := by
  induction l generalizing init with
  | nil => simp
  | cons o l ih =>
    obtain ⟨h₁, h₂⟩ := ih (max init (o.base.toNat + o.size + 1))
    refine ⟨by simp only [List.foldl_cons]; omega, ?_⟩
    intro o' ho'
    rcases List.mem_cons.mp ho' with rfl | ho'
    · simp only [List.foldl_cons]; omega
    · exact h₂ o' ho'

/-- Every object ends, with its guard byte, at or before `nextBase`. -/
theorem MemoryState.end_le_nextBase (mem : MemoryState) {o : MemoryObject} (ho : o ∈ mem.objects) :
    o.base.toNat + o.size + 1 ≤ mem.nextBase := by
  unfold nextBase
  dsimp only
  rw [← Array.foldl_toList]
  have := (le_nextBase_aux mem.objects.toList arenaSize.toNat).2 o (Array.mem_toList_iff.mpr ho)
  have h16 : objectAlignment.toNat = 16 := rfl
  rw [h16]
  omega

theorem MemoryState.nextBase_mod (mem : MemoryState) : mem.nextBase % 16 = 0 := by
  unfold nextBase
  have h16 : objectAlignment.toNat = 16 := rfl
  simp only [h16]
  exact Nat.mul_mod_left _ _

theorem MemoryState.arena_le_nextBase (mem : MemoryState) : arenaSize.toNat ≤ mem.nextBase := by
  unfold nextBase
  dsimp only
  rw [← Array.foldl_toList]
  have := (le_nextBase_aux mem.objects.toList arenaSize.toNat).1
  have h16 : objectAlignment.toNat = 16 := rfl
  rw [h16]
  omega

/-- A successful allocation appends an object at the next base, aligned to 16 bytes and
    past every object present (with a guard byte), and leaves the bytes and the other fields of
    the memory unchanged. -/
theorem MemoryState.alloc_spec {mem mem' : MemoryState} {n : UInt64} {frame : Option Nat}
    {p : Pointer} (h : mem.alloc n frame = .ok (mem', p)) :
    p.object = mem.objects.size ∧ p.address.toNat % 16 = 0 ∧ p.address.toNat = mem.nextBase ∧
    mem'.objects = mem.objects.push { base := p.address, size := n.toNat, frame } ∧
    mem'.bytes = mem.bytes ∧ mem'.globals = mem.globals ∧ mem'.heapLimit = mem.heapLimit ∧
    mem'.depth = mem.depth ∧
    (∀ o ∈ mem.objects, o.base.toNat + o.size < p.address.toNat) ∧
    p.address.toNat + n.toNat < mem.heapLimit := by
  unfold alloc at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hlim
    simp only [Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlt : mem.nextBase < 2 ^ 64 := by omega
    have hb : (UInt64.ofNat mem.nextBase).toNat = mem.nextBase := by
      rw [UInt64.toNat_ofNat_of_lt' hlt]
    refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · show (UInt64.ofNat mem.nextBase).toNat % 16 = 0
      rw [hb]; exact mem.nextBase_mod
    · exact hb
    · intro o ho
      have := mem.end_le_nextBase ho
      show o.base.toNat + o.size < (UInt64.ofNat mem.nextBase).toNat
      rw [hb]; omega
    · show (UInt64.ofNat mem.nextBase).toNat + n.toNat < mem.heapLimit
      rw [hb]; omega

theorem MemoryState.alloc_ne_ub (mem : MemoryState) (n : UInt64) (frame : Option Nat)
    (op : Option OperationPtr) : mem.alloc n frame ≠ .ub op := by
  unfold alloc; dsimp only; split <;> (intro h; cases h)

/-- Allocation fails exactly when the object with its guard byte would end past the heap
    limit (for a heap limit within the address space). -/
theorem MemoryState.alloc_fail_iff (mem : MemoryState) (n : UInt64) (frame : Option Nat)
    (hlim : mem.heapLimit ≤ 2 ^ 64) :
    (∃ op, mem.alloc n frame = .fail op) ↔ mem.nextBase + n.toNat + 1 > mem.heapLimit := by
  unfold alloc; dsimp only
  split
  · rename_i h; exact ⟨fun _ => by omega, fun _ => ⟨none, rfl⟩⟩
  · rename_i h
    constructor
    · rintro ⟨_, h'⟩; cases h'
    · intro; omega

/-! ## Liveness across a return -/

theorem MemoryState.popFrame_size (mem : MemoryState) (d : Nat) :
    (mem.popFrame d).objects.size = mem.objects.size := by
  simp [popFrame]

/-- An object of another frame than `d + 1` (a heap, global or function object, or an object of
    an outer frame) is unchanged by the return to depth `d`. -/
theorem MemoryState.popFrame_getElem?_of_ne {mem : MemoryState} {d i : Nat} {o : MemoryObject}
    (ho : mem.objects[i]? = some o) (hf : o.frame ≠ some (d + 1)) :
    (mem.popFrame d).objects[i]? = some o := by
  simp [popFrame, ho, hf]

/-- An object of the frame `d + 1` is dead after the return to depth `d`. -/
theorem MemoryState.popFrame_getElem?_of_eq {mem : MemoryState} {d i : Nat} {o : MemoryObject}
    (ho : mem.objects[i]? = some o) (hf : o.frame = some (d + 1)) :
    (mem.popFrame d).objects[i]? = some { o with live := false } := by
  simp [popFrame, ho, hf]

theorem MemoryState.popFrame_bytes (mem : MemoryState) (d : Nat) :
    (mem.popFrame d).bytes = mem.bytes := by simp [popFrame]

theorem MemoryState.popFrame_depth (mem : MemoryState) (d : Nat) :
    (mem.popFrame d).depth = d := by simp [popFrame]

/-- An access of a nonzero number of bytes to a dead object is UB. -/
theorem MemoryState.checkAccess_dead {mem : MemoryState} {p : Pointer} {o : MemoryObject}
    (ho : mem.objects[p.object]? = some o) (hdead : o.live = false) (n : UInt64) :
    mem.checkAccess p n = .ub none := by
  simp [checkAccess, getObject?, ho, hdead]

theorem MemoryState.load_dead {mem : MemoryState} {p : Pointer} {o : MemoryObject}
    (ho : mem.objects[p.object]? = some o) (hdead : o.live = false) (n : UInt64) :
    mem.load p n = .ub none := by
  simp [load, checkAccess_dead ho hdead]

theorem MemoryState.loadPoison_dead {mem : MemoryState} {p : Pointer} {o : MemoryObject}
    (ho : mem.objects[p.object]? = some o) (hdead : o.live = false) (n : UInt64) :
    mem.loadPoison p n = .ub none := by
  simp [loadPoison, checkAccess_dead ho hdead]

theorem MemoryState.store_dead {mem : MemoryState} {p : Pointer} {o : MemoryObject}
    (ho : mem.objects[p.object]? = some o) (hdead : o.live = false) (val poison : ByteArray)
    (h : poison.size = val.size) :
    mem.store p val poison h = .ub none := by
  simp [store, checkAccess_dead ho hdead]

/-- A load of an `i8`, `i16`, `i32`, `i64` or `ptr` from a dead object is UB. -/
theorem MemoryState.llvmLoad_dead {mem : MemoryState} {p : Pointer} {o : MemoryObject}
    (ho : mem.objects[p.object]? = some o) (hdead : o.live = false) (type : TypeAttr)
    (htype : (∃ w s, type.val = .integerType ⟨w, s⟩ ∧ (w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)) ∨
      ∃ a, type.val = .llvmPointerType a) :
    mem.llvmLoad p type = .ub none := by
  unfold llvmLoad
  by_cases hnull : p = .null
  · simp [hnull]
  · simp only [hnull, ite_false]
    rcases htype with ⟨w, s, ht, hw⟩ | ⟨a, ht⟩
    · rcases hw with rfl | rfl | rfl | rfl <;> rw [ht] <;>
        simp only [load_dead ho hdead, Interp.bind_ub]
    · rw [ht]; simp only [loadByte64, load_dead ho hdead, Interp.bind_ub]

/-- A store of an `i8`, `i16`, `i32`, `i64` or `ptr` value to a dead object is UB. -/
theorem MemoryState.llvmStore_dead {mem : MemoryState} {p : Pointer} {o : MemoryObject}
    (ho : mem.objects[p.object]? = some o) (hdead : o.live = false) (val : RuntimeValue)
    (hval : (∃ (w : Nat) (v : Data.LLVM.Int w), val = .int w v ∧ (w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)) ∨
      ∃ q, val = .addr q) :
    mem.llvmStore p val = .ub none := by
  unfold llvmStore
  by_cases hnull : p = .null
  · simp [hnull]
  · simp only [hnull, ite_false]
    rcases hval with ⟨w, v, rfl, hw⟩ | ⟨q, rfl⟩
    · rcases hw with rfl | rfl | rfl | rfl <;> cases v <;>
        simp [store_dead ho hdead, empoison]
    · simp [storeByte64, store_dead ho hdead]

/-- The interpretation of a function returns the memory of its body, returned to the depth of
    the call: the body's objects of the frame of the call are dead, all others unchanged. -/
theorem interpretFunction_ok_popFrame {ctx : WfIRContext OpCode} {op : OperationPtr}
    {f : FunctionOp ctx.raw op} {values : Array RuntimeValue} {mem mem' : MemoryState}
    {h : op.InBounds ctx.raw} {call : Option CallOracle} {rs : Array RuntimeValue}
    (hok : interpretFunction f values mem h call = .ok (mem', rs)) :
    ∃ body : MemoryState, mem' = body.popFrame mem.depth := by
  unfold interpretFunction at hok
  split at hok
  · cases hok
  · simp only [Interp.bind_def] at hok
    split at hok
    · cases hok
    · cases hok
    · rename_i a _
      simp only [Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq] at hok
      exact ⟨a.1.memory, hok.1.symm⟩

/-- An object of the body that is not of the frame of the call, such as an
    object allocated by `pg_alloc` (frame `none`), is unchanged, and in particular live, after
    the return. -/
theorem heap_survives_return {ctx : WfIRContext OpCode} {op : OperationPtr}
    {f : FunctionOp ctx.raw op} {values : Array RuntimeValue} {mem mem' : MemoryState}
    {h : op.InBounds ctx.raw} {call : Option CallOracle} {rs : Array RuntimeValue}
    (hok : interpretFunction f values mem h call = .ok (mem', rs)) :
    ∃ body : MemoryState, mem' = body.popFrame mem.depth ∧
      (∀ (i : Nat) (o : MemoryObject), body.objects[i]? = some o → o.frame = none → mem'.objects[i]? = some o) ∧
      (∀ (i : Nat) (o : MemoryObject), body.objects[i]? = some o → o.frame = some (mem.depth + 1) →
        mem'.objects[i]? = some { o with live := false }) := by
  obtain ⟨body, rfl⟩ := interpretFunction_ok_popFrame hok
  refine ⟨body, rfl, fun i o ho hf => ?_, fun i o ho hf => ?_⟩
  · exact MemoryState.popFrame_getElem?_of_ne ho (by simp [hf])
  · exact MemoryState.popFrame_getElem?_of_eq ho hf

/-- The external `pg_alloc(i64) -> ptr`: a heap allocation (frame `none`) of the requested
    number of bytes. -/
@[expose]
def pgAlloc (args : Array RuntimeValue) (mem : MemoryState) :
    Interp (MemoryState × Array RuntimeValue) :=
  match args.toList with
  | [.int 64 (.val n)] => do
    let (mem, p) ← mem.alloc (UInt64.ofBitVec n) none
    return (mem, #[.addr (.val p)])
  | [.int 64 .poison] => .ub none
  | _ => .fail none

/-- An object allocated by `pg_alloc` is a live heap object. -/
theorem pgAlloc_spec {args : Array RuntimeValue} {mem mem' : MemoryState}
    {rs : Array RuntimeValue} (hok : pgAlloc args mem = .ok (mem', rs)) :
    ∃ p : Pointer, rs = #[.addr (.val p)] ∧
      ∃ o, mem'.objects[p.object]? = some o ∧ o.live = true ∧ o.frame = none ∧
        o.base = p.address := by
  unfold pgAlloc at hok
  split at hok
  · simp only [Interp.bind_def] at hok
    split at hok
    · cases hok
    · cases hok
    · rename_i a halloc
      obtain ⟨m, p⟩ := a
      simp only [Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      obtain ⟨hobj, -, -, hobjs, -⟩ := MemoryState.alloc_spec halloc
      refine ⟨p, rfl, ?_⟩
      rw [hobjs, hobj, Array.getElem?_push_size]
      exact ⟨_, rfl, rfl, rfl, rfl⟩
  · cases hok
  · cases hok

end Veir
