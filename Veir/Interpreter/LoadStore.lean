module
public import Veir.Interpreter.Heap
import all Veir.Interpreter.Memory
import all Veir.ForLean
import all Std.Data.ByteSlice
import all Init.Data.ByteArray.Extra
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.LLVM.Byte.Basic

/-!
# Loads after stores

`store` as a write of bytes (`MemoryState.store_eq`, `MemoryState.writeBytes`), the bytes
that a store writes and leaves, loads after stores, and the frame lemmas of `llvmLoad` and
`llvmStore`.
-/

public section
namespace Veir
open Veir.Data

theorem List.foldl_attach_eq {α β : Type} {l : List α} (init : β) (g : β → α → β)
    (F : β → {x // x ∈ l} → β) (hF : ∀ b x, F b x = g b x.1) :
    l.attach.foldl F init = l.foldl g init := by
  rw [← List.foldl_attach (f := g)]
  exact congrArg (fun F => List.foldl F init l.attach) (funext fun b => funext fun x => hF b x)

/-- The bytes that `store` writes. -/
@[expose]
def MemoryState.writeBytes (bytes : Std.ExtHashMap UInt64 MemoryByte) (addr : UInt64)
    (val poison : ByteArray) : Std.ExtHashMap UInt64 MemoryByte :=
  (List.range val.size).foldl (fun bs i => bs.insert (addr + i.toUInt64) ⟨val[i]!, poison[i]!⟩) bytes

theorem MemoryState.store_eq (mem : MemoryState) (p : Pointer) (val poison : ByteArray)
    (h : poison.size = val.size) :
    mem.store p val poison h = (do
      mem.checkAccess p val.size.toUInt64
      return { mem with bytes := writeBytes mem.bytes p.address val poison }) := by
  simp only [store, Std.Legacy.Range.forIn'_eq_forIn'_range']
  rw [List.forIn'_pure_yield_eq_foldl, List.foldl_attach_eq (g := fun bs i =>
    bs.insert (p.address + i.toUInt64) ⟨val[i]!, poison[i]!⟩)]
  · simp only [pure_bind, writeBytes, Std.Legacy.Range.size, List.range_eq_range']
    simp
  · rintro b ⟨a, ha⟩
    simp only [List.mem_range'] at ha
    have h1 : a < val.size := by simp [Std.Legacy.Range.size] at ha; omega
    have h2 : a < poison.size := by omega
    simp [getElem!_pos val a h1, getElem!_pos poison a h2]

theorem MemoryState.getD_foldl_insert_of_ne {bytes : Std.ExtHashMap UInt64 MemoryByte}
    (l : List Nat) (k : Nat → UInt64) (v : Nat → MemoryByte) {a : UInt64} {d : MemoryByte}
    (h : ∀ i ∈ l, k i ≠ a) :
    (l.foldl (fun bs i => bs.insert (k i) (v i)) bytes).getD a d = bytes.getD a d := by
  induction l generalizing bytes with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), Std.ExtHashMap.getD_insert]
    simp [h i (List.mem_cons_self ..)]

theorem MemoryState.getD_foldl_insert_of_mem {bytes : Std.ExtHashMap UInt64 MemoryByte}
    (l : List Nat) (k : Nat → UInt64) (v : Nat → MemoryByte) {i : Nat} {d : MemoryByte}
    (hi : i ∈ l) (hnd : l.Nodup) (hk : ∀ j ∈ l, k j = k i → j = i) :
    (l.foldl (fun bs i => bs.insert (k i) (v i)) bytes).getD (k i) d = v i := by
  induction l generalizing bytes with
  | nil => simp at hi
  | cons j l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hi'
    · rw [getD_foldl_insert_of_ne]
      · simp
      · intro j' hj' heq
        have := hk j' (List.mem_cons_of_mem _ hj') heq
        subst this
        exact (List.nodup_cons.mp hnd).1 hj'
    · exact ih hi' (List.nodup_cons.mp hnd).2 (fun j' hj' => hk j' (List.mem_cons_of_mem _ hj'))

theorem UInt64.add_ofNat_inj {a : UInt64} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : a + i.toUInt64 = a + j.toUInt64) : i = j := by
  have h' : i.toUInt64 = j.toUInt64 := by
    have := congrArg (· - a) h
    simpa [UInt64.add_comm a, UInt64.add_sub_cancel] using this
  have := congrArg UInt64.toNat h'
  simpa [UInt64.toNat_ofNat_of_lt' hi, UInt64.toNat_ofNat_of_lt' hj] using this

/-- A byte that `store` wrote. -/
theorem MemoryState.getD_writeBytes_at (bytes : Std.ExtHashMap UInt64 MemoryByte)
    (addr : UInt64) (val poison : ByteArray) {i : Nat} (hi : i < val.size)
    (hsize : val.size ≤ 2 ^ 64) (d : MemoryByte) :
    (writeBytes bytes addr val poison).getD (addr + i.toUInt64) d = ⟨val[i]!, poison[i]!⟩ := by
  unfold writeBytes
  exact getD_foldl_insert_of_mem (List.range val.size) (fun i => addr + i.toUInt64)
    (fun i => ⟨val[i]!, poison[i]!⟩) (List.mem_range.mpr hi) List.nodup_range
    (fun j hj heq => UInt64.add_ofNat_inj (by have := List.mem_range.mp hj; omega) (by omega) heq)

/-- A byte that `store` did not write. -/
theorem MemoryState.getD_writeBytes_of_ne (bytes : Std.ExtHashMap UInt64 MemoryByte)
    (addr : UInt64) (val poison : ByteArray) {a : UInt64}
    (h : ∀ i < val.size, addr + i.toUInt64 ≠ a) (d : MemoryByte) :
    (writeBytes bytes addr val poison).getD a d = bytes.getD a d := by
  unfold writeBytes
  exact getD_foldl_insert_of_ne _ _ _ fun i hi => h i (List.mem_range.mp hi)


theorem MemoryState.store_ok {mem : MemoryState} {p : Pointer} {val poison : ByteArray}
    {h : poison.size = val.size} (hc : mem.checkAccess p val.size.toUInt64 = .ok ()) :
    mem.store p val poison h = .ok { mem with bytes := writeBytes mem.bytes p.address val poison } := by
  rw [store_eq, hc]; rfl

theorem MemoryState.checkAccess_bytes (mem : MemoryState) (bytes : Std.ExtHashMap UInt64 MemoryByte)
    (p : Pointer) (n : UInt64) : ({ mem with bytes } : MemoryState).checkAccess p n = mem.checkAccess p n := by
  simp only [checkAccess, getObject?]

theorem ByteArray.forIn_loop_yield {β : Type} (as : ByteArray) (f : UInt8 → β → Interp (ForInStep β))
    (hf : ∀ (j : Nat) (hj : j < as.size) (b : β), f as[j] b = .ok (.yield b)) :
    ∀ (i : Nat) (h : i ≤ as.size) (b : β), ByteArray.forIn.loop as f i h b = .ok b := by
  intro i
  induction i with
  | zero => intro h b; rfl
  | succ i ih =>
    intro h b
    rw [ByteArray.forIn.loop]
    rw [hf]
    exact ih _ b

theorem ByteArray.forIn_eq_loop {β : Type} (as : ByteArray) (b : β)
    (f : UInt8 → β → Interp (ForInStep β)) :
    forIn as b f = ByteArray.forIn.loop as f as.size (Nat.le_refl _) b := rfl

/-- `hasPoison` of a mask of zero bytes is `false`. -/
theorem MemoryState.hasPoison_of_zero {mem : MemoryState} {p : Pointer} {n : UInt64}
    {mask : ByteArray} (hl : mem.loadPoison p n = .ok mask) (hz : ∀ (j : Nat) (hj : j < mask.size), mask[j] = 0) :
    mem.hasPoison p n = .ok false := by
  unfold hasPoison
  rw [hl]
  simp only [Interp.bind_ok]
  rw [ByteArray.forIn_eq_loop, ByteArray.forIn_loop_yield]
  · rfl
  · intro j hj b; simp [hz j hj]

/-- `hasPoison` of a mask whose first byte is nonzero is `true`. -/
theorem MemoryState.hasPoison_of_first {mem : MemoryState} {p : Pointer} {n : UInt64}
    {mask : ByteArray} (hl : mem.loadPoison p n = .ok mask) (hs : 0 < mask.size)
    (h0 : mask[0] ≠ 0) :
    mem.hasPoison p n = .ok true := by
  unfold hasPoison
  rw [hl]
  simp only [Interp.bind_ok]
  rw [ByteArray.forIn_eq_loop]
  have aux : ∀ (i : Nat) (h : i ≤ mask.size), i = mask.size → ByteArray.forIn.loop mask
      (fun b r => if b ≠ 0 then (pure (ForInStep.done true) : Interp (ForInStep Bool))
        else pure (ForInStep.yield r)) i h false = Interp.ok true := by
    intro i h hi
    cases i with
    | zero => omega
    | succ j =>
      rw [ByteArray.forIn.loop]
      have hidx : mask.size - 1 - j = 0 := by omega
      simp only [hidx]
      rw [if_pos h0]
      rfl
  rw [aux _ _ rfl]; rfl


theorem MemoryState.store_ok_inv {mem mem' : MemoryState} {p : Pointer} {val poison : ByteArray}
    {h : poison.size = val.size} (hs : mem.store p val poison h = .ok mem') :
    mem.checkAccess p val.size.toUInt64 = .ok () ∧
      mem' = { mem with bytes := writeBytes mem.bytes p.address val poison } := by
  rw [store_eq] at hs
  cases hc : mem.checkAccess p val.size.toUInt64 with
  | ok u => rw [hc] at hs; cases hs; exact ⟨rfl, rfl⟩
  | ub _ => rw [hc] at hs; cases hs
  | fail _ => rw [hc] at hs; cases hs

theorem MemoryState.byte_writeBytes_at (mem : MemoryState) (addr : UInt64) (val poison : ByteArray)
    {i : Nat} (hi : i < val.size) (hsize : val.size ≤ 2 ^ 64) :
    ({ mem with bytes := writeBytes mem.bytes addr val poison } : MemoryState).byte
      (addr + i.toUInt64) = ⟨val[i]!, poison[i]!⟩ := by
  simp only [byte]
  exact getD_writeBytes_at _ _ _ _ hi hsize _

theorem MemoryState.byte_writeBytes_of_ne (mem : MemoryState) (addr : UInt64)
    (val poison : ByteArray) {a : UInt64} (h : ∀ i < val.size, addr + i.toUInt64 ≠ a) :
    ({ mem with bytes := writeBytes mem.bytes addr val poison } : MemoryState).byte a =
      mem.byte a := by
  simp only [byte]
  exact getD_writeBytes_of_ne _ _ _ _ h _

/-- A load of the bytes that a store wrote returns them. -/
theorem MemoryState.load_writeBytes {mem : MemoryState} {p : Pointer} {val poison : ByteArray}
    {n : UInt64} (hc : mem.checkAccess p n = .ok ()) (hn : n.toNat = val.size) :
    ({ mem with bytes := writeBytes mem.bytes p.address val poison } : MemoryState).load p n =
      .ok ⟨Array.ofFn fun i : Fin n.toNat => val[i.val]!⟩ := by
  unfold load
  rw [checkAccess_bytes, hc]
  simp only [Interp.bind_ok, Interp.pure_eq, Interp.ok.injEq, ByteArray.mk.injEq]
  congr 1
  funext i
  have hi : i.val < val.size := hn ▸ i.isLt
  rw [byte_writeBytes_at mem p.address val poison hi (by have := n.toNat_lt; omega)]

theorem MemoryState.loadPoison_writeBytes {mem : MemoryState} {p : Pointer} {val poison : ByteArray}
    {n : UInt64} (hc : mem.checkAccess p n = .ok ()) (hn : n.toNat = val.size) :
    ({ mem with bytes := writeBytes mem.bytes p.address val poison } : MemoryState).loadPoison p n =
      .ok ⟨Array.ofFn fun i : Fin n.toNat => poison[i.val]!⟩ := by
  unfold loadPoison
  rw [checkAccess_bytes, hc]
  simp only [Interp.bind_ok, Interp.pure_eq, Interp.ok.injEq, ByteArray.mk.injEq]
  congr 1
  funext i
  have hi : i.val < val.size := hn ▸ i.isLt
  rw [byte_writeBytes_at mem p.address val poison hi (by have := n.toNat_lt; omega)]


theorem ByteArray.data_extend (ba : ByteArray) (n : Nat) (v : UInt8) :
    (ba.extend n v).data = ba.data ++ Array.replicate n v := by
  induction n with
  | zero => simp [ByteArray.extend]
  | succ n ih =>
    have : ba.extend (n + 1) v = (ba.extend n v).push v := by
      simp only [ByteArray.extend, Nat.fold_succ]
    rw [this, ByteArray.data_push, ih, Array.replicate_succ, Array.append_push]

theorem ByteArray.getElem_replicate {n : Nat} {v : UInt8} {i : Nat}
    (hi : i < (ByteArray.replicate n v).size) : (ByteArray.replicate n v)[i] = v := by
  have hd : (ByteArray.replicate n v).data = Array.replicate n v := by
    simp [ByteArray.replicate, ByteArray.data_extend, ByteArray.emptyWithCapacity]; rfl
  rw [ByteArray.getElem_eq_getElem_data]
  simp only [hd, Array.getElem_replicate]

theorem ByteArray.getElem!_replicate (n : Nat) (v : UInt8) (j : Nat) (hj : j < n) :
    (ByteArray.replicate n v)[j]! = v := by
  rw [getElem!_pos (ByteArray.replicate n v) j (by simpa using hj)]
  exact ByteArray.getElem_replicate _

theorem ByteArray.ofFn_replicate_zero (m n : Nat) (j : Nat)
    (hj : j < (⟨Array.ofFn fun i : Fin m => (ByteArray.replicate n 0)[i.val]!⟩ : ByteArray).size) :
    (⟨Array.ofFn fun i : Fin m => (ByteArray.replicate n 0)[i.val]!⟩ : ByteArray)[j] = 0 := by
  rw [ByteArray.getElem_eq_getElem_data]
  simp only [Array.getElem_ofFn]
  by_cases h : j < n
  · exact ByteArray.getElem!_replicate n 0 j h
  · rw [getElem!_neg (ByteArray.replicate n 0) j (by simpa using h)]; rfl

/-- An `i8` load after an `i8` store at the same pointer returns the stored value. -/
theorem MemoryState.llvmLoad_llvmStore_same_i8 {mem mem' : MemoryState} {p : Pointer}
    {v : BitVec 8} (hst : mem.llvmStore p (.int 8 (.val v)) = .ok mem') {ty : TypeAttr}
    {sg : IntegerType.Signedness} (hty : ty.val = .integerType ⟨8, sg⟩) :
    mem'.llvmLoad p ty = .ok (.int 8 (.val v)) := by
  unfold llvmStore at hst
  by_cases hnull : p = .null
  · simp [hnull] at hst
  simp only [hnull, ite_false] at hst
  obtain ⟨hc, rfl⟩ := store_ok_inv hst
  have hc' : mem.checkAccess p 1 = .ok () := by simpa using hc
  unfold llvmLoad
  simp only [hnull, ite_false]
  rw [hty]
  simp only
  rw [load_writeBytes hc' (by simp), hasPoison_of_zero (loadPoison_writeBytes hc' (by simp))
    (fun j hj => ByteArray.ofFn_replicate_zero _ _ j hj)]
  simp; rfl


/-- A store leaves everything but the bytes unchanged. -/
theorem MemoryState.store_fields {mem mem' : MemoryState} {p : Pointer} {val poison : ByteArray}
    {h : poison.size = val.size} (hs : mem.store p val poison h = .ok mem') :
    mem'.objects = mem.objects ∧ mem'.globals = mem.globals ∧ mem'.heapLimit = mem.heapLimit ∧
      mem'.depth = mem.depth := by
  obtain ⟨-, rfl⟩ := store_ok_inv hs
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `llvmStore` leaves the objects (and the symbol table, heap limit and depth)
    unchanged. -/
theorem MemoryState.llvmStore_objects {mem mem' : MemoryState} {p : Pointer} {v : RuntimeValue}
    (hs : mem.llvmStore p v = .ok mem') :
    mem'.objects = mem.objects ∧ mem'.globals = mem.globals ∧ mem'.heapLimit = mem.heapLimit ∧
      mem'.depth = mem.depth := by
  unfold llvmStore at hs
  split at hs
  · cases hs
  · split at hs <;> first
      | exact store_fields hs
      | (simp only [storeByte64] at hs; exact store_fields hs)
      | (simp only [empoison] at hs; exact store_fields hs)
      | cases hs

theorem MemoryState.checkAccess_congr {m₁ m₂ : MemoryState} {p : Pointer}
    (h : m₁.objects[p.object]? = m₂.objects[p.object]?) (n : UInt64) :
    m₁.checkAccess p n = m₂.checkAccess p n := by
  simp only [checkAccess, getObject?, h]

theorem MemoryState.load_congr {m₁ m₂ : MemoryState} {p : Pointer} {n : UInt64}
    (h : m₁.objects[p.object]? = m₂.objects[p.object]?)
    (hb : ∀ i < n.toNat, m₁.byte (p.address + i.toUInt64) = m₂.byte (p.address + i.toUInt64)) :
    m₁.load p n = m₂.load p n := by
  unfold load
  rw [checkAccess_congr h]
  congr 1
  funext _
  congr 2
  exact congrArg Array.ofFn (funext fun i => by rw [hb i.val i.isLt])

theorem MemoryState.loadPoison_congr {m₁ m₂ : MemoryState} {p : Pointer} {n : UInt64}
    (h : m₁.objects[p.object]? = m₂.objects[p.object]?)
    (hb : ∀ i < n.toNat, m₁.byte (p.address + i.toUInt64) = m₂.byte (p.address + i.toUInt64)) :
    m₁.loadPoison p n = m₂.loadPoison p n := by
  unfold loadPoison
  rw [checkAccess_congr h]
  congr 1
  funext _
  congr 2
  exact congrArg Array.ofFn (funext fun i => by rw [hb i.val i.isLt])

theorem MemoryState.hasPoison_congr {m₁ m₂ : MemoryState} {p : Pointer} {n : UInt64}
    (h : m₁.objects[p.object]? = m₂.objects[p.object]?)
    (hb : ∀ i < n.toNat, m₁.byte (p.address + i.toUInt64) = m₂.byte (p.address + i.toUInt64)) :
    m₁.hasPoison p n = m₂.hasPoison p n := by
  unfold hasPoison
  rw [loadPoison_congr h hb]

theorem MemoryState.loadByte64_congr {m₁ m₂ : MemoryState} {p : Pointer}
    (h : m₁.objects[p.object]? = m₂.objects[p.object]?)
    (hb : ∀ i < 8, m₁.byte (p.address + i.toUInt64) = m₂.byte (p.address + i.toUInt64)) :
    m₁.loadByte64 p = m₂.loadByte64 p := by
  unfold loadByte64
  rw [load_congr h (n := 8) (fun i hi => hb i (by simpa using hi)),
    loadPoison_congr h (n := 8) (fun i hi => hb i (by simpa using hi))]

theorem MemoryState.ptrOfByte_congr {m₁ m₂ : MemoryState} (h : m₁.objects = m₂.objects)
    (b : Data.LLVM.Byte 64) : m₁.ptrOfByte b = m₂.ptrOfByte b := by
  simp only [ptrOfByte, decode, objectOfAddress, h]

/-- `llvmLoad` of an integer type depends only on the objects and on the bytes that it reads. -/
theorem MemoryState.llvmLoad_congr_int {m₁ m₂ : MemoryState} {p : Pointer} {type : TypeAttr}
    {w : Nat} {sg : IntegerType.Signedness} (hty : type.val = .integerType ⟨w, sg⟩)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (h : m₁.objects[p.object]? = m₂.objects[p.object]?)
    (hb : ∀ i < w / 8, m₁.byte (p.address + i.toUInt64) = m₂.byte (p.address + i.toUInt64)) :
    m₁.llvmLoad p type = m₂.llvmLoad p type := by
  unfold llvmLoad
  by_cases hnull : p = .null
  · simp only [hnull, ite_true]
  · simp only [hnull, ite_false]
    rw [hty]
    rcases hw with rfl | rfl | rfl | rfl <;> simp only <;>
      rw [load_congr h (fun i hi => hb i (by simpa using hi)),
        hasPoison_congr h (fun i hi => hb i (by simpa using hi))]

/-- `llvmLoad` of a pointer depends only on the objects and on the 8 bytes that it reads. -/
theorem MemoryState.llvmLoad_congr_ptr {m₁ m₂ : MemoryState} {p : Pointer} {type : TypeAttr}
    {a : LLVM.PointerType} (hty : type.val = .llvmPointerType a) (h : m₁.objects = m₂.objects)
    (hb : ∀ i < 8, m₁.byte (p.address + i.toUInt64) = m₂.byte (p.address + i.toUInt64)) :
    m₁.llvmLoad p type = m₂.llvmLoad p type := by
  unfold llvmLoad
  by_cases hnull : p = .null
  · simp only [hnull, ite_true]
  · simp only [hnull, ite_false]
    rw [hty]
    simp only
    rw [loadByte64_congr (by rw [h]) hb]
    simp only [ptrOfByte_congr h]


/-- The number of bytes that `llvmStore` writes for a value. -/
@[expose]
def storeBytes : RuntimeValue → Nat
  | .int w _ => w / 8
  | .byte w _ => w / 8
  | .addr _ => 8
  | _ => 0

theorem UInt16.toByteArrayLE_size' (u : UInt16) : u.toByteArrayLE.size = 2 := by
  simp [UInt16.toByteArrayLE, ByteArray.size]
theorem UInt32.toByteArrayLE_size' (u : UInt32) : u.toByteArrayLE.size = 4 := by
  simp [UInt32.toByteArrayLE, ByteArray.size]

/-- `llvmStore` writes `storeBytes v` bytes from `p` and changes nothing else. -/
theorem MemoryState.llvmStore_writes {mem mem' : MemoryState} {p : Pointer} {v : RuntimeValue}
    (hs : mem.llvmStore p v = .ok mem') :
    ∃ val poison : ByteArray, val.size = storeBytes v ∧
      mem.checkAccess p val.size.toUInt64 = .ok () ∧
      mem' = { mem with bytes := writeBytes mem.bytes p.address val poison } := by
  unfold llvmStore at hs
  split at hs
  · cases hs
  · split at hs
    all_goals first
      | (obtain ⟨hc, rfl⟩ := store_ok_inv hs
         exact ⟨_, _, by simp [storeBytes, UInt16.toByteArrayLE_size', UInt32.toByteArrayLE_size'],
           hc, rfl⟩)
      | (simp only [storeByte64] at hs
         obtain ⟨hc, rfl⟩ := store_ok_inv hs
         exact ⟨_, _, by simp [storeBytes], hc, rfl⟩)
      | (simp only [empoison] at hs
         obtain ⟨hc, rfl⟩ := store_ok_inv hs
         exact ⟨_, _, by simp [storeBytes], hc, rfl⟩)
      | cases hs

/-- A store leaves every byte outside the `storeBytes v` bytes from `p` unchanged. -/
theorem MemoryState.byte_llvmStore_of_ne {mem mem' : MemoryState} {p : Pointer} {v : RuntimeValue}
    (hs : mem.llvmStore p v = .ok mem') {a : UInt64}
    (h : ∀ j < storeBytes v, p.address + j.toUInt64 ≠ a) : mem'.byte a = mem.byte a := by
  obtain ⟨val, poison, hsize, -, rfl⟩ := llvmStore_writes hs
  exact byte_writeBytes_of_ne mem p.address val poison (hsize ▸ h)

/-- Disjoint byte ranges: an integer load (`i8`, `i16`, `i32`, `i64`) whose bytes are
    disjoint from the bytes of a store is unchanged by the store. -/
theorem MemoryState.llvmLoad_llvmStore_disjoint_int {mem mem' : MemoryState} {p q : Pointer}
    {v : RuntimeValue} (hs : mem.llvmStore p v = .ok mem') {type : TypeAttr} {w : Nat}
    {sg : IntegerType.Signedness} (hty : type.val = .integerType ⟨w, sg⟩)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (hdisj : ∀ i < w / 8, ∀ j < storeBytes v, p.address + j.toUInt64 ≠ q.address + i.toUInt64) :
    mem'.llvmLoad q type = mem.llvmLoad q type :=
  llvmLoad_congr_int hty hw (by rw [(llvmStore_objects hs).1])
    fun i hi => byte_llvmStore_of_ne hs fun j hj => hdisj i hi j hj

/-- Disjoint byte ranges: a pointer load whose 8 bytes are disjoint from the bytes of a
    store is unchanged by the store. -/
theorem MemoryState.llvmLoad_llvmStore_disjoint_ptr {mem mem' : MemoryState} {p q : Pointer}
    {v : RuntimeValue} (hs : mem.llvmStore p v = .ok mem') {type : TypeAttr}
    {a : LLVM.PointerType} (hty : type.val = .llvmPointerType a)
    (hdisj : ∀ i < 8, ∀ j < storeBytes v, p.address + j.toUInt64 ≠ q.address + i.toUInt64) :
    mem'.llvmLoad q type = mem.llvmLoad q type :=
  llvmLoad_congr_ptr hty (llvmStore_objects hs).1
    fun i hi => byte_llvmStore_of_ne hs fun j hj => hdisj i hi j hj


/-- A successful access of a nonzero number of bytes lies inside a live object. -/
theorem MemoryState.checkAccess_ok_holds {mem : MemoryState} {p : Pointer} {n : UInt64}
    (hc : mem.checkAccess p n = .ok ()) (hn : n ≠ 0) :
    ∃ o, mem.objects[p.object]? = some o ∧ o.live = true ∧ o.holds p.address n.toNat := by
  unfold checkAccess getObject? at hc
  split at hc
  · rename_i o ho
    refine ⟨o, ho, ?_, ?_⟩
    · cases hl : o.live
      · simp [hl] at hc
      · rfl
    · by_cases hlive : o.live = false
      · simp [hlive] at hc
      · simp only [hlive, ite_false, hn] at hc
        by_cases hh : o.holds p.address n.toNat
        · exact hh
        · simp [hh] at hc
  · cases hc

theorem UInt64.add_toNat_of_lt {a : UInt64} {j : Nat} (h : a.toNat + j < 2 ^ 64) :
    (a + j.toUInt64).toNat = a.toNat + j := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega)]
  exact Nat.mod_eq_of_lt h

/-- The bytes of a store into one object and the bytes of an access of another object are
    disjoint, when the objects are disjoint and do not wrap around the address space. -/
theorem MemoryState.llvmStore_bytes_disjoint_of_objects {mem mem' : MemoryState}
    {p q : Pointer} {v : RuntimeValue} (hs : mem.llvmStore p v = .ok mem') {nq : Nat}
    {op oq : MemoryObject}
    (hop : mem.objects[p.object]? = some op) (hq : oq.holds q.address nq)
    (hdisj : op.base.toNat + op.size ≤ oq.base.toNat ∨ oq.base.toNat + oq.size ≤ op.base.toNat)
    (hwp : op.base.toNat + op.size < 2 ^ 64) (hwq : oq.base.toNat + oq.size < 2 ^ 64)
    (hv : storeBytes v < 2 ^ 64) :
    ∀ i < nq, ∀ j < storeBytes v, p.address + j.toUInt64 ≠ q.address + i.toUInt64 := by
  intro i hi j hj
  have hsz : UInt64.size = 2 ^ 64 := rfl
  obtain ⟨val, poison, hsize, hc, -⟩ := llvmStore_writes hs
  have hn : val.size.toUInt64 ≠ 0 := by
    intro h0
    have := congrArg UInt64.toNat h0
    rw [UInt64.toNat_ofNat_of_lt' (by omega)] at this
    have h0' : (0 : UInt64).toNat = 0 := rfl
    omega
  obtain ⟨o, ho, -, hho⟩ := checkAccess_ok_holds hc hn
  rw [hop] at ho; cases ho
  simp only [MemoryObject.holds, decide_eq_true_eq] at hho hq
  rw [UInt64.toNat_ofNat_of_lt' (by omega)] at hho
  intro heq
  have := congrArg UInt64.toNat heq
  rw [UInt64.add_toNat_of_lt (by omega), UInt64.add_toNat_of_lt (by omega)] at this
  omega

/-- Different objects: an integer load from an object other than the object of a store,
    when the two objects are disjoint and do not wrap around the address space, is unchanged by
    the store. -/
theorem MemoryState.llvmLoad_llvmStore_disjoint_objects_int {mem mem' : MemoryState}
    {p q : Pointer} {v : RuntimeValue} (hs : mem.llvmStore p v = .ok mem') {type : TypeAttr}
    {w : Nat} {sg : IntegerType.Signedness} (hty : type.val = .integerType ⟨w, sg⟩)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {op oq : MemoryObject}
    (hop : mem.objects[p.object]? = some op) (_hoq : mem.objects[q.object]? = some oq)
    (hq : oq.holds q.address (w / 8))
    (hdisj : op.base.toNat + op.size ≤ oq.base.toNat ∨ oq.base.toNat + oq.size ≤ op.base.toNat)
    (hwp : op.base.toNat + op.size < 2 ^ 64) (hwq : oq.base.toNat + oq.size < 2 ^ 64)
    (hv : storeBytes v < 2 ^ 64) :
    mem'.llvmLoad q type = mem.llvmLoad q type :=
  llvmLoad_llvmStore_disjoint_int hs hty hw
    (llvmStore_bytes_disjoint_of_objects hs hop hq hdisj hwp hwq hv)

/-- Different objects: a pointer load from an object other than the object of a store,
    when the two objects are disjoint and do not wrap around the address space, is unchanged by
    the store. -/
theorem MemoryState.llvmLoad_llvmStore_disjoint_objects_ptr {mem mem' : MemoryState}
    {p q : Pointer} {v : RuntimeValue} (hs : mem.llvmStore p v = .ok mem') {type : TypeAttr}
    {a : LLVM.PointerType} (hty : type.val = .llvmPointerType a) {op oq : MemoryObject}
    (hop : mem.objects[p.object]? = some op) (_hoq : mem.objects[q.object]? = some oq)
    (hq : oq.holds q.address 8)
    (hdisj : op.base.toNat + op.size ≤ oq.base.toNat ∨ oq.base.toNat + oq.size ≤ op.base.toNat)
    (hwp : op.base.toNat + op.size < 2 ^ 64) (hwq : oq.base.toNat + oq.size < 2 ^ 64)
    (hv : storeBytes v < 2 ^ 64) :
    mem'.llvmLoad q type = mem.llvmLoad q type :=
  llvmLoad_llvmStore_disjoint_ptr hs hty
    (llvmStore_bytes_disjoint_of_objects hs hop hq hdisj hwp hwq hv)

/-- An integer load from an object that exists before an allocation is unchanged by the
    allocation. -/
theorem MemoryState.llvmLoad_alloc_old {mem mem' : MemoryState} {n : UInt64}
    {frame : Option Nat} {p q : Pointer} (ha : mem.alloc n frame = .ok (mem', p))
    (hq : q.object < mem.objects.size) {type : TypeAttr} {w : Nat}
    {sg : IntegerType.Signedness} (hty : type.val = .integerType ⟨w, sg⟩)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    mem'.llvmLoad q type = mem.llvmLoad q type := by
  obtain ⟨-, -, -, hobjs, hbytes, -⟩ := alloc_spec ha
  refine llvmLoad_congr_int hty hw ?_ fun i _ => ?_
  · rw [hobjs, Array.getElem?_push_lt hq, Array.getElem?_eq_getElem hq]
  · simp only [byte, hbytes]

/-- A load of the 8 bytes of a pointer from an object that exists before an allocation reads the
    same bytes (the pointer it decodes may name the new object). -/
theorem MemoryState.loadByte64_alloc_old {mem mem' : MemoryState} {n : UInt64}
    {frame : Option Nat} {p q : Pointer} (ha : mem.alloc n frame = .ok (mem', p))
    (hq : q.object < mem.objects.size) :
    mem'.loadByte64 q = mem.loadByte64 q := by
  obtain ⟨-, -, -, hobjs, hbytes, -⟩ := alloc_spec ha
  refine loadByte64_congr ?_ fun i _ => ?_
  · rw [hobjs, Array.getElem?_push_lt hq, Array.getElem?_eq_getElem hq]
  · simp only [byte, hbytes]


theorem ByteArray.toBitVecLE_two (b0 b1 : UInt8) : (ByteArray.mk #[b0, b1]).toBitVecLE 16 =
    ((b1.toBitVec.setWidth 16) <<< 8) ||| b0.toBitVec.setWidth 16 := by
  have hs : ({ data := #[b0, b1] } : ByteArray).size = 2 := rfl
  simp only [ByteArray.toBitVecLE, ByteSlice.foldr, ByteSlice.foldrM, Id.run]
  rw [ByteSlice.foldrM.loop]
  simp [ByteArray.toByteSlice, ByteSlice.size, hs, ByteSlice.start, ByteSlice.stop]
  rw [ByteSlice.foldrM.loop]
  simp [ByteSlice.size, ByteSlice.start, ByteSlice.stop]
  rw [ByteSlice.foldrM.loop]
  simp [ByteSlice.size, ByteSlice.start, ByteSlice.stop, GetElem.getElem, ByteSlice.get,
    ByteSlice.byteArray]
  rfl

theorem ByteArray.toBitVecLE_four (b0 b1 b2 b3 : UInt8) :
    (ByteArray.mk #[b0, b1, b2, b3]).toBitVecLE 32 =
    ((((b3.toBitVec.setWidth 32 <<< 8) ||| b2.toBitVec.setWidth 32) <<< 8 |||
      b1.toBitVec.setWidth 32) <<< 8) ||| b0.toBitVec.setWidth 32 := by
  have hs : ({ data := #[b0, b1, b2, b3] } : ByteArray).size = 4 := rfl
  simp only [ByteArray.toBitVecLE, ByteSlice.foldr, ByteSlice.foldrM, Id.run]
  rw [ByteSlice.foldrM.loop]
  simp [ByteArray.toByteSlice, ByteSlice.size, hs, ByteSlice.start, ByteSlice.stop]
  rw [ByteSlice.foldrM.loop]
  simp [ByteSlice.size, ByteSlice.start, ByteSlice.stop]
  rw [ByteSlice.foldrM.loop]
  simp [ByteSlice.size, ByteSlice.start, ByteSlice.stop]
  rw [ByteSlice.foldrM.loop]
  simp [ByteSlice.size, ByteSlice.start, ByteSlice.stop]
  rw [ByteSlice.foldrM.loop]
  simp [ByteSlice.size, ByteSlice.start, ByteSlice.stop, GetElem.getElem, ByteSlice.get,
    ByteSlice.byteArray]
  rfl

theorem BitVec.roundtrip16 (v : BitVec 16) :
    (((UInt16.ofBitVec v >>> 8).toUInt8.toBitVec.setWidth 16) <<< 8) |||
      (UInt16.ofBitVec v).toUInt8.toBitVec.setWidth 16 = v := by
  ext i hi
  simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
  by_cases h : i < 8
  · simp [h, BitVec.getLsbD_eq_getElem hi]
  · have h1 : i - 8 < 8 := by omega
    have h2 : 8 + (i - 8) = i := by omega
    simp [h, h1, h2, BitVec.getLsbD_eq_getElem hi]


theorem BitVec.roundtrip32 (v : BitVec 32) :
    (((((UInt32.ofBitVec v >>> 0x18).toUInt8.toBitVec.setWidth 32 <<< 8) |||
      (UInt32.ofBitVec v >>> 0x10).toUInt8.toBitVec.setWidth 32) <<< 8 |||
      (UInt32.ofBitVec v >>> 0x08).toUInt8.toBitVec.setWidth 32) <<< 8) |||
      (UInt32.ofBitVec v).toUInt8.toBitVec.setWidth 32 = v := by
  ext i hi
  simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
  by_cases h : i < 8
  · simp [h, BitVec.getLsbD_eq_getElem hi]
  by_cases h' : i < 16
  · have h1 : i - 8 < 8 := by omega
    have h2 : 8 + (i - 8) = i := by omega
    simp [h, h', h1, h2, BitVec.getLsbD_eq_getElem hi]
  by_cases h'' : i < 24
  · have h1 : i - 8 - 8 < 8 := by omega
    have h2 : 16 + (i - 8 - 8) = i := by omega
    have h3 : ¬ i - 8 < 8 := by omega
    simp [h, h', h'', h1, h2, h3, BitVec.getLsbD_eq_getElem hi]
  · have h1 : i - 8 - 8 - 8 < 8 := by omega
    have h2 : 24 + (i - 8 - 8 - 8) = i := by omega
    have h3 : ¬ i - 8 < 8 := by omega
    have h4 : ¬ i - 8 - 8 < 8 := by omega
    simp [h, h', h'', h1, h2, h3, h4, BitVec.getLsbD_eq_getElem hi]

/-- An `i16` load after an `i16` store at the same pointer returns the stored value. -/
theorem MemoryState.llvmLoad_llvmStore_same_i16 {mem mem' : MemoryState} {p : Pointer}
    {v : BitVec 16} (hst : mem.llvmStore p (.int 16 (.val v)) = .ok mem') {ty : TypeAttr}
    {sg : IntegerType.Signedness} (hty : ty.val = .integerType ⟨16, sg⟩) :
    mem'.llvmLoad p ty = .ok (.int 16 (.val v)) := by
  unfold llvmStore at hst
  by_cases hnull : p = .null
  · simp [hnull] at hst
  simp only [hnull, ite_false] at hst
  obtain ⟨hc, rfl⟩ := store_ok_inv hst
  have hc' : mem.checkAccess p 2 = .ok () := by simpa [UInt16.toByteArrayLE_size'] using hc
  unfold llvmLoad
  simp only [hnull, ite_false]
  rw [hty]
  simp only
  rw [load_writeBytes hc' (by simp [UInt16.toByteArrayLE_size']),
    hasPoison_of_zero (loadPoison_writeBytes hc' (by simp [UInt16.toByteArrayLE_size']))
    (fun j hj => ByteArray.ofFn_replicate_zero _ _ j hj)]
  simp only [Interp.bind_ok, Bool.false_eq_true, ite_false, Interp.pure_eq, Interp.ok.injEq,
    RuntimeValue.int.injEq, heq_eq_eq, true_and]
  have e : (⟨Array.ofFn fun i : Fin (2 : UInt64).toNat =>
      (UInt16.ofBitVec v).toByteArrayLE[i.val]!⟩ : ByteArray) =
      ⟨#[(UInt16.ofBitVec v).toUInt8, ((UInt16.ofBitVec v) >>> 8).toUInt8]⟩ := by
    congr 1
  rw [e, ByteArray.toBitVecLE_two]
  congr 1
  exact BitVec.roundtrip16 v


theorem UInt64.toUInt64LE_toByteArrayLE (u : UInt64) : u.toByteArrayLE.toUInt64LE! = u := by
  unfold ByteArray.toUInt64LE!
  simp [UInt64.toByteArrayLE, ByteArray.size, ByteArray.get!, -UInt64.toUInt64_toUInt8]
  apply UInt64.toBitVec_inj.mp
  ext i hi
  simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, -UInt64.toUInt64_toUInt8]
  rcases (by omega : (i / 8 = 0) ∨ (i / 8 = 1) ∨ (i / 8 = 2) ∨ (i / 8 = 3) ∨ (i / 8 = 4) ∨ (i / 8 = 5) ∨ (i / 8 = 6) ∨ (i / 8 = 7)) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · simp [(show i < 8 by omega), (show i < 16 by omega), (show i < 24 by omega), (show i < 32 by omega), (show i < 40 by omega), (show i < 48 by omega), (show i < 56 by omega), BitVec.getLsbD_eq_getElem hi]
  · simp [(show ¬ i < 8 by omega), (show i - 8 < 8 by omega), (show 8 + (i - 8) = i by omega), (show i < 16 by omega), (show i < 24 by omega), (show i < 32 by omega), (show i < 40 by omega), (show i < 48 by omega), (show i < 56 by omega), BitVec.getLsbD_eq_getElem hi]
  · simp [(show ¬ i < 8 by omega), (show ¬ i - 8 < 8 by omega), (show ¬ i < 16 by omega), (show i - 16 < 8 by omega), (show 16 + (i - 16) = i by omega), (show i < 24 by omega), (show i < 32 by omega), (show i < 40 by omega), (show i < 48 by omega), (show i < 56 by omega), BitVec.getLsbD_eq_getElem hi]
  · simp [(show ¬ i < 8 by omega), (show ¬ i - 8 < 8 by omega), (show ¬ i < 16 by omega), (show ¬ i - 16 < 8 by omega), (show ¬ i < 24 by omega), (show i - 24 < 8 by omega), (show 24 + (i - 24) = i by omega), (show i < 32 by omega), (show i < 40 by omega), (show i < 48 by omega), (show i < 56 by omega), BitVec.getLsbD_eq_getElem hi]
  · simp [(show ¬ i < 8 by omega), (show ¬ i - 8 < 8 by omega), (show ¬ i < 16 by omega), (show ¬ i - 16 < 8 by omega), (show ¬ i < 24 by omega), (show ¬ i - 24 < 8 by omega), (show ¬ i < 32 by omega), (show i - 32 < 8 by omega), (show 32 + (i - 32) = i by omega), (show i < 40 by omega), (show i < 48 by omega), (show i < 56 by omega), BitVec.getLsbD_eq_getElem hi]
  · simp [(show ¬ i < 8 by omega), (show ¬ i - 8 < 8 by omega), (show ¬ i < 16 by omega), (show ¬ i - 16 < 8 by omega), (show ¬ i < 24 by omega), (show ¬ i - 24 < 8 by omega), (show ¬ i < 32 by omega), (show ¬ i - 32 < 8 by omega), (show ¬ i < 40 by omega), (show i - 40 < 8 by omega), (show 40 + (i - 40) = i by omega), (show i < 48 by omega), (show i < 56 by omega), BitVec.getLsbD_eq_getElem hi]
  · simp [(show ¬ i < 8 by omega), (show ¬ i - 8 < 8 by omega), (show ¬ i < 16 by omega), (show ¬ i - 16 < 8 by omega), (show ¬ i < 24 by omega), (show ¬ i - 24 < 8 by omega), (show ¬ i < 32 by omega), (show ¬ i - 32 < 8 by omega), (show ¬ i < 40 by omega), (show ¬ i - 40 < 8 by omega), (show ¬ i < 48 by omega), (show i - 48 < 8 by omega), (show 48 + (i - 48) = i by omega), (show i < 56 by omega), BitVec.getLsbD_eq_getElem hi]
  · simp [(show ¬ i < 8 by omega), (show ¬ i - 8 < 8 by omega), (show ¬ i < 16 by omega), (show ¬ i - 16 < 8 by omega), (show ¬ i < 24 by omega), (show ¬ i - 24 < 8 by omega), (show ¬ i < 32 by omega), (show ¬ i - 32 < 8 by omega), (show ¬ i < 40 by omega), (show ¬ i - 40 < 8 by omega), (show ¬ i < 48 by omega), (show ¬ i - 48 < 8 by omega), (show ¬ i < 56 by omega), (show i - 56 < 8 by omega), (show 56 + (i - 56) = i by omega), BitVec.getLsbD_eq_getElem hi]

theorem ByteArray.mk_ofFn_getElem! (b : ByteArray) (n : Nat) (hn : b.size = n) :
    (⟨Array.ofFn fun i : Fin n => b[i.val]!⟩ : ByteArray) = b := by
  cases b with
  | mk data =>
    congr 1
    apply Array.ext
    · simp only [Array.size_ofFn]; exact hn.symm
    · intro i h1 h2
      simp only [Array.getElem_ofFn]
      rw [getElem!_pos (ByteArray.mk data) i h2]
      rfl

/-- An `i32` load after an `i32` store at the same pointer returns the stored value. -/
theorem MemoryState.llvmLoad_llvmStore_same_i32 {mem mem' : MemoryState} {p : Pointer}
    {v : BitVec 32} (hst : mem.llvmStore p (.int 32 (.val v)) = .ok mem') {ty : TypeAttr}
    {sg : IntegerType.Signedness} (hty : ty.val = .integerType ⟨32, sg⟩) :
    mem'.llvmLoad p ty = .ok (.int 32 (.val v)) := by
  unfold llvmStore at hst
  by_cases hnull : p = .null
  · simp [hnull] at hst
  simp only [hnull, ite_false] at hst
  obtain ⟨hc, rfl⟩ := store_ok_inv hst
  have hc' : mem.checkAccess p 4 = .ok () := by simpa [UInt32.toByteArrayLE_size'] using hc
  unfold llvmLoad
  simp only [hnull, ite_false]
  rw [hty]
  simp only
  rw [load_writeBytes hc' (by simp [UInt32.toByteArrayLE_size']),
    hasPoison_of_zero (loadPoison_writeBytes hc' (by simp [UInt32.toByteArrayLE_size']))
    (fun j hj => ByteArray.ofFn_replicate_zero _ _ j hj)]
  simp only [Interp.bind_ok, Bool.false_eq_true, ite_false, Interp.pure_eq, Interp.ok.injEq,
    RuntimeValue.int.injEq, heq_eq_eq, true_and]
  have e : (⟨Array.ofFn fun i : Fin (4 : UInt64).toNat =>
      (UInt32.ofBitVec v).toByteArrayLE[i.val]!⟩ : ByteArray) =
      ⟨#[(UInt32.ofBitVec v).toUInt8, ((UInt32.ofBitVec v) >>> 0x08).toUInt8,
        ((UInt32.ofBitVec v) >>> 0x10).toUInt8, ((UInt32.ofBitVec v) >>> 0x18).toUInt8]⟩ := by
    congr 1
  rw [e, ByteArray.toBitVecLE_four]
  congr 1
  exact BitVec.roundtrip32 v

/-- An `i64` load after an `i64` store at the same pointer returns the stored value. -/
theorem MemoryState.llvmLoad_llvmStore_same_i64 {mem mem' : MemoryState} {p : Pointer}
    {v : BitVec 64} (hst : mem.llvmStore p (.int 64 (.val v)) = .ok mem') {ty : TypeAttr}
    {sg : IntegerType.Signedness} (hty : ty.val = .integerType ⟨64, sg⟩) :
    mem'.llvmLoad p ty = .ok (.int 64 (.val v)) := by
  unfold llvmStore at hst
  by_cases hnull : p = .null
  · simp [hnull] at hst
  simp only [hnull, ite_false] at hst
  obtain ⟨hc, rfl⟩ := store_ok_inv hst
  have hc' : mem.checkAccess p 8 = .ok () := by simpa using hc
  unfold llvmLoad
  simp only [hnull, ite_false]
  rw [hty]
  simp only
  rw [load_writeBytes hc' (by simp),
    hasPoison_of_zero (loadPoison_writeBytes hc' (by simp))
    (fun j hj => ByteArray.ofFn_replicate_zero _ _ j hj)]
  simp only [Interp.bind_ok, Bool.false_eq_true, ite_false, Interp.pure_eq, Interp.ok.injEq,
    RuntimeValue.int.injEq, heq_eq_eq, true_and]
  rw [ByteArray.mk_ofFn_getElem! _ _ (by simp), UInt64.toUInt64LE_toByteArrayLE]
  congr 1
  simp


/-- A 64-bit load after a 64-bit store at the same pointer returns the stored bits, poison bits
    included. -/
theorem MemoryState.loadByte64_storeByte64 {mem mem' : MemoryState} {p : Pointer}
    {b : Data.LLVM.Byte 64} (hst : mem.storeByte64 p b = .ok mem') :
    mem'.loadByte64 p = .ok b := by
  unfold storeByte64 at hst
  obtain ⟨hc, rfl⟩ := store_ok_inv hst
  have hc' : mem.checkAccess p 8 = .ok () := by simpa using hc
  unfold loadByte64
  rw [load_writeBytes hc' (by simp), loadPoison_writeBytes hc' (by simp)]
  simp only [Interp.bind_ok, Interp.pure_eq]
  rw [ByteArray.mk_ofFn_getElem! _ _ (by simp), ByteArray.mk_ofFn_getElem! _ _ (by simp)]
  simp only [UInt64.toUInt64LE_toByteArrayLE]
  cases b with
  | mk val poison h =>
    simp only [Interp.ok.injEq, Data.LLVM.Byte.mk.injEq, and_true]
    have : val &&& ~~~poison = (val &&& ~~~poison) ||| (val &&& poison) := by rw [h]; simp
    rw [this, ← BitVec.and_or_distrib_left]
    have h2 : (~~~poison ||| poison) = BitVec.allOnes 64 := by
      rw [BitVec.or_comm]; exact BitVec.or_not_self poison
    rw [h2, BitVec.and_allOnes]

/-- A `ptr` load after a `ptr` store at the same pointer returns the stored pointer as
    the memory decodes it: the same address, and the object that the address lies in. -/
theorem MemoryState.llvmLoad_llvmStore_same_ptr {mem mem' : MemoryState} {p : Pointer}
    {q : Data.LLVM.Ptr} (hst : mem.llvmStore p (.addr q) = .ok mem') {ty : TypeAttr}
    {a : LLVM.PointerType} (hty : ty.val = .llvmPointerType a) :
    mem'.llvmLoad p ty = .ok (.addr (mem'.ptrOfByte q.toByte)) := by
  unfold llvmStore at hst
  by_cases hnull : p = .null
  · simp [hnull] at hst
  simp only [hnull, ite_false] at hst
  unfold llvmLoad
  simp only [hnull, ite_false]
  rw [hty]
  simp only
  rw [loadByte64_storeByte64 hst]
  rfl

theorem MemoryState.ptrOfByte_toByte_val (mem : MemoryState) (r : Pointer) :
    mem.ptrOfByte (Data.LLVM.Ptr.val r).toByte = .val (mem.decode r.address) := by
  simp [ptrOfByte, Data.LLVM.Ptr.toByte, Data.LLVM.Byte.toUInt64]

theorem MemoryState.ptrOfByte_toByte_poison (mem : MemoryState) :
    mem.ptrOfByte (Data.LLVM.Ptr.poison).toByte = .poison := by
  simp [ptrOfByte, Data.LLVM.Ptr.toByte, Data.LLVM.Byte.allPoison]

end Veir
