import DatomBau.Transactor

/-!
# The four covering indexes (Phase 3)

`IndexedDb` pairs a spec database with the four Datomic sort orders as
`Std.TreeSet`s of `Entry` (current fact + asserting transaction):

- EAVT — everything about an entity, grouped;
- AEVT — one attribute across all entities;
- AVET — value lookup;
- VAET — reverse references (ref values only).

Coherence (`IndexedDb.WF`) says index membership *is* the spec: an entry
is in an index iff the log's last write of its fact was an assertion in
exactly that transaction. `ofDb` rebuilds indexes from the spec and is
coherent unconditionally (`ofDb_wf`); incremental maintenance is a future
optimization behind the same WF contract.

Lookups (`datoms*`, Datomic's `d/datoms`) are stated and proven against
filter semantics, so later slice-based optimizations change no theorem
statements.
-/

namespace DatomBau

def Value.isRef : Value → Bool
  | .ref _ => true | _ => false

theorem Value.isRef_iff {v : Value} : v.isRef = true ↔ ∃ r, v = .ref r := by
  cases v <;> simp [Value.isRef]

/-! ## Current entries: the spec-level index content -/

/-- The index entry for a fact, if it is current: the fact stamped with
its asserting transaction. -/
def Db.entryOf (db : Db) (f : Fact) : Option Entry :=
  match db.lastWrite f with
  | some (tx, true) => some ⟨f, tx⟩
  | _ => none

/-- What every index must contain: each current fact, stamped with the
transaction that asserted it. -/
def Db.currentEntries (db : Db) : List Entry :=
  db.currentFacts.filterMap db.entryOf

theorem Db.mem_currentFacts_iff {db : Db} {f : Fact} :
    f ∈ db.currentFacts ↔ f ∈ db := by
  constructor
  · intro h
    have := (List.mem_filter.mp h).2
    simpa [Db.mem_def] using this
  · exact Db.mem_currentFacts_of_mem

theorem Db.mem_currentEntries {db : Db} {x : Entry} :
    x ∈ db.currentEntries ↔ db.lastWrite x.toFact = some (x.tx, true) := by
  unfold Db.currentEntries
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨f, hf, hef⟩
    unfold Db.entryOf at hef
    split at hef
    next tx htx =>
      cases hef
      simpa using htx
    next => simp at hef
  · intro hlw
    refine ⟨x.toFact, ?_, ?_⟩
    · rw [Db.mem_currentFacts_iff, Db.mem_iff_lastWrite]
      exact ⟨x.tx, hlw⟩
    · unfold Db.entryOf
      rw [hlw]

/-! ## The indexed database -/

structure IndexedDb where
  db   : Db
  eavt : Std.TreeSet Entry Entry.cmpEAVT
  aevt : Std.TreeSet Entry Entry.cmpAEVT
  avet : Std.TreeSet Entry Entry.cmpAVET
  vaet : Std.TreeSet Entry Entry.cmpVAET

/-- Coherence: index membership is exactly the spec's current view. -/
structure IndexedDb.WF (idb : IndexedDb) : Prop where
  eavt_coh : ∀ x : Entry,
    x ∈ idb.eavt ↔ idb.db.lastWrite x.toFact = some (x.tx, true)
  aevt_coh : ∀ x : Entry,
    x ∈ idb.aevt ↔ idb.db.lastWrite x.toFact = some (x.tx, true)
  avet_coh : ∀ x : Entry,
    x ∈ idb.avet ↔ idb.db.lastWrite x.toFact = some (x.tx, true)
  vaet_coh : ∀ x : Entry,
    x ∈ idb.vaet ↔
      x.v.isRef = true ∧ idb.db.lastWrite x.toFact = some (x.tx, true)

/-- Build the indexes from the spec. -/
def IndexedDb.ofDb (db : Db) : IndexedDb :=
  { db
    eavt := .ofList db.currentEntries Entry.cmpEAVT
    aevt := .ofList db.currentEntries Entry.cmpAEVT
    avet := .ofList db.currentEntries Entry.cmpAVET
    vaet := .ofList (db.currentEntries.filter fun x => x.v.isRef)
      Entry.cmpVAET }

/-- **Coherence** — unconditionally: a rebuilt index is the spec. -/
theorem IndexedDb.ofDb_wf (db : Db) : (IndexedDb.ofDb db).WF := by
  constructor <;> intro x <;>
    simp only [IndexedDb.ofDb, Std.TreeSet.mem_ofList] <;>
    rw [List.contains_iff_mem]
  case eavt_coh => exact Db.mem_currentEntries
  case aevt_coh => exact Db.mem_currentEntries
  case avet_coh => exact Db.mem_currentEntries
  case vaet_coh =>
    rw [List.mem_filter, Db.mem_currentEntries]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩

/-- Transact against an indexed database: transact on the spec, rebuild.
Rebuilding keeps coherence by construction; incremental maintenance can
replace this later behind the same `WF` contract. -/
def IndexedDb.transactData (idb : IndexedDb) (forms : List TxForm)
    (now : Nat) : Except TxError (IndexedDb × TxReport) :=
  (idb.db.transactData forms now).map fun r => (IndexedDb.ofDb r.db, r)

theorem IndexedDb.transactData_wf {idb : IndexedDb} {forms : List TxForm}
    {now : Nat} {idb' : IndexedDb} {r : TxReport}
    (h : idb.transactData forms now = .ok (idb', r)) : idb'.WF := by
  unfold IndexedDb.transactData at h
  cases hd : idb.db.transactData forms now with
  | error e => rw [hd] at h; exact absurd h (by simp [Except.map])
  | ok r' =>
    rw [hd] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact IndexedDb.ofDb_wf r'.db

/-! ## The `datoms` API (Datomic's `d/datoms`)

Stated and proven against filter semantics; sortedness comes from the
underlying tree order. -/

/-- Everything about entity `e`, in EAVT order. -/
def IndexedDb.datomsE (idb : IndexedDb) (e : Nat) : List Entry :=
  idb.eavt.toList.filter fun x => x.e == e

/-- The values of `(e, a)`, in EAVT order. -/
def IndexedDb.datomsEA (idb : IndexedDb) (e : Nat) (a : Keyword) : List Entry :=
  idb.eavt.toList.filter fun x => x.e == e && x.a == a

/-- One attribute across all entities, in AEVT order. -/
def IndexedDb.datomsA (idb : IndexedDb) (a : Keyword) : List Entry :=
  idb.aevt.toList.filter fun x => x.a == a

/-- Who has value `v` for attribute `a`, in AVET order. -/
def IndexedDb.datomsAV (idb : IndexedDb) (a : Keyword) (v : Value) : List Entry :=
  idb.avet.toList.filter fun x => x.a == a && x.v == v

/-- All current references to entity `e`, in VAET order. -/
def IndexedDb.refsTo (idb : IndexedDb) (e : Nat) : List Entry :=
  idb.vaet.toList.filter fun x => x.v == Value.ref e

/-! ### Lookup correctness -/

theorem IndexedDb.mem_datomsE {idb : IndexedDb} (h : idb.WF) {e : Nat}
    {x : Entry} :
    x ∈ idb.datomsE e ↔
      x.e = e ∧ idb.db.lastWrite x.toFact = some (x.tx, true) := by
  unfold IndexedDb.datomsE
  rw [List.mem_filter, Std.TreeSet.mem_toList, h.eavt_coh]
  simp [and_comm]

theorem IndexedDb.mem_datomsEA {idb : IndexedDb} (h : idb.WF) {e : Nat}
    {a : Keyword} {x : Entry} :
    x ∈ idb.datomsEA e a ↔
      x.e = e ∧ x.a = a ∧
        idb.db.lastWrite x.toFact = some (x.tx, true) := by
  unfold IndexedDb.datomsEA
  rw [List.mem_filter, Std.TreeSet.mem_toList, h.eavt_coh]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · exact fun ⟨hlw, he, ha⟩ => ⟨he, ha, hlw⟩
  · exact fun ⟨he, ha, hlw⟩ => ⟨hlw, he, ha⟩

theorem IndexedDb.mem_datomsA {idb : IndexedDb} (h : idb.WF) {a : Keyword}
    {x : Entry} :
    x ∈ idb.datomsA a ↔
      x.a = a ∧ idb.db.lastWrite x.toFact = some (x.tx, true) := by
  unfold IndexedDb.datomsA
  rw [List.mem_filter, Std.TreeSet.mem_toList, h.aevt_coh]
  simp [and_comm]

theorem IndexedDb.mem_datomsAV {idb : IndexedDb} (h : idb.WF) {a : Keyword}
    {v : Value} {x : Entry} :
    x ∈ idb.datomsAV a v ↔
      x.a = a ∧ x.v = v ∧
        idb.db.lastWrite x.toFact = some (x.tx, true) := by
  unfold IndexedDb.datomsAV
  rw [List.mem_filter, Std.TreeSet.mem_toList, h.avet_coh]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · exact fun ⟨hlw, ha, hv⟩ => ⟨ha, hv, hlw⟩
  · exact fun ⟨ha, hv, hlw⟩ => ⟨hlw, ha, hv⟩

theorem IndexedDb.mem_refsTo {idb : IndexedDb} (h : idb.WF) {e : Nat}
    {x : Entry} :
    x ∈ idb.refsTo e ↔
      x.v = .ref e ∧ idb.db.lastWrite x.toFact = some (x.tx, true) := by
  unfold IndexedDb.refsTo
  rw [List.mem_filter, Std.TreeSet.mem_toList, h.vaet_coh]
  constructor
  · rintro ⟨⟨-, hlw⟩, hv⟩
    exact ⟨by simpa using hv, hlw⟩
  · rintro ⟨hv, hlw⟩
    exact ⟨⟨by simp [hv, Value.isRef], hlw⟩, by simpa using hv⟩

/-! ### Sortedness: lookups come out in index order -/

theorem IndexedDb.datomsEA_sorted (idb : IndexedDb) (e : Nat) (a : Keyword) :
    (idb.datomsEA e a).Pairwise fun p q => Entry.cmpEAVT p q = .lt :=
  List.Pairwise.filter _ Std.TreeSet.ordered_toList

theorem IndexedDb.datomsAV_sorted (idb : IndexedDb) (a : Keyword) (v : Value) :
    (idb.datomsAV a v).Pairwise fun p q => Entry.cmpAVET p q = .lt :=
  List.Pairwise.filter _ Std.TreeSet.ordered_toList

/-! ## Executable sanity checks -/

private def kname : Keyword := ⟨some "person", "name"⟩
private def kfriend : Keyword := ⟨some "person", "friend"⟩

private def iSchema : Schema := .ofList
  [(kname, { valueType := .str }),
   (kfriend, { valueType := .ref, cardinality := .many })]

private def idb0 : IndexedDb := .ofDb (Db.empty iSchema)

private def idb1 : IndexedDb :=
  ((idb0.transactData
    [.add (.tmp "a") kname (.val (.str "Ada")),
     .add (.tmp "g") kname (.val (.str "Grace")),
     .add (.tmp "g") kfriend (.tmp "a")] 100).toOption.map (·.1)).getD idb0

#guard idb1.eavt.size == 4          -- 3 facts + txInstant
#guard idb1.vaet.size == 1          -- only the ref
#guard (idb1.datomsEA 1 kname).map (·.v) == [.str "Ada"]
#guard (idb1.datomsA kname).map (·.e) == [1, 2]
#guard (idb1.datomsAV kname (.str "Grace")).map (·.e) == [2]
#guard (idb1.refsTo 1).map (·.e) == [2]
#guard (idb1.datomsE 3).map (·.a) == [Keyword.txInstant]
#guard (idb1.datomsEA 1 kname).all (·.tx == 3)

end DatomBau
