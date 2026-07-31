import DatomBau.Core
import DatomBau.Schema

/-!
# The semantic model: the log is truth

A database value is an append-only log of transactions plus a fixed schema.
Everything else — current facts, time-travel views, indexes (Phase 3),
query results (Phase 4) — is defined as, or proven equal to, a projection
of the log.

The current-facts "collection" is deliberately a *function*:
`Db.lastWrite f` returns the transaction id and added-flag of the last log
entry about fact `f`. A fact is in the database iff its last write was an
assertion. This makes the membership characterization definitional and
assert-idempotency free, and it is executable (a slow scan — the indexes
are the fast path, proven coherent in Phase 3).

Flagship theorems (Phase 1): `asOf_append` — appending a fresh transaction
does not change any `asOf` view, as on-the-nose value equality — and
`asOf_maxTx` — the view at the current basis is the database itself.
-/

namespace DatomBau

/-- One transaction: its entity id (transactions are entities, allocated
from the same fresh-id stream), a wall-clock instant in milliseconds, and
the datoms it asserted/retracted. -/
structure Transaction where
  id      : Nat
  instant : Nat
  datoms  : List TxDatom
  deriving DecidableEq, Repr

/-- The log, oldest first. -/
abbrev Log := List Transaction

/-- A database value. `maxTx` and fresh ids are *derived* from the log —
caching them would break the value-equality form of the asOf theorems. -/
structure Db where
  log    : Log
  schema : Schema

/-- The empty database over a schema. -/
def Db.empty (s : Schema) : Db := ⟨[], s⟩

/-- Every datom ever, oldest first, stamped with its transaction id —
Datomic's `history` view, and the ground truth everything projects from. -/
def Db.datoms (db : Db) : List Datom :=
  db.log.flatMap fun t => t.datoms.map fun d => ⟨d.toFact, t.id, d.added⟩

/-- The last write about fact `f`: the transaction id and added-flag of the
latest log datom with `f`'s entity, attribute, and value. -/
def Db.lastWrite (db : Db) (f : Fact) : Option (Nat × Bool) :=
  (db.datoms.reverse.find? (·.toFact == f)).map fun d => (d.tx, d.added)

/-- A fact is current iff its last write was an assertion. -/
def Db.contains (db : Db) (f : Fact) : Bool :=
  match db.lastWrite f with
  | some (_, true) => true
  | _              => false

instance : Membership Fact Db := ⟨fun db f => db.contains f = true⟩

theorem Db.mem_iff_lastWrite {db : Db} {f : Fact} :
    f ∈ db ↔ ∃ tx, db.lastWrite f = some (tx, true) := by
  show db.contains f = true ↔ _
  unfold Db.contains
  cases h : db.lastWrite f with
  | none => simp
  | some p =>
    obtain ⟨tx, added⟩ := p
    cases added <;> simp

/-- The basis: the highest transaction id in the log (0 for the empty log). -/
def Db.maxTx (db : Db) : Nat :=
  db.log.foldl (fun m t => max m t.id) 0

/-- The next fresh id. Under `Db.WF` every id in the log — transaction ids,
entity positions, ref values — is bounded by `maxTx`, so this is fresh. -/
def Db.nextId (db : Db) : Nat := db.maxTx + 1

/-- Append a transaction. The raw operation the transactor (Phase 2) builds
on; it does no validation. -/
def Db.append (db : Db) (t : Transaction) : Db :=
  { db with log := db.log ++ [t] }

/-! ## Time-travel views -/

/-- The database as of transaction `t`: only log entries with id ≤ t.
Defined by `filter`, not `takeWhile`, so it is correct without any
sortedness hypothesis. -/
def Db.asOf (db : Db) (t : Nat) : Db :=
  { db with log := db.log.filter (fun tr => tr.id ≤ t) }

/-- Only what happened after `t`. -/
def Db.since (db : Db) (t : Nat) : Db :=
  { db with log := db.log.filter (fun tr => t < tr.id) }

/-! ## Well-formedness

Structural invariants the transactor maintains. Stated per-log-datom (not
per-current-fact) so they are monotone under append. -/

/-- All entity ids a datom mentions: its entity position and, for `ref`
values, the referenced entity. -/
def TxDatom.entityIds (d : TxDatom) : List Nat :=
  d.e :: (match d.v with | .ref r => [r] | _ => [])

structure Db.WF (db : Db) : Prop where
  /-- Transaction ids strictly increase along the log. -/
  txIds_strictMono : db.log.Pairwise (fun s t => s.id < t.id)
  /-- Wall-clock instants never decrease along the log. -/
  instants_mono : db.log.Pairwise (fun s t => s.instant ≤ t.instant)
  /-- Every id a transaction mentions is bounded by its own id: entities
  are allocated before (or as) the transaction that first mentions them.
  Covers ref values, not just entity positions. -/
  ids_bounded : ∀ t ∈ db.log, ∀ d ∈ t.datoms, ∀ i ∈ d.entityIds, i ≤ t.id
  /-- Every datom ever appended typechecks against the schema. -/
  wellTyped : ∀ t ∈ db.log, ∀ d ∈ t.datoms, db.schema.typechecks d = true
  /-- Every transaction carries its own `:db/txInstant` datom (transactions
  are entities). -/
  txInstant_present : ∀ t ∈ db.log,
    (⟨⟨t.id, .txInstant, .instant t.instant⟩, true⟩ : TxDatom) ∈ t.datoms

theorem Db.WF.empty (s : Schema) : (Db.empty s).WF := by
  constructor <;> simp [Db.empty]

/-! ## Flagship theorems -/

private theorem le_foldl_max {l : List Nat} {init : Nat} :
    (∀ x ∈ l, x ≤ l.foldl max init) ∧ init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons y ys ih =>
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases hx with _ | hx
      · exact Nat.le_trans (Nat.le_max_right init y) (ih (init := max init y)).2
      · exact (ih (init := max init y)).1 x ‹x ∈ ys›
    · exact Nat.le_trans (Nat.le_max_left init y) (ih (init := max init y)).2

/-- Every transaction id in the log is bounded by the basis. -/
theorem Db.le_maxTx {db : Db} {t : Transaction} (h : t ∈ db.log) :
    t.id ≤ db.maxTx := by
  have := (le_foldl_max (l := db.log.map (·.id)) (init := 0)).1 t.id
    (List.mem_map_of_mem h)
  simpa [Db.maxTx, List.foldl_map] using this

/-- **asOf views are frozen**: appending a transaction with a fresh id does
not change the database as of any earlier basis — as value equality, not
mere observational equivalence. No well-formedness needed: freshness of the
new id is enough. -/
theorem Db.asOf_append {db : Db} {t : Transaction} {tx : Nat}
    (hfresh : db.maxTx < t.id) (htx : tx ≤ db.maxTx) :
    (db.append t).asOf tx = db.asOf tx := by
  have hnot : ¬ (t.id ≤ tx) := by omega
  simp [Db.append, Db.asOf, List.filter_append, hnot]

/-- The view at the current basis is the database itself. -/
theorem Db.asOf_maxTx (db : Db) : db.asOf db.maxTx = db := by
  have h : db.log.filter (fun tr => decide (tr.id ≤ db.maxTx)) = db.log :=
    List.filter_eq_self.mpr fun t ht => by simpa using Db.le_maxTx ht
  simp [Db.asOf, h]

/-- `since` at the basis is empty. -/
theorem Db.since_maxTx (db : Db) : (db.since db.maxTx).log = [] := by
  simp only [Db.since]
  rw [List.filter_eq_nil_iff]
  intro t ht
  have := Db.le_maxTx ht
  simp; omega

/-! ## Executable sanity checks -/

private def specTestDb : Db :=
  let name : Keyword := ⟨some "person", "name"⟩
  { schema := .ofList [(name, { valueType := .str })]
    log := [
      { id := 1, instant := 10, datoms := [
          ⟨⟨1, .txInstant, .instant 10⟩, true⟩,
          ⟨⟨10, name, .str "Ada"⟩, true⟩] },
      { id := 2, instant := 20, datoms := [
          ⟨⟨2, .txInstant, .instant 20⟩, true⟩,
          ⟨⟨10, name, .str "Ada"⟩, false⟩,
          ⟨⟨10, name, .str "Lovelace"⟩, true⟩] }] }

private def kname : Keyword := ⟨some "person", "name"⟩

#guard specTestDb.contains ⟨10, kname, .str "Lovelace"⟩
#guard !specTestDb.contains ⟨10, kname, .str "Ada"⟩
#guard (specTestDb.asOf 1).contains ⟨10, kname, .str "Ada"⟩
#guard !(specTestDb.asOf 1).contains ⟨10, kname, .str "Lovelace"⟩
#guard specTestDb.lastWrite ⟨10, kname, .str "Ada"⟩ == some (2, false)
#guard specTestDb.maxTx == 2
#guard (specTestDb.since 1).contains ⟨10, kname, .str "Lovelace"⟩
#guard !(specTestDb.since 1).contains ⟨10, kname, .str "Ada"⟩
#guard !(Db.empty .base).contains ⟨10, kname, .str "Ada"⟩

end DatomBau
