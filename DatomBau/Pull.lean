import DatomBau.Index

/-!
# Pull: entity-centric reads (Phase 4 warm-up)

`pull` walks an entity's attributes — forward (`:person/name`) and reverse
(`:person/_friend`, who references me) — off the EAVT and VAET indexes.
`:db/id` is the entity id itself. Correctness is stated against the spec's
`lastWrite`, via index coherence.
-/

namespace DatomBau

inductive PullAttr where
  /-- Forward: the values of attribute `a` on the entity. -/
  | attr (a : Keyword)
  /-- Reverse (Datomic's `:ns/_attr`): entities referencing this one
  via `a`. -/
  | rev (a : Keyword)
  deriving DecidableEq, Repr

def IndexedDb.pullAttr (idb : IndexedDb) (e : Nat) : PullAttr → List Value
  | .attr a => (idb.datomsEA e a).map (·.v)
  | .rev a  => ((idb.refsTo e).filter (·.a == a)).map fun x => .ref x.e

/-- One-level pull: the requested attributes of an entity. `:db/id` is the
argument itself. -/
def IndexedDb.pull (idb : IndexedDb) (e : Nat) (pat : List PullAttr) :
    List (PullAttr × List Value) :=
  pat.map fun pa => (pa, idb.pullAttr e pa)

theorem IndexedDb.mem_pullAttr_attr {idb : IndexedDb} (h : idb.WF)
    {e : Nat} {a : Keyword} {v : Value} :
    v ∈ idb.pullAttr e (.attr a) ↔
      ∃ tx, idb.db.lastWrite ⟨e, a, v⟩ = some (tx, true) := by
  unfold IndexedDb.pullAttr
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨⟨xe, xa, xv⟩, xtx⟩, hx, rfl⟩
    obtain ⟨he, ha, hlw⟩ := (IndexedDb.mem_datomsEA h).mp hx
    dsimp at he ha hlw ⊢
    subst he; subst ha
    exact ⟨xtx, hlw⟩
  · rintro ⟨tx, hlw⟩
    exact ⟨⟨⟨e, a, v⟩, tx⟩, (IndexedDb.mem_datomsEA h).mpr ⟨rfl, rfl, hlw⟩, rfl⟩

theorem IndexedDb.mem_pullAttr_rev {idb : IndexedDb} (h : idb.WF)
    {e : Nat} {a : Keyword} {v : Value} :
    v ∈ idb.pullAttr e (.rev a) ↔
      ∃ e' tx, v = .ref e' ∧
        idb.db.lastWrite ⟨e', a, .ref e⟩ = some (tx, true) := by
  unfold IndexedDb.pullAttr
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨⟨xe, xa, xv⟩, xtx⟩, hx, rfl⟩
    obtain ⟨hmem, hfa⟩ := List.mem_filter.mp hx
    obtain ⟨hv, hlw⟩ := (IndexedDb.mem_refsTo h).mp hmem
    dsimp at hv hlw hfa ⊢
    subst hv
    have ha : xa = a := by simpa using hfa
    subst ha
    exact ⟨xe, xtx, rfl, hlw⟩
  · rintro ⟨e', tx, rfl, hlw⟩
    refine ⟨⟨⟨e', a, .ref e⟩, tx⟩, List.mem_filter.mpr ⟨?_, by simp⟩, rfl⟩
    exact (IndexedDb.mem_refsTo h).mpr ⟨rfl, hlw⟩

end DatomBau
