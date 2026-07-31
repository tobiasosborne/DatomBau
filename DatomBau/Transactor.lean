import DatomBau.Spec

/-!
# The transactor (Phase 2a: concrete entity ids)

`Db.transact` turns transaction data (adds, retracts, entity retractions)
into one appended log transaction:

1. expand ops — implicit cardinality-one retraction, `retractEntity`
   (current datoms of the entity plus inbound refs);
2. elide no-ops — asserts of already-current facts, retracts of absent
   facts — so "last write in the log" coincides with "asserting
   transaction" (real Datomic elides redundant datoms too);
3. reject conflicts — same fact asserted and retracted in one transaction,
   or two different values added for a cardinality-one attribute;
4. validate — every appended datom typechecks, every mentioned id is
   bounded by the transaction id;
5. append, with the transaction's own `:db/txInstant` datom at the head
   (transactions are entities).

Flagships: `transact_wf` (well-formedness preservation, which includes
per-log-datom well-typedness), `transact_cardOne` (the cardinality-one
invariant), and `asOf_transact` (the freeze theorem lifted to transact).

Tempids and unique-identity upsert are Phase 2b.
-/

namespace DatomBau

inductive TxOp where
  | add (e : Nat) (a : Keyword) (v : Value)
  | retract (e : Nat) (a : Keyword) (v : Value)
  | retractEntity (e : Nat)
  deriving DecidableEq, Repr

inductive TxError where
  | typeMismatch (d : TxDatom)
  | badEntityId (d : TxDatom)
  | datomConflict (f : Fact)
  | cardOneConflict (e : Nat) (a : Keyword)
  deriving Repr

/-! ## Current-state helpers (spec-level scans) -/

/-- All currently-true facts, deduplicated. Spec-level: a full scan. -/
def Db.currentFacts (db : Db) : List Fact :=
  ((db.datoms.map (·.toFact)).eraseDups).filter fun f => db.contains f

/-- Current values of `(e, a)`. -/
def Db.currentValues (db : Db) (e : Nat) (a : Keyword) : List Value :=
  (db.currentFacts.filter fun f => f.e == e && f.a == a).map (·.v)

def Schema.isCardOne (s : Schema) (a : Keyword) : Bool :=
  match s.find? a with
  | some attr => attr.cardinality == .one
  | none      => false

/-! ## Expansion, elision, conflicts -/

/-- Expand one op into datoms. An `add` on a cardinality-one attribute
implicitly retracts every *other* current value; `retractEntity` retracts
every current fact of the entity plus every inbound reference to it. -/
def Db.expandOp (db : Db) (op : TxOp) : List TxDatom :=
  match op with
  | .add e a v =>
    (if db.schema.isCardOne a then
      ((db.currentValues e a).filter fun v' => v' != v).map
        fun v' => ⟨⟨e, a, v'⟩, false⟩
    else []) ++ [⟨⟨e, a, v⟩, true⟩]
  | .retract e a v => [⟨⟨e, a, v⟩, false⟩]
  | .retractEntity e =>
    (db.currentFacts.filter fun f => f.e == e || f.v == Value.ref e).map
      fun f => ⟨f, false⟩

/-- No-op elision: keep asserts of absent facts, retracts of present ones. -/
def Db.keep (db : Db) (d : TxDatom) : Bool :=
  if d.added then !db.contains d.toFact else db.contains d.toFact

/-- Same fact, opposite polarity: rejected within one transaction. -/
def TxDatom.conflictsWith (d d' : TxDatom) : Bool :=
  d.toFact == d'.toFact && d.added != d'.added

/-- Two different values added for one cardinality-one `(e, a)`: rejected. -/
def cardOneClash (s : Schema) (d d' : TxDatom) : Bool :=
  d.added && d'.added && s.isCardOne d.a &&
    d.e == d'.e && d.a == d'.a && d.v != d'.v

/-! ## transact -/

/-- Validation and append, given the assembled datom list. Factored out so
`transact` theorems can decompose a successful run once. -/
def Db.transactCore (db : Db) (txId instant : Nat) (full : List TxDatom) :
    Except TxError Db :=
  match full.find? fun d => full.any fun d' => d.conflictsWith d' with
  | some d => throw (.datomConflict d.toFact)
  | none =>
  match full.find? fun d => full.any fun d' => cardOneClash db.schema d d' with
  | some d => throw (.cardOneConflict d.e d.a)
  | none =>
  match full.find? fun d => !db.schema.typechecks d with
  | some d => throw (.typeMismatch d)
  | none =>
  match full.find? fun d => d.entityIds.any fun i => txId < i with
  | some d => throw (.badEntityId d)
  | none => .ok (db.append ⟨txId, instant, full⟩)

/-- Transact: expand, elide, dedup, prepend the txInstant datom, validate,
append. The instant is clamped to keep instants monotone. -/
def Db.transact (db : Db) (ops : List TxOp) (now : Nat) : Except TxError Db :=
  db.transactCore db.nextId (max now db.lastInstant)
    (⟨⟨db.nextId, .txInstant, .instant (max now db.lastInstant)⟩, true⟩ ::
      ((ops.flatMap db.expandOp).filter db.keep).eraseDups)

/-! ## Decomposing a successful transact -/

private theorem pair_forall_of_find?_none {l : List TxDatom}
    {p : TxDatom → TxDatom → Bool}
    (h : (l.find? fun d => l.any fun d' => p d d') = none) :
    ∀ d ∈ l, ∀ d' ∈ l, p d d' = false := by
  intro d hd d' hd'
  have hall := List.find?_eq_none.mp h d hd
  simp only [List.any_eq_true, not_exists, not_and] at hall
  have := hall d' hd'
  simpa using this

theorem Db.transactCore_ok {db : Db} {txId instant : Nat}
    {full : List TxDatom} {db' : Db}
    (h : db.transactCore txId instant full = .ok db') :
    db' = db.append ⟨txId, instant, full⟩ ∧
    (∀ d ∈ full, ∀ d' ∈ full, d.conflictsWith d' = false) ∧
    (∀ d ∈ full, ∀ d' ∈ full, cardOneClash db.schema d d' = false) ∧
    (∀ d ∈ full, db.schema.typechecks d = true) ∧
    (∀ d ∈ full, ∀ i ∈ d.entityIds, i ≤ txId) := by
  unfold Db.transactCore at h
  split at h
  next => exact absurd h (by simp)
  next hconf =>
    split at h
    next => exact absurd h (by simp)
    next hcard =>
      split at h
      next => exact absurd h (by simp)
      next htype =>
        split at h
        next => exact absurd h (by simp)
        next hids =>
          have hdb : db' = db.append ⟨txId, instant, full⟩ := by
            cases h; rfl
          refine ⟨hdb, pair_forall_of_find?_none hconf,
            pair_forall_of_find?_none hcard, ?_, ?_⟩
          · intro d hd
            have := List.find?_eq_none.mp htype d hd
            simpa using this
          · intro d hd i hi
            have hall := List.find?_eq_none.mp hids d hd
            simp only [List.any_eq_true, not_exists, not_and] at hall
            have := hall i hi
            simp at this
            omega

/-! ## Flagship: WF preservation -/

theorem Db.transact_wf {db db' : Db} {ops : List TxOp} {now : Nat}
    (hwf : db.WF) (h : db.transact ops now = .ok db') : db'.WF := by
  unfold Db.transact at h
  obtain ⟨rfl, hconf, hcard, htype, hids⟩ := Db.transactCore_ok h
  have hfresh : ∀ s ∈ db.log, s.id < db.nextId := by
    intro s hs
    have := Db.le_maxTx hs
    simp only [Db.nextId]
    omega
  constructor
  case txIds_strictMono =>
    simp only [Db.append]
    rw [List.pairwise_append]
    exact ⟨hwf.txIds_strictMono, by simp,
      fun s hs t' ht' => by simp at ht'; subst ht'; exact hfresh s hs⟩
  case instants_mono =>
    simp only [Db.append]
    rw [List.pairwise_append]
    refine ⟨hwf.instants_mono, by simp, ?_⟩
    intro s hs t' ht'
    simp at ht'; subst ht'
    have := Db.le_lastInstant hs
    show s.instant ≤ max now db.lastInstant
    omega
  case ids_bounded =>
    simp only [Db.append]
    intro t ht d hd i hi
    rcases List.mem_append.mp ht with hold | hnew
    · exact hwf.ids_bounded t hold d hd i hi
    · simp at hnew; subst hnew
      exact hids d hd i hi
  case wellTyped =>
    simp only [Db.append]
    intro t ht d hd
    rcases List.mem_append.mp ht with hold | hnew
    · exact hwf.wellTyped t hold d hd
    · simp at hnew; subst hnew
      exact htype d hd
  case txInstant_present =>
    simp only [Db.append]
    intro t ht
    rcases List.mem_append.mp ht with hold | hnew
    · exact hwf.txInstant_present t hold
    · simp at hnew; subst hnew
      exact List.mem_cons_self ..

/-! ## Flagship: the freeze theorem, lifted to transact -/

theorem Db.asOf_transact {db db' : Db} {ops : List TxOp} {now t : Nat}
    (h : db.transact ops now = .ok db') (ht : t ≤ db.maxTx) :
    db'.asOf t = db.asOf t := by
  unfold Db.transact at h
  obtain ⟨rfl, -, -, -, -⟩ := Db.transactCore_ok h
  exact Db.asOf_append (by simp only [Db.nextId]; omega) ht

/-! ## Flagship: the cardinality-one invariant -/

/-- At most one current value per entity and cardinality-one attribute. -/
def Db.CardOneOk (db : Db) : Prop :=
  ∀ (e : Nat) (a : Keyword) (v₁ v₂ : Value),
    db.schema.isCardOne a = true →
    (⟨e, a, v₁⟩ : Fact) ∈ db → (⟨e, a, v₂⟩ : Fact) ∈ db → v₁ = v₂

theorem Db.CardOneOk.empty (s : Schema) : (Db.empty s).CardOneOk := by
  intro e a v₁ v₂ _ h₁ _
  rw [Db.mem_iff_lastWrite] at h₁
  obtain ⟨tx, h₁⟩ := h₁
  simp [Db.lastWrite, Db.empty, Db.datoms] at h₁

/-- A transaction's verdict on a mentioned fact exists. -/
theorem Transaction.lastOp_ne_none_of_mem {t : Transaction} {d : TxDatom}
    (hd : d ∈ t.datoms) : t.lastOp d.toFact ≠ none := by
  unfold Transaction.lastOp
  intro hcon
  rw [Option.map_eq_none_iff] at hcon
  have := List.find?_eq_none.mp hcon d (List.mem_reverse.mpr hd)
  simp at this

/-- Dissect a transaction verdict: some datom carries it. -/
theorem Transaction.lastOp_some {t : Transaction} {f : Fact} {b : Bool}
    (h : t.lastOp f = some b) :
    ∃ d ∈ t.datoms, d.toFact = f ∧ d.added = b := by
  unfold Transaction.lastOp at h
  cases hfind : t.datoms.reverse.find? (·.toFact == f) with
  | none => rw [hfind] at h; simp at h
  | some d =>
    rw [hfind] at h
    simp only [Option.map_some, Option.some.injEq] at h
    refine ⟨d, List.mem_reverse.mp (List.mem_of_find?_eq_some hfind), ?_, h⟩
    have := List.find?_some hfind
    simpa using this

/-- A current fact is somewhere in the datom history. -/
theorem Db.mem_currentFacts_of_mem {db : Db} {f : Fact} (hf : f ∈ db) :
    f ∈ db.currentFacts := by
  have hmem : f ∈ db.datoms.map (·.toFact) := by
    rw [Db.mem_iff_lastWrite] at hf
    obtain ⟨tx, hlw⟩ := hf
    unfold Db.lastWrite at hlw
    cases hfind : db.datoms.reverse.find? (·.toFact == f) with
    | none => rw [hfind] at hlw; simp at hlw
    | some d =>
      have hd : d ∈ db.datoms :=
        List.mem_reverse.mp (List.mem_of_find?_eq_some hfind)
      have hdf : d.toFact = f := by
        have := List.find?_some hfind
        simpa using this
      exact List.mem_map.mpr ⟨d, hd, hdf⟩
  unfold Db.currentFacts
  rw [List.mem_filter]
  exact ⟨List.mem_eraseDups.mpr hmem, by simpa [Db.mem_def] using hf⟩

theorem Db.mem_currentValues {db : Db} {e : Nat} {a : Keyword} {v : Value}
    (hf : (⟨e, a, v⟩ : Fact) ∈ db) : v ∈ db.currentValues e a := by
  unfold Db.currentValues
  exact List.mem_map.mpr ⟨⟨e, a, v⟩,
    List.mem_filter.mpr ⟨Db.mem_currentFacts_of_mem hf, by simp⟩, rfl⟩

/-- Added datoms in an expansion can only come from an `add` op. -/
theorem Db.add_of_expand_added {db : Db} {ops : List TxOp} {d : TxDatom}
    (hd : d ∈ ops.flatMap db.expandOp) (hadd : d.added = true) :
    TxOp.add d.e d.a d.v ∈ ops := by
  obtain ⟨op, hop, hmem⟩ := List.mem_flatMap.mp hd
  cases op with
  | add e a v =>
    unfold Db.expandOp at hmem
    rcases List.mem_append.mp hmem with hi | hs
    · split at hi
      · obtain ⟨v', -, rfl⟩ := List.mem_map.mp hi
        simp at hadd
      · simp at hi
    · simp at hs; subst hs
      exact hop
  | retract e a v =>
    unfold Db.expandOp at hmem
    simp at hmem; subst hmem
    simp at hadd
  | retractEntity e =>
    unfold Db.expandOp at hmem
    obtain ⟨f, -, rfl⟩ := List.mem_map.mp hmem
    simp at hadd

/-- Expansion completeness: an `add` on a cardinality-one attribute emits a
retract for every differing current value. -/
theorem Db.implicit_retract_mem {db : Db} {ops : List TxOp}
    {e : Nat} {a : Keyword} {v v' : Value}
    (hop : TxOp.add e a v ∈ ops) (hcard : db.schema.isCardOne a = true)
    (hv' : (⟨e, a, v'⟩ : Fact) ∈ db) (hne : v' ≠ v) :
    (⟨⟨e, a, v'⟩, false⟩ : TxDatom) ∈ ops.flatMap db.expandOp := by
  refine List.mem_flatMap.mpr ⟨_, hop, ?_⟩
  have hexp : db.expandOp (TxOp.add e a v) =
      ((db.currentValues e a).filter fun v'' => v'' != v).map
        (fun v'' => ⟨⟨e, a, v''⟩, false⟩) ++ [⟨⟨e, a, v⟩, true⟩] := by
    simp [Db.expandOp, hcard]
  rw [hexp]
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨v',
    List.mem_filter.mpr ⟨Db.mem_currentValues hv', by simpa using hne⟩, rfl⟩

/-- The general shape of the cardinality-one preservation argument, stated
against a raw append satisfying the transactor's checks. `hbody` is the
expansion-completeness property: every add on a cardinality-one attribute
is accompanied by retracts of all differing current values. -/
theorem Db.cardOne_of_append {db : Db} {tr : Transaction}
    (hco : db.CardOneOk)
    (hcard : ∀ d ∈ tr.datoms, ∀ d' ∈ tr.datoms, cardOneClash db.schema d d' = false)
    (hbody : ∀ d ∈ tr.datoms, d.added = true →
      db.schema.isCardOne d.a = true →
      ∀ v', (⟨d.e, d.a, v'⟩ : Fact) ∈ db → v' ≠ d.v →
        (⟨⟨d.e, d.a, v'⟩, false⟩ : TxDatom) ∈ tr.datoms) :
    (db.append tr).CardOneOk := by
  intro e a v₁ v₂ h1a hm₁ hm₂
  have hsch : (db.append tr).schema = db.schema := rfl
  rw [hsch] at h1a
  rw [Db.mem_append_iff] at hm₁ hm₂
  rcases Classical.em (v₁ = v₂) with heq | hne
  · exact heq
  exfalso
  rcases hm₁ with hop₁ | ⟨hnone₁, hdb₁⟩ <;> rcases hm₂ with hop₂ | ⟨hnone₂, hdb₂⟩
  · -- both added in tr: cardOneClash
    obtain ⟨d₁, hd₁, hf₁, hb₁⟩ := Transaction.lastOp_some hop₁
    obtain ⟨d₂, hd₂, hf₂, hb₂⟩ := Transaction.lastOp_some hop₂
    have hclash := hcard d₁ hd₁ d₂ hd₂
    have he₁ : d₁.e = e := congrArg Fact.e hf₁
    have ha₁ : d₁.a = a := congrArg Fact.a hf₁
    have hv₁ : d₁.v = v₁ := congrArg Fact.v hf₁
    have he₂ : d₂.e = e := congrArg Fact.e hf₂
    have ha₂ : d₂.a = a := congrArg Fact.a hf₂
    have hv₂ : d₂.v = v₂ := congrArg Fact.v hf₂
    unfold cardOneClash at hclash
    rw [hb₁, hb₂, ha₁, h1a, he₁, he₂, ha₂, hv₁, hv₂] at hclash
    simp at hclash
    exact hne hclash
  · -- v₁ added in tr, v₂ current and silent: expansion forces a retract
    obtain ⟨d₁, hd₁, hf₁, hb₁⟩ := Transaction.lastOp_some hop₁
    have he₁ : d₁.e = e := congrArg Fact.e hf₁
    have ha₁ : d₁.a = a := congrArg Fact.a hf₁
    have hv₁ : d₁.v = v₁ := congrArg Fact.v hf₁
    have hret := hbody d₁ hd₁ hb₁ (by rw [ha₁]; exact h1a) v₂
      (by rw [he₁, ha₁]; exact hdb₂) (by rw [hv₁]; exact fun hcon => hne hcon.symm)
    have : (⟨⟨e, a, v₂⟩, false⟩ : TxDatom) ∈ tr.datoms := by
      rw [← he₁, ← ha₁]; exact hret
    exact Transaction.lastOp_ne_none_of_mem this hnone₂
  · -- symmetric
    obtain ⟨d₂, hd₂, hf₂, hb₂⟩ := Transaction.lastOp_some hop₂
    have he₂ : d₂.e = e := congrArg Fact.e hf₂
    have ha₂ : d₂.a = a := congrArg Fact.a hf₂
    have hv₂ : d₂.v = v₂ := congrArg Fact.v hf₂
    have hret := hbody d₂ hd₂ hb₂ (by rw [ha₂]; exact h1a) v₁
      (by rw [he₂, ha₂]; exact hdb₁) (by rw [hv₂]; exact hne)
    have : (⟨⟨e, a, v₁⟩, false⟩ : TxDatom) ∈ tr.datoms := by
      rw [← he₂, ← ha₂]; exact hret
    exact Transaction.lastOp_ne_none_of_mem this hnone₁
  · -- both old: the old invariant
    exact hne (hco e a v₁ v₂ h1a hdb₁ hdb₂)

theorem Db.transact_cardOne {db db' : Db} {ops : List TxOp} {now : Nat}
    (hwf : db.WF) (hco : db.CardOneOk)
    (h : db.transact ops now = .ok db') : db'.CardOneOk := by
  unfold Db.transact at h
  obtain ⟨rfl, hconf, hcard, -, -⟩ := Db.transactCore_ok h
  refine Db.cardOne_of_append hco hcard ?_
  intro d hd hadd hcardone v' hv' hne
  rcases List.mem_cons.mp hd with rfl | hd
  · -- the txInstant head datom: its entity is fresh, so no current facts
    exfalso
    refine Db.not_mem_of_fresh hwf ?_ hv'
    simp only [Db.nextId]
    omega
  · -- a body datom: its add came from an op; expansion emitted the retract
    have hflat : d ∈ ops.flatMap db.expandOp :=
      (List.mem_filter.mp (List.mem_eraseDups.mp hd)).1
    have hop := Db.add_of_expand_added hflat hadd
    have hret := Db.implicit_retract_mem hop hcardone hv' hne
    apply List.mem_cons_of_mem
    rw [List.mem_eraseDups]
    refine List.mem_filter.mpr ⟨hret, ?_⟩
    unfold Db.keep
    simpa [Db.mem_def] using hv'

/-! ## Executable sanity checks -/

private def kname : Keyword := ⟨some "person", "name"⟩
private def kfriend : Keyword := ⟨some "person", "friend"⟩

private def tSchema : Schema := .ofList
  [(kname, { valueType := .str }),
   (kfriend, { valueType := .ref, cardinality := .many })]

private def db0 : Db := Db.empty tSchema

-- First transaction (txId 1): name entity 0.
private def db1 : Db :=
  (db0.transact [.add 0 kname (.str "Ada")] 100).toOption.getD db0

-- Second transaction (txId 2): rename — implicit card-one retraction.
private def db2 : Db :=
  (db1.transact [.add 0 kname (.str "Lovelace")] 200).toOption.getD db1

#guard (db0.transact [.add 0 kname (.str "Ada")] 100).isOk
#guard db1.contains ⟨0, kname, .str "Ada"⟩
#guard db2.contains ⟨0, kname, .str "Lovelace"⟩
#guard !db2.contains ⟨0, kname, .str "Ada"⟩          -- implicitly retracted
#guard (db2.asOf 1).contains ⟨0, kname, .str "Ada"⟩  -- but still there asOf 1
#guard db2.contains ⟨2, .txInstant, .instant 200⟩    -- tx is an entity
#guard db2.maxTx == 2

-- Type errors are rejected.
#guard !(db0.transact [.add 0 kname (.int 3)] 100).isOk
-- Unknown attributes are rejected.
#guard !(db0.transact [.add 0 ⟨some "x", "y"⟩ (.str "z")] 100).isOk
-- Add + retract of the same *non-current* fact: the retract is a no-op and
-- is elided, so this succeeds (post-elision, polarity conflicts cannot
-- occur; the check remains as belt-and-braces).
#guard (db1.transact [.add 0 kname (.str "B"), .retract 0 kname (.str "B")] 150).isOk
-- Two adds on one cardinality-one attribute are rejected.
#guard !(db0.transact [.add 0 kname (.str "A"), .add 0 kname (.str "B")] 100).isOk
-- Out-of-range entity ids are rejected.
#guard !(db0.transact [.add 99 kname (.str "A")] 100).isOk
-- No-op elision: re-asserting a current fact appends nothing about it.
#guard ((db1.transact [.add 0 kname (.str "Ada")] 150).toOption.getD db0
        |>.lastWrite ⟨0, kname, .str "Ada"⟩) == some (1, true)

-- retractEntity removes the entity's facts and inbound refs.
private def db3 : Db :=
  (db2.transact [.add 1 kname (.str "Grace"), .add 1 kfriend (.ref 0)] 300
    ).toOption.getD db2
private def db4 : Db :=
  (db3.transact [.retractEntity 0] 400).toOption.getD db3

#guard db3.contains ⟨1, kfriend, .ref 0⟩
#guard !db4.contains ⟨0, kname, .str "Lovelace"⟩
#guard !db4.contains ⟨1, kfriend, .ref 0⟩            -- inbound ref retracted
#guard db4.contains ⟨1, kname, .str "Grace"⟩          -- untouched

end DatomBau
