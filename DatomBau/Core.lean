import Std.Data.TreeSet

/-!
# Core data model

Datomic's atomic unit is the datom: an (entity, attribute, value) fact,
stamped with the transaction that asserted or retracted it.

Ordering design note: we deliberately do NOT `deriving Ord` on `Value` —
there is no deriving handler for `Std.TransCmp`/`Std.LawfulEqCmp`, and a
derived 6-constructor comparator would need a 6×6×6 transitivity case bash.
Instead every comparator in this project is a `compareLex`/`compareOn` chain
over total projections, so `TransCmp` is found by instance search from the
compositional instances in core, and only the (short) `LawfulEqCmp` proofs
are by hand.
-/

namespace DatomBau

/-- Entity ids. Transactions are entities too, allocated from the same
fresh-id stream. -/
abbrev EntityId := Nat

/-- Transaction ids are entity ids (tx-as-entity, as in Datomic). -/
abbrev TxId := Nat

/-- A namespaced keyword, e.g. `:person/name` is `⟨some "person", "name"⟩`. -/
structure Keyword where
  ns   : Option String
  name : String
  deriving DecidableEq, Repr, Inhabited

/-- Parse `"person/name"` or `":person/name"` into a keyword. -/
def Keyword.ofString (s : String) : Keyword :=
  let s := (s.dropPrefix ":").toString
  match s.splitOn "/" with
  | [ns, n] => ⟨some ns, n⟩
  | _       => ⟨none, s⟩

def Keyword.toString (k : Keyword) : String :=
  match k.ns with
  | some ns => s!":{ns}/{k.name}"
  | none    => s!":{k.name}"

instance : ToString Keyword := ⟨Keyword.toString⟩

def Keyword.cmp : Keyword → Keyword → Ordering :=
  compareLex (compareOn (·.ns)) (compareOn (·.name))

instance : Std.TransCmp Keyword.cmp := by unfold Keyword.cmp; infer_instance

instance : Std.LawfulEqCmp Keyword.cmp where
  eq_of_compare {a b} h := by
    simp only [Keyword.cmp, compareLex_eq_eq, compareOn] at h
    cases a; cases b
    simp only [Keyword.mk.injEq]
    exact ⟨Std.LawfulEqOrd.eq_of_compare h.1, Std.LawfulEqOrd.eq_of_compare h.2⟩

instance : Ord Keyword := ⟨Keyword.cmp⟩
instance : Std.TransOrd Keyword := inferInstanceAs (Std.TransCmp Keyword.cmp)
instance : Std.LawfulEqOrd Keyword := inferInstanceAs (Std.LawfulEqCmp Keyword.cmp)

/-- Values a datom can carry. `ref` makes the graph: it points at another
entity. `instant` is a timestamp in milliseconds. -/
inductive Value where
  | str     (s : String)
  | int     (n : Int)
  | bool    (b : Bool)
  | ref     (e : EntityId)
  | keyword (k : Keyword)
  | instant (t : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Value

/-- Constructor tag, the leading key of the `Value` ordering. -/
def tag : Value → Nat
  | .str _ => 0 | .int _ => 1 | .bool _ => 2
  | .ref _ => 3 | .keyword _ => 4 | .instant _ => 5

/- Total payload projections (defaulting on foreign constructors), so the
comparator is a lex chain of `compareOn`s and lawfulness comes cheap. -/

def strPayload : Value → String
  | .str s => s | _ => ""

def intPayload : Value → Int
  | .int n => n | _ => 0

def boolPayload : Value → Bool
  | .bool b => b | _ => false

/-- Shared by `ref` and `instant`; the tag disambiguates. -/
def natPayload : Value → Nat
  | .ref e => e | .instant t => t | _ => 0

def kwPayload : Value → Keyword
  | .keyword k => k | _ => ⟨none, ""⟩

def cmp : Value → Value → Ordering :=
  compareLex (compareOn tag) <|
    compareLex (compareOn strPayload) <|
      compareLex (compareOn intPayload) <|
        compareLex (compareOn boolPayload) <|
          compareLex (compareOn natPayload) (compareOn kwPayload)

instance : Std.TransCmp cmp := by unfold cmp; infer_instance

instance : Std.LawfulEqCmp cmp where
  eq_of_compare {a b} h := by
    simp only [cmp, compareLex_eq_eq, compareOn] at h
    obtain ⟨htag, hstr, hint, hbool, hnat, hkw⟩ := h
    cases a <;> cases b <;>
      simp_all [tag, strPayload, intPayload, boolPayload, natPayload, kwPayload,
        Std.LawfulEqCmp.compare_eq_iff_eq]

end Value

instance : Ord Value := ⟨Value.cmp⟩
instance : Std.TransOrd Value := inferInstanceAs (Std.TransCmp Value.cmp)
instance : Std.LawfulEqOrd Value := inferInstanceAs (Std.LawfulEqCmp Value.cmp)

/-- A fact: entity `e` has value `v` for attribute `a`. Facts are what a
database *currently* claims; datoms are facts stamped with provenance. -/
structure Fact where
  e : EntityId
  a : Keyword
  v : Value
  deriving DecidableEq, Repr

/-- A datom as stored in the log: a fact plus whether it was asserted
(`added = true`) or retracted. The transaction id lives on the enclosing
`Transaction`, not here — that redundancy would be an invariant to carry. -/
structure TxDatom extends Fact where
  added : Bool
  deriving DecidableEq, Repr

/-- The full five-tuple datom `(e a v tx added)`, as a *derived* view
produced by flattening the log. -/
structure Datom extends Fact where
  tx    : TxId
  added : Bool
  deriving DecidableEq, Repr

/-- An index entry: a currently-asserted fact plus the transaction that
asserted it. The four covering indexes are `TreeSet Entry`s under the four
sort orders below. -/
structure Entry extends Fact where
  tx : TxId
  deriving DecidableEq, Repr

namespace Entry

theorem ext' {x y : Entry} (he : x.e = y.e) (ha : x.a = y.a) (hv : x.v = y.v)
    (htx : x.tx = y.tx) : x = y := by
  obtain ⟨⟨_, _, _⟩, _⟩ := x
  obtain ⟨⟨_, _, _⟩, _⟩ := y
  simp_all

/-- EAVT: primary "row" order — everything about an entity, grouped. -/
def cmpEAVT : Entry → Entry → Ordering :=
  compareLex (compareOn (·.e)) <|
    compareLex (compareOn (·.a)) <| compareLex (compareOn (·.v)) (compareOn (·.tx))

/-- AEVT: "column" order — one attribute across all entities. -/
def cmpAEVT : Entry → Entry → Ordering :=
  compareLex (compareOn (·.a)) <|
    compareLex (compareOn (·.e)) <| compareLex (compareOn (·.v)) (compareOn (·.tx))

/-- AVET: value lookup — `(attr, value)` to entities. -/
def cmpAVET : Entry → Entry → Ordering :=
  compareLex (compareOn (·.a)) <|
    compareLex (compareOn (·.v)) <| compareLex (compareOn (·.e)) (compareOn (·.tx))

/-- VAET: reverse-reference order (only `ref` values are indexed). -/
def cmpVAET : Entry → Entry → Ordering :=
  compareLex (compareOn (·.v)) <|
    compareLex (compareOn (·.a)) <| compareLex (compareOn (·.e)) (compareOn (·.tx))

instance : Std.TransCmp cmpEAVT := by unfold cmpEAVT; infer_instance
instance : Std.TransCmp cmpAEVT := by unfold cmpAEVT; infer_instance
instance : Std.TransCmp cmpAVET := by unfold cmpAVET; infer_instance
instance : Std.TransCmp cmpVAET := by unfold cmpVAET; infer_instance

instance : Std.LawfulEqCmp cmpEAVT where
  eq_of_compare {x y} h := by
    simp only [cmpEAVT, compareLex_eq_eq, compareOn] at h
    exact ext' (Std.LawfulEqOrd.eq_of_compare h.1)
      (Std.LawfulEqOrd.eq_of_compare h.2.1)
      (Std.LawfulEqOrd.eq_of_compare h.2.2.1)
      (Std.LawfulEqOrd.eq_of_compare h.2.2.2)

instance : Std.LawfulEqCmp cmpAEVT where
  eq_of_compare {x y} h := by
    simp only [cmpAEVT, compareLex_eq_eq, compareOn] at h
    exact ext' (Std.LawfulEqOrd.eq_of_compare h.2.1)
      (Std.LawfulEqOrd.eq_of_compare h.1)
      (Std.LawfulEqOrd.eq_of_compare h.2.2.1)
      (Std.LawfulEqOrd.eq_of_compare h.2.2.2)

instance : Std.LawfulEqCmp cmpAVET where
  eq_of_compare {x y} h := by
    simp only [cmpAVET, compareLex_eq_eq, compareOn] at h
    exact ext' (Std.LawfulEqOrd.eq_of_compare h.2.2.1)
      (Std.LawfulEqOrd.eq_of_compare h.1)
      (Std.LawfulEqOrd.eq_of_compare h.2.1)
      (Std.LawfulEqOrd.eq_of_compare h.2.2.2)

instance : Std.LawfulEqCmp cmpVAET where
  eq_of_compare {x y} h := by
    simp only [cmpVAET, compareLex_eq_eq, compareOn] at h
    exact ext' (Std.LawfulEqOrd.eq_of_compare h.2.2.1)
      (Std.LawfulEqOrd.eq_of_compare h.2.1)
      (Std.LawfulEqOrd.eq_of_compare h.1)
      (Std.LawfulEqOrd.eq_of_compare h.2.2.2)

end Entry

/-! ## Phase-0 spike: the TreeSet lemmas Phase 3 depends on

If this section compiles, the index foundation is sound: membership,
`toList`, and slice lemmas all apply to our comparators.
-/

section Spike
open Std

example {t : TreeSet Entry Entry.cmpEAVT} {x : Entry} :
    x ∈ t.toList ↔ x ∈ t :=
  TreeSet.mem_toList

example {t : TreeSet Entry Entry.cmpEAVT} {x k : Entry} :
    k ∈ t.insert x ↔ Entry.cmpEAVT x k = .eq ∨ k ∈ t :=
  TreeSet.mem_insert

set_option maxHeartbeats 1000000 in
example {t : TreeSet Entry Entry.cmpAVET} {bound : Entry} :
    t[*...=bound].toList = t.toList.filter (fun x => (Entry.cmpAVET x bound).isLE) :=
  TreeSet.toList_ric (cmp := Entry.cmpAVET)

example {t : TreeSet Entry Entry.cmpVAET} :
    t.toList.Pairwise (fun x y => Entry.cmpVAET x y = .lt) :=
  TreeSet.ordered_toList

end Spike

/-! Executable sanity checks. -/

#guard Keyword.ofString ":person/name" == ⟨some "person", "name"⟩
#guard Keyword.ofString "db" == ⟨none, "db"⟩
#guard Keyword.cmp ⟨some "person", "name"⟩ ⟨some "person", "name"⟩ == .eq
#guard Value.cmp (.int 3) (.int 4) == .lt
#guard Value.cmp (.str "a") (.int 0) == .lt   -- tag order: str < int
#guard Value.cmp (.ref 7) (.instant 7) == .lt -- tags differ, payload shared

#guard
  let x : Entry := ⟨⟨1, .ofString ":person/name", .str "Ada"⟩, 100⟩
  let s : Std.TreeSet Entry Entry.cmpEAVT := (Std.TreeSet.empty).insert x
  s.contains x && !s.contains ⟨⟨2, .ofString ":person/name", .str "Ada"⟩, 100⟩

end DatomBau
