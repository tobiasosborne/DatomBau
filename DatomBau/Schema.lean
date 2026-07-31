import Std.Data.TreeMap
import DatomBau.Core

/-!
# Schema

Attribute schemas: value type, cardinality, uniqueness. In v1 the schema is
an ordinary data structure fixed at database creation — a deliberate,
documented departure from Datomic's schema-as-datoms bootstrap, with an
upgrade path (schema alteration transactions) left for later.
-/

namespace DatomBau

/-- `:db/txInstant` — the attribute carried by every transaction entity. -/
def Keyword.txInstant : Keyword := ⟨some "db", "txInstant"⟩

inductive ValueType where
  | str | int | bool | ref | keyword | instant
  deriving DecidableEq, Repr

/-- The type a value actually has. -/
def Value.valueType : Value → ValueType
  | .str _ => .str | .int _ => .int | .bool _ => .bool
  | .ref _ => .ref | .keyword _ => .keyword | .instant _ => .instant

inductive Cardinality where
  | one | many
  deriving DecidableEq, Repr

inductive Uniqueness where
  /-- Not unique. -/
  | none
  /-- Unique value: asserting a duplicate is an error. -/
  | value
  /-- Unique identity: asserting a duplicate upserts (resolves tempids to
  the existing entity). -/
  | identity
  deriving DecidableEq, Repr

structure AttributeSchema where
  valueType   : ValueType
  cardinality : Cardinality := .one
  unique      : Uniqueness := .none
  doc         : String := ""
  deriving Repr

structure Schema where
  attrs : Std.TreeMap Keyword AttributeSchema Keyword.cmp

/-- The built-in schema: just `:db/txInstant`. Every user schema extends
this, so the transactor's auto-appended txInstant datom always typechecks. -/
def Schema.base : Schema :=
  ⟨Std.TreeMap.empty.insert .txInstant
    { valueType := .instant, doc := "transaction wall-clock time" }⟩

def Schema.ofList (l : List (Keyword × AttributeSchema)) : Schema :=
  ⟨l.foldl (fun m p => m.insert p.1 p.2) Schema.base.attrs⟩

def Schema.find? (s : Schema) (a : Keyword) : Option AttributeSchema :=
  s.attrs[a]?

/-- A datom typechecks iff its attribute is declared and the value has the
declared type. (Retractions are held to the same standard.) -/
def Schema.typechecks (s : Schema) (d : TxDatom) : Bool :=
  match s.find? d.a with
  | some a => a.valueType == d.v.valueType
  | none   => false

#guard Schema.base.typechecks ⟨⟨42, .txInstant, .instant 100⟩, true⟩
#guard !Schema.base.typechecks ⟨⟨42, .txInstant, .str "yesterday"⟩, true⟩
#guard !Schema.base.typechecks ⟨⟨42, ⟨some "person", "name"⟩, .str "Ada"⟩, true⟩

end DatomBau
