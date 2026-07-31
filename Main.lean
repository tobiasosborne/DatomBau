import DatomBau

/-!
End-to-end demo: schema → transactions (tempids, upsert, retractEntity)
→ Datalog queries → asOf time-travel.
-/

open DatomBau

def kName : Keyword := .ofString ":person/name"
def kEmail : Keyword := .ofString ":person/email"
def kFriend : Keyword := .ofString ":person/friend"

def demoSchema : Schema := .ofList
  [(kName,   { valueType := .str }),
   (kEmail,  { valueType := .str, unique := .identity }),
   (kFriend, { valueType := .ref, cardinality := .many })]

def Value.show : Value → String
  | .str s => s!"\"{s}\""
  | .int n => toString n
  | .bool b => toString b
  | .ref e => s!"#{e}"
  | .keyword k => k.toString
  | .instant t => s!"@{t}"

def showRows (rows : List (List Value)) : String :=
  if rows.isEmpty then "  (no results)"
  else String.intercalate "\n" (rows.map fun row =>
    "  [" ++ String.intercalate ", " (row.map Value.show) ++ "]")

def qNames : Query :=
  ⟨["e", "n"], [⟨.var "e", .const (.keyword kName), .var "n"⟩]⟩

def qFriendNames (who : String) : Query :=
  ⟨["n"],
   [⟨.var "g", .const (.keyword kName), .const (.str who)⟩,
    ⟨.var "g", .const (.keyword kFriend), .var "f"⟩,
    ⟨.var "f", .const (.keyword kName), .var "n"⟩]⟩

def main : IO Unit := do
  IO.println "DatomBau — a verified Datomic core in Lean 4"
  IO.println "============================================\n"
  let db0 := Db.empty demoSchema

  -- tx 1: two people via tempids, wired together by a tempid ref.
  let .ok r1 := db0.transactData
    [.add (.tmp "ada")   kName   (.val (.str "Ada")),
     .add (.tmp "ada")   kEmail  (.val (.str "ada@lovelace.io")),
     .add (.tmp "grace") kName   (.val (.str "Grace")),
     .add (.tmp "grace") kEmail  (.val (.str "grace@hopper.io")),
     .add (.tmp "grace") kFriend (.tmp "ada")] 1000
    | IO.println "tx1 failed"
  IO.println s!"tx {r1.txId}: created {r1.tempids.map (·.2)} \
    (tempids {r1.tempids.map (·.1)})"
  IO.println "\n[:find ?e ?n :where [?e :person/name ?n]]"
  IO.println (showRows (r1.db.query qNames))

  -- tx 2: upsert by unique email — resolves to Ada's entity, and
  -- cardinality-one implicitly retracts the old name.
  let .ok r2 := r1.db.transactData
    [.add (.tmp "x") kEmail (.val (.str "ada@lovelace.io")),
     .add (.tmp "x") kName  (.val (.str "Ada Lovelace"))] 2000
    | IO.println "tx2 failed"
  IO.println s!"\ntx {r2.txId}: upsert via email — tempid \"x\" resolved to \
    entity {(r2.tempids.map (·.2)).head!}"
  IO.println "\n[:find ?e ?n :where [?e :person/name ?n]]"
  IO.println (showRows (r2.db.query qNames))

  -- Time travel: the world as of tx 1 still has the old name.
  IO.println s!"\nsame query, asOf tx {r1.txId} (proven frozen forever):"
  IO.println (showRows ((r2.db.asOf r1.txId).query qNames))

  IO.println "\n[:find ?n :where [?g :name \"Grace\"] [?g :friend ?f] [?f :name ?n]]"
  IO.println (showRows (r2.db.query (qFriendNames "Grace")))

  -- tx 3: retract Ada entirely — her facts and inbound refs vanish.
  let ada := (r2.tempids.map (·.2)).head!
  let .ok r3 := r2.db.transactData [.retractEntity (.id ada)] 3000
    | IO.println "tx3 failed"
  IO.println s!"\ntx {r3.txId}: retractEntity #{ada}"
  IO.println "\n[:find ?e ?n :where [?e :person/name ?n]]"
  IO.println (showRows (r3.db.query qNames))
  IO.println "\nGrace's friends now:"
  IO.println (showRows (r3.db.query (qFriendNames "Grace")))
  IO.println s!"\n...but asOf tx {r2.txId}, Ada is still there:"
  IO.println (showRows ((r3.db.asOf r2.txId).query qNames))

  -- Transactions are entities: query their instants like any fact.
  IO.println "\n[:find ?tx ?t :where [?tx :db/txInstant ?t]]"
  IO.println (showRows (r3.db.query
    ⟨["tx", "t"], [⟨.var "tx", .const (.keyword .txInstant), .var "t"⟩]⟩))
