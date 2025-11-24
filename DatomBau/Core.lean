namespace DatomBau

def hello := "world"

-- A Datom: atomic fact
structure Datom where
  entity : Nat        -- entity ID
  attr : String     -- attribute name
  value    : String     -- value (could later be polymorphic)
  deriving Inhabited, BEq, Repr

-- Transaction ID
abbrev TxId := Nat

-- Datom log entry: associates a datom with a transaction
structure LogEntry where
  datom : Datom
  tx    : TxId
  added : Bool  -- true = addition, false = retraction
  deriving Inhabited, BEq, Repr

end DatomBau
