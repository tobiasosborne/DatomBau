namespace DatomBau

inductive Cardinality
  | One
  | Many

-- Repr
instance : Repr Cardinality :=
  ⟨fun
    | .One, _  => Std.Format.text "One"
    | .Many, _ => Std.Format.text "Many"
  ⟩

instance : BEq Cardinality :=
  ⟨fun
    | .One, .One   => true
    | .Many, .Many => true
    | _, _         => false
  ⟩

instance : Inhabited Cardinality := ⟨.One⟩

structure AttributeSchema where
  name       : String
  type       : String       -- placeholder, could be refined later
  cardinality : Cardinality
  unique     : Bool
  deriving  BEq, Repr

structure Schema where
  attributes : List AttributeSchema
  deriving Repr

end DatomBau
