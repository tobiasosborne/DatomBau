import DatomBau.Index

/-!
# The Datalog core (Phase 4)

Data patterns over `(e, a, v)` with variables in any position, conjunctive
`:where`, and a `:find` projection. Everything is lifted to `Value`
(entities as `.ref`, attributes as `.keyword`), so a binding is one
uniform assoc list `String ↦ Value`.

Two evaluators share one engine (`evalOn`, the dumbest possible
left-to-right fold — its shape exists to make the completeness induction
go through):

- `Db.evalSpec` runs over the spec's `currentFacts`;
- `IndexedDb.evalIdx` runs off the EAVT index.

Flagships: `evalSpec_sound` (every returned binding matches every clause,
and binds exactly the query's variables), `evalSpec_complete` (every
matching binding is found, up to agreement on the query's variables — the
statement is over assoc lists precisely because function-valued bindings
would make this false), and the bridge `evalIdx_mem_iff` (index-backed
evaluation answers exactly what the spec answers). All performance work
belongs behind the bridge, never inside the completeness proof.
-/

namespace DatomBau

inductive Term where
  | var   (x : String)
  | const (v : Value)
  deriving DecidableEq, Repr

/-- A data pattern `[?e :attr ?v]`. -/
structure Clause where
  e : Term
  a : Term
  v : Term
  deriving DecidableEq, Repr

/-- Bindings are assoc lists; extension conses fresh variables only. -/
abbrev Binding := List (String × Value)

def Binding.lookup? : Binding → String → Option Value
  | [], _ => none
  | (y, v) :: σ, x => if y == x then some v else Binding.lookup? σ x

def Binding.binds (σ : Binding) (x : String) : Prop :=
  ∃ v, Binding.lookup? σ x = some v

/-- `τ` has everything `σ` has (and possibly more). -/
def Binding.Extends (τ σ : Binding) : Prop :=
  ∀ x v, Binding.lookup? σ x = some v → Binding.lookup? τ x = some v

theorem Binding.Extends.refl {σ : Binding} : σ.Extends σ := fun _ _ h => h

theorem Binding.Extends.trans {σ₁ σ₂ σ₃ : Binding}
    (h₂₁ : σ₂.Extends σ₁) (h₃₂ : σ₃.Extends σ₂) : σ₃.Extends σ₁ :=
  fun x v h => h₃₂ x v (h₂₁ x v h)

theorem Binding.lookup?_cons {x y : String} {v : Value} {σ : Binding} :
    Binding.lookup? ((y, v) :: σ) x =
      if y == x then some v else Binding.lookup? σ x := rfl

def Term.subst (σ : Binding) : Term → Option Value
  | .var x => Binding.lookup? σ x
  | .const v => some v

def Term.vars : Term → List String
  | .var x => [x]
  | .const _ => []

theorem Term.subst_mono {σ τ : Binding} {t : Term} {val : Value}
    (h : t.subst σ = some val) (hext : τ.Extends σ) : t.subst τ = some val := by
  cases t with
  | var x => exact hext x val h
  | const v => exact h

/-- Substitute a binding into a clause. `none` if a variable is unbound,
the entity slot is not a `ref`, or the attribute slot is not a keyword. -/
def Clause.subst (σ : Binding) (c : Clause) : Option Fact :=
  match c.e.subst σ, c.a.subst σ, c.v.subst σ with
  | some (.ref e), some (.keyword a), some vv => some ⟨e, a, vv⟩
  | _, _, _ => none

def Clause.vars (c : Clause) : List String := c.e.vars ++ c.a.vars ++ c.v.vars

theorem Clause.subst_mono {σ τ : Binding} {c : Clause} {f : Fact}
    (h : c.subst σ = some f) (hext : τ.Extends σ) : c.subst τ = some f := by
  simp only [Clause.subst] at h ⊢
  split at h
  next e a vv he ha hv =>
    cases h
    rw [Term.subst_mono he hext, Term.subst_mono ha hext,
      Term.subst_mono hv hext]
  next => exact absurd h (by simp)

/-- `σ` satisfies every clause against `db`. -/
def Matches (db : Db) (cs : List Clause) (σ : Binding) : Prop :=
  ∀ c ∈ cs, ∃ f, Clause.subst σ c = some f ∧ f ∈ db

/-! ## The engine -/

/-- Unify one term with one value, extending the binding if the term is an
unbound variable. -/
def Term.unify (σ : Binding) (t : Term) (val : Value) : Option Binding :=
  match t with
  | .const v => if v == val then some σ else none
  | .var x =>
    match Binding.lookup? σ x with
    | some v => if v == val then some σ else none
    | none => some ((x, val) :: σ)

def Clause.unify (c : Clause) (f : Fact) (σ : Binding) : Option Binding :=
  match Term.unify σ c.e (.ref f.e) with
  | some σ₁ =>
    match Term.unify σ₁ c.a (.keyword f.a) with
    | some σ₂ => Term.unify σ₂ c.v f.v
    | none => none
  | none => none

def evalClauseOn (facts : List Fact) (c : Clause) (σ : Binding) :
    List Binding :=
  facts.filterMap fun f => c.unify f σ

/-- Left-to-right fold over clauses; deliberately naive. -/
def evalOn (facts : List Fact) : List Clause → List Binding → List Binding
  | [], σs => σs
  | c :: cs, σs => evalOn facts cs (σs.flatMap fun σ => evalClauseOn facts c σ)

/-- Reference evaluator over the spec. -/
def Db.evalSpec (db : Db) (cs : List Clause) : List Binding :=
  evalOn db.currentFacts cs [[]]

/-- Index-backed evaluator: the fact source is the EAVT index. -/
def IndexedDb.evalIdx (idb : IndexedDb) (cs : List Clause) : List Binding :=
  evalOn (idb.eavt.toList.map (·.toFact)) cs [[]]

structure Query where
  find : List String
  wher : List Clause
  deriving Repr

/-- Rows: project each binding onto the `find` variables. -/
def Db.query (db : Db) (q : Query) : List (List Value) :=
  (db.evalSpec q.wher).filterMap fun σ => q.find.mapM (Binding.lookup? σ)

def IndexedDb.query (idb : IndexedDb) (q : Query) : List (List Value) :=
  (idb.evalIdx q.wher).filterMap fun σ => q.find.mapM (Binding.lookup? σ)

/-! ## Unification lemmas -/

theorem Term.unify_sound {σ σ' : Binding} {t : Term} {val : Value}
    (h : Term.unify σ t val = some σ') :
    σ'.Extends σ ∧ t.subst σ' = some val ∧
      (∀ x, σ'.binds x ↔ σ.binds x ∨ x ∈ t.vars) := by
  cases t with
  | const v =>
    simp only [Term.unify] at h
    split at h
    next hv =>
      cases h
      have hveq : v = val := by simpa using hv
      subst hveq
      exact ⟨Binding.Extends.refl, rfl, fun x => by simp [Term.vars]⟩
    next => exact absurd h (by simp)
  | var x =>
    simp only [Term.unify] at h
    split at h
    next v hl =>
      split at h
      next hv =>
        cases h
        have hveq : v = val := by simpa using hv
        subst hveq
        refine ⟨Binding.Extends.refl, hl, fun y => ?_⟩
        constructor
        · exact fun hb => Or.inl hb
        · rintro (hb | hy)
          · exact hb
          · simp [Term.vars] at hy
            subst hy
            exact ⟨v, hl⟩
      next => exact absurd h (by simp)
    next hl =>
      cases h
      refine ⟨?_, ?_, fun y => ?_⟩
      · intro y w hw
        rw [Binding.lookup?_cons]
        split
        next hxy =>
          exfalso
          have hxy' : x = y := by simpa using hxy
          subst hxy'
          rw [hl] at hw
          simp at hw
        next => exact hw
      · show Binding.lookup? ((x, val) :: σ) x = some val
        rw [Binding.lookup?_cons]
        simp
      · rw [Term.vars]
        constructor
        · rintro ⟨w, hw⟩
          rw [Binding.lookup?_cons] at hw
          split at hw
          next hxy =>
            have hxy' : x = y := by simpa using hxy
            exact Or.inr (by simp [hxy'])
          next => exact Or.inl ⟨w, hw⟩
        · rintro (⟨w, hw⟩ | hy)
          · refine ⟨w, ?_⟩
            rw [Binding.lookup?_cons]
            split
            next hxy =>
              exfalso
              have hxy' : x = y := by simpa using hxy
              subst hxy'
              rw [hl] at hw
              simp at hw
            next => exact hw
          · simp at hy
            subst hy
            exact ⟨val, by rw [Binding.lookup?_cons]; simp⟩

theorem Term.unify_complete {σ τ : Binding} {t : Term} {val : Value}
    (hext : τ.Extends σ) (ht : t.subst τ = some val) :
    ∃ σ', Term.unify σ t val = some σ' ∧ τ.Extends σ' := by
  cases t with
  | const v =>
    have hv : v = val := by simpa [Term.subst] using ht
    subst hv
    exact ⟨σ, by simp [Term.unify], hext⟩
  | var x =>
    have hτ : Binding.lookup? τ x = some val := ht
    cases hl : Binding.lookup? σ x with
    | some v =>
      have hveq : v = val := by
        have h2 := hext x v hl
        rw [hτ] at h2
        exact (Option.some.inj h2).symm
      subst hveq
      exact ⟨σ, by simp [Term.unify, hl], hext⟩
    | none =>
      refine ⟨(x, val) :: σ, by simp [Term.unify, hl], ?_⟩
      intro y w hw
      rw [Binding.lookup?_cons] at hw
      split at hw
      next hxy =>
        have hxy' : x = y := by simpa using hxy
        subst hxy'
        cases hw
        exact hτ
      next => exact hext y w hw

theorem Clause.unify_sound {c : Clause} {f : Fact} {σ σ' : Binding}
    (h : c.unify f σ = some σ') :
    σ'.Extends σ ∧ c.subst σ' = some f ∧
      (∀ x, σ'.binds x ↔ σ.binds x ∨ x ∈ c.vars) := by
  simp only [Clause.unify] at h
  split at h
  next σ₁ h₁ =>
    split at h
    next σ₂ h₂ =>
      obtain ⟨he₁, hs₁, hd₁⟩ := Term.unify_sound h₁
      obtain ⟨he₂, hs₂, hd₂⟩ := Term.unify_sound h₂
      obtain ⟨he₃, hs₃, hd₃⟩ := Term.unify_sound h
      refine ⟨(he₁.trans he₂).trans he₃, ?_, fun x => ?_⟩
      · simp only [Clause.subst]
        rw [Term.subst_mono hs₁ (he₂.trans he₃), Term.subst_mono hs₂ he₃, hs₃]
      · rw [hd₃, hd₂, hd₁]
        unfold Clause.vars
        simp [or_assoc]
    next => exact absurd h (by simp)
  next => exact absurd h (by simp)

theorem Clause.unify_complete {c : Clause} {f : Fact} {σ τ : Binding}
    (hext : τ.Extends σ) (hsub : c.subst τ = some f) :
    ∃ σ', c.unify f σ = some σ' ∧ τ.Extends σ' := by
  simp only [Clause.subst] at hsub
  split at hsub
  next e a vv he ha hv =>
    cases hsub
    obtain ⟨σ₁, hu₁, hτ₁⟩ := Term.unify_complete hext he
    obtain ⟨σ₂, hu₂, hτ₂⟩ := Term.unify_complete hτ₁ ha
    obtain ⟨σ₃, hu₃, hτ₃⟩ := Term.unify_complete hτ₂ hv
    exact ⟨σ₃, by simp [Clause.unify, hu₁, hu₂, hu₃], hτ₃⟩
  next => exact absurd hsub (by simp)

/-! ## Engine lemmas -/

theorem evalOn_sound {facts : List Fact} {cs : List Clause}
    {σs : List Binding} {σ' : Binding}
    (h : σ' ∈ evalOn facts cs σs) :
    ∃ σ ∈ σs, σ'.Extends σ ∧
      (∀ c ∈ cs, ∃ f, Clause.subst σ' c = some f ∧ f ∈ facts) ∧
      (∀ x, σ'.binds x ↔ σ.binds x ∨ x ∈ cs.flatMap Clause.vars) := by
  induction cs generalizing σs with
  | nil =>
    exact ⟨σ', by simpa [evalOn] using h, Binding.Extends.refl,
      by simp, fun x => by simp⟩
  | cons c cs ih =>
    unfold evalOn at h
    obtain ⟨σ₀, hσ₀, hext, hsat, hdom⟩ := ih h
    obtain ⟨σᵢ, hσᵢ, hσ₀'⟩ := List.mem_flatMap.mp hσ₀
    obtain ⟨f, hf, hu⟩ := List.mem_filterMap.mp hσ₀'
    obtain ⟨hex₀, hsub₀, hdom₀⟩ := Clause.unify_sound hu
    refine ⟨σᵢ, hσᵢ, hex₀.trans hext, ?_, fun x => ?_⟩
    · intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨f, Clause.subst_mono hsub₀ hext, hf⟩
      · exact hsat c' hc'
    · rw [hdom x, hdom₀ x]
      simp [or_assoc]

theorem evalOn_complete {facts : List Fact} {cs : List Clause} {τ : Binding}
    (hm : ∀ c ∈ cs, ∃ f, Clause.subst τ c = some f ∧ f ∈ facts) :
    ∀ σs (σ : Binding), σ ∈ σs → τ.Extends σ →
      ∃ σ' ∈ evalOn facts cs σs, τ.Extends σ' ∧
        (∀ x, σ.binds x ∨ x ∈ cs.flatMap Clause.vars → σ'.binds x) := by
  induction cs with
  | nil =>
    intro σs σ hσ hτσ
    refine ⟨σ, by simpa [evalOn] using hσ, hτσ, fun x hx => ?_⟩
    simpa using hx.resolve_right (by simp)
  | cons c cs ih =>
    intro σs σ hσ hτσ
    obtain ⟨f, hsub, hf⟩ := hm c (List.mem_cons_self ..)
    obtain ⟨σ₁, hu, hτσ₁⟩ := Clause.unify_complete hτσ hsub
    obtain ⟨hex₁, -, hdom₁⟩ := Clause.unify_sound hu
    have hσ₁ : σ₁ ∈ σs.flatMap fun σ => evalClauseOn facts c σ :=
      List.mem_flatMap.mpr ⟨σ, hσ, List.mem_filterMap.mpr ⟨f, hf, hu⟩⟩
    have hm' : ∀ c' ∈ cs, ∃ f, Clause.subst τ c' = some f ∧ f ∈ facts :=
      fun c' hc' => hm c' (List.mem_cons_of_mem _ hc')
    obtain ⟨σ', hσ', hτσ', hcov⟩ := ih hm' _ σ₁ hσ₁ hτσ₁
    refine ⟨σ', by simpa [evalOn] using hσ', hτσ', fun x hx => ?_⟩
    rcases hx with hb | hv
    · exact hcov x (Or.inl ((hdom₁ x).mpr (Or.inl hb)))
    · simp only [List.flatMap_cons, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hcov x (Or.inl ((hdom₁ x).mpr (Or.inr hv)))
      · exact hcov x (Or.inr hv)

/-! ## Flagships -/

/-- **Soundness**: every returned binding matches every clause, and binds
exactly the query's variables. -/
theorem Db.evalSpec_sound {db : Db} {cs : List Clause} {σ : Binding}
    (h : σ ∈ db.evalSpec cs) :
    Matches db cs σ ∧ (∀ x, σ.binds x ↔ x ∈ cs.flatMap Clause.vars) := by
  obtain ⟨σ₀, hσ₀, hext, hsat, hdom⟩ := evalOn_sound h
  have hσ₀' : σ₀ = [] := by simpa using hσ₀
  subst hσ₀'
  refine ⟨fun c hc => ?_, fun x => ?_⟩
  · obtain ⟨f, hs, hf⟩ := hsat c hc
    exact ⟨f, hs, Db.mem_currentFacts_iff.mp hf⟩
  · rw [hdom x]
    simp [Binding.binds, Binding.lookup?]

/-- **Completeness**: every binding that matches all clauses is found, up
to agreement on the query's variables. -/
theorem Db.evalSpec_complete {db : Db} {cs : List Clause} {τ : Binding}
    (hm : Matches db cs τ) :
    ∃ σ ∈ db.evalSpec cs,
      ∀ x ∈ cs.flatMap Clause.vars,
        Binding.lookup? σ x = Binding.lookup? τ x := by
  have hm' : ∀ c ∈ cs, ∃ f, Clause.subst τ c = some f ∧ f ∈ db.currentFacts :=
    fun c hc => by
      obtain ⟨f, hs, hf⟩ := hm c hc
      exact ⟨f, hs, Db.mem_currentFacts_iff.mpr hf⟩
  obtain ⟨σ', hσ', hτσ', hcov⟩ :=
    evalOn_complete hm' [[]] [] (by simp)
      (fun x v h => by simp [Binding.lookup?] at h)
  refine ⟨σ', hσ', fun x hx => ?_⟩
  obtain ⟨v, hv⟩ := hcov x (Or.inr hx)
  rw [hv, hτσ' x v hv]

/-- Evaluation only depends on the fact source's membership. -/
theorem evalOn_mem_congr {fs₁ fs₂ : List Fact}
    (hf : ∀ f, f ∈ fs₁ ↔ f ∈ fs₂) :
    ∀ (cs : List Clause) (σs₁ σs₂ : List Binding),
      (∀ σ, σ ∈ σs₁ ↔ σ ∈ σs₂) →
      ∀ σ, (σ ∈ evalOn fs₁ cs σs₁ ↔ σ ∈ evalOn fs₂ cs σs₂) := by
  intro cs
  induction cs with
  | nil => intro σs₁ σs₂ hσs σ; simpa [evalOn] using hσs σ
  | cons c cs ih =>
    intro σs₁ σs₂ hσs σ
    unfold evalOn
    apply ih
    intro σ'
    rw [List.mem_flatMap, List.mem_flatMap]
    constructor
    · rintro ⟨σ₀, hσ₀, hσ'⟩
      obtain ⟨f, hf', hu⟩ := List.mem_filterMap.mp hσ'
      exact ⟨σ₀, (hσs σ₀).mp hσ₀,
        List.mem_filterMap.mpr ⟨f, (hf f).mp hf', hu⟩⟩
    · rintro ⟨σ₀, hσ₀, hσ'⟩
      obtain ⟨f, hf', hu⟩ := List.mem_filterMap.mp hσ'
      exact ⟨σ₀, (hσs σ₀).mpr hσ₀,
        List.mem_filterMap.mpr ⟨f, (hf f).mpr hf', hu⟩⟩

theorem IndexedDb.mem_factsIdx {idb : IndexedDb} (h : idb.WF) {f : Fact} :
    f ∈ idb.eavt.toList.map (·.toFact) ↔ f ∈ idb.db.currentFacts := by
  rw [List.mem_map, Db.mem_currentFacts_iff, Db.mem_iff_lastWrite]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.tx, (h.eavt_coh x).mp (Std.TreeSet.mem_toList.mp hx)⟩
  · rintro ⟨tx, hlw⟩
    exact ⟨⟨f, tx⟩, Std.TreeSet.mem_toList.mpr ((h.eavt_coh ⟨f, tx⟩).mpr hlw),
      rfl⟩

/-- **The bridge**: index-backed evaluation answers exactly what the spec
answers. Performance work goes here, never into the completeness proof. -/
theorem IndexedDb.evalIdx_mem_iff {idb : IndexedDb} (h : idb.WF)
    {cs : List Clause} {σ : Binding} :
    σ ∈ idb.evalIdx cs ↔ σ ∈ idb.db.evalSpec cs :=
  evalOn_mem_congr (fun _ => IndexedDb.mem_factsIdx h) cs [[]] [[]]
    (fun _ => Iff.rfl) σ

/-! ## The headline: the database is a value

Queries against `asOf` views are frozen for all time — transacting never
changes the answer of any query against any past basis. That these are
one-line `rw`s is the point: the whole design (value-equality asOf
theorems, spec-first evaluation, the index bridge) was chosen to make
them so. -/

theorem Db.query_asOf_stable {db db' : Db} {ops : List TxOp} {now t : Nat}
    (h : db.transact ops now = .ok db') (ht : t ≤ db.maxTx) (q : Query) :
    (db'.asOf t).query q = (db.asOf t).query q := by
  rw [Db.asOf_transact h ht]

/-- The same, through the full transactor with tempids and upsert. -/
theorem Db.query_asOf_stable_data {db : Db} {forms : List TxForm}
    {now t : Nat} {r : TxReport}
    (h : db.transactData forms now = .ok r) (ht : t ≤ db.maxTx) (q : Query) :
    (r.db.asOf t).query q = (db.asOf t).query q := by
  rw [Db.asOf_transactData h ht]

/-- And through the index-backed engine. -/
theorem IndexedDb.query_asOf_stable {db : Db} {forms : List TxForm}
    {now t : Nat} {r : TxReport}
    (h : db.transactData forms now = .ok r) (ht : t ≤ db.maxTx) (q : Query) :
    (IndexedDb.ofDb (r.db.asOf t)).query q =
      (IndexedDb.ofDb (db.asOf t)).query q := by
  rw [Db.asOf_transactData h ht]

/-! ## Executable sanity checks -/

private def kname : Keyword := ⟨some "person", "name"⟩
private def kfriend : Keyword := ⟨some "person", "friend"⟩

private def qSchema : Schema := .ofList
  [(kname, { valueType := .str }),
   (kfriend, { valueType := .ref, cardinality := .many })]

private def qdb : Db :=
  (((Db.empty qSchema).transactData
    [.add (.tmp "a") kname (.val (.str "Ada")),
     .add (.tmp "g") kname (.val (.str "Grace")),
     .add (.tmp "g") kfriend (.tmp "a")] 100).toOption.map (·.db)).getD
    (Db.empty qSchema)

-- Who is named Ada?  [:find ?e :where [?e :person/name "Ada"]]
#guard qdb.query ⟨["e"], [⟨.var "e", .const (.keyword kname), .const (.str "Ada")⟩]⟩
  == [[.ref 1]]

-- Join: names of Grace's friends.
-- [:find ?n :where [?g :name "Grace"] [?g :friend ?f] [?f :name ?n]]
#guard qdb.query ⟨["n"],
  [⟨.var "g", .const (.keyword kname), .const (.str "Grace")⟩,
   ⟨.var "g", .const (.keyword kfriend), .var "f"⟩,
   ⟨.var "f", .const (.keyword kname), .var "n"⟩]⟩
  == [[.str "Ada"]]

-- All (entity, name) pairs; spec and index engines agree.
private def qAll : Query :=
  ⟨["e", "n"], [⟨.var "e", .const (.keyword kname), .var "n"⟩]⟩

#guard qdb.query qAll == [[.ref 1, .str "Ada"], [.ref 2, .str "Grace"]]
#guard ((IndexedDb.ofDb qdb).query qAll).length == 2
#guard ((IndexedDb.ofDb qdb).query qAll).all (qdb.query qAll).contains

end DatomBau
