import Lean
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/- Stream exact payload DAG nodes. Pointer cache is safe only because the imported
environment and all cached native ModuleData/CompactedRegions stay live until export ends.
Never use ordinary BEq Expr, which is alpha equivalence. -/
structure CmpDag where
  seen : Std.HashMap USize Nat := {}
  next : Nat := 0

def emitCmp (j : Json) : IO Unit := IO.println ("FL_CMP " ++ j.compress)

unsafe def cmpExpr (e : Expr) : StateT CmpDag IO Nat := do
  let key := ptrAddrUnsafe e
  if let some id := (← get).seen[key]? then return id
  let (payload,children) ← match e with
    | .bvar i => pure (#[toJson "bvar",toJson i], #[])
    | .fvar i => pure (#[toJson "fvar",toJson (reprStr i.name)], #[])
    | .mvar i => pure (#[toJson "mvar",toJson (reprStr i.name)], #[])
    | .sort l => pure (#[toJson "sort",toJson (reprStr l)], #[])
    | .const n ls => pure (#[toJson "const",toJson (reprStr n),toJson (ls.map reprStr)], #[])
    | .app f a => do
      let f ← cmpExpr f; let a ← cmpExpr a
      pure (#[toJson "app"], #[f,a])
    | .lam n t b bi => do
      let t ← cmpExpr t; let b ← cmpExpr b
      pure (#[toJson "lam",toJson (reprStr n),toJson (reprStr bi)], #[t,b])
    | .forallE n t b bi => do
      let t ← cmpExpr t; let b ← cmpExpr b
      pure (#[toJson "forallE",toJson (reprStr n),toJson (reprStr bi)], #[t,b])
    | .letE n t v b nd => do
      let t ← cmpExpr t; let v ← cmpExpr v; let b ← cmpExpr b
      pure (#[toJson "letE",toJson (reprStr n),toJson nd], #[t,v,b])
    | .lit l => pure (#[toJson "lit",toJson (reprStr l)], #[])
    | .mdata md b => do
      let b ← cmpExpr b
      pure (#[toJson "mdata",toJson (reprStr md)], #[b])
    | .proj n i b => do
      let b ← cmpExpr b
      pure (#[toJson "proj",toJson (reprStr n),toJson i], #[b])
  let id := (← get).next
  modify fun s => { seen := s.seen.insert key id, next := id+1 }
  liftM <| emitCmp <| Json.mkObj [("event",toJson "node"),("id",toJson id),
    ("payload",toJson payload),("children",toJson children)]
  return id

-- All nonexpression ConstantInfo fields; ordered names/universes remain literal.
def cmpNative (c : ConstantInfo) : Json :=
  match c with
  | .axiomInfo v => Json.mkObj [("isUnsafe",toJson v.isUnsafe)]
  | .defnInfo v =>
    let hints := match v.hints with
      | .opaque => Json.arr #[toJson "opaque"]
      | .abbrev => Json.arr #[toJson "abbrev"]
      | .regular h => Json.arr #[toJson "regular",toJson h.toNat]
    Json.mkObj [("hints",hints),("safety",toJson (reprStr v.safety)),("all",toJson (v.all.map reprStr))]
  | .thmInfo v => Json.mkObj [("all",toJson (v.all.map reprStr))]
  | .opaqueInfo v => Json.mkObj [("isUnsafe",toJson v.isUnsafe),("all",toJson (v.all.map reprStr))]
  | .inductInfo v => Json.mkObj [("numParams",toJson v.numParams),("numIndices",toJson v.numIndices),
      ("all",toJson (v.all.map reprStr)),("ctors",toJson (v.ctors.map reprStr)),("numNested",toJson v.numNested),
      ("isRec",toJson v.isRec),("isUnsafe",toJson v.isUnsafe),("isReflexive",toJson v.isReflexive)]
  | .ctorInfo v => Json.mkObj [("induct",toJson (reprStr v.induct)),("cidx",toJson v.cidx),
      ("numParams",toJson v.numParams),("numFields",toJson v.numFields),("isUnsafe",toJson v.isUnsafe)]
  | .recInfo v => Json.mkObj [("all",toJson (v.all.map reprStr)),("numParams",toJson v.numParams),
      ("numIndices",toJson v.numIndices),("numMotives",toJson v.numMotives),("numMinors",toJson v.numMinors),
      ("k",toJson v.k),("isUnsafe",toJson v.isUnsafe),
      ("rules",toJson (v.rules.map (fun r => Json.arr #[toJson (reprStr r.ctor),toJson r.nfields])))]
  | .quotInfo v => Json.mkObj [("kind",toJson (match v.kind with
      | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"))]

def cmpKind (c : ConstantInfo) : String := match c with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quotient"

-- Full explicit predicate from the accepted native-payload comparator.
unsafe def cmpEqual (a b : Expr) : StateT (Std.HashSet (USize × USize)) IO Bool := do
  if ptrAddrUnsafe a == ptrAddrUnsafe b then return true
  let key := (ptrAddrUnsafe a,ptrAddrUnsafe b)
  if (← get).contains key then return true
  modify (·.insert key)
  match a,b with
  | .bvar x,.bvar y => return x==y
  | .fvar x,.fvar y => return x.name==y.name
  | .mvar x,.mvar y => return x.name==y.name
  | .sort x,.sort y => return reprStr x==reprStr y
  | .const x u,.const y v => return x==y && reprStr u==reprStr v
  | .lit x,.lit y => return x==y
  | .app f x,.app g y => return (← cmpEqual f g) && (← cmpEqual x y)
  | .lam n t b i,.lam n' t' b' i'
  | .forallE n t b i,.forallE n' t' b' i' =>
    return n==n' && i==i' && (← cmpEqual t t') && (← cmpEqual b b')
  | .letE n t v b f,.letE n' t' v' b' f' =>
    return n==n' && f==f' && (← cmpEqual t t') && (← cmpEqual v v') && (← cmpEqual b b')
  | .mdata m b,.mdata m' b' => return reprStr m==reprStr m' && (← cmpEqual b b')
  | .proj n i b,.proj n' i' b' => return n==n' && i==i' && (← cmpEqual b b')
  | _,_ => return false

unsafe def cmpNativeEqual (a b : ConstantInfo) : IO Bool := do
  if cmpKind a != cmpKind b || a.name != b.name || a.levelParams != b.levelParams ||
      (cmpNative a).compress != (cmpNative b).compress then return false
  if !(← (cmpEqual a.type b.type).run' {}) then return false
  match a.value? true,b.value? true with
  | some v,some w => if !(← (cmpEqual v w).run' {}) then return false
  | none,none => pure ()
  | _,_ => return false
  match a,b with
  | .recInfo x,.recInfo y =>
    for (r,s) in x.rules.zip y.rules do
      if !(← (cmpEqual r.rhs s.rhs).run' {}) then return false
  | _,_ => pure ()
  return true

structure CmpStorage where
  regions : NameMap (Array (ModuleData × CompactedRegion)) := {}
  byOwner : NameMap (NameMap (Array ConstantInfo)) := {}

def loadCmpStorage (owner : Name) (cache : CmpStorage) : IO CmpStorage := do
  if cache.byOwner.contains owner then return cache
  let obj ← findOLean owner
  let main ← readModuleData obj
  let data ← if main.1.isModule then
    readModuleDataParts #[obj,OLeanLevel.server.adjustFileName obj,OLeanLevel.private.adjustFileName obj]
    else pure #[main]
  let mut index : NameMap (Array ConstantInfo) := {}
  for (md,_) in data do
    for c in md.constants do index := index.insert c.name ((index.find? c.name).getD #[] |>.push c)
  return { regions := cache.regions.insert owner data, byOwner := cache.byOwner.insert owner index }

def cmpStage (stage : String) (count total : Nat) (last : String := "") : IO Unit := do
  let err ← IO.getStderr
  err.putStrLn <| "FL_CMP_PROGRESS " ++ (Json.mkObj [("stage",toJson stage),("processed",toJson count),
    ("total",toJson total),("last",toJson last)]).compress
  err.flush

unsafe def exportComparator (configPath : String) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile configPath)
  let moduleStrings ← IO.ofExcept <| config.getObjValAs? (Array String) "modules"
  let roots ← IO.ofExcept <| config.getObjValAs? (Array String) "roots"
  let overrides ← IO.ofExcept <| config.getObjValAs? (Array (String × String)) "storage_overrides"
  let wanted : Std.HashSet String := moduleStrings.foldl (fun s n => s.insert n) {}
  let storageOverrides : Std.HashMap String String := overrides.foldl (fun s (n,m) => s.insert n m) {}
  -- Build the owner candidate index once; never enumerate all modules per declaration.
  let mut ownerIndex : NameMap (Array Name) := {}
  for i in [:env.header.moduleNames.size] do
    for n in env.header.moduleData[i]!.constNames do
      ownerIndex := ownerIndex.insert n ((ownerIndex.find? n).getD #[] |>.push env.header.moduleNames[i]!)
  let projectConstants := env.constants.toList.filter fun (n,_) =>
    (env.getModuleIdxFor? n).any fun i => wanted.contains env.header.moduleNames[i.toNat]!.toString
  let total := projectConstants.length
  liftIO <| cmpStage "owner-index-ready" 0 total
  let mut storage : CmpStorage := {}
  let mut dag : CmpDag := {}
  let mut seen : Std.HashSet Name := {}
  let mut foundRoots : Std.HashSet String := {}
  let mut count := 0
  for nominal in env.header.moduleNames do
    let obj ← findOLean nominal
    let isProject := wanted.contains nominal.toString
    liftIO <| emitCmp <| Json.mkObj [("event",toJson "module"),("module",toJson nominal.toString),
      ("object",toJson obj.toString),("project",toJson isProject)]
    if !isProject then continue
    liftIO <| cmpStage "native-module" count total nominal.toString
    storage ← liftIO <| loadCmpStorage nominal storage
    let parts := (storage.regions.find? nominal).getD #[]
    let mut nativeNames : Std.HashSet Name := {}
    for (md,_) in parts do
      for stored in md.constants do
        let n := stored.name
        let some idx := env.getModuleIdxFor? n | throwError "No compiler owner: {n}"
        if env.header.moduleNames[idx.toNat]! != nominal then
          liftIO <| emitCmp <| Json.mkObj [("event",toJson "export_alias"),("name",toJson n.toString),
            ("module",toJson nominal.toString),("nominal_owner",toJson env.header.moduleNames[idx.toNat]!.toString)]
          continue
        if nativeNames.contains n then throwError "Duplicate native record: {n} in {nominal}"
        nativeNames := nativeNames.insert n
        if seen.contains n then throwError "Duplicate ambiguous owner: {n}"
        seen := seen.insert n
        let some active := env.find? n | throwError "Imported environment missing native declaration: {n}"
        let mut actualOwner := nominal
        let mut actual := stored
        if let some donor := storageOverrides[n.toString]? then
          actualOwner := donor.toName
          storage ← liftIO <| loadCmpStorage actualOwner storage
          let candidates := ((storage.byOwner.find? actualOwner).getD {}).find? n |>.getD #[]
          if candidates.size != 1 then throwError "Ambiguous storage override: {n} in {actualOwner}"
          actual := candidates[0]!
        else if !(← liftIO <| cmpNativeEqual active actual) then
          -- Nominal owner tables can point to an earlier counterpart after a
          -- filename alias reexports the same kernel Name. Locate actual storage
          -- only by an exact complete payload match, never by Name normalization.
          let mut candidates : Array (Name × ConstantInfo) := #[]
          liftIO <| cmpStage "resolve-exact-storage" count total n.toString
          for owner in (ownerIndex.find? n).getD #[] do
            storage ← liftIO <| loadCmpStorage owner storage
            let nativeCandidates := ((storage.byOwner.find? owner).getD {}).find? n |>.getD #[]
            for ci in nativeCandidates do
              if (← liftIO <| cmpNativeEqual active ci) then candidates := candidates.push (owner,ci)
          if candidates.size != 1 then
            throwError "Ambiguous actual storage: {n}; nominal={nominal}; exact candidates={candidates.map (fun x => x.1)}"
          actualOwner := candidates[0]!.1
          actual := candidates[0]!.2
        unless (← liftIO <| cmpNativeEqual active actual) do
          throwError "Active/native payload differs: {n}; nominal={nominal}; actual={actualOwner}. Explicit reviewed storage override required."
        if count % 100 == 0 then liftIO <| cmpStage "serialize-constant" count total n.toString
        let c := actual
        if c.type.hasSorry || (c.value? true).any Expr.hasSorry then throwError "Placeholder: {n}"
        let (typeId,state) ← liftIO <| (cmpExpr c.type).run dag
        dag := state
        let mut valueId : Option Nat := none
        if let some v := c.value? true then
          let (id,state) ← liftIO <| (cmpExpr v).run dag
          dag := state; valueId := some id
        let mut rules : Array Nat := #[]
        let mut deps := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
        match c with
        | .defnInfo d => deps := deps ++ d.all.toArray
        | .thmInfo d => deps := deps ++ d.all.toArray
        | .opaqueInfo d => deps := deps ++ d.all.toArray
        | .inductInfo d => deps := deps ++ d.all.toArray ++ d.ctors.toArray
        | .ctorInfo d => deps := deps.push d.induct
        | .recInfo r =>
          deps := deps ++ r.all.toArray
          for rule in r.rules do
            if rule.rhs.hasSorry then throwError "Placeholder recursor: {n}"
            let (id,state) ← liftIO <| (cmpExpr rule.rhs).run dag
            dag := state; rules := rules.push id
            deps := deps.push rule.ctor ++ rule.rhs.getUsedConstants
        | _ => pure ()
        let proofValued ← liftTermElabM <| Meta.isProp c.type
        let mut structureInfo : Json := Json.null
        if let some si := getStructureInfo? env n then
          let mut fields : Array Json := #[]
          for f in si.fieldInfo do
            deps := deps.push f.projFn
            if let some sub := f.subobject? then deps := deps.push sub
            let mut ap : Option Nat := none
            if let some e := f.autoParam? then
              deps := deps ++ e.getUsedConstants
              let (id,state) ← liftIO <| (cmpExpr e).run dag
              dag := state; ap := some id
            fields := fields.push <| Json.mkObj [("field",toJson (reprStr f.fieldName)),
              ("projection",toJson (reprStr f.projFn)),("subobject",toJson (f.subobject?.map reprStr)),
              ("binderInfo",toJson (reprStr f.binderInfo)),("autoParam",toJson ap)]
          structureInfo := Json.mkObj [("fields",toJson fields),("ordered_field_names",toJson (si.fieldNames.map reprStr)),
            ("parents",toJson (si.parentInfo.map (fun p => Json.arr #[toJson (reprStr p.structName),toJson p.subobject,toJson (reprStr p.projFn)])))]
          for p in si.parentInfo do deps := deps.push p.structName |>.push p.projFn
        let projection := (env.getProjectionFnInfo? n).map fun p => Json.mkObj [
          ("ctor",toJson (reprStr p.ctorName)),("numParams",toJson p.numParams),("i",toJson p.i),("fromClass",toJson p.fromClass)]
        if let some p := env.getProjectionFnInfo? n then deps := deps.push p.ctorName
        for d in deps do
          unless env.contains d do throwError "Missing retained dependency: {n} -> {d}"
        let instances := instanceExtension.getState env
        let inst := instances.instanceNames.find? n
        let inst := inst.map fun e => Json.mkObj [("value",toJson (reprStr e.val)),("keys",toJson (reprStr e.keys)),
          ("priority",toJson e.priority),("synthOrder",toJson e.synthOrder),("attrKind",toJson (toString e.attrKind)),
          ("globalName",toJson (e.globalName?.map reprStr))]
        let axioms ← withEnv env <| collectAxioms n
        let isRoot := roots.contains n.toString
        if isRoot then foundRoots := foundRoots.insert n.toString
        liftIO <| emitCmp <| Json.mkObj [("event",toJson "constant"),("name",toJson n.toString),
          ("raw_name",toJson (reprStr n)),("nominal_owner",toJson nominal.toString),("storage_owner",toJson actualOwner.toString),
          ("kind",toJson (cmpKind c)),("ordered_universes",toJson (c.levelParams.map reprStr)),
          ("type",toJson typeId),("value",toJson valueId),("recursor_rhs",toJson rules),
          ("native",cmpNative c),("structure",structureInfo),("projection",toJson projection),("instance",toJson inst),
          ("proof_valued",toJson proofValued),("dependencies",toJson (deps.map Name.toString)),
          ("axioms",toJson (axioms.map Name.toString)),("root",toJson isRoot)]
        count := count+1
  for root in roots do
    unless foundRoots.contains root do throwError "Missing root: {root}"
  for (n,_) in projectConstants do
    if let some idx := env.getModuleIdxFor? n then
      if wanted.contains env.header.moduleNames[idx.toNat]!.toString && !seen.contains n then
        throwError "Imported project constant missing native census: {n}"
  liftIO <| cmpStage "complete" count total
  liftIO <| emitCmp <| Json.mkObj [("event",toJson "complete"),("constants",toJson count),("nodes",toJson dag.next)]
