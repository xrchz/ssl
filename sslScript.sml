open HolKernel bossLib boolLib boolSimps Parse lcsymtacs stringTheory intLib finite_mapTheory sortingTheory listTheory ParseExtras

val _ = new_theory"ssl"

val _ = tight_equality()

val _ = type_abbrev("name",``:string``)

val _ = type_abbrev("relpath",``:name list``)

val _ = type_abbrev("inode", ``:num``)
val _ = type_abbrev("ofaddr", ``:num``)
val _ = type_abbrev("dirstream", ``:num``)
val _ = type_abbrev("address", ``:num``)
val _ = type_abbrev("var", ``:num``)
val _ = type_abbrev("num", ``:num``)

val _ = Hol_datatype `path =
    EmptyPath
  | AbsPath of relpath
  | RelPath of name => relpath`

val _ = overload_on("NamePath",``λn. RelPath n []``)
val _ = overload_on("RootPath",``AbsPath []``)

val path_concat_def = Define`
  (path_concat EmptyPath p = SOME p) ∧
  (path_concat p EmptyPath = SOME p) ∧
  (path_concat (AbsPath p1) (RelPath h2 p2) = SOME (AbsPath (p1 ++ (h2::p2)))) ∧
  (path_concat (RelPath h1 p1) (RelPath h2 p2) = SOME (RelPath h1 (p1 ++ (h2::p2)))) ∧
  (path_concat _ _ = NONE)`

val path_base_def = Define`
  (path_base EmptyPath = NONE) ∧
  (path_base (AbsPath []) = SOME (AbsPath [])) ∧
  (path_base (AbsPath p) = SOME (AbsPath [LAST p])) ∧
  (path_base (RelPath h []) = SOME (RelPath h [])) ∧
  (path_base (RelPath h p) = SOME (RelPath (LAST p) []))`

val path_dir_def = Define`
  (path_dir EmptyPath = NONE) ∧
  (path_dir (AbsPath []) = SOME (AbsPath [])) ∧
  (path_dir (AbsPath p) = SOME (AbsPath (FRONT p))) ∧
  (path_dir (RelPath h []) = SOME (RelPath h [])) ∧
  (path_dir (RelPath h p) = SOME (RelPath h (FRONT p)))`

val _ = type_abbrev("abstract_path", ``:path # address option``)

val _ = Hol_datatype `ftype =
  TFile | TDirectory`

val _ = type_abbrev("bytes",``:char list``)
val _ = type_abbrev("string",``:char list``)

val _ = Hol_datatype `prog_value =
    Int of int
  | Bool of bool
  | Path of path
  | Bytes of bytes
  | Inode of inode
  | Ofaddr of ofaddr
  | Dirstream of dirstream
  | FType of ftype`

val _ = overload_on("NameVal",``λn. Path (NamePath n)``)
val _ = overload_on("RootVal",``Path RootPath``)

val _ = Hol_datatype `
  prog_exp =
    Lit of prog_value
  | Equal of prog_exp => prog_exp
  | Less of prog_exp => prog_exp
  | And of prog_exp => prog_exp
  | Not of prog_exp
  | Plus of prog_exp => prog_exp
  | Minus of prog_exp => prog_exp
  | Concat of prog_exp => prog_exp
  | Base of prog_exp
  | Dir of prog_exp`

val _ = overload_on("Name",``λn. Lit (NameVal n)``)
val _ = overload_on("Root",``Lit RootVal``)

val _ = overload_on("/",``Concat``)

val (eval_prog_exp_rules,eval_prog_exp_ind,eval_prog_exp_cases) = Hol_reln`
  (eval_prog_exp (Lit l) l) ∧

  (eval_prog_exp e1 v1 ∧
   eval_prog_exp e2 v2
   ⇒
   eval_prog_exp (Equal e1 e2) (Bool(v1 = v2))) ∧

  (eval_prog_exp e1 (Int i1) ∧
   eval_prog_exp e2 (Int i2)
   ⇒
   eval_prog_exp (Less e1 e2) (Bool(i1 < i2))) ∧

  (eval_prog_exp e1 (Bool b1) ∧
   eval_prog_exp e2 (Bool b2)
   ⇒
   eval_prog_exp (And e1 e2) (Bool(b1 ∧ b2))) ∧

  (eval_prog_exp e (Bool b)
   ⇒
   eval_prog_exp (Not e) (Bool(¬b))) ∧

  (eval_prog_exp e1 (Int i1) ∧
   eval_prog_exp e2 (Int i2)
   ⇒
   eval_prog_exp (Plus e1 e2) (Int(i1 + i2))) ∧

  (eval_prog_exp e1 (Int i1) ∧
   eval_prog_exp e2 (Int i2)
   ⇒
   eval_prog_exp (Minus e1 e2) (Int(i1 + i2))) ∧

  (eval_prog_exp e1 (Path p1) ∧
   eval_prog_exp e2 (Path p2) ∧
   path_concat p1 p2 = SOME p3
   ⇒
   eval_prog_exp (Concat e1 e2) (Path p3)) ∧

  (eval_prog_exp e (Path p) ∧
   path_base p = SOME p'
   ⇒
   eval_prog_exp (Base e) (Path p')) ∧

  (eval_prog_exp e (Path p) ∧
   path_dir p = SOME p'
   ⇒
   eval_prog_exp (Dir e) (Path p'))`

val _ = Hol_datatype`directory =
    FileLink of name => inode
  | Directory of name => directory list
  | Address of address`

val _ = type_abbrev("forest",``:directory list``)

val subst_def = xDefine "subst"`
  subst a vs (FileLink n i) = [FileLink n i] ∧
  subst a vs (Directory n ds) = [Directory n (subst_forest a vs ds)] ∧
  subst a vs (Address b) = (if a = b then vs else [Address b]) ∧
  subst_forest a vs [] = [] ∧
  subst_forest a vs (d::ds) = subst a vs d ++ subst_forest a vs ds`

val resolve_def = tDefine "resolve"`
  (resolve [p] NONE (FileLink q i) =
     if p = q then SOME (FileLink q i) else NONE) ∧

  (resolve [p] NONE (Directory q ids) =
     if p = q then SOME (Directory q ids) else NONE) ∧

  (resolve [] (SOME a) (Address b) =
    if a = b then SOME (Address b) else NONE) ∧

  (resolve (p::ps) a (Directory q ids) =
     if p = q then
       resolve_list ps a ids
     else NONE) ∧

  (resolve _ _ _ = NONE) ∧

  (resolve_list _ _ [] = NONE) ∧
  (resolve_list ps a (id::ids) =
     case resolve ps a id of
     | SOME x => SOME x
     | NONE => resolve_list ps a ids)`
(WF_REL_TAC`measure (λx. case x of
  | INL (_,_,ud) => directory_size ud
  | INR (_,_,ds) => directory1_size ds)`)

val _ = Hol_datatype `value =
    ProgValue of prog_value
  | ForestValue of forest
  | PathValue of abstract_path
  | AddressValue of address`

val _ = Hol_datatype `
  exp =
    ProgExp of prog_exp
  | Vals of value set
  | AddrVal of address
  | Union of exp => exp
  | Inter of exp => exp
  | Diff of exp => exp
  | IsElement of exp => exp`

val values_same_type_def = Define`
  values_same_type s ⇔
    (∀x. x ∈ s ⇒ ∃v. x = ProgValue v) ∨
    (∀x. x ∈ s ⇒ ∃v. x = ForestValue v) ∨
    (∀x. x ∈ s ⇒ ∃v. x = PathValue v) ∨
    (∀x. x ∈ s ⇒ ∃v. x = AddressValue v)`

val (eval_exp_rules,eval_exp_ind,eval_exp_cases) = Hol_reln`
  (eval_prog_exp pe pv
   ⇒
   eval_exp (ProgExp pe) {ProgValue pv}) ∧

  (values_same_type vs
   ⇒
   eval_exp (Vals vs) vs) ∧

  (eval_exp (AddrVal a) {AddressValue a}) ∧

  (eval_exp e1 vs1 ∧
   eval_exp e2 vs2 ∧
   values_same_type (vs1 ∪ vs2)
   ⇒
   eval_exp (Union e1 e2) (vs1 ∪ vs2)) ∧

  (eval_exp e1 vs1 ∧
   eval_exp e2 vs2 ∧
   values_same_type (vs1 ∪ vs2)
   ⇒
   eval_exp (Inter e1 e2) (vs1 ∩ vs2)) ∧

  (eval_exp e1 vs1 ∧
   eval_exp e2 vs2
   ⇒
   eval_exp (Diff e1 e2) (vs1 DIFF vs2))`

val _ = type_abbrev("env",``:var |-> prog_value``)

val _ = type_abbrev("dir_assertion",``:forest set``)

val DEmpty_def = Define`DEmpty = { [] }`
val _ = overload_on("∅",``DEmpty``)

val DFileLink_def = Define`
  DFileLink e1 e2 = { [FileLink n b] |
    eval_exp e1 {ProgValue (NameVal n)} ∧
    eval_exp e2 {ProgValue (Inode b)}}`

val DDirectory_def = Define`
  DDirectory e (da:dir_assertion) = { [Directory n ds] |
    eval_exp e {ProgValue (NameVal n)} ∧
    ds ∈ da }`

val DExp_def = Define`
  DExp exp = { ds | ∃vs. eval_exp exp vs ∧ (ForestValue ds) ∈ vs }`

val DConcat_def = Define`
  DConcat (da1:dir_assertion) (da2:dir_assertion) =
    { ds | ∃l1 l2. l1 ∈ da1 ∧ l2 ∈ da2 ∧ PERM (l1++l2) ds }`
val _ = overload_on("+",``DConcat``)

val DContextApplication_def = Define`
  DContextApplication (da1:dir_assertion) addr (da2:dir_assertion) =
    { subst_forest addr f2 f1 | (f2,f1) | f1 ∈ da1 ∧ f2 ∈ da2 ∧ (∃p. EXISTS (λd. IS_SOME (resolve p (SOME addr) d)) f1) }`

val DPathResolution_def = Define`
  DPathResolution exp env = { ds |
    ∃p ps a.
    eval_exp exp {PathValue (RelPath p ps,a)} ∧
    EXISTS IS_SOME (MAP (resolve (p::ps) a) ds) }`

val DLift_def = Define`
  DLift f (da1:dir_assertion) da2 = { ds | f (ds ∈ da1) (ds ∈ da2) }`
val _ = overload_on("/\\",``DLift $/\``)
val _ = overload_on("\\/",``DLift $\/``)
val _ = overload_on("F",``({}):dir_assertion``)
val _ = overload_on("T",``(UNIV):dir_assertion``)
val _ = overload_on("==>",``DLift $==>``)
val _ = overload_on("<=>",``DLift $<=>``)
val _ = overload_on("~",``λda:dir_assertion. da ⇒ F``)

val DExists_def = Define`
  DExists (P : α -> dir_assertion) = { ds | ∃v. ds ∈ (P v) }`
val _ = overload_on("?",``DExists``)
val _ = overload_on("!",``λP : α -> dir_assertion. ¬∃v. ¬(P v)``)

val _ = Hol_datatype`instrumented_filesystem =
  <| root : forest option
   ; address_env : address |-> (abstract_path # forest)
   ; inode_env : inode |-> bytes
   |>`

val _ = Hol_datatype`process_heap =
  <| filedesc_env : ofaddr |-> (inode # num)
   ; dirstream_env : dirstream |-> name set
   ; heap_env : num |-> int
   |>`

val _ = Hol_datatype`instrumented_state =
  <| fs : instrumented_filesystem
   ; heap : process_heap
   ; env : env
   |>`

val _ = type_abbrev("assertion",``:instrumented_state set``)

val Empty_def = Define`
  Empty
    = { <| fs := <| root := NONE; address_env := FEMPTY; inode_env := FEMPTY |>
         ; heap := <| filedesc_env := FEMPTY; dirstream_env := FEMPTY; heap_env := FEMPTY |>
         ; env := FEMPTY
         |> }`

val DirCell_def = Define`
  DirCell addr path_exp da = { state |
    ∃ap ds.
    FLOOKUP state.fs.address_env addr = SOME (ap,ds) ∧
    eval_exp path_exp {PathValue ap} ∧
    ds ∈ da }`

val RootCell_def = Define`
  RootCell da = { state |
    ∃ds. state.fs.root = SOME ds ∧
    ds ∈ da }`

val FileCell_def = Define`
  FileCell inode_exp bytes_exp env = { state |
   ∃inode bytes.
   FLOOKUP state.fs.inode_env inode = SOME bytes ∧
   eval_exp inode_exp {ProgValue (Inode inode)} ∧
   eval_exp bytes_exp {ProgValue (Bytes bytes)} }`

val FileDescCell_def = Define`
  FileDescCell fd_exp inode_exp offset_exp = { state |
    ∃fd inode offset.
    0 ≤ offset ∧
    FLOOKUP state.heap.filedesc_env fd = SOME (inode, Num offset) ∧
    eval_exp fd_exp {ProgValue (Ofaddr fd)} ∧
    eval_exp inode_exp {ProgValue (Inode inode)} ∧
    eval_exp offset_exp {ProgValue (Int offset)} }`

val DirStreamCell_def = Define`
  DirStreamCell ds_exp names_exp = { state |
    ∃dirstr ns.
    FLOOKUP state.heap.dirstream_env dirstr = SOME { n | ProgValue(NameVal n) ∈ ns } ∧
    eval_exp ds_exp {ProgValue (Dirstream dirstr)} ∧
    eval_exp names_exp ns ∧
    (∀v. v ∈ ns ⇒ ∃n. v = ProgValue(NameVal n)) }`

val HeapCell_def = Define`
  HeapCell addr_exp val_exp = { state |
    ∃addr v.
    0 ≤ addr ∧
    FLOOKUP state.heap.heap_env (Num addr) = SOME v ∧
    eval_exp addr_exp {ProgValue (Int addr)} ∧
    eval_exp val_exp {ProgValue (Int v)} }`

(* Ramana: Why can't we just use ExpCell (Var v) for this? *)
(* Gian: There is a subtle difference in their use. VarCell is used as a spatial
   formula whereas ExpCell is not. Using ExpCell to describe the value of a
   program expression requires the use of VarCells for every variable occurring
   within the program expression. Single variables can be always treated disjointly,
   whereas program expressions may have an overlap in the variables they use.
   That being said, in this work I think it is simpler to treat command arugments as simple variables,
   since we are not fully formalising the programming language anyway. *)
val VarCell_def = Define`
  VarCell var val_exp = { state |
    ∃v.
    FLOOKUP state.env var = SOME v ∧
    eval_exp val_exp {ProgValue v} }`

val Exp_def = Define`
  Exp exp = { state | state | eval_exp exp {ProgValue (Bool T)} }`

val root_compose_def = Define`
  (root_compose NONE     NONE     x ⇔ (x = NONE)  ) ∧
  (root_compose NONE     (SOME y) x ⇔ (x = SOME y)) ∧
  (root_compose (SOME y) NONE     x ⇔ (x = SOME y)) ∧
  (root_compose (SOME _) (SOME _) _ ⇔ F)`

val dfunion_def = Define`
  dfunion f1 f2 f3 ⇔ DISJOINT (FDOM f1) (FDOM f2) ∧ f3 = (f1 ⊌ f2)`

val Star_def = Define`
  Star a1 a2 = { state |
    ∃fs1 fs2 h1 h2 env1 env2.
      root_compose fs1.root          fs2.root          state.fs.root          ∧
      dfunion      fs1.address_env   fs2.address_env   state.fs.address_env   ∧
      dfunion      fs1.inode_env     fs2.inode_env     state.fs.inode_env     ∧
      dfunion      h1.filedesc_env   h2.filedesc_env   state.heap.filedesc_env  ∧
      dfunion      h1.dirstream_env  h2.dirstream_env  state.heap.dirstream_env ∧
      dfunion      h1.heap_env       h2.heap_env       state.heap.heap_env ∧
      dfunion      env1              env2              state.env ∧
      <| fs:=fs1; heap:=h1; env:=env1 |> ∈ a1 ∧
      <| fs:=fs2; heap:=h2; env:=env2 |> ∈ a2 }`
val _ = Parse.overload_on("*",``Star``)

val Lift_def = Define`
  Lift f (a1:assertion) a2 = { state | f (state ∈ a1) (state ∈ a2) }`
val _ = Parse.overload_on("/\\",``Lift $/\``)
val _ = Parse.overload_on("\\/",``Lift $\/``)
val _ = Parse.overload_on("F",``{}:assertion``)
val _ = Parse.overload_on("T",``UNIV:assertion``)
val _ = Parse.overload_on("==>",``Lift $==>``)
val _ = Parse.overload_on("<=>",``Lift $<=>``)
val _ = Parse.overload_on("~",``λa:assertion. a ⇒ F``)

val Exists_def = Define`
  Exists (P : α -> assertion) = { state | ∃v. state ∈ (P v) }`
val _ = Parse.overload_on("?",``Exists``)
val _ = Parse.overload_on("!",``λP : α -> assertion. ¬∃v. ¬(P v)``)

val SomeVarCell_def = Define`
    SomeVarCell var = ∃v. (VarCell var (Vals {ProgValue v}))`

val Somewhere_def = Define`
  Somewhere (da: dir_assertion) =
    ∃x. DContextApplication T x da`

val SomewhereTop_def = Define`
    SomewhereTop (da: dir_assertion) = DConcat T da`

val CompleteTree_def = Define`
  CompleteTree = ¬(∃x. (Somewhere (DExp (AddrVal x))))`

(* Ramana: Do you require some variable to bind v in the program environment? *)
(* Gian: No, here v is a logical variable *)
val Entry_def = Define`
  Entry name_exp =
    ((DDirectory name_exp T) ∨
		 (∃v. DFileLink name_exp (Vals {ProgValue v})))`

val TopAddress_def = Define`
  TopAddress = ∃x. (SomewhereTop (DExp (AddrVal x)))`

val TopContents_def = Define`
  TopContents (da: dir_assertion) = (da ∧ ¬TopAddress)`

val NameNotHere_def = Define`
    NameNotHere name_exp =
      (¬ SomewhereTop (Entry name_exp) ∧ ¬ TopAddress)`

(* Commands *)
val _ = Hol_datatype `command =
    (* First var is the one storing the return value after execution *)
    Mkdir of var => var
  | Rename of var => var => var`

(* Hoare triples *)
val _ = type_abbrev("hoare_triple", ``:assertion # command # assertion``)

(* AXIOMS *)

val _ = overload_on("DDir",``λe da. DDirectory (ProgExp e) da``)
val _ = overload_on("Safe",``λn. NameNotHere (ProgExp n)``)
val _ = overload_on("VarP",``λvar path. VarCell var (ProgExp path)``)
val _ = overload_on("VarI",``λvar int. VarCell var (ProgExp (Lit (Int int)))``)
val _ = overload_on("DirP",``λaddr path da. DirCell addr (ProgExp path) da``)
val _ = overload_on(":>",``λname inode. DFileLink (ProgExp name) (ProgExp inode)``)
val _ = add_infix(":>",425,NONASSOC)
val _ = overload_on("=",``λe1 e2. Exp (ProgExp (Equal e1 e2))``)
val _ = overload_on("<>",``λe1 e2. Exp (ProgExp (Neg (Equal e1 e2)))``)
val _ = Unicode.uoverload_on(Unicode.UChar.neq,``λe1 e2. Exp (ProgExp (Neg (Equal e1 e2)))``)

(* mkdir *)
(* Ramana:
   All the lowercase names here (r,p,b,a,v,c,path) are HOL variables.
   mkdir is schematic in them - any one of those variables can be instantiated with another HOL term.
   r and path are of type var. they are program variables, and are affected by the * operator:
     if the same one appears in more than one starred conjunct, the triple becomes vacuous, since
     the star is ensuring all the program variables are disjoint between assertions.
   v is of type address, and is also affected by * because the address_env is split.
   c is of type value set. it is a logical variable standing for whatever set you want.
   p, b, and a are of type path.
   I figure the axiom is really a schema for any particular path names you want to put in those places,
   so the axiom talks about literal paths but we put a HOL variable for the path name.
*)
val mkdir = ``
    let P = Lit (Path p) in
    let B = Lit (Path b) in
    let A = Lit (Path a) in
    let C = DExp (Vals c) in
    (* Ramana: should we constrain c to only contain ForestValues here? *)

    (SomeVarCell r
     * VarP path (P / B / A)
     * DirCell v (ProgExp P)
         (DDir B (C ∧ Safe A))

    ,Mkdir r path

    ,VarI r 0
     * VarP path (P / B / A)
     * DirCell v (ProgExp P)
         (DDir B (C + DDir A ∅))
    )``

(* mkdir, directly under root case *)
val mkdir_root = ``
    let A = Lit (Path a) in
    let C = DExp (Vals c) in

    (SomeVarCell r
     * VarP path (Root / A)
     * RootCell (C ∧ Safe A)

    ,Mkdir r path

    ,VarI r 0
     * VarP path (Root / A)
     * RootCell (C + (DDir A ∅))
    )``

(* rename, dir, move, target not exists *)
val rename_dir_move_not_exist = ``
    let P = Lit (Path p) in
    let D = Lit (Path d) in
    let A = Lit (Path a) in
    let P' = Lit (Path p') in
    let B = Lit (Path b) in
    let C = DExp (Vals c) in
    let C' = DExp (Vals c') in

    (SomeVarCell r
     * VarP old (P / A)
     * VarP new (P' / D / B) (* Ramana: do we need p ≠ p'? *) 
     (* Gian: No, that is a perfectly valid case: move the source dir to under some sibling. *)
     * DirP v P (DDir A (C ∧ CompleteTree))
     * DirP w P' (DDir D (C' ∧ Safe B))

    ,Rename r old new

    ,VarI r 0
     * VarP old (P / A)
     * VarP new (P' / D / B)
     * DirP v P ∅
     * DirP w P' (DDir D (C' + (DDir B C)))
      (* Ramana: why is CompleteTree not re-asserted? *)
      (* Gian: it does not matter. C is invariant, so it's still complete in the postocondition *)
    )``

(* rename, dir, move, target not exists, under root *)
val rename_dir_move_not_exist_root = ``
    let P = Lit (Path p) in
    let A = Lit (Path a) in
    let B = Lit (Path b) in
    let C = DExp (Vals c) in
    let C' = DExp (Vals c') in

    (SomeVarCell r
     * VarP old (P / A)
     * VarP new (Root / B)
     * DirP v P (DDir A (C ∧ CompleteTree))
     * RootCell (C' ∧ Safe B)

    ,Rename r old new

    ,VarI r 0
     * VarP old (P / A)
     * VarP new (Root / B)
     * DirP v P ∅
     * RootCell (C' + DDir B C)
    )``

(* rename, dir, target not exists *)
val rename_dir_not_exist = ``
    let P = Lit (Path p) in
    let D = Lit (Path d) in
    let A = Lit (Path a) in
    let B = Lit (Path b) in
    let C = DExp (Vals c) in
    let C' = DExp (Vals c') in

    (SomeVarCell r
     * VarP old (P / D / A)
     * VarP new (P / D / B)
     * DirP v P
         (DDir D
           (C + DDir A (C' ∧ CompleteTree)
            ∧ Safe B))

    ,Rename r old new

    ,VarI r 0
     * VarP old (P / D / A)
     * VarP new (P / D / B)
     * DirP v P
         (DDir D (C + DDir B C'))
    )``

(* rename, dir, target not exist, root *)
val rename_dir_not_exist_root = ``
    let A = Lit (Path a) in
    let B = Lit (Path b) in
    let C = DExp (Vals c) in
    let C' = DExp (Vals c') in

    (SomeVarCell r
     * VarP old (Root / A)
     * VarP new (Root / B)
     * RootCell
         (C + DDir A (C' ∧ CompleteTree)
          ∧ Safe B)

    ,Rename r old new

    ,VarI r 0
     * VarP old (Root / A)
     * VarP new (Root / B)
     * RootCell (C + DDir B C')
    )``

(* rename: dir, target exists *)
val rename_move_dir_exist = ``
    let P = Lit (Path p) in
    let A = Lit (Path a) in
    let P' = Lit (Path p') in
    let B = Lit (Path b) in
    let C = DExp (Vals c) in

    (SomeVarCell r
     * VarP old (P / A)
     * VarP new (P' / B)
     * DirP v P (DDir A (C ∧ CompleteTree))
     * DirP w P' (DDir B ∅)

    ,Rename r old new

    ,VarI r 0
     * VarP old (P / A)
     * VarP new (P' / B)
     * DirP v P ∅
     * DirP w P' (DDir B C)
    )``

(* rename: move, file, target not exist *)
val rename_move_file_not_exist =``
    let P = Lit (Path p) in
    let A = Name a in
    let P' = Lit (Path p') in
    let D = Lit (Path d) in
    let B = Name b in
    let I = Lit (Inode i) in
    let C = DExp (Vals c) in

    (SomeVarCell r
     * VarP old (P / A)
     * VarP new (P' / D / B)
     * DirP v P (A :> I)
     * DirP w P' (DDir D (C ∧ Safe B))

    ,Rename r old new

    ,VarI r 0
     * VarP old (P / A)
     * VarP new (P' / D / B)
     * DirP v P ∅
     * DirP w P' (DDir D (C + (B :> I)))
    )``

(* rename: move, file, target not exists under root *)
val rename_move_file_not_exist_root = ``
    let P = Lit (Path p) in
    let A = Name a in
    let B = Name b in
    let I = Lit (Inode i) in
    let C = DExp (Vals c) in

    (SomeVarCell 0
     * VarP old (P / A)
     * VarP new (Root / B)
     * DirP v P (A :> I)
     * RootCell (C ∧ Safe B)

    ,Rename r old new

    ,VarI r 0
     * VarP old (P / A)
     * VarP new (Root / B)
     * DirP v P ∅
     * RootCell (C + (B :> I))
    )``

(* rename: file, target not exist *)
val rename_file_not_exist = ``
    let P = Lit (Path p) in
    let D = Lit (Path d) in
    let A = Name a in
    let B = Name b in
    let I = Lit (Inode i) in
    let C = DExp (Vals c) in

    (SomeVarCell r
	   * VarP old (P / D / A)
     * VarP new (P / D / B)
     * DirP v P (DDir D (C + (A :> I) ∧ Safe B))

    ,Rename r old new

    ,VarI r 0
	   * VarP old (P / D / A)
     * VarP new (P / D / B)
     * DirP v P (DDir D (C + (B :> I)))
    )``

(* rename: file, target not exist under root *)
val rename_file_not_exist_root = ``
    let A = Name a in
    let B = Name b in
    let I = Lit (Inode i) in
    let C = DExp (Vals c) in

    (SomeVarCell r
	   * VarP old (Root / A)
     * VarP new (Root / B)
     * RootCell (C + (A :> I) ∧ Safe B)

    ,Rename r old new

    ,VarI r 0
	   * VarP old (Root / A)
     * VarP new (Root / B)
     * RootCell (C + (B :> I))
    )``

(* rename: file, target exists *)
val rename_file_exist = ``
    let P = Lit (Path p) in
    let A = Name a in
    let P' = Lit (Path p') in
    let B = Name b in
    let I = Lit (Inode i) in
    let I' = Lit (Inode i') in

    (SomeVarCell r
	   * VarP old (P / A)
     * VarP new (P' / B)
     * DirP v P (A :> I)
     * DirP w P' (B :> I')
     ∧ I ≠ I'

    ,Rename r old new

    ,VarI r 0
	   * VarP old (P / A)
     * VarP new (P' / B)
     * DirP v P ∅
     * DirP w P' (B :> I)
    )``

(* rename: file, target exist, same inode *)
val rename_file_exist_same = ``
    let P = Lit (Path p) in
    let A = Name a in
    let P' = Lit (Path p') in
    let B = Name b in
    let I = Lit (Inode i) in

    (SomeVarCell r
	   * VarP old (P / A)
     * VarP new (P' / B)
     * DirP v P (A :> I)
     * DirP w P' (B :> I)

    ,Rename r old new

    ,VarI r 0
	   * VarP old (P / A)
     * VarP new (P' / B)
     * DirP v P (A :> I)
     * DirP w P' (B :> I)
    )``

(* rename: same paths *)
val rename_same = ``
    let P = Lit (Path p) in
    let A = Lit (Path a) in

    (SomeVarCell 0
	   * VarP old (P / A)
     * VarP new (P / A)
     * DirP v P (da ∧ Entry (ProgExp A))

    ,Rename r old new

    ,VarI r 0
	   * VarP old (P / A)
     * VarP new (P / A)
     * DirP v P da
    )``

(* Assertion sanity checks *)
(* Directory assertion checks *)

(* Gian: Directory assertions have an envirnment,
   so I need to apply some environment to get the set
   of states satisfied by the assertion *)

(* empty forest satisfies dirempty *)
val t1 = prove(``([]:forest list) ∈ ∅``, rw[DEmpty_def])

(* non empty forest does not satisfy ∅ *)
val t2 = prove(``FileLink name inode ∉ ∅``, rw[DEmpty_def])

(* nothing satisfies false; anything satisfies true *)
val t3 = prove(``[FileLink name inode] ∉ F``, rw[DLift_def])
val t4 = prove(``[FileLink name inode] ∈ T``, rw[DLift_def])

(* directory does not satisfy file and vice versa *)
val t5 = prove(
  ``[Directory dn[FileLink fn x]] ∈
          (DDir (Name dn) (Name fn :> Lit (Inode x)))``,
  rw[DDirectory_def] >- (
    rw[Once eval_exp_cases] >>
    rw[Once eval_prog_exp_cases] ) >>
  rw[DFileLink_def] >>
  rw[Once eval_exp_cases] >>
  rw[Once eval_prog_exp_cases] )

val t6 = prove(
  ``[Directory dn [FileLink fn n]] ∉
      (DFileLink (ProgExp (Name dn)) (ProgExp (Lit (Inode n))))``,
  rw[DFileLink_def])

val t7 = prove(
  ``[FileLink fn n] ∈ (DFileLink (ProgExp (Name fn)) (ProgExp (Lit (Inode n))))``,
  rw[DFileLink_def] >>
  rw[Once eval_exp_cases] >>
  rw[Once eval_prog_exp_cases])

val t8 = prove(
  ``[FileLink "foo" 42] ∉ (DDirectory (ProgExp (Name "foo")) T)``,
  rw[DDirectory_def])

(* directory contents with true *)
val dir = ``[Directory "a" [Directory "b" []; Directory "c" [FileLink "d" 42; Directory "e" []; FileLink "g" 42]; Directory "d" [FileLink "f" 4242]]]``
val t9 = prove(
  ``^dir ∈ (DDir (Name "a") T)``,
  rw[DDirectory_def] >>
  rw[Once eval_exp_cases] >>
  rw[Once eval_prog_exp_cases] )

val t10 = prove(
  ``^dir ∉ (DDir (Name "a") (DDir (Name "b") ∅))``,
  rw[DDirectory_def])

val t11 = prove(
  ``^dir ∉ (DDir (Name "a") (DDir (Name "b") T))``,
  rw[DDirectory_def])

val t12 = prove(
  ``^dir ∈ (DDir (Name "a") ((DDir (Name "b") T) + T))``,
  rw[DDirectory_def,DConcat_def] >- (
    simp[Once eval_exp_cases] >>
    simp[Once eval_prog_exp_cases] ) >>
  srw_tac[DNF_ss][] >>
  simp[Once eval_exp_cases] >>
  simp[Once eval_prog_exp_cases] >>
  qho_match_abbrev_tac`∃l2 ds. PERM (D ds::l2) (CONS (D []) Y)` >>
  `D [] :: Y = [] ++ (D [] :: Y)` by simp[] >>
  pop_assum SUBST1_TAC >>
  qexists_tac`Y` >> qexists_tac`[]` >>
  match_mp_tac CONS_PERM >>
  simp[])

(* + is commutative *)
val t13 = prove(
  ``^dir ∈ (DDir (Name "a") ((DDir (Name "c") T) + T))``,
  rw[DDirectory_def,DConcat_def] >- (
    simp[Once eval_exp_cases] >>
    simp[Once eval_prog_exp_cases] ) >>
  srw_tac[DNF_ss][] >>
  simp[Once eval_exp_cases] >>
  simp[Once eval_prog_exp_cases] >>
  qho_match_abbrev_tac`∃l2 ds. PERM (D ds::l2) (CONS E (CONS (D X) Y))` >>
  qexists_tac`E::Y` >> qexists_tac`X` >>
  `E::D X::Y = [E] ++ D X :: Y` by simp[] >>
  pop_assum SUBST1_TAC >>
  match_mp_tac CONS_PERM >>
  simp[])

val subst_forest_MAP = store_thm("subst_forest_MAP",
  ``∀ls a vs. subst_forest a vs ls = FLAT (MAP (subst a vs) ls)``,
  Induct >> simp[subst_def])

val FLAT_EQ_NIL = store_thm("FLAT_EQ_NIL",
  ``∀ls. (FLAT ls = []) = EVERY ($= []) ls``,
  Induct THEN SRW_TAC[][EQ_IMP_THM])

val FLAT_EQ_SING = store_thm("FLAT_EQ_SING",
  ``∀ls x. (FLAT ls = [x]) ⇔ ∃l1 l2. (ls = l1 ++ [[x]] ++ l2) ∧ EVERY ($= []) l1 ∧ EVERY ($= []) l2``,
  Induct >> simp[] >>
  Cases >> simp[] >- (
    rw[EQ_IMP_THM] >- (
      qexists_tac`[]::l1` >>
      simp[] ) >>
    Cases_on`l1` >- fs[] >>
    qexists_tac`t` >>
    ntac 2 (pop_assum mp_tac) >>
    simp[] >> rw[] >> fs[] ) >>
  rw[EQ_IMP_THM,FLAT_EQ_NIL] >- (
    qexists_tac`[]` >>
    simp[] ) >>
  ntac 2 (pop_assum mp_tac) >>
  Cases_on`l1`>> simp[] >> rw[] >>
  fs[] )

val subst_not_nil = store_thm("subst_not_nil",
  ``∀ls a vs. vs ≠ [] ⇒ subst a vs ls ≠ []``,
  Induct >> simp[subst_def] >> rw[])

val subst_sing_or_vs = store_thm("subst_sing_or_vs",
  ``∀ls a vs. (subst a vs ls = vs) ∨ ∃x. subst a vs ls = [x]``,
  Induct >> simp[subst_def] >> rw[])

val resolve_SOME_SOME = store_thm("resolve_SOME_SOME",
   ``(∀p sa d a x. resolve p sa d = SOME x ∧ sa = SOME a ⇒ x = Address a) ∧
     (∀p sa ds a x. resolve_list p sa ds = SOME x ∧ sa = SOME a ⇒ x = Address a)``,
   ho_match_mp_tac(theorem"resolve_ind") >>
   simp[resolve_def] >> rw[] >>
   BasicProvers.EVERY_CASE_TAC >> fs[])

val resolve_nil_SOME = store_thm("resolve_nil_SOME",
  ``∀d a x. resolve [] a d = SOME x ⇒ ∃y. a = SOME y ∧ x = Address y ∧ d = Address y``,
  Induct >> simp[resolve_def] >>
  gen_tac >> Cases >> simp[resolve_def])

val subst_forest_nil = store_thm("subst_forest_nil",
  ``∀ls a vs. vs ≠ [] ⇒ (subst_forest a vs ls = [] ⇔ (ls = []))``,
  Induct >> simp[subst_def] >> metis_tac[subst_not_nil])

(* context application *)
val t14 = prove(
  ``^dir ∉ (DContextApplication T 42 (DDir (Name "G") ∅))``,
  rw[DContextApplication_def] >>
  rw[DDirectory_def] >>
  rw[Once eval_exp_cases] >>
  rw[Once eval_prog_exp_cases] >>
  rw[DEmpty_def] >>
  Cases_on`f2 = [Directory "G" []]` >> simp[] >> rw[] >>
  spose_not_then strip_assume_tac >> fs[] >>
  fs[listTheory.EXISTS_MEM] >> rw[] >>
  Cases_on`resolve p (SOME 42) e`>>fs[] >> rw[] >>
  fs[subst_forest_MAP] >>
  qmatch_assum_abbrev_tac`[z] = FLAT y` >>
  qpat_assum`[z] = FLAT y`(mp_tac o SYM) >>
  simp[FLAT_EQ_SING] >> rw[] >>
  spose_not_then strip_assume_tac >>
  qunabbrev_tac`y` >>
  fs[EVERY_MEM] >>
  reverse(Cases_on`l1`) >- (
    fs[] >>
    `h = []` by metis_tac[] >>
    Cases_on`f1`>>fs[] >>
    metis_tac[subst_not_nil,NOT_NIL_CONS] ) >>
  fs[] >> rw[] >>
  qpat_assum`MEM e f1`mp_tac >>
  Cases_on`f1`>>fs[]>>
  reverse(Cases_on`t`) >- (
    fs[] >>
    Cases_on`l2`>>fs[]>>
    metis_tac[subst_not_nil,NOT_NIL_CONS] ) >>
  fs[] >> rw[] >> fs[] >> rw[] >>
  spose_not_then strip_assume_tac >> rw[] >>
  imp_res_tac resolve_SOME_SOME >> fs[] >> rw[] >>
  Cases_on`p`>- (
    imp_res_tac resolve_nil_SOME >>
    fs[subst_def] >> fs[Abbr`z`] ) >>
  Cases_on`e`>>fs[resolve_def] >>
  Cases_on`h=s`>>fs[]>>rw[]>>
  fs[subst_def]>>
  fs[Abbr`z`]>>
  Cases_on`l`>>fs[resolve_def]>>
  rw[] >>
  fs[subst_def] >>
  qmatch_assum_abbrev_tac`subst a vs x ++ ls = z` >>
  Cases_on`subst a vs x = vs` >- ( fs[Abbr`vs`] ) >>
  `∃y. subst a vs x = [y]` by metis_tac[subst_sing_or_vs] >>
  fs[Abbr`ls`,Abbr`z`] >>
  reverse BasicProvers.EVERY_CASE_TAC >- (
    imp_res_tac resolve_SOME_SOME >> fs[] >> rw[] >>
    qpat_assum`Abbrev(x=Z)`kall_tac >>
    reverse(Cases_on`x`>>fs[subst_def,resolve_def])>-(
      Cases_on`a=n`>>fs[Abbr`vs`] ) >>
    `l = []` by metis_tac[subst_forest_nil,NOT_NIL_CONS] >>
    Cases_on`t`>>fs[resolve_def] ) >>
  Cases_on`t'`>>fs[subst_def] >>
  Cases_on`subst a vs h = vs` >- ( fs[Abbr`vs`] ) >>
  `∃q. subst a vs h = [q]` by metis_tac[subst_sing_or_vs] >>
  fs[] >>
  fs[resolve_def]>>
  Cases_on`t''`>>fs[subst_def]>>
  Cases_on`subst a vs h'' = vs` >- ( fs[Abbr`vs`] ) >>
  `∃r. subst a vs h'' = [r]` by metis_tac[subst_sing_or_vs] >>
  fs[] >> rw[] >>
  fs[Abbr`vs`] >> rw[] >>
  reverse(Cases_on`h`>>fs[subst_def])>-(
    Cases_on`a=n`>>fs[]) >>
  fs[resolve_def]>>
  qpat_assum`X = SOME Y`mp_tac >>
  reverse BasicProvers.CASE_TAC >- (
    imp_res_tac resolve_SOME_SOME >>
    fs[] >>
    reverse(Cases_on`h''`>>fs[subst_def])>-(
      Cases_on`a=n`>>fs[]) >>
    Cases_on`l'`>>fs[subst_def]>>
    qabbrev_tac`vs = [Directory "G" []]` >>
    Cases_on`subst a vs h = vs` >- fs[Abbr`vs`]>>
    `∃z. subst a vs h = [z]` by metis_tac[subst_sing_or_vs] >>
    fs[]>>
    Cases_on`t`>>fs[resolve_def]>>
    Cases_on`h''=s'`>>fs[]>>
    `t'' = []` by metis_tac[subst_forest_nil,NOT_NIL_CONS]>>
    fs[resolve_def]>>
    BasicProvers.EVERY_CASE_TAC>>fs[]>>rw[]>>
    reverse(Cases_on`h`>>fs[subst_def])>-(
      Cases_on`a=n`>>fs[]) >>
    rw[]>>Cases_on`t'''`>>fs[resolve_def]) >>
  rw[] >>
  reverse(Cases_on`h''`>>fs[subst_def])>-(
    Cases_on`a=n`>>fs[])>>
  Cases_on`l'`>>fs[subst_def]>>
  qabbrev_tac`vs = [Directory "G" []]` >>
  Cases_on`subst a vs h = vs` >- fs[Abbr`vs`]>>
  `∃z. subst a vs h = [z]` by metis_tac[subst_sing_or_vs] >>
  fs[]>>
  `t'' = []` by metis_tac[subst_forest_nil,NOT_NIL_CONS]>>
  rw[]>>
  reverse(Cases_on`h`>>fs[subst_def])>-(
    Cases_on`a=n`>>fs[]) >>
  rw[]>>
  `t' = []` by metis_tac[subst_forest_nil,NOT_NIL_CONS]>>
  rw[resolve_def]>>
  BasicProvers.CASE_TAC>>
  Cases_on`t`>>fs[resolve_def]>>
  Cases_on`h="c"`>>fs[]>>
  Cases_on`l`>>fs[subst_def]>>
  fs[resolve_def]>>
  Cases_on`subst a vs h'' = vs` >- fs[Abbr`vs`]>>
  `∃z. subst a vs h'' = [z]` by metis_tac[subst_sing_or_vs] >>
  fs[]>>
  Cases_on`t`>>fs[resolve_def,subst_def]>>
  Cases_on`subst a vs h''' = vs` >- fs[Abbr`vs`]>>
  `∃z. subst a vs h''' = [z]` by metis_tac[subst_sing_or_vs] >>
  fs[]>>
  Cases_on`t''`>>fs[resolve_def,subst_def]>>
  Cases_on`subst a vs h'''' = vs` >- fs[Abbr`vs`]>>
  `∃z. subst a vs h'''' = [z]` by metis_tac[subst_sing_or_vs] >>
  fs[]>>
  `t=[]` by metis_tac[subst_forest_nil,NOT_NIL_CONS]>>
  fs[resolve_def]>> rw[] >>
  reverse(Cases_on`h''`>>fs[subst_def]) >- (
    Cases_on`a=n`>>fs[]) >>
  rw[]>>
  reverse(Cases_on`h'''`>>fs[subst_def]) >- (
    Cases_on`a=n`>>fs[]) >>
  rw[]>>
  reverse(Cases_on`h''''`>>fs[subst_def]) >- (
    Cases_on`a=n`>>fs[]) >>
  rw[]>>
  `l=[]` by metis_tac[subst_forest_nil,NOT_NIL_CONS]>>
  rw[]>>fs[]>>
  Cases_on`t'`>>fs[resolve_def])

val _ = dir ∈ (DContextApplication T 42 (DFileLink (ProgExp (Name "g")) (ProgExp (Lit (Inode 42))))) FEMPTY
val _ = dir ∈ (DContextApplication (DDirectory (ProgExp (Name "a")) (Address 42)) 42 T) FEMPTY
val _ = dir ∉ (DContextApplication (DDirectory (ProgExp (Name "a")) DEmpty) 42 T) FEMPTY

(* Gian: we also need: 
   - sibling uniqueness in directory forests
   - uniqueness of abstract addresses *)

(* instrumented directory heap cell assertions *)

let state_cons env =
  { <| fs := <| root := NONE; address_env := env; inode_env := FEMPTY |>
      ; heap := <| filedesc_env := FEMPTY; dirstream_env := FEMPTY; heap_env := FEMPTY |>
      ; env := FEMPTY
    |> }

val _ = 
  let state = address_env_cons { 42 |-> (AbsPath ["foo"])  [] }
  state ∉ DirP 41 (Lit (Path (AbsPath["foo"]))) ∅

val _ = 
  let state = address_env_cons { 42 |-> (AbsPath ["foo"])  [] }
  state ∈ DirP 42 (Lit (Path (AbsPath["foo"]))) ∅

(* star on non-disjoint addresses is false *)
val _ =
    { } ∈ address_env_cons { 42 |-> (AbsPath ["foo"])  []; 42 |-> (AbsPath ["foo"])  [] }

val _ =
  let state = address_env_cons { 42 |-> (AbsPath ["foo"])  dir }
  state ∈ DirP 41 (Lit (Path (AbsPath["foo"]))) (DDirectory (ProgExp (Name "a")) (Address 42)) 42 T)

val _ = export_theory()
