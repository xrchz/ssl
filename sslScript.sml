open HolKernel bossLib boolLib Parse lcsymtacs stringTheory intLib finite_mapTheory ParseExtras

val _ = new_theory"ssl"

val _ = tight_equality()

val _ = type_abbrev("name",``:string``)

val _ = type_abbrev("relpath",``:name list``)

val _ = type_abbrev("inode", ``:num``)
val _ = type_abbrev("ofaddr", ``:num``)
val _ = type_abbrev("dirstream", ``:num``)
val _ = type_abbrev("address", ``:num``)
val _ = type_abbrev("var", ``:num``)

val _ = Hol_datatype `path =
    EmptyPath
  | AbsPath of relpath
  | RelPath of name => relpath`

val _ = overload_on("Name",``λn. RelPath n []``)

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

val _ = type_abbrev("abspath", ``:path # address option``)

val _ = Hol_datatype `ftype =
  File | Directory`

val _ = type_abbrev("bytes",``:char list``)

val _ = Hol_datatype `prog_value =
    Int of int
  | Bool of bool
  | Path of path
  | Byte of bytes
  | Inode of inode
  | Ofaddr of ofaddr
  | Dirstream of dirstream
  | FType of ftype`

val _ = Hol_datatype `
  prog_exp =
    Lit of prog_value
  | ProgVar of var
  | Equal of prog_exp => prog_exp
  | Less of prog_exp => prog_exp
  | And of prog_exp => prog_exp
  | Not of prog_exp
  | Plus of prog_exp => prog_exp
  | Minus of prog_exp => prog_exp
  | Concat of prog_exp => prog_exp
  | Base of prog_exp
  | Dir of prog_exp`

val (eval_prog_exp_rules,eval_prog_exp_ind,eval_prog_exp_cases) = Hol_reln`
  (eval_prog_exp env (Lit l) l) ∧

  (FLOOKUP env var = SOME v
   ⇒
   eval_prog_exp env (ProgVar var) v) ∧

  (eval_prog_exp env e1 v1 ∧
   eval_prog_exp env e2 v2
   ⇒
   eval_prog_exp env (Equal e1 e2) (Bool(v1 = v2))) ∧

  (eval_prog_exp env e1 (Int i1) ∧
   eval_prog_exp env e2 (Int i2)
   ⇒
   eval_prog_exp env (Less e1 e2) (Bool(i1 < i2))) ∧

  (eval_prog_exp env e1 (Bool b1) ∧
   eval_prog_exp env e2 (Bool b2)
   ⇒
   eval_prog_exp env (And e1 e2) (Bool(b1 ∧ b2))) ∧

  (eval_prog_exp env e (Bool b)
   ⇒
   eval_prog_exp env (Not e) (Bool(¬b))) ∧

  (eval_prog_exp env e1 (Int i1) ∧
   eval_prog_exp env e2 (Int i2)
   ⇒
   eval_prog_exp env (Plus e1 e2) (Int(i1 + i2))) ∧

  (eval_prog_exp env e1 (Int i1) ∧
   eval_prog_exp env e2 (Int i2)
   ⇒
   eval_prog_exp env (Minus e1 e2) (Int(i1 + i2))) ∧

  (eval_prog_exp env e1 (Path p1) ∧
   eval_prog_exp env e2 (Path p2) ∧
   path_concat p1 p2 = SOME p3
   ⇒
   eval_prog_exp env (Concat e1 e2) (Path p3)) ∧

  (eval_prog_exp env e (Path p) ∧
   path_base p = SOME p'
   ⇒
   eval_prog_exp env (Base e) (Path p')) ∧

  (eval_prog_exp env e (Path p) ∧
   path_dir p = SOME p'
   ⇒
   eval_prog_exp env (Dir e) (Path p'))`

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
  | PathValue of abspath
  | AddressValue of address`

val _ = Hol_datatype `
  exp =
    ProgExp of prog_exp
  | Var of var
  | Union of exp => exp
  | Inter of exp => exp
  | Diff of exp => exp`

val values_same_type_def = Define`
  values_same_type s ⇔
    (∀x. x ∈ s ⇒ ∃v. x = ProgValue v) ∨
    (∀x. x ∈ s ⇒ ∃v. x = ForestValue v) ∨
    (∀x. x ∈ s ⇒ ∃v. x = PathValue v) ∨
    (∀x. x ∈ s ⇒ ∃v. x = AddressValue v)`

val dest_ProgValue_def = Define`
  dest_ProgValue (ProgValue v) = v`

val (eval_exp_rules,eval_exp_ind,eval_exp_cases) = Hol_reln`
  (eval_prog_exp (dest_ProgValue o_f (DRESTRICT env {x | FLOOKUP env x = SOME (ProgValue pv)})) pe pv
   ⇒
   eval_exp env (ProgExp pe) {ProgValue pv}) ∧

  (FLOOKUP env x = SOME v
   ⇒
   eval_exp env (Var x) {v}) ∧

  (eval_exp env e1 vs1 ∧
   eval_exp env e2 vs2
   ⇒
   eval_exp env (Union e1 e2) (vs1 ∪ vs2)) ∧

  (eval_exp env e1 vs1 ∧
   eval_exp env e2 vs2
   ⇒
   eval_exp env (Inter e1 e2) (vs1 ∩ vs2)) ∧

  (eval_exp env e1 vs1 ∧
   eval_exp env e2 vs2
   ⇒
   eval_exp env (Diff e1 e2) (vs1 DIFF vs2))`

val _ = type_abbrev("env",``:var |-> value``)

val _ = type_abbrev("dir_assertion",``:env -> forest set``)

val DEmpty_def = Define`DEmpty env = { [] }`

val DFileLink_def = Define`
  DFileLink e1 e2 env = { [FileLink n b] |
    eval_exp env e1 {ProgValue (Path (Name n))} ∧
    eval_exp env e2 {ProgValue (Inode b)}}`

val DDirectory_def = Define`
  DDirectory e (da:dir_assertion) env = { [Directory n ds] |
    eval_exp env e {ProgValue (Path (Name n))} ∧
    da env ds }`

val DExp_def = Define`
  DExp exp env = { ds | ∃vs. eval_exp env exp vs ∧ (ForestValue ds) ∈ vs }`

val DConcat_def = Define`
  DConcat (da1:dir_assertion) (da2:dir_assertion) env =
    { l1++l2 | l1 ∈ da1 env ∧ l2 ∈ da2 env }`

val DContextApplication_def = Define`
  DContextApplication (da1:dir_assertion) addr (da2:dir_assertion) env =
    { subst_forest addr f2 f1 | f1 ∈ da1 env ∧ f2 ∈ da2 env }`

val DPathResolution_def = Define`
  DPathResolution exp env = { ds |
    ∃p ps a.
    eval_exp env exp {PathValue (RelPath p ps,a)} ∧
    EXISTS IS_SOME (MAP (resolve (p::ps) a) ds) }`

(*

type_of
``DConcat (DDirectory (ProgExp(Lit(Path(Name a)))) DEmpty)
          (DDirectory (ProgExp(Lit(Path(Name b)))) DEmpty)``

*)

val _ = Hol_datatype`instrumented_filesystem =
  <| root : forest option
   ; address_env : address |-> (abspath # forest)
   ; inode_env : inode |-> bytes
   |>`

val _ = Hol_datatype`process_heap =
  <| filedesc_env : ofaddr |-> (inode # num)
   ; dirstream_env : dirstream |-> name set
   ; heap_env : num |-> int
   |>`

val _ = Hol_datatype`instrumented_state =
  <| fs : instrumented_filesystem
   ; ph : process_heap
   ; vs : var |-> value
   |>`

val _ = type_abbrev("assertion",``:env -> instrumented_state set``)

val Empty_def = Define`
  Empty (env:env)
    = { <| fs := <| root := NONE; address_env := FEMPTY; inode_env := FEMPTY |>
         ; ph := <| filedesc_env := FEMPTY; dirstream_env := FEMPTY; heap_env := FEMPTY |>
         ; vs := FEMPTY
         |> }`

val DirCell_def = Define`
  DirCell addr exp da env = { state |
    ∃ap ds.
    FLOOKUP state.fs.address_env addr = SOME (ap,ds) ∧
    eval_exp env exp {PathValue ap} ∧
    ds ∈ da env }`

val RootCell_def = Define`
  RootCell da env = { state |
    ∃ds. state.fs.root = SOME ds ∧
    ds ∈ da env }`

val FileCell_def = Define`
  FileCell inode_exp bytes_exp env = { state |
   ∃inode bytes.
   FLOOKUP state.fs.inode_env inode = SOME bytes ∧
   eval_exp env inode_exp {ProgValue (Inode inode)} ∧
   eval_exp env bytes_exp {ProgValue (Byte bytes)} }`

val FileDescCell_def = Define`
  FileDescCell fd_exp inode_exp offset_exp env = { state |
    ∃fd inode offset.
    0 ≤ offset ∧
    FLOOKUP state.ph.filedesc_env fd = SOME (inode, Num offset) ∧
    eval_exp env fd_exp {ProgValue (Ofaddr fd)} ∧
    eval_exp env inode_exp {ProgValue (Inode inode)} ∧
    eval_exp env offset_exp {ProgValue (Int offset)} }`

val DirStreamCell_def = Define`
  DirStreamCell ds_exp names_exp env = { state |
    ∃dirstr names ns.
    FLOOKUP state.ph.dirstream_env dirstr = SOME names ∧
    eval_exp env ds_exp {ProgValue (Dirstream dirstr)} ∧
    eval_exp env names_exp ns ∧

    (* Ramana: I don't quite understand what's supposed to happen here.
       names is going to be a set of bytes, since that's what's in the range of dirstream_env.
       how do we relate (names:bytes set) to (ns:value set)?
     *)

    (* GIAN: We need name set, but in env we have no such values.
       Instead, we have path set. We need the path set to include only
       relative paths with a single component. *)
   ∀n. n ∈ ns ⇔ ∃m. n = ProgValue (RelPath m []) ∧
   (* maybe the above is superflous because MAP throws an exception
      in case of an incomplete pattern match ? *)
   names = MAP (λ ProgValue (RelPath n []). n) ns }`

val HeapCell_def = Define`
  HeapCell addr_exp val_exp env = { state |
    ∃addr v.
    0 ≤ addr ∧
    FLOOKUP state.ph.heap_env (Num addr) = SOME v ∧
    eval_exp env addr_exp {ProgValue (Int addr)} ∧
    eval_exp env val_exp {ProgValue (Int v)} }`

val VarCell_def = Define`
  VarCell var val_exp env = { state |
    ∃v.
    FLOOKUP state.vs var = SOME v ∧
    eval_exp env val_exp {v} }`

val ExpCell_def = Define`
  ExpCell prog_exp exp env = { state |
    ∃thevalue.
    (* Ramana: is state.vs supposed to only contain prog_values in its domain?
       currently it contains values in its domain *)
    eval_prog_exp state.vs prog_exp thevalue ∧
    eval_exp env exp {ProgValue thevalue} }`

val Exp_def = Define`
  (* If exp evaluates to true then it's all the instrumented states, else it's no states *)
  (* (Ramana: yes, that correctly describes what's below) *)
  Exp exp env = { state | eval_exp env exp {ProgValue (Bool TRUE)} }`

val root_compose_def = Define`
  (root_compose NONE     NONE     x ⇔ (x = NONE)  ) ∧
  (root_compose NONE     (SOME y) x ⇔ (x = SOME y)) ∧
  (root_compose (SOME y) NONE     x ⇔ (x = SOME y)) ∧
  (root_compose (SOME _) (SOME _) _ ⇔ F)`

val dfunion_def = Define`
  dfunion f1 f2 f3 ⇔ DISJOINT (FDOM f1) (FDOM f2) ∧ f3 = (f1 ⊌ f2)`

val Star_def = Define`
  Star a1 a2 = { state |
    ∃fs1 fs2 ph1 ph2 vs1 vs2.
      root_compose fs1.root          fs2.root          state.fs.root          ∧
      dfunion      fs1.address_env   fs2.address_env   state.fs.address_env   ∧
      dfunion      fs1.inode_env     fs2.inode_env     state.fs.inode_env     ∧
      dfunion      ph1.filedesc_env  ph2.filedesc_env  state.ph.filedesc_env  ∧
      dfunion      ph1.dirstream_env ph2.dirstream_env state.ph.dirstream_env ∧
      dfunion      ph1.heap_env      ph2.heap_env      state.ph.heap_env ∧
      dfunion      vs1               vs2               state.vs }`

(*
val _ = Hol_datatype`
  assertion =
    Empty
  | DirCell of address => exp => dir_assertion
  | FileCell of exp => exp
  | DescCell of exp => exp => exp
  | DirStreamCell of exp => exp
  | HeapCell of exp => exp
  | VarCell of var => exp
  | ExpCell of exp => exp
  | Exp of exp`

  assertion_semantics : assertion -> (var |-> value) -> instrumented_state set

eval_exp : (var |-> value) exp -> value

val assertion_semantics_def = Define`
  assertion_semantics env Empty = { <| fs = <| root = NONE; address_env = FEMPTY; inode_env = FEMPTY |>
                                     ; ph = <| filedesc_env := FEMPTY; dirstream_env := FEMPTY |>
                                     ; vs = FEMPTY
                                     |> } ∧
  assertion_semantics env (DirCell addr exp dir_assertion)
  assertion_semantics env (FileCell e1 e2) = { is |
    ∃n b.
      eval_exp env e1 = Inode n ∧
      eval_exp env e2 = Byte b ∧
      FLOOKUP is.fs.inode_env n = SOME b } ∧
  assertion_semantics env 


{ assertion language } programming language { assertion language }

val (assertion_semantics_rules,assertion_semantics_ind,assertion_semantics_cases)
assertion includes:
  program expressions
  logical expressions
*)

val _ = export_theory()
