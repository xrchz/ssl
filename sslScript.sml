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
  TFile | TDirectory`

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

val _ = Parse.overload_on("/",``Concat``)

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
  | Val of value set
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
  (eval_prog_exp env pe pv
   ⇒
   eval_exp env (ProgExp pe) {ProgValue pv}) ∧

  (eval_exp env (Val vs) vs) ∧

  (eval_exp env (AddrVal a) {AddressValue a}) ∧

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

val _ = type_abbrev("prog_env",``:var |-> prog_value``)

val _ = type_abbrev("dir_assertion",``:prog_env -> forest set``)

val DEmpty_def = Define`DEmpty env = { [] }`
val _ = Parse.overload_on("∅",``DEmpty``)

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
val _ = Parse.overload_on("+",``DConcat``)

val DContextApplication_def = Define`
  DContextApplication (da1:dir_assertion) addr (da2:dir_assertion) env =
    { subst_forest addr f2 f1 | f1 ∈ da1 env ∧ f2 ∈ da2 env }`

val DPathResolution_def = Define`
  DPathResolution exp env = { ds |
    ∃p ps a.
    eval_exp env exp {PathValue (RelPath p ps,a)} ∧
    EXISTS IS_SOME (MAP (resolve (p::ps) a) ds) }`

val DLift_def = Define`
  DLift f (da1:dir_assertion) da2 env = { ds | f (ds ∈ da1 env) (ds ∈ da2 env) }`
val _ = Parse.overload_on("/\\",``DLift $/\``)
val _ = Parse.overload_on("\\/",``DLift $\/``)
val _ = Parse.overload_on("F",``(K {}):dir_assertion``)
val _ = Parse.overload_on("T",``(K UNIV):dir_assertion``)
val _ = Parse.overload_on("==>",``DLift $==>``)
val _ = Parse.overload_on("<=>",``DLift $<=>``)
val _ = Parse.overload_on("~",``λda:dir_assertion. da ⇒ F``)

val DExists_def = Define`
  DExists (P : α -> dir_assertion) env = { ds | ∃v. ds ∈ (P v) env }`
val _ = Parse.overload_on("?",``DExists``)
val _ = Parse.overload_on("!",``λP : α -> dir_assertion. ¬∃v. ¬(P v)``)

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
   ; vs : var |-> prog_value
   |>`

val _ = type_abbrev("assertion",``:instrumented_state set``)

val Empty_def = Define`
  Empty
    = { <| fs := <| root := NONE; address_env := FEMPTY; inode_env := FEMPTY |>
         ; ph := <| filedesc_env := FEMPTY; dirstream_env := FEMPTY; heap_env := FEMPTY |>
         ; vs := FEMPTY
         |> }`

val DirCell_def = Define`
  DirCell addr path_exp da = { state |
    ∃ap ds.
    FLOOKUP state.fs.address_env addr = SOME (ap,ds) ∧
    eval_exp state.vs path_exp {PathValue ap} ∧
    ds ∈ da state.vs }`

val RootCell_def = Define`
  RootCell da = { state |
    ∃ds. state.fs.root = SOME ds ∧
    ds ∈ da state.vs }`

val FileCell_def = Define`
  FileCell inode_exp bytes_exp env = { state |
   ∃inode bytes.
   FLOOKUP state.fs.inode_env inode = SOME bytes ∧
   eval_exp state.vs inode_exp {ProgValue (Inode inode)} ∧
   eval_exp state.vs bytes_exp {ProgValue (Byte bytes)} }`

val FileDescCell_def = Define`
  FileDescCell fd_exp inode_exp offset_exp = { state |
    ∃fd inode offset.
    0 ≤ offset ∧
    FLOOKUP state.ph.filedesc_env fd = SOME (inode, Num offset) ∧
    eval_exp state.vs fd_exp {ProgValue (Ofaddr fd)} ∧
    eval_exp state.vs inode_exp {ProgValue (Inode inode)} ∧
    eval_exp state.vs offset_exp {ProgValue (Int offset)} }`

val DirStreamCell_def = Define`
  DirStreamCell ds_exp names_exp = { state |
    ∃dirstr ns.
    FLOOKUP state.ph.dirstream_env dirstr = SOME { n | ProgValue(Path(Name n)) ∈ ns } ∧
    eval_exp state.vs ds_exp {ProgValue (Dirstream dirstr)} ∧
    eval_exp state.vs names_exp ns ∧
    (∀v. v ∈ ns ⇒ ∃n. v = ProgValue(Path(Name n))) }`

val HeapCell_def = Define`
  HeapCell addr_exp val_exp = { state |
    ∃addr v.
    0 ≤ addr ∧
    FLOOKUP state.ph.heap_env (Num addr) = SOME v ∧
    eval_exp state.vs addr_exp {ProgValue (Int addr)} ∧
    eval_exp state.vs val_exp {ProgValue (Int v)} }`

(* Ramana: Why can't we just use ExpCell (ProgVar v) for this? *)
val VarCell_def = Define`
  VarCell var val_exp = { state |
    ∃v.
    FLOOKUP state.vs var = SOME v ∧
    eval_exp state.vs val_exp {ProgValue v} }`

val ExpCell_def = Define`
  ExpCell prog_exp exp = { state |
    ∃thevalue.
    eval_prog_exp state.vs prog_exp thevalue ∧
    eval_exp state.vs exp {ProgValue thevalue} }`

val Exp_def = Define`
  Exp exp = { state | state | eval_exp state.vs exp {ProgValue (Bool T)} }`

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
      dfunion      vs1               vs2               state.vs ∧
      <| fs:=fs1; ph:=ph1; vs:=vs1 |> ∈ a1 ∧
      <| fs:=fs2; ph:=ph2; vs:=vs2 |> ∈ a2 }`
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
    SomeVarCell var = ∃v. (VarCell var (Val {ProgValue v}))`

val Somewhere_def = Define`
  Somewhere (da: dir_assertion) =
    ∃x. DContextApplication T x da`

val SomewhereTop_def = Define`
    SomewhereTop (da: dir_assertion) = DConcat T da`

val CompleteTree_def = Define`
  CompleteTree = ¬(∃x. (Somewhere (DExp (AddrVal x))))`

(* Ramana: Do you require some variable to bind v in the program environment? *)
val Entry_def = Define`
  Entry name_exp =
    ((DDirectory name_exp T) ∨
		 (∃v. DFileLink name_exp (Val {ProgValue v})))`

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

(* mkdir *)
(* Ramana:
   All the lowercase names here (r,p,b,a,v,c,path) are HOL variables.
   mkdir is schematic in them - any one of those variables can be instantiated with another HOL term.
   r, path, and v are of type var. they are program variables, and are affected by the * operator:
     if the same one appears in more than one starred conjunct, the triple becomes vacuous, since
     the star is ensuring all the program variables are disjoint between assertions.
   c is of type value set. it is a logical variable standing for whatever set of forests you want.
   p, b, and a are of type path.
   I figure the axiom is really a schema for any particular path names you want to put in those places,
   so the axiom talks about literal paths but we put a HOL variable for the path name.
*)
val mkdir = ``
    (SomeVarCell r
     *
     VarCell path (ProgExp (Lit (Path p) / Lit (Path b) / Lit (Path a)))
     *
     DirCell v (ProgExp (Lit (Path p)))
       (DDirectory (ProgExp (Lit (Path b)))
         (DExp (Val c) ∧ NameNotHere (ProgExp (Lit (Path a)))))

    ,Mkdir r path

    ,VarCell r (ProgExp (Lit (Int 0)))
     *
     VarCell path (ProgExp (Lit (Path p) / Lit (Path b) / Lit (Path a)))
     *
     DirCell v (ProgExp (Lit (Path p)))
       (DDirectory (ProgExp (Lit (Path b)))
         (DExp (Val c)
          +
          DDirectory (ProgExp (Lit (Path a))) ∅))
    )``

(* mkdir, directly under root case *)
val mkdir_root =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 2))))
		(RootCell (Conjunction (DExp (Var 3)) (NameNotThere (ProgExp (ProgVar 2))))))),
    (Mkdir 0 1),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 2))))
		(RootCell (DConcat (DExp (Var 3)) (DDirectory (ProgExp (ProgVar 2)) Empty)))))

(* rename, dir, move, target not exists *)
val rename_dir_move_not_exist =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 5) (Concat (ProgVar 6) (ProgVar 7)))))
		      (Star (DirCell 8 (ProgExp (ProgVar 2)) (DDirectory (ProgExp (ProgVar 3))
									 (DConjunction (DExp (Var 9))
										       CompleteTree)))
			    (DirCell 10 (ProgExp (ProgVar 5)) (DDirectory (ProgExp (ProgVar 6))
									  (DConjunction (DExp (Var 11))
											(NameNotThere (ProgExp (ProgVar 7)))))))))),
    (Rename 0 1 4),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 5) (Concat (ProgVar 6) (ProgVar 7)))))
		      (Star (DirCell 8 (ProgExp (ProgVar 2)) DEmpty)
			    (DirCell 10 (ProgExp (ProgVar 5)) (DDirectory (ProgExp (ProgVar 6))
									  (DConcat (DExp (Var 11))
										   (DDirectory (ProgExp (ProgVar 3))
											       (DExp (Var 9))))))))))

(* rename, dir, move, targe not exists, under root *)
val rename_dir_move_not_exist_root =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 5))))
		      (Star (DirCell 6 (ProgExp (ProgVar 2)) (DDirectory (ProgExp (ProgVar 3))
									 (DConjunction (DExp (Var 7))
										       CompleteTree)))
			    (RootCell (DConjunction (DExp (Var 8)) (NameNotThere (ProgExp (ProgVar 5))))))))),
    (Rename 0 1 4),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 5))))
		      (Star (DirCell 6 (ProgExp (ProgVar 2)) DEmpty)
			    (RootCell (DConcat (DExp (Var 8)) (DDirectory (ProgExp (ProgVar 3))
									  (DExp (Var 7)))))))))

(* rename, dir, target not exists *)
val rename_dir_not_exist =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (Concat (ProgVar 3) (ProgVar 4)))))
		(Star (VarCell 5 (ProgExp (Concat (ProgVar 2) (Concat (ProgVar 3) (ProgVar 6)))))
		      (DirCell 7 (ProgExp (ProgVar 2)) (DDirectory (ProgExp (ProgVar 3))
								   (DConcat (DDirectory (ProgExp (ProgVar 4))
											(DConjunction (DExp (Var 8))
												      CompleteTree))
									    (DConjunction (DExp (Var 9))
											  (NameNotThere (ProgExp (ProgVar 6)))))))))),
    (Rename 0 1 5),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (Concat (ProgVar 3) (ProgVar 4)))))
		(Star (VarCell 5 (ProgExp (Concat (ProgVar 2) (Concat (ProgVar 3) (ProgVar 6)))))
		      (DirCell 7 (ProgExp (ProgVar 2)) (DDirectory (ProgExp (ProgVar 3))
								   (DConcat (DExp (Var 9))
									    (DDirectory (ProgExp (ProgVar 6))
											(DExp (Var 8)))))))))

(* rename, dir, target not exist, root *)
val rename_dir_not_exist_root =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 2))))
		(Star (VarCell 3 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 4))))
		      (RootCell (DConcat (DDirectory (ProgExp (ProgVar 2)) (DConjunction (DExp (Var 5)) CompleteTree))
					 (DConjunction (DExp (Var 6)) (NameNotThere (ProgExp (ProgVar 4))))))))),
    (Rename 0 1 3),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 2))))
		(Star (VarCell 3 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 4))))
		      (RootCell (DConcat (DExp (Var 6)) (DDirectory (ProgExp (ProgVar 4)) (DExp (Var 5))))))))

(* rename: dir, target exists *)
val rename_move_dir_exist =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 5) (ProgVar 6))))
		      (Star (DirCell 7 (ProgExp (ProgVar 2)) (DDirectory (ProgExp (ProgVar 3))
									 (DConjunction (DExp (Var 8))
										       CompleteTree)))
			    (DirCell 9 (ProgExp (ProgVar 5)) (DDirectory (ProgExp (ProgVar 6))
									 DEmpty)))))),
    (Rename 0 1 4),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 5) (ProgVar 6))))
		      (Star (DirCell 7 (ProgExp (ProgVar 2)) DEmpty)
			    (DirCell 9 (ProgExp (ProgVar 5)) (DDirectory (ProgExp (ProgVar 3))
									 (DExp (Var 8))))))))

(* rename: move, file, target not exist *)
val rename_move_file_not_exist =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 5) (Concat (ProgVar 6) (ProgVar 7)))))
		      (Star (DirCell 8 (ProgExp (ProgVar 2)) (DFileLink (ProgExp (ProgVar 3)) (ProgExp (ProgVar 9))))
			    (DirCell 10 (ProgExp (ProgVar 5)) (DDirectory (ProgExp (ProgVar 6))
									  (DConjunction (DExp (Var 11))
											(NameNotThere (ProgExp (ProgVar 7)))))))))),
    (Rename 0 1 4),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 5) (Concat (ProgVar 6) (ProgVar 7)))))
		      (Star (DirCell 8 (ProgExp (ProgVar 2)) DEmpty)
			    (DirCell 10 (ProgExp (ProgVar 5)) (DDirectory (ProgExp (ProgVar 6))
									  (DConcat (DExp (Var 11))
										   (DFileLink (ProgExp (ProgVar 7)) (ProgExp (ProgVar 9))))))))))

(* rename: move, file, target not exists under root *)
val rename_move_file_not_exist_root =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 5))))
		      (Star (DirCell 6 (ProgExp (ProgVar 2)) (DFileLink (ProgExp (ProgVar 3)) (ProgExp (ProgVar 7))))
			    (RootCell (DConjunction (DExp (Var 8)) (NameNotThere (ProgExp (ProgVar 5))))))))),
    (Rename 0 1 4),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 5))))
		      (Star (DirCell 6 (ProgExp (ProgVar 2)) DEmpty)
			    (RootCell (DConcat (DExp (Var 8)) (DFileLink (ProgExp (ProgVar 5)) (ProgExp (ProgVar 7)))))))))

(* rename: file, target not exist *)
val rename_file_not_exist =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (Concat (ProgVar 3) (ProgVar 4)))))
		(Star (VarCell 5 (ProgExp (Concat (ProgVar 2) (Concat (ProgVar 3) (ProgVar 6)))))
		      (DirCell 7 (ProgExp (ProgVar 2)) (DDirectory (ProgExp (ProgVar 3))
								   (DConcat (DFileLink (ProgExp (ProgVar 4)) (ProgExp (ProgVar 8)))
									    (DConjunction (DExp (Var 9)) (NameNotThere (ProgExp (ProgVar 6)))))))))),
    (Rename 0 1 5),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (Concat (ProgVar 3) (ProgVar 4)))))
		(Star (VarCell 5 (ProgExp (Concat (ProgVar 2) (Concat (ProgVar 3) (ProgVar 6)))))
		      (DirCell 7 (ProgExp (ProgVar 2)) (DDirectory (ProgExp (ProgVar 3))
								   (DConcat (DExp (Var 9)) (DFileLink (ProgExp (ProgVar 6)) (ProgExp (ProgVar 8)))))))))

(* rename: file, target not exist under root *)
val rename_file_not_exist_root =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 2))))
		(Star (VarCell 3 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 4))))
		      (RootCell (DConcat (DFileLink (ProgExp (ProgVar 2)) (ProgExp (ProgVar 5)))
					 (DConjunction (DExp (Var 6)) (NameNotThere (ProgExp (ProgVar 4))))))))),
    (Rename 0 1 3),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 2))))
		(Star (VarCell 3 (ProgExp (Concat (Lit (Path (AbsPath []))) (ProgVar 4))))
		      (RootCell (DConcat (DExp (Var 6)) (DFileLink (ProgExp (ProgVar 4)) (ProgExp (ProgVar 5))))))))

(* rename: file, target exists *)
val rename_file_exist =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 5) (ProgVar 6))))
		      (Star (DirCell 7 (ProgExp (ProgVar 2)) (DFileLink (ProgExp (ProgVar 3)) (ProgExp (ProgVar 8))))
			    (DirCell 9 (ProgExp (ProgVar 5)) (Conjunction (DFileLink (ProgExp (ProgVar 6)) (ProgExp (ProgVar 10)))
									  (Neg (Exp (Equal (ProgExp (ProgVar 8)) (ProgExp (ProgVar 10))))))))))),
    (Rename 0 1 4),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 5) (ProgVar 6))))
		      (Star (DirCell 7 (ProgExp (ProgVar 2)) DEmpty)
			    (DirCell 9 (ProgExp (ProgVar 5)) (DFileLink (ProgExp (ProgVar 6)) (ProgExp (ProgVar 8))))))))

(* rename: file, target exist, same inode *)
val rename_file_exist_same =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 5) (ProgVar 6))))
		      (Star (DirCell 7 (ProgExp (ProgVar 2)) (DFileLink (ProgExp (ProgVar 3)) (ProgExp (ProgVar 8))))
			    (DirCell 9 (ProgExp (ProgVar 5)) (Conjunction (DFileLink (ProgExp (ProgVar 6)) (ProgExp (ProgVar 8))))))))),
    (Rename 0 1 4),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 5) (ProgVar 6))))
		      (Star (DirCell 7 (ProgExp (ProgVar 2)) (DFileLink (ProgExp (ProgVar 3)) (ProgExp (ProgVar 8))))
			    (DirCell 9 (ProgExp (ProgVar 5)) (Conjunction (DFileLink (ProgExp (ProgVar 6)) (ProgExp (ProgVar 8)))))))))

(* rename: same paths *)
val rename_same =
    (Star (SomeVarCell 0)
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		      (DirCell 5 (ProgExp (ProgVar 2)) (DConjuntion (DExp (Var 6)) (Entry (ProgExp (ProgVar 3)))))))),
    (Rename 0 1 4),
    (Star (VarCell 0 (ProgExp (Lit (Int 0))))
	  (Star (VarCell 1 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		(Star (VarCell 4 (ProgExp (Concat (ProgVar 2) (ProgVar 3))))
		      (DirCell 5 (ProgExp (ProgVar 2)) (DExp (Var 6))))))

(*
Val _ = Hol_datatype`
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
