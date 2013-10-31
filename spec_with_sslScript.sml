(* * prelude *)


(*
Interactive use:

val _ = app load ["numLib","finite_mapTheory", "stringTheory", "unwindLib","prim_recTheory","sumTheory"]; (* unwindLib for tactics; prim_rec for measure *)

val _ = app load ["fs_specTheory","dir_treeTheory"]

val _ = app load ["sslTheory"]

val ready = "ready";

(* DONT do this if working with ssl; I find ASCII easier to read than (single width) unicode *)
(* val _ = set_trace "Unicode" 0; *)

*)


(* 
HOL_Interactive.toggle_quietdec()
*)

open HolKernel Parse boolLib proofManagerLib bossLib

open numLib finite_mapTheory stringTheory unwindLib prim_recTheory sumTheory pairTheory pred_setTheory

open fs_specTheory dir_treeTheory

open sslTheory 

(* 
HOL_Interactive.toggle_quietdec()
*)


(* * spec_with_ssl *)

val _ = new_theory "spec_with_ssl";

(* 

We want to set up the connection between Hoare triples from ssl, and transitions
from fs_spec.

Hoare triples describe triples: (s,cmd,s')

Transitions describe tiples: (t,lbl,(t',ev))

The cmd is a program command, and can contain free program vars (which are
constrained by the state s). The cmd also contains a reference to a variable r,
which holds the result of the cmd (>=0 for success, or -1 for error; commands
such as stat etc, which return non-integers, have not yet been formalized). The
state s also contains a global errno, which holds an integer indentifying the
particular error that occurred.

The transition system is somewhat simpler: the value ev is either an error, or a
return value. Return values can be ints, stats, etc. - see ret_value type
definition in fs_specScript.sml

We want to map from Hoare triples to transitions. 

  * To map s to t, we keep only the instrumented filesystem part of s, and we
    "assemble" this into a directory tree (assemble needs to be defined).

  * To map the cmd to a label, suppose the cmd is of the form (Mkdir r p). r is
    a program var which will hold the result of the cmd. p is a program
    variable, but the state s will constrain this to be a path (essentially a
    list of names). The resulting label is MKDIR(f p,dummy_perms), where f maps
    paths in ssl to strings (insert / at beginning if absolute path and between
    entries), and dummy_perms is some dummy value for permissions (we don't deal
    with permissions yet).

  * To map s' to t', we need knowledge of the program variable r. Then s'
    constrains r to be either 0 (for success) or -1 (for error; at the moment
    all triples have r=0). t' is constructed from s' in the same way that t is
    constructed from s. And the return value/error ev is "similarly constructed"
    from the state s' (at the moment it is always None1, corresponding to a
    successful call, but eventually it will have to take account of the errno,
    and different possible return types).

*)


(* this belongs in fs_specScript *)

  (* s0 is impl state *)
val fs_lbl_of_def = Define `
fs_lbl_of ops s0 cwd lbl = (
    let pp = process_path ops s0 cwd in
     case lbl of
      LINK (s,d) => (FS_LINK(pp s, pp d))
    | MKDIR (s,p) => (FS_MKDIR(pp s, p))
    | OPEN (p,fs) => (FS_OPEN(pp p, fs))
    | READ (p,i,j) => (FS_READ(pp p, i, j))
    | READDIR p => (FS_READDIR(pp p))
    | RENAME (s,d) => (FS_RENAME(pp s, pp d))
    | RMDIR p => (FS_RMDIR(pp p))
    | STAT p => (FS_STAT(pp p))
    | SYMLINK (s,d) => failwith "FIXME" (* (symlink ops s d) *)
    | TRUNCATE (p,l) => (FS_TRUNCATE(pp p,l))
    | UNLINK p => (FS_UNLINK(pp p))
    | WRITE (p,ofs,bs,len) => (FS_WRITE(pp p,ofs,bs,len)))
`;

val dummy_perms_def = Define `
dummy_perms = (ARB:file_perm)
`;

(* GIAN: This needs termination proof *)
val string_of_path_def = tDefine`
  (string_of_path EmptyPath = "") ∧
  (string_of_path (RelPath name rpath) = STRCAT name (string_of_list rpath)) ∧
  (string_of_path (AbsPath rpath) = STRCAT "/" (string_of_list rpath)) ∧
  (string_of_list names = string_of_list_fold "" names) ∧
  (string_of_list_fold acc [] = acc) ∧
  (string_of_list_fold acc (n::ns) = string_of_list_fold (STRCAT (STRCAT acc "/") n) ns)`

(* GIAN: This is dummy so that I can attempt typechecking its dependencies *)
val string_of_path_dummy_def = Define`string_of_path (p: path) = (ARB: string)`

(* GIAN: relation mapping ssl directory to entrya *)
val entrya_of_directory_def = Hol_reln`
  (* GIAN: Could I just say?: entry_of_directory (name, (Flie inode)) (FileLink (name, inode)) ⇔ T *)
  (name = name' ∧
   inode = inode'
   ⇒ entrya_of_directory (name, (File (Inode_ref inode))) (FileLink name' inode')) ∧
  
  (name = name' ∧
   entrya_of_directory_forests es ds
   ⇒ entrya_of_directory (name, (Dir es)) (Directory name' ds)) ∧

  (entrya_of_directory e d ∧
   entrya_of_directory_forests es ds
   ⇒ entrya_of_directory_forests (e::es) (d::ds))`

val iref_inode_match_def = Define`
  iref_inode_match (cs: contents_heap) ih (Inode_ref i) = 
    ∃ bs cstr. 
    fmap_lookup cs (Inode_ref i) = SOME cstr ∧
    FLOOKUP ih i = SOME bs ∧
    IMPLODE cstr = bs`

(* GIAN: Map the inode heap to inode_ref contents *)
val file_list_of_inode_heap_def = Hol_reln`
  (EVERY (iref_inode_match cs ih) (fmap_dom cs)
   ⇒ file_list_of_inode_heap cs ih)`

(* GIAN: Map commands to labels *)
val label_of_command_def = Define`
  (label_of_command (s: instrumented_state) (Mkdir pvar) = { MKDIR (pstr, dummy_perms) | pstr, dummy_perms |
     ∃ pval.
     FLOOKUP s.env pvar = SOME (Path pval) ∧
     string_of_path pval = pstr }) ∧
  
  (label_of_command s (Rename oldpvar newpvar) = { RENAME (spath, dpath) |
    ∃ oldpval newpval.
    FLOOKUP s.env oldpvar = SOME (Path oldpval) ∧
    FLOOKUP s.env newpvar = SOME (Path newpval) ∧
    string_of_path oldpval = spath ∧
    string_of_path newpval = dpath })`
    
val retval_to_progval_def = Define`retval_to_progval (v: ret_value) = (ARB: prog_value)`

(* GIAN: Map a spec state transition to an ssl command interpretation *)
val fs_lbl_trans_embed_def = Define`
  fs_lbl_trans_embed (s, cmd) = { state |
    ∃ lbl lbl' es ds ds' cs ops fs fs' ev err.
    ops = dirtree$ops1 ∧
    (* the input state must not have any instrumentation here *)
    complete_ifs s.fs ∧
    (* embed instrumented state components to dir_treeScript components *)
    s.fs.root = SOME ds ∧
    entrya_of_directory (Dir es) ds ∧
    file_list_of_inode_heap cs s.fs.inode_env ∧
    fs = <| es1 := es; cs1 := cs |> ∧
    (* map command to label *)
    label_of_command s cmd = lbl ∧
    lbl' = fs_lbl_of ops fs (dest_Some (ops.get_root1 fs)) lbl ∧
    (* transition on the label *)
    finset_mem (fs', ev) (fs_trans ops fs lbl') ∧
    (* return value / error on the variable store *)
    (case ev of
       INL e => 
         FLOOKUP state.env errno = SOME (Error err) ∧ 
         err = e ∧ (* GIAN; currently these are not the same type *)
         FLOOKUP state.env rvalue = SOME (Int -1)
      | INR None1 => (* No value result produced; in this case the rvalue will be 0 *)
         FLOOKUP state.evn rvalue = SOME (Int 0)
      | INR (Some1 v) => (* There is some value result *)
         FLOOKUP state.env rvalue = SOME (value_to_prog_value v)) ∧
    (* directories and files *)
    state.fs.root = SOME ds' ∧
    entrya_of_directory fs'.es1 ds' ∧
    file_list_of_inode_hep fs'.cs1 state.fs.inode_env ∧
    (* let's just enforce this as well (just in case) *)
    complete_ifs state.fs }`


(* FIXME overloading on equals at end of sslTheory causes many problems! *) 

(* val _ = overload_on ("=",Term`min$=`); trying to restore =; doesn't work *)

(*
val string_of_path_def = Define `
string_of_path (p:path) = (ARB:string) (* FIXME *)
`;
*)

val string_of_prog_exp_def = Define `
string_of_prog_exp s (p:var) = (ARB:string) (* FIXME *)
`;

val assemble_def = Define `
assemble (s:instrumented_state) (t:fs1) = (ARB:bool) (* FIXME *)
`;

(* written as a relation, but should probably be a function *)
val map_triple_def = Define `
map_triple (s,cmd,s') (t,lbl,(t',ev)) = ( 
  case cmd of
  | Mkdir r p => (    
    (assemble s t) 
    /\ (lbl = MKDIR(string_of_prog_exp s p,dummy_perms))
    /\ (assemble s' t') 
    /\ (case s' IN (VarI r 0) of 
      (* success case *)
      | T => (case ev of 
        | INL e => F
        | INR None1 => T
        | INR _ => F)
      (* failure case *)
      | F => (case ev of
        | INL e => T (* FIXME and the errno must match *)
        | _ => F)))
  | _ => F)
`;

(* example triple *)
val mkdir = ``
\ p b a c path v r.
    let P = Lit (Path p) in
    let B = Lit (Path b) in
    let A = Lit (Path a) in
    let (C:dir_assertion) = DExp (Vals c) in
    (* Ramana: should we constrain c to only contain ForestValues here? *)
    (SomeVarCell r
     * VarP path (P / B / A)
     * DirCell v (ProgExp P)
         (DDir B ((DLift $/\ ) C (Safe A)))  (* if unicode is turned off, the original doesn't parse   *)
    ,Mkdir r path
    ,VarI r 0
     * VarP path (P / B / A)
     * DirCell v (ProgExp P)
         (DDir B (C  + DDir A ∅))
    )``;

val main_thm_def = Define `
main_thm = (
  ! s cmd s' t lbl t' ev.
  let triples = {
    (s,cmd,s') | 
      ? p b a c path v r. 
        let (u,v,w) = (^mkdir p b a c path v r) in  (* or mkdir_root, or other triples *)
        s IN u /\ (cmd=v) /\ s' IN w }
  in
  let ops = dir_tree$ops1 in
  let lbl' = fs_lbl_of ops t (dest_Some (ops.get_root1 t)) lbl in
  (s,cmd,s') IN triples
  /\ map_triple (s,cmd,s') (t,lbl,(t',ev))
  ==> finset_mem (t',ev) (fs_trans ops t lbl'))
`;


(* * end *)

val _ = export_theory();

(*

Local Variables:
outline-regexp: "^(\\* +[*+.]+ "
fill-column: 80
mode: sml
mode: outline-minor
mode: hi-lock
sml-program-name: "hol"
End:

*)
