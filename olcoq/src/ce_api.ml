open Ol
open Constr
open Pp
open Context
open Typing
(* Example: simple, no-op tactic + print *)
module PV = Proofview

let decomp_term sigma (c : Constr.t) =
  Constr.kind (EConstr.Unsafe.to_constr (Termops.strip_outer_cast sigma (EConstr.of_constr c)))

let lib_constr n = lazy (UnivGen.constr_of_monomorphic_global (Global.env ()) @@ Coqlib.lib_ref n)

let find_reference = Coqlib.find_reference [@ocaml.warning "-3"]

let msg_in_tactic str : unit PV.tactic =
  PV.tclLIFT (PV.NonLogical.make (fun () ->
      Feedback.msg_warning (Pp.str str)))

let printHello : unit PV.tactic =
  let open PV.Notations in
  msg_in_tactic "hello" >>= fun () ->
  Tacticals.tclIDTAC


let printTestOL : unit PV.tactic =
  let open PV.Notations in
  msg_in_tactic show_ol >>= fun () ->
  Tacticals.tclIDTAC

let identity (t: Evd.econstr) (h: Names.Id.t): unit PV.tactic =
  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.pf_env gl in
    let sigma = Tacmach.project gl in
    let t2 = EConstr.Unsafe.to_constr t in
    let typ = type_of env sigma t in
    let typ_c = EConstr.Unsafe.to_constr (snd typ) in
    let id = Constr.mkLambda(nameR (Names.Id.of_string "x"), typ_c, Constr.mkRel 1) in
    let idt = Constr.mkApp (id, [|t2|]) in
    let eq_t_idt = Constr.mkApp (Lazy.force (lib_constr "core.eq.type"), [|typ_c; t2; idt|]) in
    let eq_refl = Constr.mkApp (Lazy.force (lib_constr "core.eq.refl"), [|eq_t_idt; t2|]) in
    let eq_refl = EConstr.of_constr eq_refl in
    Tacticals.tclTHENLIST [
            Tactics.pose_proof (Names.Name.mk_name h) eq_refl;
          ]
  end

let identity2 (t: Evd.econstr) : unit PV.tactic =
  Proofview.Goal.enter begin fun gl ->
    let _concl = Proofview.Goal.concl gl in
    let concl = EConstr.Unsafe.to_constr t in
    let sigma = Tacmach.project gl in
    let t = decomp_term sigma concl in
    match t with
    | App (c, [|typ; tl; tr|]) ->
      let idt = Constr.mkApp (c, [|typ; tl; tr|]) in
      let idt = EConstr.of_constr idt in
      Tacticals.tclTHENLIST [
              Tactics.change_concl idt;
            ]
    | _ -> 
      let msg = str "Failed match" in
      Tacticals.tclFAIL msg
  end








(* Reification*)


let (===) = Constr.equal

module Constrhash = Hashtbl.Make
  (struct type t = constr
          let equal = eq_constr_nounivs
          let hash = Constr.hash
   end)


let decomp_term sigma (c : Constr.t) =
  Constr.kind (EConstr.Unsafe.to_constr (Termops.strip_outer_cast sigma (EConstr.of_constr c)))

let lib_constr n = lazy (UnivGen.constr_of_monomorphic_global (Global.env ()) @@ Coqlib.lib_ref n)

let eq = lib_constr "core.eq.type"
let bool_typ    = lib_constr "core.bool.type"
let trueb  = lib_constr "core.bool.true"
let falseb = lib_constr "core.bool.false"
let andb   = lib_constr "core.bool.andb"
let orb    = lib_constr "core.bool.orb"
let xorb   = lib_constr "core.bool.xorb"
let negb   = lib_constr "core.bool.negb"


let quote (env : Environ.env) sigma (e : Constr.t)  =

  let trueb = Lazy.force trueb in
  let falseb = Lazy.force falseb in
  let andb = Lazy.force andb in
  let orb = Lazy.force orb in
  let xorb = Lazy.force xorb in
  let negb = Lazy.force negb in
  (* hashtable from int to types*)
  let counter = ref 0 in
  let map: (int, types) Hashtbl.t = Hashtbl.create 50 in
  let revmap = Constrhash.create 50 in

  let rec aux e = match decomp_term sigma e with
  | App (head, args) ->
    if head === andb && Array.length args = 2 then
      new_and [aux args.(0); aux args.(1)]
    else if head === orb && Array.length args = 2 then
      new_or [aux args.(0); aux args.(1)]
    else if head === xorb && Array.length args = 2 then
      let a0 = aux args.(0) in
      let a1 = aux args.(1) in
      new_or [new_and [a0; new_neg a1]; new_and [new_neg a0; a1]]
    else if head === negb && Array.length args = 1 then
      new_neg (aux args.(0))
    else (
      match Constrhash.find_opt revmap e with
      | Some v -> v
      | None ->
        (incr counter;
        let v = new_variable (!counter) in
        Constrhash.add revmap e v;
        Hashtbl.add map !counter e;
        v)
    )
  (*| Case (info, _, _, _, _, arg, pats) ->
    let is_bool =
      let i = info.ci_ind in
      Names.Ind.CanOrd.equal i (Lazy.force ind)
    in
    if is_bool then
      Ifb ((aux arg), (aux (snd pats.(0))), (aux (snd pats.(1))))
    else
      Var (Env.add env e)*)
  | _ ->
    if e === falseb then new_literal false
    else if e === trueb then new_literal true
    else (
      match Constrhash.find_opt revmap e with
      | Some v -> v
      | None ->
        (incr counter;
        let v = new_variable (!counter) in
        Constrhash.add revmap e v;
        Hashtbl.add map !counter e;
        v)
    )
  in
  aux e, map


let unquote (f: formula) (map: (int, types) Hashtbl.t) : Constr.t =
  let trueb = Lazy.force trueb in
  let falseb = Lazy.force falseb in
  let andb = Lazy.force andb in
  let orb = Lazy.force orb in
  let negb = Lazy.force negb in

  let rec aux f = match f with
  | Variable r -> Hashtbl.find map r.id
  | Neg r -> Constr.mkApp (negb, [|aux r.child|])
  | Or r -> (match r.children with
    | [] -> falseb
    | head :: tail -> List.fold_left (fun acc x -> 
      Constr.mkApp (orb, [|acc; aux x|])) (aux head) tail
    )
  | And r -> (match r.children with
    | [] -> trueb
    | head :: tail -> List.fold_left (fun acc x -> 
      Constr.mkApp (andb, [|acc; aux x|])) (aux head) tail
    )
  | Literal r -> if r.b then trueb else falseb
  in
  aux f



let ol_normal (t: Evd.econstr) (h: Names.Id.t): unit PV.tactic =
  let bool = Lazy.force bool_typ in

  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.pf_env gl in
    let sigma = Tacmach.project gl in
    let t2 = EConstr.Unsafe.to_constr t in
    let typ = type_of env sigma t in
    let typ_c = EConstr.Unsafe.to_constr (snd typ) in
    if typ_c === bool then
      let formula, map = quote env sigma t2 in
      let normal_form = reduced_form formula in
      let res = unquote normal_form map in
      let res  = EConstr.of_constr res in
    Tacticals.tclTHENLIST [
            Tactics.pose_tac (Names.Name.mk_name h) res;
          ]
    else
      let typ_str = Pp.string_of_ppcmds (Printer.pr_constr_env env sigma typ_c) in
      let msg = str "Not a boolean expression: " ++ str typ_str in
      Tacticals.tclFAIL msg
  end