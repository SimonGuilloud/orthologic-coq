open Ol
open Constr
open Pp
open Typing
open Util


module PV = Proofview


let counter_bug = ref 0
let checkfail () = 
  incr counter_bug;
  if !counter_bug > 30 then failwith "bug"



(* Coq helpers *)
let decomp_term sigma (c : Constr.t) =
  Constr.kind (EConstr.Unsafe.to_constr (Termops.strip_outer_cast sigma (EConstr.of_constr c)))

let lib_constr n = lazy (UnivGen.constr_of_monomorphic_global (Global.env ()) @@ Coqlib.lib_ref n)

let find_reference = Coqlib.find_reference [@ocaml.warning "-3"]

let msg_in_tactic str : unit PV.tactic =
  PV.tclLIFT (PV.NonLogical.make (fun () ->
      Feedback.msg_warning (Pp.str str)))

let (===) = Constr.equal



(* Hash table with coq terms as keys *)
module Constrhash = Hashtbl.Make
  (struct type t = constr
          let equal = eq_constr_nounivs
          let hash = Constr.hash
   end)



(* Reference Theorems *)

let eq = lib_constr "core.eq.type"
let bool_typ    = lib_constr "core.bool.type"
let trueb  = lib_constr "core.bool.true"
let falseb = lib_constr "core.bool.false"
let andb   = lib_constr "core.bool.andb"
let orb    = lib_constr "core.bool.orb"
let xorb   = lib_constr "core.bool.xorb"
let negb   = lib_constr "core.bool.negb"
let eqb   = lib_constr "core.bool.eqb"



let tpair = lib_constr "olplugin.tpair"
let left_true_or = lib_constr "olplugin.left_true_or"
let right_true_or = lib_constr "olplugin.right_true_or"
let left_neg_or = lib_constr "olplugin.left_neg_or"
let right_neg_or = lib_constr "olplugin.right_neg_or"
let left_and_or = lib_constr "olplugin.left_and_or"
let right_and_or = lib_constr "olplugin.right_and_or"
let left_or_or_1 = lib_constr "olplugin.left_or_or_1"
let left_or_or_2 = lib_constr "olplugin.left_or_or_2"
let right_or_or_1 = lib_constr "olplugin.right_or_or_1"
let right_or_or_2 = lib_constr "olplugin.right_or_or_2"
let contract_or_1 = lib_constr "olplugin.contract_or_1"
let contract_or_2 = lib_constr "olplugin.contract_or_2"

let tpair_to_eq = lib_constr "olplugin.tpair_to_eq"



(* Reification in ol.ml formulas*)


let revmap_ol_formula = Constrhash.create 50
let map_var_types: (int, types) Hashtbl.t = Hashtbl.create 50
let counter = ref 0

let quote (env : Environ.env) sigma (e : Constr.t)  =

  let trueb = Lazy.force trueb in
  let falseb = Lazy.force falseb in
  let andb = Lazy.force andb in
  let orb = Lazy.force orb in
  let xorb = Lazy.force xorb in
  let negb = Lazy.force negb in

  let rec aux e = match decomp_term sigma e with
  | App (head, args) ->
    if head === andb && Array.length args = 2 then
      let a0 = aux args.(0) in
      let a1 = aux args.(1) in
      new_and [a0; a1]
    else if head === orb && Array.length args = 2 then
      let a0 = aux args.(0) in
      let a1 = aux args.(1) in
      new_or [a0; a1]
    else if head === xorb && Array.length args = 2 then
      let a0 = aux args.(0) in
      let a1 = aux args.(1) in
      new_or [new_and [a0; new_neg a1]; new_and [new_neg a0; a1]]
    else if head === negb && Array.length args = 1 then
      new_neg (aux args.(0))
    else (
      match Constrhash.find_opt revmap_ol_formula e with
      | Some v -> v
      | None ->
        (incr counter;
        let v = new_variable (!counter) in
        Constrhash.add revmap_ol_formula e v;
        Hashtbl.add map_var_types !counter e;
        v)
    )
  | _ ->
    if e === falseb then new_literal false
    else if e === trueb then new_literal true
    else (
      match Constrhash.find_opt revmap_ol_formula e with
      | Some v -> v
      | None ->
        (incr counter;
        let v = new_variable (!counter) in
        Constrhash.add revmap_ol_formula e v;
        Hashtbl.add map_var_types !counter e;
        v)
    )
  in
  aux e


let unquote (f: formula) : Constr.t =
  let trueb = Lazy.force trueb in
  let falseb = Lazy.force falseb in
  let andb = Lazy.force andb in
  let orb = Lazy.force orb in
  let negb = Lazy.force negb in

  let rec aux f = match f with
  | Variable r -> Hashtbl.find map_var_types r.id
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




(* Formulas used for the proof-producing certification algorithm *)
type cert_formula = 
| CertVariable of { polarity : bool; id : int;
      unique_key : int; lt_cache : (int, types option) Hashtbl.t; coqterm : types }
| CertNeg of { child: cert_formula; 
      unique_key : int; lt_cache : (int, types option) Hashtbl.t; coqterm : types }
| CertOr of { c1: cert_formula; c2:cert_formula; 
      unique_key : int; lt_cache : (int, types option) Hashtbl.t; coqterm : types }
| CertAnd of { c1: cert_formula; c2:cert_formula; 
      unique_key : int; lt_cache : (int, types option) Hashtbl.t; coqterm : types }
| CertLiteral of { b : bool; 
      unique_key : int; lt_cache : (int, types option) Hashtbl.t; coqterm : types }

let tot_cert = ref 0
let tot_id = ref 0


(* This is of course better, but it's a little cheating for the benchmarks...*)
  (*let revmap : (cert_formula Constrhash.t) = Constrhash.create 50*)

(* helpers for cert_formula *)
let new_formulas (env : Environ.env) sigma (e:(types array)) : cert_formula array =
  let trueb = Lazy.force trueb in
  let falseb = Lazy.force falseb in
  let andb = Lazy.force andb in
  let orb = Lazy.force orb in
  let negb = Lazy.force negb in

  let revmap : (cert_formula Constrhash.t) = Constrhash.create 50 in

  let rec aux e =
    incr tot_cert;
    let key = !tot_cert in
    match decomp_term sigma e with
    | App (head, args) when head === andb && Array.length args = 2 ->
      CertAnd {c1 = aux args.(0); c2 = aux args.(1); 
        unique_key = key; lt_cache = Hashtbl.create 50; coqterm = e}
    | App (head, args) when head === orb && Array.length args = 2 ->
      CertOr {c1 = aux args.(0); c2 = aux args.(1); 
        unique_key = key; lt_cache = Hashtbl.create 50; coqterm = e}
    | _ when e === trueb -> CertLiteral {b = true; 
        unique_key = key; lt_cache = Hashtbl.create 50; coqterm = e}
    | _ when e === falseb -> CertLiteral {b = false; 
        unique_key = key; lt_cache = Hashtbl.create 50; coqterm = e}
    | App (head, args) when head === negb && Array.length args = 1 ->
      CertNeg {child = aux args.(0); 
        unique_key = key; lt_cache = Hashtbl.create 50; coqterm = e}
    | _ -> match Constrhash.find_opt revmap e with
      | Some v -> v
      | None ->
        (incr tot_id;
        let id = !tot_id in
        let v = CertVariable {polarity = true; id = id; 
          unique_key = key; lt_cache = Hashtbl.create 50; coqterm = e} in
        Constrhash.add revmap e v;
        v)

  in Array.map aux e

let get_cert_key (f: cert_formula) : int =
  match f with
  | CertVariable {unique_key = k; _} -> k
  | CertNeg {unique_key = k; _} -> k
  | CertOr {unique_key = k; _} -> k
  | CertAnd {unique_key = k; _} -> k
  | CertLiteral {unique_key = k; _} -> k

let get_coq_term (f: cert_formula) : types =
  match f with
  | CertVariable {coqterm = c; _} -> c
  | CertNeg {coqterm = c; _} -> c
  | CertOr {coqterm = c; _} -> c
  | CertAnd {coqterm = c; _} -> c
  | CertLiteral {coqterm = c; _} -> c


let get_lt_cache_cert cf =
  match cf with
  | CertVariable {lt_cache = c; _} -> c
  | CertNeg {lt_cache = c; _} -> c
  | CertOr {lt_cache = c; _} -> c
  | CertAnd {lt_cache = c; _} -> c
  | CertLiteral {lt_cache = c; _} -> c

let lt_cached_cert cf1 cf2 =
  Hashtbl.find_opt (get_lt_cache_cert cf1) (get_cert_key cf2)


let set_lt_cached_cert cf1 cf2 res =
  Hashtbl.add (get_lt_cache_cert cf1) (get_cert_key cf2) res


let cert_formula_to_string (f: cert_formula) : string =
  let rec aux f = match f with
  | CertVariable {id = i; _} -> Printf.sprintf "Var(%d)" i
  | CertNeg {child = c; _} -> Printf.sprintf "Neg(%s)" (aux c)
  | CertOr {c1 = c1; c2 = c2; _} -> Printf.sprintf "Or(%s, %s)" (aux c1) (aux c2)
  | CertAnd {c1 = c1; c2 = c2; _} -> Printf.sprintf "And(%s, %s)" (aux c1) (aux c2)
  | CertLiteral {b = b; _} -> Printf.sprintf "Lit(%b)" b
  in aux f



(* Returns the first option if it is defined, the second otherwise *)
let first_some opt1 opt2 =
  match opt1 with
  | Some _ -> opt1
  | None -> Lazy.force opt2 

(* Produces a proof that f1 = f2, using the laws of orthologic.
   If no such proof is found, return None. *)
let proof_ol (f1: cert_formula) (f2: cert_formula): types option =
  let left_true_or = Lazy.force left_true_or in
  let right_true_or = Lazy.force right_true_or in
  let left_neg_or = Lazy.force left_neg_or in
  let right_neg_or = Lazy.force right_neg_or in
  let left_and_or = Lazy.force left_and_or in
  let right_and_or = Lazy.force right_and_or in
  let left_or_or_1 = Lazy.force left_or_or_1 in
  let left_or_or_2 = Lazy.force left_or_or_2 in
  let right_or_or_1 = Lazy.force right_or_or_1 in
  let right_or_or_2 = Lazy.force right_or_or_2 in
  let contract_or_1 = Lazy.force contract_or_1 in
  let contract_or_2 = Lazy.force contract_or_2 in

  let rec aux f1 f2: types option = 
    match lt_cached_cert f1 f2 with
    | Some res -> res
    | None ->
      set_lt_cached_cert f1 f2 None;
      let gct = get_coq_term in
      let res = match f1, f2 with
      | CertLiteral a, _ when a.b -> Some (Constr.mkApp(left_true_or, [|gct f2|]))
      | _, CertLiteral a when a.b -> Some (Constr.mkApp(right_true_or, [|gct f1|]))
      | CertNeg {child = CertVariable a; _}, CertVariable b when a.id = b.id -> 
        Some (Constr.mkApp(left_neg_or, [|gct f2|]))
      | CertVariable a, CertNeg {child = CertVariable b; _} when a.id = b.id -> 
        Some (Constr.mkApp(right_neg_or, [|gct f1|]))
      | CertAnd a, _ -> 
        let r1 = aux a.c1 f2 in
        (match r1 with
        | Some x -> 
          let r2 = aux a.c2 f2 in
          (match r2 with
          | Some y -> Some (Constr.mkApp(left_and_or, [|gct a.c1; gct a.c2; gct f2; x; y|]))
          | _ -> None)  
        | _ -> None)
      | _, CertAnd a ->
        let r1 = aux f1 a.c1 in 
        (match r1 with
        | Some x -> let r2 = aux f1 a.c2 in
          (match r2 with
          | Some y -> Some (Constr.mkApp(right_and_or, [|gct f1; gct a.c1; gct a.c2; x; y|]))
          | _ -> None)
        | _ -> None)
      | _ -> (first_some (first_some (first_some
        (match f1 with | CertOr a -> 
          first_some (Option.map (fun x -> Constr.mkApp(left_or_or_1, [|gct a.c1; gct a.c2; gct f2; x|])) (aux a.c1 f2))
                      (lazy (Option.map (fun x -> Constr.mkApp(left_or_or_2, [|gct a.c1; gct a.c2; gct f2; x|])) (aux a.c2 f2)))
        | _ -> None)
        
        (lazy (match f2 with | CertOr b -> 
          first_some (Option.map (fun x -> Constr.mkApp(right_or_or_1, [|gct f1; gct b.c1; gct b.c2; x|])) (aux f1 b.c1))
                      (lazy (Option.map (fun x -> Constr.mkApp(right_or_or_2, [|gct f1; gct b.c1; gct b.c2; x|])) (aux f1 b.c2)))
        | _ -> None))
      )
        (lazy (Option.map (fun x -> Constr.mkApp(contract_or_1, [|gct f1; gct f2; x|])) (aux f1 f1)))
      )
        (lazy (Option.map (fun x -> Constr.mkApp(contract_or_2, [|gct f1; gct f2; x|])) (aux f2 f2)))
      )
      in
      set_lt_cached_cert f1 f2 res;
      res
  in 
  aux f1 f2

(* Find the atom in a formula (i.e. variable) that appears most often *)
let best_atom (l: cert_formula list) : cert_formula option =

  let counts = Hashtbl.create 50 in
  let rec aux f = 
    match f with
    | CertVariable a -> 
      let count = Hashtbl.find_opt counts a.id in
      (match count with
      | Some (c, e) -> Hashtbl.replace counts a.id ((c + 1), e)
      | None -> Hashtbl.add counts a.id (1, f))
    | CertNeg a -> aux a.child
    | CertOr a -> aux a.c1; aux a.c2
    | CertAnd a -> aux a.c1; aux a.c2
    | CertLiteral _ -> ()
    in

  List.iter aux l;
  let max_key = ref None in
  let max_value = ref 0 in
  Hashtbl.iter (fun key (c, e) ->
    if c > !max_value then begin
      max_value := c;
      max_key := Some e
    end
  ) counts;
  !max_key


(* Tactic: Introduces the normal form of a t as h, without proving equality*)

let ol_normal (t: Evd.econstr) (h: Names.Id.t): unit PV.tactic =
  let bool = Lazy.force bool_typ in

  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.pf_env gl in
    let sigma = Tacmach.project gl in
    let t2 = EConstr.Unsafe.to_constr t in
    let typ = type_of env sigma t in
    let typ_c = EConstr.Unsafe.to_constr (snd typ) in
    if typ_c === bool then
      let formula = quote env sigma t2 in
      let normal_form = reduced_form formula in
      let res = unquote normal_form in
      let res  = EConstr.of_constr res in
    Tacticals.tclTHENLIST [
            Tactics.pose_tac (Names.Name.mk_name h) res;
          ]
    else
      let typ_str = Pp.string_of_ppcmds (Printer.pr_constr_env env sigma typ_c) in
      let msg = str "Not a boolean expression: " ++ str typ_str in
      Tacticals.tclFAIL msg
  end





(* Tactic: introduce as "h" a proof of t, where t is a tpair of between boolean terms. *)
let ol_cert_tactic (t: Evd.econstr) (h: Names.Id.t): unit PV.tactic =
  let tpair = Lazy.force tpair in

  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.pf_env gl in
    let sigma = Tacmach.project gl in
    let t2 = EConstr.Unsafe.to_constr t in
    match decomp_term sigma t2 with
    | App (head, args) when head === tpair && Array.length args = 2 ->
      let new_forms = new_formulas env sigma args in
      let f1 = new_forms.(0) in
      let f2 = new_forms.(1) in
      let res = proof_ol f1 f2 in
      (match res with
      | Some res ->
        let res = EConstr.of_constr res in
        Tacticals.tclTHENLIST [
                Tactics.pose_tac (Names.Name.mk_name h) res;
              ]
      | None ->
        let msg = str "No proof found" in
        Tacticals.tclFAIL msg)
    | App (head, args) when head === tpair -> 
      let msg = str (Printf.sprintf "Not a pair of boolean expressions. Is tpair but args size: %d" (Array.length args)) in
      Tacticals.tclFAIL msg

    | _ ->
      let typ_str = Pp.string_of_ppcmds (Printer.pr_constr_env env sigma t2) in
      let msg = str "Goal is not a tpair: " ++ str typ_str in
      Tacticals.tclFAIL msg
  end

(* Tactic: Prove the current goal, which has to be of the form `tpair a b` or ` a = b` with a and b of type bool, using orthologic rules. *)
let ol_cert_goal_tactic cl : unit PV.tactic =
  let tpair = Lazy.force tpair in
  let eq = Lazy.force eq in

  let aux () =
    Proofview.Goal.enter begin fun gl ->
      let concl = Proofview.Goal.concl gl in
      let env = Tacmach.pf_env gl in
      let sigma = Tacmach.project gl in
      let concl2 = EConstr.Unsafe.to_constr concl in
      match decomp_term sigma concl2 with
      | App (head, args) when head === tpair && Array.length args = 2 ->
        let new_forms = new_formulas env sigma args in
        let f1 = new_forms.(0) in
        let f2 = new_forms.(1) in
        let res = proof_ol f1 f2 in
        (match res with
        | Some res ->
          let res = EConstr.of_constr res in
          Tacticals.tclTHENLIST [
            Tactics.exact_check res;
          ]
        | None ->
          let f1_s = Pp.string_of_ppcmds (Printer.pr_constr_env env sigma args.(0)) in
          let f2_s = Pp.string_of_ppcmds (Printer.pr_constr_env env sigma args.(1)) in
          let msg = str (Printf.sprintf "No proof of tpair %s %s found" f1_s f2_s) in
          Tacticals.tclFAIL msg)
      | _ ->
        let typ_str = Pp.string_of_ppcmds (Printer.pr_constr_env env sigma concl2) in
        let msg = str "Goal is not a tpair nor an equality: " ++ str typ_str in
        Tacticals.tclFAIL msg
      end
    in
    Proofview.Goal.enter begin fun gl ->
      let concl = Proofview.Goal.concl gl in
      let env = Tacmach.pf_env gl in
      let sigma = Tacmach.project gl in
      let concl2 = EConstr.Unsafe.to_constr concl in
      match decomp_term sigma concl2 with
      | App (head, args) when head === tpair && Array.length args = 2 ->
        Tacticals.tclTHENLIST [
          Autorewrite.auto_multi_rewrite ["nnf_lemmas"] cl;
          aux ()
        ]
      | App (head, args) when head === eq ->
          Tacticals.tclTHENFIRSTn
            (Tactics.apply (EConstr.of_constr (Lazy.force tpair_to_eq)))
            [|
              (Tacticals.tclTHEN
              (Autorewrite.auto_multi_rewrite ["nnf_lemmas"] cl)
              (aux ()));

              (Tacticals.tclTHEN
              (Autorewrite.auto_multi_rewrite ["nnf_lemmas"] cl)
              (aux ()))
            |]

      | App (head, args) when head === tpair -> 
        let msg = str (Printf.sprintf "Not a pair of boolean expressions. Is tpair but args size: %d" (Array.length args)) in
        Tacticals.tclFAIL msg

      | _ ->
        let typ_str = Pp.string_of_ppcmds (Printer.pr_constr_env env sigma concl2) in
        let msg = str "Goal is not a tpair nor an equality: " ++ str typ_str in
        Tacticals.tclFAIL msg
  end


(* Tactic: Prove the current goal, which has to be of the form `tpair a b` or ` a = b` with a and b of type bool, using orthologic rules. *)

(* Tactic: Destruct the boolean atom in a boolean term that appears most often *)
let destruct_atom () : unit PV.tactic =
  

  Proofview.Goal.enter begin fun gl ->
    let eq = Lazy.force eq in
    let bool_typ = Lazy.force bool_typ in
    let env = Tacmach.pf_env gl in
    let sigma = Tacmach.project gl in
    let concl = Proofview.Goal.concl gl in
    let concl = EConstr.Unsafe.to_constr concl in
    let t = decomp_term sigma concl in
    match t with
    | App (head, args) when head === eq && Array.length args = 3 && args.(0) === bool_typ ->
      let new_forms = new_formulas env sigma [|args.(1); args.(2)|] in
      let tl = new_forms.(0) in
      let tr = new_forms.(1) in
      let res = best_atom [tl; tr] in
      
      (match res with
      | Some res ->
        let res = get_coq_term res in
        let res = EConstr.of_constr res in
        Tactics.destruct false None res None None;
      | None ->
        let msg = str "No atom found" in
        Tacticals.tclFAIL msg)
    | _ ->
      let msg = str "Not an equality of boolean expressions" in
      Tacticals.tclFAIL msg
  end


(* Tactic: For every maximal boolean subterm `a` of `t`,
   compute `a'` the OL-normal form of `a`, prove `a=a'`, and substitute `ta`by `a'` in the goal. *)
let ol_norm_cert_tactic (t: Evd.econstr) cl : unit PV.tactic =
  let andb = Lazy.force andb in
  let orb = Lazy.force orb in
  let xorb = Lazy.force xorb in
  let negb = Lazy.force negb in
  let eqb = Lazy.force eqb in

  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.pf_env gl in
    let sigma = Tacmach.project gl in
    let rec aux t: types list =
      match decomp_term sigma t with
      | App (head, args) when 
        head === andb && Array.length args = 2 ||
        head === orb && Array.length args = 2 ||
        head === xorb && Array.length args = 2 ||
        head === negb && Array.length args = 1 ||
        head === eqb && Array.length args = 2 ->
        [t]
      | App (head, args) ->
        let h: types list = aux head in
        let rest: types list = List.flatten (List.map aux (Array.to_list args)) in
        h @ rest
      | _ -> 
        []
      in
    let t2 = EConstr.Unsafe.to_constr t in
    let l = aux t2 in
    let l = List.map (fun t2 -> 
      let f = quote env sigma t2 in
      (t2, f, size f)
      ) l in
    let l = List.sort (fun (_, _, i1) -> fun (_, _, i2) -> Int.compare i2 i1) l in
    Tacticals.tclTHENLIST
      (List.map (fun (t, f, _) ->
        let normal_form = reduced_form f in

        let res = unquote normal_form in
        let tac = ol_cert_goal_tactic cl in
        let res2 = EConstr.of_constr res in
        let t2 = EConstr.of_constr t in
        Equality.replace_by t2 res2 tac
      ) l)
    
  end




(* Tactic: For every maximal boolean subterm `a` of the goal,
   compute `a'` the OL-normal form of `a`, prove `a=a'`, and substitute `ta`by `a'` in the goal. *)
let ol_norm_cert_goal_tactic cl : unit PV.tactic =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    ol_norm_cert_tactic concl cl
  end


  
(* Tactic: oltauto with certification*)

let oltauto_cert cl : unit PV.tactic =

  let eq = Lazy.force eq in
  let bool_typ = Lazy.force bool_typ in
  let rec aux () : unit PV.tactic = Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.pf_env gl in
    let sigma = Tacmach.project gl in
    let concl = Proofview.Goal.concl gl in
    let concl = EConstr.Unsafe.to_constr concl in
    match decomp_term sigma concl with
    | App (head, args) when head === eq && Array.length args = 3 && args.(0) === bool_typ ->
      let f1 = args.(1) in
      let f2 = args.(2) in
      let f1_q = quote env sigma f1 in
      let f2_q = quote env sigma f2 in
      let f1_q_n = polar_to_normal_form (polarize f1_q true) in
      let f2_q_n = polar_to_normal_form (polarize f2_q true) in
      let f1_q_r = to_formula f1_q_n in
      let f2_q_r = to_formula f2_q_n in
      if (lattices_leq f1_q_n f2_q_n) && (lattices_leq f2_q_n f1_q_n) then
        ol_cert_goal_tactic cl
      else (
        let f1_n = unquote f1_q_r in
        let f2_n = unquote f2_q_r in
        let f1_n_e = EConstr.of_constr f1_n in
        let f2_n_e = EConstr.of_constr f2_n in
        let tac = 
          (Proofview.tclIFCATCH
              (ol_cert_goal_tactic cl) 
              (fun () -> aux ())
              (fun er -> (
                Tactics.pose_tac (Names.Name.mk_name (Names.Id.of_string "Nothing")) (EConstr.of_constr (Lazy.force trueb)))
              )
            ) in
        let t1, t2 = 
          let f1_e = EConstr.of_constr f1 in
          let f2_e = EConstr.of_constr f2 in
          if (size f1_q) > (size f2_q) then 
            (Equality.replace_by f1_e f1_n_e tac, Equality.replace_by f2_e f2_n_e tac)
          else 
            (Equality.replace_by f2_e f2_n_e tac, Equality.replace_by f1_e f1_n_e tac)
          in

        Tacticals.tclTHENLIST [
          t1; 
          t2;
            (Proofview.tclIFCATCH
              (Tacticals.tclTHEN (destruct_atom ()) (Autorewrite.auto_multi_rewrite ["nnf_lemmas"] cl;))
              (fun () -> aux ())
              (fun er -> (
                let (e, info) = er in
                let _msg = Pp.string_of_ppcmds (CErrors.print e) in
                Tactics.pose_tac (Names.Name.mk_name (Names.Id.of_string "Nothing")) (EConstr.of_constr (Lazy.force trueb)))
              )
            )
        ]
      )
    | _ ->
      let typ_str = Pp.string_of_ppcmds (Printer.pr_constr_env env sigma concl) in
      let msg = str "Goal must be an equality between boolean terms: " ++ str typ_str in
      Tacticals.tclFAIL msg
    end in
  aux ()

(* Tactic: oltauto with certification*)