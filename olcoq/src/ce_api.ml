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

let identity (t: Evd.econstr) : unit PV.tactic =
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
            Tactics.pose_proof (Names.Name.mk_name (Names.Id.of_string "H_refl")) eq_refl;
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