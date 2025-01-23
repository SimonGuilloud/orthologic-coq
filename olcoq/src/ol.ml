[@@@ocaml.warnings "-31-32"]



(* Unique key counters *)
let total_formula = ref 0
let total_polar = ref 0
let total_normal = ref 0

(* Formula, Polar Formula and Normal Formula types *)

type formula = 
  | Variable of { id : int; 
        unique_key : int; mutable polar_formula : polar_formula option }
  | Neg of { child : formula; 
        unique_key : int; mutable polar_formula : polar_formula option }
  | Or of { children : formula list; 
        unique_key : int; mutable polar_formula : polar_formula option }
  | And of { children : formula list; 
        unique_key : int; mutable polar_formula : polar_formula option }
  | Literal of { b : bool; 
        unique_key : int; mutable polar_formula : polar_formula option }


and polar_formula = 
  | PolarVariable of { id : int; polarity : bool; 
        unique_key : int; 
        mutable inverse : polar_formula option; 
        mutable normal_form : normal_formula option }
  | PolarAnd of { children : polar_formula list; polarity : bool; 
        unique_key : int; 
        mutable inverse : polar_formula option; 
        mutable normal_form : normal_formula option }
  | PolarLiteral of { b : bool; 
        unique_key : int; 
        mutable inverse : polar_formula option; 
        mutable normal_form : normal_formula option }


and normal_formula = 
  | NormalVariable of { id : int; polarity : bool; 
        unique_key : int; 
        mutable inverse : normal_formula option;
        mutable formulaP : formula option;
        mutable formulaN : formula option;
        lt_cache : (int, bool) Hashtbl.t }
  | NormalAnd of { children : normal_formula list; polarity : bool; 
        unique_key : int; 
        mutable inverse : normal_formula option;
        mutable formulaP : formula option;
        mutable formulaN : formula option;
        lt_cache : (int, bool) Hashtbl.t }
  | NormalLiteral of { b : bool; 
        unique_key : int; 
        mutable inverse : normal_formula option;
        mutable formulaP : formula option;
        mutable formulaN : formula option;
        lt_cache : (int, bool) Hashtbl.t }



(* Factory functions for formula, incrementing global counter *)
let new_variable id =
  incr total_formula;
  Variable { id; unique_key = !total_formula; polar_formula = None }

let new_neg child =
  incr total_formula;
  Neg { child; unique_key = !total_formula; polar_formula = None }

let new_or children =
  incr total_formula;
  Or { children; unique_key = !total_formula; polar_formula = None }

let new_and children =
  incr total_formula;
  And { children; unique_key = !total_formula; polar_formula = None }

let new_literal b =
  incr total_formula;
  Literal { b; unique_key = !total_formula; polar_formula = None }

  (* Factory functions for polar_formula, incrementing global counter *)
let new_p_variable id polarity =
  incr total_polar;
  PolarVariable { id; polarity; 
                  unique_key = !total_polar; inverse = None;
                  normal_form = None }

let new_p_and children polarity =
  incr total_polar;
  PolarAnd { children; polarity; 
            unique_key = !total_polar; inverse = None;
            normal_form = None }

let new_p_literal b =
  incr total_polar;
  PolarLiteral { b; 
                unique_key = !total_polar; inverse = None;
                normal_form = None }

  (* Factory functions for normal_formula, incrementing global counter *)
let new_n_variable id polarity =
  incr total_normal;
  NormalVariable { id; polarity; 
                  unique_key = !total_normal; inverse = None; formulaP = None; formulaN = None;
                  lt_cache = Hashtbl.create 10 }

let new_n_and children polarity =
  incr total_normal;
  NormalAnd { children; polarity; 
              unique_key = !total_normal; inverse = None; formulaP = None; formulaN = None;
              lt_cache = Hashtbl.create 10 }

let new_n_literal b =
  incr total_normal;
  NormalLiteral { b; 
                  unique_key = !total_normal; inverse = None; formulaP = None; formulaN = None;
                  lt_cache = Hashtbl.create 10 }


  (* Getter and Setters for formulas*)
let get_key f =
  match f with
  | Variable v -> v.unique_key
  | Neg neg -> neg.unique_key
  | Or or_f -> or_f.unique_key
  | And and_f -> and_f.unique_key
  | Literal lit -> lit.unique_key

let get_polar_formula f =
  match f with
  | Variable v -> v.polar_formula
  | Neg neg -> neg.polar_formula
  | Or or_f -> or_f.polar_formula
  | And and_f -> and_f.polar_formula
  | Literal lit -> lit.polar_formula

let set_polar_formula f p =
  match f with
  | Variable v -> v.polar_formula <- p
  | Neg neg -> neg.polar_formula <- p
  | Or or_f -> or_f.polar_formula <- p
  | And and_f -> and_f.polar_formula <- p
  | Literal lit -> lit.polar_formula <- p

let get_p_normal_form pf =
  match pf with
  | PolarVariable v -> v.normal_form
  | PolarAnd and_f -> and_f.normal_form
  | PolarLiteral lit -> lit.normal_form

let set_p_normal_form pf nf =
  match pf with
  | PolarVariable v -> v.normal_form <- nf
  | PolarAnd and_f -> and_f.normal_form <- nf
  | PolarLiteral lit -> lit.normal_form <- nf

  (* Getter and Setters for polar formulas*)
let get_p_key pf =
  match pf with
  | PolarVariable v -> v.unique_key
  | PolarAnd and_f -> and_f.unique_key
  | PolarLiteral lit -> lit.unique_key

let get_p_inverse_option pf =
  match pf with
  | PolarVariable v -> v.inverse
  | PolarAnd and_f -> and_f.inverse
  | PolarLiteral lit -> lit.inverse

let set_p_inverse_option pf1 pf2 =
  match pf1 with
  | PolarVariable v -> v.inverse <- pf2
  | PolarAnd and_f -> and_f.inverse <- pf2
  | PolarLiteral lit -> lit.inverse <- pf2

  (* Getters and Setters for normal formulas*)
let get_n_key nf =
  match nf with
  | NormalVariable v -> v.unique_key
  | NormalAnd and_f -> and_f.unique_key
  | NormalLiteral lit -> lit.unique_key

let get_n_inverse_option nf =
  match nf with
  | NormalVariable v -> v.inverse
  | NormalAnd and_f -> and_f.inverse
  | NormalLiteral lit -> lit.inverse

let set_n_inverse_option nf1 nf2 =
  match nf1 with
  | NormalVariable v -> v.inverse <- nf2
  | NormalAnd and_f -> and_f.inverse <- nf2
  | NormalLiteral lit -> lit.inverse <- nf2

let get_formulaP nf =
  match nf with
  | NormalVariable v -> v.formulaP
  | NormalAnd and_f -> and_f.formulaP
  | NormalLiteral lit -> lit.formulaP 

let set_formulaP nf f =
  match nf with
  | NormalVariable v -> v.formulaP <- f
  | NormalAnd and_f -> and_f.formulaP <- f
  | NormalLiteral lit -> lit.formulaP <- f  

let get_formulaN nf =
  match nf with
  | NormalVariable v -> v.formulaN
  | NormalAnd and_f -> and_f.formulaN
  | NormalLiteral lit -> lit.formulaN

let set_formulaN nf f =
  match nf with
  | NormalVariable v -> v.formulaN <- f
  | NormalAnd and_f -> and_f.formulaN <- f
  | NormalLiteral lit -> lit.formulaN <- f

let get_lt_cache nf =
  match nf with
  | NormalVariable v -> v.lt_cache
  | NormalAnd and_f -> and_f.lt_cache
  | NormalLiteral lit -> lit.lt_cache

let lt_cached nf1 nf2 =
    Hashtbl.find_opt (get_lt_cache nf1) (get_n_key nf2)

let set_lt_cached nf1 nf2 b =
    Hashtbl.add (get_lt_cache nf1) (get_n_key nf2) b

  (* Pretty printers *)

let rec formula_to_string f =
  match f with
  | Variable v -> Printf.sprintf "V_%d" v.id 
  | Neg neg -> Printf.sprintf "Neg(%s)" (formula_to_string neg.child)
  | Or or_f -> Printf.sprintf "Or(%s)" 
                  (String.concat ", " (List.map formula_to_string or_f.children))
  | And and_f -> Printf.sprintf "And(%s)" 
                  (String.concat ", " (List.map formula_to_string and_f.children))
  | Literal lit -> if lit.b then "True" else "False"

let rec polar_formula_to_string pf =
  match pf with
  | PolarVariable v -> if v.polarity then 
                        Printf.sprintf "PV_(%d)" v.id 
                      else 
                        Printf.sprintf "!PV_(%d)" v.id
  | PolarAnd and_f -> if and_f.polarity then 
                        Printf.sprintf "PAnd(%s)" 
                          (String.concat ", " (List.map polar_formula_to_string and_f.children))
                      else 
                        Printf.sprintf "!PAnd(%s)" 
                        (String.concat ", " (List.map polar_formula_to_string and_f.children))
  | PolarLiteral lit -> if lit.b then "PTrue" else "PFalse"

let rec normal_formula_to_string nf =
  match nf with
  | NormalVariable v -> if v.polarity then 
                        Printf.sprintf "NV_(%d)" v.id 
                      else 
                        Printf.sprintf "!NV_(%d)" v.id
  | NormalAnd and_f -> if and_f.polarity then 
                        Printf.sprintf "NAnd(%s)" 
                          (String.concat ", " (List.map normal_formula_to_string and_f.children))
                      else 
                        Printf.sprintf "!NAnd(%s)" 
                        (String.concat ", " (List.map normal_formula_to_string and_f.children))
  | NormalLiteral lit -> if lit.b then "NTrue" else "NFalse"



(* Function to convert a formula to normal form *)



(* Function to polarize a formula *)



let get_polar_inverse (pf: polar_formula) =
  match get_p_inverse_option pf with
  | Some pf' -> pf'
  | None -> 
    let pf' = 
      match pf with
      | PolarVariable v -> new_p_variable v.id (not v.polarity)
      | PolarAnd and_f -> new_p_and and_f.children (not and_f.polarity)
      | PolarLiteral lit -> new_p_literal (not lit.b)
    in
    set_p_inverse_option pf (Some pf');
    pf'

let rec polarize f polarity =
  match get_polar_formula f with
  | Some pf -> if polarity then pf else get_polar_inverse pf
  | None -> 
    let pf = 
      match f with
      | Variable v -> new_p_variable v.id polarity
      | Neg neg -> polarize neg.child (not polarity)
      | Or or_f -> new_p_and (List.map (fun x -> polarize x false) or_f.children) (not polarity)
      | And and_f -> new_p_and (List.map (fun x -> polarize x true) and_f.children) polarity
      | Literal lit -> new_p_literal (lit.b == polarity)
    in
    if polarity then set_polar_formula f (Some pf) else set_polar_formula f (Some (get_polar_inverse pf));
    pf

let get_normal_inverse (nf: normal_formula) =
  match get_n_inverse_option nf with
  | Some nf' -> nf'
  | None ->
    let nf' = 
      match nf with
      | NormalVariable v -> new_n_variable v.id (not v.polarity)
      | NormalAnd and_f -> new_n_and and_f.children (not and_f.polarity)
      | NormalLiteral lit -> new_n_literal (not lit.b)
    in
    set_n_inverse_option nf (Some nf');
    set_n_inverse_option nf' (Some nf);
    nf'


let rec to_formula_nnf (nf: normal_formula) (positive: bool): formula =
  let invnf = get_normal_inverse nf in
  match get_formulaP nf, get_formulaN invnf, get_formulaN nf, get_formulaP invnf with
  | Some f, _, _, _ when positive -> f
  | _, Some f, _, _ when positive -> f
  | _, _, Some f, _ when not positive -> f
  | _, _, _, Some f when not positive -> f
  | _ ->
    let r = 
      match nf with
      | NormalVariable v -> if positive = v.polarity then new_variable v.id else new_neg (to_formula_nnf nf (not positive))
      | NormalAnd and_f -> 
        if positive = and_f.polarity then 
          new_and (List.map (fun x -> to_formula_nnf x true) and_f.children) 
        else 
          new_or (List.map (fun x -> to_formula_nnf x false) and_f.children)
      | NormalLiteral lit -> new_literal (positive == lit.b)
    in
    if positive then set_formulaP nf (Some r) else set_formulaN nf (Some r);
    r


let to_formula (nf: normal_formula) = to_formula_nnf nf true



let rec lattices_leq (nf1: normal_formula) (nf2: normal_formula) =
  if get_n_key nf1 = get_n_key nf2 then true
  else
    match lt_cached nf1 nf2 with
    | Some b -> b
    | None ->
      let r = 
        match (nf1, nf2) with
        | (NormalLiteral lit1, NormalLiteral lit2) -> not lit1.b || lit2.b
        | (NormalLiteral lit, _) -> not lit.b
        | (_, NormalLiteral lit) -> lit.b
        | (NormalVariable v1, NormalVariable v2) -> v1.id = v2.id && v1.polarity = v2.polarity
        | (_, NormalAnd and_f) when and_f.polarity -> List.for_all (fun x -> lattices_leq nf1 x) and_f.children
        | (NormalAnd and_f, _) when not and_f.polarity -> List.for_all (fun x -> lattices_leq (get_normal_inverse x) nf2) and_f.children
        | (NormalVariable v, NormalAnd and_f) when not and_f.polarity -> List.exists (fun x -> lattices_leq nf1 (get_normal_inverse x)) and_f.children
        | (NormalAnd and_f, NormalVariable v) when and_f.polarity -> List.exists (fun x -> lattices_leq x nf2) and_f.children
        | (NormalAnd and_f1, NormalAnd and_f2) -> List.exists (fun x -> lattices_leq x nf2) and_f1.children || List.exists (fun x -> lattices_leq nf1 x) and_f2.children
        | _ -> raise (Failure "Impossible case")
      in
      set_lt_cached nf1 nf2 r;
      r

let simplify (children: normal_formula list) (polarity: bool) =
  let non_simplified = new_n_and children polarity in
  let rec treat_child i = 
    match i with
    | NormalAnd and_f when and_f.polarity -> and_f.children
    | NormalAnd and_f when not and_f.polarity -> (
      if polarity then 
        let tr_ch = List.map get_normal_inverse and_f.children in
        match List.find_opt (fun f -> lattices_leq non_simplified f) tr_ch with
        | Some value -> treat_child value
        | None -> [i]
      else 
        let tr_ch = and_f.children in
        match List.find_opt (fun f -> lattices_leq f non_simplified) tr_ch with
        | Some value -> treat_child (get_normal_inverse value)
        | None -> [i]
        )
    | NormalVariable v -> [i]
    | NormalLiteral lit -> [i]
    | _ -> [i]
  in
  let remaining = List.flatten (List.map treat_child children) in
  let rec loop (acc: normal_formula list) (rem: normal_formula list) =
    match rem with
    | current::tail ->
      if (lattices_leq (new_n_and (acc @ tail) true) current) then
        loop acc tail
      else
        loop (current::acc) tail
    | [] -> acc
      in
  match loop [] remaining with
  | [] -> new_n_literal polarity
  | [x] -> if polarity then x else get_normal_inverse x
  | accepted -> new_n_and accepted polarity

let check_for_contradiction (f: normal_formula) =
  match f with
  | NormalAnd (and_f) when not and_f.polarity -> 
    List.exists (fun x -> lattices_leq x f) and_f.children
  | NormalAnd (and_f) when and_f.polarity -> 
    let shadow_children = List.map get_normal_inverse and_f.children in
    List.exists (fun x -> lattices_leq f x) shadow_children
  | _ -> false
  
let rec polar_to_normal_form (pf: polar_formula) =
  match get_p_normal_form pf with
  | Some nf -> nf
  | None ->
    let r = 
      match pf with
      | PolarVariable v -> 
        if v.polarity then new_n_variable v.id true 
        else get_normal_inverse (polar_to_normal_form (get_polar_inverse pf))
      | PolarAnd and_f -> 
        let new_children = List.map polar_to_normal_form and_f.children in
        let simp = simplify new_children and_f.polarity in
        if check_for_contradiction simp then new_n_literal (not and_f.polarity) else simp
      | PolarLiteral lit -> new_n_literal lit.b
    in
    set_p_normal_form pf (Some r);
    r

let reduced_form (f: formula) =
  let p = polarize f true in
  let nf = polar_to_normal_form p in
  to_formula nf

  


(* Example usage *)
let a = new_variable 0
let b = new_variable 1
let f = new_or [ new_and [ new_neg a; b ]; new_neg a ]

(* Function to convert Formula to string *)


(* Printing results *)
let show_ol  = 
  (Printf.sprintf "Formula: %s\n" (formula_to_string f)) ^
  (Printf.sprintf "Polarized: %s\n" (polar_formula_to_string (polarize f true))) ^
  (Printf.sprintf "Normal Form: %s\n" (formula_to_string (reduced_form f)));;


