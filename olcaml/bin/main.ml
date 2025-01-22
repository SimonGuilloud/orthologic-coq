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

(* Function to convert a formula to normal form *)



(* Function to polarize a formula *)



let rec get_polar_inverse (pf: polar_formula) =
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





    



(* Example usage *)
let a = new_variable 0
let b = new_variable 1
let f = new_or [ new_and [ new_neg a; b ]; new_neg a ]
let f2 = polarize f true

(* Function to convert Formula to string *)
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

(* Printing results *)
let () =
  Printf.printf "Formula: %s\n" (formula_to_string f);
  Printf.printf "Polarized: %s\n" (polar_formula_to_string f2)
