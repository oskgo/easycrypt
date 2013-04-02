(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcTypes

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

let mem_equal = EcIdent.id_equal

(* -------------------------------------------------------------------- *)

type local_memtype = {
  mt_path : EcPath.mpath;
  mt_vars : ty Msym.t
}

type memtype = local_memtype option


let lmt_equal mt1 mt2 =   
  EcPath.m_equal mt1.mt_path mt2.mt_path &&
    Msym.equal ty_equal mt1.mt_vars mt2.mt_vars

let lmt_mpath mt = mt.mt_path
let lmt_bindings mt = mt.mt_vars

let mt_equal mt1 mt2 = 
  match mt1, mt2 with
  | Some mt1, Some mt2 -> lmt_equal mt1 mt2
  | None, None         -> true
  | _   , _            -> false

let mt_mpath = function
  | None -> assert false
  | Some mt -> lmt_mpath mt
 
let mt_bindings = function
  | None -> assert false
  | Some mt -> lmt_bindings mt
(* -------------------------------------------------------------------- *)


type memenv = memory * memtype 

let me_equal (m1,mt1) (m2,mt2) = 
  mem_equal m1 m2 && mt_equal mt1 mt2 

(* -------------------------------------------------------------------- *)
let memory   (m,_) = m
let memtype  (_,mt) = mt
let mpath    (_,mt) = mt_mpath mt
let bindings (_,mt) = mt_bindings mt

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
let empty_local (me : memory) mp =
  (me, Some {mt_path   = mp; mt_vars   = Msym.empty; } )

let abstract (me:memory) = (me,None)

(* -------------------------------------------------------------------- *)
let bind (x : symbol) (ty : EcTypes.ty) ((m,mt) : memenv) =
  let mt = match mt with
    | None -> assert false
    | Some mt -> mt in
  let merger = function
    | Some _ -> raise (DuplicatedMemoryBinding x)
    | None   -> Some ty
  in
    (m, Some { mt with mt_vars = Msym.change merger x mt.mt_vars })

(* -------------------------------------------------------------------- *)
let lookup (x : symbol) ((_,mt) : memenv) =
  match mt with 
  | None -> None
  | Some mt ->  Msym.find_opt x (lmt_bindings mt)

(* -------------------------------------------------------------------- *)
let mt_subst sp smp st o =
  match o with
  | None -> o
  | Some mt ->
    let p' = EcPath.m_subst sp smp mt.mt_path in
    let vars' = 
      if st == identity then mt.mt_vars else
        Msym.map st mt.mt_vars in (* FIXME could be greate to use smart_map *)
    if p' == mt.mt_path && vars' == mt.mt_vars then o else
      Some { mt_path   = p'; mt_vars   = vars' }

let me_subst sp smp sm st (m,mt as me) =
  let m' = EcIdent.Mid.find_def m m sm in
  let mt' = mt_subst sp smp st mt in
  if m' == m && mt' == mt then me else 
    (m', mt')



