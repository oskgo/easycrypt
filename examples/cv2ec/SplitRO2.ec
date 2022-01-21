require import AllCore PROM SmtMap Distr DProd.

abstract theory Split.

  type in_t,out_t,d_in_t,d_out_t.

  op dout : in_t -> out_t distr.

  clone import FullRO as IdealAll with
    type in_t    <- in_t,
    type out_t   <- out_t,
    type d_in_t  <- d_in_t,
    type d_out_t <- d_out_t,
    op   dout    <- dout.

abstract theory SplitDomT.

module type ROt = {
  include RO [-init]
  proc init (_ : in_t -> bool) : unit
}.

abstract theory MkROt.
module RO : ROt = {
  var m : (in_t, out_t) fmap

  proc init (t : in_t -> bool) = {
    m <- empty;
  }

  proc get (x : in_t) = {
    var r;

    r <$ dout x;
    if (x \notin m) {
      m.[x] <- r;
    }
    return (oget m.[x]);
  }

  proc set (x : in_t, y : out_t) = {
    m.[x] <- y;
  }

  proc rem (x : in_t) = {
    m <- rem m x;
  }

  proc sample (x : in_t) = {
    get(x);
  }

  proc restrK () = {
    return m;
  }
}.
end MkROt.

clone include MkROt.

module type RO_DistinguisherT (G : ROt) = {
  proc get_test () : in_t -> bool {}
  proc distinguish (_ : d_in_t): d_out_t
}.

module MainDT (D : RO_DistinguisherT) (RO : ROt) = {
  proc distinguish (x) = {
    var t, r;

    t <@ D(RO).get_test();
    RO.init(t);
    r <@ D(RO).distinguish(x);
    return r;
  }
}.


module RO_DOMt (ROT : RO) (ROF: RO) : ROt = {
  var test : in_t -> bool

  proc init (test': in_t -> bool) = { test <- test'; ROT.init(); ROF.init(); }

  proc get (x : in_t) = {
    var r;
    if (test x) r <@ ROT.get(x);
    else r <@ ROF.get(x);
    return r;
  }

  proc set (x : in_t, y : out_t) = {
    if (test x) ROT.set(x, y);
    else ROF.set(x, y);
  }

  proc rem (x : in_t) = {
    if (test x) ROT.rem(x);
    else ROF.rem(x);
  }

  proc sample (x : in_t) = {
    if (test x) ROT.sample(x);
    else ROF.sample(x);
  }
}.

clone MkRO as ROT.
clone MkRO as ROF.

section PROOFS.

declare module D <: RO_DistinguisherT {RO, RO_DOMt, ROT.RO, ROF.RO}.

equiv RO_split :
  MainDT(D, RO).distinguish ~ MainDT(D, RO_DOMt(ROT.RO, ROF.RO)).distinguish :
  ={arg, glob D} ==>
  ={res, glob D} /\ RO.m{1} = union_map ROT.RO.m{2} ROF.RO.m{2} /\
  (forall x, x \in ROT.RO.m{2} =>   RO_DOMt.test{2} x) /\
  (forall x, x \in ROF.RO.m{2} => ! RO_DOMt.test{2} x).
proof.
  proc.
  call (_ : RO.m{1} = union_map ROT.RO.m{2} ROF.RO.m{2} /\
            (forall x, x \in ROT.RO.m{2} =>   RO_DOMt.test{2} x) /\
            (forall x, x \in ROF.RO.m{2} => ! RO_DOMt.test{2} x)).
  - proc; inline *.
    if {2}; auto=> />; 2: smt(get_setE mergeE set_union_map_r).
    by smt(get_setE mem_union_map mergeE set_union_map_l).
  - proc; inline *.
    if {2}; auto=> />; 2: smt(get_setE mergeE set_union_map_r).
    by smt(get_setE mem_union_map mergeE set_union_map_l).
  - by proc; inline *; auto=> />; smt(mem_rem rem_id rem_merge).
  - proc; inline *.
    if {2}; auto=> />; 2: smt(get_setE mergeE set_union_map_r).
    by smt(get_setE mem_union_map mergeE set_union_map_l).
  - proc; inline *; auto => />.
    by rewrite {1}/union_map merge_empty //; smt(mem_empty).
  - inline *; auto; call(: true) => />; 1: by move=> /> /#.
    by skip => /> r; rewrite {1}/union_map merge_empty //; smt(mem_empty).
qed.

end section PROOFS.

end SplitDomT.

end Split.
