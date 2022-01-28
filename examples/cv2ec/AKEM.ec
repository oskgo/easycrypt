require import AllCore List Finite Distr DBool DInterval LorR FSet SmtMap.
require (****) PROM Means.

(* preliminaries *)

lemma finite_dinter (a b : int) : is_finite (support [a..b]).
proof.
rewrite is_finiteE; exists (range a (b+1)).
by rewrite range_uniq /= => x; rewrite mem_range supp_dinter /#.
qed.

lemma supp_range (a b : int) : 
  perm_eq (to_seq (support [a..b])) (range a (b+1)).
proof. 
apply: uniq_perm_eq; first exact/uniq_to_seq/finite_dinter.
+ exact: range_uniq.
by move=> x; rewrite mem_to_seq ?finite_dinter // supp_dinter mem_range /#.
qed.

lemma supp_range_pred (a b : int) : 
  perm_eq (to_seq (support [a..b-1])) (range a b).
proof. by have /# := supp_range a (b-1). qed.  

lemma supp_dinter1E (x : int) (a b : int) :
  x \in [a..b] => mu1 [a..b] x = 1%r / (b - a + 1)%r.
proof. by rewrite supp_dinter dinter1E => ->. qed.

lemma find_map (m : ('a, 'b) fmap) (f : 'a -> 'b -> 'c) (P : 'a -> 'c -> bool) : 
  find P (map f m) = find (fun x y => P x (f x y)) m.
proof.
rewrite !findE fdom_map; congr; apply find_eq_in => x /=.
by rewrite -memE fdomP /= mapE; case(m.[x]).
qed.

lemma find_not_none (P : 'a -> 'b -> bool) (m : ('a,'b) fmap) : 
  find P m <> None => exists x y, find P m = Some x /\ m.[x] = Some y /\ P x y.
proof. by case: (findP P m) => // x y ? ? ? _; exists x y. qed.

lemma uniq_mem_rem (y x : 'a) (s : 'a list) : 
  uniq s => y \in rem x s <=> y \in s /\ y <> x.
proof. by elim: s => //= /#. qed.

lemma finite_dprod (d1 d2 : 'a distr) : 
  is_finite (support d1) => is_finite (support d2) => is_finite (support (d1 `*` d2)).
proof.
move=> fin_d1 fin_d2; rewrite dprod_dlet finite_dlet // => x x_d1.
by apply finite_dlet => // y y_d2; apply finite_dunit.
qed.

lemma oget_map (m : ('a,'b) fmap) (f : 'a -> 'b -> 'c) i :
  i \in m => oget (map f m).[i] = f i (oget m.[i]).
proof. by rewrite mapE fmapP => -[y ->]. qed.

lemma ifT (b : bool) (e1 e2 : 'a) : b => (if b then e1 else e2) = e1. 
proof. smt(). qed.

lemma ifF (b : bool) (e1 e2 : 'a) : !b => (if b then e1 else e2) = e2. 
proof. smt(). qed.

require StdBigop.
import StdBigop.Bigreal.BRA.

(* shadows more restrictive big_reinded from theories *)
lemma nosmt big_reindex ['a 'b]
  (P : 'a -> bool) (F : 'a -> real) (f : 'b -> 'a) (f' : 'a -> 'b) (s : 'a list) :
  (forall x, x \in s => f (f' x) = x) => big P F s = big (P \o f) (F \o f) (map f' s).
proof. 
by move => /eq_in_map id_ff'; rewrite -big_map -map_comp id_ff' id_map.
qed.

(* end preliminaries *)


type keyseed.
type pkey.
type skey.
type key.
type ciphertext.

op [lossless] dkeyseed : keyseed distr.
op [lossless] dkey : key distr.

op pkgen : keyseed -> pkey.
op skgen : keyseed -> skey.

type encseed.
op [lossless] dencseed : encseed distr.

op encap : encseed -> skey -> pkey -> ciphertext * key.
op decap : skey -> pkey -> ciphertext -> key option.

axiom encapK (ks1 ks2 : keyseed) (es : encseed) :
  let (c,k) = encap es (skgen ks1) (pkgen ks2) in
  decap (skgen ks2) (pkgen ks1) c = Some k.

(* module type Scheme = { *)
(*   proc encap(sender : skey, receiver : pkey)  : ciphertext * key *)
(*   proc decap(receiver : skey, sender : pkey, c:ciphertext) : key option *)
(* }. *)

(* participants *)
type user = [u1|u2].

clone import FinType.FinType as UserFinType with
  type t = user,
  op enum = [u1;u2]
proof*.
realize enum_spec by case.

theory Outsider2CCA.

(* these need to be parameters of the theory, since B depends on qc
and is part of the final statement *)
op qe : int.
op qd : int.
op qc : { int | 0 < qc } as qc_gt0.

module type Oracle = { 
  proc pkey  (_ : user) : pkey
  proc encap (_ : user * pkey) : ciphertext * key
  proc decap (_ : user * pkey * ciphertext) : key option
  proc chall (_ : user * user) : ciphertext * key
}.

module type Oracle_i = { 
  include Oracle
  proc init() : unit
}.

abstract theory MkCount.
module Count (O : Oracle) = { 
  var ce, cd, cc : int

  proc init() = {
    ce <- 0;
    cd <- 0;
    cc <- 0;
  } 

  proc pkey = O.pkey

  proc encap(x) = { 
    var r; 
    ce <- ce + 1 ;
    r <@ O.encap(x);
    return r;
  }

  proc decap(x) = { 
    var r; 
    cd <- cd + 1 ;
    r <@ O.decap(x);
    return r;
  }

  proc chall(x) = { 
    var r; 
    cc <- cc + 1 ;
    r <@ O.chall(x);
    return r;
  }
}.
end MkCount.
clone import MkCount as C.

module type Adversary (O : Oracle) = { 
  proc guess() : bool
}.

module Game (O : Oracle_i) (A : Adversary) = {
  proc main() = {
    var r;

    O.init();
    Count(O).init();
    r <@ A(Count(O)).guess();
    return r;
  }
}.

(* real game *)
module Oreal : Oracle_i = {
  var pk1, pk2 : pkey
  var sk1, sk2 : skey

  proc init() = {
    var ks1,ks2;

    ks1 <$ dkeyseed;
    ks2 <$ dkeyseed;

    sk1 <- skgen ks1;
    pk1 <- pkgen ks1;
    
    sk2 <- skgen ks2;
    pk2 <- pkgen ks2;
  }

  proc pkey (u : user) = { 
    return (if u = u1 then pk1 else pk2);
  }

  proc skey (u : user) = {
    return (if u = u1 then sk1 else sk2);
  }

  proc encap (u : user, pk : pkey) = {
    var c,k,sk,es;
   
    sk <@ skey(u);
    es <$ dencseed;
    (c,k) <- encap es sk pk;
    return (c,k);  
  }

  proc decap (u : user, pk : pkey, c : ciphertext) = {
    var k,sk;

    sk <@ skey(u);
    k <- decap sk pk c;
    return k;
  }

  proc chall (snd : user, rcv : user) = {
    var pk,sk,c,k,es;
    
    sk <@ skey(snd);
    pk <@ pkey(rcv);
    es <$ dencseed;

    (c,k) <- encap es sk pk;
    return (c,k);
  }

}.

(* ideal game - challenge oracle yields random keys *)
module Oideal = {
  include var Oreal [-init,chall,decap]
  var m : (pkey * pkey * ciphertext, key) fmap

  proc init() = {
    Oreal.init();
    m <- empty;
  }

  proc decap (u : user, pk : pkey, c : ciphertext) = {
    var k,sku,pku;

    sku <@ skey(u);
    pku <@ pkey(u); 

    if ((pk,pku,c) \in m) {
      k <- m.[(pk,pku,c)];
    } else { 
      k <- decap sku pk c;
    }
    return k;
  }

  proc chall (snd : user, rcv : user) = {
    var pks, pk,sk,c,k,es;
    
    sk <@ skey(snd);
    pk <@ pkey(rcv);
    es <$ dencseed;
    (c,k) <- encap es sk pk;
    k <$ dkey;
    pks <@ pkey(snd); 
    m.[(pks,pk,c)] <- k;
    return (c,k);
  }
}.

module (B (A : Adversary) : Adversary) (O : Oracle) = { 
  module OB : Oracle = { 
    var m : (pkey * pkey * ciphertext, key) fmap
    var q,ctr : int
    
    proc encap = O.encap

    proc pkey = O.pkey

    proc decap (u : user, pk : pkey, c : ciphertext) = {
      var k,pku;

      pku <@ pkey(u); 
      if ((pk,pku,c) \in m) {
        k <- m.[(pk,pku,c)];
      } else { 
        k <@ O.decap(u,pk,c);
    }
      return k;
    }

    proc chall (snd : user, rcv : user) : ciphertext * key = { 
      var pk,pks,c,k;
      
      pk <@ pkey(rcv);
      ctr <- ctr + 1;
      if   (ctr < q) { (c,k) <@ O.encap(snd,pk); }
      elif (ctr = q) { (c,k) <@ O.chall(snd,rcv); }
      else { 
        (c,k) <@ O.encap(snd,pk);
        k <$ dkey;
      }
      pks <@ pkey(snd);
      m.[(pks,pk,c)] <- k;
      return (c,k);
    }
  }

  proc guess() = { 
    var r; 
    OB.q <$ [1..qc];
    OB.ctr <- 0;
    OB.m <- empty;
    r <@ A(OB).guess() ; return r;
  }
}.

op counts0 (e d c : int) = e = 0 /\ d = 0 /\ c = 0.
op counts qe qd qc (e d c : int) = e <= qe /\ d <= qd /\ c <= qc.

clone MkCount as CB.

section PROOF.

declare module A <: Adversary{Oreal,Oideal,Count,B,CB.Count}.

declare axiom A_ll : forall (O <: Oracle{A}),
  islossless O.pkey =>
  islossless O.encap =>
  islossless O.decap => 
  islossless O.chall => 
  islossless A(O).guess.

local clone Means as M1 with
  type input <- int,
  type output <- bool,
  op d <- [1..qc]
proof*.

local clone Means as M0 with
  type input <- int,
  type output <- bool,
  op d <- [0..qc-1]
proof*.

local module OG : Oracle_i = { 
  import var Oreal
  include var Oideal [-init,chall]
  var q,ctr : int
  
  proc init () = { 
    Oreal.init();
    m <- empty;
    ctr <- 0;
  }

  proc chall (snd : user, rcv : user) = {
    var pks, pk,sk,c,k,es;
    
    sk <@ skey(snd);
    pk <@ pkey(rcv);
    es <$ dencseed; 
    (c,k) <- encap es sk pk;
    ctr <- ctr + 1;
    if (q < ctr) { k <$ dkey; }
    pks <@ pkey(snd); 
    m.[(pks,pk,c)] <- k;
    return (c,k);
  }
}.

local module G : M1.Worker = { 
  proc work (q : int) = {
    var r;

    OG.init();
    OG.q <- q;
    Count(OG).init();
    r <@ A(Count(OG)).guess();
    return r;
  }
}.

declare axiom A_bound (O <: Oracle) :
  hoare [ A(Count(O)).guess : 
  counts0 Count.ce Count.cd Count.cc ==> 
  counts qe qd qc Count.ce Count.cd Count.cc].

(* The ideal game corresponds to G.work(0), where k is always randomized *)
local lemma Oideal_Gqc &m : 
  Pr [ Game(Oideal,A).main() @ &m : res ] = 
  Pr [ G.work(0) @ &m : res ].
proof.
byequiv => //; proc; inline *.
call (: ={glob Oreal, Oideal.m, glob Count} /\ OG.q{2} = 0 /\ 0 <= OG.ctr{2}).
- conseq />; sim.
- conseq />; sim.
- conseq />; sim.
- proc; inline*; conseq />. 
  rcondt{2} 10; first by auto => /> /#. 
  by auto => /#.
- auto; smt().
qed.

(* The real game corresponds to G.work(qc), where k is never randomized 
There are two complications:

1. The proof relies on A making at most qc challenge queries. For this
we turn [qc < OG.ctr] into a bad event and prove that this does not
happen.

2. In Oreal, the decap oracle always calls the decap operation, in
G.work(), challenge queries are logged and the decap orcale uses the
log to answer. So we need to maintain the invariant that answering
using the log is equivalent to running decap. This relies on
correctness of the AKEM scheme. *)
local lemma Oreal_G0 &m : 
  Pr [ Game(Oreal,A).main() @ &m : res ] = 
  Pr [ G.work(qc) @ &m : res ].
proof.
byequiv => //; proc; inline *.
conseq (: _ ==> OG.ctr{2} <= qc => ={r}) _ (: _ ==> OG.ctr <= qc); 1:smt().
- conseq (: _ ==> OG.ctr = Count.cc) 
         (: _ ==> counts qe qd qc Count.ce Count.cd Count.cc); 1: smt().
  + by call (A_bound OG); auto.
  + call(: OG.ctr = Count.cc); 1..3: by conseq />. 
    proc; inline*; auto. swap 9 -7.
    seq 2 : (#pre); [by auto|by conseq />].
  + by auto.
call (: qc < OG.ctr, 
       ={glob Oreal} /\ OG.q{2} = qc /\
       (forall pks c k, Oideal.m.[pks,Oreal.pk1,c] = Some k => 
                        decap Oreal.sk1 pks c = Some k){2} /\
       (forall pks c k, Oideal.m.[pks,Oreal.pk2,c] = Some k => 
                        decap Oreal.sk2 pks c = Some k){2} /\ 
       (exists ks1 ks2, 
         (Oreal.pk1,Oreal.pk2,Oreal.sk1,Oreal.sk2) = 
         (pkgen ks1,pkgen ks2, skgen ks1, skgen ks2)){2}).
- exact A_ll.
(* pkey *)
- conseq />; proc; auto. 
- move => *. islossless. 
- move => *; proc; auto.
(* encap *)
- proc; inline*; conseq />. auto.
- move => *. islossless; apply encap_ll.
- move=> *; proc; inline*. auto => />; smt(dencseed_ll).
(* decap *)
- proc; inline*; auto => /> &2 H1 H2 H3 H4.
  move: (x{2}) H4 => [u pk c] /=. smt.
- move =>*; islossless.
- move=> *; proc; inline*. auto => />.
(* chall *)
- proc; inline*. conseq />.
  swap 7 -6. seq 1 1 : (#pre /\ ={es}); first by conseq />; auto. 
  wp. sp. if{2}; first by auto. auto => /> &1 ? E _ H1 H2 ks1 ks2 /> _. 
  move: E. case (snd{1} = u1) => _; case (rcv{1} = u1) => _ /> /= E.
  + split; 1:smt(); split => pks c' k; rewrite get_setE /=.
    case: (pks = pkgen ks1 /\ c' = c{1}) => />; smt(encapK). 
    case: (pks = pkgen ks1 /\ pkgen ks2 = pkgen ks1 /\ c' = c{1}) => />; smt(encapK).
  + split; 1:smt(); split => pks c' k; rewrite get_setE /=.
    case: (pks = pkgen ks1 /\ pkgen ks1 = pkgen ks2 /\ c' = c{1}) => />; smt(encapK).
    case: (pks = pkgen ks1 /\ c' = c{1}) => />; smt(encapK). 
  + split; 1:smt(); split => pks c' k; rewrite get_setE /=.
    case: (pks = pkgen ks2 /\ c' = c{1}) => />; smt(encapK). 
    case: (pks = pkgen ks2 /\ pkgen ks2 = pkgen ks1 /\ c' = c{1}) => />; smt(encapK).
  + split; 1:smt(); split => pks c' k; rewrite get_setE /=.
    case: (pks = pkgen ks2 /\ pkgen ks1 = pkgen ks2 /\ c' = c{1}) => />; smt(encapK).
    case: (pks = pkgen ks2 /\ c' = c{1}) => />; smt(encapK). 
- move=>*; islossless.
- move=> *; proc; inline*. swap 9 -8.
  conseq (:_ ==> true) (:_ ==> _); auto; last by islossless.
  seq 1 : #pre; [by auto;smt()| by conseq />].
by auto => />; smt(emptyE).
qed.

(* In the real game, B(A) corresponds to the game 
   q <$ [1..qc]; G.work(q) *)
local lemma OrealB_Gq &m : 
  Pr [ Game(Oreal, B(A)).main() @ &m : res] = 
  Pr [ M1.Rand(G).main() @ &m : res.`2].
proof.
byequiv => //; proc; inline *; auto.
call (: ={glob Oreal} /\ 
        ={m}(B.OB,Oideal) /\ 
        ={ctr,q}(B.OB,OG)
      ).
- sim.
- sim.
- proc. inline*. sp 2 6.
  by if; [move => />|auto|auto; call(:true); auto]. 
- proc; inline OG.chall B(A, Count(Oreal)).OB.pkey OG.skey OG.pkey.
  wp. sp 3 6. 
  if{1}. 
  + rcondf{2} 4; first by auto => /> /#.
    inline*; by auto. 
  if{1}. 
  + rcondf{2} 4; first by auto => /> /#.
    by inline*; auto. 
  rcondt{2} 4; first by auto => /> /#.
  by inline*; auto. 
- by swap{1} 10 -9; auto.
qed.

(* In the ideal game, B(A) corresponds to the game 
   q <$ [0..qc-1]; G.work(q) *)
local lemma OidealB_Gq1 &m : 
  Pr [ Game(Oideal,B(A)).main() @ &m : res] = 
  Pr [ M0.Rand(G).main() @ &m : res.`2 ].
proof.
byequiv => //; proc; inline *; auto.
call (: ={glob Oreal} /\ ={m}(B.OB,Oideal) /\ ={ctr}(B.OB,OG) /\
  (B.OB.q{1} = OG.q{2} + 1) /\ 
  (forall x, x \in Oideal.m => x \in B.OB.m){1} ).
- conseq />; sim.
- conseq />; sim.
- proc. 
  inline OG.decap B(A, Count(Oideal)).OB.pkey Oideal.skey. 
  sp 2 6. 
  if; [by move => />|by auto|]. inline*. 
  rcondf{1} 8. move => &m0; auto => /> /#.
  by auto.
- proc; inline OG.chall B(A, Count(Oreal)).OB.pkey OG.skey OG.pkey.
  wp. sp 3 6. 
  if{1}. 
  + rcondf{2} 4; first by auto => /> /#. 
    by inline*; auto; smt(mem_set).
  if{1}. 
  + rcondt{2} 4; first by auto => /> /#.
    by inline*; auto; smt(mem_set).
  rcondt{2} 4; first by auto => /> /#.
  by inline*; auto; smt(mem_set).
- swap{1} 11 -10; wp; rnd; rnd; wp. 
  rnd (fun n => n - 1) (fun n => n + 1). 
  auto => />; smt(supp_dinter dinter1E).
qed.



local module H(O:Oracle) = {
  proc main() = {
    var r;
    B.OB.q <$ [1..qc];                   
    B.OB.ctr <- 0;                       
    B.OB.m <- empty;
    Count(B(A,CB.Count(O)).OB).init();
    r <@ A(Count(B(A, CB.Count(O)).OB)).guess();
  }
}.

local equiv foo (O<:Oracle{A,B,CB.Count,Count}) : 
    B(A,CB.Count(O)).guess ~ H(O).main : 
    ={glob A, glob B, glob O, glob CB.Count} ==> ={glob A, glob B, glob CB.Count}.
proof.
proc; call (: ={glob B, glob CB.Count, glob O}); last by inline *; auto.
- by sim.
- by proc; inline*; sim.
- by proc; inline*; sim; auto.
proc; inline*; auto.
sim / true : (={glob B, glob CB.Count, glob O,c,k,pks,pk}). 
by auto.
qed.

lemma B_bound:
  forall (O <: Oracle{A,B,CB.Count,Count}),
    hoare[ B(A,CB.Count(O)).guess :
            counts0 CB.Count.ce CB.Count.cd CB.Count.cc ==>
            counts (qe+qc) qd 1 CB.Count.ce CB.Count.cd CB.Count.cc].
proof.
move => O.
conseq (foo(O)) 
(: counts0 CB.Count.ce CB.Count.cd CB.Count.cc ==> 
   counts (qe+qc) qd 1 CB.Count.ce CB.Count.cd CB.Count.cc); 1,2: smt().
proc.
conseq 
  (: _ ==> counts qe qd qc Count.ce Count.cd Count.cc) 
  (: _ ==> counts qe qd qc Count.ce Count.cd Count.cc => 
             counts (qe + qc) qd 1 CB.Count.ce CB.Count.cd CB.Count.cc).
- smt(). 
- smt(). 
- call (: CB.Count.cc = b2i (B.OB.q <= B.OB.ctr) /\
          CB.Count.ce <= Count.ce + Count.cc /\
          CB.Count.cd <= Count.cd).
  + by conseq />.
  + proc; inline*; auto; call(: true); auto => /> /#.
  + proc; inline*; auto; conseq />. 
    seq 3 : (CB.Count.cd < Count.cd); 1: by call(:true); auto => /> /#.
    by if; [auto=>/> /#|wp; call(:true); auto => /> /#].
  + proc; inline*; auto; conseq />. 
    seq 3 : (#[1]pre /\  CB.Count.ce < Count.ce + Count.cc).
      by call(:true); auto => /> /#.
    sp; if; 1: by call(:true); auto; call(:true); auto => /> /#.
    if; 1: by call(:true); auto; call(:true); auto => /> /#.
    by call(:true); auto; call(:true); auto => /> /#.
  + inline*; auto => />; smt(supp_dinter).
- by call (A_bound (<: B(A,CB.Count(O)).OB)); inline*; auto.
qed.

lemma lemma2 &m : 
  `| Pr[ Game(Oreal ,A).main() @ &m : res ] - 
     Pr[ Game(Oideal,A).main() @ &m : res] |
= qc%r * `| Pr[ Game(Oreal ,B(A)).main() @ &m : res] - 
            Pr[ Game(Oideal,B(A)).main() @ &m : res]|.
proof.
rewrite Oreal_G0 Oideal_Gqc OrealB_Gq OidealB_Gq1.
pose ev (_:int) (_:glob G) (b : bool) := b.
have /= -> := M1.Mean_uni G &m ev (1%r/qc%r) _ (finite_dinter 1 qc). 
  by move=> x /supp_dinter1E -> /#.
have /= -> := M0.Mean_uni G &m ev (1%r/qc%r) _ (finite_dinter 0 (qc-1)). 
  by move=> x /supp_dinter1E -> /#.
rewrite /ev /=.
rewrite (eq_big_perm _ _ _ _ (supp_range 1 qc)).
rewrite (eq_big_perm _ _ _ _ (supp_range_pred 0 qc)).
rewrite [range 0 _]range_ltn 1:#smt big_cons {2}/predT /=. 
rewrite rangeSr 1:#smt big_rcons {1}/predT /=.
rewrite -StdOrder.RealOrder.normrZ. smt.
rewrite RField.mulrBr ![qc%r * _]RField.mulrC -!RField.mulrA RField.mulVf /=; 1:smt.
by have -> : forall (a b c : real), a + b - (c + a) = b - c by smt().
qed.

end section PROOF.
  
end Outsider2CCA.


(** * n-participant version of Outsider-CCA *)

theory OutsiderCCA.

op n : { int | 0 < n } as n_gt0.
op qe : { int | 0 < qe } as qe_gt0.
op qd : int.

module type Oracle = {
  proc encap (i : int, pk : pkey) : ciphertext * key
  proc decap (j : int, pk : pkey, c : ciphertext) : key option
  proc pkey(i : int) : pkey
}.

module type Oracle_i = {
  proc init () : unit
  include Oracle
}.

module type Adversary (O : Oracle) = {
  proc guess () : bool
}.

abstract theory MkCount.
module Count (O : Oracle) = { 
  var ce, cd : int

  proc init() = {
    ce <- 0;
    cd <- 0;
  } 

  proc pkey = O.pkey

  proc encap(x) = { 
    var r; 
    ce <- ce + 1 ;
    r <@ O.encap(x);
    return r;
  }

  proc decap(x) = { 
    var r; 
    cd <- cd + 1 ;
    r <@ O.decap(x);
    return r;
  }
}.
end MkCount.
clone import MkCount as C.

module Game (O : Oracle_i, A : Adversary) = {
  proc main() = {
    var r;

    O.init();
    Count(O).init();
    r <@ A(Count(O)).guess();
    return r;
  }
}.

clone import PROM.FullRO as K with
  type in_t    <- int,
  type out_t   <- keyseed,
  op dout      <- fun _ => dkeyseed,
  type d_in_t  <- unit,
  type d_out_t <- bool
proof*.
module KS = K.RO.

(* We don't want to use an oracle at this point 
clone import PROM.FullRO as E with
  type in_t    <- int,
  type out_t   <- encseed,
  op dout      <- fun _ => dencseed,
  type d_in_t  <- unit,
  type d_out_t <- bool.
module ES = E.RO. *)

(* The "real" game: encap and decap answer faithfully. Note that,
unlike in the paper, participants (i.e., their associated keyseed) are
generated "on-demand" whenever the adversary calls an oracle with the
index of a given participant. This matches the behavior of the CV
code. *)
module Oreal : Oracle_i = { 
  proc init() : unit = { 
    KS.init();
  }

  (* provide oracle access to public keys *)
  proc pkey (i : int) = {
    var ks;
    var pk:pkey <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      pk <- pkgen(ks);
    }
    return pk;
  }

  proc encap (i : int,  pk : pkey) : ciphertext * key = { 
    var es,ks,sk;
    var c <-witness;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      es <$ dencseed;
      sk <- skgen(ks);
      (c,k) <- encap es sk pk;
    }
    return (c,k);
  }

  proc decap (i : int, pk : pkey, c : ciphertext) : key option = {
    var ks,sk;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      sk <- skgen(ks);
      k <- decap sk pk c;
    }
    return k;
  } 
}.

(* The "ideal" game: we radmomize the shared key if the revceiver
public key belongs to a participant of the game. Note that KS.allKnown
returns only the keyseeds that have acutally been returned by KS.get,
keys that have merely been sampled are ignored. *)
module Oideal : Oracle_i = { 
  include Oreal [pkey]
  var m : (pkey * pkey * ciphertext, key) fmap
  
  proc init() = {
    KS.init();
    m <- empty;
  }

  proc encap (i : int,  pk : pkey) : ciphertext * key = { 
    var es,ks,sk,pks,m_ks;
    var c <-witness;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      es <$ dencseed;
      sk <- skgen(ks);
      (c,k) <- encap es sk pk;
      m_ks <@ KS.restrK();
      if (find (fun _ ks => pk = pkgen ks) m_ks <> None)
      { 
        k <$ dkey; 
        pks <- pkgen(ks);
        m.[(pks,pk,c)] <- k;
      }
    }
    return (c,k);
  }

  proc decap (i : int, pk : pkey, c : ciphertext) : key option = {
    var ks,sk,pki;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      pki <- pkgen(ks);
      if ((pk,pki,c) \in m) { 
        k <- m.[pk,pki,c];
      } else {
        sk <- skgen(ks);      
        k <- decap sk pk c;
      }
    }
    return k;
  } 
}.

clone Outsider2CCA as O2 with
  op qe <- qe,
  op qd <- qd,
  op qc <- qe,
  axiom qc_gt0 = qe_gt0
proof*.

(* B is an adversary against the Outsider-2-CCA game, which does not
use KS or ES. Hence, we can reuse them here. *)
module (B (A : Adversary) : O2.Adversary) (O2 : O2.Oracle) = {
  module O = {
    var u,v : int
    var f : int -> user
    var m : (pkey * pkey * ciphertext, key) fmap

    (* map of participants and their keys, needed to check whether a pkey 
       belongs to a participant without accidentally sampling a new keyseed *)
    var mpk : (int, pkey) fmap
    var msk : (int, skey) fmap

    (* internal - don't call on u or v *)
    proc skey (i : int) = {
      var ks;
      
      ks <$ dkeyseed;
      if (i \notin msk) { 
        msk.[i] <- skgen(ks);
        mpk.[i] <- pkgen(ks); (* also generate and store pkey *)
      } 
      return oget (msk.[i]);
    }

    proc pkey (i : int) = {
      var ks,pki;
      if (1 <= i <= n) { 
        if (i \notin mpk) {
          if (i = u \/ i = v) { 
            pki <@ O2.pkey(f i);
            mpk.[i] <- pki;
          } else {
            ks <$ dkeyseed;
            msk.[i] <- skgen(ks); (* also generate and store skey *)
            mpk.[i] <- pkgen(ks); 
          }
        }
      }
      return oget mpk.[i];
    }

    proc encap (i : int, pk : pkey) = {
      var ski,pki,oj,es;
      var c <- witness;
      var k <- witness;
      if (1 <= i <= n) { 
        (* get pkey for i and ensure it has been sampled *)
        pki <@ pkey(i);
        (* determine whether pk belongs to some participant *)
        oj <- find (fun _ pkj => pk = pkj) mpk;
        
        if   (i = u /\ oj = Some v) 
        { (c,k) <- O2.chall(f u, f v); }
        elif (i = u \/ i = v) 
        { (c,k) <- O2.encap(f i, pk); }
        else 
        { (* msk.[i] defined due to pkey call and i <> u,v *) 
          ski <- oget (msk.[i]); 
          es <$ dencseed;
          (c,k) <- encap es ski pk; }
        
        if (oj <> None /\ (u < i \/ i = u /\ v < oget oj)) {
           k <$ dkey;
           pki <- oget (mpk.[i]);
           m.[(pki,pk,c)] <-k;
        }
      }
      return (c,k);
    }

    proc decap (i : int, pk : pkey, c : ciphertext) : key option = { 
      var sk,pki;
      var k <- witness;
      if (1 <= i <= n) {
        pki <@ pkey(i);
        if ((pk,pki,c) \in m) { 
          k <- m.[pk,pki,c];
        } else {
          if (i = u \/ i = v) {
            k <@ O2.decap(f i,pk, c);
          } else {
            sk <@ skey(i);
            k <- decap sk pk c;
          }
        }
      }
      return k;
    }
  }
      
  proc guess() = { 
    var r:bool <- witness;
    (O.u,O.v) <$ [1..n] `*` [1..n];
    O.m <- empty;
    O.mpk <- empty;
    O.msk <- empty;
    O.f <- fun x => if x = O.u then u1 else u2;
    r <@ A(O).guess();
    return r;
  }
}.

section PROOF.

declare module A <: Adversary{Oreal,Oideal,Count,B,
                              O2.C.Count, O2.Oreal, O2.Oideal,O2.B, O2.CB.Count}.

declare axiom A_ll : forall (O <: Oracle{A}),
  islossless O.pkey =>
  islossless O.encap =>
  islossless O.decap => 
  islossless A(O).guess.

local clone Means as M1 with
  type input <- int * int,
  type output <- bool,
  op d <- [1..n] `*` [1..n]
proof *.

local clone Means as M0 with
  type input <- int * int,
  type output <- bool,
  op d <- [1..n] `*` [0..n-1]
proof *.

local module OG : Oracle = {
  include Oreal [init,pkey]
  include var Oideal[decap]
  var u,v : int

  proc encap (i : int,  pk : pkey) : ciphertext * key = { 
    var es,ks,sk,pks,m_ks,oj;
    var c <-witness;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      es <$ dencseed;
      sk <- skgen(ks);
      (c,k) <- encap es sk pk;
      m_ks <@ KS.restrK();
      oj <- find (fun _ ks => pk = pkgen ks) m_ks;
      if (oj <> None /\ (u < i \/ i = u /\ v < oget oj))
      { 
        k <$ dkey; 
        pks <- pkgen(ks);
        m.[(pks,pk,c)] <- k;
      }
    }
    return (c,k);
  }
}.

local module G : M1.Worker = {
  proc work(u:int,v:int) = {
    var r;

    Oideal.init();
    OG.u <- u;
    OG.v <- v;
    r <@ A(OG).guess();
    return r;
  }
}.


local lemma Oreal_Gnn &m : 
  Pr[ Game(Oreal ,A).main() @ &m : res ] = Pr[ G.work(n,n) @ &m : res].
proof.
byequiv => //; proc; inline*.
call(: OG.u{2} = n /\ OG.v{2} = n /\ ={KS.m} /\ (Oideal.m = empty){2} /\
       forall i, i \in KS.m{2} => 1 <= i <= n ).
- proc; inline Oreal.encap; sp; if; 1,3: by auto. 
  seq 4 5 : (={pk,i,ks,es,c,k} /\ ={KS.m} /\ (Oideal.m = empty){2} /\
             OG.u{2} = n /\ OG.v{2} = n /\ (i \in KS.m){2} /\ (m_ks = KS.m){2} /\ 
             (forall i, i \in KS.m => 1 <= i <= n){2}).
    inline*; auto => />; smt(mem_set).
  rcondf{2} 2; last by auto.
  auto => &2 /> ? ks_bound; rewrite negb_and -implybE => /find_not_none /> j ks -> /#.
- proc; inline Oreal.decap; sp; if; 1,3: by auto.
  by inline KS.get; auto => />; smt(mem_set mem_empty).
- proc; inline*; sp; if; 1,3: by auto. auto => />; smt(mem_set).
auto => />; smt(mem_empty).
qed.

local lemma Oideal_G10 &m : 
   Pr[ Game(Oideal ,A).main() @ &m : res ] = Pr[ G.work(1,0) @ &m : res].
proof.
byequiv => //; proc; inline*.
call(: OG.u{2} = 1 /\ OG.v{2} = 0 /\ ={KS.m, Oideal.m} /\ 
       forall i, i \in KS.m{2} => 1 <= i <= n ).
- proc; inline Oideal.encap; sp; if; 1,3: by auto. 
  seq 5 5 : (={pk,i,ks,es,c,k,m_ks} /\ ={KS.m, Oideal.m} /\
             OG.u{2} = 1 /\ OG.v{2} = 0 /\ (m_ks = KS.m){2} /\ (i \in KS.m){2} /\ 
             (forall i, i \in KS.m => 1 <= i <= n){2}).
  + by inline*; auto => />; smt(mem_set).
  sp; if; 2,3: by auto. 
  by move => &1 &2 /> ? ks_bound /find_not_none /> j ks -> /#.
- proc; inline Oideal.decap; sp; if; 1,3: by auto.
  by inline KS.get; auto => />; smt(mem_set).
- proc; inline*; sp; if; 1,3: by auto. auto => />; smt(mem_set).
auto => />; smt(mem_empty).
qed.

local clone PROM.FullRO as K2 with
  type in_t    <- user,
  type out_t   <- keyseed,
  op dout      <- fun _ => dkeyseed,
  type d_in_t  <- unit,
  type d_out_t <- bool
proof*.

local clone K2.FinEager as EK2 with
  theory FinFrom <- UserFinType
proof*.

local module ERO = EK2.FinRO.

(* Variant of the 2p real game where the keys are handled by an oracle *)
local module O2real(K2 : K2.RO) : O2.Oracle_i = {
  proc init() = {
    K2.init();
  }

  proc pkey (u : user) = { 
    var ks;

    ks <@ K2.get(u);
    return (pkgen ks);
  }

  proc skey (u : user) = {
    var ks;

    ks <@ K2.get(u);
    return (skgen ks);
  }

    proc encap (u : user, pk : pkey) = {
    var c,k,sk,es;
   
    sk <@ skey(u);
    es <$ dencseed;
    (c,k) <- encap es sk pk;
    return (c,k);  
  }

  proc decap (u : user, pk : pkey, c : ciphertext) = {
    var k,sk;

    sk <@ skey(u);
    k <- decap sk pk c;
    return k;
  }

  proc chall (snd : user, rcv : user) = {
    var pk,sk,c,k,es;
    
    sk <@ skey(snd);
    pk <@ pkey(rcv);
    es <$ dencseed;

    (c,k) <- encap es sk pk;
    return (c,k);
  }

}.

local module O2ideal (K2 : K2.RO) : O2.Oracle_i = {
  include var O2real(K2)[-init,chall,decap]
  var m : (pkey * pkey * ciphertext, key) fmap

  proc init() = {
    K2.init();
    m <- empty;
  }

  proc decap (u : user, pk : pkey, c : ciphertext) = {
    var k,sku,pku;

    sku <@ skey(u);
    pku <@ pkey(u); 

    if ((pk,pku,c) \in m) {
      k <- m.[(pk,pku,c)];
    } else { 
      k <- decap sku pk c;
    }
    return k;
  }

  proc chall (snd : user, rcv : user) = {
    var pks, pk,sk,c,k,es;
    
    sk <@ skey(snd);
    pk <@ pkey(rcv);
    es <$ dencseed;
    (c,k) <- encap es sk pk;
    k <$ dkey;
    pks <@ pkey(snd); 
    m.[(pks,pk,c)] <- k;
    return (c,k);
  }
}.

local module (Dreal (C : O2.Adversary) : EK2.FinRO_Distinguisher) (K2 : K2.RO) = {
  proc distinguish() = {
    var r;
    O2.C.Count(O2real(K2)).init();
    r <@ C(O2.C.Count(O2real(K2))).guess();
    return r;
  }
}.

local module (Dideal (C : O2.Adversary) : EK2.FinRO_Distinguisher) (K2 : K2.RO) = {
  proc distinguish() = {
    var r;
    O2ideal.m <- empty;
    O2.C.Count(O2ideal(K2)).init();
    r <@ C(O2.C.Count(O2ideal(K2))).guess();
    return r;
  }
}.

local equiv O2real_lazy (C <: O2.Adversary{K2.RO,O2.Oreal,O2real,O2.C.Count,K2.FRO}) :
  O2.Game(O2.Oreal, C).main ~ O2.Game(O2real(K2.RO), C).main 
  : ={glob C,glob O2.C.Count} ==> ={res}.
proof.
transitivity O2.Game(O2real(ERO),C).main 
  (={glob C,glob O2.C.Count} ==> ={res}) (={glob C,glob O2.C.Count} ==> ={res}); 1,2: smt().
- proc; inline*. 
  rcondt{2} 3; 1: by auto.
  rcondt{2} 6; 1: by auto; smt(emptyE).
  rcondt{2} 8; 1: by auto.
  rcondt{2} 11; 1: by auto => />; smt(get_setE emptyE).
  rcondf{2} 13; 1: by auto.
  wp.
  call (: (forall u, u \in K2.RO.m){2} 
          /\ O2.Oreal.sk1{1} = skgen (oget K2.RO.m.[u1]{2})
          /\ O2.Oreal.pk1{1} = pkgen (oget K2.RO.m.[u1]{2})
          /\ O2.Oreal.sk2{1} = skgen (oget K2.RO.m.[u2]{2})
          /\ O2.Oreal.pk2{1} = pkgen (oget K2.RO.m.[u2]{2})
    ); 1..4: by proc; inline*; auto => />; smt(get_setE).
  by auto => /> /=; smt(get_setE).
transitivity K2.MainD(Dreal(C),ERO).distinguish
  (={glob C,glob O2.C.Count} ==> ={res}) 
  (={glob C,glob O2.C.Count} ==> ={res}); 
    1,2: smt(); first by proc; inline*; sim.
transitivity K2.MainD(Dreal(C),K2.RO).distinguish
  (={glob C,glob O2.C.Count} ==> ={res}) 
  (={glob C,glob O2.C.Count} ==> ={res}); 
    1,2: smt(); last by proc; inline*; sim.
have X := EK2.RO_FinRO_D _ (Dreal(C)); 1: smt(dkeyseed_ll). 
by symmetry; conseq X; auto. 
qed.

local equiv O2ideal_lazy (C <: O2.Adversary{K2.RO,O2.Oideal,O2ideal,O2.C.Count,K2.FRO}) :  
  O2.Game(O2.Oideal, C).main ~ O2.Game(O2ideal(K2.RO), C).main 
  : ={glob C,glob O2.C.Count} ==> ={res}.
proof.
transitivity O2.Game(O2ideal(ERO),C).main 
  (={glob C,glob O2.C.Count} ==> ={res}) 
  (={glob C,glob O2.C.Count,glob O2ideal} ==> ={res}); 1,2: smt().
- proc; inline*. 
  rcondt{2} 3; 1: by auto.
  rcondt{2} 6; 1: by auto; smt(emptyE).
  rcondt{2} 8; 1: by auto.
  rcondt{2} 11; 1: by auto => />; smt(get_setE emptyE).
  rcondf{2} 13; 1: by auto.
  wp.
  call (: (forall u, u \in K2.RO.m){2} 
          /\ O2.Oreal.sk1{1} = skgen (oget K2.RO.m.[u1]{2})
          /\ O2.Oreal.pk1{1} = pkgen (oget K2.RO.m.[u1]{2})
          /\ O2.Oreal.sk2{1} = skgen (oget K2.RO.m.[u2]{2})
          /\ O2.Oreal.pk2{1} = pkgen (oget K2.RO.m.[u2]{2})
          /\ ={m}(O2.Oideal,O2ideal)
    ); 1..4: by proc; inline*; auto => />; smt(get_setE).
  by auto => /> /=; smt(get_setE).
transitivity K2.MainD(Dideal(C),ERO).distinguish
  (={glob C,glob O2.C.Count,glob O2ideal} ==> ={res}) 
  (={glob C,glob O2.C.Count,glob O2ideal} ==> ={res}); 
    1,2: smt(); first by proc; inline*; sim.
transitivity K2.MainD(Dideal(C),K2.RO).distinguish
  (={glob C,glob O2.C.Count,glob O2ideal} ==> ={res}) 
  (={glob C,glob O2.C.Count,glob O2ideal} ==> ={res}); 
    1,2: smt(); last by proc; inline*; sim.
have X := EK2.RO_FinRO_D _ (Dideal(C)); 1: smt(dkeyseed_ll). 
by symmetry; conseq X; auto => />.
qed.

local lemma OrealB_Guv &m : 
  Pr [ O2.Game(O2.Oreal, B(A)).main() @ &m : res] = 
  Pr [ M1.Rand(G).main() @ &m : res.`2].
proof.
have -> : Pr[O2.Game(O2.Oreal, B(A)).main() @ &m : res] =
          Pr[O2.Game(O2real(K2.RO), B(A)).main() @ &m : res] by byequiv (O2real_lazy (B(A))).
byequiv => //; proc; inline *. 
wp. call (: ={u,v}(B.O,OG)  
            /\ (B.O.f{1} = fun i => if i = B.O.u then u1 else u2){1}
            /\ B.O.mpk{1} = map (fun _ ks => pkgen ks) RO.m{2}
            /\ (forall i, i <> OG.u{2} => i <> OG.v{2} => B.O.msk.[i]{1} = omap skgen RO.m.[i]{2})
            /\ (forall i, !(1 <= i <= n) => B.O.mpk.[i] = None){1}
            /\ (forall i, i = OG.u{2} \/ i = OG.v{2} => K2.RO.m.[B.O.f i]{1} = RO.m.[i]{2})
            /\ ={m}(B.O,Oideal)
          ). 
- proc; sp; if; 1,3: by auto.
  seq 1 1 : (#[/5:]pre /\ pki{1} = pkgen ks{2} /\ KS.m.[i]{2} = Some ks{2}). 
  + (* redo pkey proof ... *) 
    inline*. rcondt{1} 2; 1: by auto. sp.
    if{1}. 
    + rcondt{2} 2; first by auto => />; smt(mem_map).
      if{1}. 
      * rcondt{1} 4; 1: by auto => />; smt(fmapP mem_map oget_map).
        wp. rnd. auto. move => /> &1 &2; smt(get_setE map_set). 
      * wp. rnd. auto. move => />; smt(fmapP get_setE map_set). 
    + rcondf{2} 2; first by auto => />; smt(mem_map). 
      auto => />; smt(oget_map mem_map).
  seq 2 3 : (#pre /\ ={c,k} /\ (oj = find (fun (_ : int) (pkj : pkey) => pk = pkj) B.O.mpk){1}).
  + sp; if{1}; last if{1}.
    * (* challenge oracle query *)
      inline*. (* TODO: cleanup *)
      rcondf{1} 7; first by auto => />; smt(fmapP). 
      rcondf{1} 12. 
        auto => />. progress. case (OG.v{m0} = OG.u{m0}) => ?. smt(). 
        move/find_some : H5 => -[pku]. rewrite mapE /= -H1 //= ifF //. smt().
      auto => /> &1 &2 2? HK2 2? Hu Hv 4? es _. rewrite !HK2 //. have /= -> := HK2 (OG.u{2}).
      rewrite Hu. case/find_some: Hv => pk'. rewrite mapE /=. smt().
    * (* encap oracle query *)
      inline*. 
      rcondf{1} 7; first by auto => />; smt(fmapP). 
      by auto => /> &1 &2 ? ? HK2 ? ? ? ? ? _ _ es _; rewrite HK2 // /#. 
    * (* encapsulate locally *)
      by auto => />; smt(). 
  inline KS.restrK; sp. 
  if; 2,3: by auto => />; smt(oget_map mem_map). 
  by move => /> ? ?; rewrite !find_map /#.
- proc; sp; if; 1,3: by auto.
  inline B(A, O2.C.Count(O2real(K2.RO))).O.pkey KS.get; sp.
  seq 2 4 : (#pre /\ ={pki} /\ pki{1} = pkgen ks{2} /\ KS.m.[i]{2} = Some ks{2}). 
  (* redo pkey proof once again *)
  + inline*. rcondt{1} 1; first by auto. 
    if{1}.
    + rcondt{2} 2; first by auto => />; smt(mem_map).
      if{1}.
      * rcondt{1} 4; 1: by auto => />; smt(fmapP mem_map oget_map).
        wp. rnd. auto. move => /> &1 &2; smt(get_setE map_set).
      * wp. rnd. auto. move => />; smt(fmapP get_setE map_set).
    + rcondf{2} 2; first by auto => />; smt(mem_map).
      auto => />; smt(oget_map mem_map).
  if; 1,2: by auto. 
  if{1}. 
  + inline*.
    rcondf{1} 7; first by auto => /> /#.
    by auto => /> &1 &2 ? ? HK2 ? ? ? ? ? _ _; rewrite HK2 //= /#. 
  + inline*. rcondf{1} 3; first by auto => /> /#.
    by auto => /> &1 &2 Hmsk ? HK2 ? ? ? ? ? _ _; rewrite Hmsk //= /#. 
- proc. sp. inline*. if; 1,3: by auto => /#.
  if{1}. 
  + rcondt{2} 3; first by auto => />; smt(mem_map).
    if{1}. 
    * rcondt{1} 4; 1: by auto => />; smt(fmapP mem_map oget_map).
      wp. rnd. auto. move => /> &1 &2; smt(get_setE map_set). 
    * wp. rnd. auto. move => />; smt(fmapP get_setE map_set). 
  + rcondf{2} 3; first by auto => />; smt(mem_map). 
    auto => />; smt(oget_map mem_map).
auto => />; smt(map_empty emptyE).
qed.

local lemma OidealB_Guv1 &m : 
  Pr [ O2.Game(O2.Oideal, B(A)).main() @ &m : res] = 
  Pr [ M0.Rand(G).main() @ &m : res.`2].
proof.
have -> : Pr[O2.Game(O2.Oideal, B(A)).main() @ &m : res] =
          Pr[O2.Game(O2ideal(K2.RO), B(A)).main() @ &m : res] by byequiv (O2ideal_lazy (B(A))).
byequiv => //; proc; inline *. 
wp. call (: ={u}(B.O,OG) /\ B.O.v{1} = OG.v{2} + 1
            /\ (B.O.f{1} = fun i => if i = B.O.u then u1 else u2){1}
            /\ B.O.mpk{1} = map (fun _ ks => pkgen ks) RO.m{2}
            /\ (forall i, i <> OG.u{2} => i <> OG.v{2} => B.O.msk.[i]{1} = omap skgen RO.m.[i]{2})
            /\ (forall i, !(1 <= i <= n) => B.O.mpk.[i] = None){1}
            /\ (forall i, i = OG.u{2} \/ i = OG.v{2} => K2.RO.m.[B.O.f i]{1} = RO.m.[i]{2})
            /\ ={m}(B.O,Oideal)
          ). 
- proc; sp; if; 1,3: by auto.
  seq 1 1 : (#[/5:]pre /\ pki{1} = pkgen ks{2} /\ KS.m.[i]{2} = Some ks{2}). 
  + admit.
  seq 2 3 : (#pre /\ ={c,k} /\ (oj = find (fun (_ : int) (pkj : pkey) => pk = pkj) B.O.mpk){1}).
  + sp; if{1}; last if{1}.
    * (* challenge oracle query *)
      inline*. (* TODO: cleanup *)
      rcondf{1} 7; first by auto => />; smt(fmapP). 
      rcondf{1} 12. 
        auto => />. progress. case (OG.v{m0} + 1 = OG.u{m0}) => ?. smt(). 
        move/find_some : H5 => -[pku]. rewrite mapE /= -H1 //=. (* ifF //. smt(). *)
  (*     auto => /> &1 &2 2? HK2 2? Hu Hv 4? es _. rewrite !HK2 //. have /= -> := HK2 (OG.u{2}). *)
  (*     rewrite Hu. case/find_some: Hv => pk'. rewrite mapE /=. smt(). *)
  (*   * (* encap oracle query *) *)
  (*     inline*.  *)
  (*     rcondf{1} 7; first by auto => />; smt(fmapP).  *)
  (*     by auto => /> &1 &2 ? ? HK2 ? ? ? ? ? _ _ es _; rewrite HK2 // /#.  *)
  (*   * (* encapsulate locally *) *)
  (*     by auto => />; smt().  *)
  (* inline KS.restrK; sp.  *)
  (* if; 2,3: by auto => />; smt(oget_map mem_map).  *)
  (* by move => /> ? ?; rewrite !find_map /#.   *)
admitted.

local lemma G_shift &m u : 1 <= u < n =>
  Pr [G.work(u,n) @ &m : res] = Pr [G.work(u+1,0) @ &m : res].
admitted.

lemma lemma3 &m : 
  `| Pr[ Game(Oreal ,A).main() @ &m : res ] - 
     Pr[ Game(Oideal,A).main() @ &m : res] |
=  (n^2)%r * `| Pr[ O2.Game(O2.Oreal ,B(A)).main() @ &m : res] - 
                Pr[ O2.Game(O2.Oideal,B(A)).main() @ &m : res]|.
proof.
rewrite Oreal_Gnn Oideal_G10 OrealB_Guv OidealB_Guv1.
have fin_prod : forall a b, is_finite (support ([1..n] `*` [a..b])). admit.
have -> /= := M1.Mean_uni G &m (fun _ _ b => b) (1%r/(n^2)%r) _ _.
- admit.
- exact fin_prod.
have -> /= := M0.Mean_uni G &m (fun _ _ b => b) (1%r/(n^2)%r) _ _.
- admit.
- exact fin_prod.
pose s1 := to_seq _; pose s0 := to_seq _.
have uniq_s1 : uniq s1 by apply/uniq_to_seq/fin_prod.
have uniq_s0 : uniq s0 by apply/uniq_to_seq/fin_prod.
rewrite (big_rem _ _ s1 (n,n)) {1}/predT /=. admit.
rewrite (big_rem _ _ s0 (1,0)) {2}/predT /=. admit.
rewrite -StdOrder.RealOrder.normrZ. smt.
rewrite RField.mulrBr ![(n^2)%r * _]RField.mulrC -!RField.mulrA RField.mulVf /=; 1:smt.
suff -> : big predT (fun (v : int * int) => Pr[G.work(v) @ &m : res]) (rem (n, n) s1)
        = big predT (fun (v : int * int) => Pr[G.work(v) @ &m : res]) (rem (1, 0) s0).
by have -> : forall (a b c : real), b + a - (c + a) = b - c by smt().
pose f (v : int * int) := if v.`2 = n then (v.`1+1,0) else v.
pose g (v : int * int) := if v.`2 = 0 then (v.`1-1,n) else v.
have can_f : forall x, x \in rem (1,0) s0 => f (g x) = x. 
  case => u v. rewrite uniq_mem_rem // /s1 mem_to_seq ?fin_prod /=.
  by rewrite supp_dprod /= !supp_dinter /f /g /= /#.
rewrite (big_reindex _ _ _ _ _ can_f) /(\o).
rewrite [big _ _ (List.map _ _)](eq_big_perm _ _ _ (rem (n, n) s1)).
- (* TODO: clean this up *)
  apply uniq_perm_eq; 2: by rewrite rem_uniq uniq_to_seq fin_prod.
  + rewrite map_inj_in_uniq 1:/# rem_uniq uniq_to_seq fin_prod.
  + case => u v. rewrite uniq_mem_rem // mem_to_seq ?fin_prod supp_dprod !supp_dinter /=.
    split => [/mapP [[u' v']]|]. 
    * rewrite uniq_mem_rem // mem_to_seq ?fin_prod supp_dprod !supp_dinter /=. smt().
    * move => ?. apply/mapP; exists (f (u,v)). 
      rewrite uniq_mem_rem // mem_to_seq ?fin_prod supp_dprod !supp_dinter /=. smt().
apply eq_big_seq => // -[u v]. 
rewrite uniq_mem_rem // mem_to_seq ?fin_prod supp_dprod !supp_dinter /=.
rewrite /f /=. case (v = n) => // -> {v} ?. apply: G_shift. smt().
qed.

(* combining everything to get the theorem *)
module B11 (A : Adversary) : O2.Adversary = O2.B(B(A)).

(* The advantage of A is [n^2 * qc] times the advantage of B11 ...  *)
lemma theorem11 &m : 
  `| Pr[ Game(Oreal ,A).main() @ &m : res ] - 
     Pr[ Game(Oideal,A).main() @ &m : res ] | 
= (n^2 * qe)%r * `| Pr[ O2.Game(O2.Oreal ,B11(A)).main() @ &m : res] - 
                    Pr[ O2.Game(O2.Oideal,B11(A)).main() @ &m : res]|.
proof. 
have l2 := O2.lemma2 (B(A)) _ _ &m.
- admit. (* B(A) is lossless *)
- admit. (* B(A) stays within the query bound *)
by rewrite lemma3 l2 /#.
qed.

(* ... and B11 makes at most 2*qe queries to encap, at most qd queries
to decap, and at most one challenge querey. *)
lemma B11_bound : 
  forall (O <: O2.Oracle{A,B,O2.CB.Count,Count}),
    hoare[ B11(A,O2.CB.Count(O)).guess :
            O2.counts0 O2.CB.Count.ce O2.CB.Count.cd O2.CB.Count.cc ==>
            O2.counts (2*qe) qd 1 O2.CB.Count.ce O2.CB.Count.cd O2.CB.Count.cc].
admitted.

end section PROOF.  

end OutsiderCCA.
