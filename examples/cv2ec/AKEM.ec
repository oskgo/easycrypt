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

(* end preliminaries *)

require StdBigop.
import StdBigop.Bigreal.BRA.

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
module KS = K.FRO.

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
  include Oreal [init,pkey]
  var m : (pkey * pkey * ciphertext, key) fmap

  proc encap (i : int,  pk : pkey) : ciphertext * key = { 
    var es,ks,sk,pks,m_ks;
    var c <-witness;
    var k <- witness;
    if (1 <= i <= n) {
      ks <@ KS.get(i);
      es <$ dencseed;
      sk <- skgen(ks);
      (c,k) <- encap es sk pk;
      m_ks <@ KS.allKnown();
      if (pk \in frng (map (fun _ ks => pkgen ks) m_ks))
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

    (* internal *)
    proc skey (i : int) = {
      var ks;
      ks <@ KS.get(i);
      return skgen(ks);
    } 

    proc pkey (i : int) = {
      var ks;
      var pk <- witness;
      if (1 <= i <= n) { 
        if (i = u \/ u = v) { 
          pk <- O2.pkey(f i);
        } else {
          ks <@ KS.get(i);
          pk <- pkgen(ks);    
        }
      }
      return pk;
    }

    proc encap (i : int, pk : pkey) = {
      var ski,pki,pkj,m_ks,o_j,j,es;
      var c <- witness;
      var k <- witness;
      if (1 <= i <= n) { 
        if (i = u \/ u = v) { 
          (c,k) <- O2.encap(f i,pk);
        } else {
          ski <@ skey(i);
          es <$ dencseed;
          (c,k) <- encap es ski pk;
        }
        m_ks <@ KS.allKnown();
        o_j <- find (fun x ks => pk = pkgen(ks)) m_ks;
        if (o_j <> None) { (* given public key belongs to some user j *)
          j <- oget o_j;
          if (i = u /\ j = v) { 
            (c,k) <- O2.chall(u1, f j); (* if u = v, f j is u1, else u2 *)
          } elif (u < i \/ i = u /\ v < j) {
            k <$ dkey;
            pki <@ pkey(i);
            pkj <@ pkey(j); 
            m.[(pki,pkj,c)] <- k;
          } 
        }
      }
      return (c,k);
    }

    proc decap (i : int, pk : pkey, c : ciphertext) : key option = { 
      return None;
    }
  }

  proc guess() = { 
    var r:bool <- witness;
    KS.init();
    O.u <$ [1..n];
    O.v <$ [1..n];
    O.m <- empty;
    O.f <- fun x => if x = O.u then u1 else u2;
    r <@ A(O).guess();
    return r;
  }
}.
    
section PROOF.

declare module A <: Adversary{Oreal,Oideal,Count,
                              O2.C.Count, O2.Oreal, O2.Oideal,O2.B, O2.CB.Count}.

declare axiom A_ll : forall (O <: Oracle{A}),
  islossless O.pkey =>
  islossless O.encap =>
  islossless O.decap => 
  islossless A(O).guess.

lemma lemma3 &m : 
  `| Pr[ Game(Oreal ,A).main() @ &m : res ] - 
     Pr[ Game(Oideal,A).main() @ &m : res] |
=  (n^2)%r * `| Pr[ O2.Game(O2.Oreal ,B(A)).main() @ &m : res] - 
                Pr[ O2.Game(O2.Oideal,B(A)).main() @ &m : res]|.
admitted.

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
- admit. 
- admit.
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
