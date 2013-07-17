require import Bool.
require import Int.
require import Option.
require import List.

type pkey.
type skey.
type plaintext.
type ciphertext.

module type Scheme = {
  fun kg() : pkey * skey 
  fun enc(pk:pkey, m:plaintext)  : ciphertext 
  fun dec(sk:skey, c:ciphertext) : plaintext option
}.

module type Adversary = {
  fun choose(pk:pkey)     : plaintext * plaintext 
  fun guess(c:ciphertext) : bool                  
}.

module CPA (S:Scheme, A:Adversary) = {
  fun main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;

    (pk, sk) = S.kg();
    (m0, m1) = A.choose(pk);
    b        = ${0,1};
    c        = S.enc(pk, b ? m1 : m0);
    b'       = A.guess(c);
    return (b' = b);
  } 
}.


(* 
** Based on lists. Several versions can be given as in RandOrcl.
** Also, oracle annotations could be used to provide different oracles during
** the choose and guess stages of the experiment.
*)
const qD : int.

axiom qD_pos : 0 < qD.

module CCA (S:Scheme, A:Adversary) = {
  var log : ciphertext list
  var cstar : ciphertext
  var guess : bool
  var sk : skey

  fun dec(c:ciphertext) : plaintext option = {
    var m : plaintext option;

    if (length log < qD && (guess => c <> cstar)) {
      log = c :: log;
      m = S.dec(sk, c);
    }
    else m = None;
    return m;
  }

  fun main() : bool = {
    var pk : pkey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;

    log = [];
    guess = false;
    (pk, sk) = S.kg();
    (m0, m1) = A.choose(pk);
    b        = ${0,1};
    c        = S.enc(pk, b ? m1 : m0);
    guess    = true;
    b'       = A.guess(c);
    return (b' = b);
  } 
}.

module Correctness (S:Scheme) = {
  fun main(m:plaintext) : bool = {
    var pk : pkey;
    var sk : skey;
    var c  : ciphertext;
    var m' : plaintext option;

    (pk, sk) = S.kg();
    c        = S.enc(pk, m);
    m'       = S.dec(sk, c); 
    return (m' = Some m);
  }
}.
