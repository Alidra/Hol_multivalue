Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_MOD_term_abbrevs.
Require Import ADD_AC_spec.
Require Import DIVISION_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import MOD_EQ_spec.
Require Import MOD_ZERO_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_EQ_0_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem182190 (m : nat) : term0 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem182191 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem182192 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem182191 m) (@lem182190 m)). Qed.
Lemma lem182193 (m : nat) (n : nat) (p : nat) : term2 m n p.
Proof. exact (@lem182192 m (Nat.mul n p)). Qed.
Lemma lem182194 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (term3 m n p).
Proof. exact (eq_refl (term2 m n p)). Qed.
Lemma lem182195 (m : nat) (n : nat) (p : nat) : term3 m n p.
Proof. exact (EQ_MP (@lem182194 m n p) (@lem182193 m n p)). Qed.
Lemma lem182196 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem182197 (m : nat) (h1 : term4) : term5 m.
Proof. exact (@lem182196 h1 m). Qed.
Lemma lem182198 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem182199 (m : nat) (h1 : term4) : term6 m.
Proof. exact (EQ_MP (@lem182198 m) (@lem182197 m h1)). Qed.
Lemma lem182200 (m : nat) (n : nat) (h1 : term4) : term7 m n.
Proof. exact (@lem182199 m h1 n). Qed.
Lemma lem182201 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem182202 (m : nat) (n : nat) (h1 : term4) : term8 m n.
Proof. exact (EQ_MP (@lem182201 m n) (@lem182200 m n h1)). Qed.
Lemma lem182203 (m : nat) (n : nat) (p : nat) (h1 : term4) : term9 m n p.
Proof. exact (@lem182202 m n h1 p). Qed.
Lemma lem182204 (m : nat) (n : nat) (p : nat) : (term9 m n p) = (term10 m n p).
Proof. exact (eq_refl (term9 m n p)). Qed.
Lemma lem182205 (m : nat) (n : nat) (p : nat) (h1 : term4) : term10 m n p.
Proof. exact (EQ_MP (@lem182204 m n p) (@lem182203 m n p h1)). Qed.
Lemma lem182206 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term4) : term11 m n p q.
Proof. exact (@lem182205 m n p h1 q). Qed.
Lemma lem182207 (q : nat) (m : nat) (n : nat) (p : nat) : (term11 m n p q) = (term12 q m n p).
Proof. exact (eq_refl (term11 m n p q)). Qed.
Lemma lem182208 (q : nat) (m : nat) (n : nat) (p : nat) (h1 : term4) : term12 q m n p.
Proof. exact (EQ_MP (@lem182207 q m n p) (@lem182206 m n p q h1)). Qed.
Lemma lem182209 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : m = (term13 n q p)) : m = (term13 n q p).
Proof. exact (h1). Qed.
Lemma lem182210 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : term4) (h2 : m = (term13 n q p)) : (Nat.modulo m p) = (Nat.modulo n p).
Proof. exact (@lem182208 q m n p h1 (@lem182209 m n q p h2)). Qed.
Lemma lem182211 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : m = (term13 n q p)) : term14 m n p.
Proof. exact (fun h0 : term4 => @lem182210 m n q p h0 h1). Qed.
Lemma lem182212 (m : nat) (n : nat) (p : nat) (h1 : term15 m n p) : term15 m n p.
Proof. exact (h1). Qed.
Lemma lem182213 (m : nat) (n : nat) (p : nat) (h1 : term15 m n p) : term14 m n p.
Proof. exact (ex_elim (@lem182212 m n p h1) (fun q : nat => fun h0 : term16 m n p q => @lem182211 m n q p h0)). Qed.
Lemma lem182214 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem182215 (m : nat) (n : nat) (p : nat) (h1 : term4) (h2 : term15 m n p) : (Nat.modulo m p) = (Nat.modulo n p).
Proof. exact (@lem182213 m n p h2 (@lem182214 h1)). Qed.
Lemma lem182216 (m : nat) (n : nat) (p : nat) (h1 : term4) : term17 m n p.
Proof. exact (fun h0 : term15 m n p => @lem182215 m n p h1 h0). Qed.
Lemma lem182217 (m : nat) (n : nat) (h1 : term4) : term18 m n.
Proof. exact (fun p : nat => @lem182216 m n p h1). Qed.
Lemma lem182218 (m : nat) (h1 : term4) : term19 m.
Proof. exact (fun n : nat => @lem182217 m n h1). Qed.
Lemma lem182219 (h1 : term4) : term20.
Proof. exact (fun m : nat => @lem182218 m h1). Qed.
Lemma lem182220 : term21.
Proof. exact (fun h0 : term4 => @lem182219 h0). Qed.
Lemma lem182221 : term20.
Proof. exact (@lem182220 (@lem178251)). Qed.
Lemma lem182222 (m : nat) : term22 m.
Proof. exact (@lem182221 m). Qed.
Lemma lem182223 (m : nat) : (term22 m) = (term19 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem182224 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem182223 m) (@lem182222 m)). Qed.
Lemma lem182225 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem182224 m n). Qed.
Lemma lem182226 (m : nat) (n : nat) : (term23 m n) = (term18 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem182227 (m : nat) (n : nat) : term18 m n.
Proof. exact (EQ_MP (@lem182226 m n) (@lem182225 m n)). Qed.
Lemma lem182228 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (@lem182227 m n p). Qed.
Lemma lem182229 (m : nat) (n : nat) (p : nat) : (term24 m n p) = (term17 m n p).
Proof. exact (eq_refl (term24 m n p)). Qed.
Lemma lem182231 (n : nat) : term25 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem182232 (n : nat) : (term25 n) = (term26 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem182233 (n : nat) : term26 n.
Proof. exact (EQ_MP (@lem182232 n) (@lem182231 n)). Qed.
Lemma lem182235 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (h1). Qed.
Lemma lem182236 (p : nat) : term25 p.
Proof. exact (@lem9784 (p = (NUMERAL 0))). Qed.
Lemma lem182237 (p : nat) : (term25 p) = (term26 p).
Proof. exact (eq_refl (term25 p)). Qed.
Lemma lem182238 (p : nat) : term26 p.
Proof. exact (EQ_MP (@lem182237 p) (@lem182236 p)). Qed.
Lemma lem182240 (p : nat) (h1 : term27 p) : term27 p.
Proof. exact (h1). Qed.
Lemma lem182241 : term28.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem182267 : term29.
Proof. exact (proj1 (@lem182241)). Qed.
Lemma lem182268 (m : nat) : term30 m.
Proof. exact (@lem182267 m). Qed.
Lemma lem182269 (m : nat) : (term30 m) = ((term31 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem182275 (n : nat) : term32 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem182276 (n : nat) : (term32 n) = ((term33 n) = n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem182281 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem182282 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem182283 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul n p) = (term31 n).
Proof. exact (MK_COMB (@lem182282 n) (@lem182281 p h1)). Qed.
Lemma lem182285 (m : nat) : (term31 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem182269 m) (@lem182268 m)). Qed.
Lemma lem182286 (n : nat) : (term31 n) = (NUMERAL 0).
Proof. exact (@lem182285 n). Qed.
Lemma lem182287 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem182283 n p h1) (@lem182286 n)). Qed.
Lemma lem182288 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem182289 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term34 m n p) = (term33 m).
Proof. exact (MK_COMB (@lem182288 m) (@lem182287 n p h1)). Qed.
Lemma lem182291 (n : nat) : (term33 n) = n.
Proof. exact (EQ_MP (@lem182276 n) (@lem182275 n)). Qed.
Lemma lem182292 (m : nat) : (term33 m) = m.
Proof. exact (@lem182291 m). Qed.
Lemma lem182293 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term34 m n p) = m.
Proof. exact (TRANS (@lem182289 n m p h1) (@lem182292 m)). Qed.
Lemma lem182294 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem182295 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term35 m n p) = (Nat.modulo m).
Proof. exact (MK_COMB (@lem182294) (@lem182293 n m p h1)). Qed.
Lemma lem182296 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem182297 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term36 m p n) = (Nat.modulo m n).
Proof. exact (MK_COMB (@lem182295 n m p h1) (@lem182296 n)). Qed.
Lemma lem182298 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem182299 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term37 m p n) = (term38 m n).
Proof. exact (MK_COMB (@lem182298) (@lem182297 m n p h1)). Qed.
Lemma lem182300 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (eq_refl (Nat.modulo m n)). Qed.
Lemma lem182301 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term36 m p n) = (Nat.modulo m n)) = ((Nat.modulo m n) = (Nat.modulo m n)).
Proof. exact (MK_COMB (@lem182299 m n p h1) (@lem182300 m n)). Qed.
Lemma lem182303 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem182304 (x : nat) : (x = x) = True.
Proof. exact (@lem182303 nat x). Qed.
Lemma lem182305 (m : nat) (n : nat) : ((Nat.modulo m n) = (Nat.modulo m n)) = True.
Proof. exact (@lem182304 (Nat.modulo m n)). Qed.
Lemma lem182306 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term36 m p n) = (Nat.modulo m n)) = True.
Proof. exact (TRANS (@lem182301 m n p h1) (@lem182305 m n)). Qed.
Lemma lem182307 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : True = ((term36 m p n) = (Nat.modulo m n)).
Proof. exact (SYM (@lem182306 m n p h1)). Qed.
Lemma lem182308 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term36 m p n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem182307 m n p h1) (@lem0)). Qed.
Lemma lem182393 : term39.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem182394 (n : nat) : term40 n.
Proof. exact (@lem182393 n). Qed.
Lemma lem182395 (n : nat) : (term40 n) = ((term41 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem182397 (n : nat) : term32 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem182398 (n : nat) : (term32 n) = ((term33 n) = n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem182416 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem182417 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem182418 (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n) = term42.
Proof. exact (MK_COMB (@lem182417) (@lem182416 n h1)). Qed.
Lemma lem182419 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem182420 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n p) = (term41 p).
Proof. exact (MK_COMB (@lem182418 n h1) (@lem182419 p)). Qed.
Lemma lem182422 (n : nat) : (term41 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem182395 n) (@lem182394 n)). Qed.
Lemma lem182423 (p : nat) : (term41 p) = (NUMERAL 0).
Proof. exact (@lem182422 p). Qed.
Lemma lem182424 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem182420 p n h1) (@lem182423 p)). Qed.
Lemma lem182425 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem182426 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term34 m n p) = (term33 m).
Proof. exact (MK_COMB (@lem182425 m) (@lem182424 p n h1)). Qed.
Lemma lem182428 (n : nat) : (term33 n) = n.
Proof. exact (EQ_MP (@lem182398 n) (@lem182397 n)). Qed.
Lemma lem182429 (m : nat) : (term33 m) = m.
Proof. exact (@lem182428 m). Qed.
Lemma lem182430 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term34 m n p) = m.
Proof. exact (TRANS (@lem182426 p m n h1) (@lem182429 m)). Qed.
Lemma lem182431 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem182432 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term35 m n p) = (Nat.modulo m).
Proof. exact (MK_COMB (@lem182431) (@lem182430 p m n h1)). Qed.
Lemma lem182434 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem182435 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term36 m p n) = (term33 m).
Proof. exact (MK_COMB (@lem182432 p m n h1) (@lem182434 n h1)). Qed.
Lemma lem182437 (n : nat) : (term33 n) = n.
Proof. exact (EQ_MP (@lem182398 n) (@lem182397 n)). Qed.
Lemma lem182438 (m : nat) : (term33 m) = m.
Proof. exact (@lem182437 m). Qed.
Lemma lem182439 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term36 m p n) = m.
Proof. exact (TRANS (@lem182435 p m n h1) (@lem182438 m)). Qed.
Lemma lem182440 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem182441 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term37 m p n) = (@eq nat m).
Proof. exact (MK_COMB (@lem182440) (@lem182439 p m n h1)). Qed.
Lemma lem182443 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem182444 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem182445 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term33 m).
Proof. exact (MK_COMB (@lem182444 m) (@lem182443 n h1)). Qed.
Lemma lem182447 (n : nat) : (term33 n) = n.
Proof. exact (EQ_MP (@lem182398 n) (@lem182397 n)). Qed.
Lemma lem182448 (m : nat) : (term33 m) = m.
Proof. exact (@lem182447 m). Qed.
Lemma lem182449 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = m.
Proof. exact (TRANS (@lem182445 m n h1) (@lem182448 m)). Qed.
Lemma lem182450 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term36 m p n) = (Nat.modulo m n)) = (m = m).
Proof. exact (MK_COMB (@lem182441 p m n h1) (@lem182449 m n h1)). Qed.
Lemma lem182452 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem182453 (x : nat) : (x = x) = True.
Proof. exact (@lem182452 nat x). Qed.
Lemma lem182454 (m : nat) : (m = m) = True.
Proof. exact (@lem182453 m). Qed.
Lemma lem182455 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term36 m p n) = (Nat.modulo m n)) = True.
Proof. exact (TRANS (@lem182450 p m n h1) (@lem182454 m)). Qed.
Lemma lem182456 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term36 m p n) = (Nat.modulo m n)).
Proof. exact (SYM (@lem182455 p m n h1)). Qed.
Lemma lem182457 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term36 m p n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem182456 p m n h1) (@lem0)). Qed.
Lemma lem182525 (p : nat) (m : nat) (n : nat) (h1 : (term36 m p n) = (Nat.modulo m n)) : (term36 m p n) = (Nat.modulo m n).
Proof. exact (h1). Qed.
Lemma lem182526 (p : nat) (m : nat) (n : nat) (h1 : (term36 m p n) = (Nat.modulo m n)) : (Nat.modulo m n) = (term36 m p n).
Proof. exact (SYM (@lem182525 p m n h1)). Qed.
Lemma lem182527 (m : nat) (p : nat) (n : nat) (h1 : (Nat.modulo m n) = (term36 m p n)) : (Nat.modulo m n) = (term36 m p n).
Proof. exact (h1). Qed.
Lemma lem182528 (m : nat) (p : nat) (n : nat) (h1 : (Nat.modulo m n) = (term36 m p n)) : (term36 m p n) = (Nat.modulo m n).
Proof. exact (SYM (@lem182527 m p n h1)). Qed.
Lemma lem182529 (m : nat) (p : nat) (n : nat) : ((term36 m p n) = (Nat.modulo m n)) = ((Nat.modulo m n) = (term36 m p n)).
Proof. exact (prop_ext (fun h1 : (term36 m p n) = (Nat.modulo m n) => @lem182526 p m n h1) (fun h1 : (Nat.modulo m n) = (term36 m p n) => @lem182528 m p n h1)). Qed.
Lemma lem182530 (p : nat) (m : nat) (n : nat) : ((Nat.modulo m n) = (term36 m p n)) = ((term36 m p n) = (Nat.modulo m n)).
Proof. exact (SYM (@lem182529 m p n)). Qed.
Lemma lem182532 (m : nat) (n : nat) (p : nat) : term17 m n p.
Proof. exact (EQ_MP (@lem182229 m n p) (@lem182228 m n p)). Qed.
Lemma lem182533 (m : nat) (p : nat) (n : nat) : term43 m p n.
Proof. exact (@lem182532 m (term34 m n p) n). Qed.
Lemma lem182538 (n : nat) (m : nat) (p : nat) : term44 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem182542 (m : nat) : term45 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem182543 (m : nat) : (term45 m) = (term46 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem182544 (m : nat) : term46 m.
Proof. exact (EQ_MP (@lem182543 m) (@lem182542 m)). Qed.
Lemma lem182545 (m : nat) (n : nat) : term47 m n.
Proof. exact (@lem182544 m n). Qed.
Lemma lem182546 (m : nat) (n : nat) : (term47 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term48 m n)).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem182548 (p : nat) : term49 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem182561 (n : nat) : term49 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem182579 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term48 m n).
Proof. exact (EQ_MP (@lem182546 m n) (@lem182545 m n)). Qed.
Lemma lem182580 (n : nat) (p : nat) : ((Nat.mul n p) = (NUMERAL 0)) = (term48 n p).
Proof. exact (@lem182579 n p). Qed.
Lemma lem182584 (n : nat) (h1 : term27 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem182561 n (@lem182235 n h1)). Qed.
Lemma lem182585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem182586 (n : nat) (h1 : term27 n) : (term50 n) = (or False).
Proof. exact (MK_COMB (@lem182585) (@lem182584 n h1)). Qed.
Lemma lem182588 (p : nat) (h1 : term27 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem182548 p (@lem182240 p h1)). Qed.
Lemma lem182589 (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term48 n p) = (False \/ False).
Proof. exact (MK_COMB (@lem182586 n h1) (@lem182588 p h2)). Qed.
Lemma lem182591 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem182592 : (False \/ False) = False.
Proof. exact (@lem182591 False). Qed.
Lemma lem182593 (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term48 n p) = False.
Proof. exact (TRANS (@lem182589 n p h1 h2) (@lem182592)). Qed.
Lemma lem182594 (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : ((Nat.mul n p) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem182580 n p) (@lem182593 n p h1 h2)). Qed.
Lemma lem182595 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem182596 (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term51 n p) = (~ False).
Proof. exact (MK_COMB (@lem182595) (@lem182594 n p h1 h2)). Qed.
Lemma lem182598 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem182599 (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term51 n p) = True.
Proof. exact (TRANS (@lem182596 n p h1 h2) (@lem182598)). Qed.
Lemma lem182600 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem182601 (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term52 n p) = (imp True).
Proof. exact (MK_COMB (@lem182600) (@lem182599 n p h1 h2)). Qed.
Lemma lem182610 (n : nat) (m : nat) (p : nat) : (term53 m n p) = (term53 n m p).
Proof. exact (proj2 (@lem182538 n m p)). Qed.
Lemma lem182611 (m : nat) (n : nat) (p : nat) : (term54 m n p) = (term55 m n p).
Proof. exact (@lem182610 n (term56 m n p) p). Qed.
Lemma lem182619 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem182620 (m : nat) (n : nat) (p : nat) : (term57 m n p) = (term58 m n p).
Proof. exact (@lem182619 p (term56 m n p)). Qed.
Lemma lem182627 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem182628 (m : nat) (n : nat) (p : nat) : (term55 m n p) = (term59 m n p).
Proof. exact (MK_COMB (@lem182627 n) (@lem182620 m n p)). Qed.
Lemma lem182635 (m : nat) (n : nat) (p : nat) : (term54 m n p) = (term59 m n p).
Proof. exact (TRANS (@lem182611 m n p) (@lem182628 m n p)). Qed.
Lemma lem182636 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem182637 (m : nat) (n : nat) (p : nat) : (term60 m n p) = (term61 m n p).
Proof. exact (MK_COMB (@lem182636) (@lem182635 m n p)). Qed.
Lemma lem182641 (m : nat) (n : nat) (p : nat) : (term34 m n p) = (term34 m n p).
Proof. exact (eq_refl (term34 m n p)). Qed.
Lemma lem182642 (m : nat) (n : nat) (p : nat) : (term62 m n p) = (term63 m n p).
Proof. exact (MK_COMB (@lem182637 m n p) (@lem182641 m n p)). Qed.
Lemma lem182646 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem182647 (m : nat) (n : nat) (p : nat) : (m = (term62 m n p)) = (m = (term63 m n p)).
Proof. exact (MK_COMB (@lem182646 m) (@lem182642 m n p)). Qed.
Lemma lem182650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem182651 (m : nat) (n : nat) (p : nat) : (term64 m n p) = (term65 m n p).
Proof. exact (MK_COMB (@lem182650) (@lem182647 m n p)). Qed.
Lemma lem182658 (m : nat) (n : nat) (p : nat) : (term66 m n p) = (term66 m n p).
Proof. exact (eq_refl (term66 m n p)). Qed.
Lemma lem182659 (m : nat) (n : nat) (p : nat) : (term67 m n p) = (term68 m n p).
Proof. exact (MK_COMB (@lem182651 m n p) (@lem182658 m n p)). Qed.
Lemma lem182662 (m : nat) (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term3 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem182601 n p h1 h2) (@lem182659 m n p)). Qed.
Lemma lem182664 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem182665 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term68 m n p).
Proof. exact (@lem182664 (term68 m n p)). Qed.
Lemma lem182694 (m : nat) (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term3 m n p) = (term68 m n p).
Proof. exact (TRANS (@lem182662 m n p h1 h2) (@lem182665 m n p)). Qed.
Lemma lem182695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem182696 (m : nat) (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term70 m n p) = (term71 m n p).
Proof. exact (MK_COMB (@lem182695) (@lem182694 m n p h1 h2)). Qed.
Lemma lem182700 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem182701 (m : nat) (n : nat) (p : nat) : (term72 m p n) = (term73 m n p).
Proof. exact (@lem182700 (term74 m p n) (term34 m n p)). Qed.
Lemma lem182706 (m : nat) (n : nat) (p : nat) : (term75 m n p) = (term53 m n p).
Proof. exact (proj1 (@lem182538 n m p)). Qed.
Lemma lem182707 (m : nat) (p : nat) (n : nat) : (term74 m p n) = (term76 m p n).
Proof. exact (@lem182706 (term56 m n p) p n). Qed.
Lemma lem182709 (n : nat) (m : nat) (p : nat) : (term53 m n p) = (term53 n m p).
Proof. exact (proj2 (@lem182538 n m p)). Qed.
Lemma lem182710 (m : nat) (p : nat) (n : nat) : (term76 m p n) = (term77 m p n).
Proof. exact (@lem182709 p (term56 m n p) n). Qed.
Lemma lem182717 (m : nat) (p : nat) (n : nat) : (term74 m p n) = (term77 m p n).
Proof. exact (TRANS (@lem182707 m p n) (@lem182710 m p n)). Qed.
Lemma lem182719 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem182720 (m : nat) (n : nat) (p : nat) : (term78 m p n) = (term79 m n p).
Proof. exact (@lem182719 n (term56 m n p)). Qed.
Lemma lem182727 (p : nat) : (Nat.mul p) = (Nat.mul p).
Proof. exact (eq_refl (Nat.mul p)). Qed.
Lemma lem182728 (m : nat) (n : nat) (p : nat) : (term77 m p n) = (term80 m n p).
Proof. exact (MK_COMB (@lem182727 p) (@lem182720 m n p)). Qed.
Lemma lem182730 (n : nat) (m : nat) (p : nat) : (term53 m n p) = (term53 n m p).
Proof. exact (proj2 (@lem182538 n m p)). Qed.
Lemma lem182731 (m : nat) (n : nat) (p : nat) : (term80 m n p) = (term59 m n p).
Proof. exact (@lem182730 n p (term56 m n p)). Qed.
Lemma lem182744 (m : nat) (n : nat) (p : nat) : (term77 m p n) = (term59 m n p).
Proof. exact (TRANS (@lem182728 m n p) (@lem182731 m n p)). Qed.
Lemma lem182745 (m : nat) (n : nat) (p : nat) : (term74 m p n) = (term59 m n p).
Proof. exact (TRANS (@lem182717 m p n) (@lem182744 m n p)). Qed.
Lemma lem182746 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem182747 (m : nat) (n : nat) (p : nat) : (term81 m p n) = (term61 m n p).
Proof. exact (MK_COMB (@lem182746) (@lem182745 m n p)). Qed.
Lemma lem182751 (m : nat) (n : nat) (p : nat) : (term34 m n p) = (term34 m n p).
Proof. exact (eq_refl (term34 m n p)). Qed.
Lemma lem182752 (m : nat) (n : nat) (p : nat) : (term73 m n p) = (term63 m n p).
Proof. exact (MK_COMB (@lem182747 m n p) (@lem182751 m n p)). Qed.
Lemma lem182756 (m : nat) (n : nat) (p : nat) : (term72 m p n) = (term63 m n p).
Proof. exact (TRANS (@lem182701 m n p) (@lem182752 m n p)). Qed.
Lemma lem182757 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem182758 (m : nat) (n : nat) (p : nat) : (m = (term72 m p n)) = (m = (term63 m n p)).
Proof. exact (MK_COMB (@lem182757 m) (@lem182756 m n p)). Qed.
Lemma lem182761 (m : nat) (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term82 m p n) = (term83 m n p).
Proof. exact (MK_COMB (@lem182696 m n p h1 h2) (@lem182758 m n p)). Qed.
Lemma lem182764 (m : nat) (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term83 m n p) = (term82 m p n).
Proof. exact (SYM (@lem182761 m n p h1 h2)). Qed.
Lemma lem182765 (m : nat) (n : nat) (p : nat) (h1 : term68 m n p) : term68 m n p.
Proof. exact (h1). Qed.
Lemma lem182767 (m : nat) (n : nat) (p : nat) (h1 : m = (term63 m n p)) : m = (term63 m n p).
Proof. exact (h1). Qed.
Lemma lem182768 (m : nat) (n : nat) (p : nat) (h1 : m = (term63 m n p)) : (term63 m n p) = m.
Proof. exact (SYM (@lem182767 m n p h1)). Qed.
Lemma lem182769 (n : nat) (p : nat) (m : nat) (h1 : (term63 m n p) = m) : (term63 m n p) = m.
Proof. exact (h1). Qed.
Lemma lem182770 (n : nat) (p : nat) (m : nat) (h1 : (term63 m n p) = m) : m = (term63 m n p).
Proof. exact (SYM (@lem182769 n p m h1)). Qed.
Lemma lem182771 (n : nat) (p : nat) (m : nat) : (m = (term63 m n p)) = ((term63 m n p) = m).
Proof. exact (prop_ext (fun h1 : m = (term63 m n p) => @lem182768 m n p h1) (fun h1 : (term63 m n p) = m => @lem182770 n p m h1)). Qed.
Lemma lem182772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem182773 (n : nat) (p : nat) (m : nat) : (term65 m n p) = (term84 n p m).
Proof. exact (MK_COMB (@lem182772) (@lem182771 n p m)). Qed.
Lemma lem182775 (m : nat) (n : nat) (p : nat) : (term66 m n p) = (term66 m n p).
Proof. exact (eq_refl (term66 m n p)). Qed.
Lemma lem182776 (m : nat) (n : nat) (p : nat) : (term68 m n p) = (term85 m n p).
Proof. exact (MK_COMB (@lem182773 n p m) (@lem182775 m n p)). Qed.
Lemma lem182777 (m : nat) (n : nat) (p : nat) (h1 : term68 m n p) : term85 m n p.
Proof. exact (EQ_MP (@lem182776 m n p) (@lem182765 m n p h1)). Qed.
Lemma lem182785 (m : nat) (n : nat) (p : nat) (h1 : term68 m n p) : (term63 m n p) = m.
Proof. exact (proj1 (@lem182777 m n p h1)). Qed.
Lemma lem182786 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem182787 (m : nat) (n : nat) (p : nat) (h1 : term68 m n p) : (m = (term63 m n p)) = (m = m).
Proof. exact (MK_COMB (@lem182786 m) (@lem182785 m n p h1)). Qed.
Lemma lem182789 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem182790 (x : nat) : (x = x) = True.
Proof. exact (@lem182789 nat x). Qed.
Lemma lem182791 (m : nat) : (m = m) = True.
Proof. exact (@lem182790 m). Qed.
Lemma lem182792 (m : nat) (n : nat) (p : nat) (h1 : term68 m n p) : (m = (term63 m n p)) = True.
Proof. exact (TRANS (@lem182787 m n p h1) (@lem182791 m)). Qed.
Lemma lem182793 (m : nat) (n : nat) (p : nat) (h1 : term68 m n p) : True = (m = (term63 m n p)).
Proof. exact (SYM (@lem182792 m n p h1)). Qed.
Lemma lem182794 (m : nat) (n : nat) (p : nat) (h1 : term68 m n p) : m = (term63 m n p).
Proof. exact (EQ_MP (@lem182793 m n p h1) (@lem0)). Qed.
Lemma lem182795 (m : nat) (n : nat) (p : nat) : term83 m n p.
Proof. exact (fun h0 : term68 m n p => @lem182794 m n p h0). Qed.
Lemma lem182796 (m : nat) (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : term82 m p n.
Proof. exact (EQ_MP (@lem182764 m n p h1 h2) (@lem182795 m n p)). Qed.
Lemma lem182797 (m : nat) (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : m = (term72 m p n).
Proof. exact (@lem182796 m n p h1 h2 (@lem182195 m n p)). Qed.
Lemma lem182798 (m : nat) (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : term86 m p n.
Proof. exact (ex_intro (term87 m p n) (term57 m n p) (@lem182797 m n p h1 h2)). Qed.
Lemma lem182799 (m : nat) (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (Nat.modulo m n) = (term36 m p n).
Proof. exact (@lem182533 m p n (@lem182798 m n p h1 h2)). Qed.
Lemma lem182801 (m : nat) (n : nat) (p : nat) (h1 : term27 n) (h2 : term27 p) : (term36 m p n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem182530 p m n) (@lem182799 m n p h1 h2)). Qed.
Lemma lem182803 (m : nat) (n : nat) (p : nat) (h1 : term27 p) : (term36 m p n) = (Nat.modulo m n).
Proof. exact (or_elim (@lem182233 n) (fun h0 : n = (NUMERAL 0) => @lem182457 p m n h0) (fun h0 : term27 n => @lem182801 m n p h0 h1)). Qed.
Lemma lem182804 (p : nat) (m : nat) (n : nat) : (term36 m p n) = (Nat.modulo m n).
Proof. exact (or_elim (@lem182238 p) (fun h0 : p = (NUMERAL 0) => @lem182308 m n p h0) (fun h0 : term27 p => @lem182803 m n p h0)). Qed.
Lemma lem182809 (m : nat) (n : nat) : term88 m n.
Proof. exact (fun p : nat => @lem182804 p m n). Qed.
Lemma lem182814 (m : nat) : term89 m.
Proof. exact (fun n : nat => @lem182809 m n). Qed.
Lemma lem182819 : term90.
Proof. exact (fun m : nat => @lem182814 m). Qed.
