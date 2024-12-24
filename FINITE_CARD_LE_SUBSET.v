Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_CARD_LE_SUBSET_term_abbrevs.
Require Import CARD_SUBSET_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import LE_TRANS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem3907201 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3907202 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3907203 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3907202 t1) (@lem3907201 t1)). Qed.
Lemma lem3907204 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3907203 t1 t2). Qed.
Lemma lem3907205 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3907206 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3907205 t1 t2) (@lem3907204 t1 t2)). Qed.
Lemma lem3907207 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3907206 t1 t2 t3). Qed.
Lemma lem3907208 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3907209 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3907208 t1 t2 t3) (@lem3907207 t1 t2 t3)). Qed.
Lemma lem3907210 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3907209 t1 t2 t3)). Qed.
Lemma lem3907212 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3907213 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem3907212 (term8 A)). Qed.
Lemma lem3907214 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem3907213 A)). Qed.
Lemma lem3907215 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3907216 {A : Type'} : term11 A.
Proof. exact (@lem3599924 A). Qed.
Lemma lem3907218 {A : Type'} : term12 A.
Proof. exact (@lem3902682 A). Qed.
Lemma lem3907223 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3907224 {A : Type'} : term14 A.
Proof. exact (fun h0 : term13 A => @lem3907223 A h0). Qed.
Lemma lem3907225 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem3907226 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3907227 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem3907225 A h2 (@lem3907226 A h1)). Qed.
Lemma lem3907228 {A : Type'} (h1 : term13 A) : term15 A.
Proof. exact (fun h0 : term14 A => @lem3907227 A h1 h0). Qed.
Lemma lem3907229 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem3907230 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem3907228 A h1 (@lem3907229 A h2)). Qed.
Lemma lem3907231 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (fun h0 : term13 A => @lem3907230 A h0 h1). Qed.
Lemma lem3907232 {A : Type'} : term16 A.
Proof. exact (fun h0 : term14 A => @lem3907231 A h0). Qed.
Lemma lem3907235 {A : Type'} : term14 A.
Proof. exact (@lem3907232 A (@lem3907224 A)). Qed.
Lemma lem3907236 {A : Type'} : term14 A.
Proof. exact (@lem3907235 A). Qed.
Lemma lem3907292 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3907293 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem3907292 (term11 A)). Qed.
Lemma lem3907306 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem3907307 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem3907306 A) (@lem3907293 A)). Qed.
Lemma lem3907310 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem3907311 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem3907310) (@lem3907307 A)). Qed.
Lemma lem3907314 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (eq_refl (term25 A)). Qed.
Lemma lem3907321 {A : Type'} : (term13 A) = (term26 A).
Proof. exact (MK_COMB (@lem3907314 A) (@lem3907311 A)). Qed.
Lemma lem3907330 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term27 A t s) = (term27 A t s).
Proof. exact (eq_refl (term27 A t s)). Qed.
Lemma lem3907331 {A : Type'} (s : A -> Prop) : (term28 A s) = (term28 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3907330 A t s)). Qed.
Lemma lem3907332 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907333 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (MK_COMB (@lem3907332 A) (@lem3907331 A s)). Qed.
Lemma lem3907334 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3907333 A s)). Qed.
Lemma lem3907335 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907336 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3907335 A) (@lem3907334 A)). Qed.
Lemma lem3907337 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3907338 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem3907337) (@lem3907336 A)). Qed.
Lemma lem3907347 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term31 A a b) = (term31 A a b).
Proof. exact (eq_refl (term31 A a b)). Qed.
Lemma lem3907348 {A : Type'} (a : A -> Prop) : (term32 A a) = (term32 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3907347 A a b)). Qed.
Lemma lem3907349 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907350 {A : Type'} (a : A -> Prop) : (term33 A a) = (term33 A a).
Proof. exact (MK_COMB (@lem3907349 A) (@lem3907348 A a)). Qed.
Lemma lem3907351 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3907350 A a)). Qed.
Lemma lem3907352 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907353 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3907352 A) (@lem3907351 A)). Qed.
Lemma lem3907354 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3907355 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem3907354) (@lem3907353 A)). Qed.
Lemma lem3907356 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem3907355 A) (@lem3907338 A)). Qed.
Lemma lem3907365 (n : nat) (m : nat) (p : nat) : (term35 n m p) = (term35 n m p).
Proof. exact (eq_refl (term35 n m p)). Qed.
Lemma lem3907366 (n : nat) (m : nat) : (term36 n m) = (term36 n m).
Proof. exact (fun_ext (fun p : nat => @lem3907365 n m p)). Qed.
Lemma lem3907367 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3907368 (n : nat) (m : nat) : (term37 n m) = (term37 n m).
Proof. exact (MK_COMB (@lem3907367) (@lem3907366 n m)). Qed.
Lemma lem3907369 (m : nat) : (term38 m) = (term38 m).
Proof. exact (fun_ext (fun n : nat => @lem3907368 n m)). Qed.
Lemma lem3907370 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3907371 (m : nat) : (term39 m) = (term39 m).
Proof. exact (MK_COMB (@lem3907370) (@lem3907369 m)). Qed.
Lemma lem3907372 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem3907371 m)). Qed.
Lemma lem3907373 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3907374 : term41 = term41.
Proof. exact (MK_COMB (@lem3907373) (@lem3907372)). Qed.
Lemma lem3907375 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3907376 : term22 = term22.
Proof. exact (MK_COMB (@lem3907375) (@lem3907374)). Qed.
Lemma lem3907377 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem3907376) (@lem3907356 A)). Qed.
Lemma lem3907394 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) : (term42 A t s n) = (term42 A t s n).
Proof. exact (eq_refl (term42 A t s n)). Qed.
Lemma lem3907395 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term43 A t s) = (term43 A t s).
Proof. exact (fun_ext (fun n : nat => @lem3907394 A t s n)). Qed.
Lemma lem3907396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3907397 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term44 A t s) = (term44 A t s).
Proof. exact (MK_COMB (@lem3907396) (@lem3907395 A t s)). Qed.
Lemma lem3907398 {A : Type'} (s : A -> Prop) : (term45 A s) = (term45 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3907397 A t s)). Qed.
Lemma lem3907399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907400 {A : Type'} (s : A -> Prop) : (term46 A s) = (term46 A s).
Proof. exact (MK_COMB (@lem3907399 A) (@lem3907398 A s)). Qed.
Lemma lem3907401 {A : Type'} : (term47 A) = (term47 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3907400 A s)). Qed.
Lemma lem3907402 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907403 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem3907402 A) (@lem3907401 A)). Qed.
Lemma lem3907404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3907405 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem3907404) (@lem3907403 A)). Qed.
Lemma lem3907406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3907407 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem3907406) (@lem3907405 A)). Qed.
Lemma lem3907408 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem3907407 A) (@lem3907377 A)). Qed.
Lemma lem3907497 {A : Type'} : (term13 A) = (term26 A).
Proof. exact (TRANS (@lem3907321 A) (@lem3907408 A)). Qed.
Lemma lem3907498 {A : Type'} : (term26 A) = (term13 A).
Proof. exact (SYM (@lem3907497 A)). Qed.
Lemma lem3907499 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3907500 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem3907501 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem3907502 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem3907518 {A : Type'} (s : A -> Prop) (n : nat) : (term48 A s n) = (term49 A s n).
Proof. exact (@lem17045 (@FINITE A s) (term50 A s n)). Qed.
Lemma lem3907520 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term51 A s t n) = (term51 A s t n).
Proof. exact (eq_refl (term51 A s t n)). Qed.
Lemma lem3907521 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) : (term52 A t s n) = (term53 A t s n).
Proof. exact (MK_COMB (@lem3907520 A s t n) (@lem3907518 A s n)). Qed.
Lemma lem3907522 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) : (term54 A t s n) = (term52 A t s n).
Proof. exact (@lem17362 (term55 A s t n) (term56 A s n)). Qed.
Lemma lem3907523 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) : (term54 A t s n) = (term53 A t s n).
Proof. exact (TRANS (@lem3907522 A t s n) (@lem3907521 A t s n)). Qed.
Lemma lem3907524 (P : nat -> Prop) : (term57 P) = (term58 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem3907525 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term59 A t s) = (term60 A t s).
Proof. exact (@lem3907524 (term43 A t s)). Qed.
Lemma lem3907526 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) : (term61 A t s n) = (term42 A t s n).
Proof. exact (eq_refl (term61 A t s n)). Qed.
Lemma lem3907527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3907528 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) : (term62 A t s n) = (term54 A t s n).
Proof. exact (MK_COMB (@lem3907527) (@lem3907526 A t s n)). Qed.
Lemma lem3907529 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) : (term62 A t s n) = (term53 A t s n).
Proof. exact (TRANS (@lem3907528 A t s n) (@lem3907523 A t s n)). Qed.
Lemma lem3907530 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term63 A t s) = (term64 A t s).
Proof. exact (fun_ext (fun n : nat => @lem3907529 A t s n)). Qed.
Lemma lem3907531 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3907532 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term60 A t s) = (term65 A t s).
Proof. exact (MK_COMB (@lem3907531) (@lem3907530 A t s)). Qed.
Lemma lem3907533 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term59 A t s) = (term65 A t s).
Proof. exact (TRANS (@lem3907525 A t s) (@lem3907532 A t s)). Qed.
Lemma lem3907534 {A : Type'} (P : type686 A) : (term66 A P) = (term67 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3907535 {A : Type'} (s : A -> Prop) : (term68 A s) = (term69 A s).
Proof. exact (@lem3907534 A (term45 A s)). Qed.
Lemma lem3907536 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term70 A s t) = (term44 A t s).
Proof. exact (eq_refl (term70 A s t)). Qed.
Lemma lem3907537 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3907538 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term71 A s t) = (term59 A t s).
Proof. exact (MK_COMB (@lem3907537) (@lem3907536 A t s)). Qed.
Lemma lem3907539 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term71 A s t) = (term65 A t s).
Proof. exact (TRANS (@lem3907538 A t s) (@lem3907533 A t s)). Qed.
Lemma lem3907540 {A : Type'} (s : A -> Prop) : (term72 A s) = (term73 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3907539 A t s)). Qed.
Lemma lem3907541 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3907542 {A : Type'} (s : A -> Prop) : (term69 A s) = (term74 A s).
Proof. exact (MK_COMB (@lem3907541 A) (@lem3907540 A s)). Qed.
Lemma lem3907543 {A : Type'} (s : A -> Prop) : (term68 A s) = (term74 A s).
Proof. exact (TRANS (@lem3907535 A s) (@lem3907542 A s)). Qed.
Lemma lem3907544 {A : Type'} (P : type686 A) : (term66 A P) = (term67 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3907545 {A : Type'} : (term10 A) = (term75 A).
Proof. exact (@lem3907544 A (term47 A)). Qed.
Lemma lem3907546 {A : Type'} (s : A -> Prop) : (term76 A s) = (term46 A s).
Proof. exact (eq_refl (term76 A s)). Qed.
Lemma lem3907547 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3907548 {A : Type'} (s : A -> Prop) : (term77 A s) = (term68 A s).
Proof. exact (MK_COMB (@lem3907547) (@lem3907546 A s)). Qed.
Lemma lem3907549 {A : Type'} (s : A -> Prop) : (term77 A s) = (term74 A s).
Proof. exact (TRANS (@lem3907548 A s) (@lem3907543 A s)). Qed.
Lemma lem3907550 {A : Type'} : (term78 A) = (term79 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3907549 A s)). Qed.
Lemma lem3907551 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3907552 {A : Type'} : (term75 A) = (term80 A).
Proof. exact (MK_COMB (@lem3907551 A) (@lem3907550 A)). Qed.
Lemma lem3907613 {A : Type'} : (term10 A) = (term80 A).
Proof. exact (TRANS (@lem3907545 A) (@lem3907552 A)). Qed.
Lemma lem3907614 {A : Type'} (h1 : term10 A) : term80 A.
Proof. exact (EQ_MP (@lem3907613 A) (@lem3907499 A h1)). Qed.
Lemma lem3907621 (m : nat) (n : nat) (p : nat) : (term81 m n p) = (term82 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem3907622 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem3907623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3907624 (m : nat) (n : nat) (p : nat) : (term83 m n p) = (term84 m n p).
Proof. exact (MK_COMB (@lem3907623) (@lem3907621 m n p)). Qed.
Lemma lem3907625 (n : nat) (m : nat) (p : nat) : (term85 n m p) = (term86 n m p).
Proof. exact (MK_COMB (@lem3907624 m n p) (@lem3907622 m p)). Qed.
Lemma lem3907626 (n : nat) (m : nat) (p : nat) : (term35 n m p) = (term85 n m p).
Proof. exact (@lem17265 (term87 m n p) (Peano.le m p)). Qed.
Lemma lem3907627 (n : nat) (m : nat) (p : nat) : (term35 n m p) = (term86 n m p).
Proof. exact (TRANS (@lem3907626 n m p) (@lem3907625 n m p)). Qed.
Lemma lem3907628 (n : nat) (m : nat) : (term36 n m) = (term88 n m).
Proof. exact (fun_ext (fun p : nat => @lem3907627 n m p)). Qed.
Lemma lem3907629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3907630 (n : nat) (m : nat) : (term37 n m) = (term89 n m).
Proof. exact (MK_COMB (@lem3907629) (@lem3907628 n m)). Qed.
Lemma lem3907631 (m : nat) : (term38 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem3907630 n m)). Qed.
Lemma lem3907632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3907633 (m : nat) : (term39 m) = (term91 m).
Proof. exact (MK_COMB (@lem3907632) (@lem3907631 m)). Qed.
Lemma lem3907634 : term40 = term92.
Proof. exact (fun_ext (fun m : nat => @lem3907633 m)). Qed.
Lemma lem3907635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3907696 : term41 = term93.
Proof. exact (MK_COMB (@lem3907635) (@lem3907634)). Qed.
Lemma lem3907697 (h1 : term41) : term93.
Proof. exact (EQ_MP (@lem3907696) (@lem3907500 h1)). Qed.
Lemma lem3907704 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term94 A a b) = (term95 A a b).
Proof. exact (@lem17045 (@SUBSET A a b) (@FINITE A b)). Qed.
Lemma lem3907705 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term96 A a b) = (term96 A a b).
Proof. exact (eq_refl (term96 A a b)). Qed.
Lemma lem3907706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3907707 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term97 A a b) = (term98 A a b).
Proof. exact (MK_COMB (@lem3907706) (@lem3907704 A a b)). Qed.
Lemma lem3907708 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term99 A a b) = (term100 A a b).
Proof. exact (MK_COMB (@lem3907707 A a b) (@lem3907705 A a b)). Qed.
Lemma lem3907709 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term31 A a b) = (term99 A a b).
Proof. exact (@lem17265 (term101 A a b) (term96 A a b)). Qed.
Lemma lem3907710 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term31 A a b) = (term100 A a b).
Proof. exact (TRANS (@lem3907709 A a b) (@lem3907708 A a b)). Qed.
Lemma lem3907711 {A : Type'} (a : A -> Prop) : (term32 A a) = (term102 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3907710 A a b)). Qed.
Lemma lem3907712 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907713 {A : Type'} (a : A -> Prop) : (term33 A a) = (term103 A a).
Proof. exact (MK_COMB (@lem3907712 A) (@lem3907711 A a)). Qed.
Lemma lem3907714 {A : Type'} : (term34 A) = (term104 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3907713 A a)). Qed.
Lemma lem3907715 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907772 {A : Type'} : (term12 A) = (term105 A).
Proof. exact (MK_COMB (@lem3907715 A) (@lem3907714 A)). Qed.
Lemma lem3907773 {A : Type'} (h1 : term12 A) : term105 A.
Proof. exact (EQ_MP (@lem3907772 A) (@lem3907501 A h1)). Qed.
Lemma lem3907780 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term107 A s t).
Proof. exact (@lem17045 (@FINITE A t) (@SUBSET A s t)). Qed.
Lemma lem3907781 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3907782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3907783 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term108 A s t) = (term109 A s t).
Proof. exact (MK_COMB (@lem3907782) (@lem3907780 A s t)). Qed.
Lemma lem3907784 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term110 A t s) = (term111 A t s).
Proof. exact (MK_COMB (@lem3907783 A s t) (@lem3907781 A s)). Qed.
Lemma lem3907785 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term27 A t s) = (term110 A t s).
Proof. exact (@lem17265 (term112 A s t) (@FINITE A s)). Qed.
Lemma lem3907786 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term27 A t s) = (term111 A t s).
Proof. exact (TRANS (@lem3907785 A t s) (@lem3907784 A t s)). Qed.
Lemma lem3907787 {A : Type'} (s : A -> Prop) : (term28 A s) = (term113 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3907786 A t s)). Qed.
Lemma lem3907788 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907789 {A : Type'} (s : A -> Prop) : (term29 A s) = (term114 A s).
Proof. exact (MK_COMB (@lem3907788 A) (@lem3907787 A s)). Qed.
Lemma lem3907790 {A : Type'} : (term30 A) = (term115 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3907789 A s)). Qed.
Lemma lem3907791 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907792 {A : Type'} : (term11 A) = (term116 A).
Proof. exact (MK_COMB (@lem3907791 A) (@lem3907790 A)). Qed.
Lemma lem3907818 {A : Type'} (P : A -> Prop) (Q : Prop) : (term117 A P Q) = (term118 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem3907819 {A : Type'} (P : type686 A) (Q : Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem3907818 (A -> Prop) P Q). Qed.
Lemma lem3907820 {A : Type'} (s : A -> Prop) : (term121 A s) = (term122 A s).
Proof. exact (@lem3907819 A (term123 A s) (@FINITE A s)). Qed.
Lemma lem3907821 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term124 A s t) = (term107 A s t).
Proof. exact (eq_refl (term124 A s t)). Qed.
Lemma lem3907822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3907823 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term109 A s t).
Proof. exact (MK_COMB (@lem3907822) (@lem3907821 A s t)). Qed.
Lemma lem3907824 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3907825 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term126 A t s) = (term111 A t s).
Proof. exact (MK_COMB (@lem3907823 A s t) (@lem3907824 A s)). Qed.
Lemma lem3907826 {A : Type'} (s : A -> Prop) : (term127 A s) = (term113 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3907825 A t s)). Qed.
Lemma lem3907827 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907828 {A : Type'} (s : A -> Prop) : (term121 A s) = (term114 A s).
Proof. exact (MK_COMB (@lem3907827 A) (@lem3907826 A s)). Qed.
Lemma lem3907829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3907830 {A : Type'} (s : A -> Prop) : (term128 A s) = (term129 A s).
Proof. exact (MK_COMB (@lem3907829) (@lem3907828 A s)). Qed.
Lemma lem3907831 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term124 A s t) = (term107 A s t).
Proof. exact (eq_refl (term124 A s t)). Qed.
Lemma lem3907832 {A : Type'} (s : A -> Prop) : (term130 A s) = (term123 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3907831 A s t)). Qed.
Lemma lem3907833 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907834 {A : Type'} (s : A -> Prop) : (term131 A s) = (term132 A s).
Proof. exact (MK_COMB (@lem3907833 A) (@lem3907832 A s)). Qed.
Lemma lem3907835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3907836 {A : Type'} (s : A -> Prop) : (term133 A s) = (term134 A s).
Proof. exact (MK_COMB (@lem3907835) (@lem3907834 A s)). Qed.
Lemma lem3907837 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3907838 {A : Type'} (s : A -> Prop) : (term122 A s) = (term135 A s).
Proof. exact (MK_COMB (@lem3907836 A s) (@lem3907837 A s)). Qed.
Lemma lem3907839 {A : Type'} (s : A -> Prop) : ((term121 A s) = (term122 A s)) = ((term114 A s) = (term135 A s)).
Proof. exact (MK_COMB (@lem3907830 A s) (@lem3907838 A s)). Qed.
Lemma lem3907840 {A : Type'} (s : A -> Prop) : (term114 A s) = (term135 A s).
Proof. exact (EQ_MP (@lem3907839 A s) (@lem3907820 A s)). Qed.
Lemma lem3907889 {A : Type'} : (term115 A) = (term136 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3907840 A s)). Qed.
Lemma lem3907890 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907925 {A : Type'} : (term116 A) = (term137 A).
Proof. exact (MK_COMB (@lem3907890 A) (@lem3907889 A)). Qed.
Lemma lem3907926 {A : Type'} : (term11 A) = (term137 A).
Proof. exact (TRANS (@lem3907792 A) (@lem3907925 A)). Qed.
Lemma lem3907927 {A : Type'} (h1 : term11 A) : term137 A.
Proof. exact (EQ_MP (@lem3907926 A) (@lem3907502 A h1)). Qed.
Lemma lem3907928 {A : Type'} (s : A -> Prop) (h1 : term74 A s) : term74 A s.
Proof. exact (h1). Qed.
Lemma lem3907929 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term65 A t s) : term65 A t s.
Proof. exact (h1). Qed.
Lemma lem3907955 (n : nat) (m : nat) (p : nat) : (term86 n m p) = (term86 n m p).
Proof. exact (eq_refl (term86 n m p)). Qed.
Lemma lem3907956 (n : nat) (m : nat) : (term88 n m) = (term88 n m).
Proof. exact (fun_ext (fun p : nat => @lem3907955 n m p)). Qed.
Lemma lem3907957 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3907958 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (MK_COMB (@lem3907957) (@lem3907956 n m)). Qed.
Lemma lem3907959 (m : nat) : (term90 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem3907958 n m)). Qed.
Lemma lem3907960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3907961 (m : nat) : (term91 m) = (term91 m).
Proof. exact (MK_COMB (@lem3907960) (@lem3907959 m)). Qed.
Lemma lem3907962 : term92 = term92.
Proof. exact (fun_ext (fun m : nat => @lem3907961 m)). Qed.
Lemma lem3907963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3907964 : term93 = term93.
Proof. exact (MK_COMB (@lem3907963) (@lem3907962)). Qed.
Lemma lem3907965 (h1 : term41) : term93.
Proof. exact (EQ_MP (@lem3907964) (@lem3907697 h1)). Qed.
Lemma lem3907992 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term100 A a b) = (term100 A a b).
Proof. exact (eq_refl (term100 A a b)). Qed.
Lemma lem3907993 {A : Type'} (a : A -> Prop) : (term102 A a) = (term102 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3907992 A a b)). Qed.
Lemma lem3907994 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907995 {A : Type'} (a : A -> Prop) : (term103 A a) = (term103 A a).
Proof. exact (MK_COMB (@lem3907994 A) (@lem3907993 A a)). Qed.
Lemma lem3907996 {A : Type'} : (term104 A) = (term104 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3907995 A a)). Qed.
Lemma lem3907997 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3907998 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (MK_COMB (@lem3907997 A) (@lem3907996 A)). Qed.
Lemma lem3907999 {A : Type'} (h1 : term12 A) : term105 A.
Proof. exact (EQ_MP (@lem3907998 A) (@lem3907773 A h1)). Qed.
Lemma lem3908002 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3908017 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term107 A s t) = (term107 A s t).
Proof. exact (eq_refl (term107 A s t)). Qed.
Lemma lem3908018 {A : Type'} (s : A -> Prop) : (term123 A s) = (term123 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3908017 A s t)). Qed.
Lemma lem3908019 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3908020 {A : Type'} (s : A -> Prop) : (term132 A s) = (term132 A s).
Proof. exact (MK_COMB (@lem3908019 A) (@lem3908018 A s)). Qed.
Lemma lem3908021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3908022 {A : Type'} (s : A -> Prop) : (term134 A s) = (term134 A s).
Proof. exact (MK_COMB (@lem3908021) (@lem3908020 A s)). Qed.
Lemma lem3908023 {A : Type'} (s : A -> Prop) : (term135 A s) = (term135 A s).
Proof. exact (MK_COMB (@lem3908022 A s) (@lem3908002 A s)). Qed.
Lemma lem3908024 {A : Type'} : (term136 A) = (term136 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3908023 A s)). Qed.
Lemma lem3908025 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3908026 {A : Type'} : (term137 A) = (term137 A).
Proof. exact (MK_COMB (@lem3908025 A) (@lem3908024 A)). Qed.
Lemma lem3908027 {A : Type'} (h1 : term11 A) : term137 A.
Proof. exact (EQ_MP (@lem3908026 A) (@lem3907927 A h1)). Qed.
Lemma lem3908069 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term53 A t s n.
Proof. exact (h1). Qed.
Lemma lem3908070 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term49 A s n.
Proof. exact (proj2 (@lem3908069 A t s n h1)). Qed.
Lemma lem3908071 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term55 A s t n.
Proof. exact (proj1 (@lem3908069 A t s n h1)). Qed.
Lemma lem3908072 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term56 A t n.
Proof. exact (proj2 (@lem3908071 A t s n h1)). Qed.
Lemma lem3908126 {A : Type'} (P : A -> Prop) (Q : Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3908127 {A : Type'} (P : type686 A) (Q : Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (@lem3908126 (A -> Prop) P Q). Qed.
Lemma lem3908128 {A : Type'} (s : A -> Prop) : (term122 A s) = (term121 A s).
Proof. exact (@lem3908127 A (term123 A s) (@FINITE A s)). Qed.
Lemma lem3908129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term124 A s t) = (term107 A s t).
Proof. exact (eq_refl (term124 A s t)). Qed.
Lemma lem3908130 {A : Type'} (s : A -> Prop) : (term130 A s) = (term123 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3908129 A s t)). Qed.
Lemma lem3908131 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3908132 {A : Type'} (s : A -> Prop) : (term131 A s) = (term132 A s).
Proof. exact (MK_COMB (@lem3908131 A) (@lem3908130 A s)). Qed.
Lemma lem3908133 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3908134 {A : Type'} (s : A -> Prop) : (term133 A s) = (term134 A s).
Proof. exact (MK_COMB (@lem3908133) (@lem3908132 A s)). Qed.
Lemma lem3908135 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3908136 {A : Type'} (s : A -> Prop) : (term122 A s) = (term135 A s).
Proof. exact (MK_COMB (@lem3908134 A s) (@lem3908135 A s)). Qed.
Lemma lem3908137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3908138 {A : Type'} (s : A -> Prop) : (term138 A s) = (term139 A s).
Proof. exact (MK_COMB (@lem3908137) (@lem3908136 A s)). Qed.
Lemma lem3908139 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term124 A s t) = (term107 A s t).
Proof. exact (eq_refl (term124 A s t)). Qed.
Lemma lem3908140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3908141 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term109 A s t).
Proof. exact (MK_COMB (@lem3908140) (@lem3908139 A s t)). Qed.
Lemma lem3908142 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3908143 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term126 A t s) = (term111 A t s).
Proof. exact (MK_COMB (@lem3908141 A s t) (@lem3908142 A s)). Qed.
Lemma lem3908144 {A : Type'} (s : A -> Prop) : (term127 A s) = (term113 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3908143 A t s)). Qed.
Lemma lem3908145 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3908146 {A : Type'} (s : A -> Prop) : (term121 A s) = (term114 A s).
Proof. exact (MK_COMB (@lem3908145 A) (@lem3908144 A s)). Qed.
Lemma lem3908147 {A : Type'} (s : A -> Prop) : ((term122 A s) = (term121 A s)) = ((term135 A s) = (term114 A s)).
Proof. exact (MK_COMB (@lem3908138 A s) (@lem3908146 A s)). Qed.
Lemma lem3908148 {A : Type'} (s : A -> Prop) : (term135 A s) = (term114 A s).
Proof. exact (EQ_MP (@lem3908147 A s) (@lem3908128 A s)). Qed.
Lemma lem3908149 {A : Type'} : (term136 A) = (term115 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3908148 A s)). Qed.
Lemma lem3908150 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3908151 {A : Type'} : (term137 A) = (term116 A).
Proof. exact (MK_COMB (@lem3908150 A) (@lem3908149 A)). Qed.
Lemma lem3908164 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term111 A t s) = (term111 A t s).
Proof. exact (eq_refl (term111 A t s)). Qed.
Lemma lem3908165 {A : Type'} (s : A -> Prop) : (term113 A s) = (term113 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3908164 A t s)). Qed.
Lemma lem3908166 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3908167 {A : Type'} (s : A -> Prop) : (term114 A s) = (term114 A s).
Proof. exact (MK_COMB (@lem3908166 A) (@lem3908165 A s)). Qed.
Lemma lem3908168 {A : Type'} : (term115 A) = (term115 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3908167 A s)). Qed.
Lemma lem3908169 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3908170 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem3908169 A) (@lem3908168 A)). Qed.
Lemma lem3908171 {A : Type'} : (term137 A) = (term116 A).
Proof. exact (TRANS (@lem3908151 A) (@lem3908170 A)). Qed.
Lemma lem3908172 {A : Type'} (h1 : term11 A) : term116 A.
Proof. exact (EQ_MP (@lem3908171 A) (@lem3908027 A h1)). Qed.
Lemma lem3908188 {A : Type'} (s : A -> Prop) (h1 : term140 A s) : term140 A s.
Proof. exact (h1). Qed.
Lemma lem3908202 (n : nat) (m : nat) (p : nat) : (term86 n m p) = (term86 n m p).
Proof. exact (eq_refl (term86 n m p)). Qed.
Lemma lem3908203 (n : nat) (m : nat) : (term88 n m) = (term88 n m).
Proof. exact (fun_ext (fun p : nat => @lem3908202 n m p)). Qed.
Lemma lem3908204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3908205 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (MK_COMB (@lem3908204) (@lem3908203 n m)). Qed.
Lemma lem3908206 (m : nat) : (term90 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem3908205 n m)). Qed.
Lemma lem3908207 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3908208 (m : nat) : (term91 m) = (term91 m).
Proof. exact (MK_COMB (@lem3908207) (@lem3908206 m)). Qed.
Lemma lem3908209 : term92 = term92.
Proof. exact (fun_ext (fun m : nat => @lem3908208 m)). Qed.
Lemma lem3908210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3908212 : term93 = term93.
Proof. exact (MK_COMB (@lem3908210) (@lem3908209)). Qed.
Lemma lem3908213 (h1 : term41) : term93.
Proof. exact (EQ_MP (@lem3908212) (@lem3907965 h1)). Qed.
Lemma lem3908227 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term100 A a b) = (term100 A a b).
Proof. exact (eq_refl (term100 A a b)). Qed.
Lemma lem3908228 {A : Type'} (a : A -> Prop) : (term102 A a) = (term102 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3908227 A a b)). Qed.
Lemma lem3908229 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3908230 {A : Type'} (a : A -> Prop) : (term103 A a) = (term103 A a).
Proof. exact (MK_COMB (@lem3908229 A) (@lem3908228 A a)). Qed.
Lemma lem3908231 {A : Type'} : (term104 A) = (term104 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3908230 A a)). Qed.
Lemma lem3908232 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3908234 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (MK_COMB (@lem3908232 A) (@lem3908231 A)). Qed.
Lemma lem3908235 {A : Type'} (h1 : term12 A) : term105 A.
Proof. exact (EQ_MP (@lem3908234 A) (@lem3907999 A h1)). Qed.
Lemma lem3908299 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term141 A s n) : term141 A s n.
Proof. exact (h1). Qed.
Lemma lem3908315 {A : Type'} (_45427 : A -> Prop) (h1 : term11 A) : term142 A _45427.
Proof. exact (@lem3908172 A h1 _45427). Qed.
Lemma lem3908316 {A : Type'} (_45427 : A -> Prop) : (term142 A _45427) = (term114 A _45427).
Proof. exact (eq_refl (term142 A _45427)). Qed.
Lemma lem3908317 {A : Type'} (_45427 : A -> Prop) (h1 : term11 A) : term114 A _45427.
Proof. exact (EQ_MP (@lem3908316 A _45427) (@lem3908315 A _45427 h1)). Qed.
Lemma lem3908318 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) (h1 : term11 A) : term143 A _45427 _45428.
Proof. exact (@lem3908317 A _45427 h1 _45428). Qed.
Lemma lem3908319 {A : Type'} (_45428 : A -> Prop) (_45427 : A -> Prop) : (term143 A _45427 _45428) = (term111 A _45428 _45427).
Proof. exact (eq_refl (term143 A _45427 _45428)). Qed.
Lemma lem3908320 {A : Type'} (_45428 : A -> Prop) (_45427 : A -> Prop) (h1 : term11 A) : term111 A _45428 _45427.
Proof. exact (EQ_MP (@lem3908319 A _45428 _45427) (@lem3908318 A _45427 _45428 h1)). Qed.
Lemma lem3908321 (_45429 : nat) (h1 : term41) : term144 _45429.
Proof. exact (@lem3908213 h1 _45429). Qed.
Lemma lem3908322 (_45429 : nat) : (term144 _45429) = (term91 _45429).
Proof. exact (eq_refl (term144 _45429)). Qed.
Lemma lem3908323 (_45429 : nat) (h1 : term41) : term91 _45429.
Proof. exact (EQ_MP (@lem3908322 _45429) (@lem3908321 _45429 h1)). Qed.
Lemma lem3908324 (_45429 : nat) (_45430 : nat) (h1 : term41) : term145 _45429 _45430.
Proof. exact (@lem3908323 _45429 h1 _45430). Qed.
Lemma lem3908325 (_45430 : nat) (_45429 : nat) : (term145 _45429 _45430) = (term89 _45430 _45429).
Proof. exact (eq_refl (term145 _45429 _45430)). Qed.
Lemma lem3908326 (_45430 : nat) (_45429 : nat) (h1 : term41) : term89 _45430 _45429.
Proof. exact (EQ_MP (@lem3908325 _45430 _45429) (@lem3908324 _45429 _45430 h1)). Qed.
Lemma lem3908327 (_45430 : nat) (_45429 : nat) (_45431 : nat) (h1 : term41) : term146 _45430 _45429 _45431.
Proof. exact (@lem3908326 _45430 _45429 h1 _45431). Qed.
Lemma lem3908328 (_45430 : nat) (_45429 : nat) (_45431 : nat) : (term146 _45430 _45429 _45431) = (term86 _45430 _45429 _45431).
Proof. exact (eq_refl (term146 _45430 _45429 _45431)). Qed.
Lemma lem3908329 (_45430 : nat) (_45429 : nat) (_45431 : nat) (h1 : term41) : term86 _45430 _45429 _45431.
Proof. exact (EQ_MP (@lem3908328 _45430 _45429 _45431) (@lem3908327 _45430 _45429 _45431 h1)). Qed.
Lemma lem3908330 {A : Type'} (_45432 : A -> Prop) (h1 : term12 A) : term147 A _45432.
Proof. exact (@lem3908235 A h1 _45432). Qed.
Lemma lem3908331 {A : Type'} (_45432 : A -> Prop) : (term147 A _45432) = (term103 A _45432).
Proof. exact (eq_refl (term147 A _45432)). Qed.
Lemma lem3908332 {A : Type'} (_45432 : A -> Prop) (h1 : term12 A) : term103 A _45432.
Proof. exact (EQ_MP (@lem3908331 A _45432) (@lem3908330 A _45432 h1)). Qed.
Lemma lem3908333 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) (h1 : term12 A) : term148 A _45432 _45433.
Proof. exact (@lem3908332 A _45432 h1 _45433). Qed.
Lemma lem3908334 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term148 A _45432 _45433) = (term100 A _45432 _45433).
Proof. exact (eq_refl (term148 A _45432 _45433)). Qed.
Lemma lem3908335 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) (h1 : term12 A) : term100 A _45432 _45433.
Proof. exact (EQ_MP (@lem3908334 A _45432 _45433) (@lem3908333 A _45432 _45433 h1)). Qed.
Lemma lem3908376 {A : Type'} (_45428 : A -> Prop) (_45427 : A -> Prop) : (term111 A _45428 _45427) = (term149 A _45428 _45427).
Proof. exact (@lem3907210 (term140 A _45428) (term150 A _45427 _45428) (@FINITE A _45427)). Qed.
Lemma lem3908377 {A : Type'} (_45428 : A -> Prop) (_45427 : A -> Prop) (h1 : term11 A) : term149 A _45428 _45427.
Proof. exact (EQ_MP (@lem3908376 A _45428 _45427) (@lem3908320 A _45428 _45427 h1)). Qed.
Lemma lem3908385 {A : Type'} (s : A -> Prop) (h1 : term140 A s) : term140 A s.
Proof. exact (h1). Qed.
Lemma lem3908396 (_45430 : nat) (_45429 : nat) (_45431 : nat) : (term86 _45430 _45429 _45431) = (term151 _45430 _45429 _45431).
Proof. exact (@lem3907210 (term152 _45429 _45430) (term152 _45430 _45431) (Peano.le _45429 _45431)). Qed.
Lemma lem3908397 (_45430 : nat) (_45429 : nat) (_45431 : nat) (h1 : term41) : term151 _45430 _45429 _45431.
Proof. exact (EQ_MP (@lem3908396 _45430 _45429 _45431) (@lem3908329 _45430 _45429 _45431 h1)). Qed.
Lemma lem3908408 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term100 A _45432 _45433) = (term153 A _45432 _45433).
Proof. exact (@lem3907210 (term150 A _45432 _45433) (term140 A _45433) (term96 A _45432 _45433)). Qed.
Lemma lem3908409 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) (h1 : term12 A) : term153 A _45432 _45433.
Proof. exact (EQ_MP (@lem3908408 A _45432 _45433) (@lem3908335 A _45432 _45433 h1)). Qed.
Lemma lem3908429 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term141 A s n) : term141 A s n.
Proof. exact (h1). Qed.
Lemma lem3908431 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : @FINITE A t.
Proof. exact (proj1 (@lem3908072 A t s n h1)). Qed.
Lemma lem3908432 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term154 A t.
Proof. exact (fun h0 : term140 A t => @lem3908431 A t s n h1). Qed.
Lemma lem3908434 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3908435 {A : Type'} (t : A -> Prop) : (term154 A t) = (@FINITE A t).
Proof. exact (@lem3908434 (@FINITE A t)). Qed.
Lemma lem3908436 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : @FINITE A t.
Proof. exact (EQ_MP (@lem3908435 A t) (@lem3908432 A t s n h1)). Qed.
Lemma lem3908438 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : @SUBSET A s t.
Proof. exact (proj1 (@lem3908071 A t s n h1)). Qed.
Lemma lem3908439 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term156 A s t.
Proof. exact (fun h0 : term150 A s t => @lem3908438 A t s n h1). Qed.
Lemma lem3908441 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3908442 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term156 A s t) = (@SUBSET A s t).
Proof. exact (@lem3908441 (@SUBSET A s t)). Qed.
Lemma lem3908443 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3908442 A s t) (@lem3908439 A t s n h1)). Qed.
Lemma lem3908459 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3908460 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term157 A _45428 _45427) = (term158 A _45427 _45428).
Proof. exact (@lem3908459 (@FINITE A _45427) (term150 A _45427 _45428)). Qed.
Lemma lem3908466 {A : Type'} (_45428 : A -> Prop) : (term159 A _45428) = (term159 A _45428).
Proof. exact (eq_refl (term159 A _45428)). Qed.
Lemma lem3908467 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term149 A _45428 _45427) = (term160 A _45427 _45428).
Proof. exact (MK_COMB (@lem3908466 A _45428) (@lem3908460 A _45427 _45428)). Qed.
Lemma lem3908471 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3908472 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term160 A _45427 _45428) = (term161 A _45427 _45428).
Proof. exact (@lem3908471 (@FINITE A _45427) (term140 A _45428) (term150 A _45427 _45428)). Qed.
Lemma lem3908488 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term149 A _45428 _45427) = (term161 A _45427 _45428).
Proof. exact (TRANS (@lem3908467 A _45427 _45428) (@lem3908472 A _45427 _45428)). Qed.
Lemma lem3908489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3908490 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term162 A _45428 _45427) = (term163 A _45427 _45428).
Proof. exact (MK_COMB (@lem3908489) (@lem3908488 A _45427 _45428)). Qed.
Lemma lem3908506 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term161 A _45427 _45428) = (term161 A _45427 _45428).
Proof. exact (eq_refl (term161 A _45427 _45428)). Qed.
Lemma lem3908507 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : ((term149 A _45428 _45427) = (term161 A _45427 _45428)) = ((term161 A _45427 _45428) = (term161 A _45427 _45428)).
Proof. exact (MK_COMB (@lem3908490 A _45427 _45428) (@lem3908506 A _45427 _45428)). Qed.
Lemma lem3908509 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3908510 (x : Prop) : (x = x) = True.
Proof. exact (@lem3908509 Prop x). Qed.
Lemma lem3908511 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : ((term161 A _45427 _45428) = (term161 A _45427 _45428)) = True.
Proof. exact (@lem3908510 (term161 A _45427 _45428)). Qed.
Lemma lem3908512 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : ((term149 A _45428 _45427) = (term161 A _45427 _45428)) = True.
Proof. exact (TRANS (@lem3908507 A _45427 _45428) (@lem3908511 A _45427 _45428)). Qed.
Lemma lem3908513 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : True = ((term149 A _45428 _45427) = (term161 A _45427 _45428)).
Proof. exact (SYM (@lem3908512 A _45427 _45428)). Qed.
Lemma lem3908514 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term149 A _45428 _45427) = (term161 A _45427 _45428).
Proof. exact (EQ_MP (@lem3908513 A _45427 _45428) (@lem0)). Qed.
Lemma lem3908515 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) (h1 : term11 A) : term161 A _45427 _45428.
Proof. exact (EQ_MP (@lem3908514 A _45427 _45428) (@lem3908377 A _45428 _45427 h1)). Qed.
Lemma lem3908517 (b : Prop) (a : Prop) : (a \/ b) = (term164 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3908518 {A : Type'} (_45428 : A -> Prop) (_45427 : A -> Prop) : (term161 A _45427 _45428) = (term165 A _45428 _45427).
Proof. exact (@lem3908517 (term107 A _45427 _45428) (@FINITE A _45427)). Qed.
Lemma lem3908520 (a : Prop) (b : Prop) : (term166 a b) = (term167 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3908521 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term168 A _45427 _45428) = (term169 A _45427 _45428).
Proof. exact (@lem3908520 (term140 A _45428) (term150 A _45427 _45428)). Qed.
Lemma lem3908523 (a : Prop) : (term170 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3908524 {A : Type'} (_45428 : A -> Prop) : (term171 A _45428) = (@FINITE A _45428).
Proof. exact (@lem3908523 (@FINITE A _45428)). Qed.
Lemma lem3908525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3908526 {A : Type'} (_45428 : A -> Prop) : (term172 A _45428) = (term173 A _45428).
Proof. exact (MK_COMB (@lem3908525) (@lem3908524 A _45428)). Qed.
Lemma lem3908528 (a : Prop) : (term170 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3908529 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term174 A _45427 _45428) = (@SUBSET A _45427 _45428).
Proof. exact (@lem3908528 (@SUBSET A _45427 _45428)). Qed.
Lemma lem3908530 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term169 A _45427 _45428) = (term112 A _45427 _45428).
Proof. exact (MK_COMB (@lem3908526 A _45428) (@lem3908529 A _45427 _45428)). Qed.
Lemma lem3908531 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term168 A _45427 _45428) = (term112 A _45427 _45428).
Proof. exact (TRANS (@lem3908521 A _45427 _45428) (@lem3908530 A _45427 _45428)). Qed.
Lemma lem3908532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3908533 {A : Type'} (_45427 : A -> Prop) (_45428 : A -> Prop) : (term175 A _45427 _45428) = (term176 A _45427 _45428).
Proof. exact (MK_COMB (@lem3908532) (@lem3908531 A _45427 _45428)). Qed.
Lemma lem3908534 {A : Type'} (_45427 : A -> Prop) : (@FINITE A _45427) = (@FINITE A _45427).
Proof. exact (eq_refl (@FINITE A _45427)). Qed.
Lemma lem3908535 {A : Type'} (_45428 : A -> Prop) (_45427 : A -> Prop) : (term165 A _45428 _45427) = (term27 A _45428 _45427).
Proof. exact (MK_COMB (@lem3908533 A _45427 _45428) (@lem3908534 A _45427)). Qed.
Lemma lem3908536 {A : Type'} (_45428 : A -> Prop) (_45427 : A -> Prop) : (term161 A _45427 _45428) = (term27 A _45428 _45427).
Proof. exact (TRANS (@lem3908518 A _45428 _45427) (@lem3908535 A _45428 _45427)). Qed.
Lemma lem3908538 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term112 A s t.
Proof. exact (conj (@lem3908436 A t s n h1) (@lem3908443 A t s n h1)). Qed.
Lemma lem3908540 {A : Type'} (_45428 : A -> Prop) (_45427 : A -> Prop) (h1 : term11 A) : term27 A _45428 _45427.
Proof. exact (EQ_MP (@lem3908536 A _45428 _45427) (@lem3908515 A _45427 _45428 h1)). Qed.
Lemma lem3908541 {A : Type'} (_45428 : A -> Prop) (_45427 : A -> Prop) (h1 : term11 A) : term27 A _45428 _45427.
Proof. exact (@lem3908540 A _45428 _45427 h1). Qed.
Lemma lem3908542 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term11 A) : term27 A t s.
Proof. exact (@lem3908541 A t s h1). Qed.
Lemma lem3908545 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term53 A t s n) : @FINITE A s.
Proof. exact (@lem3908542 A t s h1 (@lem3908538 A t s n h2)). Qed.
Lemma lem3908546 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term53 A t s n) : term154 A s.
Proof. exact (fun h0 : term140 A s => @lem3908545 A t s n h1 h2). Qed.
Lemma lem3908548 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3908549 {A : Type'} (s : A -> Prop) : (term154 A s) = (@FINITE A s).
Proof. exact (@lem3908548 (@FINITE A s)). Qed.
Lemma lem3908550 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term53 A t s n) : @FINITE A s.
Proof. exact (EQ_MP (@lem3908549 A s) (@lem3908546 A t s n h1 h2)). Qed.
Lemma lem3908553 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3908555 {A : Type'} (s : A -> Prop) : (term140 A s) = (term177 A s).
Proof. exact (@lem3908553 (@FINITE A s)). Qed.
Lemma lem3908558 {A : Type'} (s : A -> Prop) (h1 : term140 A s) : term177 A s.
Proof. exact (EQ_MP (@lem3908555 A s) (@lem3908385 A s h1)). Qed.
Lemma lem3908561 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term140 A s) (h3 : term53 A t s n) : False.
Proof. exact (@lem3908558 A s h2 (@lem3908550 A t s n h1 h3)). Qed.
Lemma lem3908562 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term140 A s) (h3 : term53 A t s n) : term178.
Proof. exact (fun h0 : ~ False => @lem3908561 A t s n h1 h2 h3). Qed.
Lemma lem3908564 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3908565 : term178 = False.
Proof. exact (@lem3908564 False). Qed.
Lemma lem3908566 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term140 A s) (h3 : term53 A t s n) : False.
Proof. exact (EQ_MP (@lem3908565) (@lem3908562 A t s n h1 h2 h3)). Qed.
Lemma lem3908568 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : @SUBSET A s t.
Proof. exact (proj1 (@lem3908071 A t s n h1)). Qed.
Lemma lem3908569 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term156 A s t.
Proof. exact (fun h0 : term150 A s t => @lem3908568 A t s n h1). Qed.
Lemma lem3908571 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3908572 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term156 A s t) = (@SUBSET A s t).
Proof. exact (@lem3908571 (@SUBSET A s t)). Qed.
Lemma lem3908573 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3908572 A s t) (@lem3908569 A t s n h1)). Qed.
Lemma lem3908575 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : @FINITE A t.
Proof. exact (proj1 (@lem3908072 A t s n h1)). Qed.
Lemma lem3908576 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term154 A t.
Proof. exact (fun h0 : term140 A t => @lem3908575 A t s n h1). Qed.
Lemma lem3908578 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3908579 {A : Type'} (t : A -> Prop) : (term154 A t) = (@FINITE A t).
Proof. exact (@lem3908578 (@FINITE A t)). Qed.
Lemma lem3908580 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : @FINITE A t.
Proof. exact (EQ_MP (@lem3908579 A t) (@lem3908576 A t s n h1)). Qed.
Lemma lem3908586 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3908587 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term153 A _45432 _45433) = (term179 A _45432 _45433).
Proof. exact (@lem3908586 (term140 A _45433) (term150 A _45432 _45433) (term96 A _45432 _45433)). Qed.
Lemma lem3908601 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3908602 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term180 A _45432 _45433) = (term181 A _45432 _45433).
Proof. exact (@lem3908601 (term96 A _45432 _45433) (term150 A _45432 _45433)). Qed.
Lemma lem3908608 {A : Type'} (_45433 : A -> Prop) : (term159 A _45433) = (term159 A _45433).
Proof. exact (eq_refl (term159 A _45433)). Qed.
Lemma lem3908609 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term179 A _45432 _45433) = (term182 A _45432 _45433).
Proof. exact (MK_COMB (@lem3908608 A _45433) (@lem3908602 A _45432 _45433)). Qed.
Lemma lem3908613 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3908614 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term182 A _45432 _45433) = (term183 A _45432 _45433).
Proof. exact (@lem3908613 (term96 A _45432 _45433) (term140 A _45433) (term150 A _45432 _45433)). Qed.
Lemma lem3908630 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term179 A _45432 _45433) = (term183 A _45432 _45433).
Proof. exact (TRANS (@lem3908609 A _45432 _45433) (@lem3908614 A _45432 _45433)). Qed.
Lemma lem3908631 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term153 A _45432 _45433) = (term183 A _45432 _45433).
Proof. exact (TRANS (@lem3908587 A _45432 _45433) (@lem3908630 A _45432 _45433)). Qed.
Lemma lem3908632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3908633 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term184 A _45432 _45433) = (term185 A _45432 _45433).
Proof. exact (MK_COMB (@lem3908632) (@lem3908631 A _45432 _45433)). Qed.
Lemma lem3908647 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3908648 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term95 A _45432 _45433) = (term107 A _45432 _45433).
Proof. exact (@lem3908647 (term140 A _45433) (term150 A _45432 _45433)). Qed.
Lemma lem3908654 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term186 A _45432 _45433) = (term186 A _45432 _45433).
Proof. exact (eq_refl (term186 A _45432 _45433)). Qed.
Lemma lem3908655 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term187 A _45432 _45433) = (term183 A _45432 _45433).
Proof. exact (MK_COMB (@lem3908654 A _45432 _45433) (@lem3908648 A _45432 _45433)). Qed.
Lemma lem3908666 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : ((term153 A _45432 _45433) = (term187 A _45432 _45433)) = ((term183 A _45432 _45433) = (term183 A _45432 _45433)).
Proof. exact (MK_COMB (@lem3908633 A _45432 _45433) (@lem3908655 A _45432 _45433)). Qed.
Lemma lem3908668 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3908669 (x : Prop) : (x = x) = True.
Proof. exact (@lem3908668 Prop x). Qed.
Lemma lem3908670 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : ((term183 A _45432 _45433) = (term183 A _45432 _45433)) = True.
Proof. exact (@lem3908669 (term183 A _45432 _45433)). Qed.
Lemma lem3908671 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : ((term153 A _45432 _45433) = (term187 A _45432 _45433)) = True.
Proof. exact (TRANS (@lem3908666 A _45432 _45433) (@lem3908670 A _45432 _45433)). Qed.
Lemma lem3908672 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : True = ((term153 A _45432 _45433) = (term187 A _45432 _45433)).
Proof. exact (SYM (@lem3908671 A _45432 _45433)). Qed.
Lemma lem3908673 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term153 A _45432 _45433) = (term187 A _45432 _45433).
Proof. exact (EQ_MP (@lem3908672 A _45432 _45433) (@lem0)). Qed.
Lemma lem3908674 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) (h1 : term12 A) : term187 A _45432 _45433.
Proof. exact (EQ_MP (@lem3908673 A _45432 _45433) (@lem3908409 A _45432 _45433 h1)). Qed.
Lemma lem3908676 (b : Prop) (a : Prop) : (a \/ b) = (term164 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3908677 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term187 A _45432 _45433) = (term188 A _45432 _45433).
Proof. exact (@lem3908676 (term95 A _45432 _45433) (term96 A _45432 _45433)). Qed.
Lemma lem3908679 (a : Prop) (b : Prop) : (term166 a b) = (term167 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3908680 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term189 A _45432 _45433) = (term190 A _45432 _45433).
Proof. exact (@lem3908679 (term150 A _45432 _45433) (term140 A _45433)). Qed.
Lemma lem3908682 (a : Prop) : (term170 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3908683 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term174 A _45432 _45433) = (@SUBSET A _45432 _45433).
Proof. exact (@lem3908682 (@SUBSET A _45432 _45433)). Qed.
Lemma lem3908684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3908685 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term191 A _45432 _45433) = (term192 A _45432 _45433).
Proof. exact (MK_COMB (@lem3908684) (@lem3908683 A _45432 _45433)). Qed.
Lemma lem3908687 (a : Prop) : (term170 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3908688 {A : Type'} (_45433 : A -> Prop) : (term171 A _45433) = (@FINITE A _45433).
Proof. exact (@lem3908687 (@FINITE A _45433)). Qed.
Lemma lem3908689 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term190 A _45432 _45433) = (term101 A _45432 _45433).
Proof. exact (MK_COMB (@lem3908685 A _45432 _45433) (@lem3908688 A _45433)). Qed.
Lemma lem3908690 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term189 A _45432 _45433) = (term101 A _45432 _45433).
Proof. exact (TRANS (@lem3908680 A _45432 _45433) (@lem3908689 A _45432 _45433)). Qed.
Lemma lem3908691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3908692 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term193 A _45432 _45433) = (term194 A _45432 _45433).
Proof. exact (MK_COMB (@lem3908691) (@lem3908690 A _45432 _45433)). Qed.
Lemma lem3908693 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term96 A _45432 _45433) = (term96 A _45432 _45433).
Proof. exact (eq_refl (term96 A _45432 _45433)). Qed.
Lemma lem3908694 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term188 A _45432 _45433) = (term31 A _45432 _45433).
Proof. exact (MK_COMB (@lem3908692 A _45432 _45433) (@lem3908693 A _45432 _45433)). Qed.
Lemma lem3908695 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) : (term187 A _45432 _45433) = (term31 A _45432 _45433).
Proof. exact (TRANS (@lem3908677 A _45432 _45433) (@lem3908694 A _45432 _45433)). Qed.
Lemma lem3908697 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term101 A s t.
Proof. exact (conj (@lem3908573 A t s n h1) (@lem3908580 A t s n h1)). Qed.
Lemma lem3908699 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) (h1 : term12 A) : term31 A _45432 _45433.
Proof. exact (EQ_MP (@lem3908695 A _45432 _45433) (@lem3908674 A _45432 _45433 h1)). Qed.
Lemma lem3908700 {A : Type'} (_45432 : A -> Prop) (_45433 : A -> Prop) (h1 : term12 A) : term31 A _45432 _45433.
Proof. exact (@lem3908699 A _45432 _45433 h1). Qed.
Lemma lem3908701 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) : term31 A s t.
Proof. exact (@lem3908700 A s t h1). Qed.
Lemma lem3908704 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term53 A t s n) : term96 A s t.
Proof. exact (@lem3908701 A s t h1 (@lem3908697 A t s n h2)). Qed.
Lemma lem3908705 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term53 A t s n) : term195 A s t.
Proof. exact (fun h0 : term196 A s t => @lem3908704 A t s n h1 h2). Qed.
Lemma lem3908707 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3908708 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term195 A s t) = (term96 A s t).
Proof. exact (@lem3908707 (term96 A s t)). Qed.
Lemma lem3908709 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term53 A t s n) : term96 A s t.
Proof. exact (EQ_MP (@lem3908708 A s t) (@lem3908705 A t s n h1 h2)). Qed.
Lemma lem3908711 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term50 A t n.
Proof. exact (proj2 (@lem3908072 A t s n h1)). Qed.
Lemma lem3908712 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term197 A t n.
Proof. exact (fun h0 : term141 A t n => @lem3908711 A t s n h1). Qed.
Lemma lem3908714 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3908715 {A : Type'} (t : A -> Prop) (n : nat) : (term197 A t n) = (term50 A t n).
Proof. exact (@lem3908714 (term50 A t n)). Qed.
Lemma lem3908716 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term53 A t s n) : term50 A t n.
Proof. exact (EQ_MP (@lem3908715 A t n) (@lem3908712 A t s n h1)). Qed.
Lemma lem3908732 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3908733 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term198 _45430 _45429 _45431) = (term199 _45429 _45430 _45431).
Proof. exact (@lem3908732 (Peano.le _45429 _45431) (term152 _45430 _45431)). Qed.
Lemma lem3908739 (_45429 : nat) (_45430 : nat) : (term200 _45429 _45430) = (term200 _45429 _45430).
Proof. exact (eq_refl (term200 _45429 _45430)). Qed.
Lemma lem3908740 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term151 _45430 _45429 _45431) = (term201 _45429 _45430 _45431).
Proof. exact (MK_COMB (@lem3908739 _45429 _45430) (@lem3908733 _45429 _45430 _45431)). Qed.
Lemma lem3908744 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3908745 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term201 _45429 _45430 _45431) = (term202 _45429 _45430 _45431).
Proof. exact (@lem3908744 (Peano.le _45429 _45431) (term152 _45429 _45430) (term152 _45430 _45431)). Qed.
Lemma lem3908761 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term151 _45430 _45429 _45431) = (term202 _45429 _45430 _45431).
Proof. exact (TRANS (@lem3908740 _45429 _45430 _45431) (@lem3908745 _45429 _45430 _45431)). Qed.
Lemma lem3908762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3908763 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term203 _45430 _45429 _45431) = (term204 _45429 _45430 _45431).
Proof. exact (MK_COMB (@lem3908762) (@lem3908761 _45429 _45430 _45431)). Qed.
Lemma lem3908779 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term202 _45429 _45430 _45431) = (term202 _45429 _45430 _45431).
Proof. exact (eq_refl (term202 _45429 _45430 _45431)). Qed.
Lemma lem3908780 (_45429 : nat) (_45430 : nat) (_45431 : nat) : ((term151 _45430 _45429 _45431) = (term202 _45429 _45430 _45431)) = ((term202 _45429 _45430 _45431) = (term202 _45429 _45430 _45431)).
Proof. exact (MK_COMB (@lem3908763 _45429 _45430 _45431) (@lem3908779 _45429 _45430 _45431)). Qed.
Lemma lem3908782 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3908783 (x : Prop) : (x = x) = True.
Proof. exact (@lem3908782 Prop x). Qed.
Lemma lem3908784 (_45429 : nat) (_45430 : nat) (_45431 : nat) : ((term202 _45429 _45430 _45431) = (term202 _45429 _45430 _45431)) = True.
Proof. exact (@lem3908783 (term202 _45429 _45430 _45431)). Qed.
Lemma lem3908785 (_45429 : nat) (_45430 : nat) (_45431 : nat) : ((term151 _45430 _45429 _45431) = (term202 _45429 _45430 _45431)) = True.
Proof. exact (TRANS (@lem3908780 _45429 _45430 _45431) (@lem3908784 _45429 _45430 _45431)). Qed.
Lemma lem3908786 (_45429 : nat) (_45430 : nat) (_45431 : nat) : True = ((term151 _45430 _45429 _45431) = (term202 _45429 _45430 _45431)).
Proof. exact (SYM (@lem3908785 _45429 _45430 _45431)). Qed.
Lemma lem3908787 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term151 _45430 _45429 _45431) = (term202 _45429 _45430 _45431).
Proof. exact (EQ_MP (@lem3908786 _45429 _45430 _45431) (@lem0)). Qed.
Lemma lem3908788 (_45429 : nat) (_45430 : nat) (_45431 : nat) (h1 : term41) : term202 _45429 _45430 _45431.
Proof. exact (EQ_MP (@lem3908787 _45429 _45430 _45431) (@lem3908397 _45430 _45429 _45431 h1)). Qed.
Lemma lem3908790 (b : Prop) (a : Prop) : (a \/ b) = (term164 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3908791 (_45430 : nat) (_45429 : nat) (_45431 : nat) : (term202 _45429 _45430 _45431) = (term205 _45430 _45429 _45431).
Proof. exact (@lem3908790 (term82 _45429 _45430 _45431) (Peano.le _45429 _45431)). Qed.
Lemma lem3908793 (a : Prop) (b : Prop) : (term166 a b) = (term167 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3908794 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term206 _45429 _45430 _45431) = (term207 _45429 _45430 _45431).
Proof. exact (@lem3908793 (term152 _45429 _45430) (term152 _45430 _45431)). Qed.
Lemma lem3908796 (a : Prop) : (term170 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3908797 (_45429 : nat) (_45430 : nat) : (term208 _45429 _45430) = (Peano.le _45429 _45430).
Proof. exact (@lem3908796 (Peano.le _45429 _45430)). Qed.
Lemma lem3908798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3908799 (_45429 : nat) (_45430 : nat) : (term209 _45429 _45430) = (term210 _45429 _45430).
Proof. exact (MK_COMB (@lem3908798) (@lem3908797 _45429 _45430)). Qed.
Lemma lem3908801 (a : Prop) : (term170 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3908802 (_45430 : nat) (_45431 : nat) : (term208 _45430 _45431) = (Peano.le _45430 _45431).
Proof. exact (@lem3908801 (Peano.le _45430 _45431)). Qed.
Lemma lem3908803 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term207 _45429 _45430 _45431) = (term87 _45429 _45430 _45431).
Proof. exact (MK_COMB (@lem3908799 _45429 _45430) (@lem3908802 _45430 _45431)). Qed.
Lemma lem3908804 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term206 _45429 _45430 _45431) = (term87 _45429 _45430 _45431).
Proof. exact (TRANS (@lem3908794 _45429 _45430 _45431) (@lem3908803 _45429 _45430 _45431)). Qed.
Lemma lem3908805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3908806 (_45429 : nat) (_45430 : nat) (_45431 : nat) : (term211 _45429 _45430 _45431) = (term212 _45429 _45430 _45431).
Proof. exact (MK_COMB (@lem3908805) (@lem3908804 _45429 _45430 _45431)). Qed.
Lemma lem3908807 (_45429 : nat) (_45431 : nat) : (Peano.le _45429 _45431) = (Peano.le _45429 _45431).
Proof. exact (eq_refl (Peano.le _45429 _45431)). Qed.
Lemma lem3908808 (_45430 : nat) (_45429 : nat) (_45431 : nat) : (term205 _45430 _45429 _45431) = (term35 _45430 _45429 _45431).
Proof. exact (MK_COMB (@lem3908806 _45429 _45430 _45431) (@lem3908807 _45429 _45431)). Qed.
Lemma lem3908809 (_45430 : nat) (_45429 : nat) (_45431 : nat) : (term202 _45429 _45430 _45431) = (term35 _45430 _45429 _45431).
Proof. exact (TRANS (@lem3908791 _45430 _45429 _45431) (@lem3908808 _45430 _45429 _45431)). Qed.
Lemma lem3908811 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term53 A t s n) : term213 A s t n.
Proof. exact (conj (@lem3908709 A t s n h1 h2) (@lem3908716 A t s n h2)). Qed.
Lemma lem3908813 (_45430 : nat) (_45429 : nat) (_45431 : nat) (h1 : term41) : term35 _45430 _45429 _45431.
Proof. exact (EQ_MP (@lem3908809 _45430 _45429 _45431) (@lem3908788 _45429 _45430 _45431 h1)). Qed.
Lemma lem3908814 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term41) : term214 A t s n.
Proof. exact (@lem3908813 (@CARD A t) (@CARD A s) n h1). Qed.
Lemma lem3908817 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term53 A t s n) : term50 A s n.
Proof. exact (@lem3908814 A t s n h2 (@lem3908811 A t s n h1 h3)). Qed.
Lemma lem3908818 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term53 A t s n) : term197 A s n.
Proof. exact (fun h0 : term141 A s n => @lem3908817 A t s n h1 h2 h3). Qed.
Lemma lem3908820 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3908821 {A : Type'} (s : A -> Prop) (n : nat) : (term197 A s n) = (term50 A s n).
Proof. exact (@lem3908820 (term50 A s n)). Qed.
Lemma lem3908822 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term53 A t s n) : term50 A s n.
Proof. exact (EQ_MP (@lem3908821 A s n) (@lem3908818 A t s n h1 h2 h3)). Qed.
Lemma lem3908825 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3908827 {A : Type'} (s : A -> Prop) (n : nat) : (term141 A s n) = (term215 A s n).
Proof. exact (@lem3908825 (term50 A s n)). Qed.
Lemma lem3908830 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term141 A s n) : term215 A s n.
Proof. exact (EQ_MP (@lem3908827 A s n) (@lem3908429 A s n h1)). Qed.
Lemma lem3908833 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term141 A s n) (h4 : term53 A t s n) : False.
Proof. exact (@lem3908830 A s n h3 (@lem3908822 A t s n h1 h2 h4)). Qed.
Lemma lem3908834 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term141 A s n) (h4 : term53 A t s n) : term178.
Proof. exact (fun h0 : ~ False => @lem3908833 A t s n h1 h2 h3 h4). Qed.
Lemma lem3908836 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3908837 : term178 = False.
Proof. exact (@lem3908836 False). Qed.
Lemma lem3908838 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term141 A s n) (h4 : term53 A t s n) : False.
Proof. exact (EQ_MP (@lem3908837) (@lem3908834 A t s n h1 h2 h3 h4)). Qed.
Lemma lem3908839 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term141 A s n) (h4 : term53 A t s n) : (term141 A s n) = False.
Proof. exact (prop_ext (fun h5 : term141 A s n => @lem3908838 A t s n h1 h2 h3 h4) (fun h5 : False => @lem3908429 A s n h3)). Qed.
Lemma lem3908840 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term141 A s n) (h4 : term53 A t s n) : False.
Proof. exact (EQ_MP (@lem3908839 A t s n h1 h2 h3 h4) (@lem3908429 A s n h3)). Qed.
Lemma lem3908841 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term140 A s) (h3 : term53 A t s n) : (term140 A s) = False.
Proof. exact (prop_ext (fun h4 : term140 A s => @lem3908566 A t s n h1 h2 h3) (fun h4 : False => @lem3908385 A s h2)). Qed.
Lemma lem3908842 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term140 A s) (h3 : term53 A t s n) : False.
Proof. exact (EQ_MP (@lem3908841 A t s n h1 h2 h3) (@lem3908385 A s h2)). Qed.
Lemma lem3908843 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term141 A s n) (h4 : term53 A t s n) : (term141 A s n) = False.
Proof. exact (prop_ext (fun h5 : term141 A s n => @lem3908840 A t s n h1 h2 h3 h4) (fun h5 : False => @lem3908299 A s n h3)). Qed.
Lemma lem3908844 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term141 A s n) (h4 : term53 A t s n) : False.
Proof. exact (EQ_MP (@lem3908843 A t s n h1 h2 h3 h4) (@lem3908299 A s n h3)). Qed.
Lemma lem3908845 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term140 A s) (h3 : term53 A t s n) : (term140 A s) = False.
Proof. exact (prop_ext (fun h4 : term140 A s => @lem3908842 A t s n h1 h2 h3) (fun h4 : False => @lem3908188 A s h2)). Qed.
Lemma lem3908846 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term140 A s) (h3 : term53 A t s n) : False.
Proof. exact (EQ_MP (@lem3908845 A t s n h1 h2 h3) (@lem3908188 A s h2)). Qed.
Lemma lem3908847 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term141 A s n) (h4 : term53 A t s n) : (term141 A s n) = False.
Proof. exact (prop_ext (fun h5 : term141 A s n => @lem3908844 A t s n h1 h2 h3 h4) (fun h5 : False => @lem3908299 A s n h3)). Qed.
Lemma lem3908848 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term12 A) (h2 : term41) (h3 : term141 A s n) (h4 : term53 A t s n) : False.
Proof. exact (EQ_MP (@lem3908847 A t s n h1 h2 h3 h4) (@lem3908299 A s n h3)). Qed.
Lemma lem3908849 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term140 A s) (h3 : term53 A t s n) : (term140 A s) = False.
Proof. exact (prop_ext (fun h4 : term140 A s => @lem3908846 A t s n h1 h2 h3) (fun h4 : False => @lem3908188 A s h2)). Qed.
Lemma lem3908850 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term140 A s) (h3 : term53 A t s n) : False.
Proof. exact (EQ_MP (@lem3908849 A t s n h1 h2 h3) (@lem3908188 A s h2)). Qed.
Lemma lem3908851 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term12 A) (h3 : term41) (h4 : term53 A t s n) : False.
Proof. exact (or_elim (@lem3908070 A t s n h4) (fun h0 : term140 A s => @lem3908850 A t s n h1 h0 h4) (fun h0 : term141 A s n => @lem3908848 A t s n h2 h3 h0 h4)). Qed.
Lemma lem3908852 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term12 A) (h3 : term41) (h4 : term53 A t s n) : (term53 A t s n) = False.
Proof. exact (prop_ext (fun h5 : term53 A t s n => @lem3908851 A t s n h1 h2 h3 h4) (fun h5 : False => @lem3908069 A t s n h4)). Qed.
Lemma lem3908853 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) (h1 : term11 A) (h2 : term12 A) (h3 : term41) (h4 : term53 A t s n) : False.
Proof. exact (EQ_MP (@lem3908852 A t s n h1 h2 h3 h4) (@lem3908069 A t s n h4)). Qed.
Lemma lem3908854 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term11 A) (h2 : term12 A) (h3 : term41) (h4 : term65 A t s) : False.
Proof. exact (ex_elim (@lem3907929 A t s h4) (fun n : nat => fun h0 : term64 A t s n => @lem3908853 A t s n h1 h2 h3 h0)). Qed.
Lemma lem3908855 {A : Type'} (s : A -> Prop) (h1 : term11 A) (h2 : term12 A) (h3 : term41) (h4 : term74 A s) : False.
Proof. exact (ex_elim (@lem3907928 A s h4) (fun t : A -> Prop => fun h0 : term73 A s t => @lem3908854 A t s h1 h2 h3 h0)). Qed.
Lemma lem3908856 {A : Type'} (h1 : term11 A) (h2 : term12 A) (h3 : term41) (h4 : term10 A) : False.
Proof. exact (ex_elim (@lem3907614 A h4) (fun s : A -> Prop => fun h0 : term79 A s => @lem3908855 A s h1 h2 h3 h0)). Qed.
Lemma lem3908857 {A : Type'} (h1 : term12 A) (h2 : term41) (h3 : term10 A) : term17 A.
Proof. exact (fun h0 : term11 A => @lem3908856 A h0 h1 h2 h3). Qed.
Lemma lem3908858 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem3908859 {A : Type'} (h1 : term12 A) (h2 : term41) (h3 : term10 A) : term18 A.
Proof. exact (EQ_MP (@lem3908858 A) (@lem3908857 A h1 h2 h3)). Qed.
Lemma lem3908860 {A : Type'} (h1 : term41) (h2 : term10 A) : term21 A.
Proof. exact (fun h0 : term12 A => @lem3908859 A h0 h1 h2). Qed.
Lemma lem3908861 {A : Type'} (h1 : term10 A) : term24 A.
Proof. exact (fun h0 : term41 => @lem3908860 A h0 h1). Qed.
Lemma lem3908862 {A : Type'} : term26 A.
Proof. exact (fun h0 : term10 A => @lem3908861 A h0). Qed.
Lemma lem3908863 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3907498 A) (@lem3908862 A)). Qed.
Lemma lem3908865 {A : Type'} : term13 A.
Proof. exact (@lem3907236 A (@lem3908863 A)). Qed.
Lemma lem3908866 {A : Type'} (h1 : term10 A) : term23 A.
Proof. exact (@lem3908865 A (@lem3907215 A h1)). Qed.
Lemma lem3908867 {A : Type'} (h1 : term10 A) : term20 A.
Proof. exact (@lem3908866 A h1 (@lem93743)). Qed.
Lemma lem3908868 {A : Type'} (h1 : term10 A) : term17 A.
Proof. exact (@lem3908867 A h1 (@lem3907218 A)). Qed.
Lemma lem3908869 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem3908868 A h1 (@lem3907216 A)). Qed.
Lemma lem3908870 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem3908869 A h1) (fun h2 : False => @lem3907215 A h1)). Qed.
Lemma lem3908871 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem3908870 A h1) (@lem3907215 A h1)). Qed.
Lemma lem3908872 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem3908871 A h0). Qed.
Lemma lem3908873 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3907214 A) (@lem3908872 A)). Qed.
