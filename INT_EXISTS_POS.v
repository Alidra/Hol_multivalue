Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EXISTS_POS_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import INT_FORALL_POS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem2315391 (P : int -> Prop) : term0 P.
Proof. exact (@lem2315380 P). Qed.
Lemma lem2315392 (P : int -> Prop) : (term0 P) = ((term1 P) = (term2 P)).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem2315394 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem2315395 {A : Type'} (P : A -> Prop) : (term3 A P) = ((term4 A P) = (term5 A P)).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem2315405 (p : Prop) : term6 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem2315406 (p : Prop) : (term6 p) = (term7 p).
Proof. exact (eq_refl (term6 p)). Qed.
Lemma lem2315407 (p : Prop) : term7 p.
Proof. exact (EQ_MP (@lem2315406 p) (@lem2315405 p)). Qed.
Lemma lem2315408 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem2315409 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem2315418 (q : Prop) : (term8 q) = (term8 q).
Proof. exact (eq_refl (term8 q)). Qed.
Lemma lem2315419 (q : Prop) (p : Prop) (h1 : p = True) : (term9 q p) = (term10 q).
Proof. exact (MK_COMB (@lem2315418 q) (@lem2315408 p h1)). Qed.
Lemma lem2315420 (q : Prop) : (term10 q) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (eq_refl (term10 q)). Qed.
Lemma lem2315421 (q : Prop) (p : Prop) : (term11 q p) = (term11 q p).
Proof. exact (eq_refl (term11 q p)). Qed.
Lemma lem2315422 (p : Prop) (q : Prop) : ((term9 q p) = (term10 q)) = ((term9 q p) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (MK_COMB (@lem2315421 q p) (@lem2315420 q)). Qed.
Lemma lem2315423 (p : Prop) (q : Prop) : (term9 q p) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (eq_refl (term9 q p)). Qed.
Lemma lem2315424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315425 (p : Prop) (q : Prop) : (term11 q p) = (term12 p q).
Proof. exact (MK_COMB (@lem2315424) (@lem2315423 p q)). Qed.
Lemma lem2315426 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (eq_refl ((True = q) = ((~ True) = (~ q)))). Qed.
Lemma lem2315427 (p : Prop) (q : Prop) : ((term9 q p) = ((True = q) = ((~ True) = (~ q)))) = (((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (MK_COMB (@lem2315425 p q) (@lem2315426 q)). Qed.
Lemma lem2315428 (p : Prop) (q : Prop) : ((term9 q p) = (term10 q)) = (((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (TRANS (@lem2315422 p q) (@lem2315427 p q)). Qed.
Lemma lem2315429 (q : Prop) (p : Prop) (h1 : p = True) : ((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (EQ_MP (@lem2315428 p q) (@lem2315419 q p h1)). Qed.
Lemma lem2315430 (q : Prop) (p : Prop) (h1 : p = True) : ((True = q) = ((~ True) = (~ q))) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (SYM (@lem2315429 q p h1)). Qed.
Lemma lem2315431 (q : Prop) : (term8 q) = (term8 q).
Proof. exact (eq_refl (term8 q)). Qed.
Lemma lem2315432 (q : Prop) (p : Prop) (h1 : p = False) : (term9 q p) = (term13 q).
Proof. exact (MK_COMB (@lem2315431 q) (@lem2315409 p h1)). Qed.
Lemma lem2315433 (q : Prop) : (term13 q) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (eq_refl (term13 q)). Qed.
Lemma lem2315434 (q : Prop) (p : Prop) : (term11 q p) = (term11 q p).
Proof. exact (eq_refl (term11 q p)). Qed.
Lemma lem2315435 (p : Prop) (q : Prop) : ((term9 q p) = (term13 q)) = ((term9 q p) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (MK_COMB (@lem2315434 q p) (@lem2315433 q)). Qed.
Lemma lem2315436 (p : Prop) (q : Prop) : (term9 q p) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (eq_refl (term9 q p)). Qed.
Lemma lem2315437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315438 (p : Prop) (q : Prop) : (term11 q p) = (term12 p q).
Proof. exact (MK_COMB (@lem2315437) (@lem2315436 p q)). Qed.
Lemma lem2315439 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (eq_refl ((False = q) = ((~ False) = (~ q)))). Qed.
Lemma lem2315440 (p : Prop) (q : Prop) : ((term9 q p) = ((False = q) = ((~ False) = (~ q)))) = (((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (MK_COMB (@lem2315438 p q) (@lem2315439 q)). Qed.
Lemma lem2315441 (p : Prop) (q : Prop) : ((term9 q p) = (term13 q)) = (((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (TRANS (@lem2315435 p q) (@lem2315440 p q)). Qed.
Lemma lem2315442 (q : Prop) (p : Prop) (h1 : p = False) : ((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (EQ_MP (@lem2315441 p q) (@lem2315432 q p h1)). Qed.
Lemma lem2315443 (q : Prop) (p : Prop) (h1 : p = False) : ((False = q) = ((~ False) = (~ q))) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (SYM (@lem2315442 q p h1)). Qed.
Lemma lem2315447 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2315448 (q : Prop) : (True = q) = q.
Proof. exact (@lem2315447 q). Qed.
Lemma lem2315449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315450 (q : Prop) : (term14 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem2315449) (@lem2315448 q)). Qed.
Lemma lem2315454 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem2315455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315456 : term15 = (@eq Prop False).
Proof. exact (MK_COMB (@lem2315455) (@lem2315454)). Qed.
Lemma lem2315457 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem2315458 (q : Prop) : ((~ True) = (~ q)) = (False = (~ q)).
Proof. exact (MK_COMB (@lem2315456) (@lem2315457 q)). Qed.
Lemma lem2315460 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2315461 (q : Prop) : (False = (~ q)) = (term16 q).
Proof. exact (@lem2315460 (~ q)). Qed.
Lemma lem2315463 (t : Prop) : (term16 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem2315464 (q : Prop) : (term16 q) = q.
Proof. exact (@lem2315463 q). Qed.
Lemma lem2315465 (q : Prop) : (False = (~ q)) = q.
Proof. exact (TRANS (@lem2315461 q) (@lem2315464 q)). Qed.
Lemma lem2315466 (q : Prop) : ((~ True) = (~ q)) = q.
Proof. exact (TRANS (@lem2315458 q) (@lem2315465 q)). Qed.
Lemma lem2315467 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = (q = q).
Proof. exact (MK_COMB (@lem2315450 q) (@lem2315466 q)). Qed.
Lemma lem2315469 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2315470 (x : Prop) : (x = x) = True.
Proof. exact (@lem2315469 Prop x). Qed.
Lemma lem2315471 (q : Prop) : (q = q) = True.
Proof. exact (@lem2315470 q). Qed.
Lemma lem2315472 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = True.
Proof. exact (TRANS (@lem2315467 q) (@lem2315471 q)). Qed.
Lemma lem2315473 (q : Prop) : True = ((True = q) = ((~ True) = (~ q))).
Proof. exact (SYM (@lem2315472 q)). Qed.
Lemma lem2315474 (q : Prop) : (True = q) = ((~ True) = (~ q)).
Proof. exact (EQ_MP (@lem2315473 q) (@lem0)). Qed.
Lemma lem2315478 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2315479 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem2315478 q). Qed.
Lemma lem2315480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315481 (q : Prop) : (term17 q) = (term18 q).
Proof. exact (MK_COMB (@lem2315480) (@lem2315479 q)). Qed.
Lemma lem2315485 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2315486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315487 : term19 = (@eq Prop True).
Proof. exact (MK_COMB (@lem2315486) (@lem2315485)). Qed.
Lemma lem2315488 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem2315489 (q : Prop) : ((~ False) = (~ q)) = (True = (~ q)).
Proof. exact (MK_COMB (@lem2315487) (@lem2315488 q)). Qed.
Lemma lem2315491 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2315492 (q : Prop) : (True = (~ q)) = (~ q).
Proof. exact (@lem2315491 (~ q)). Qed.
Lemma lem2315493 (q : Prop) : ((~ False) = (~ q)) = (~ q).
Proof. exact (TRANS (@lem2315489 q) (@lem2315492 q)). Qed.
Lemma lem2315494 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem2315481 q) (@lem2315493 q)). Qed.
Lemma lem2315496 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2315497 (x : Prop) : (x = x) = True.
Proof. exact (@lem2315496 Prop x). Qed.
Lemma lem2315498 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem2315497 (~ q)). Qed.
Lemma lem2315499 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = True.
Proof. exact (TRANS (@lem2315494 q) (@lem2315498 q)). Qed.
Lemma lem2315500 (q : Prop) : True = ((False = q) = ((~ False) = (~ q))).
Proof. exact (SYM (@lem2315499 q)). Qed.
Lemma lem2315501 (q : Prop) : (False = q) = ((~ False) = (~ q)).
Proof. exact (EQ_MP (@lem2315500 q) (@lem0)). Qed.
Lemma lem2315502 (q : Prop) (p : Prop) (h1 : p = False) : (p = q) = ((~ p) = (~ q)).
Proof. exact (EQ_MP (@lem2315443 q p h1) (@lem2315501 q)). Qed.
Lemma lem2315503 (q : Prop) (p : Prop) (h1 : p = True) : (p = q) = ((~ p) = (~ q)).
Proof. exact (EQ_MP (@lem2315430 q p h1) (@lem2315474 q)). Qed.
Lemma lem2315508 (p : Prop) (q : Prop) : (p = q) = ((~ p) = (~ q)).
Proof. exact (or_elim (@lem2315407 p) (fun h0 : p = True => @lem2315503 q p h0) (fun h0 : p = False => @lem2315502 q p h0)). Qed.
Lemma lem2315509 (P : int -> Prop) : ((term20 P) = (term21 P)) = ((term22 P) = (term23 P)).
Proof. exact (@lem2315508 (term20 P) (term21 P)). Qed.
Lemma lem2315510 (P : int -> Prop) : ((term22 P) = (term23 P)) = ((term20 P) = (term21 P)).
Proof. exact (SYM (@lem2315509 P)). Qed.
Lemma lem2315514 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (EQ_MP (@lem2315395 A P) (@lem2315394 A P)). Qed.
Lemma lem2315515 (P : nat -> Prop) : (term24 P) = (term25 P).
Proof. exact (@lem2315514 nat P). Qed.
Lemma lem2315516 (P : int -> Prop) : (term26 P) = (term27 P).
Proof. exact (@lem2315515 (term28 P)). Qed.
Lemma lem2315517 (P : int -> Prop) (n : nat) : (term29 P n) = (term30 P n).
Proof. exact (eq_refl (term29 P n)). Qed.
Lemma lem2315518 (P : int -> Prop) : (term31 P) = (term28 P).
Proof. exact (fun_ext (fun n : nat => @lem2315517 P n)). Qed.
Lemma lem2315519 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2315520 (P : int -> Prop) : (term32 P) = (term20 P).
Proof. exact (MK_COMB (@lem2315519) (@lem2315518 P)). Qed.
Lemma lem2315521 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2315522 (P : int -> Prop) : (term26 P) = (term22 P).
Proof. exact (MK_COMB (@lem2315521) (@lem2315520 P)). Qed.
Lemma lem2315523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315524 (P : int -> Prop) : (term33 P) = (term34 P).
Proof. exact (MK_COMB (@lem2315523) (@lem2315522 P)). Qed.
Lemma lem2315525 (P : int -> Prop) (n : nat) : (term29 P n) = (term30 P n).
Proof. exact (eq_refl (term29 P n)). Qed.
Lemma lem2315526 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2315527 (P : int -> Prop) (n : nat) : (term35 P n) = (term36 P n).
Proof. exact (MK_COMB (@lem2315526) (@lem2315525 P n)). Qed.
Lemma lem2315528 (P : int -> Prop) : (term37 P) = (term38 P).
Proof. exact (fun_ext (fun n : nat => @lem2315527 P n)). Qed.
Lemma lem2315529 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2315530 (P : int -> Prop) : (term27 P) = (term39 P).
Proof. exact (MK_COMB (@lem2315529) (@lem2315528 P)). Qed.
Lemma lem2315531 (P : int -> Prop) : ((term26 P) = (term27 P)) = ((term22 P) = (term39 P)).
Proof. exact (MK_COMB (@lem2315524 P) (@lem2315530 P)). Qed.
Lemma lem2315532 (P : int -> Prop) : (term22 P) = (term39 P).
Proof. exact (EQ_MP (@lem2315531 P) (@lem2315516 P)). Qed.
Lemma lem2315538 (P : int -> Prop) : (term1 P) = (term2 P).
Proof. exact (EQ_MP (@lem2315392 P) (@lem2315391 P)). Qed.
Lemma lem2315539 (P : int -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem2315538 (term42 P)). Qed.
Lemma lem2315540 (P : int -> Prop) (n : nat) : (term43 P n) = (term36 P n).
Proof. exact (eq_refl (term43 P n)). Qed.
Lemma lem2315541 (P : int -> Prop) : (term44 P) = (term38 P).
Proof. exact (fun_ext (fun n : nat => @lem2315540 P n)). Qed.
Lemma lem2315542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2315543 (P : int -> Prop) : (term40 P) = (term39 P).
Proof. exact (MK_COMB (@lem2315542) (@lem2315541 P)). Qed.
Lemma lem2315544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315545 (P : int -> Prop) : (term45 P) = (term46 P).
Proof. exact (MK_COMB (@lem2315544) (@lem2315543 P)). Qed.
Lemma lem2315546 (P : int -> Prop) (i : int) : (term47 P i) = (term48 P i).
Proof. exact (eq_refl (term47 P i)). Qed.
Lemma lem2315547 (i : int) : (term49 i) = (term49 i).
Proof. exact (eq_refl (term49 i)). Qed.
Lemma lem2315548 (P : int -> Prop) (i : int) : (term50 P i) = (term51 P i).
Proof. exact (MK_COMB (@lem2315547 i) (@lem2315546 P i)). Qed.
Lemma lem2315549 (P : int -> Prop) : (term52 P) = (term53 P).
Proof. exact (fun_ext (fun i : int => @lem2315548 P i)). Qed.
Lemma lem2315550 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2315551 (P : int -> Prop) : (term41 P) = (term54 P).
Proof. exact (MK_COMB (@lem2315550) (@lem2315549 P)). Qed.
Lemma lem2315552 (P : int -> Prop) : ((term40 P) = (term41 P)) = ((term39 P) = (term54 P)).
Proof. exact (MK_COMB (@lem2315545 P) (@lem2315551 P)). Qed.
Lemma lem2315553 (P : int -> Prop) : (term39 P) = (term54 P).
Proof. exact (EQ_MP (@lem2315552 P) (@lem2315539 P)). Qed.
Lemma lem2315560 (P : int -> Prop) : (term22 P) = (term54 P).
Proof. exact (TRANS (@lem2315532 P) (@lem2315553 P)). Qed.
Lemma lem2315563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315564 (P : int -> Prop) : (term34 P) = (term55 P).
Proof. exact (MK_COMB (@lem2315563) (@lem2315560 P)). Qed.
Lemma lem2315566 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (EQ_MP (@lem2315395 A P) (@lem2315394 A P)). Qed.
Lemma lem2315567 (P : int -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem2315566 int P). Qed.
Lemma lem2315568 (P : int -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem2315567 (term60 P)). Qed.
Lemma lem2315569 (P : int -> Prop) (i : int) : (term61 P i) = (term62 P i).
Proof. exact (eq_refl (term61 P i)). Qed.
Lemma lem2315570 (P : int -> Prop) : (term63 P) = (term60 P).
Proof. exact (fun_ext (fun i : int => @lem2315569 P i)). Qed.
Lemma lem2315571 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2315572 (P : int -> Prop) : (term64 P) = (term21 P).
Proof. exact (MK_COMB (@lem2315571) (@lem2315570 P)). Qed.
Lemma lem2315573 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2315574 (P : int -> Prop) : (term58 P) = (term23 P).
Proof. exact (MK_COMB (@lem2315573) (@lem2315572 P)). Qed.
Lemma lem2315575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315576 (P : int -> Prop) : (term65 P) = (term66 P).
Proof. exact (MK_COMB (@lem2315575) (@lem2315574 P)). Qed.
Lemma lem2315577 (P : int -> Prop) (i : int) : (term61 P i) = (term62 P i).
Proof. exact (eq_refl (term61 P i)). Qed.
Lemma lem2315578 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2315579 (P : int -> Prop) (i : int) : (term67 P i) = (term68 P i).
Proof. exact (MK_COMB (@lem2315578) (@lem2315577 P i)). Qed.
Lemma lem2315580 (P : int -> Prop) : (term69 P) = (term70 P).
Proof. exact (fun_ext (fun i : int => @lem2315579 P i)). Qed.
Lemma lem2315581 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2315582 (P : int -> Prop) : (term59 P) = (term71 P).
Proof. exact (MK_COMB (@lem2315581) (@lem2315580 P)). Qed.
Lemma lem2315583 (P : int -> Prop) : ((term58 P) = (term59 P)) = ((term23 P) = (term71 P)).
Proof. exact (MK_COMB (@lem2315576 P) (@lem2315582 P)). Qed.
Lemma lem2315584 (P : int -> Prop) : (term23 P) = (term71 P).
Proof. exact (EQ_MP (@lem2315583 P) (@lem2315568 P)). Qed.
Lemma lem2315593 (P : int -> Prop) : ((term22 P) = (term23 P)) = ((term54 P) = (term71 P)).
Proof. exact (MK_COMB (@lem2315564 P) (@lem2315584 P)). Qed.
Lemma lem2315596 (P : int -> Prop) : ((term54 P) = (term71 P)) = ((term22 P) = (term23 P)).
Proof. exact (SYM (@lem2315593 P)). Qed.
Lemma lem2315598 (p : Prop) : p = (term72 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2315599 (P : int -> Prop) : ((term54 P) = (term71 P)) = (term73 P).
Proof. exact (@lem2315598 ((term54 P) = (term71 P))). Qed.
Lemma lem2315600 (P : int -> Prop) : (term73 P) = ((term54 P) = (term71 P)).
Proof. exact (SYM (@lem2315599 P)). Qed.
Lemma lem2315601 (P : int -> Prop) (h1 : term74 P) : term74 P.
Proof. exact (h1). Qed.
Lemma lem2315604 (P : int -> Prop) (h1 : term73 P) : term73 P.
Proof. exact (h1). Qed.
Lemma lem2315605 (P : int -> Prop) : term75 P.
Proof. exact (fun h0 : term73 P => @lem2315604 P h0). Qed.
Lemma lem2315606 (P : int -> Prop) (h1 : term75 P) : term75 P.
Proof. exact (h1). Qed.
Lemma lem2315607 (P : int -> Prop) (h1 : term73 P) : term73 P.
Proof. exact (h1). Qed.
Lemma lem2315608 (P : int -> Prop) (h1 : term73 P) (h2 : term75 P) : term73 P.
Proof. exact (@lem2315606 P h2 (@lem2315607 P h1)). Qed.
Lemma lem2315609 (P : int -> Prop) (h1 : term73 P) : term76 P.
Proof. exact (fun h0 : term75 P => @lem2315608 P h1 h0). Qed.
Lemma lem2315610 (P : int -> Prop) (h1 : term75 P) : term75 P.
Proof. exact (h1). Qed.
Lemma lem2315611 (P : int -> Prop) (h1 : term73 P) (h2 : term75 P) : term73 P.
Proof. exact (@lem2315609 P h1 (@lem2315610 P h2)). Qed.
Lemma lem2315612 (P : int -> Prop) (h1 : term75 P) : term75 P.
Proof. exact (fun h0 : term73 P => @lem2315611 P h0 h1). Qed.
Lemma lem2315613 (P : int -> Prop) : term77 P.
Proof. exact (fun h0 : term75 P => @lem2315612 P h0). Qed.
Lemma lem2315616 (P : int -> Prop) : term75 P.
Proof. exact (@lem2315613 P (@lem2315605 P)). Qed.
Lemma lem2315622 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2315623 (P : int -> Prop) : (term73 P) = (term78 P).
Proof. exact (@lem2315622 (term74 P)). Qed.
Lemma lem2315625 (t : Prop) : (term16 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2315626 (P : int -> Prop) : (term78 P) = ((term54 P) = (term71 P)).
Proof. exact (@lem2315625 ((term54 P) = (term71 P))). Qed.
Lemma lem2315627 (P : int -> Prop) : (term73 P) = ((term54 P) = (term71 P)).
Proof. exact (TRANS (@lem2315623 P) (@lem2315626 P)). Qed.
Lemma lem2315640 : term79 = term80.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2315627 P)). Qed.
Lemma lem2315641 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem2315650 : term81 = term82.
Proof. exact (MK_COMB (@lem2315641) (@lem2315640)). Qed.
Lemma lem2315657 (P : int -> Prop) (i : int) : (term68 P i) = (term68 P i).
Proof. exact (eq_refl (term68 P i)). Qed.
Lemma lem2315658 (P : int -> Prop) : (term70 P) = (term70 P).
Proof. exact (fun_ext (fun i : int => @lem2315657 P i)). Qed.
Lemma lem2315659 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2315660 (P : int -> Prop) : (term71 P) = (term71 P).
Proof. exact (MK_COMB (@lem2315659) (@lem2315658 P)). Qed.
Lemma lem2315667 (P : int -> Prop) (i : int) : (term51 P i) = (term51 P i).
Proof. exact (eq_refl (term51 P i)). Qed.
Lemma lem2315668 (P : int -> Prop) : (term53 P) = (term53 P).
Proof. exact (fun_ext (fun i : int => @lem2315667 P i)). Qed.
Lemma lem2315669 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2315670 (P : int -> Prop) : (term54 P) = (term54 P).
Proof. exact (MK_COMB (@lem2315669) (@lem2315668 P)). Qed.
Lemma lem2315671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315672 (P : int -> Prop) : (term55 P) = (term55 P).
Proof. exact (MK_COMB (@lem2315671) (@lem2315670 P)). Qed.
Lemma lem2315673 (P : int -> Prop) : ((term54 P) = (term71 P)) = ((term54 P) = (term71 P)).
Proof. exact (MK_COMB (@lem2315672 P) (@lem2315660 P)). Qed.
Lemma lem2315674 : term80 = term80.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2315673 P)). Qed.
Lemma lem2315675 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem2315676 : term82 = term82.
Proof. exact (MK_COMB (@lem2315675) (@lem2315674)). Qed.
Lemma lem2315701 : term81 = term82.
Proof. exact (TRANS (@lem2315650) (@lem2315676)). Qed.
Lemma lem2315702 : term82 = term81.
Proof. exact (SYM (@lem2315701)). Qed.
Lemma lem2315704 (p : Prop) : p = (term72 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2315705 (P : int -> Prop) : ((term54 P) = (term71 P)) = (term73 P).
Proof. exact (@lem2315704 ((term54 P) = (term71 P))). Qed.
Lemma lem2315706 (P : int -> Prop) : (term73 P) = ((term54 P) = (term71 P)).
Proof. exact (SYM (@lem2315705 P)). Qed.
Lemma lem2315707 (P : int -> Prop) (h1 : term74 P) : term74 P.
Proof. exact (h1). Qed.
Lemma lem2315713 (P : int -> Prop) (i : int) : (term83 P i) = (P i).
Proof. exact (@lem16933 (P i)). Qed.
Lemma lem2315715 (i : int) : (term84 i) = (term84 i).
Proof. exact (eq_refl (term84 i)). Qed.
Lemma lem2315716 (P : int -> Prop) (i : int) : (term85 P i) = (term62 P i).
Proof. exact (MK_COMB (@lem2315715 i) (@lem2315713 P i)). Qed.
Lemma lem2315717 (P : int -> Prop) (i : int) : (term86 P i) = (term85 P i).
Proof. exact (@lem17362 (term87 i) (term48 P i)). Qed.
Lemma lem2315718 (P : int -> Prop) (i : int) : (term86 P i) = (term62 P i).
Proof. exact (TRANS (@lem2315717 P i) (@lem2315716 P i)). Qed.
Lemma lem2315723 (P : int -> Prop) (i : int) : (term51 P i) = (term88 P i).
Proof. exact (@lem17265 (term87 i) (term48 P i)). Qed.
Lemma lem2315724 (P : int -> Prop) : (term89 P) = (term90 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2315725 (P : int -> Prop) : (term91 P) = (term92 P).
Proof. exact (@lem2315724 (term53 P)). Qed.
Lemma lem2315726 (P : int -> Prop) (i : int) : (term93 P i) = (term51 P i).
Proof. exact (eq_refl (term93 P i)). Qed.
Lemma lem2315727 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2315728 (P : int -> Prop) (i : int) : (term94 P i) = (term86 P i).
Proof. exact (MK_COMB (@lem2315727) (@lem2315726 P i)). Qed.
Lemma lem2315729 (P : int -> Prop) (i : int) : (term94 P i) = (term62 P i).
Proof. exact (TRANS (@lem2315728 P i) (@lem2315718 P i)). Qed.
Lemma lem2315730 (P : int -> Prop) : (term95 P) = (term60 P).
Proof. exact (fun_ext (fun i : int => @lem2315729 P i)). Qed.
Lemma lem2315731 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2315732 (P : int -> Prop) : (term92 P) = (term21 P).
Proof. exact (MK_COMB (@lem2315731) (@lem2315730 P)). Qed.
Lemma lem2315733 (P : int -> Prop) : (term91 P) = (term21 P).
Proof. exact (TRANS (@lem2315725 P) (@lem2315732 P)). Qed.
Lemma lem2315734 (P : int -> Prop) : (term53 P) = (term96 P).
Proof. exact (fun_ext (fun i : int => @lem2315723 P i)). Qed.
Lemma lem2315735 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2315736 (P : int -> Prop) : (term54 P) = (term97 P).
Proof. exact (MK_COMB (@lem2315735) (@lem2315734 P)). Qed.
Lemma lem2315745 (P : int -> Prop) (i : int) : (term68 P i) = (term88 P i).
Proof. exact (@lem17045 (term87 i) (P i)). Qed.
Lemma lem2315750 (P : int -> Prop) (i : int) : (term98 P i) = (term62 P i).
Proof. exact (@lem16933 (term62 P i)). Qed.
Lemma lem2315751 (P : int -> Prop) : (term89 P) = (term90 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2315752 (P : int -> Prop) : (term99 P) = (term100 P).
Proof. exact (@lem2315751 (term70 P)). Qed.
Lemma lem2315753 (P : int -> Prop) (i : int) : (term101 P i) = (term68 P i).
Proof. exact (eq_refl (term101 P i)). Qed.
Lemma lem2315754 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2315755 (P : int -> Prop) (i : int) : (term102 P i) = (term98 P i).
Proof. exact (MK_COMB (@lem2315754) (@lem2315753 P i)). Qed.
Lemma lem2315756 (P : int -> Prop) (i : int) : (term102 P i) = (term62 P i).
Proof. exact (TRANS (@lem2315755 P i) (@lem2315750 P i)). Qed.
Lemma lem2315757 (P : int -> Prop) : (term103 P) = (term60 P).
Proof. exact (fun_ext (fun i : int => @lem2315756 P i)). Qed.
Lemma lem2315758 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2315759 (P : int -> Prop) : (term100 P) = (term21 P).
Proof. exact (MK_COMB (@lem2315758) (@lem2315757 P)). Qed.
Lemma lem2315760 (P : int -> Prop) : (term99 P) = (term21 P).
Proof. exact (TRANS (@lem2315752 P) (@lem2315759 P)). Qed.
Lemma lem2315761 (P : int -> Prop) : (term70 P) = (term96 P).
Proof. exact (fun_ext (fun i : int => @lem2315745 P i)). Qed.
Lemma lem2315762 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2315763 (P : int -> Prop) : (term71 P) = (term97 P).
Proof. exact (MK_COMB (@lem2315762) (@lem2315761 P)). Qed.
Lemma lem2315764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2315765 (P : int -> Prop) : (term104 P) = (term105 P).
Proof. exact (MK_COMB (@lem2315764) (@lem2315733 P)). Qed.
Lemma lem2315766 (P : int -> Prop) : (term106 P) = (term107 P).
Proof. exact (MK_COMB (@lem2315765 P) (@lem2315763 P)). Qed.
Lemma lem2315767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2315768 (P : int -> Prop) : (term108 P) = (term109 P).
Proof. exact (MK_COMB (@lem2315767) (@lem2315736 P)). Qed.
Lemma lem2315769 (P : int -> Prop) : (term110 P) = (term111 P).
Proof. exact (MK_COMB (@lem2315768 P) (@lem2315760 P)). Qed.
Lemma lem2315770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2315771 (P : int -> Prop) : (term112 P) = (term113 P).
Proof. exact (MK_COMB (@lem2315770) (@lem2315769 P)). Qed.
Lemma lem2315772 (P : int -> Prop) : (term114 P) = (term115 P).
Proof. exact (MK_COMB (@lem2315771 P) (@lem2315766 P)). Qed.
Lemma lem2315773 (P : int -> Prop) : (term74 P) = (term114 P).
Proof. exact (@lem17646 (term54 P) (term71 P)). Qed.
Lemma lem2315774 (P : int -> Prop) : (term74 P) = (term115 P).
Proof. exact (TRANS (@lem2315773 P) (@lem2315772 P)). Qed.
Lemma lem2315937 {A : Type'} (P : Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2315938 (P : Prop) (Q : int -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem2315937 int P Q). Qed.
Lemma lem2315939 (P : int -> Prop) : (term120 P) = (term121 P).
Proof. exact (@lem2315938 (term97 P) (term60 P)). Qed.
Lemma lem2315940 (P : int -> Prop) (i : int) : (term61 P i) = (term62 P i).
Proof. exact (eq_refl (term61 P i)). Qed.
Lemma lem2315941 (P : int -> Prop) : (term63 P) = (term60 P).
Proof. exact (fun_ext (fun i : int => @lem2315940 P i)). Qed.
Lemma lem2315942 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2315943 (P : int -> Prop) : (term64 P) = (term21 P).
Proof. exact (MK_COMB (@lem2315942) (@lem2315941 P)). Qed.
Lemma lem2315944 (P : int -> Prop) : (term109 P) = (term109 P).
Proof. exact (eq_refl (term109 P)). Qed.
Lemma lem2315945 (P : int -> Prop) : (term120 P) = (term111 P).
Proof. exact (MK_COMB (@lem2315944 P) (@lem2315943 P)). Qed.
Lemma lem2315946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315947 (P : int -> Prop) : (term122 P) = (term123 P).
Proof. exact (MK_COMB (@lem2315946) (@lem2315945 P)). Qed.
Lemma lem2315948 (P : int -> Prop) (i : int) : (term61 P i) = (term62 P i).
Proof. exact (eq_refl (term61 P i)). Qed.
Lemma lem2315949 (P : int -> Prop) : (term109 P) = (term109 P).
Proof. exact (eq_refl (term109 P)). Qed.
Lemma lem2315950 (P : int -> Prop) (i : int) : (term124 P i) = (term125 P i).
Proof. exact (MK_COMB (@lem2315949 P) (@lem2315948 P i)). Qed.
Lemma lem2315951 (P : int -> Prop) : (term126 P) = (term127 P).
Proof. exact (fun_ext (fun i : int => @lem2315950 P i)). Qed.
Lemma lem2315952 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2315953 (P : int -> Prop) : (term121 P) = (term128 P).
Proof. exact (MK_COMB (@lem2315952) (@lem2315951 P)). Qed.
Lemma lem2315954 (P : int -> Prop) : ((term120 P) = (term121 P)) = ((term111 P) = (term128 P)).
Proof. exact (MK_COMB (@lem2315947 P) (@lem2315953 P)). Qed.
Lemma lem2315955 (P : int -> Prop) : (term111 P) = (term128 P).
Proof. exact (EQ_MP (@lem2315954 P) (@lem2315939 P)). Qed.
Lemma lem2315956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2315957 (P : int -> Prop) : (term113 P) = (term129 P).
Proof. exact (MK_COMB (@lem2315956) (@lem2315955 P)). Qed.
Lemma lem2315959 {A : Type'} (P : A -> Prop) (Q : Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem2315960 (P : int -> Prop) (Q : Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem2315959 int P Q). Qed.
Lemma lem2315961 (P : int -> Prop) : (term134 P) = (term135 P).
Proof. exact (@lem2315960 (term60 P) (term97 P)). Qed.
Lemma lem2315962 (P : int -> Prop) (i : int) : (term61 P i) = (term62 P i).
Proof. exact (eq_refl (term61 P i)). Qed.
Lemma lem2315963 (P : int -> Prop) : (term63 P) = (term60 P).
Proof. exact (fun_ext (fun i : int => @lem2315962 P i)). Qed.
Lemma lem2315964 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2315965 (P : int -> Prop) : (term64 P) = (term21 P).
Proof. exact (MK_COMB (@lem2315964) (@lem2315963 P)). Qed.
Lemma lem2315966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2315967 (P : int -> Prop) : (term136 P) = (term105 P).
Proof. exact (MK_COMB (@lem2315966) (@lem2315965 P)). Qed.
Lemma lem2315968 (P : int -> Prop) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem2315969 (P : int -> Prop) : (term134 P) = (term107 P).
Proof. exact (MK_COMB (@lem2315967 P) (@lem2315968 P)). Qed.
Lemma lem2315970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315971 (P : int -> Prop) : (term137 P) = (term138 P).
Proof. exact (MK_COMB (@lem2315970) (@lem2315969 P)). Qed.
Lemma lem2315972 (P : int -> Prop) (i : int) : (term61 P i) = (term62 P i).
Proof. exact (eq_refl (term61 P i)). Qed.
Lemma lem2315973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2315974 (P : int -> Prop) (i : int) : (term139 P i) = (term140 P i).
Proof. exact (MK_COMB (@lem2315973) (@lem2315972 P i)). Qed.
Lemma lem2315975 (P : int -> Prop) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem2315976 (i : int) (P : int -> Prop) : (term141 i P) = (term142 i P).
Proof. exact (MK_COMB (@lem2315974 P i) (@lem2315975 P)). Qed.
Lemma lem2315977 (P : int -> Prop) : (term143 P) = (term144 P).
Proof. exact (fun_ext (fun i : int => @lem2315976 i P)). Qed.
Lemma lem2315978 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2315979 (P : int -> Prop) : (term135 P) = (term145 P).
Proof. exact (MK_COMB (@lem2315978) (@lem2315977 P)). Qed.
Lemma lem2315980 (P : int -> Prop) : ((term134 P) = (term135 P)) = ((term107 P) = (term145 P)).
Proof. exact (MK_COMB (@lem2315971 P) (@lem2315979 P)). Qed.
Lemma lem2315981 (P : int -> Prop) : (term107 P) = (term145 P).
Proof. exact (EQ_MP (@lem2315980 P) (@lem2315961 P)). Qed.
Lemma lem2315982 (P : int -> Prop) : (term115 P) = (term146 P).
Proof. exact (MK_COMB (@lem2315957 P) (@lem2315981 P)). Qed.
Lemma lem2315984 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2315985 (P : int -> Prop) (Q : int -> Prop) : (term149 P Q) = (term150 P Q).
Proof. exact (@lem2315984 int P Q). Qed.
Lemma lem2315986 (P : int -> Prop) : (term151 P) = (term152 P).
Proof. exact (@lem2315985 (term127 P) (term144 P)). Qed.
Lemma lem2315987 (P : int -> Prop) (i : int) : (term153 P i) = (term125 P i).
Proof. exact (eq_refl (term153 P i)). Qed.
Lemma lem2315988 (P : int -> Prop) : (term154 P) = (term127 P).
Proof. exact (fun_ext (fun i : int => @lem2315987 P i)). Qed.
Lemma lem2315989 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2315990 (P : int -> Prop) : (term155 P) = (term128 P).
Proof. exact (MK_COMB (@lem2315989) (@lem2315988 P)). Qed.
Lemma lem2315991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2315992 (P : int -> Prop) : (term156 P) = (term129 P).
Proof. exact (MK_COMB (@lem2315991) (@lem2315990 P)). Qed.
Lemma lem2315993 (i : int) (P : int -> Prop) : (term157 P i) = (term142 i P).
Proof. exact (eq_refl (term157 P i)). Qed.
Lemma lem2315994 (P : int -> Prop) : (term158 P) = (term144 P).
Proof. exact (fun_ext (fun i : int => @lem2315993 i P)). Qed.
Lemma lem2315995 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2315996 (P : int -> Prop) : (term159 P) = (term145 P).
Proof. exact (MK_COMB (@lem2315995) (@lem2315994 P)). Qed.
Lemma lem2315997 (P : int -> Prop) : (term151 P) = (term146 P).
Proof. exact (MK_COMB (@lem2315992 P) (@lem2315996 P)). Qed.
Lemma lem2315998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2315999 (P : int -> Prop) : (term160 P) = (term161 P).
Proof. exact (MK_COMB (@lem2315998) (@lem2315997 P)). Qed.
Lemma lem2316000 (P : int -> Prop) (i : int) : (term153 P i) = (term125 P i).
Proof. exact (eq_refl (term153 P i)). Qed.
Lemma lem2316001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2316002 (P : int -> Prop) (i : int) : (term162 P i) = (term163 P i).
Proof. exact (MK_COMB (@lem2316001) (@lem2316000 P i)). Qed.
Lemma lem2316003 (i : int) (P : int -> Prop) : (term157 P i) = (term142 i P).
Proof. exact (eq_refl (term157 P i)). Qed.
Lemma lem2316004 (i : int) (P : int -> Prop) : (term164 P i) = (term165 i P).
Proof. exact (MK_COMB (@lem2316002 P i) (@lem2316003 i P)). Qed.
Lemma lem2316005 (P : int -> Prop) : (term166 P) = (term167 P).
Proof. exact (fun_ext (fun i : int => @lem2316004 i P)). Qed.
Lemma lem2316006 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2316007 (P : int -> Prop) : (term152 P) = (term168 P).
Proof. exact (MK_COMB (@lem2316006) (@lem2316005 P)). Qed.
Lemma lem2316008 (P : int -> Prop) : ((term151 P) = (term152 P)) = ((term146 P) = (term168 P)).
Proof. exact (MK_COMB (@lem2315999 P) (@lem2316007 P)). Qed.
Lemma lem2316009 (P : int -> Prop) : (term146 P) = (term168 P).
Proof. exact (EQ_MP (@lem2316008 P) (@lem2315986 P)). Qed.
Lemma lem2316011 (P : int -> Prop) : (term115 P) = (term168 P).
Proof. exact (TRANS (@lem2315982 P) (@lem2316009 P)). Qed.
Lemma lem2316012 (P : int -> Prop) : (term74 P) = (term168 P).
Proof. exact (TRANS (@lem2315774 P) (@lem2316011 P)). Qed.
Lemma lem2316013 (P : int -> Prop) (h1 : term74 P) : term168 P.
Proof. exact (EQ_MP (@lem2316012 P) (@lem2315707 P h1)). Qed.
Lemma lem2316014 (i : int) (P : int -> Prop) (h1 : term165 i P) : term165 i P.
Proof. exact (h1). Qed.
Lemma lem2316033 (P : int -> Prop) (i : int) : (term88 P i) = (term88 P i).
Proof. exact (eq_refl (term88 P i)). Qed.
Lemma lem2316034 (P : int -> Prop) : (term96 P) = (term96 P).
Proof. exact (fun_ext (fun i : int => @lem2316033 P i)). Qed.
Lemma lem2316035 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2316036 (P : int -> Prop) : (term97 P) = (term97 P).
Proof. exact (MK_COMB (@lem2316035) (@lem2316034 P)). Qed.
Lemma lem2316053 (P : int -> Prop) (i : int) : (term140 P i) = (term140 P i).
Proof. exact (eq_refl (term140 P i)). Qed.
Lemma lem2316054 (i : int) (P : int -> Prop) : (term142 i P) = (term142 i P).
Proof. exact (MK_COMB (@lem2316053 P i) (@lem2316036 P)). Qed.
Lemma lem2316069 (P : int -> Prop) (i : int) : (term62 P i) = (term62 P i).
Proof. exact (eq_refl (term62 P i)). Qed.
Lemma lem2316088 (P : int -> Prop) (i : int) : (term88 P i) = (term88 P i).
Proof. exact (eq_refl (term88 P i)). Qed.
Lemma lem2316089 (P : int -> Prop) : (term96 P) = (term96 P).
Proof. exact (fun_ext (fun i : int => @lem2316088 P i)). Qed.
Lemma lem2316090 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2316091 (P : int -> Prop) : (term97 P) = (term97 P).
Proof. exact (MK_COMB (@lem2316090) (@lem2316089 P)). Qed.
Lemma lem2316092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2316093 (P : int -> Prop) : (term109 P) = (term109 P).
Proof. exact (MK_COMB (@lem2316092) (@lem2316091 P)). Qed.
Lemma lem2316094 (P : int -> Prop) (i : int) : (term125 P i) = (term125 P i).
Proof. exact (MK_COMB (@lem2316093 P) (@lem2316069 P i)). Qed.
Lemma lem2316095 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2316096 (P : int -> Prop) (i : int) : (term163 P i) = (term163 P i).
Proof. exact (MK_COMB (@lem2316095) (@lem2316094 P i)). Qed.
Lemma lem2316097 (i : int) (P : int -> Prop) : (term165 i P) = (term165 i P).
Proof. exact (MK_COMB (@lem2316096 P i) (@lem2316054 i P)). Qed.
Lemma lem2316098 (i : int) (P : int -> Prop) (h1 : term165 i P) : term165 i P.
Proof. exact (EQ_MP (@lem2316097 i P) (@lem2316014 i P h1)). Qed.
Lemma lem2316099 (P : int -> Prop) (i : int) (h1 : term125 P i) : term125 P i.
Proof. exact (h1). Qed.
Lemma lem2316100 (i : int) (P : int -> Prop) (h1 : term142 i P) : term142 i P.
Proof. exact (h1). Qed.
Lemma lem2316101 (P : int -> Prop) (i : int) (h1 : term125 P i) : term62 P i.
Proof. exact (proj2 (@lem2316099 P i h1)). Qed.
Lemma lem2316102 (P : int -> Prop) (i : int) (h1 : term125 P i) : term97 P.
Proof. exact (proj1 (@lem2316099 P i h1)). Qed.
Lemma lem2316105 (i : int) (P : int -> Prop) (h1 : term142 i P) : term97 P.
Proof. exact (proj2 (@lem2316100 i P h1)). Qed.
Lemma lem2316106 (i : int) (P : int -> Prop) (h1 : term142 i P) : term62 P i.
Proof. exact (proj1 (@lem2316100 i P h1)). Qed.
Lemma lem2316116 (P : int -> Prop) (i : int) : (term88 P i) = (term88 P i).
Proof. exact (eq_refl (term88 P i)). Qed.
Lemma lem2316117 (P : int -> Prop) : (term96 P) = (term96 P).
Proof. exact (fun_ext (fun i : int => @lem2316116 P i)). Qed.
Lemma lem2316118 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2316120 (P : int -> Prop) : (term97 P) = (term97 P).
Proof. exact (MK_COMB (@lem2316118) (@lem2316117 P)). Qed.
Lemma lem2316121 (P : int -> Prop) (i : int) (h1 : term125 P i) : term97 P.
Proof. exact (EQ_MP (@lem2316120 P) (@lem2316102 P i h1)). Qed.
Lemma lem2316137 (P : int -> Prop) (i : int) : (term88 P i) = (term88 P i).
Proof. exact (eq_refl (term88 P i)). Qed.
Lemma lem2316138 (P : int -> Prop) : (term96 P) = (term96 P).
Proof. exact (fun_ext (fun i : int => @lem2316137 P i)). Qed.
Lemma lem2316139 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2316141 (P : int -> Prop) : (term97 P) = (term97 P).
Proof. exact (MK_COMB (@lem2316139) (@lem2316138 P)). Qed.
Lemma lem2316142 (i : int) (P : int -> Prop) (h1 : term142 i P) : term97 P.
Proof. exact (EQ_MP (@lem2316141 P) (@lem2316105 i P h1)). Qed.
Lemma lem2316151 (_28990 : int) (P : int -> Prop) (i : int) (h1 : term125 P i) : term169 P _28990.
Proof. exact (@lem2316121 P i h1 _28990). Qed.
Lemma lem2316152 (P : int -> Prop) (_28990 : int) : (term169 P _28990) = (term88 P _28990).
Proof. exact (eq_refl (term169 P _28990)). Qed.
Lemma lem2316154 (_28991 : int) (i : int) (P : int -> Prop) (h1 : term142 i P) : term169 P _28991.
Proof. exact (@lem2316142 i P h1 _28991). Qed.
Lemma lem2316155 (P : int -> Prop) (_28991 : int) : (term169 P _28991) = (term88 P _28991).
Proof. exact (eq_refl (term169 P _28991)). Qed.
Lemma lem2316162 (_28990 : int) (P : int -> Prop) (i : int) (h1 : term125 P i) : term88 P _28990.
Proof. exact (EQ_MP (@lem2316152 P _28990) (@lem2316151 _28990 P i h1)). Qed.
Lemma lem2316172 (_28991 : int) (i : int) (P : int -> Prop) (h1 : term142 i P) : term88 P _28991.
Proof. exact (EQ_MP (@lem2316155 P _28991) (@lem2316154 _28991 i P h1)). Qed.
Lemma lem2316178 (P : int -> Prop) (i : int) (h1 : term125 P i) : term87 i.
Proof. exact (proj1 (@lem2316101 P i h1)). Qed.
Lemma lem2316179 (P : int -> Prop) (i : int) (h1 : term125 P i) : term170 i.
Proof. exact (fun h0 : term171 i => @lem2316178 P i h1). Qed.
Lemma lem2316181 (p : Prop) : (term172 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2316182 (i : int) : (term170 i) = (term87 i).
Proof. exact (@lem2316181 (term87 i)). Qed.
Lemma lem2316183 (P : int -> Prop) (i : int) (h1 : term125 P i) : term87 i.
Proof. exact (EQ_MP (@lem2316182 i) (@lem2316179 P i h1)). Qed.
Lemma lem2316185 (P : int -> Prop) (i : int) (h1 : term125 P i) : P i.
Proof. exact (proj2 (@lem2316101 P i h1)). Qed.
Lemma lem2316186 (P : int -> Prop) (i : int) (h1 : term125 P i) : term173 P i.
Proof. exact (fun h0 : term48 P i => @lem2316185 P i h1). Qed.
Lemma lem2316188 (p : Prop) : (term172 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2316189 (P : int -> Prop) (i : int) : (term173 P i) = (P i).
Proof. exact (@lem2316188 (P i)). Qed.
Lemma lem2316190 (P : int -> Prop) (i : int) (h1 : term125 P i) : P i.
Proof. exact (EQ_MP (@lem2316189 P i) (@lem2316186 P i h1)). Qed.
Lemma lem2316192 (a : Prop) (b : Prop) : (term174 a b) = (term175 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem2316193 (P : int -> Prop) (_28990 : int) : (term88 P _28990) = (term68 P _28990).
Proof. exact (@lem2316192 (term87 _28990) (P _28990)). Qed.
Lemma lem2316195 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2316196 (P : int -> Prop) (_28990 : int) : (term68 P _28990) = (term176 P _28990).
Proof. exact (@lem2316195 (term62 P _28990)). Qed.
Lemma lem2316197 (P : int -> Prop) (_28990 : int) : (term88 P _28990) = (term176 P _28990).
Proof. exact (TRANS (@lem2316193 P _28990) (@lem2316196 P _28990)). Qed.
Lemma lem2316199 (P : int -> Prop) (i : int) (h1 : term125 P i) : term62 P i.
Proof. exact (conj (@lem2316183 P i h1) (@lem2316190 P i h1)). Qed.
Lemma lem2316201 (_28990 : int) (P : int -> Prop) (i : int) (h1 : term125 P i) : term176 P _28990.
Proof. exact (EQ_MP (@lem2316197 P _28990) (@lem2316162 _28990 P i h1)). Qed.
Lemma lem2316202 (P : int -> Prop) (i : int) (h1 : term125 P i) : term176 P i.
Proof. exact (@lem2316201 i P i h1). Qed.
Lemma lem2316205 (P : int -> Prop) (i : int) (h1 : term125 P i) : False.
Proof. exact (@lem2316202 P i h1 (@lem2316199 P i h1)). Qed.
Lemma lem2316206 (P : int -> Prop) (i : int) (h1 : term125 P i) : term177.
Proof. exact (fun h0 : ~ False => @lem2316205 P i h1). Qed.
Lemma lem2316208 (p : Prop) : (term172 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2316209 : term177 = False.
Proof. exact (@lem2316208 False). Qed.
Lemma lem2316210 (P : int -> Prop) (i : int) (h1 : term125 P i) : False.
Proof. exact (EQ_MP (@lem2316209) (@lem2316206 P i h1)). Qed.
Lemma lem2316212 (i : int) (P : int -> Prop) (h1 : term142 i P) : term87 i.
Proof. exact (proj1 (@lem2316106 i P h1)). Qed.
Lemma lem2316213 (i : int) (P : int -> Prop) (h1 : term142 i P) : term170 i.
Proof. exact (fun h0 : term171 i => @lem2316212 i P h1). Qed.
Lemma lem2316215 (p : Prop) : (term172 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2316216 (i : int) : (term170 i) = (term87 i).
Proof. exact (@lem2316215 (term87 i)). Qed.
Lemma lem2316217 (i : int) (P : int -> Prop) (h1 : term142 i P) : term87 i.
Proof. exact (EQ_MP (@lem2316216 i) (@lem2316213 i P h1)). Qed.
Lemma lem2316219 (i : int) (P : int -> Prop) (h1 : term142 i P) : P i.
Proof. exact (proj2 (@lem2316106 i P h1)). Qed.
Lemma lem2316220 (i : int) (P : int -> Prop) (h1 : term142 i P) : term173 P i.
Proof. exact (fun h0 : term48 P i => @lem2316219 i P h1). Qed.
Lemma lem2316222 (p : Prop) : (term172 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2316223 (P : int -> Prop) (i : int) : (term173 P i) = (P i).
Proof. exact (@lem2316222 (P i)). Qed.
Lemma lem2316224 (i : int) (P : int -> Prop) (h1 : term142 i P) : P i.
Proof. exact (EQ_MP (@lem2316223 P i) (@lem2316220 i P h1)). Qed.
Lemma lem2316226 (a : Prop) (b : Prop) : (term174 a b) = (term175 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem2316227 (P : int -> Prop) (_28991 : int) : (term88 P _28991) = (term68 P _28991).
Proof. exact (@lem2316226 (term87 _28991) (P _28991)). Qed.
Lemma lem2316229 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2316230 (P : int -> Prop) (_28991 : int) : (term68 P _28991) = (term176 P _28991).
Proof. exact (@lem2316229 (term62 P _28991)). Qed.
Lemma lem2316231 (P : int -> Prop) (_28991 : int) : (term88 P _28991) = (term176 P _28991).
Proof. exact (TRANS (@lem2316227 P _28991) (@lem2316230 P _28991)). Qed.
Lemma lem2316233 (i : int) (P : int -> Prop) (h1 : term142 i P) : term62 P i.
Proof. exact (conj (@lem2316217 i P h1) (@lem2316224 i P h1)). Qed.
Lemma lem2316235 (_28991 : int) (i : int) (P : int -> Prop) (h1 : term142 i P) : term176 P _28991.
Proof. exact (EQ_MP (@lem2316231 P _28991) (@lem2316172 _28991 i P h1)). Qed.
Lemma lem2316236 (i : int) (P : int -> Prop) (h1 : term142 i P) : term176 P i.
Proof. exact (@lem2316235 i i P h1). Qed.
Lemma lem2316239 (i : int) (P : int -> Prop) (h1 : term142 i P) : False.
Proof. exact (@lem2316236 i P h1 (@lem2316233 i P h1)). Qed.
Lemma lem2316240 (i : int) (P : int -> Prop) (h1 : term142 i P) : term177.
Proof. exact (fun h0 : ~ False => @lem2316239 i P h1). Qed.
Lemma lem2316242 (p : Prop) : (term172 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2316243 : term177 = False.
Proof. exact (@lem2316242 False). Qed.
Lemma lem2316244 (i : int) (P : int -> Prop) (h1 : term142 i P) : False.
Proof. exact (EQ_MP (@lem2316243) (@lem2316240 i P h1)). Qed.
Lemma lem2316245 (i : int) (P : int -> Prop) (h1 : term165 i P) : False.
Proof. exact (or_elim (@lem2316098 i P h1) (fun h0 : term125 P i => @lem2316210 P i h0) (fun h0 : term142 i P => @lem2316244 i P h0)). Qed.
Lemma lem2316246 (i : int) (P : int -> Prop) (h1 : term165 i P) : (term165 i P) = False.
Proof. exact (prop_ext (fun h2 : term165 i P => @lem2316245 i P h1) (fun h2 : False => @lem2316098 i P h1)). Qed.
Lemma lem2316247 (i : int) (P : int -> Prop) (h1 : term165 i P) : False.
Proof. exact (EQ_MP (@lem2316246 i P h1) (@lem2316098 i P h1)). Qed.
Lemma lem2316248 (P : int -> Prop) (h1 : term74 P) : False.
Proof. exact (ex_elim (@lem2316013 P h1) (fun i : int => fun h0 : term167 P i => @lem2316247 i P h0)). Qed.
Lemma lem2316249 (P : int -> Prop) (h1 : term74 P) : (term74 P) = False.
Proof. exact (prop_ext (fun h2 : term74 P => @lem2316248 P h1) (fun h2 : False => @lem2315707 P h1)). Qed.
Lemma lem2316250 (P : int -> Prop) (h1 : term74 P) : False.
Proof. exact (EQ_MP (@lem2316249 P h1) (@lem2315707 P h1)). Qed.
Lemma lem2316251 (P : int -> Prop) : term73 P.
Proof. exact (fun h0 : term74 P => @lem2316250 P h0). Qed.
Lemma lem2316252 (P : int -> Prop) : (term54 P) = (term71 P).
Proof. exact (EQ_MP (@lem2315706 P) (@lem2316251 P)). Qed.
Lemma lem2316257 : term82.
Proof. exact (fun P : int -> Prop => @lem2316252 P). Qed.
Lemma lem2316258 : term81.
Proof. exact (EQ_MP (@lem2315702) (@lem2316257)). Qed.
Lemma lem2316259 (P : int -> Prop) : term178 P.
Proof. exact (@lem2316258 P). Qed.
Lemma lem2316260 (P : int -> Prop) : (term178 P) = (term73 P).
Proof. exact (eq_refl (term178 P)). Qed.
Lemma lem2316261 (P : int -> Prop) : term73 P.
Proof. exact (EQ_MP (@lem2316260 P) (@lem2316259 P)). Qed.
Lemma lem2316263 (P : int -> Prop) : term73 P.
Proof. exact (@lem2315616 P (@lem2316261 P)). Qed.
Lemma lem2316264 (P : int -> Prop) (h1 : term74 P) : False.
Proof. exact (@lem2316263 P (@lem2315601 P h1)). Qed.
Lemma lem2316265 (P : int -> Prop) (h1 : term74 P) : (term74 P) = False.
Proof. exact (prop_ext (fun h2 : term74 P => @lem2316264 P h1) (fun h2 : False => @lem2315601 P h1)). Qed.
Lemma lem2316266 (P : int -> Prop) (h1 : term74 P) : False.
Proof. exact (EQ_MP (@lem2316265 P h1) (@lem2315601 P h1)). Qed.
Lemma lem2316267 (P : int -> Prop) : term73 P.
Proof. exact (fun h0 : term74 P => @lem2316266 P h0). Qed.
Lemma lem2316268 (P : int -> Prop) : (term54 P) = (term71 P).
Proof. exact (EQ_MP (@lem2315600 P) (@lem2316267 P)). Qed.
Lemma lem2316269 (P : int -> Prop) : (term22 P) = (term23 P).
Proof. exact (EQ_MP (@lem2315596 P) (@lem2316268 P)). Qed.
Lemma lem2316270 (P : int -> Prop) : (term20 P) = (term21 P).
Proof. exact (EQ_MP (@lem2315510 P) (@lem2316269 P)). Qed.
Lemma lem2316275 : term179.
Proof. exact (fun P : int -> Prop => @lem2316270 P). Qed.
