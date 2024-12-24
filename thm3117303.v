Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117303_term_abbrevs.
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
Require Import thm1842_spec.
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
Lemma lem3116362 (P : int -> Prop) : term0 P.
Proof. exact (@lem2315380 P). Qed.
Lemma lem3116363 (P : int -> Prop) : (term0 P) = ((term1 P) = (term2 P)).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem3116365 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem3116366 {A : Type'} (P : A -> Prop) : (term3 A P) = ((term4 A P) = (term5 A P)).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem3116376 (a : Prop) : term6 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem3116377 (a : Prop) : (term6 a) = (term7 a).
Proof. exact (eq_refl (term6 a)). Qed.
Lemma lem3116378 (a : Prop) : term7 a.
Proof. exact (EQ_MP (@lem3116377 a) (@lem3116376 a)). Qed.
Lemma lem3116379 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem3116380 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem3116389 (b : Prop) : (term8 b) = (term8 b).
Proof. exact (eq_refl (term8 b)). Qed.
Lemma lem3116390 (b : Prop) (a : Prop) (h1 : a = True) : (term9 b a) = (term10 b).
Proof. exact (MK_COMB (@lem3116389 b) (@lem3116379 a h1)). Qed.
Lemma lem3116391 (b : Prop) : (term10 b) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (eq_refl (term10 b)). Qed.
Lemma lem3116392 (b : Prop) (a : Prop) : (term11 b a) = (term11 b a).
Proof. exact (eq_refl (term11 b a)). Qed.
Lemma lem3116393 (a : Prop) (b : Prop) : ((term9 b a) = (term10 b)) = ((term9 b a) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (MK_COMB (@lem3116392 b a) (@lem3116391 b)). Qed.
Lemma lem3116394 (a : Prop) (b : Prop) : (term9 b a) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (eq_refl (term9 b a)). Qed.
Lemma lem3116395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116396 (a : Prop) (b : Prop) : (term11 b a) = (term12 a b).
Proof. exact (MK_COMB (@lem3116395) (@lem3116394 a b)). Qed.
Lemma lem3116397 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (eq_refl ((True = b) = ((~ True) = (~ b)))). Qed.
Lemma lem3116398 (a : Prop) (b : Prop) : ((term9 b a) = ((True = b) = ((~ True) = (~ b)))) = (((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (MK_COMB (@lem3116396 a b) (@lem3116397 b)). Qed.
Lemma lem3116399 (a : Prop) (b : Prop) : ((term9 b a) = (term10 b)) = (((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (TRANS (@lem3116393 a b) (@lem3116398 a b)). Qed.
Lemma lem3116400 (b : Prop) (a : Prop) (h1 : a = True) : ((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (EQ_MP (@lem3116399 a b) (@lem3116390 b a h1)). Qed.
Lemma lem3116401 (b : Prop) (a : Prop) (h1 : a = True) : ((True = b) = ((~ True) = (~ b))) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (SYM (@lem3116400 b a h1)). Qed.
Lemma lem3116402 (b : Prop) : (term8 b) = (term8 b).
Proof. exact (eq_refl (term8 b)). Qed.
Lemma lem3116403 (b : Prop) (a : Prop) (h1 : a = False) : (term9 b a) = (term13 b).
Proof. exact (MK_COMB (@lem3116402 b) (@lem3116380 a h1)). Qed.
Lemma lem3116404 (b : Prop) : (term13 b) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (eq_refl (term13 b)). Qed.
Lemma lem3116405 (b : Prop) (a : Prop) : (term11 b a) = (term11 b a).
Proof. exact (eq_refl (term11 b a)). Qed.
Lemma lem3116406 (a : Prop) (b : Prop) : ((term9 b a) = (term13 b)) = ((term9 b a) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (MK_COMB (@lem3116405 b a) (@lem3116404 b)). Qed.
Lemma lem3116407 (a : Prop) (b : Prop) : (term9 b a) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (eq_refl (term9 b a)). Qed.
Lemma lem3116408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116409 (a : Prop) (b : Prop) : (term11 b a) = (term12 a b).
Proof. exact (MK_COMB (@lem3116408) (@lem3116407 a b)). Qed.
Lemma lem3116410 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (eq_refl ((False = b) = ((~ False) = (~ b)))). Qed.
Lemma lem3116411 (a : Prop) (b : Prop) : ((term9 b a) = ((False = b) = ((~ False) = (~ b)))) = (((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (MK_COMB (@lem3116409 a b) (@lem3116410 b)). Qed.
Lemma lem3116412 (a : Prop) (b : Prop) : ((term9 b a) = (term13 b)) = (((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (TRANS (@lem3116406 a b) (@lem3116411 a b)). Qed.
Lemma lem3116413 (b : Prop) (a : Prop) (h1 : a = False) : ((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (EQ_MP (@lem3116412 a b) (@lem3116403 b a h1)). Qed.
Lemma lem3116414 (b : Prop) (a : Prop) (h1 : a = False) : ((False = b) = ((~ False) = (~ b))) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (SYM (@lem3116413 b a h1)). Qed.
Lemma lem3116418 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3116419 (b : Prop) : (True = b) = b.
Proof. exact (@lem3116418 b). Qed.
Lemma lem3116420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116421 (b : Prop) : (term14 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem3116420) (@lem3116419 b)). Qed.
Lemma lem3116425 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3116426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116427 : term15 = (@eq Prop False).
Proof. exact (MK_COMB (@lem3116426) (@lem3116425)). Qed.
Lemma lem3116428 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem3116429 (b : Prop) : ((~ True) = (~ b)) = (False = (~ b)).
Proof. exact (MK_COMB (@lem3116427) (@lem3116428 b)). Qed.
Lemma lem3116431 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3116432 (b : Prop) : (False = (~ b)) = (term16 b).
Proof. exact (@lem3116431 (~ b)). Qed.
Lemma lem3116434 (t : Prop) : (term16 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem3116435 (b : Prop) : (term16 b) = b.
Proof. exact (@lem3116434 b). Qed.
Lemma lem3116436 (b : Prop) : (False = (~ b)) = b.
Proof. exact (TRANS (@lem3116432 b) (@lem3116435 b)). Qed.
Lemma lem3116437 (b : Prop) : ((~ True) = (~ b)) = b.
Proof. exact (TRANS (@lem3116429 b) (@lem3116436 b)). Qed.
Lemma lem3116438 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = (b = b).
Proof. exact (MK_COMB (@lem3116421 b) (@lem3116437 b)). Qed.
Lemma lem3116440 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3116441 (x : Prop) : (x = x) = True.
Proof. exact (@lem3116440 Prop x). Qed.
Lemma lem3116442 (b : Prop) : (b = b) = True.
Proof. exact (@lem3116441 b). Qed.
Lemma lem3116443 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = True.
Proof. exact (TRANS (@lem3116438 b) (@lem3116442 b)). Qed.
Lemma lem3116444 (b : Prop) : True = ((True = b) = ((~ True) = (~ b))).
Proof. exact (SYM (@lem3116443 b)). Qed.
Lemma lem3116445 (b : Prop) : (True = b) = ((~ True) = (~ b)).
Proof. exact (EQ_MP (@lem3116444 b) (@lem0)). Qed.
Lemma lem3116449 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3116450 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem3116449 b). Qed.
Lemma lem3116451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116452 (b : Prop) : (term17 b) = (term18 b).
Proof. exact (MK_COMB (@lem3116451) (@lem3116450 b)). Qed.
Lemma lem3116456 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3116457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116458 : term19 = (@eq Prop True).
Proof. exact (MK_COMB (@lem3116457) (@lem3116456)). Qed.
Lemma lem3116459 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem3116460 (b : Prop) : ((~ False) = (~ b)) = (True = (~ b)).
Proof. exact (MK_COMB (@lem3116458) (@lem3116459 b)). Qed.
Lemma lem3116462 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3116463 (b : Prop) : (True = (~ b)) = (~ b).
Proof. exact (@lem3116462 (~ b)). Qed.
Lemma lem3116464 (b : Prop) : ((~ False) = (~ b)) = (~ b).
Proof. exact (TRANS (@lem3116460 b) (@lem3116463 b)). Qed.
Lemma lem3116465 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem3116452 b) (@lem3116464 b)). Qed.
Lemma lem3116467 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3116468 (x : Prop) : (x = x) = True.
Proof. exact (@lem3116467 Prop x). Qed.
Lemma lem3116469 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem3116468 (~ b)). Qed.
Lemma lem3116470 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = True.
Proof. exact (TRANS (@lem3116465 b) (@lem3116469 b)). Qed.
Lemma lem3116471 (b : Prop) : True = ((False = b) = ((~ False) = (~ b))).
Proof. exact (SYM (@lem3116470 b)). Qed.
Lemma lem3116472 (b : Prop) : (False = b) = ((~ False) = (~ b)).
Proof. exact (EQ_MP (@lem3116471 b) (@lem0)). Qed.
Lemma lem3116473 (b : Prop) (a : Prop) (h1 : a = False) : (a = b) = ((~ a) = (~ b)).
Proof. exact (EQ_MP (@lem3116414 b a h1) (@lem3116472 b)). Qed.
Lemma lem3116474 (b : Prop) (a : Prop) (h1 : a = True) : (a = b) = ((~ a) = (~ b)).
Proof. exact (EQ_MP (@lem3116401 b a h1) (@lem3116445 b)). Qed.
Lemma lem3116479 (a : Prop) (b : Prop) : (a = b) = ((~ a) = (~ b)).
Proof. exact (or_elim (@lem3116378 a) (fun h0 : a = True => @lem3116474 b a h0) (fun h0 : a = False => @lem3116473 b a h0)). Qed.
Lemma lem3116480 (P : int -> Prop) : ((term20 P) = (term21 P)) = ((term22 P) = (term23 P)).
Proof. exact (@lem3116479 (term20 P) (term21 P)). Qed.
Lemma lem3116481 (P : int -> Prop) : (term24 P) = (term24 P).
Proof. exact (eq_refl (term24 P)). Qed.
Lemma lem3116482 (P : int -> Prop) : (term25 P) = (term26 P).
Proof. exact (MK_COMB (@lem3116481 P) (@lem3116480 P)). Qed.
Lemma lem3116483 (P : int -> Prop) : (term26 P) = (term25 P).
Proof. exact (SYM (@lem3116482 P)). Qed.
Lemma lem3116493 (P : int -> Prop) : (term1 P) = (term2 P).
Proof. exact (EQ_MP (@lem3116363 P) (@lem3116362 P)). Qed.
Lemma lem3116502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116503 (P : int -> Prop) : (term27 P) = (term28 P).
Proof. exact (MK_COMB (@lem3116502) (@lem3116493 P)). Qed.
Lemma lem3116512 (P : int -> Prop) : (term2 P) = (term2 P).
Proof. exact (eq_refl (term2 P)). Qed.
Lemma lem3116513 (P : int -> Prop) : ((term1 P) = (term2 P)) = ((term2 P) = (term2 P)).
Proof. exact (MK_COMB (@lem3116503 P) (@lem3116512 P)). Qed.
Lemma lem3116515 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3116516 (x : Prop) : (x = x) = True.
Proof. exact (@lem3116515 Prop x). Qed.
Lemma lem3116517 (P : int -> Prop) : ((term2 P) = (term2 P)) = True.
Proof. exact (@lem3116516 (term2 P)). Qed.
Lemma lem3116518 (P : int -> Prop) : ((term1 P) = (term2 P)) = True.
Proof. exact (TRANS (@lem3116513 P) (@lem3116517 P)). Qed.
Lemma lem3116519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3116520 (P : int -> Prop) : (term24 P) = (and True).
Proof. exact (MK_COMB (@lem3116519) (@lem3116518 P)). Qed.
Lemma lem3116524 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (EQ_MP (@lem3116366 A P) (@lem3116365 A P)). Qed.
Lemma lem3116525 (P : nat -> Prop) : (term29 P) = (term30 P).
Proof. exact (@lem3116524 nat P). Qed.
Lemma lem3116526 (P : int -> Prop) : (term31 P) = (term32 P).
Proof. exact (@lem3116525 (term33 P)). Qed.
Lemma lem3116527 (P : int -> Prop) (n : nat) : (term34 P n) = (term35 P n).
Proof. exact (eq_refl (term34 P n)). Qed.
Lemma lem3116528 (P : int -> Prop) : (term36 P) = (term33 P).
Proof. exact (fun_ext (fun n : nat => @lem3116527 P n)). Qed.
Lemma lem3116529 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3116530 (P : int -> Prop) : (term37 P) = (term20 P).
Proof. exact (MK_COMB (@lem3116529) (@lem3116528 P)). Qed.
Lemma lem3116531 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3116532 (P : int -> Prop) : (term31 P) = (term22 P).
Proof. exact (MK_COMB (@lem3116531) (@lem3116530 P)). Qed.
Lemma lem3116533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116534 (P : int -> Prop) : (term38 P) = (term39 P).
Proof. exact (MK_COMB (@lem3116533) (@lem3116532 P)). Qed.
Lemma lem3116535 (P : int -> Prop) (n : nat) : (term34 P n) = (term35 P n).
Proof. exact (eq_refl (term34 P n)). Qed.
Lemma lem3116536 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3116537 (P : int -> Prop) (n : nat) : (term40 P n) = (term41 P n).
Proof. exact (MK_COMB (@lem3116536) (@lem3116535 P n)). Qed.
Lemma lem3116538 (P : int -> Prop) : (term42 P) = (term43 P).
Proof. exact (fun_ext (fun n : nat => @lem3116537 P n)). Qed.
Lemma lem3116539 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3116540 (P : int -> Prop) : (term32 P) = (term44 P).
Proof. exact (MK_COMB (@lem3116539) (@lem3116538 P)). Qed.
Lemma lem3116541 (P : int -> Prop) : ((term31 P) = (term32 P)) = ((term22 P) = (term44 P)).
Proof. exact (MK_COMB (@lem3116534 P) (@lem3116540 P)). Qed.
Lemma lem3116542 (P : int -> Prop) : (term22 P) = (term44 P).
Proof. exact (EQ_MP (@lem3116541 P) (@lem3116526 P)). Qed.
Lemma lem3116548 (P : int -> Prop) : (term1 P) = (term2 P).
Proof. exact (EQ_MP (@lem3116363 P) (@lem3116362 P)). Qed.
Lemma lem3116549 (P : int -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem3116548 (term47 P)). Qed.
Lemma lem3116550 (P : int -> Prop) (n : nat) : (term48 P n) = (term41 P n).
Proof. exact (eq_refl (term48 P n)). Qed.
Lemma lem3116551 (P : int -> Prop) : (term49 P) = (term43 P).
Proof. exact (fun_ext (fun n : nat => @lem3116550 P n)). Qed.
Lemma lem3116552 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3116553 (P : int -> Prop) : (term45 P) = (term44 P).
Proof. exact (MK_COMB (@lem3116552) (@lem3116551 P)). Qed.
Lemma lem3116554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116555 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (MK_COMB (@lem3116554) (@lem3116553 P)). Qed.
Lemma lem3116556 (P : int -> Prop) (i : int) : (term52 P i) = (term53 P i).
Proof. exact (eq_refl (term52 P i)). Qed.
Lemma lem3116557 (i : int) : (term54 i) = (term54 i).
Proof. exact (eq_refl (term54 i)). Qed.
Lemma lem3116558 (P : int -> Prop) (i : int) : (term55 P i) = (term56 P i).
Proof. exact (MK_COMB (@lem3116557 i) (@lem3116556 P i)). Qed.
Lemma lem3116559 (P : int -> Prop) : (term57 P) = (term58 P).
Proof. exact (fun_ext (fun i : int => @lem3116558 P i)). Qed.
Lemma lem3116560 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3116561 (P : int -> Prop) : (term46 P) = (term59 P).
Proof. exact (MK_COMB (@lem3116560) (@lem3116559 P)). Qed.
Lemma lem3116562 (P : int -> Prop) : ((term45 P) = (term46 P)) = ((term44 P) = (term59 P)).
Proof. exact (MK_COMB (@lem3116555 P) (@lem3116561 P)). Qed.
Lemma lem3116563 (P : int -> Prop) : (term44 P) = (term59 P).
Proof. exact (EQ_MP (@lem3116562 P) (@lem3116549 P)). Qed.
Lemma lem3116570 (P : int -> Prop) : (term22 P) = (term59 P).
Proof. exact (TRANS (@lem3116542 P) (@lem3116563 P)). Qed.
Lemma lem3116573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116574 (P : int -> Prop) : (term39 P) = (term60 P).
Proof. exact (MK_COMB (@lem3116573) (@lem3116570 P)). Qed.
Lemma lem3116576 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (EQ_MP (@lem3116366 A P) (@lem3116365 A P)). Qed.
Lemma lem3116577 (P : int -> Prop) : (term61 P) = (term62 P).
Proof. exact (@lem3116576 int P). Qed.
Lemma lem3116578 (P : int -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem3116577 (term65 P)). Qed.
Lemma lem3116579 (P : int -> Prop) (i : int) : (term66 P i) = (term67 P i).
Proof. exact (eq_refl (term66 P i)). Qed.
Lemma lem3116580 (P : int -> Prop) : (term68 P) = (term65 P).
Proof. exact (fun_ext (fun i : int => @lem3116579 P i)). Qed.
Lemma lem3116581 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3116582 (P : int -> Prop) : (term69 P) = (term21 P).
Proof. exact (MK_COMB (@lem3116581) (@lem3116580 P)). Qed.
Lemma lem3116583 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3116584 (P : int -> Prop) : (term63 P) = (term23 P).
Proof. exact (MK_COMB (@lem3116583) (@lem3116582 P)). Qed.
Lemma lem3116585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116586 (P : int -> Prop) : (term70 P) = (term71 P).
Proof. exact (MK_COMB (@lem3116585) (@lem3116584 P)). Qed.
Lemma lem3116587 (P : int -> Prop) (i : int) : (term66 P i) = (term67 P i).
Proof. exact (eq_refl (term66 P i)). Qed.
Lemma lem3116588 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3116589 (P : int -> Prop) (i : int) : (term72 P i) = (term73 P i).
Proof. exact (MK_COMB (@lem3116588) (@lem3116587 P i)). Qed.
Lemma lem3116590 (P : int -> Prop) : (term74 P) = (term75 P).
Proof. exact (fun_ext (fun i : int => @lem3116589 P i)). Qed.
Lemma lem3116591 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3116592 (P : int -> Prop) : (term64 P) = (term76 P).
Proof. exact (MK_COMB (@lem3116591) (@lem3116590 P)). Qed.
Lemma lem3116593 (P : int -> Prop) : ((term63 P) = (term64 P)) = ((term23 P) = (term76 P)).
Proof. exact (MK_COMB (@lem3116586 P) (@lem3116592 P)). Qed.
Lemma lem3116594 (P : int -> Prop) : (term23 P) = (term76 P).
Proof. exact (EQ_MP (@lem3116593 P) (@lem3116578 P)). Qed.
Lemma lem3116603 (P : int -> Prop) : ((term22 P) = (term23 P)) = ((term59 P) = (term76 P)).
Proof. exact (MK_COMB (@lem3116574 P) (@lem3116594 P)). Qed.
Lemma lem3116606 (P : int -> Prop) : (term26 P) = (term77 P).
Proof. exact (MK_COMB (@lem3116520 P) (@lem3116603 P)). Qed.
Lemma lem3116608 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3116609 (P : int -> Prop) : (term77 P) = ((term59 P) = (term76 P)).
Proof. exact (@lem3116608 ((term59 P) = (term76 P))). Qed.
Lemma lem3116628 (P : int -> Prop) : (term26 P) = ((term59 P) = (term76 P)).
Proof. exact (TRANS (@lem3116606 P) (@lem3116609 P)). Qed.
Lemma lem3116629 (P : int -> Prop) : ((term59 P) = (term76 P)) = (term26 P).
Proof. exact (SYM (@lem3116628 P)). Qed.
Lemma lem3116631 (p : Prop) : p = (term78 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3116632 (P : int -> Prop) : ((term59 P) = (term76 P)) = (term79 P).
Proof. exact (@lem3116631 ((term59 P) = (term76 P))). Qed.
Lemma lem3116633 (P : int -> Prop) : (term79 P) = ((term59 P) = (term76 P)).
Proof. exact (SYM (@lem3116632 P)). Qed.
Lemma lem3116634 (P : int -> Prop) (h1 : term80 P) : term80 P.
Proof. exact (h1). Qed.
Lemma lem3116637 (P : int -> Prop) (h1 : term79 P) : term79 P.
Proof. exact (h1). Qed.
Lemma lem3116638 (P : int -> Prop) : term81 P.
Proof. exact (fun h0 : term79 P => @lem3116637 P h0). Qed.
Lemma lem3116639 (P : int -> Prop) (h1 : term81 P) : term81 P.
Proof. exact (h1). Qed.
Lemma lem3116640 (P : int -> Prop) (h1 : term79 P) : term79 P.
Proof. exact (h1). Qed.
Lemma lem3116641 (P : int -> Prop) (h1 : term79 P) (h2 : term81 P) : term79 P.
Proof. exact (@lem3116639 P h2 (@lem3116640 P h1)). Qed.
Lemma lem3116642 (P : int -> Prop) (h1 : term79 P) : term82 P.
Proof. exact (fun h0 : term81 P => @lem3116641 P h1 h0). Qed.
Lemma lem3116643 (P : int -> Prop) (h1 : term81 P) : term81 P.
Proof. exact (h1). Qed.
Lemma lem3116644 (P : int -> Prop) (h1 : term79 P) (h2 : term81 P) : term79 P.
Proof. exact (@lem3116642 P h1 (@lem3116643 P h2)). Qed.
Lemma lem3116645 (P : int -> Prop) (h1 : term81 P) : term81 P.
Proof. exact (fun h0 : term79 P => @lem3116644 P h0 h1). Qed.
Lemma lem3116646 (P : int -> Prop) : term83 P.
Proof. exact (fun h0 : term81 P => @lem3116645 P h0). Qed.
Lemma lem3116649 (P : int -> Prop) : term81 P.
Proof. exact (@lem3116646 P (@lem3116638 P)). Qed.
Lemma lem3116655 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3116656 (P : int -> Prop) : (term79 P) = (term84 P).
Proof. exact (@lem3116655 (term80 P)). Qed.
Lemma lem3116658 (t : Prop) : (term16 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3116659 (P : int -> Prop) : (term84 P) = ((term59 P) = (term76 P)).
Proof. exact (@lem3116658 ((term59 P) = (term76 P))). Qed.
Lemma lem3116660 (P : int -> Prop) : (term79 P) = ((term59 P) = (term76 P)).
Proof. exact (TRANS (@lem3116656 P) (@lem3116659 P)). Qed.
Lemma lem3116673 : term85 = term86.
Proof. exact (fun_ext (fun P : int -> Prop => @lem3116660 P)). Qed.
Lemma lem3116674 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem3116683 : term87 = term88.
Proof. exact (MK_COMB (@lem3116674) (@lem3116673)). Qed.
Lemma lem3116690 (P : int -> Prop) (i : int) : (term73 P i) = (term73 P i).
Proof. exact (eq_refl (term73 P i)). Qed.
Lemma lem3116691 (P : int -> Prop) : (term75 P) = (term75 P).
Proof. exact (fun_ext (fun i : int => @lem3116690 P i)). Qed.
Lemma lem3116692 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3116693 (P : int -> Prop) : (term76 P) = (term76 P).
Proof. exact (MK_COMB (@lem3116692) (@lem3116691 P)). Qed.
Lemma lem3116700 (P : int -> Prop) (i : int) : (term56 P i) = (term56 P i).
Proof. exact (eq_refl (term56 P i)). Qed.
Lemma lem3116701 (P : int -> Prop) : (term58 P) = (term58 P).
Proof. exact (fun_ext (fun i : int => @lem3116700 P i)). Qed.
Lemma lem3116702 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3116703 (P : int -> Prop) : (term59 P) = (term59 P).
Proof. exact (MK_COMB (@lem3116702) (@lem3116701 P)). Qed.
Lemma lem3116704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116705 (P : int -> Prop) : (term60 P) = (term60 P).
Proof. exact (MK_COMB (@lem3116704) (@lem3116703 P)). Qed.
Lemma lem3116706 (P : int -> Prop) : ((term59 P) = (term76 P)) = ((term59 P) = (term76 P)).
Proof. exact (MK_COMB (@lem3116705 P) (@lem3116693 P)). Qed.
Lemma lem3116707 : term86 = term86.
Proof. exact (fun_ext (fun P : int -> Prop => @lem3116706 P)). Qed.
Lemma lem3116708 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem3116709 : term88 = term88.
Proof. exact (MK_COMB (@lem3116708) (@lem3116707)). Qed.
Lemma lem3116734 : term87 = term88.
Proof. exact (TRANS (@lem3116683) (@lem3116709)). Qed.
Lemma lem3116735 : term88 = term87.
Proof. exact (SYM (@lem3116734)). Qed.
Lemma lem3116737 (p : Prop) : p = (term78 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3116738 (P : int -> Prop) : ((term59 P) = (term76 P)) = (term79 P).
Proof. exact (@lem3116737 ((term59 P) = (term76 P))). Qed.
Lemma lem3116739 (P : int -> Prop) : (term79 P) = ((term59 P) = (term76 P)).
Proof. exact (SYM (@lem3116738 P)). Qed.
Lemma lem3116740 (P : int -> Prop) (h1 : term80 P) : term80 P.
Proof. exact (h1). Qed.
Lemma lem3116746 (P : int -> Prop) (i : int) : (term89 P i) = (P i).
Proof. exact (@lem16933 (P i)). Qed.
Lemma lem3116748 (i : int) : (term90 i) = (term90 i).
Proof. exact (eq_refl (term90 i)). Qed.
Lemma lem3116749 (P : int -> Prop) (i : int) : (term91 P i) = (term67 P i).
Proof. exact (MK_COMB (@lem3116748 i) (@lem3116746 P i)). Qed.
Lemma lem3116750 (P : int -> Prop) (i : int) : (term92 P i) = (term91 P i).
Proof. exact (@lem17362 (term93 i) (term53 P i)). Qed.
Lemma lem3116751 (P : int -> Prop) (i : int) : (term92 P i) = (term67 P i).
Proof. exact (TRANS (@lem3116750 P i) (@lem3116749 P i)). Qed.
Lemma lem3116756 (P : int -> Prop) (i : int) : (term56 P i) = (term94 P i).
Proof. exact (@lem17265 (term93 i) (term53 P i)). Qed.
Lemma lem3116757 (P : int -> Prop) : (term95 P) = (term96 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3116758 (P : int -> Prop) : (term97 P) = (term98 P).
Proof. exact (@lem3116757 (term58 P)). Qed.
Lemma lem3116759 (P : int -> Prop) (i : int) : (term99 P i) = (term56 P i).
Proof. exact (eq_refl (term99 P i)). Qed.
Lemma lem3116760 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3116761 (P : int -> Prop) (i : int) : (term100 P i) = (term92 P i).
Proof. exact (MK_COMB (@lem3116760) (@lem3116759 P i)). Qed.
Lemma lem3116762 (P : int -> Prop) (i : int) : (term100 P i) = (term67 P i).
Proof. exact (TRANS (@lem3116761 P i) (@lem3116751 P i)). Qed.
Lemma lem3116763 (P : int -> Prop) : (term101 P) = (term65 P).
Proof. exact (fun_ext (fun i : int => @lem3116762 P i)). Qed.
Lemma lem3116764 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3116765 (P : int -> Prop) : (term98 P) = (term21 P).
Proof. exact (MK_COMB (@lem3116764) (@lem3116763 P)). Qed.
Lemma lem3116766 (P : int -> Prop) : (term97 P) = (term21 P).
Proof. exact (TRANS (@lem3116758 P) (@lem3116765 P)). Qed.
Lemma lem3116767 (P : int -> Prop) : (term58 P) = (term102 P).
Proof. exact (fun_ext (fun i : int => @lem3116756 P i)). Qed.
Lemma lem3116768 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3116769 (P : int -> Prop) : (term59 P) = (term103 P).
Proof. exact (MK_COMB (@lem3116768) (@lem3116767 P)). Qed.
Lemma lem3116778 (P : int -> Prop) (i : int) : (term73 P i) = (term94 P i).
Proof. exact (@lem17045 (term93 i) (P i)). Qed.
Lemma lem3116783 (P : int -> Prop) (i : int) : (term104 P i) = (term67 P i).
Proof. exact (@lem16933 (term67 P i)). Qed.
Lemma lem3116784 (P : int -> Prop) : (term95 P) = (term96 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3116785 (P : int -> Prop) : (term105 P) = (term106 P).
Proof. exact (@lem3116784 (term75 P)). Qed.
Lemma lem3116786 (P : int -> Prop) (i : int) : (term107 P i) = (term73 P i).
Proof. exact (eq_refl (term107 P i)). Qed.
Lemma lem3116787 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3116788 (P : int -> Prop) (i : int) : (term108 P i) = (term104 P i).
Proof. exact (MK_COMB (@lem3116787) (@lem3116786 P i)). Qed.
Lemma lem3116789 (P : int -> Prop) (i : int) : (term108 P i) = (term67 P i).
Proof. exact (TRANS (@lem3116788 P i) (@lem3116783 P i)). Qed.
Lemma lem3116790 (P : int -> Prop) : (term109 P) = (term65 P).
Proof. exact (fun_ext (fun i : int => @lem3116789 P i)). Qed.
Lemma lem3116791 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3116792 (P : int -> Prop) : (term106 P) = (term21 P).
Proof. exact (MK_COMB (@lem3116791) (@lem3116790 P)). Qed.
Lemma lem3116793 (P : int -> Prop) : (term105 P) = (term21 P).
Proof. exact (TRANS (@lem3116785 P) (@lem3116792 P)). Qed.
Lemma lem3116794 (P : int -> Prop) : (term75 P) = (term102 P).
Proof. exact (fun_ext (fun i : int => @lem3116778 P i)). Qed.
Lemma lem3116795 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3116796 (P : int -> Prop) : (term76 P) = (term103 P).
Proof. exact (MK_COMB (@lem3116795) (@lem3116794 P)). Qed.
Lemma lem3116797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3116798 (P : int -> Prop) : (term110 P) = (term111 P).
Proof. exact (MK_COMB (@lem3116797) (@lem3116766 P)). Qed.
Lemma lem3116799 (P : int -> Prop) : (term112 P) = (term113 P).
Proof. exact (MK_COMB (@lem3116798 P) (@lem3116796 P)). Qed.
Lemma lem3116800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3116801 (P : int -> Prop) : (term114 P) = (term115 P).
Proof. exact (MK_COMB (@lem3116800) (@lem3116769 P)). Qed.
Lemma lem3116802 (P : int -> Prop) : (term116 P) = (term117 P).
Proof. exact (MK_COMB (@lem3116801 P) (@lem3116793 P)). Qed.
Lemma lem3116803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3116804 (P : int -> Prop) : (term118 P) = (term119 P).
Proof. exact (MK_COMB (@lem3116803) (@lem3116802 P)). Qed.
Lemma lem3116805 (P : int -> Prop) : (term120 P) = (term121 P).
Proof. exact (MK_COMB (@lem3116804 P) (@lem3116799 P)). Qed.
Lemma lem3116806 (P : int -> Prop) : (term80 P) = (term120 P).
Proof. exact (@lem17646 (term59 P) (term76 P)). Qed.
Lemma lem3116807 (P : int -> Prop) : (term80 P) = (term121 P).
Proof. exact (TRANS (@lem3116806 P) (@lem3116805 P)). Qed.
Lemma lem3116970 {A : Type'} (P : Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3116971 (P : Prop) (Q : int -> Prop) : (term124 P Q) = (term125 P Q).
Proof. exact (@lem3116970 int P Q). Qed.
Lemma lem3116972 (P : int -> Prop) : (term126 P) = (term127 P).
Proof. exact (@lem3116971 (term103 P) (term65 P)). Qed.
Lemma lem3116973 (P : int -> Prop) (i : int) : (term66 P i) = (term67 P i).
Proof. exact (eq_refl (term66 P i)). Qed.
Lemma lem3116974 (P : int -> Prop) : (term68 P) = (term65 P).
Proof. exact (fun_ext (fun i : int => @lem3116973 P i)). Qed.
Lemma lem3116975 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3116976 (P : int -> Prop) : (term69 P) = (term21 P).
Proof. exact (MK_COMB (@lem3116975) (@lem3116974 P)). Qed.
Lemma lem3116977 (P : int -> Prop) : (term115 P) = (term115 P).
Proof. exact (eq_refl (term115 P)). Qed.
Lemma lem3116978 (P : int -> Prop) : (term126 P) = (term117 P).
Proof. exact (MK_COMB (@lem3116977 P) (@lem3116976 P)). Qed.
Lemma lem3116979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3116980 (P : int -> Prop) : (term128 P) = (term129 P).
Proof. exact (MK_COMB (@lem3116979) (@lem3116978 P)). Qed.
Lemma lem3116981 (P : int -> Prop) (i : int) : (term66 P i) = (term67 P i).
Proof. exact (eq_refl (term66 P i)). Qed.
Lemma lem3116982 (P : int -> Prop) : (term115 P) = (term115 P).
Proof. exact (eq_refl (term115 P)). Qed.
Lemma lem3116983 (P : int -> Prop) (i : int) : (term130 P i) = (term131 P i).
Proof. exact (MK_COMB (@lem3116982 P) (@lem3116981 P i)). Qed.
Lemma lem3116984 (P : int -> Prop) : (term132 P) = (term133 P).
Proof. exact (fun_ext (fun i : int => @lem3116983 P i)). Qed.
Lemma lem3116985 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3116986 (P : int -> Prop) : (term127 P) = (term134 P).
Proof. exact (MK_COMB (@lem3116985) (@lem3116984 P)). Qed.
Lemma lem3116987 (P : int -> Prop) : ((term126 P) = (term127 P)) = ((term117 P) = (term134 P)).
Proof. exact (MK_COMB (@lem3116980 P) (@lem3116986 P)). Qed.
Lemma lem3116988 (P : int -> Prop) : (term117 P) = (term134 P).
Proof. exact (EQ_MP (@lem3116987 P) (@lem3116972 P)). Qed.
Lemma lem3116989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3116990 (P : int -> Prop) : (term119 P) = (term135 P).
Proof. exact (MK_COMB (@lem3116989) (@lem3116988 P)). Qed.
Lemma lem3116992 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3116993 (P : int -> Prop) (Q : Prop) : (term138 P Q) = (term139 P Q).
Proof. exact (@lem3116992 int P Q). Qed.
Lemma lem3116994 (P : int -> Prop) : (term140 P) = (term141 P).
Proof. exact (@lem3116993 (term65 P) (term103 P)). Qed.
Lemma lem3116995 (P : int -> Prop) (i : int) : (term66 P i) = (term67 P i).
Proof. exact (eq_refl (term66 P i)). Qed.
Lemma lem3116996 (P : int -> Prop) : (term68 P) = (term65 P).
Proof. exact (fun_ext (fun i : int => @lem3116995 P i)). Qed.
Lemma lem3116997 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3116998 (P : int -> Prop) : (term69 P) = (term21 P).
Proof. exact (MK_COMB (@lem3116997) (@lem3116996 P)). Qed.
Lemma lem3116999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3117000 (P : int -> Prop) : (term142 P) = (term111 P).
Proof. exact (MK_COMB (@lem3116999) (@lem3116998 P)). Qed.
Lemma lem3117001 (P : int -> Prop) : (term103 P) = (term103 P).
Proof. exact (eq_refl (term103 P)). Qed.
Lemma lem3117002 (P : int -> Prop) : (term140 P) = (term113 P).
Proof. exact (MK_COMB (@lem3117000 P) (@lem3117001 P)). Qed.
Lemma lem3117003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3117004 (P : int -> Prop) : (term143 P) = (term144 P).
Proof. exact (MK_COMB (@lem3117003) (@lem3117002 P)). Qed.
Lemma lem3117005 (P : int -> Prop) (i : int) : (term66 P i) = (term67 P i).
Proof. exact (eq_refl (term66 P i)). Qed.
Lemma lem3117006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3117007 (P : int -> Prop) (i : int) : (term145 P i) = (term146 P i).
Proof. exact (MK_COMB (@lem3117006) (@lem3117005 P i)). Qed.
Lemma lem3117008 (P : int -> Prop) : (term103 P) = (term103 P).
Proof. exact (eq_refl (term103 P)). Qed.
Lemma lem3117009 (i : int) (P : int -> Prop) : (term147 i P) = (term148 i P).
Proof. exact (MK_COMB (@lem3117007 P i) (@lem3117008 P)). Qed.
Lemma lem3117010 (P : int -> Prop) : (term149 P) = (term150 P).
Proof. exact (fun_ext (fun i : int => @lem3117009 i P)). Qed.
Lemma lem3117011 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3117012 (P : int -> Prop) : (term141 P) = (term151 P).
Proof. exact (MK_COMB (@lem3117011) (@lem3117010 P)). Qed.
Lemma lem3117013 (P : int -> Prop) : ((term140 P) = (term141 P)) = ((term113 P) = (term151 P)).
Proof. exact (MK_COMB (@lem3117004 P) (@lem3117012 P)). Qed.
Lemma lem3117014 (P : int -> Prop) : (term113 P) = (term151 P).
Proof. exact (EQ_MP (@lem3117013 P) (@lem3116994 P)). Qed.
Lemma lem3117015 (P : int -> Prop) : (term121 P) = (term152 P).
Proof. exact (MK_COMB (@lem3116990 P) (@lem3117014 P)). Qed.
Lemma lem3117017 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term153 A P Q) = (term154 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3117018 (P : int -> Prop) (Q : int -> Prop) : (term155 P Q) = (term156 P Q).
Proof. exact (@lem3117017 int P Q). Qed.
Lemma lem3117019 (P : int -> Prop) : (term157 P) = (term158 P).
Proof. exact (@lem3117018 (term133 P) (term150 P)). Qed.
Lemma lem3117020 (P : int -> Prop) (i : int) : (term159 P i) = (term131 P i).
Proof. exact (eq_refl (term159 P i)). Qed.
Lemma lem3117021 (P : int -> Prop) : (term160 P) = (term133 P).
Proof. exact (fun_ext (fun i : int => @lem3117020 P i)). Qed.
Lemma lem3117022 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3117023 (P : int -> Prop) : (term161 P) = (term134 P).
Proof. exact (MK_COMB (@lem3117022) (@lem3117021 P)). Qed.
Lemma lem3117024 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3117025 (P : int -> Prop) : (term162 P) = (term135 P).
Proof. exact (MK_COMB (@lem3117024) (@lem3117023 P)). Qed.
Lemma lem3117026 (i : int) (P : int -> Prop) : (term163 P i) = (term148 i P).
Proof. exact (eq_refl (term163 P i)). Qed.
Lemma lem3117027 (P : int -> Prop) : (term164 P) = (term150 P).
Proof. exact (fun_ext (fun i : int => @lem3117026 i P)). Qed.
Lemma lem3117028 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3117029 (P : int -> Prop) : (term165 P) = (term151 P).
Proof. exact (MK_COMB (@lem3117028) (@lem3117027 P)). Qed.
Lemma lem3117030 (P : int -> Prop) : (term157 P) = (term152 P).
Proof. exact (MK_COMB (@lem3117025 P) (@lem3117029 P)). Qed.
Lemma lem3117031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3117032 (P : int -> Prop) : (term166 P) = (term167 P).
Proof. exact (MK_COMB (@lem3117031) (@lem3117030 P)). Qed.
Lemma lem3117033 (P : int -> Prop) (i : int) : (term159 P i) = (term131 P i).
Proof. exact (eq_refl (term159 P i)). Qed.
Lemma lem3117034 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3117035 (P : int -> Prop) (i : int) : (term168 P i) = (term169 P i).
Proof. exact (MK_COMB (@lem3117034) (@lem3117033 P i)). Qed.
Lemma lem3117036 (i : int) (P : int -> Prop) : (term163 P i) = (term148 i P).
Proof. exact (eq_refl (term163 P i)). Qed.
Lemma lem3117037 (i : int) (P : int -> Prop) : (term170 P i) = (term171 i P).
Proof. exact (MK_COMB (@lem3117035 P i) (@lem3117036 i P)). Qed.
Lemma lem3117038 (P : int -> Prop) : (term172 P) = (term173 P).
Proof. exact (fun_ext (fun i : int => @lem3117037 i P)). Qed.
Lemma lem3117039 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3117040 (P : int -> Prop) : (term158 P) = (term174 P).
Proof. exact (MK_COMB (@lem3117039) (@lem3117038 P)). Qed.
Lemma lem3117041 (P : int -> Prop) : ((term157 P) = (term158 P)) = ((term152 P) = (term174 P)).
Proof. exact (MK_COMB (@lem3117032 P) (@lem3117040 P)). Qed.
Lemma lem3117042 (P : int -> Prop) : (term152 P) = (term174 P).
Proof. exact (EQ_MP (@lem3117041 P) (@lem3117019 P)). Qed.
Lemma lem3117044 (P : int -> Prop) : (term121 P) = (term174 P).
Proof. exact (TRANS (@lem3117015 P) (@lem3117042 P)). Qed.
Lemma lem3117045 (P : int -> Prop) : (term80 P) = (term174 P).
Proof. exact (TRANS (@lem3116807 P) (@lem3117044 P)). Qed.
Lemma lem3117046 (P : int -> Prop) (h1 : term80 P) : term174 P.
Proof. exact (EQ_MP (@lem3117045 P) (@lem3116740 P h1)). Qed.
Lemma lem3117047 (i : int) (P : int -> Prop) (h1 : term171 i P) : term171 i P.
Proof. exact (h1). Qed.
Lemma lem3117066 (P : int -> Prop) (i : int) : (term94 P i) = (term94 P i).
Proof. exact (eq_refl (term94 P i)). Qed.
Lemma lem3117067 (P : int -> Prop) : (term102 P) = (term102 P).
Proof. exact (fun_ext (fun i : int => @lem3117066 P i)). Qed.
Lemma lem3117068 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3117069 (P : int -> Prop) : (term103 P) = (term103 P).
Proof. exact (MK_COMB (@lem3117068) (@lem3117067 P)). Qed.
Lemma lem3117086 (P : int -> Prop) (i : int) : (term146 P i) = (term146 P i).
Proof. exact (eq_refl (term146 P i)). Qed.
Lemma lem3117087 (i : int) (P : int -> Prop) : (term148 i P) = (term148 i P).
Proof. exact (MK_COMB (@lem3117086 P i) (@lem3117069 P)). Qed.
Lemma lem3117102 (P : int -> Prop) (i : int) : (term67 P i) = (term67 P i).
Proof. exact (eq_refl (term67 P i)). Qed.
Lemma lem3117121 (P : int -> Prop) (i : int) : (term94 P i) = (term94 P i).
Proof. exact (eq_refl (term94 P i)). Qed.
Lemma lem3117122 (P : int -> Prop) : (term102 P) = (term102 P).
Proof. exact (fun_ext (fun i : int => @lem3117121 P i)). Qed.
Lemma lem3117123 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3117124 (P : int -> Prop) : (term103 P) = (term103 P).
Proof. exact (MK_COMB (@lem3117123) (@lem3117122 P)). Qed.
Lemma lem3117125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3117126 (P : int -> Prop) : (term115 P) = (term115 P).
Proof. exact (MK_COMB (@lem3117125) (@lem3117124 P)). Qed.
Lemma lem3117127 (P : int -> Prop) (i : int) : (term131 P i) = (term131 P i).
Proof. exact (MK_COMB (@lem3117126 P) (@lem3117102 P i)). Qed.
Lemma lem3117128 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3117129 (P : int -> Prop) (i : int) : (term169 P i) = (term169 P i).
Proof. exact (MK_COMB (@lem3117128) (@lem3117127 P i)). Qed.
Lemma lem3117130 (i : int) (P : int -> Prop) : (term171 i P) = (term171 i P).
Proof. exact (MK_COMB (@lem3117129 P i) (@lem3117087 i P)). Qed.
Lemma lem3117131 (i : int) (P : int -> Prop) (h1 : term171 i P) : term171 i P.
Proof. exact (EQ_MP (@lem3117130 i P) (@lem3117047 i P h1)). Qed.
Lemma lem3117132 (P : int -> Prop) (i : int) (h1 : term131 P i) : term131 P i.
Proof. exact (h1). Qed.
Lemma lem3117133 (i : int) (P : int -> Prop) (h1 : term148 i P) : term148 i P.
Proof. exact (h1). Qed.
Lemma lem3117134 (P : int -> Prop) (i : int) (h1 : term131 P i) : term67 P i.
Proof. exact (proj2 (@lem3117132 P i h1)). Qed.
Lemma lem3117135 (P : int -> Prop) (i : int) (h1 : term131 P i) : term103 P.
Proof. exact (proj1 (@lem3117132 P i h1)). Qed.
Lemma lem3117138 (i : int) (P : int -> Prop) (h1 : term148 i P) : term103 P.
Proof. exact (proj2 (@lem3117133 i P h1)). Qed.
Lemma lem3117139 (i : int) (P : int -> Prop) (h1 : term148 i P) : term67 P i.
Proof. exact (proj1 (@lem3117133 i P h1)). Qed.
Lemma lem3117149 (P : int -> Prop) (i : int) : (term94 P i) = (term94 P i).
Proof. exact (eq_refl (term94 P i)). Qed.
Lemma lem3117150 (P : int -> Prop) : (term102 P) = (term102 P).
Proof. exact (fun_ext (fun i : int => @lem3117149 P i)). Qed.
Lemma lem3117151 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3117153 (P : int -> Prop) : (term103 P) = (term103 P).
Proof. exact (MK_COMB (@lem3117151) (@lem3117150 P)). Qed.
Lemma lem3117154 (P : int -> Prop) (i : int) (h1 : term131 P i) : term103 P.
Proof. exact (EQ_MP (@lem3117153 P) (@lem3117135 P i h1)). Qed.
Lemma lem3117170 (P : int -> Prop) (i : int) : (term94 P i) = (term94 P i).
Proof. exact (eq_refl (term94 P i)). Qed.
Lemma lem3117171 (P : int -> Prop) : (term102 P) = (term102 P).
Proof. exact (fun_ext (fun i : int => @lem3117170 P i)). Qed.
Lemma lem3117172 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3117174 (P : int -> Prop) : (term103 P) = (term103 P).
Proof. exact (MK_COMB (@lem3117172) (@lem3117171 P)). Qed.
Lemma lem3117175 (i : int) (P : int -> Prop) (h1 : term148 i P) : term103 P.
Proof. exact (EQ_MP (@lem3117174 P) (@lem3117138 i P h1)). Qed.
Lemma lem3117184 (_32371 : int) (P : int -> Prop) (i : int) (h1 : term131 P i) : term175 P _32371.
Proof. exact (@lem3117154 P i h1 _32371). Qed.
Lemma lem3117185 (P : int -> Prop) (_32371 : int) : (term175 P _32371) = (term94 P _32371).
Proof. exact (eq_refl (term175 P _32371)). Qed.
Lemma lem3117187 (_32372 : int) (i : int) (P : int -> Prop) (h1 : term148 i P) : term175 P _32372.
Proof. exact (@lem3117175 i P h1 _32372). Qed.
Lemma lem3117188 (P : int -> Prop) (_32372 : int) : (term175 P _32372) = (term94 P _32372).
Proof. exact (eq_refl (term175 P _32372)). Qed.
Lemma lem3117195 (_32371 : int) (P : int -> Prop) (i : int) (h1 : term131 P i) : term94 P _32371.
Proof. exact (EQ_MP (@lem3117185 P _32371) (@lem3117184 _32371 P i h1)). Qed.
Lemma lem3117205 (_32372 : int) (i : int) (P : int -> Prop) (h1 : term148 i P) : term94 P _32372.
Proof. exact (EQ_MP (@lem3117188 P _32372) (@lem3117187 _32372 i P h1)). Qed.
Lemma lem3117211 (P : int -> Prop) (i : int) (h1 : term131 P i) : term93 i.
Proof. exact (proj1 (@lem3117134 P i h1)). Qed.
Lemma lem3117212 (P : int -> Prop) (i : int) (h1 : term131 P i) : term176 i.
Proof. exact (fun h0 : term177 i => @lem3117211 P i h1). Qed.
Lemma lem3117214 (p : Prop) : (term178 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3117215 (i : int) : (term176 i) = (term93 i).
Proof. exact (@lem3117214 (term93 i)). Qed.
Lemma lem3117216 (P : int -> Prop) (i : int) (h1 : term131 P i) : term93 i.
Proof. exact (EQ_MP (@lem3117215 i) (@lem3117212 P i h1)). Qed.
Lemma lem3117218 (P : int -> Prop) (i : int) (h1 : term131 P i) : P i.
Proof. exact (proj2 (@lem3117134 P i h1)). Qed.
Lemma lem3117219 (P : int -> Prop) (i : int) (h1 : term131 P i) : term179 P i.
Proof. exact (fun h0 : term53 P i => @lem3117218 P i h1). Qed.
Lemma lem3117221 (p : Prop) : (term178 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3117222 (P : int -> Prop) (i : int) : (term179 P i) = (P i).
Proof. exact (@lem3117221 (P i)). Qed.
Lemma lem3117223 (P : int -> Prop) (i : int) (h1 : term131 P i) : P i.
Proof. exact (EQ_MP (@lem3117222 P i) (@lem3117219 P i h1)). Qed.
Lemma lem3117225 (a : Prop) (b : Prop) : (term180 a b) = (term181 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3117226 (P : int -> Prop) (_32371 : int) : (term94 P _32371) = (term73 P _32371).
Proof. exact (@lem3117225 (term93 _32371) (P _32371)). Qed.
Lemma lem3117228 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3117229 (P : int -> Prop) (_32371 : int) : (term73 P _32371) = (term182 P _32371).
Proof. exact (@lem3117228 (term67 P _32371)). Qed.
Lemma lem3117230 (P : int -> Prop) (_32371 : int) : (term94 P _32371) = (term182 P _32371).
Proof. exact (TRANS (@lem3117226 P _32371) (@lem3117229 P _32371)). Qed.
Lemma lem3117232 (P : int -> Prop) (i : int) (h1 : term131 P i) : term67 P i.
Proof. exact (conj (@lem3117216 P i h1) (@lem3117223 P i h1)). Qed.
Lemma lem3117234 (_32371 : int) (P : int -> Prop) (i : int) (h1 : term131 P i) : term182 P _32371.
Proof. exact (EQ_MP (@lem3117230 P _32371) (@lem3117195 _32371 P i h1)). Qed.
Lemma lem3117235 (P : int -> Prop) (i : int) (h1 : term131 P i) : term182 P i.
Proof. exact (@lem3117234 i P i h1). Qed.
Lemma lem3117238 (P : int -> Prop) (i : int) (h1 : term131 P i) : False.
Proof. exact (@lem3117235 P i h1 (@lem3117232 P i h1)). Qed.
Lemma lem3117239 (P : int -> Prop) (i : int) (h1 : term131 P i) : term183.
Proof. exact (fun h0 : ~ False => @lem3117238 P i h1). Qed.
Lemma lem3117241 (p : Prop) : (term178 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3117242 : term183 = False.
Proof. exact (@lem3117241 False). Qed.
Lemma lem3117243 (P : int -> Prop) (i : int) (h1 : term131 P i) : False.
Proof. exact (EQ_MP (@lem3117242) (@lem3117239 P i h1)). Qed.
Lemma lem3117245 (i : int) (P : int -> Prop) (h1 : term148 i P) : term93 i.
Proof. exact (proj1 (@lem3117139 i P h1)). Qed.
Lemma lem3117246 (i : int) (P : int -> Prop) (h1 : term148 i P) : term176 i.
Proof. exact (fun h0 : term177 i => @lem3117245 i P h1). Qed.
Lemma lem3117248 (p : Prop) : (term178 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3117249 (i : int) : (term176 i) = (term93 i).
Proof. exact (@lem3117248 (term93 i)). Qed.
Lemma lem3117250 (i : int) (P : int -> Prop) (h1 : term148 i P) : term93 i.
Proof. exact (EQ_MP (@lem3117249 i) (@lem3117246 i P h1)). Qed.
Lemma lem3117252 (i : int) (P : int -> Prop) (h1 : term148 i P) : P i.
Proof. exact (proj2 (@lem3117139 i P h1)). Qed.
Lemma lem3117253 (i : int) (P : int -> Prop) (h1 : term148 i P) : term179 P i.
Proof. exact (fun h0 : term53 P i => @lem3117252 i P h1). Qed.
Lemma lem3117255 (p : Prop) : (term178 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3117256 (P : int -> Prop) (i : int) : (term179 P i) = (P i).
Proof. exact (@lem3117255 (P i)). Qed.
Lemma lem3117257 (i : int) (P : int -> Prop) (h1 : term148 i P) : P i.
Proof. exact (EQ_MP (@lem3117256 P i) (@lem3117253 i P h1)). Qed.
Lemma lem3117259 (a : Prop) (b : Prop) : (term180 a b) = (term181 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3117260 (P : int -> Prop) (_32372 : int) : (term94 P _32372) = (term73 P _32372).
Proof. exact (@lem3117259 (term93 _32372) (P _32372)). Qed.
Lemma lem3117262 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3117263 (P : int -> Prop) (_32372 : int) : (term73 P _32372) = (term182 P _32372).
Proof. exact (@lem3117262 (term67 P _32372)). Qed.
Lemma lem3117264 (P : int -> Prop) (_32372 : int) : (term94 P _32372) = (term182 P _32372).
Proof. exact (TRANS (@lem3117260 P _32372) (@lem3117263 P _32372)). Qed.
Lemma lem3117266 (i : int) (P : int -> Prop) (h1 : term148 i P) : term67 P i.
Proof. exact (conj (@lem3117250 i P h1) (@lem3117257 i P h1)). Qed.
Lemma lem3117268 (_32372 : int) (i : int) (P : int -> Prop) (h1 : term148 i P) : term182 P _32372.
Proof. exact (EQ_MP (@lem3117264 P _32372) (@lem3117205 _32372 i P h1)). Qed.
Lemma lem3117269 (i : int) (P : int -> Prop) (h1 : term148 i P) : term182 P i.
Proof. exact (@lem3117268 i i P h1). Qed.
Lemma lem3117272 (i : int) (P : int -> Prop) (h1 : term148 i P) : False.
Proof. exact (@lem3117269 i P h1 (@lem3117266 i P h1)). Qed.
Lemma lem3117273 (i : int) (P : int -> Prop) (h1 : term148 i P) : term183.
Proof. exact (fun h0 : ~ False => @lem3117272 i P h1). Qed.
Lemma lem3117275 (p : Prop) : (term178 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3117276 : term183 = False.
Proof. exact (@lem3117275 False). Qed.
Lemma lem3117277 (i : int) (P : int -> Prop) (h1 : term148 i P) : False.
Proof. exact (EQ_MP (@lem3117276) (@lem3117273 i P h1)). Qed.
Lemma lem3117278 (i : int) (P : int -> Prop) (h1 : term171 i P) : False.
Proof. exact (or_elim (@lem3117131 i P h1) (fun h0 : term131 P i => @lem3117243 P i h0) (fun h0 : term148 i P => @lem3117277 i P h0)). Qed.
Lemma lem3117279 (i : int) (P : int -> Prop) (h1 : term171 i P) : (term171 i P) = False.
Proof. exact (prop_ext (fun h2 : term171 i P => @lem3117278 i P h1) (fun h2 : False => @lem3117131 i P h1)). Qed.
Lemma lem3117280 (i : int) (P : int -> Prop) (h1 : term171 i P) : False.
Proof. exact (EQ_MP (@lem3117279 i P h1) (@lem3117131 i P h1)). Qed.
Lemma lem3117281 (P : int -> Prop) (h1 : term80 P) : False.
Proof. exact (ex_elim (@lem3117046 P h1) (fun i : int => fun h0 : term173 P i => @lem3117280 i P h0)). Qed.
Lemma lem3117282 (P : int -> Prop) (h1 : term80 P) : (term80 P) = False.
Proof. exact (prop_ext (fun h2 : term80 P => @lem3117281 P h1) (fun h2 : False => @lem3116740 P h1)). Qed.
Lemma lem3117283 (P : int -> Prop) (h1 : term80 P) : False.
Proof. exact (EQ_MP (@lem3117282 P h1) (@lem3116740 P h1)). Qed.
Lemma lem3117284 (P : int -> Prop) : term79 P.
Proof. exact (fun h0 : term80 P => @lem3117283 P h0). Qed.
Lemma lem3117285 (P : int -> Prop) : (term59 P) = (term76 P).
Proof. exact (EQ_MP (@lem3116739 P) (@lem3117284 P)). Qed.
Lemma lem3117290 : term88.
Proof. exact (fun P : int -> Prop => @lem3117285 P). Qed.
Lemma lem3117291 : term87.
Proof. exact (EQ_MP (@lem3116735) (@lem3117290)). Qed.
Lemma lem3117292 (P : int -> Prop) : term184 P.
Proof. exact (@lem3117291 P). Qed.
Lemma lem3117293 (P : int -> Prop) : (term184 P) = (term79 P).
Proof. exact (eq_refl (term184 P)). Qed.
Lemma lem3117294 (P : int -> Prop) : term79 P.
Proof. exact (EQ_MP (@lem3117293 P) (@lem3117292 P)). Qed.
Lemma lem3117296 (P : int -> Prop) : term79 P.
Proof. exact (@lem3116649 P (@lem3117294 P)). Qed.
Lemma lem3117297 (P : int -> Prop) (h1 : term80 P) : False.
Proof. exact (@lem3117296 P (@lem3116634 P h1)). Qed.
Lemma lem3117298 (P : int -> Prop) (h1 : term80 P) : (term80 P) = False.
Proof. exact (prop_ext (fun h2 : term80 P => @lem3117297 P h1) (fun h2 : False => @lem3116634 P h1)). Qed.
Lemma lem3117299 (P : int -> Prop) (h1 : term80 P) : False.
Proof. exact (EQ_MP (@lem3117298 P h1) (@lem3116634 P h1)). Qed.
Lemma lem3117300 (P : int -> Prop) : term79 P.
Proof. exact (fun h0 : term80 P => @lem3117299 P h0). Qed.
Lemma lem3117301 (P : int -> Prop) : (term59 P) = (term76 P).
Proof. exact (EQ_MP (@lem3116633 P) (@lem3117300 P)). Qed.
Lemma lem3117302 (P : int -> Prop) : term26 P.
Proof. exact (EQ_MP (@lem3116629 P) (@lem3117301 P)). Qed.
Lemma lem3117303 (P : int -> Prop) : term25 P.
Proof. exact (EQ_MP (@lem3116483 P) (@lem3117302 P)). Qed.
