Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513549_term_abbrevs.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm513141_spec.
Require Import thm513146_spec.
Require Import thm513147_spec.
Require Import thm513166_spec.
Require Import thm513167_spec.
Require Import thm513173_spec.
Require Import thm513174_spec.
Require Import thm513181_spec.
Require Import thm513182_spec.
Require Import thm513185_spec.
Require Import thm513186_spec.
Require Import thm513189_spec.
Require Import thm513190_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem513388 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem513389 : term1.
Proof. exact (@lem513388 term2). Qed.
Lemma lem513390 : term3 = (term4 = term5).
Proof. exact (eq_refl term3). Qed.
Lemma lem513391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513392 : term6 = term7.
Proof. exact (MK_COMB (@lem513391) (@lem513390)). Qed.
Lemma lem513393 (n : nat) : (term8 n) = ((term9 n) = (term10 n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem513394 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem513395 (n : nat) : (term11 n) = (term12 n).
Proof. exact (MK_COMB (@lem513394) (@lem513393 n)). Qed.
Lemma lem513396 (n : nat) : (term13 n) = ((term14 n) = (term15 n)).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem513397 (n : nat) : (term16 n) = (term17 n).
Proof. exact (MK_COMB (@lem513395 n) (@lem513396 n)). Qed.
Lemma lem513398 : term18 = term19.
Proof. exact (fun_ext (fun n : nat => @lem513397 n)). Qed.
Lemma lem513399 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513400 : term20 = term21.
Proof. exact (MK_COMB (@lem513399) (@lem513398)). Qed.
Lemma lem513401 : term22 = term23.
Proof. exact (MK_COMB (@lem513392) (@lem513400)). Qed.
Lemma lem513402 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem513403 : term24 = term25.
Proof. exact (MK_COMB (@lem513402) (@lem513401)). Qed.
Lemma lem513404 (n : nat) : (term8 n) = ((term9 n) = (term10 n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem513405 : term26 = term2.
Proof. exact (fun_ext (fun n : nat => @lem513404 n)). Qed.
Lemma lem513406 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513407 : term27 = term28.
Proof. exact (MK_COMB (@lem513406) (@lem513405)). Qed.
Lemma lem513408 : term1 = term29.
Proof. exact (MK_COMB (@lem513403) (@lem513407)). Qed.
Lemma lem513409 : term29.
Proof. exact (EQ_MP (@lem513408) (@lem513389)). Qed.
Lemma lem513414 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem513190 n) (@lem513189 n)). Qed.
Lemma lem513415 : (NUMERAL 0) = 0.
Proof. exact (@lem513414 0). Qed.
Lemma lem513416 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem513417 : term30 = (Nat.add 0).
Proof. exact (MK_COMB (@lem513416) (@lem513415)). Qed.
Lemma lem513419 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem513190 n) (@lem513189 n)). Qed.
Lemma lem513420 : (NUMERAL 0) = 0.
Proof. exact (@lem513419 0). Qed.
Lemma lem513421 : term31 = (Nat.add 0 0).
Proof. exact (MK_COMB (@lem513417) (@lem513420)). Qed.
Lemma lem513423 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem513182 n) (@lem513181 n)). Qed.
Lemma lem513424 : (Nat.add 0 0) = 0.
Proof. exact (@lem513423 0). Qed.
Lemma lem513425 : term31 = 0.
Proof. exact (TRANS (@lem513421) (@lem513424)). Qed.
Lemma lem513426 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem513427 : term4 = (Nat.pred 0).
Proof. exact (MK_COMB (@lem513426) (@lem513425)). Qed.
Lemma lem513429 : (Nat.pred 0) = 0.
Proof. exact (proj1 (@lem513141)). Qed.
Lemma lem513430 : term4 = 0.
Proof. exact (TRANS (@lem513427) (@lem513429)). Qed.
Lemma lem513431 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513432 : term32 = (@eq nat 0).
Proof. exact (MK_COMB (@lem513431) (@lem513430)). Qed.
Lemma lem513438 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem513190 n) (@lem513189 n)). Qed.
Lemma lem513439 : (NUMERAL 0) = 0.
Proof. exact (@lem513438 0). Qed.
Lemma lem513440 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513441 : term33 = (@eq nat 0).
Proof. exact (MK_COMB (@lem513440) (@lem513439)). Qed.
Lemma lem513442 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem513443 : ((NUMERAL 0) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem513441) (@lem513442)). Qed.
Lemma lem513445 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513446 (x : nat) : (x = x) = True.
Proof. exact (@lem513445 nat x). Qed.
Lemma lem513447 : (0 = 0) = True.
Proof. exact (@lem513446 0). Qed.
Lemma lem513448 : ((NUMERAL 0) = 0) = True.
Proof. exact (TRANS (@lem513443) (@lem513447)). Qed.
Lemma lem513449 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem513450 : term34 = (@COND nat True).
Proof. exact (MK_COMB (@lem513449) (@lem513448)). Qed.
Lemma lem513451 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem513452 : term35 = (@COND nat True 0).
Proof. exact (MK_COMB (@lem513450) (@lem513451)). Qed.
Lemma lem513454 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem513190 n) (@lem513189 n)). Qed.
Lemma lem513455 : (NUMERAL 0) = 0.
Proof. exact (@lem513454 0). Qed.
Lemma lem513456 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem513457 : term36 = (Nat.pred 0).
Proof. exact (MK_COMB (@lem513456) (@lem513455)). Qed.
Lemma lem513459 : (Nat.pred 0) = 0.
Proof. exact (proj1 (@lem513141)). Qed.
Lemma lem513460 : term36 = 0.
Proof. exact (TRANS (@lem513457) (@lem513459)). Qed.
Lemma lem513461 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem513462 : term37 = (Nat.add 0).
Proof. exact (MK_COMB (@lem513461) (@lem513460)). Qed.
Lemma lem513464 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem513190 n) (@lem513189 n)). Qed.
Lemma lem513465 : (NUMERAL 0) = 0.
Proof. exact (@lem513464 0). Qed.
Lemma lem513466 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem513467 : term36 = (Nat.pred 0).
Proof. exact (MK_COMB (@lem513466) (@lem513465)). Qed.
Lemma lem513469 : (Nat.pred 0) = 0.
Proof. exact (proj1 (@lem513141)). Qed.
Lemma lem513470 : term36 = 0.
Proof. exact (TRANS (@lem513467) (@lem513469)). Qed.
Lemma lem513471 : term38 = (Nat.add 0 0).
Proof. exact (MK_COMB (@lem513462) (@lem513470)). Qed.
Lemma lem513473 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem513182 n) (@lem513181 n)). Qed.
Lemma lem513474 : (Nat.add 0 0) = 0.
Proof. exact (@lem513473 0). Qed.
Lemma lem513475 : term38 = 0.
Proof. exact (TRANS (@lem513471) (@lem513474)). Qed.
Lemma lem513476 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem513477 : term39 = (S 0).
Proof. exact (MK_COMB (@lem513476) (@lem513475)). Qed.
Lemma lem513478 : term5 = term40.
Proof. exact (MK_COMB (@lem513452) (@lem513477)). Qed.
Lemma lem513480 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem513481 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem513480 nat t2 t1). Qed.
Lemma lem513482 : term40 = 0.
Proof. exact (@lem513481 (S 0) 0). Qed.
Lemma lem513483 : term5 = 0.
Proof. exact (TRANS (@lem513478) (@lem513482)). Qed.
Lemma lem513484 : (term4 = term5) = (0 = 0).
Proof. exact (MK_COMB (@lem513432) (@lem513483)). Qed.
Lemma lem513486 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513487 (x : nat) : (x = x) = True.
Proof. exact (@lem513486 nat x). Qed.
Lemma lem513488 : (0 = 0) = True.
Proof. exact (@lem513487 0). Qed.
Lemma lem513489 : (term4 = term5) = True.
Proof. exact (TRANS (@lem513484) (@lem513488)). Qed.
Lemma lem513490 : True = (term4 = term5).
Proof. exact (SYM (@lem513489)). Qed.
Lemma lem513491 : term4 = term5.
Proof. exact (EQ_MP (@lem513490) (@lem0)). Qed.
Lemma lem513495 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem513174 m n) (@lem513173 m n)). Qed.
Lemma lem513496 (n : nat) : (term43 n) = (term44 n).
Proof. exact (@lem513495 n (S n)). Qed.
Lemma lem513498 (m : nat) (n : nat) : (term45 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem513167 m n) (@lem513166 m n)). Qed.
Lemma lem513499 (n : nat) : (term46 n) = (term47 n).
Proof. exact (@lem513498 n n). Qed.
Lemma lem513500 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem513501 (n : nat) : (term44 n) = (term48 n).
Proof. exact (MK_COMB (@lem513500) (@lem513499 n)). Qed.
Lemma lem513502 (n : nat) : (term43 n) = (term48 n).
Proof. exact (TRANS (@lem513496 n) (@lem513501 n)). Qed.
Lemma lem513503 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem513504 (n : nat) : (term14 n) = (term49 n).
Proof. exact (MK_COMB (@lem513503) (@lem513502 n)). Qed.
Lemma lem513506 (n : nat) : (term50 n) = n.
Proof. exact (EQ_MP (@lem513186 n) (@lem513185 n)). Qed.
Lemma lem513507 (n : nat) : (term49 n) = (term47 n).
Proof. exact (@lem513506 (term47 n)). Qed.
Lemma lem513508 (n : nat) : (term14 n) = (term47 n).
Proof. exact (TRANS (@lem513504 n) (@lem513507 n)). Qed.
Lemma lem513509 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513510 (n : nat) : (term51 n) = (term52 n).
Proof. exact (MK_COMB (@lem513509) (@lem513508 n)). Qed.
Lemma lem513514 (n : nat) : ((S n) = 0) = False.
Proof. exact (@lem513147 n (@lem513146 n)). Qed.
Lemma lem513515 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem513516 (n : nat) : (term53 n) = (@COND nat False).
Proof. exact (MK_COMB (@lem513515) (@lem513514 n)). Qed.
Lemma lem513517 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem513518 (n : nat) : (term54 n) = (@COND nat False 0).
Proof. exact (MK_COMB (@lem513516 n) (@lem513517)). Qed.
Lemma lem513520 (n : nat) : (term50 n) = n.
Proof. exact (EQ_MP (@lem513186 n) (@lem513185 n)). Qed.
Lemma lem513521 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem513522 (n : nat) : (term55 n) = (Nat.add n).
Proof. exact (MK_COMB (@lem513521) (@lem513520 n)). Qed.
Lemma lem513524 (n : nat) : (term50 n) = n.
Proof. exact (EQ_MP (@lem513186 n) (@lem513185 n)). Qed.
Lemma lem513525 (n : nat) : (term56 n) = (Nat.add n n).
Proof. exact (MK_COMB (@lem513522 n) (@lem513524 n)). Qed.
Lemma lem513526 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem513527 (n : nat) : (term57 n) = (term47 n).
Proof. exact (MK_COMB (@lem513526) (@lem513525 n)). Qed.
Lemma lem513528 (n : nat) : (term15 n) = (term58 n).
Proof. exact (MK_COMB (@lem513518 n) (@lem513527 n)). Qed.
Lemma lem513530 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem513531 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem513530 nat t1 t2). Qed.
Lemma lem513532 (n : nat) : (term58 n) = (term47 n).
Proof. exact (@lem513531 0 (term47 n)). Qed.
Lemma lem513533 (n : nat) : (term15 n) = (term47 n).
Proof. exact (TRANS (@lem513528 n) (@lem513532 n)). Qed.
Lemma lem513534 (n : nat) : ((term14 n) = (term15 n)) = ((term47 n) = (term47 n)).
Proof. exact (MK_COMB (@lem513510 n) (@lem513533 n)). Qed.
Lemma lem513536 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513537 (x : nat) : (x = x) = True.
Proof. exact (@lem513536 nat x). Qed.
Lemma lem513538 (n : nat) : ((term47 n) = (term47 n)) = True.
Proof. exact (@lem513537 (term47 n)). Qed.
Lemma lem513539 (n : nat) : ((term14 n) = (term15 n)) = True.
Proof. exact (TRANS (@lem513534 n) (@lem513538 n)). Qed.
Lemma lem513540 (n : nat) : True = ((term14 n) = (term15 n)).
Proof. exact (SYM (@lem513539 n)). Qed.
Lemma lem513541 (n : nat) : (term14 n) = (term15 n).
Proof. exact (EQ_MP (@lem513540 n) (@lem0)). Qed.
Lemma lem513542 (n : nat) : term17 n.
Proof. exact (fun h0 : (term9 n) = (term10 n) => @lem513541 n). Qed.
Lemma lem513547 : term21.
Proof. exact (fun n : nat => @lem513542 n). Qed.
Lemma lem513548 : term23.
Proof. exact (conj (@lem513491) (@lem513547)). Qed.
Lemma lem513549 : term28.
Proof. exact (@lem513409 (@lem513548)). Qed.
