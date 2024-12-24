Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_ADD_LCANCEL_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem79434 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem79435 : term1.
Proof. exact (@lem79434 term2). Qed.
Lemma lem79436 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem79437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem79438 : term5 = term6.
Proof. exact (MK_COMB (@lem79437) (@lem79436)). Qed.
Lemma lem79439 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem79440 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79441 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem79440) (@lem79439 m)). Qed.
Lemma lem79442 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem79443 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem79441 m) (@lem79442 m)). Qed.
Lemma lem79444 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem79443 m)). Qed.
Lemma lem79445 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79446 : term17 = term18.
Proof. exact (MK_COMB (@lem79445) (@lem79444)). Qed.
Lemma lem79447 : term19 = term20.
Proof. exact (MK_COMB (@lem79438) (@lem79446)). Qed.
Lemma lem79448 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79449 : term21 = term22.
Proof. exact (MK_COMB (@lem79448) (@lem79447)). Qed.
Lemma lem79450 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem79451 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem79450 m)). Qed.
Lemma lem79452 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79453 : term24 = term25.
Proof. exact (MK_COMB (@lem79452) (@lem79451)). Qed.
Lemma lem79454 : term1 = term26.
Proof. exact (MK_COMB (@lem79449) (@lem79453)). Qed.
Lemma lem79455 : term26.
Proof. exact (EQ_MP (@lem79454) (@lem79435)). Qed.
Lemma lem79456 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem79483 : term27.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem79484 (n : nat) : term28 n.
Proof. exact (@lem79483 n). Qed.
Lemma lem79485 (n : nat) : (term28 n) = ((term29 n) = n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem79500 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem79485 n) (@lem79484 n)). Qed.
Lemma lem79501 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem79502 (n : nat) : (term30 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem79501) (@lem79500 n)). Qed.
Lemma lem79504 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem79485 n) (@lem79484 n)). Qed.
Lemma lem79505 (p : nat) : (term29 p) = p.
Proof. exact (@lem79504 p). Qed.
Lemma lem79506 (n : nat) (p : nat) : ((term29 n) = (term29 p)) = (n = p).
Proof. exact (MK_COMB (@lem79502 n) (@lem79505 p)). Qed.
Lemma lem79509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem79510 (n : nat) (p : nat) : (term31 n p) = (term32 n p).
Proof. exact (MK_COMB (@lem79509) (@lem79506 n p)). Qed.
Lemma lem79513 (n : nat) (p : nat) : (n = p) = (n = p).
Proof. exact (eq_refl (n = p)). Qed.
Lemma lem79514 (n : nat) (p : nat) : (((term29 n) = (term29 p)) = (n = p)) = ((n = p) = (n = p)).
Proof. exact (MK_COMB (@lem79510 n p) (@lem79513 n p)). Qed.
Lemma lem79516 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem79517 (x : Prop) : (x = x) = True.
Proof. exact (@lem79516 Prop x). Qed.
Lemma lem79518 (n : nat) (p : nat) : ((n = p) = (n = p)) = True.
Proof. exact (@lem79517 (n = p)). Qed.
Lemma lem79519 (n : nat) (p : nat) : (((term29 n) = (term29 p)) = (n = p)) = True.
Proof. exact (TRANS (@lem79514 n p) (@lem79518 n p)). Qed.
Lemma lem79520 (n : nat) : (term33 n) = term34.
Proof. exact (fun_ext (fun p : nat => @lem79519 n p)). Qed.
Lemma lem79521 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79522 (n : nat) : (term35 n) = term36.
Proof. exact (MK_COMB (@lem79521) (@lem79520 n)). Qed.
Lemma lem79524 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem79525 (t : Prop) : (term38 t) = t.
Proof. exact (@lem79524 nat t). Qed.
Lemma lem79526 : term36 = True.
Proof. exact (@lem79525 True). Qed.
Lemma lem79527 (n : nat) : (term35 n) = True.
Proof. exact (TRANS (@lem79522 n) (@lem79526)). Qed.
Lemma lem79528 : term39 = term34.
Proof. exact (fun_ext (fun n : nat => @lem79527 n)). Qed.
Lemma lem79529 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79530 : term4 = term36.
Proof. exact (MK_COMB (@lem79529) (@lem79528)). Qed.
Lemma lem79532 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem79533 (t : Prop) : (term38 t) = t.
Proof. exact (@lem79532 nat t). Qed.
Lemma lem79534 : term36 = True.
Proof. exact (@lem79533 True). Qed.
Lemma lem79535 : term4 = True.
Proof. exact (TRANS (@lem79530) (@lem79534)). Qed.
Lemma lem79536 : True = term4.
Proof. exact (SYM (@lem79535)). Qed.
Lemma lem79537 : term4.
Proof. exact (EQ_MP (@lem79536) (@lem0)). Qed.
Lemma lem79538 (m : nat) : term40 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem79539 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem79540 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem79539 m) (@lem79538 m)). Qed.
Lemma lem79541 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem79540 m n). Qed.
Lemma lem79542 (m : nat) (n : nat) : (term42 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem79544 : term43.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem79545 : term44.
Proof. exact (proj2 (@lem79544)). Qed.
Lemma lem79553 : term45.
Proof. exact (proj1 (@lem79545)). Qed.
Lemma lem79554 (m : nat) : term46 m.
Proof. exact (@lem79553 m). Qed.
Lemma lem79555 (m : nat) : (term46 m) = (term47 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem79556 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem79555 m) (@lem79554 m)). Qed.
Lemma lem79557 (m : nat) (n : nat) : term48 m n.
Proof. exact (@lem79556 m n). Qed.
Lemma lem79558 (m : nat) (n : nat) : (term48 m n) = ((term49 m n) = (term50 m n)).
Proof. exact (eq_refl (term48 m n)). Qed.
Lemma lem79568 (n : nat) (m : nat) (h1 : term8 m) : term51 m n.
Proof. exact (@lem79456 m h1 n). Qed.
Lemma lem79569 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (eq_refl (term51 m n)). Qed.
Lemma lem79570 (n : nat) (m : nat) (h1 : term8 m) : term52 m n.
Proof. exact (EQ_MP (@lem79569 m n) (@lem79568 n m h1)). Qed.
Lemma lem79571 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : term53 m n p.
Proof. exact (@lem79570 n m h1 p). Qed.
Lemma lem79572 (m : nat) (n : nat) (p : nat) : (term53 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term53 m n p)). Qed.
Lemma lem79587 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (EQ_MP (@lem79558 m n) (@lem79557 m n)). Qed.
Lemma lem79588 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem79589 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem79588) (@lem79587 m n)). Qed.
Lemma lem79591 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (EQ_MP (@lem79558 m n) (@lem79557 m n)). Qed.
Lemma lem79592 (m : nat) (p : nat) : (term49 m p) = (term50 m p).
Proof. exact (@lem79591 m p). Qed.
Lemma lem79593 (n : nat) (m : nat) (p : nat) : ((term49 m n) = (term49 m p)) = ((term50 m n) = (term50 m p)).
Proof. exact (MK_COMB (@lem79589 m n) (@lem79592 m p)). Qed.
Lemma lem79595 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem79542 m n) (@lem79541 m n)). Qed.
Lemma lem79596 (n : nat) (m : nat) (p : nat) : ((term50 m n) = (term50 m p)) = ((Nat.add m n) = (Nat.add m p)).
Proof. exact (@lem79595 (Nat.add m n) (Nat.add m p)). Qed.
Lemma lem79598 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem79572 m n p) (@lem79571 n p m h1)). Qed.
Lemma lem79601 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : ((term50 m n) = (term50 m p)) = (n = p).
Proof. exact (TRANS (@lem79596 n m p) (@lem79598 n p m h1)). Qed.
Lemma lem79602 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : ((term49 m n) = (term49 m p)) = (n = p).
Proof. exact (TRANS (@lem79593 n m p) (@lem79601 n p m h1)). Qed.
Lemma lem79603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem79604 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term56 n m p) = (term32 n p).
Proof. exact (MK_COMB (@lem79603) (@lem79602 n p m h1)). Qed.
Lemma lem79607 (n : nat) (p : nat) : (n = p) = (n = p).
Proof. exact (eq_refl (n = p)). Qed.
Lemma lem79608 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (((term49 m n) = (term49 m p)) = (n = p)) = ((n = p) = (n = p)).
Proof. exact (MK_COMB (@lem79604 n p m h1) (@lem79607 n p)). Qed.
Lemma lem79610 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem79611 (x : Prop) : (x = x) = True.
Proof. exact (@lem79610 Prop x). Qed.
Lemma lem79612 (n : nat) (p : nat) : ((n = p) = (n = p)) = True.
Proof. exact (@lem79611 (n = p)). Qed.
Lemma lem79613 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (((term49 m n) = (term49 m p)) = (n = p)) = True.
Proof. exact (TRANS (@lem79608 n p m h1) (@lem79612 n p)). Qed.
Lemma lem79614 (n : nat) (m : nat) (h1 : term8 m) : (term57 m n) = term34.
Proof. exact (fun_ext (fun p : nat => @lem79613 n p m h1)). Qed.
Lemma lem79615 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79616 (n : nat) (m : nat) (h1 : term8 m) : (term58 m n) = term36.
Proof. exact (MK_COMB (@lem79615) (@lem79614 n m h1)). Qed.
Lemma lem79618 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem79619 (t : Prop) : (term38 t) = t.
Proof. exact (@lem79618 nat t). Qed.
Lemma lem79620 : term36 = True.
Proof. exact (@lem79619 True). Qed.
Lemma lem79621 (n : nat) (m : nat) (h1 : term8 m) : (term58 m n) = True.
Proof. exact (TRANS (@lem79616 n m h1) (@lem79620)). Qed.
Lemma lem79622 (m : nat) (h1 : term8 m) : (term59 m) = term34.
Proof. exact (fun_ext (fun n : nat => @lem79621 n m h1)). Qed.
Lemma lem79623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79624 (m : nat) (h1 : term8 m) : (term12 m) = term36.
Proof. exact (MK_COMB (@lem79623) (@lem79622 m h1)). Qed.
Lemma lem79626 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem79627 (t : Prop) : (term38 t) = t.
Proof. exact (@lem79626 nat t). Qed.
Lemma lem79628 : term36 = True.
Proof. exact (@lem79627 True). Qed.
Lemma lem79629 (m : nat) (h1 : term8 m) : (term12 m) = True.
Proof. exact (TRANS (@lem79624 m h1) (@lem79628)). Qed.
Lemma lem79630 (m : nat) (h1 : term8 m) : True = (term12 m).
Proof. exact (SYM (@lem79629 m h1)). Qed.
Lemma lem79631 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (EQ_MP (@lem79630 m h1) (@lem0)). Qed.
Lemma lem79632 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem79631 m h0). Qed.
Lemma lem79637 : term18.
Proof. exact (fun m : nat => @lem79632 m). Qed.
Lemma lem79638 : term20.
Proof. exact (conj (@lem79537) (@lem79637)). Qed.
Lemma lem79639 : term25.
Proof. exact (@lem79455 (@lem79638)). Qed.
