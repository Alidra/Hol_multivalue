Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SUBSET_NUMSEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_NUMSEG_spec.
Require Import FINITE_SUBSET_spec.
Require Import IN_INSERT_spec.
Require Import IN_NUMSEG_spec.
Require Import LE_0_spec.
Require Import LE_CASES_spec.
Require Import LE_REFL_spec.
Require Import LE_TRANS_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5376490 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5376491 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5376492 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5376491 t1) (@lem5376490 t1)). Qed.
Lemma lem5376493 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5376492 t1 t2). Qed.
Lemma lem5376494 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5376495 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5376494 t1 t2) (@lem5376493 t1 t2)). Qed.
Lemma lem5376496 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5376495 t1 t2 t3). Qed.
Lemma lem5376497 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5376498 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5376497 t1 t2 t3) (@lem5376496 t1 t2 t3)). Qed.
Lemma lem5376499 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5376498 t1 t2 t3)). Qed.
Lemma lem5376500 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5376501 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5376502 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5376501 t1) (@lem5376500 t1)). Qed.
Lemma lem5376503 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5376502 t1 t2). Qed.
Lemma lem5376504 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5376505 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5376504 t1 t2) (@lem5376503 t1 t2)). Qed.
Lemma lem5376506 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5376505 t1 t2 t3). Qed.
Lemma lem5376507 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5376508 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5376507 t1 t2 t3) (@lem5376506 t1 t2 t3)). Qed.
Lemma lem5376509 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5376508 t1 t2 t3)). Qed.
Lemma lem5376510 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5376511 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem5376512 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem5376511 A x) (@lem5376510 A x)). Qed.
Lemma lem5376513 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5376515 {A : Type'} (x : A) : term10 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5376516 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (eq_refl (term10 A x)). Qed.
Lemma lem5376517 {A : Type'} (x : A) : term11 A x.
Proof. exact (EQ_MP (@lem5376516 A x) (@lem5376515 A x)). Qed.
Lemma lem5376518 {A : Type'} (x : A) (y : A) : term12 A x y.
Proof. exact (@lem5376517 A x y). Qed.
Lemma lem5376519 {A : Type'} (y : A) (x : A) : (term12 A x y) = (term13 A y x).
Proof. exact (eq_refl (term12 A x y)). Qed.
Lemma lem5376520 {A : Type'} (y : A) (x : A) : term13 A y x.
Proof. exact (EQ_MP (@lem5376519 A y x) (@lem5376518 A x y)). Qed.
Lemma lem5376521 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term14 A y x s.
Proof. exact (@lem5376520 A y x s). Qed.
Lemma lem5376522 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term14 A y x s) = ((term15 A x y s) = (term16 A y x s)).
Proof. exact (eq_refl (term14 A y x s)). Qed.
Lemma lem5376524 {A : Type'} (h1 : term17 A) : term17 A.
Proof. exact (h1). Qed.
Lemma lem5376525 {A : Type'} (P : type686 A) (h1 : term17 A) : term18 A P.
Proof. exact (@lem5376524 A h1 P). Qed.
Lemma lem5376526 {A : Type'} (P : type686 A) : (term18 A P) = (term19 A P).
Proof. exact (eq_refl (term18 A P)). Qed.
Lemma lem5376527 {A : Type'} (P : type686 A) (h1 : term17 A) : term19 A P.
Proof. exact (EQ_MP (@lem5376526 A P) (@lem5376525 A P h1)). Qed.
Lemma lem5376528 {A : Type'} (P : type686 A) (h1 : term20 A P) : term20 A P.
Proof. exact (h1). Qed.
Lemma lem5376529 {A : Type'} (P : type686 A) (h1 : term17 A) (h2 : term20 A P) : term21 A P.
Proof. exact (@lem5376527 A P h1 (@lem5376528 A P h2)). Qed.
Lemma lem5376530 {A : Type'} (P : type686 A) (h1 : term20 A P) : term22 A P.
Proof. exact (fun h0 : term17 A => @lem5376529 A P h0 h1). Qed.
Lemma lem5376531 {A : Type'} (h1 : term17 A) : term17 A.
Proof. exact (h1). Qed.
Lemma lem5376532 {A : Type'} (P : type686 A) (h1 : term17 A) (h2 : term20 A P) : term21 A P.
Proof. exact (@lem5376530 A P h2 (@lem5376531 A h1)). Qed.
Lemma lem5376533 {A : Type'} (P : type686 A) (h1 : term17 A) : term19 A P.
Proof. exact (fun h0 : term20 A P => @lem5376532 A P h1 h0). Qed.
Lemma lem5376534 {A : Type'} (h1 : term17 A) : term17 A.
Proof. exact (fun P : type686 A => @lem5376533 A P h1). Qed.
Lemma lem5376535 {A : Type'} : term23 A.
Proof. exact (fun h0 : term17 A => @lem5376534 A h0). Qed.
Lemma lem5376536 {A : Type'} : term17 A.
Proof. exact (@lem5376535 A (@lem3558722 A)). Qed.
Lemma lem5376537 {A : Type'} (P : type686 A) : term18 A P.
Proof. exact (@lem5376536 A P). Qed.
Lemma lem5376538 {A : Type'} (P : type686 A) : (term18 A P) = (term19 A P).
Proof. exact (eq_refl (term18 A P)). Qed.
Lemma lem5376540 (n : nat) : term24 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem5376541 (n : nat) : (term24 n) = (term25 n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem5376542 (n : nat) : term25 n.
Proof. exact (EQ_MP (@lem5376541 n) (@lem5376540 n)). Qed.
Lemma lem5376543 (n : nat) : (term25 n) = ((term25 n) = True).
Proof. exact (@lem7 (term25 n)). Qed.
Lemma lem5376545 (m : nat) : term26 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5376546 (m : nat) : (term26 m) = (term27 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem5376547 (m : nat) : term27 m.
Proof. exact (EQ_MP (@lem5376546 m) (@lem5376545 m)). Qed.
Lemma lem5376548 (m : nat) (n : nat) : term28 m n.
Proof. exact (@lem5376547 m n). Qed.
Lemma lem5376549 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem5376550 (m : nat) (n : nat) : term29 m n.
Proof. exact (EQ_MP (@lem5376549 m n) (@lem5376548 m n)). Qed.
Lemma lem5376551 (m : nat) (n : nat) (p : nat) : term30 m n p.
Proof. exact (@lem5376550 m n p). Qed.
Lemma lem5376552 (m : nat) (p : nat) (n : nat) : (term30 m n p) = ((term31 p m n) = (term32 m p n)).
Proof. exact (eq_refl (term30 m n p)). Qed.
Lemma lem5376554 {A : Type'} (s : A -> Prop) : term33 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem5376555 {A : Type'} (s : A -> Prop) : (term33 A s) = (term34 A s).
Proof. exact (eq_refl (term33 A s)). Qed.
Lemma lem5376556 {A : Type'} (s : A -> Prop) : term34 A s.
Proof. exact (EQ_MP (@lem5376555 A s) (@lem5376554 A s)). Qed.
Lemma lem5376557 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term35 A s t.
Proof. exact (@lem5376556 A s t). Qed.
Lemma lem5376558 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = ((@SUBSET A s t) = (term36 A s t)).
Proof. exact (eq_refl (term35 A s t)). Qed.
Lemma lem5376567 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem5376558 A s t) (@lem5376557 A s t)). Qed.
Lemma lem5376568 (s : nat -> Prop) (t : nat -> Prop) : (@SUBSET nat s t) = (term37 s t).
Proof. exact (@lem5376567 nat s t). Qed.
Lemma lem5376569 (s : nat -> Prop) (n : nat) : (term38 s n) = (term39 s n).
Proof. exact (@lem5376568 s (term40 n)). Qed.
Lemma lem5376577 (m : nat) (p : nat) (n : nat) : (term31 p m n) = (term32 m p n).
Proof. exact (EQ_MP (@lem5376552 m p n) (@lem5376551 m n p)). Qed.
Lemma lem5376578 (x : nat) (n : nat) : (term41 x n) = (term42 x n).
Proof. exact (@lem5376577 (NUMERAL 0) x n). Qed.
Lemma lem5376582 (n : nat) : (term25 n) = True.
Proof. exact (EQ_MP (@lem5376543 n) (@lem5376542 n)). Qed.
Lemma lem5376583 (x : nat) : (term25 x) = True.
Proof. exact (@lem5376582 x). Qed.
Lemma lem5376584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5376585 (x : nat) : (term43 x) = (and True).
Proof. exact (MK_COMB (@lem5376584) (@lem5376583 x)). Qed.
Lemma lem5376586 (x : nat) (n : nat) : (Peano.le x n) = (Peano.le x n).
Proof. exact (eq_refl (Peano.le x n)). Qed.
Lemma lem5376587 (x : nat) (n : nat) : (term42 x n) = (term44 x n).
Proof. exact (MK_COMB (@lem5376585 x) (@lem5376586 x n)). Qed.
Lemma lem5376589 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5376590 (x : nat) (n : nat) : (term44 x n) = (Peano.le x n).
Proof. exact (@lem5376589 (Peano.le x n)). Qed.
Lemma lem5376591 (x : nat) (n : nat) : (term42 x n) = (Peano.le x n).
Proof. exact (TRANS (@lem5376587 x n) (@lem5376590 x n)). Qed.
Lemma lem5376592 (x : nat) (n : nat) : (term41 x n) = (Peano.le x n).
Proof. exact (TRANS (@lem5376578 x n) (@lem5376591 x n)). Qed.
Lemma lem5376593 (x : nat) (s : nat -> Prop) : (term45 x s) = (term45 x s).
Proof. exact (eq_refl (term45 x s)). Qed.
Lemma lem5376594 (s : nat -> Prop) (x : nat) (n : nat) : (term46 s x n) = (term47 s x n).
Proof. exact (MK_COMB (@lem5376593 x s) (@lem5376592 x n)). Qed.
Lemma lem5376597 (s : nat -> Prop) (n : nat) : (term48 s n) = (term49 s n).
Proof. exact (fun_ext (fun x : nat => @lem5376594 s x n)). Qed.
Lemma lem5376598 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376599 (s : nat -> Prop) (n : nat) : (term39 s n) = (term50 s n).
Proof. exact (MK_COMB (@lem5376598) (@lem5376597 s n)). Qed.
Lemma lem5376604 (s : nat -> Prop) (n : nat) : (term38 s n) = (term50 s n).
Proof. exact (TRANS (@lem5376569 s n) (@lem5376599 s n)). Qed.
Lemma lem5376605 (s : nat -> Prop) : (term51 s) = (term52 s).
Proof. exact (fun_ext (fun n : nat => @lem5376604 s n)). Qed.
Lemma lem5376606 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5376607 (s : nat -> Prop) : (term53 s) = (term54 s).
Proof. exact (MK_COMB (@lem5376606) (@lem5376605 s)). Qed.
Lemma lem5376612 (s : nat -> Prop) : (term55 s) = (term55 s).
Proof. exact (eq_refl (term55 s)). Qed.
Lemma lem5376613 (s : nat -> Prop) : (term56 s) = (term57 s).
Proof. exact (MK_COMB (@lem5376612 s) (@lem5376607 s)). Qed.
Lemma lem5376616 (s : nat -> Prop) : (term57 s) = (term56 s).
Proof. exact (SYM (@lem5376613 s)). Qed.
Lemma lem5376618 {A : Type'} (P : type686 A) : term19 A P.
Proof. exact (EQ_MP (@lem5376538 A P) (@lem5376537 A P)). Qed.
Lemma lem5376619 (P : type993) : term58 P.
Proof. exact (@lem5376618 nat P). Qed.
Lemma lem5376620 : term59.
Proof. exact (@lem5376619 term60). Qed.
Lemma lem5376621 : term61 = term62.
Proof. exact (eq_refl term61). Qed.
Lemma lem5376622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5376623 : term63 = term64.
Proof. exact (MK_COMB (@lem5376622) (@lem5376621)). Qed.
Lemma lem5376624 (s : nat -> Prop) : (term65 s) = (term54 s).
Proof. exact (eq_refl (term65 s)). Qed.
Lemma lem5376625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5376626 (s : nat -> Prop) : (term66 s) = (term67 s).
Proof. exact (MK_COMB (@lem5376625) (@lem5376624 s)). Qed.
Lemma lem5376627 (x : nat) (s : nat -> Prop) : (term68 x s) = (term68 x s).
Proof. exact (eq_refl (term68 x s)). Qed.
Lemma lem5376628 (x : nat) (s : nat -> Prop) : (term69 x s) = (term70 x s).
Proof. exact (MK_COMB (@lem5376626 s) (@lem5376627 x s)). Qed.
Lemma lem5376629 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5376630 (x : nat) (s : nat -> Prop) : (term71 x s) = (term72 x s).
Proof. exact (MK_COMB (@lem5376629) (@lem5376628 x s)). Qed.
Lemma lem5376631 (x : nat) (s : nat -> Prop) : (term73 x s) = (term74 x s).
Proof. exact (eq_refl (term73 x s)). Qed.
Lemma lem5376632 (x : nat) (s : nat -> Prop) : (term75 x s) = (term76 x s).
Proof. exact (MK_COMB (@lem5376630 x s) (@lem5376631 x s)). Qed.
Lemma lem5376633 (x : nat) : (term77 x) = (term78 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5376632 x s)). Qed.
Lemma lem5376634 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5376635 (x : nat) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem5376634) (@lem5376633 x)). Qed.
Lemma lem5376636 : term81 = term82.
Proof. exact (fun_ext (fun x : nat => @lem5376635 x)). Qed.
Lemma lem5376637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376638 : term83 = term84.
Proof. exact (MK_COMB (@lem5376637) (@lem5376636)). Qed.
Lemma lem5376639 : term85 = term86.
Proof. exact (MK_COMB (@lem5376623) (@lem5376638)). Qed.
Lemma lem5376640 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5376641 : term87 = term88.
Proof. exact (MK_COMB (@lem5376640) (@lem5376639)). Qed.
Lemma lem5376642 (s : nat -> Prop) : (term65 s) = (term54 s).
Proof. exact (eq_refl (term65 s)). Qed.
Lemma lem5376643 (s : nat -> Prop) : (term55 s) = (term55 s).
Proof. exact (eq_refl (term55 s)). Qed.
Lemma lem5376644 (s : nat -> Prop) : (term89 s) = (term57 s).
Proof. exact (MK_COMB (@lem5376643 s) (@lem5376642 s)). Qed.
Lemma lem5376645 : term90 = term91.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5376644 s)). Qed.
Lemma lem5376646 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5376647 : term92 = term93.
Proof. exact (MK_COMB (@lem5376646) (@lem5376645)). Qed.
Lemma lem5376648 : term59 = term94.
Proof. exact (MK_COMB (@lem5376641) (@lem5376647)). Qed.
Lemma lem5376649 : term94.
Proof. exact (EQ_MP (@lem5376648) (@lem5376620)). Qed.
Lemma lem5376663 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5376513 A x (@lem5376512 A x)). Qed.
Lemma lem5376664 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem5376663 nat x). Qed.
Lemma lem5376665 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5376666 (x : nat) : (term95 x) = (imp False).
Proof. exact (MK_COMB (@lem5376665) (@lem5376664 x)). Qed.
Lemma lem5376667 (x : nat) (n : nat) : (Peano.le x n) = (Peano.le x n).
Proof. exact (eq_refl (Peano.le x n)). Qed.
Lemma lem5376668 (x : nat) (n : nat) : (term96 x n) = (term97 x n).
Proof. exact (MK_COMB (@lem5376666 x) (@lem5376667 x n)). Qed.
Lemma lem5376670 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5376671 (x : nat) (n : nat) : (term97 x n) = True.
Proof. exact (@lem5376670 (Peano.le x n)). Qed.
Lemma lem5376672 (x : nat) (n : nat) : (term96 x n) = True.
Proof. exact (TRANS (@lem5376668 x n) (@lem5376671 x n)). Qed.
Lemma lem5376673 (n : nat) : (term98 n) = term99.
Proof. exact (fun_ext (fun x : nat => @lem5376672 x n)). Qed.
Lemma lem5376674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376675 (n : nat) : (term100 n) = term101.
Proof. exact (MK_COMB (@lem5376674) (@lem5376673 n)). Qed.
Lemma lem5376677 {A : Type'} (t : Prop) : (term102 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5376678 (t : Prop) : (term103 t) = t.
Proof. exact (@lem5376677 nat t). Qed.
Lemma lem5376679 : term101 = True.
Proof. exact (@lem5376678 True). Qed.
Lemma lem5376680 (n : nat) : (term100 n) = True.
Proof. exact (TRANS (@lem5376675 n) (@lem5376679)). Qed.
Lemma lem5376681 : term104 = term99.
Proof. exact (fun_ext (fun n : nat => @lem5376680 n)). Qed.
Lemma lem5376682 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5376683 : term62 = term105.
Proof. exact (MK_COMB (@lem5376682) (@lem5376681)). Qed.
Lemma lem5376685 {A : Type'} (t : Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem5376686 (t : Prop) : (term107 t) = t.
Proof. exact (@lem5376685 nat t). Qed.
Lemma lem5376687 : term105 = True.
Proof. exact (@lem5376686 True). Qed.
Lemma lem5376688 : term62 = True.
Proof. exact (TRANS (@lem5376683) (@lem5376687)). Qed.
Lemma lem5376689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5376690 : term64 = (and True).
Proof. exact (MK_COMB (@lem5376689) (@lem5376688)). Qed.
Lemma lem5376726 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (EQ_MP (@lem5376522 A y x s) (@lem5376521 A y x s)). Qed.
Lemma lem5376727 (y : nat) (x : nat) (s : nat -> Prop) : (term108 x y s) = (term109 y x s).
Proof. exact (@lem5376726 nat y x s). Qed.
Lemma lem5376728 (x : nat) (x' : nat) (s : nat -> Prop) : (term108 x' x s) = (term109 x x' s).
Proof. exact (@lem5376727 x x' s). Qed.
Lemma lem5376733 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5376734 (x : nat) (x' : nat) (s : nat -> Prop) : (term110 x' x s) = (term111 x x' s).
Proof. exact (MK_COMB (@lem5376733) (@lem5376728 x x' s)). Qed.
Lemma lem5376735 (x' : nat) (n : nat) : (Peano.le x' n) = (Peano.le x' n).
Proof. exact (eq_refl (Peano.le x' n)). Qed.
Lemma lem5376736 (x : nat) (s : nat -> Prop) (x' : nat) (n : nat) : (term112 x s x' n) = (term113 x s x' n).
Proof. exact (MK_COMB (@lem5376734 x x' s) (@lem5376735 x' n)). Qed.
Lemma lem5376739 (x : nat) (s : nat -> Prop) (n : nat) : (term114 x s n) = (term115 x s n).
Proof. exact (fun_ext (fun x' : nat => @lem5376736 x s x' n)). Qed.
Lemma lem5376740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376741 (x : nat) (s : nat -> Prop) (n : nat) : (term116 x s n) = (term117 x s n).
Proof. exact (MK_COMB (@lem5376740) (@lem5376739 x s n)). Qed.
Lemma lem5376746 (x : nat) (s : nat -> Prop) : (term118 x s) = (term119 x s).
Proof. exact (fun_ext (fun n : nat => @lem5376741 x s n)). Qed.
Lemma lem5376747 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5376748 (x : nat) (s : nat -> Prop) : (term74 x s) = (term120 x s).
Proof. exact (MK_COMB (@lem5376747) (@lem5376746 x s)). Qed.
Lemma lem5376753 (x : nat) (s : nat -> Prop) : (term72 x s) = (term72 x s).
Proof. exact (eq_refl (term72 x s)). Qed.
Lemma lem5376754 (x : nat) (s : nat -> Prop) : (term76 x s) = (term121 x s).
Proof. exact (MK_COMB (@lem5376753 x s) (@lem5376748 x s)). Qed.
Lemma lem5376757 (x : nat) : (term78 x) = (term122 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5376754 x s)). Qed.
Lemma lem5376758 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5376759 (x : nat) : (term80 x) = (term123 x).
Proof. exact (MK_COMB (@lem5376758) (@lem5376757 x)). Qed.
Lemma lem5376764 : term82 = term124.
Proof. exact (fun_ext (fun x : nat => @lem5376759 x)). Qed.
Lemma lem5376765 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376766 : term84 = term125.
Proof. exact (MK_COMB (@lem5376765) (@lem5376764)). Qed.
Lemma lem5376771 : term86 = term126.
Proof. exact (MK_COMB (@lem5376690) (@lem5376766)). Qed.
Lemma lem5376773 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5376774 : term126 = term125.
Proof. exact (@lem5376773 term125). Qed.
Lemma lem5376813 : term86 = term125.
Proof. exact (TRANS (@lem5376771) (@lem5376774)). Qed.
Lemma lem5376814 : term125 = term86.
Proof. exact (SYM (@lem5376813)). Qed.
Lemma lem5376816 (p : Prop) : p = (term127 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5376817 : term125 = term128.
Proof. exact (@lem5376816 term125). Qed.
Lemma lem5376818 : term128 = term125.
Proof. exact (SYM (@lem5376817)). Qed.
Lemma lem5376819 (h1 : term129) : term129.
Proof. exact (h1). Qed.
Lemma lem5376822 (h1 : term130) : term130.
Proof. exact (h1). Qed.
Lemma lem5376823 : term131.
Proof. exact (fun h0 : term130 => @lem5376822 h0). Qed.
Lemma lem5376824 (h1 : term131) : term131.
Proof. exact (h1). Qed.
Lemma lem5376825 (h1 : term130) : term130.
Proof. exact (h1). Qed.
Lemma lem5376826 (h1 : term130) (h2 : term131) : term130.
Proof. exact (@lem5376824 h2 (@lem5376825 h1)). Qed.
Lemma lem5376827 (h1 : term130) : term132.
Proof. exact (fun h0 : term131 => @lem5376826 h1 h0). Qed.
Lemma lem5376828 (h1 : term131) : term131.
Proof. exact (h1). Qed.
Lemma lem5376829 (h1 : term130) (h2 : term131) : term130.
Proof. exact (@lem5376827 h1 (@lem5376828 h2)). Qed.
Lemma lem5376830 (h1 : term131) : term131.
Proof. exact (fun h0 : term130 => @lem5376829 h0 h1). Qed.
Lemma lem5376831 : term133.
Proof. exact (fun h0 : term131 => @lem5376830 h0). Qed.
Lemma lem5376834 : term131.
Proof. exact (@lem5376831 (@lem5376823)). Qed.
Lemma lem5376898 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5376899 : term134 = term135.
Proof. exact (@lem5376898 term136). Qed.
Lemma lem5376954 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem5376955 : term138 = term139.
Proof. exact (MK_COMB (@lem5376954) (@lem5376899)). Qed.
Lemma lem5376958 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem5376959 : term141 = term142.
Proof. exact (MK_COMB (@lem5376958) (@lem5376955)). Qed.
Lemma lem5376962 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5376969 : term130 = term144.
Proof. exact (MK_COMB (@lem5376962) (@lem5376959)). Qed.
Lemma lem5376974 (n : nat) (m : nat) : (term145 n m) = (term145 n m).
Proof. exact (eq_refl (term145 n m)). Qed.
Lemma lem5376975 (m : nat) : (term146 m) = (term146 m).
Proof. exact (fun_ext (fun n : nat => @lem5376974 n m)). Qed.
Lemma lem5376976 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376977 (m : nat) : (term147 m) = (term147 m).
Proof. exact (MK_COMB (@lem5376976) (@lem5376975 m)). Qed.
Lemma lem5376978 : term148 = term148.
Proof. exact (fun_ext (fun m : nat => @lem5376977 m)). Qed.
Lemma lem5376979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376980 : term136 = term136.
Proof. exact (MK_COMB (@lem5376979) (@lem5376978)). Qed.
Lemma lem5376981 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5376982 : term135 = term135.
Proof. exact (MK_COMB (@lem5376981) (@lem5376980)). Qed.
Lemma lem5376983 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5376984 : term149 = term149.
Proof. exact (fun_ext (fun n : nat => @lem5376983 n)). Qed.
Lemma lem5376985 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376986 : term150 = term150.
Proof. exact (MK_COMB (@lem5376985) (@lem5376984)). Qed.
Lemma lem5376987 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5376988 : term137 = term137.
Proof. exact (MK_COMB (@lem5376987) (@lem5376986)). Qed.
Lemma lem5376989 : term139 = term139.
Proof. exact (MK_COMB (@lem5376988) (@lem5376982)). Qed.
Lemma lem5376998 (n : nat) (m : nat) (p : nat) : (term151 n m p) = (term151 n m p).
Proof. exact (eq_refl (term151 n m p)). Qed.
Lemma lem5376999 (n : nat) (m : nat) : (term152 n m) = (term152 n m).
Proof. exact (fun_ext (fun p : nat => @lem5376998 n m p)). Qed.
Lemma lem5377000 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377001 (n : nat) (m : nat) : (term153 n m) = (term153 n m).
Proof. exact (MK_COMB (@lem5377000) (@lem5376999 n m)). Qed.
Lemma lem5377002 (m : nat) : (term154 m) = (term154 m).
Proof. exact (fun_ext (fun n : nat => @lem5377001 n m)). Qed.
Lemma lem5377003 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377004 (m : nat) : (term155 m) = (term155 m).
Proof. exact (MK_COMB (@lem5377003) (@lem5377002 m)). Qed.
Lemma lem5377005 : term156 = term156.
Proof. exact (fun_ext (fun m : nat => @lem5377004 m)). Qed.
Lemma lem5377006 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377007 : term157 = term157.
Proof. exact (MK_COMB (@lem5377006) (@lem5377005)). Qed.
Lemma lem5377008 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5377009 : term140 = term140.
Proof. exact (MK_COMB (@lem5377008) (@lem5377007)). Qed.
Lemma lem5377010 : term142 = term142.
Proof. exact (MK_COMB (@lem5377009) (@lem5376989)). Qed.
Lemma lem5377019 (x : nat) (s : nat -> Prop) (x' : nat) (n : nat) : (term113 x s x' n) = (term113 x s x' n).
Proof. exact (eq_refl (term113 x s x' n)). Qed.
Lemma lem5377020 (x : nat) (s : nat -> Prop) (n : nat) : (term115 x s n) = (term115 x s n).
Proof. exact (fun_ext (fun x' : nat => @lem5377019 x s x' n)). Qed.
Lemma lem5377021 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377022 (x : nat) (s : nat -> Prop) (n : nat) : (term117 x s n) = (term117 x s n).
Proof. exact (MK_COMB (@lem5377021) (@lem5377020 x s n)). Qed.
Lemma lem5377023 (x : nat) (s : nat -> Prop) : (term119 x s) = (term119 x s).
Proof. exact (fun_ext (fun n : nat => @lem5377022 x s n)). Qed.
Lemma lem5377024 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377025 (x : nat) (s : nat -> Prop) : (term120 x s) = (term120 x s).
Proof. exact (MK_COMB (@lem5377024) (@lem5377023 x s)). Qed.
Lemma lem5377032 (x : nat) (s : nat -> Prop) : (term68 x s) = (term68 x s).
Proof. exact (eq_refl (term68 x s)). Qed.
Lemma lem5377037 (s : nat -> Prop) (x : nat) (n : nat) : (term47 s x n) = (term47 s x n).
Proof. exact (eq_refl (term47 s x n)). Qed.
Lemma lem5377038 (s : nat -> Prop) (n : nat) : (term49 s n) = (term49 s n).
Proof. exact (fun_ext (fun x : nat => @lem5377037 s x n)). Qed.
Lemma lem5377039 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377040 (s : nat -> Prop) (n : nat) : (term50 s n) = (term50 s n).
Proof. exact (MK_COMB (@lem5377039) (@lem5377038 s n)). Qed.
Lemma lem5377041 (s : nat -> Prop) : (term52 s) = (term52 s).
Proof. exact (fun_ext (fun n : nat => @lem5377040 s n)). Qed.
Lemma lem5377042 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377043 (s : nat -> Prop) : (term54 s) = (term54 s).
Proof. exact (MK_COMB (@lem5377042) (@lem5377041 s)). Qed.
Lemma lem5377044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5377045 (s : nat -> Prop) : (term67 s) = (term67 s).
Proof. exact (MK_COMB (@lem5377044) (@lem5377043 s)). Qed.
Lemma lem5377046 (x : nat) (s : nat -> Prop) : (term70 x s) = (term70 x s).
Proof. exact (MK_COMB (@lem5377045 s) (@lem5377032 x s)). Qed.
Lemma lem5377047 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5377048 (x : nat) (s : nat -> Prop) : (term72 x s) = (term72 x s).
Proof. exact (MK_COMB (@lem5377047) (@lem5377046 x s)). Qed.
Lemma lem5377049 (x : nat) (s : nat -> Prop) : (term121 x s) = (term121 x s).
Proof. exact (MK_COMB (@lem5377048 x s) (@lem5377025 x s)). Qed.
Lemma lem5377050 (x : nat) : (term122 x) = (term122 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5377049 x s)). Qed.
Lemma lem5377051 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5377052 (x : nat) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem5377051) (@lem5377050 x)). Qed.
Lemma lem5377053 : term124 = term124.
Proof. exact (fun_ext (fun x : nat => @lem5377052 x)). Qed.
Lemma lem5377054 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377055 : term125 = term125.
Proof. exact (MK_COMB (@lem5377054) (@lem5377053)). Qed.
Lemma lem5377056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5377057 : term129 = term129.
Proof. exact (MK_COMB (@lem5377056) (@lem5377055)). Qed.
Lemma lem5377058 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5377059 : term143 = term143.
Proof. exact (MK_COMB (@lem5377058) (@lem5377057)). Qed.
Lemma lem5377060 : term144 = term144.
Proof. exact (MK_COMB (@lem5377059) (@lem5377010)). Qed.
Lemma lem5377159 : term130 = term144.
Proof. exact (TRANS (@lem5376969) (@lem5377060)). Qed.
Lemma lem5377160 : term144 = term130.
Proof. exact (SYM (@lem5377159)). Qed.
Lemma lem5377161 (h1 : term129) : term129.
Proof. exact (h1). Qed.
Lemma lem5377162 (h1 : term157) : term157.
Proof. exact (h1). Qed.
Lemma lem5377163 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem5377164 (h1 : term136) : term136.
Proof. exact (h1). Qed.
Lemma lem5377171 (s : nat -> Prop) (x : nat) (n : nat) : (term47 s x n) = (term158 s x n).
Proof. exact (@lem17265 (@IN nat x s) (Peano.le x n)). Qed.
Lemma lem5377172 (s : nat -> Prop) (n : nat) : (term49 s n) = (term159 s n).
Proof. exact (fun_ext (fun x : nat => @lem5377171 s x n)). Qed.
Lemma lem5377173 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377174 (s : nat -> Prop) (n : nat) : (term50 s n) = (term160 s n).
Proof. exact (MK_COMB (@lem5377173) (@lem5377172 s n)). Qed.
Lemma lem5377175 (s : nat -> Prop) : (term52 s) = (term161 s).
Proof. exact (fun_ext (fun n : nat => @lem5377174 s n)). Qed.
Lemma lem5377176 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377177 (s : nat -> Prop) : (term54 s) = (term162 s).
Proof. exact (MK_COMB (@lem5377176) (@lem5377175 s)). Qed.
Lemma lem5377182 (x : nat) (s : nat -> Prop) : (term68 x s) = (term68 x s).
Proof. exact (eq_refl (term68 x s)). Qed.
Lemma lem5377183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5377184 (s : nat -> Prop) : (term67 s) = (term163 s).
Proof. exact (MK_COMB (@lem5377183) (@lem5377177 s)). Qed.
Lemma lem5377185 (x : nat) (s : nat -> Prop) : (term70 x s) = (term164 x s).
Proof. exact (MK_COMB (@lem5377184 s) (@lem5377182 x s)). Qed.
Lemma lem5377196 (x : nat) (s : nat -> Prop) (x' : nat) (n : nat) : (term165 x s x' n) = (term166 x s x' n).
Proof. exact (@lem17362 (term109 x x' s) (Peano.le x' n)). Qed.
Lemma lem5377197 (P : nat -> Prop) : (term167 P) = (term168 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5377198 (x : nat) (s : nat -> Prop) (n : nat) : (term169 x s n) = (term170 x s n).
Proof. exact (@lem5377197 (term115 x s n)). Qed.
Lemma lem5377199 (x : nat) (s : nat -> Prop) (x' : nat) (n : nat) : (term171 x s n x') = (term113 x s x' n).
Proof. exact (eq_refl (term171 x s n x')). Qed.
Lemma lem5377200 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5377201 (x : nat) (s : nat -> Prop) (x' : nat) (n : nat) : (term172 x s n x') = (term165 x s x' n).
Proof. exact (MK_COMB (@lem5377200) (@lem5377199 x s x' n)). Qed.
Lemma lem5377202 (x : nat) (s : nat -> Prop) (x' : nat) (n : nat) : (term172 x s n x') = (term166 x s x' n).
Proof. exact (TRANS (@lem5377201 x s x' n) (@lem5377196 x s x' n)). Qed.
Lemma lem5377203 (x : nat) (s : nat -> Prop) (n : nat) : (term173 x s n) = (term174 x s n).
Proof. exact (fun_ext (fun x' : nat => @lem5377202 x s x' n)). Qed.
Lemma lem5377204 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377205 (x : nat) (s : nat -> Prop) (n : nat) : (term170 x s n) = (term175 x s n).
Proof. exact (MK_COMB (@lem5377204) (@lem5377203 x s n)). Qed.
Lemma lem5377206 (x : nat) (s : nat -> Prop) (n : nat) : (term169 x s n) = (term175 x s n).
Proof. exact (TRANS (@lem5377198 x s n) (@lem5377205 x s n)). Qed.
Lemma lem5377207 (P : nat -> Prop) : (term176 P) = (term177 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem5377208 (x : nat) (s : nat -> Prop) : (term178 x s) = (term179 x s).
Proof. exact (@lem5377207 (term119 x s)). Qed.
Lemma lem5377209 (x : nat) (s : nat -> Prop) (n : nat) : (term180 x s n) = (term117 x s n).
Proof. exact (eq_refl (term180 x s n)). Qed.
Lemma lem5377210 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5377211 (x : nat) (s : nat -> Prop) (n : nat) : (term181 x s n) = (term169 x s n).
Proof. exact (MK_COMB (@lem5377210) (@lem5377209 x s n)). Qed.
Lemma lem5377212 (x : nat) (s : nat -> Prop) (n : nat) : (term181 x s n) = (term175 x s n).
Proof. exact (TRANS (@lem5377211 x s n) (@lem5377206 x s n)). Qed.
Lemma lem5377213 (x : nat) (s : nat -> Prop) : (term182 x s) = (term183 x s).
Proof. exact (fun_ext (fun n : nat => @lem5377212 x s n)). Qed.
Lemma lem5377214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377215 (x : nat) (s : nat -> Prop) : (term179 x s) = (term184 x s).
Proof. exact (MK_COMB (@lem5377214) (@lem5377213 x s)). Qed.
Lemma lem5377216 (x : nat) (s : nat -> Prop) : (term178 x s) = (term184 x s).
Proof. exact (TRANS (@lem5377208 x s) (@lem5377215 x s)). Qed.
Lemma lem5377217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5377218 (x : nat) (s : nat -> Prop) : (term185 x s) = (term186 x s).
Proof. exact (MK_COMB (@lem5377217) (@lem5377185 x s)). Qed.
Lemma lem5377219 (x : nat) (s : nat -> Prop) : (term187 x s) = (term188 x s).
Proof. exact (MK_COMB (@lem5377218 x s) (@lem5377216 x s)). Qed.
Lemma lem5377220 (x : nat) (s : nat -> Prop) : (term189 x s) = (term187 x s).
Proof. exact (@lem17362 (term70 x s) (term120 x s)). Qed.
Lemma lem5377221 (x : nat) (s : nat -> Prop) : (term189 x s) = (term188 x s).
Proof. exact (TRANS (@lem5377220 x s) (@lem5377219 x s)). Qed.
Lemma lem5377222 (P : type993) : (term190 P) = (term191 P).
Proof. exact (@lem18392 (nat -> Prop) P). Qed.
Lemma lem5377223 (x : nat) : (term192 x) = (term193 x).
Proof. exact (@lem5377222 (term122 x)). Qed.
Lemma lem5377224 (x : nat) (s : nat -> Prop) : (term194 x s) = (term121 x s).
Proof. exact (eq_refl (term194 x s)). Qed.
Lemma lem5377225 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5377226 (x : nat) (s : nat -> Prop) : (term195 x s) = (term189 x s).
Proof. exact (MK_COMB (@lem5377225) (@lem5377224 x s)). Qed.
Lemma lem5377227 (x : nat) (s : nat -> Prop) : (term195 x s) = (term188 x s).
Proof. exact (TRANS (@lem5377226 x s) (@lem5377221 x s)). Qed.
Lemma lem5377228 (x : nat) : (term196 x) = (term197 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5377227 x s)). Qed.
Lemma lem5377229 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem5377230 (x : nat) : (term193 x) = (term198 x).
Proof. exact (MK_COMB (@lem5377229) (@lem5377228 x)). Qed.
Lemma lem5377231 (x : nat) : (term192 x) = (term198 x).
Proof. exact (TRANS (@lem5377223 x) (@lem5377230 x)). Qed.
Lemma lem5377232 (P : nat -> Prop) : (term167 P) = (term168 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5377233 : term129 = term199.
Proof. exact (@lem5377232 term124). Qed.
Lemma lem5377234 (x : nat) : (term200 x) = (term123 x).
Proof. exact (eq_refl (term200 x)). Qed.
Lemma lem5377235 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5377236 (x : nat) : (term201 x) = (term192 x).
Proof. exact (MK_COMB (@lem5377235) (@lem5377234 x)). Qed.
Lemma lem5377237 (x : nat) : (term201 x) = (term198 x).
Proof. exact (TRANS (@lem5377236 x) (@lem5377231 x)). Qed.
Lemma lem5377238 : term202 = term203.
Proof. exact (fun_ext (fun x : nat => @lem5377237 x)). Qed.
Lemma lem5377239 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377240 : term199 = term204.
Proof. exact (MK_COMB (@lem5377239) (@lem5377238)). Qed.
Lemma lem5377241 : term129 = term204.
Proof. exact (TRANS (@lem5377233) (@lem5377240)). Qed.
Lemma lem5377400 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5377401 (P : nat -> Prop) (Q : Prop) : (term207 P Q) = (term208 P Q).
Proof. exact (@lem5377400 nat P Q). Qed.
Lemma lem5377402 (x : nat) (s : nat -> Prop) : (term209 x s) = (term210 x s).
Proof. exact (@lem5377401 (term161 s) (term68 x s)). Qed.
Lemma lem5377403 (s : nat -> Prop) (n : nat) : (term211 s n) = (term160 s n).
Proof. exact (eq_refl (term211 s n)). Qed.
Lemma lem5377404 (s : nat -> Prop) : (term212 s) = (term161 s).
Proof. exact (fun_ext (fun n : nat => @lem5377403 s n)). Qed.
Lemma lem5377405 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377406 (s : nat -> Prop) : (term213 s) = (term162 s).
Proof. exact (MK_COMB (@lem5377405) (@lem5377404 s)). Qed.
Lemma lem5377407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5377408 (s : nat -> Prop) : (term214 s) = (term163 s).
Proof. exact (MK_COMB (@lem5377407) (@lem5377406 s)). Qed.
Lemma lem5377409 (x : nat) (s : nat -> Prop) : (term68 x s) = (term68 x s).
Proof. exact (eq_refl (term68 x s)). Qed.
Lemma lem5377410 (x : nat) (s : nat -> Prop) : (term209 x s) = (term164 x s).
Proof. exact (MK_COMB (@lem5377408 s) (@lem5377409 x s)). Qed.
Lemma lem5377411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5377412 (x : nat) (s : nat -> Prop) : (term215 x s) = (term216 x s).
Proof. exact (MK_COMB (@lem5377411) (@lem5377410 x s)). Qed.
Lemma lem5377413 (s : nat -> Prop) (n : nat) : (term211 s n) = (term160 s n).
Proof. exact (eq_refl (term211 s n)). Qed.
Lemma lem5377414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5377415 (s : nat -> Prop) (n : nat) : (term217 s n) = (term218 s n).
Proof. exact (MK_COMB (@lem5377414) (@lem5377413 s n)). Qed.
Lemma lem5377416 (x : nat) (s : nat -> Prop) : (term68 x s) = (term68 x s).
Proof. exact (eq_refl (term68 x s)). Qed.
Lemma lem5377417 (n : nat) (x : nat) (s : nat -> Prop) : (term219 n x s) = (term220 n x s).
Proof. exact (MK_COMB (@lem5377415 s n) (@lem5377416 x s)). Qed.
Lemma lem5377418 (x : nat) (s : nat -> Prop) : (term221 x s) = (term222 x s).
Proof. exact (fun_ext (fun n : nat => @lem5377417 n x s)). Qed.
Lemma lem5377419 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377420 (x : nat) (s : nat -> Prop) : (term210 x s) = (term223 x s).
Proof. exact (MK_COMB (@lem5377419) (@lem5377418 x s)). Qed.
Lemma lem5377421 (x : nat) (s : nat -> Prop) : ((term209 x s) = (term210 x s)) = ((term164 x s) = (term223 x s)).
Proof. exact (MK_COMB (@lem5377412 x s) (@lem5377420 x s)). Qed.
Lemma lem5377422 (x : nat) (s : nat -> Prop) : (term164 x s) = (term223 x s).
Proof. exact (EQ_MP (@lem5377421 x s) (@lem5377402 x s)). Qed.
Lemma lem5377423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5377424 (x : nat) (s : nat -> Prop) : (term186 x s) = (term224 x s).
Proof. exact (MK_COMB (@lem5377423) (@lem5377422 x s)). Qed.
Lemma lem5377426 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5377427 (P : type1605) : (term227 P) = (term228 P).
Proof. exact (@lem5377426 nat nat P). Qed.
Lemma lem5377428 (x : nat) (s : nat -> Prop) : (term229 x s) = (term230 x s).
Proof. exact (@lem5377427 (term231 x s)). Qed.
Lemma lem5377429 (x : nat) (s : nat -> Prop) (n : nat) : (term232 x s n) = (term174 x s n).
Proof. exact (eq_refl (term232 x s n)). Qed.
Lemma lem5377430 (x' : nat) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5377431 (x : nat) (s : nat -> Prop) (n : nat) (x' : nat) : (term233 x s n x') = (term234 x s n x').
Proof. exact (MK_COMB (@lem5377429 x s n) (@lem5377430 x')). Qed.
Lemma lem5377432 (x : nat) (s : nat -> Prop) (x' : nat) (n : nat) : (term234 x s n x') = (term166 x s x' n).
Proof. exact (eq_refl (term234 x s n x')). Qed.
Lemma lem5377433 (x : nat) (s : nat -> Prop) (x' : nat) (n : nat) : (term233 x s n x') = (term166 x s x' n).
Proof. exact (TRANS (@lem5377431 x s n x') (@lem5377432 x s x' n)). Qed.
Lemma lem5377434 (x : nat) (s : nat -> Prop) (n : nat) : (term235 x s n) = (term174 x s n).
Proof. exact (fun_ext (fun x' : nat => @lem5377433 x s x' n)). Qed.
Lemma lem5377435 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377436 (x : nat) (s : nat -> Prop) (n : nat) : (term236 x s n) = (term175 x s n).
Proof. exact (MK_COMB (@lem5377435) (@lem5377434 x s n)). Qed.
Lemma lem5377437 (x : nat) (s : nat -> Prop) : (term237 x s) = (term183 x s).
Proof. exact (fun_ext (fun n : nat => @lem5377436 x s n)). Qed.
Lemma lem5377438 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377439 (x : nat) (s : nat -> Prop) : (term229 x s) = (term184 x s).
Proof. exact (MK_COMB (@lem5377438) (@lem5377437 x s)). Qed.
Lemma lem5377440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5377441 (x : nat) (s : nat -> Prop) : (term238 x s) = (term239 x s).
Proof. exact (MK_COMB (@lem5377440) (@lem5377439 x s)). Qed.
Lemma lem5377442 (x : nat) (s : nat -> Prop) (n : nat) : (term232 x s n) = (term174 x s n).
Proof. exact (eq_refl (term232 x s n)). Qed.
Lemma lem5377443 (x' : nat -> nat) (n : nat) : (x' n) = (x' n).
Proof. exact (eq_refl (x' n)). Qed.
Lemma lem5377444 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (n : nat) : (term240 x s x' n) = (term241 x s x' n).
Proof. exact (MK_COMB (@lem5377442 x s n) (@lem5377443 x' n)). Qed.
Lemma lem5377445 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (n : nat) : (term241 x s x' n) = (term242 x s x' n).
Proof. exact (eq_refl (term241 x s x' n)). Qed.
Lemma lem5377446 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (n : nat) : (term240 x s x' n) = (term242 x s x' n).
Proof. exact (TRANS (@lem5377444 x s x' n) (@lem5377445 x s x' n)). Qed.
Lemma lem5377447 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term243 x s x') = (term244 x s x').
Proof. exact (fun_ext (fun n : nat => @lem5377446 x s x' n)). Qed.
Lemma lem5377448 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377449 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term245 x s x') = (term246 x s x').
Proof. exact (MK_COMB (@lem5377448) (@lem5377447 x s x')). Qed.
Lemma lem5377450 (x : nat) (s : nat -> Prop) : (term247 x s) = (term248 x s).
Proof. exact (fun_ext (fun x' : nat -> nat => @lem5377449 x s x')). Qed.
Lemma lem5377451 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem5377452 (x : nat) (s : nat -> Prop) : (term230 x s) = (term249 x s).
Proof. exact (MK_COMB (@lem5377451) (@lem5377450 x s)). Qed.
Lemma lem5377453 (x : nat) (s : nat -> Prop) : ((term229 x s) = (term230 x s)) = ((term184 x s) = (term249 x s)).
Proof. exact (MK_COMB (@lem5377441 x s) (@lem5377452 x s)). Qed.
Lemma lem5377454 (x : nat) (s : nat -> Prop) : (term184 x s) = (term249 x s).
Proof. exact (EQ_MP (@lem5377453 x s) (@lem5377428 x s)). Qed.
Lemma lem5377455 (x : nat) (s : nat -> Prop) : (term188 x s) = (term250 x s).
Proof. exact (MK_COMB (@lem5377424 x s) (@lem5377454 x s)). Qed.
Lemma lem5377457 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5377458 (P : nat -> Prop) (Q : Prop) : (term207 P Q) = (term208 P Q).
Proof. exact (@lem5377457 nat P Q). Qed.
Lemma lem5377459 (x : nat) (s : nat -> Prop) : (term251 x s) = (term252 x s).
Proof. exact (@lem5377458 (term222 x s) (term249 x s)). Qed.
Lemma lem5377460 (n : nat) (x : nat) (s : nat -> Prop) : (term253 x s n) = (term220 n x s).
Proof. exact (eq_refl (term253 x s n)). Qed.
Lemma lem5377461 (x : nat) (s : nat -> Prop) : (term254 x s) = (term222 x s).
Proof. exact (fun_ext (fun n : nat => @lem5377460 n x s)). Qed.
Lemma lem5377462 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377463 (x : nat) (s : nat -> Prop) : (term255 x s) = (term223 x s).
Proof. exact (MK_COMB (@lem5377462) (@lem5377461 x s)). Qed.
Lemma lem5377464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5377465 (x : nat) (s : nat -> Prop) : (term256 x s) = (term224 x s).
Proof. exact (MK_COMB (@lem5377464) (@lem5377463 x s)). Qed.
Lemma lem5377466 (x : nat) (s : nat -> Prop) : (term249 x s) = (term249 x s).
Proof. exact (eq_refl (term249 x s)). Qed.
Lemma lem5377467 (x : nat) (s : nat -> Prop) : (term251 x s) = (term250 x s).
Proof. exact (MK_COMB (@lem5377465 x s) (@lem5377466 x s)). Qed.
Lemma lem5377468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5377469 (x : nat) (s : nat -> Prop) : (term257 x s) = (term258 x s).
Proof. exact (MK_COMB (@lem5377468) (@lem5377467 x s)). Qed.
Lemma lem5377470 (n : nat) (x : nat) (s : nat -> Prop) : (term253 x s n) = (term220 n x s).
Proof. exact (eq_refl (term253 x s n)). Qed.
Lemma lem5377471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5377472 (n : nat) (x : nat) (s : nat -> Prop) : (term259 x s n) = (term260 n x s).
Proof. exact (MK_COMB (@lem5377471) (@lem5377470 n x s)). Qed.
Lemma lem5377473 (x : nat) (s : nat -> Prop) : (term249 x s) = (term249 x s).
Proof. exact (eq_refl (term249 x s)). Qed.
Lemma lem5377474 (n : nat) (x : nat) (s : nat -> Prop) : (term261 n x s) = (term262 n x s).
Proof. exact (MK_COMB (@lem5377472 n x s) (@lem5377473 x s)). Qed.
Lemma lem5377475 (x : nat) (s : nat -> Prop) : (term263 x s) = (term264 x s).
Proof. exact (fun_ext (fun n : nat => @lem5377474 n x s)). Qed.
Lemma lem5377476 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377477 (x : nat) (s : nat -> Prop) : (term252 x s) = (term265 x s).
Proof. exact (MK_COMB (@lem5377476) (@lem5377475 x s)). Qed.
Lemma lem5377478 (x : nat) (s : nat -> Prop) : ((term251 x s) = (term252 x s)) = ((term250 x s) = (term265 x s)).
Proof. exact (MK_COMB (@lem5377469 x s) (@lem5377477 x s)). Qed.
Lemma lem5377479 (x : nat) (s : nat -> Prop) : (term250 x s) = (term265 x s).
Proof. exact (EQ_MP (@lem5377478 x s) (@lem5377459 x s)). Qed.
Lemma lem5377481 {A : Type'} (P : Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5377482 (P : Prop) (Q : type1002) : (term268 P Q) = (term269 P Q).
Proof. exact (@lem5377481 (nat -> nat) P Q). Qed.
Lemma lem5377483 (n : nat) (x : nat) (s : nat -> Prop) : (term270 n x s) = (term271 n x s).
Proof. exact (@lem5377482 (term220 n x s) (term248 x s)). Qed.
Lemma lem5377484 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term272 x s x') = (term246 x s x').
Proof. exact (eq_refl (term272 x s x')). Qed.
Lemma lem5377485 (x : nat) (s : nat -> Prop) : (term273 x s) = (term248 x s).
Proof. exact (fun_ext (fun x' : nat -> nat => @lem5377484 x s x')). Qed.
Lemma lem5377486 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem5377487 (x : nat) (s : nat -> Prop) : (term274 x s) = (term249 x s).
Proof. exact (MK_COMB (@lem5377486) (@lem5377485 x s)). Qed.
Lemma lem5377488 (n : nat) (x : nat) (s : nat -> Prop) : (term260 n x s) = (term260 n x s).
Proof. exact (eq_refl (term260 n x s)). Qed.
Lemma lem5377489 (n : nat) (x : nat) (s : nat -> Prop) : (term270 n x s) = (term262 n x s).
Proof. exact (MK_COMB (@lem5377488 n x s) (@lem5377487 x s)). Qed.
Lemma lem5377490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5377491 (n : nat) (x : nat) (s : nat -> Prop) : (term275 n x s) = (term276 n x s).
Proof. exact (MK_COMB (@lem5377490) (@lem5377489 n x s)). Qed.
Lemma lem5377492 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term272 x s x') = (term246 x s x').
Proof. exact (eq_refl (term272 x s x')). Qed.
Lemma lem5377493 (n : nat) (x : nat) (s : nat -> Prop) : (term260 n x s) = (term260 n x s).
Proof. exact (eq_refl (term260 n x s)). Qed.
Lemma lem5377494 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term277 n x s x') = (term278 n x s x').
Proof. exact (MK_COMB (@lem5377493 n x s) (@lem5377492 x s x')). Qed.
Lemma lem5377495 (n : nat) (x : nat) (s : nat -> Prop) : (term279 n x s) = (term280 n x s).
Proof. exact (fun_ext (fun x' : nat -> nat => @lem5377494 n x s x')). Qed.
Lemma lem5377496 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem5377497 (n : nat) (x : nat) (s : nat -> Prop) : (term271 n x s) = (term281 n x s).
Proof. exact (MK_COMB (@lem5377496) (@lem5377495 n x s)). Qed.
Lemma lem5377498 (n : nat) (x : nat) (s : nat -> Prop) : ((term270 n x s) = (term271 n x s)) = ((term262 n x s) = (term281 n x s)).
Proof. exact (MK_COMB (@lem5377491 n x s) (@lem5377497 n x s)). Qed.
Lemma lem5377499 (n : nat) (x : nat) (s : nat -> Prop) : (term262 n x s) = (term281 n x s).
Proof. exact (EQ_MP (@lem5377498 n x s) (@lem5377483 n x s)). Qed.
Lemma lem5377500 (x : nat) (s : nat -> Prop) : (term264 x s) = (term282 x s).
Proof. exact (fun_ext (fun n : nat => @lem5377499 n x s)). Qed.
Lemma lem5377501 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377502 (x : nat) (s : nat -> Prop) : (term265 x s) = (term283 x s).
Proof. exact (MK_COMB (@lem5377501) (@lem5377500 x s)). Qed.
Lemma lem5377503 (x : nat) (s : nat -> Prop) : (term250 x s) = (term283 x s).
Proof. exact (TRANS (@lem5377479 x s) (@lem5377502 x s)). Qed.
Lemma lem5377504 (x : nat) (s : nat -> Prop) : (term188 x s) = (term283 x s).
Proof. exact (TRANS (@lem5377455 x s) (@lem5377503 x s)). Qed.
Lemma lem5377505 (x : nat) : (term197 x) = (term284 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5377504 x s)). Qed.
Lemma lem5377506 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem5377507 (x : nat) : (term198 x) = (term285 x).
Proof. exact (MK_COMB (@lem5377506) (@lem5377505 x)). Qed.
Lemma lem5377508 : term203 = term286.
Proof. exact (fun_ext (fun x : nat => @lem5377507 x)). Qed.
Lemma lem5377509 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5377511 : term204 = term287.
Proof. exact (MK_COMB (@lem5377509) (@lem5377508)). Qed.
Lemma lem5377512 : term129 = term287.
Proof. exact (TRANS (@lem5377241) (@lem5377511)). Qed.
Lemma lem5377513 (h1 : term129) : term287.
Proof. exact (EQ_MP (@lem5377512) (@lem5377161 h1)). Qed.
Lemma lem5377520 (m : nat) (n : nat) (p : nat) : (term288 m n p) = (term289 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem5377521 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem5377522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5377523 (m : nat) (n : nat) (p : nat) : (term290 m n p) = (term291 m n p).
Proof. exact (MK_COMB (@lem5377522) (@lem5377520 m n p)). Qed.
Lemma lem5377524 (n : nat) (m : nat) (p : nat) : (term292 n m p) = (term293 n m p).
Proof. exact (MK_COMB (@lem5377523 m n p) (@lem5377521 m p)). Qed.
Lemma lem5377525 (n : nat) (m : nat) (p : nat) : (term151 n m p) = (term292 n m p).
Proof. exact (@lem17265 (term32 m n p) (Peano.le m p)). Qed.
Lemma lem5377526 (n : nat) (m : nat) (p : nat) : (term151 n m p) = (term293 n m p).
Proof. exact (TRANS (@lem5377525 n m p) (@lem5377524 n m p)). Qed.
Lemma lem5377527 (n : nat) (m : nat) : (term152 n m) = (term294 n m).
Proof. exact (fun_ext (fun p : nat => @lem5377526 n m p)). Qed.
Lemma lem5377528 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377529 (n : nat) (m : nat) : (term153 n m) = (term295 n m).
Proof. exact (MK_COMB (@lem5377528) (@lem5377527 n m)). Qed.
Lemma lem5377530 (m : nat) : (term154 m) = (term296 m).
Proof. exact (fun_ext (fun n : nat => @lem5377529 n m)). Qed.
Lemma lem5377531 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377532 (m : nat) : (term155 m) = (term297 m).
Proof. exact (MK_COMB (@lem5377531) (@lem5377530 m)). Qed.
Lemma lem5377533 : term156 = term298.
Proof. exact (fun_ext (fun m : nat => @lem5377532 m)). Qed.
Lemma lem5377534 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377595 : term157 = term299.
Proof. exact (MK_COMB (@lem5377534) (@lem5377533)). Qed.
Lemma lem5377596 (h1 : term157) : term299.
Proof. exact (EQ_MP (@lem5377595) (@lem5377162 h1)). Qed.
Lemma lem5377597 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5377598 : term149 = term149.
Proof. exact (fun_ext (fun n : nat => @lem5377597 n)). Qed.
Lemma lem5377599 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377608 : term150 = term150.
Proof. exact (MK_COMB (@lem5377599) (@lem5377598)). Qed.
Lemma lem5377609 (h1 : term150) : term150.
Proof. exact (EQ_MP (@lem5377608) (@lem5377163 h1)). Qed.
Lemma lem5377614 (n : nat) (m : nat) : (term145 n m) = (term145 n m).
Proof. exact (eq_refl (term145 n m)). Qed.
Lemma lem5377615 (m : nat) : (term146 m) = (term146 m).
Proof. exact (fun_ext (fun n : nat => @lem5377614 n m)). Qed.
Lemma lem5377616 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377617 (m : nat) : (term147 m) = (term147 m).
Proof. exact (MK_COMB (@lem5377616) (@lem5377615 m)). Qed.
Lemma lem5377618 : term148 = term148.
Proof. exact (fun_ext (fun m : nat => @lem5377617 m)). Qed.
Lemma lem5377619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377676 : term136 = term136.
Proof. exact (MK_COMB (@lem5377619) (@lem5377618)). Qed.
Lemma lem5377677 (h1 : term136) : term136.
Proof. exact (EQ_MP (@lem5377676) (@lem5377164 h1)). Qed.
Lemma lem5377678 (x : nat) (h1 : term285 x) : term285 x.
Proof. exact (h1). Qed.
Lemma lem5377679 (x : nat) (s : nat -> Prop) (h1 : term283 x s) : term283 x s.
Proof. exact (h1). Qed.
Lemma lem5377680 (n : nat) (x : nat) (s : nat -> Prop) (h1 : term281 n x s) : term281 n x s.
Proof. exact (h1). Qed.
Lemma lem5377681 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term278 n x s x'.
Proof. exact (h1). Qed.
Lemma lem5377706 (n : nat) (m : nat) (p : nat) : (term293 n m p) = (term293 n m p).
Proof. exact (eq_refl (term293 n m p)). Qed.
Lemma lem5377707 (n : nat) (m : nat) : (term294 n m) = (term294 n m).
Proof. exact (fun_ext (fun p : nat => @lem5377706 n m p)). Qed.
Lemma lem5377708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377709 (n : nat) (m : nat) : (term295 n m) = (term295 n m).
Proof. exact (MK_COMB (@lem5377708) (@lem5377707 n m)). Qed.
Lemma lem5377710 (m : nat) : (term296 m) = (term296 m).
Proof. exact (fun_ext (fun n : nat => @lem5377709 n m)). Qed.
Lemma lem5377711 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377712 (m : nat) : (term297 m) = (term297 m).
Proof. exact (MK_COMB (@lem5377711) (@lem5377710 m)). Qed.
Lemma lem5377713 : term298 = term298.
Proof. exact (fun_ext (fun m : nat => @lem5377712 m)). Qed.
Lemma lem5377714 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377715 : term299 = term299.
Proof. exact (MK_COMB (@lem5377714) (@lem5377713)). Qed.
Lemma lem5377716 (h1 : term157) : term299.
Proof. exact (EQ_MP (@lem5377715) (@lem5377596 h1)). Qed.
Lemma lem5377721 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5377722 : term149 = term149.
Proof. exact (fun_ext (fun n : nat => @lem5377721 n)). Qed.
Lemma lem5377723 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377724 : term150 = term150.
Proof. exact (MK_COMB (@lem5377723) (@lem5377722)). Qed.
Lemma lem5377725 (h1 : term150) : term150.
Proof. exact (EQ_MP (@lem5377724) (@lem5377609 h1)). Qed.
Lemma lem5377738 (n : nat) (m : nat) : (term145 n m) = (term145 n m).
Proof. exact (eq_refl (term145 n m)). Qed.
Lemma lem5377739 (m : nat) : (term146 m) = (term146 m).
Proof. exact (fun_ext (fun n : nat => @lem5377738 n m)). Qed.
Lemma lem5377740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377741 (m : nat) : (term147 m) = (term147 m).
Proof. exact (MK_COMB (@lem5377740) (@lem5377739 m)). Qed.
Lemma lem5377742 : term148 = term148.
Proof. exact (fun_ext (fun m : nat => @lem5377741 m)). Qed.
Lemma lem5377743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377744 : term136 = term136.
Proof. exact (MK_COMB (@lem5377743) (@lem5377742)). Qed.
Lemma lem5377745 (h1 : term136) : term136.
Proof. exact (EQ_MP (@lem5377744) (@lem5377677 h1)). Qed.
Lemma lem5377774 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (n : nat) : (term242 x s x' n) = (term242 x s x' n).
Proof. exact (eq_refl (term242 x s x' n)). Qed.
Lemma lem5377775 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term244 x s x') = (term244 x s x').
Proof. exact (fun_ext (fun n : nat => @lem5377774 x s x' n)). Qed.
Lemma lem5377776 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377777 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term246 x s x') = (term246 x s x').
Proof. exact (MK_COMB (@lem5377776) (@lem5377775 x s x')). Qed.
Lemma lem5377790 (x : nat) (s : nat -> Prop) : (term68 x s) = (term68 x s).
Proof. exact (eq_refl (term68 x s)). Qed.
Lemma lem5377805 (s : nat -> Prop) (x : nat) (n : nat) : (term158 s x n) = (term158 s x n).
Proof. exact (eq_refl (term158 s x n)). Qed.
Lemma lem5377806 (s : nat -> Prop) (n : nat) : (term159 s n) = (term159 s n).
Proof. exact (fun_ext (fun x : nat => @lem5377805 s x n)). Qed.
Lemma lem5377807 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377808 (s : nat -> Prop) (n : nat) : (term160 s n) = (term160 s n).
Proof. exact (MK_COMB (@lem5377807) (@lem5377806 s n)). Qed.
Lemma lem5377809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5377810 (s : nat -> Prop) (n : nat) : (term218 s n) = (term218 s n).
Proof. exact (MK_COMB (@lem5377809) (@lem5377808 s n)). Qed.
Lemma lem5377811 (n : nat) (x : nat) (s : nat -> Prop) : (term220 n x s) = (term220 n x s).
Proof. exact (MK_COMB (@lem5377810 s n) (@lem5377790 x s)). Qed.
Lemma lem5377812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5377813 (n : nat) (x : nat) (s : nat -> Prop) : (term260 n x s) = (term260 n x s).
Proof. exact (MK_COMB (@lem5377812) (@lem5377811 n x s)). Qed.
Lemma lem5377814 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term278 n x s x') = (term278 n x s x').
Proof. exact (MK_COMB (@lem5377813 n x s) (@lem5377777 x s x')). Qed.
Lemma lem5377815 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term278 n x s x'.
Proof. exact (EQ_MP (@lem5377814 n x s x') (@lem5377681 n x s x' h1)). Qed.
Lemma lem5377816 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term246 x s x'.
Proof. exact (proj2 (@lem5377815 n x s x' h1)). Qed.
Lemma lem5377817 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term220 n x s.
Proof. exact (proj1 (@lem5377815 n x s x' h1)). Qed.
Lemma lem5377819 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term160 s n.
Proof. exact (proj1 (@lem5377817 n x s x' h1)). Qed.
Lemma lem5377835 (n : nat) (m : nat) (p : nat) : (term293 n m p) = (term293 n m p).
Proof. exact (eq_refl (term293 n m p)). Qed.
Lemma lem5377836 (n : nat) (m : nat) : (term294 n m) = (term294 n m).
Proof. exact (fun_ext (fun p : nat => @lem5377835 n m p)). Qed.
Lemma lem5377837 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377838 (n : nat) (m : nat) : (term295 n m) = (term295 n m).
Proof. exact (MK_COMB (@lem5377837) (@lem5377836 n m)). Qed.
Lemma lem5377839 (m : nat) : (term296 m) = (term296 m).
Proof. exact (fun_ext (fun n : nat => @lem5377838 n m)). Qed.
Lemma lem5377840 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377841 (m : nat) : (term297 m) = (term297 m).
Proof. exact (MK_COMB (@lem5377840) (@lem5377839 m)). Qed.
Lemma lem5377842 : term298 = term298.
Proof. exact (fun_ext (fun m : nat => @lem5377841 m)). Qed.
Lemma lem5377843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377845 : term299 = term299.
Proof. exact (MK_COMB (@lem5377843) (@lem5377842)). Qed.
Lemma lem5377846 (h1 : term157) : term299.
Proof. exact (EQ_MP (@lem5377845) (@lem5377716 h1)). Qed.
Lemma lem5377848 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem5377849 : term149 = term149.
Proof. exact (fun_ext (fun n : nat => @lem5377848 n)). Qed.
Lemma lem5377850 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377852 : term150 = term150.
Proof. exact (MK_COMB (@lem5377850) (@lem5377849)). Qed.
Lemma lem5377853 (h1 : term150) : term150.
Proof. exact (EQ_MP (@lem5377852) (@lem5377725 h1)). Qed.
Lemma lem5377861 (n : nat) (m : nat) : (term145 n m) = (term145 n m).
Proof. exact (eq_refl (term145 n m)). Qed.
Lemma lem5377862 (m : nat) : (term146 m) = (term146 m).
Proof. exact (fun_ext (fun n : nat => @lem5377861 n m)). Qed.
Lemma lem5377863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377864 (m : nat) : (term147 m) = (term147 m).
Proof. exact (MK_COMB (@lem5377863) (@lem5377862 m)). Qed.
Lemma lem5377865 : term148 = term148.
Proof. exact (fun_ext (fun m : nat => @lem5377864 m)). Qed.
Lemma lem5377866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377868 : term136 = term136.
Proof. exact (MK_COMB (@lem5377866) (@lem5377865)). Qed.
Lemma lem5377869 (h1 : term136) : term136.
Proof. exact (EQ_MP (@lem5377868) (@lem5377745 h1)). Qed.
Lemma lem5377881 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (n : nat) : (term242 x s x' n) = (term242 x s x' n).
Proof. exact (eq_refl (term242 x s x' n)). Qed.
Lemma lem5377882 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term244 x s x') = (term244 x s x').
Proof. exact (fun_ext (fun n : nat => @lem5377881 x s x' n)). Qed.
Lemma lem5377883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377885 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term246 x s x') = (term246 x s x').
Proof. exact (MK_COMB (@lem5377883) (@lem5377882 x s x')). Qed.
Lemma lem5377886 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term246 x s x'.
Proof. exact (EQ_MP (@lem5377885 x s x') (@lem5377816 n x s x' h1)). Qed.
Lemma lem5377894 (s : nat -> Prop) (x : nat) (n : nat) : (term158 s x n) = (term158 s x n).
Proof. exact (eq_refl (term158 s x n)). Qed.
Lemma lem5377895 (s : nat -> Prop) (n : nat) : (term159 s n) = (term159 s n).
Proof. exact (fun_ext (fun x : nat => @lem5377894 s x n)). Qed.
Lemma lem5377896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5377898 (s : nat -> Prop) (n : nat) : (term160 s n) = (term160 s n).
Proof. exact (MK_COMB (@lem5377896) (@lem5377895 s n)). Qed.
Lemma lem5377899 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term160 s n.
Proof. exact (EQ_MP (@lem5377898 s n) (@lem5377819 n x s x' h1)). Qed.
Lemma lem5377908 (_69761 : nat) (h1 : term157) : term300 _69761.
Proof. exact (@lem5377846 h1 _69761). Qed.
Lemma lem5377909 (_69761 : nat) : (term300 _69761) = (term297 _69761).
Proof. exact (eq_refl (term300 _69761)). Qed.
Lemma lem5377910 (_69761 : nat) (h1 : term157) : term297 _69761.
Proof. exact (EQ_MP (@lem5377909 _69761) (@lem5377908 _69761 h1)). Qed.
Lemma lem5377911 (_69761 : nat) (_69762 : nat) (h1 : term157) : term301 _69761 _69762.
Proof. exact (@lem5377910 _69761 h1 _69762). Qed.
Lemma lem5377912 (_69762 : nat) (_69761 : nat) : (term301 _69761 _69762) = (term295 _69762 _69761).
Proof. exact (eq_refl (term301 _69761 _69762)). Qed.
Lemma lem5377913 (_69762 : nat) (_69761 : nat) (h1 : term157) : term295 _69762 _69761.
Proof. exact (EQ_MP (@lem5377912 _69762 _69761) (@lem5377911 _69761 _69762 h1)). Qed.
Lemma lem5377914 (_69762 : nat) (_69761 : nat) (_69763 : nat) (h1 : term157) : term302 _69762 _69761 _69763.
Proof. exact (@lem5377913 _69762 _69761 h1 _69763). Qed.
Lemma lem5377915 (_69762 : nat) (_69761 : nat) (_69763 : nat) : (term302 _69762 _69761 _69763) = (term293 _69762 _69761 _69763).
Proof. exact (eq_refl (term302 _69762 _69761 _69763)). Qed.
Lemma lem5377916 (_69762 : nat) (_69761 : nat) (_69763 : nat) (h1 : term157) : term293 _69762 _69761 _69763.
Proof. exact (EQ_MP (@lem5377915 _69762 _69761 _69763) (@lem5377914 _69762 _69761 _69763 h1)). Qed.
Lemma lem5377917 (_69764 : nat) (h1 : term150) : term303 _69764.
Proof. exact (@lem5377853 h1 _69764). Qed.
Lemma lem5377918 (_69764 : nat) : (term303 _69764) = (Peano.le _69764 _69764).
Proof. exact (eq_refl (term303 _69764)). Qed.
Lemma lem5377920 (_69765 : nat) (h1 : term136) : term304 _69765.
Proof. exact (@lem5377869 h1 _69765). Qed.
Lemma lem5377921 (_69765 : nat) : (term304 _69765) = (term147 _69765).
Proof. exact (eq_refl (term304 _69765)). Qed.
Lemma lem5377922 (_69765 : nat) (h1 : term136) : term147 _69765.
Proof. exact (EQ_MP (@lem5377921 _69765) (@lem5377920 _69765 h1)). Qed.
Lemma lem5377923 (_69765 : nat) (_69766 : nat) (h1 : term136) : term305 _69765 _69766.
Proof. exact (@lem5377922 _69765 h1 _69766). Qed.
Lemma lem5377924 (_69766 : nat) (_69765 : nat) : (term305 _69765 _69766) = (term145 _69766 _69765).
Proof. exact (eq_refl (term305 _69765 _69766)). Qed.
Lemma lem5377926 (_69767 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term306 x s x' _69767.
Proof. exact (@lem5377886 n x s x' h1 _69767). Qed.
Lemma lem5377927 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (_69767 : nat) : (term306 x s x' _69767) = (term242 x s x' _69767).
Proof. exact (eq_refl (term306 x s x' _69767)). Qed.
Lemma lem5377928 (_69767 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term242 x s x' _69767.
Proof. exact (EQ_MP (@lem5377927 x s x' _69767) (@lem5377926 _69767 n x s x' h1)). Qed.
Lemma lem5377929 (_69768 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term307 s n _69768.
Proof. exact (@lem5377899 n x s x' h1 _69768). Qed.
Lemma lem5377930 (s : nat -> Prop) (_69768 : nat) (n : nat) : (term307 s n _69768) = (term158 s _69768 n).
Proof. exact (eq_refl (term307 s n _69768)). Qed.
Lemma lem5377944 (_69762 : nat) (_69761 : nat) (_69763 : nat) : (term293 _69762 _69761 _69763) = (term308 _69762 _69761 _69763).
Proof. exact (@lem5376509 (term309 _69761 _69762) (term309 _69762 _69763) (Peano.le _69761 _69763)). Qed.
Lemma lem5377945 (_69762 : nat) (_69761 : nat) (_69763 : nat) (h1 : term157) : term308 _69762 _69761 _69763.
Proof. exact (EQ_MP (@lem5377944 _69762 _69761 _69763) (@lem5377916 _69762 _69761 _69763 h1)). Qed.
Lemma lem5377953 (_69766 : nat) (_69765 : nat) (h1 : term136) : term145 _69766 _69765.
Proof. exact (EQ_MP (@lem5377924 _69766 _69765) (@lem5377923 _69765 _69766 h1)). Qed.
Lemma lem5377959 (_69768 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term158 s _69768 n.
Proof. exact (EQ_MP (@lem5377930 s _69768 n) (@lem5377929 _69768 n x s x' h1)). Qed.
Lemma lem5377969 (_69767 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term310 x x' _69767 s.
Proof. exact (proj1 (@lem5377928 _69767 n x s x' h1)). Qed.
Lemma lem5377971 (_69767 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term311 x' _69767.
Proof. exact (proj2 (@lem5377928 _69767 n x s x' h1)). Qed.
Lemma lem5378003 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem5378004 (_69775 : nat) (_69777 : nat) (h1 : _69775 = _69777) : _69775 = _69777.
Proof. exact (h1). Qed.
Lemma lem5378005 (_69776 : nat) (_69778 : nat) (h1 : _69776 = _69778) : _69776 = _69778.
Proof. exact (h1). Qed.
Lemma lem5378006 (_69775 : nat) (_69777 : nat) (h1 : _69775 = _69777) : (Peano.le _69775) = (Peano.le _69777).
Proof. exact (MK_COMB (@lem5378003) (@lem5378004 _69775 _69777 h1)). Qed.
Lemma lem5378007 (_69775 : nat) (_69777 : nat) (_69776 : nat) (_69778 : nat) (h1 : _69775 = _69777) (h2 : _69776 = _69778) : (Peano.le _69775 _69776) = (Peano.le _69777 _69778).
Proof. exact (MK_COMB (@lem5378006 _69775 _69777 h1) (@lem5378005 _69776 _69778 h2)). Qed.
Lemma lem5378009 (b : Prop) (a : Prop) : term312 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5378010 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : term313 _69777 _69778 _69775 _69776.
Proof. exact (@lem5378009 (Peano.le _69777 _69778) (Peano.le _69775 _69776)). Qed.
Lemma lem5378011 (_69775 : nat) (_69777 : nat) (_69776 : nat) (_69778 : nat) (h1 : _69775 = _69777) (h2 : _69776 = _69778) : term314 _69777 _69778 _69775 _69776.
Proof. exact (@lem5378010 _69777 _69778 _69775 _69776 (@lem5378007 _69775 _69777 _69776 _69778 h1 h2)). Qed.
Lemma lem5378012 (_69778 : nat) (_69776 : nat) (_69775 : nat) (_69777 : nat) (h1 : _69775 = _69777) : term315 _69777 _69778 _69775 _69776.
Proof. exact (fun h0 : _69776 = _69778 => @lem5378011 _69775 _69777 _69776 _69778 h1 h0). Qed.
Lemma lem5378014 (a : Prop) (b : Prop) : (a -> b) = (term316 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5378015 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : (term315 _69777 _69778 _69775 _69776) = (term317 _69777 _69778 _69775 _69776).
Proof. exact (@lem5378014 (_69776 = _69778) (term314 _69777 _69778 _69775 _69776)). Qed.
Lemma lem5378016 (_69778 : nat) (_69776 : nat) (_69775 : nat) (_69777 : nat) (h1 : _69775 = _69777) : term317 _69777 _69778 _69775 _69776.
Proof. exact (EQ_MP (@lem5378015 _69777 _69778 _69775 _69776) (@lem5378012 _69778 _69776 _69775 _69777 h1)). Qed.
Lemma lem5378017 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : term318 _69777 _69778 _69775 _69776.
Proof. exact (fun h0 : _69775 = _69777 => @lem5378016 _69778 _69776 _69775 _69777 h0). Qed.
Lemma lem5378019 (a : Prop) (b : Prop) : (a -> b) = (term316 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5378020 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : (term318 _69777 _69778 _69775 _69776) = (term319 _69777 _69778 _69775 _69776).
Proof. exact (@lem5378019 (_69775 = _69777) (term317 _69777 _69778 _69775 _69776)). Qed.
Lemma lem5378021 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : term319 _69777 _69778 _69775 _69776.
Proof. exact (EQ_MP (@lem5378020 _69777 _69778 _69775 _69776) (@lem5378017 _69777 _69778 _69775 _69776)). Qed.
Lemma lem5378022 (x' : nat -> nat) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5378023 (_69779 : nat) (_69780 : nat) (h1 : _69779 = _69780) : _69779 = _69780.
Proof. exact (h1). Qed.
Lemma lem5378024 (x' : nat -> nat) (_69779 : nat) (_69780 : nat) (h1 : _69779 = _69780) : (x' _69779) = (x' _69780).
Proof. exact (MK_COMB (@lem5378022 x') (@lem5378023 _69779 _69780 h1)). Qed.
Lemma lem5378025 (_69779 : nat) (x' : nat -> nat) (_69780 : nat) : term320 _69779 x' _69780.
Proof. exact (fun h0 : _69779 = _69780 => @lem5378024 x' _69779 _69780 h0). Qed.
Lemma lem5378027 (a : Prop) (b : Prop) : (a -> b) = (term316 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5378028 (_69779 : nat) (x' : nat -> nat) (_69780 : nat) : (term320 _69779 x' _69780) = (term321 _69779 x' _69780).
Proof. exact (@lem5378027 (_69779 = _69780) ((x' _69779) = (x' _69780))). Qed.
Lemma lem5378029 (_69779 : nat) (x' : nat -> nat) (_69780 : nat) : term321 _69779 x' _69780.
Proof. exact (EQ_MP (@lem5378028 _69779 x' _69780) (@lem5378025 _69779 x' _69780)). Qed.
Lemma lem5378035 (_69767 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term311 x' _69767.
Proof. exact (proj2 (@lem5377928 _69767 n x s x' h1)). Qed.
Lemma lem5378036 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term322 x' n.
Proof. exact (@lem5378035 (x' n) n x s x' h1). Qed.
Lemma lem5378037 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term323 x' n.
Proof. exact (fun h0 : term324 x' n => @lem5378036 n x s x' h1). Qed.
Lemma lem5378039 (p : Prop) : (term325 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5378040 (x' : nat -> nat) (n : nat) : (term323 x' n) = (term322 x' n).
Proof. exact (@lem5378039 (term324 x' n)). Qed.
Lemma lem5378041 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term322 x' n.
Proof. exact (EQ_MP (@lem5378040 x' n) (@lem5378037 n x s x' h1)). Qed.
Lemma lem5378052 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5378053 (_69766 : nat) (_69765 : nat) : (term145 _69765 _69766) = (term145 _69766 _69765).
Proof. exact (@lem5378052 (Peano.le _69765 _69766) (Peano.le _69766 _69765)). Qed.
Lemma lem5378059 (_69766 : nat) (_69765 : nat) : (term326 _69766 _69765) = (term326 _69766 _69765).
Proof. exact (eq_refl (term326 _69766 _69765)). Qed.
Lemma lem5378060 (_69766 : nat) (_69765 : nat) : ((term145 _69766 _69765) = (term145 _69765 _69766)) = ((term145 _69766 _69765) = (term145 _69766 _69765)).
Proof. exact (MK_COMB (@lem5378059 _69766 _69765) (@lem5378053 _69766 _69765)). Qed.
Lemma lem5378062 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5378063 (x : Prop) : (x = x) = True.
Proof. exact (@lem5378062 Prop x). Qed.
Lemma lem5378064 (_69766 : nat) (_69765 : nat) : ((term145 _69766 _69765) = (term145 _69766 _69765)) = True.
Proof. exact (@lem5378063 (term145 _69766 _69765)). Qed.
Lemma lem5378065 (_69765 : nat) (_69766 : nat) : ((term145 _69766 _69765) = (term145 _69765 _69766)) = True.
Proof. exact (TRANS (@lem5378060 _69766 _69765) (@lem5378064 _69766 _69765)). Qed.
Lemma lem5378066 (_69765 : nat) (_69766 : nat) : True = ((term145 _69766 _69765) = (term145 _69765 _69766)).
Proof. exact (SYM (@lem5378065 _69765 _69766)). Qed.
Lemma lem5378067 (_69765 : nat) (_69766 : nat) : (term145 _69766 _69765) = (term145 _69765 _69766).
Proof. exact (EQ_MP (@lem5378066 _69765 _69766) (@lem0)). Qed.
Lemma lem5378068 (_69765 : nat) (_69766 : nat) (h1 : term136) : term145 _69765 _69766.
Proof. exact (EQ_MP (@lem5378067 _69765 _69766) (@lem5377953 _69766 _69765 h1)). Qed.
Lemma lem5378070 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5378073 (_69766 : nat) (_69765 : nat) : (term145 _69765 _69766) = (term328 _69766 _69765).
Proof. exact (@lem5378070 (Peano.le _69765 _69766) (Peano.le _69766 _69765)). Qed.
Lemma lem5378076 (_69766 : nat) (_69765 : nat) (h1 : term136) : term328 _69766 _69765.
Proof. exact (EQ_MP (@lem5378073 _69766 _69765) (@lem5378068 _69765 _69766 h1)). Qed.
Lemma lem5378077 (x' : nat -> nat) (n : nat) (h1 : term136) : term329 x' n.
Proof. exact (@lem5378076 (x' n) (term330 x' n) h1). Qed.
Lemma lem5378080 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term278 n x s x') : term331 x' n.
Proof. exact (@lem5378077 x' n h1 (@lem5378041 n x s x' h2)). Qed.
Lemma lem5378081 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term278 n x s x') : term332 x' n.
Proof. exact (fun h0 : term333 x' n => @lem5378080 n x s x' h1 h2). Qed.
Lemma lem5378083 (p : Prop) : (term334 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5378084 (x' : nat -> nat) (n : nat) : (term332 x' n) = (term331 x' n).
Proof. exact (@lem5378083 (term331 x' n)). Qed.
Lemma lem5378085 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term278 n x s x') : term331 x' n.
Proof. exact (EQ_MP (@lem5378084 x' n) (@lem5378081 n x s x' h1 h2)). Qed.
Lemma lem5378088 (x' : nat -> nat) (n : nat) (h1 : term311 x' n) : term311 x' n.
Proof. exact (h1). Qed.
Lemma lem5378089 (x' : nat -> nat) (n : nat) (h1 : term311 x' n) : term335 x' n.
Proof. exact (fun h0 : term336 x' n => @lem5378088 x' n h1). Qed.
Lemma lem5378091 (p : Prop) : (term325 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5378092 (x' : nat -> nat) (n : nat) : (term335 x' n) = (term311 x' n).
Proof. exact (@lem5378091 (term336 x' n)). Qed.
Lemma lem5378093 (x' : nat -> nat) (n : nat) (h1 : term311 x' n) : term311 x' n.
Proof. exact (EQ_MP (@lem5378092 x' n) (@lem5378089 x' n h1)). Qed.
Lemma lem5378109 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5378110 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term337 _69762 _69761 _69763) = (term338 _69761 _69762 _69763).
Proof. exact (@lem5378109 (Peano.le _69761 _69763) (term309 _69762 _69763)). Qed.
Lemma lem5378116 (_69761 : nat) (_69762 : nat) : (term339 _69761 _69762) = (term339 _69761 _69762).
Proof. exact (eq_refl (term339 _69761 _69762)). Qed.
Lemma lem5378117 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term308 _69762 _69761 _69763) = (term340 _69761 _69762 _69763).
Proof. exact (MK_COMB (@lem5378116 _69761 _69762) (@lem5378110 _69761 _69762 _69763)). Qed.
Lemma lem5378121 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5378122 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term340 _69761 _69762 _69763) = (term341 _69761 _69762 _69763).
Proof. exact (@lem5378121 (Peano.le _69761 _69763) (term309 _69761 _69762) (term309 _69762 _69763)). Qed.
Lemma lem5378138 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term308 _69762 _69761 _69763) = (term341 _69761 _69762 _69763).
Proof. exact (TRANS (@lem5378117 _69761 _69762 _69763) (@lem5378122 _69761 _69762 _69763)). Qed.
Lemma lem5378139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5378140 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term342 _69762 _69761 _69763) = (term343 _69761 _69762 _69763).
Proof. exact (MK_COMB (@lem5378139) (@lem5378138 _69761 _69762 _69763)). Qed.
Lemma lem5378144 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5378145 (_69762 : nat) (_69761 : nat) (_69763 : nat) : (term344 _69762 _69761 _69763) = (term308 _69762 _69761 _69763).
Proof. exact (@lem5378144 (term309 _69761 _69762) (term309 _69762 _69763) (Peano.le _69761 _69763)). Qed.
Lemma lem5378159 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5378160 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term337 _69762 _69761 _69763) = (term338 _69761 _69762 _69763).
Proof. exact (@lem5378159 (Peano.le _69761 _69763) (term309 _69762 _69763)). Qed.
Lemma lem5378166 (_69761 : nat) (_69762 : nat) : (term339 _69761 _69762) = (term339 _69761 _69762).
Proof. exact (eq_refl (term339 _69761 _69762)). Qed.
Lemma lem5378167 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term308 _69762 _69761 _69763) = (term340 _69761 _69762 _69763).
Proof. exact (MK_COMB (@lem5378166 _69761 _69762) (@lem5378160 _69761 _69762 _69763)). Qed.
Lemma lem5378171 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5378172 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term340 _69761 _69762 _69763) = (term341 _69761 _69762 _69763).
Proof. exact (@lem5378171 (Peano.le _69761 _69763) (term309 _69761 _69762) (term309 _69762 _69763)). Qed.
Lemma lem5378188 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term308 _69762 _69761 _69763) = (term341 _69761 _69762 _69763).
Proof. exact (TRANS (@lem5378167 _69761 _69762 _69763) (@lem5378172 _69761 _69762 _69763)). Qed.
Lemma lem5378189 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term344 _69762 _69761 _69763) = (term341 _69761 _69762 _69763).
Proof. exact (TRANS (@lem5378145 _69762 _69761 _69763) (@lem5378188 _69761 _69762 _69763)). Qed.
Lemma lem5378190 (_69761 : nat) (_69762 : nat) (_69763 : nat) : ((term308 _69762 _69761 _69763) = (term344 _69762 _69761 _69763)) = ((term341 _69761 _69762 _69763) = (term341 _69761 _69762 _69763)).
Proof. exact (MK_COMB (@lem5378140 _69761 _69762 _69763) (@lem5378189 _69761 _69762 _69763)). Qed.
Lemma lem5378192 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5378193 (x : Prop) : (x = x) = True.
Proof. exact (@lem5378192 Prop x). Qed.
Lemma lem5378194 (_69761 : nat) (_69762 : nat) (_69763 : nat) : ((term341 _69761 _69762 _69763) = (term341 _69761 _69762 _69763)) = True.
Proof. exact (@lem5378193 (term341 _69761 _69762 _69763)). Qed.
Lemma lem5378195 (_69762 : nat) (_69761 : nat) (_69763 : nat) : ((term308 _69762 _69761 _69763) = (term344 _69762 _69761 _69763)) = True.
Proof. exact (TRANS (@lem5378190 _69761 _69762 _69763) (@lem5378194 _69761 _69762 _69763)). Qed.
Lemma lem5378196 (_69762 : nat) (_69761 : nat) (_69763 : nat) : True = ((term308 _69762 _69761 _69763) = (term344 _69762 _69761 _69763)).
Proof. exact (SYM (@lem5378195 _69762 _69761 _69763)). Qed.
Lemma lem5378197 (_69762 : nat) (_69761 : nat) (_69763 : nat) : (term308 _69762 _69761 _69763) = (term344 _69762 _69761 _69763).
Proof. exact (EQ_MP (@lem5378196 _69762 _69761 _69763) (@lem0)). Qed.
Lemma lem5378198 (_69762 : nat) (_69761 : nat) (_69763 : nat) (h1 : term157) : term344 _69762 _69761 _69763.
Proof. exact (EQ_MP (@lem5378197 _69762 _69761 _69763) (@lem5377945 _69762 _69761 _69763 h1)). Qed.
Lemma lem5378200 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5378201 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term344 _69762 _69761 _69763) = (term345 _69761 _69762 _69763).
Proof. exact (@lem5378200 (term346 _69762 _69761 _69763) (term309 _69762 _69763)). Qed.
Lemma lem5378203 (a : Prop) (b : Prop) : (term347 a b) = (term348 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5378204 (_69762 : nat) (_69761 : nat) (_69763 : nat) : (term349 _69762 _69761 _69763) = (term350 _69762 _69761 _69763).
Proof. exact (@lem5378203 (term309 _69761 _69762) (Peano.le _69761 _69763)). Qed.
Lemma lem5378206 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5378207 (_69761 : nat) (_69762 : nat) : (term352 _69761 _69762) = (Peano.le _69761 _69762).
Proof. exact (@lem5378206 (Peano.le _69761 _69762)). Qed.
Lemma lem5378208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5378209 (_69761 : nat) (_69762 : nat) : (term353 _69761 _69762) = (term354 _69761 _69762).
Proof. exact (MK_COMB (@lem5378208) (@lem5378207 _69761 _69762)). Qed.
Lemma lem5378210 (_69761 : nat) (_69763 : nat) : (term309 _69761 _69763) = (term309 _69761 _69763).
Proof. exact (eq_refl (term309 _69761 _69763)). Qed.
Lemma lem5378211 (_69762 : nat) (_69761 : nat) (_69763 : nat) : (term350 _69762 _69761 _69763) = (term355 _69762 _69761 _69763).
Proof. exact (MK_COMB (@lem5378209 _69761 _69762) (@lem5378210 _69761 _69763)). Qed.
Lemma lem5378212 (_69762 : nat) (_69761 : nat) (_69763 : nat) : (term349 _69762 _69761 _69763) = (term355 _69762 _69761 _69763).
Proof. exact (TRANS (@lem5378204 _69762 _69761 _69763) (@lem5378211 _69762 _69761 _69763)). Qed.
Lemma lem5378213 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5378214 (_69762 : nat) (_69761 : nat) (_69763 : nat) : (term356 _69762 _69761 _69763) = (term357 _69762 _69761 _69763).
Proof. exact (MK_COMB (@lem5378213) (@lem5378212 _69762 _69761 _69763)). Qed.
Lemma lem5378215 (_69762 : nat) (_69763 : nat) : (term309 _69762 _69763) = (term309 _69762 _69763).
Proof. exact (eq_refl (term309 _69762 _69763)). Qed.
Lemma lem5378216 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term345 _69761 _69762 _69763) = (term358 _69761 _69762 _69763).
Proof. exact (MK_COMB (@lem5378214 _69762 _69761 _69763) (@lem5378215 _69762 _69763)). Qed.
Lemma lem5378217 (_69761 : nat) (_69762 : nat) (_69763 : nat) : (term344 _69762 _69761 _69763) = (term358 _69761 _69762 _69763).
Proof. exact (TRANS (@lem5378201 _69761 _69762 _69763) (@lem5378216 _69761 _69762 _69763)). Qed.
Lemma lem5378219 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term311 x' n) (h3 : term278 n x s x') : term359 x' n.
Proof. exact (conj (@lem5378085 n x s x' h1 h3) (@lem5378093 x' n h2)). Qed.
Lemma lem5378221 (_69761 : nat) (_69762 : nat) (_69763 : nat) (h1 : term157) : term358 _69761 _69762 _69763.
Proof. exact (EQ_MP (@lem5378217 _69761 _69762 _69763) (@lem5378198 _69762 _69761 _69763 h1)). Qed.
Lemma lem5378222 (x' : nat -> nat) (n : nat) (h1 : term157) : term360 x' n.
Proof. exact (@lem5378221 (x' n) (term330 x' n) n h1). Qed.
Lemma lem5378225 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term311 x' n) (h4 : term278 n x s x') : term361 x' n.
Proof. exact (@lem5378222 x' n h1 (@lem5378219 n x s x' h2 h3 h4)). Qed.
Lemma lem5378226 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term311 x' n) (h4 : term278 n x s x') : term362 x' n.
Proof. exact (fun h0 : term363 x' n => @lem5378225 n x s x' h1 h2 h3 h4). Qed.
Lemma lem5378228 (p : Prop) : (term325 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5378229 (x' : nat -> nat) (n : nat) : (term362 x' n) = (term361 x' n).
Proof. exact (@lem5378228 (term363 x' n)). Qed.
Lemma lem5378230 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term311 x' n) (h4 : term278 n x s x') : term361 x' n.
Proof. exact (EQ_MP (@lem5378229 x' n) (@lem5378226 n x s x' h1 h2 h3 h4)). Qed.
Lemma lem5378232 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5378235 (n : nat) (_69768 : nat) (s : nat -> Prop) : (term158 s _69768 n) = (term364 n _69768 s).
Proof. exact (@lem5378232 (Peano.le _69768 n) (term365 _69768 s)). Qed.
Lemma lem5378238 (_69768 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term364 n _69768 s.
Proof. exact (EQ_MP (@lem5378235 n _69768 s) (@lem5377959 _69768 n x s x' h1)). Qed.
Lemma lem5378239 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term366 x' n s.
Proof. exact (@lem5378238 (term330 x' n) n x s x' h1). Qed.
Lemma lem5378242 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term311 x' n) (h4 : term278 n x s x') : term367 x' n s.
Proof. exact (@lem5378239 n x s x' h4 (@lem5378230 n x s x' h1 h2 h3 h4)). Qed.
Lemma lem5378243 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term311 x' n) (h4 : term278 n x s x') : term368 x' n s.
Proof. exact (fun h0 : term369 x' n s => @lem5378242 n x s x' h1 h2 h3 h4). Qed.
Lemma lem5378245 (p : Prop) : (term325 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5378246 (x' : nat -> nat) (n : nat) (s : nat -> Prop) : (term368 x' n s) = (term367 x' n s).
Proof. exact (@lem5378245 (term369 x' n s)). Qed.
Lemma lem5378247 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term311 x' n) (h4 : term278 n x s x') : term367 x' n s.
Proof. exact (EQ_MP (@lem5378246 x' n s) (@lem5378243 n x s x' h1 h2 h3 h4)). Qed.
Lemma lem5378249 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5378252 (s : nat -> Prop) (x' : nat -> nat) (_69767 : nat) (x : nat) : (term310 x x' _69767 s) = (term370 s x' _69767 x).
Proof. exact (@lem5378249 (term371 x' _69767 s) ((x' _69767) = x)). Qed.
Lemma lem5378255 (_69767 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term370 s x' _69767 x.
Proof. exact (EQ_MP (@lem5378252 s x' _69767 x) (@lem5377969 _69767 n x s x' h1)). Qed.
Lemma lem5378256 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term372 s x' n x.
Proof. exact (@lem5378255 (x' n) n x s x' h1). Qed.
Lemma lem5378259 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term311 x' n) (h4 : term278 n x s x') : (term330 x' n) = x.
Proof. exact (@lem5378256 n x s x' h4 (@lem5378247 n x s x' h1 h2 h3 h4)). Qed.
Lemma lem5378260 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term311 x' n) (h4 : term278 n x s x') : term373 x' n x.
Proof. exact (fun h0 : term374 x' n x => @lem5378259 n x s x' h1 h2 h3 h4). Qed.
Lemma lem5378262 (p : Prop) : (term334 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5378263 (x' : nat -> nat) (n : nat) (x : nat) : (term373 x' n x) = ((term330 x' n) = x).
Proof. exact (@lem5378262 ((term330 x' n) = x)). Qed.
Lemma lem5378264 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term311 x' n) (h4 : term278 n x s x') : (term330 x' n) = x.
Proof. exact (EQ_MP (@lem5378263 x' n x) (@lem5378260 n x s x' h1 h2 h3 h4)). Qed.
Lemma lem5378266 (_69767 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term311 x' _69767.
Proof. exact (proj2 (@lem5377928 _69767 n x s x' h1)). Qed.
Lemma lem5378267 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term311 x' x.
Proof. exact (@lem5378266 x n x s x' h1). Qed.
Lemma lem5378268 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term335 x' x.
Proof. exact (fun h0 : term336 x' x => @lem5378267 n x s x' h1). Qed.
Lemma lem5378270 (p : Prop) : (term325 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5378271 (x' : nat -> nat) (x : nat) : (term335 x' x) = (term311 x' x).
Proof. exact (@lem5378270 (term336 x' x)). Qed.
Lemma lem5378272 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term311 x' x.
Proof. exact (EQ_MP (@lem5378271 x' x) (@lem5378268 n x s x' h1)). Qed.
Lemma lem5378274 (_69764 : nat) (h1 : term150) : Peano.le _69764 _69764.
Proof. exact (EQ_MP (@lem5377918 _69764) (@lem5377917 _69764 h1)). Qed.
Lemma lem5378275 (x' : nat -> nat) (n : nat) (h1 : term150) : term375 x' n.
Proof. exact (@lem5378274 (term330 x' n) h1). Qed.
Lemma lem5378276 (x' : nat -> nat) (n : nat) (h1 : term150) : term376 x' n.
Proof. exact (fun h0 : term377 x' n => @lem5378275 x' n h1). Qed.
Lemma lem5378278 (p : Prop) : (term334 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5378279 (x' : nat -> nat) (n : nat) : (term376 x' n) = (term375 x' n).
Proof. exact (@lem5378278 (term375 x' n)). Qed.
Lemma lem5378280 (x' : nat -> nat) (n : nat) (h1 : term150) : term375 x' n.
Proof. exact (EQ_MP (@lem5378279 x' n) (@lem5378276 x' n h1)). Qed.
Lemma lem5378282 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5378283 (_69778 : nat) (_69776 : nat) (_69775 : nat) (_69777 : nat) : (term319 _69777 _69778 _69775 _69776) = (term378 _69778 _69776 _69775 _69777).
Proof. exact (@lem5378282 (term317 _69777 _69778 _69775 _69776) (term379 _69775 _69777)). Qed.
Lemma lem5378285 (a : Prop) (b : Prop) : (term347 a b) = (term348 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5378286 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : (term380 _69777 _69778 _69775 _69776) = (term381 _69777 _69778 _69775 _69776).
Proof. exact (@lem5378285 (term379 _69776 _69778) (term314 _69777 _69778 _69775 _69776)). Qed.
Lemma lem5378288 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5378289 (_69776 : nat) (_69778 : nat) : (term382 _69776 _69778) = (_69776 = _69778).
Proof. exact (@lem5378288 (_69776 = _69778)). Qed.
Lemma lem5378290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5378291 (_69776 : nat) (_69778 : nat) : (term383 _69776 _69778) = (term384 _69776 _69778).
Proof. exact (MK_COMB (@lem5378290) (@lem5378289 _69776 _69778)). Qed.
Lemma lem5378293 (a : Prop) (b : Prop) : (term347 a b) = (term348 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5378294 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : (term385 _69777 _69778 _69775 _69776) = (term386 _69777 _69778 _69775 _69776).
Proof. exact (@lem5378293 (Peano.le _69777 _69778) (term309 _69775 _69776)). Qed.
Lemma lem5378296 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5378297 (_69775 : nat) (_69776 : nat) : (term352 _69775 _69776) = (Peano.le _69775 _69776).
Proof. exact (@lem5378296 (Peano.le _69775 _69776)). Qed.
Lemma lem5378298 (_69777 : nat) (_69778 : nat) : (term387 _69777 _69778) = (term387 _69777 _69778).
Proof. exact (eq_refl (term387 _69777 _69778)). Qed.
Lemma lem5378299 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : (term386 _69777 _69778 _69775 _69776) = (term388 _69777 _69778 _69775 _69776).
Proof. exact (MK_COMB (@lem5378298 _69777 _69778) (@lem5378297 _69775 _69776)). Qed.
Lemma lem5378300 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : (term385 _69777 _69778 _69775 _69776) = (term388 _69777 _69778 _69775 _69776).
Proof. exact (TRANS (@lem5378294 _69777 _69778 _69775 _69776) (@lem5378299 _69777 _69778 _69775 _69776)). Qed.
Lemma lem5378301 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : (term381 _69777 _69778 _69775 _69776) = (term389 _69777 _69778 _69775 _69776).
Proof. exact (MK_COMB (@lem5378291 _69776 _69778) (@lem5378300 _69777 _69778 _69775 _69776)). Qed.
Lemma lem5378302 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : (term380 _69777 _69778 _69775 _69776) = (term389 _69777 _69778 _69775 _69776).
Proof. exact (TRANS (@lem5378286 _69777 _69778 _69775 _69776) (@lem5378301 _69777 _69778 _69775 _69776)). Qed.
Lemma lem5378303 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5378304 (_69777 : nat) (_69778 : nat) (_69775 : nat) (_69776 : nat) : (term390 _69777 _69778 _69775 _69776) = (term391 _69777 _69778 _69775 _69776).
Proof. exact (MK_COMB (@lem5378303) (@lem5378302 _69777 _69778 _69775 _69776)). Qed.
Lemma lem5378305 (_69775 : nat) (_69777 : nat) : (term379 _69775 _69777) = (term379 _69775 _69777).
Proof. exact (eq_refl (term379 _69775 _69777)). Qed.
Lemma lem5378306 (_69778 : nat) (_69776 : nat) (_69775 : nat) (_69777 : nat) : (term378 _69778 _69776 _69775 _69777) = (term392 _69778 _69776 _69775 _69777).
Proof. exact (MK_COMB (@lem5378304 _69777 _69778 _69775 _69776) (@lem5378305 _69775 _69777)). Qed.
Lemma lem5378307 (_69778 : nat) (_69776 : nat) (_69775 : nat) (_69777 : nat) : (term319 _69777 _69778 _69775 _69776) = (term392 _69778 _69776 _69775 _69777).
Proof. exact (TRANS (@lem5378283 _69778 _69776 _69775 _69777) (@lem5378306 _69778 _69776 _69775 _69777)). Qed.
Lemma lem5378309 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term150) (h2 : term278 n x s x') : term393 x x' n.
Proof. exact (conj (@lem5378272 n x s x' h2) (@lem5378280 x' n h1)). Qed.
Lemma lem5378310 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term394 x x' n.
Proof. exact (conj (@lem5378264 n x s x' h1 h2 h4 h5) (@lem5378309 n x s x' h3 h5)). Qed.
Lemma lem5378312 (_69778 : nat) (_69776 : nat) (_69775 : nat) (_69777 : nat) : term392 _69778 _69776 _69775 _69777.
Proof. exact (EQ_MP (@lem5378307 _69778 _69776 _69775 _69777) (@lem5378021 _69777 _69778 _69775 _69776)). Qed.
Lemma lem5378313 (n : nat) (x' : nat -> nat) (x : nat) : term395 n x' x.
Proof. exact (@lem5378312 x (term330 x' n) (term330 x' n) (x' x)). Qed.
Lemma lem5378316 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term396 n x' x.
Proof. exact (@lem5378313 n x' x (@lem5378310 n x s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5378317 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term397 n x' x.
Proof. exact (fun h0 : (term330 x' n) = (x' x) => @lem5378316 n x s x' h1 h2 h3 h4 h5). Qed.
Lemma lem5378319 (p : Prop) : (term325 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5378320 (n : nat) (x' : nat -> nat) (x : nat) : (term397 n x' x) = (term396 n x' x).
Proof. exact (@lem5378319 ((term330 x' n) = (x' x))). Qed.
Lemma lem5378321 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term396 n x' x.
Proof. exact (EQ_MP (@lem5378320 n x' x) (@lem5378317 n x s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5378323 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5378326 (x' : nat -> nat) (_69779 : nat) (_69780 : nat) : (term321 _69779 x' _69780) = (term398 x' _69779 _69780).
Proof. exact (@lem5378323 ((x' _69779) = (x' _69780)) (term379 _69779 _69780)). Qed.
Lemma lem5378329 (x' : nat -> nat) (_69779 : nat) (_69780 : nat) : term398 x' _69779 _69780.
Proof. exact (EQ_MP (@lem5378326 x' _69779 _69780) (@lem5378029 _69779 x' _69780)). Qed.
Lemma lem5378330 (x' : nat -> nat) (n : nat) (x : nat) : term399 x' n x.
Proof. exact (@lem5378329 x' (x' n) x). Qed.
Lemma lem5378333 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term400 x' n x.
Proof. exact (@lem5378330 x' n x (@lem5378321 n x s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5378334 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term401 x' n x.
Proof. exact (fun h0 : (x' n) = x => @lem5378333 n x s x' h1 h2 h3 h4 h5). Qed.
Lemma lem5378336 (p : Prop) : (term325 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5378337 (x' : nat -> nat) (n : nat) (x : nat) : (term401 x' n x) = (term400 x' n x).
Proof. exact (@lem5378336 ((x' n) = x)). Qed.
Lemma lem5378338 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term400 x' n x.
Proof. exact (EQ_MP (@lem5378337 x' n x) (@lem5378334 n x s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5378351 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5378352 (x : nat) (x' : nat -> nat) (_69767 : nat) (s : nat -> Prop) : (term402 s x' _69767 x) = (term310 x x' _69767 s).
Proof. exact (@lem5378351 ((x' _69767) = x) (term371 x' _69767 s)). Qed.
Lemma lem5378360 (x : nat) (x' : nat -> nat) (_69767 : nat) (s : nat -> Prop) : (term403 x x' _69767 s) = (term403 x x' _69767 s).
Proof. exact (eq_refl (term403 x x' _69767 s)). Qed.
Lemma lem5378361 (x : nat) (x' : nat -> nat) (_69767 : nat) (s : nat -> Prop) : ((term310 x x' _69767 s) = (term402 s x' _69767 x)) = ((term310 x x' _69767 s) = (term310 x x' _69767 s)).
Proof. exact (MK_COMB (@lem5378360 x x' _69767 s) (@lem5378352 x x' _69767 s)). Qed.
Lemma lem5378363 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5378364 (x : Prop) : (x = x) = True.
Proof. exact (@lem5378363 Prop x). Qed.
Lemma lem5378365 (x : nat) (x' : nat -> nat) (_69767 : nat) (s : nat -> Prop) : ((term310 x x' _69767 s) = (term310 x x' _69767 s)) = True.
Proof. exact (@lem5378364 (term310 x x' _69767 s)). Qed.
Lemma lem5378366 (s : nat -> Prop) (x' : nat -> nat) (_69767 : nat) (x : nat) : ((term310 x x' _69767 s) = (term402 s x' _69767 x)) = True.
Proof. exact (TRANS (@lem5378361 x x' _69767 s) (@lem5378365 x x' _69767 s)). Qed.
Lemma lem5378367 (s : nat -> Prop) (x' : nat -> nat) (_69767 : nat) (x : nat) : True = ((term310 x x' _69767 s) = (term402 s x' _69767 x)).
Proof. exact (SYM (@lem5378366 s x' _69767 x)). Qed.
Lemma lem5378368 (s : nat -> Prop) (x' : nat -> nat) (_69767 : nat) (x : nat) : (term310 x x' _69767 s) = (term402 s x' _69767 x).
Proof. exact (EQ_MP (@lem5378367 s x' _69767 x) (@lem0)). Qed.
Lemma lem5378369 (_69767 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term402 s x' _69767 x.
Proof. exact (EQ_MP (@lem5378368 s x' _69767 x) (@lem5377969 _69767 n x s x' h1)). Qed.
Lemma lem5378371 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5378374 (x : nat) (x' : nat -> nat) (_69767 : nat) (s : nat -> Prop) : (term402 s x' _69767 x) = (term404 x x' _69767 s).
Proof. exact (@lem5378371 ((x' _69767) = x) (term371 x' _69767 s)). Qed.
Lemma lem5378377 (_69767 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term404 x x' _69767 s.
Proof. exact (EQ_MP (@lem5378374 x x' _69767 s) (@lem5378369 _69767 n x s x' h1)). Qed.
Lemma lem5378378 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term404 x x' n s.
Proof. exact (@lem5378377 n n x s x' h1). Qed.
Lemma lem5378381 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term371 x' n s.
Proof. exact (@lem5378378 n x s x' h5 (@lem5378338 n x s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5378382 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term405 x' n s.
Proof. exact (fun h0 : term406 x' n s => @lem5378381 n x s x' h1 h2 h3 h4 h5). Qed.
Lemma lem5378384 (p : Prop) : (term334 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5378385 (x' : nat -> nat) (n : nat) (s : nat -> Prop) : (term405 x' n s) = (term371 x' n s).
Proof. exact (@lem5378384 (term371 x' n s)). Qed.
Lemma lem5378386 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term371 x' n s.
Proof. exact (EQ_MP (@lem5378385 x' n s) (@lem5378382 n x s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5378392 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5378393 (n : nat) (_69768 : nat) (s : nat -> Prop) : (term158 s _69768 n) = (term407 n _69768 s).
Proof. exact (@lem5378392 (Peano.le _69768 n) (term365 _69768 s)). Qed.
Lemma lem5378399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5378400 (n : nat) (_69768 : nat) (s : nat -> Prop) : (term408 s _69768 n) = (term409 n _69768 s).
Proof. exact (MK_COMB (@lem5378399) (@lem5378393 n _69768 s)). Qed.
Lemma lem5378406 (n : nat) (_69768 : nat) (s : nat -> Prop) : (term407 n _69768 s) = (term407 n _69768 s).
Proof. exact (eq_refl (term407 n _69768 s)). Qed.
Lemma lem5378407 (n : nat) (_69768 : nat) (s : nat -> Prop) : ((term158 s _69768 n) = (term407 n _69768 s)) = ((term407 n _69768 s) = (term407 n _69768 s)).
Proof. exact (MK_COMB (@lem5378400 n _69768 s) (@lem5378406 n _69768 s)). Qed.
Lemma lem5378409 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5378410 (x : Prop) : (x = x) = True.
Proof. exact (@lem5378409 Prop x). Qed.
Lemma lem5378411 (n : nat) (_69768 : nat) (s : nat -> Prop) : ((term407 n _69768 s) = (term407 n _69768 s)) = True.
Proof. exact (@lem5378410 (term407 n _69768 s)). Qed.
Lemma lem5378412 (n : nat) (_69768 : nat) (s : nat -> Prop) : ((term158 s _69768 n) = (term407 n _69768 s)) = True.
Proof. exact (TRANS (@lem5378407 n _69768 s) (@lem5378411 n _69768 s)). Qed.
Lemma lem5378413 (n : nat) (_69768 : nat) (s : nat -> Prop) : True = ((term158 s _69768 n) = (term407 n _69768 s)).
Proof. exact (SYM (@lem5378412 n _69768 s)). Qed.
Lemma lem5378414 (n : nat) (_69768 : nat) (s : nat -> Prop) : (term158 s _69768 n) = (term407 n _69768 s).
Proof. exact (EQ_MP (@lem5378413 n _69768 s) (@lem0)). Qed.
Lemma lem5378415 (_69768 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term407 n _69768 s.
Proof. exact (EQ_MP (@lem5378414 n _69768 s) (@lem5377959 _69768 n x s x' h1)). Qed.
Lemma lem5378417 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5378418 (s : nat -> Prop) (_69768 : nat) (n : nat) : (term407 n _69768 s) = (term410 s _69768 n).
Proof. exact (@lem5378417 (term365 _69768 s) (Peano.le _69768 n)). Qed.
Lemma lem5378420 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5378421 (_69768 : nat) (s : nat -> Prop) : (term411 _69768 s) = (@IN nat _69768 s).
Proof. exact (@lem5378420 (@IN nat _69768 s)). Qed.
Lemma lem5378422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5378423 (_69768 : nat) (s : nat -> Prop) : (term412 _69768 s) = (term45 _69768 s).
Proof. exact (MK_COMB (@lem5378422) (@lem5378421 _69768 s)). Qed.
Lemma lem5378424 (_69768 : nat) (n : nat) : (Peano.le _69768 n) = (Peano.le _69768 n).
Proof. exact (eq_refl (Peano.le _69768 n)). Qed.
Lemma lem5378425 (s : nat -> Prop) (_69768 : nat) (n : nat) : (term410 s _69768 n) = (term47 s _69768 n).
Proof. exact (MK_COMB (@lem5378423 _69768 s) (@lem5378424 _69768 n)). Qed.
Lemma lem5378426 (s : nat -> Prop) (_69768 : nat) (n : nat) : (term407 n _69768 s) = (term47 s _69768 n).
Proof. exact (TRANS (@lem5378418 s _69768 n) (@lem5378425 s _69768 n)). Qed.
Lemma lem5378429 (_69768 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term47 s _69768 n.
Proof. exact (EQ_MP (@lem5378426 s _69768 n) (@lem5378415 _69768 n x s x' h1)). Qed.
Lemma lem5378430 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term413 s x' n.
Proof. exact (@lem5378429 (x' n) n x s x' h1). Qed.
Lemma lem5378433 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term311 x' n) (h5 : term278 n x s x') : term336 x' n.
Proof. exact (@lem5378430 n x s x' h5 (@lem5378386 n x s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5378434 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : term414 x' n.
Proof. exact (fun h0 : term311 x' n => @lem5378433 n x s x' h1 h2 h3 h0 h4). Qed.
Lemma lem5378436 (p : Prop) : (term334 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5378437 (x' : nat -> nat) (n : nat) : (term414 x' n) = (term336 x' n).
Proof. exact (@lem5378436 (term336 x' n)). Qed.
Lemma lem5378438 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : term336 x' n.
Proof. exact (EQ_MP (@lem5378437 x' n) (@lem5378434 n x s x' h1 h2 h3 h4)). Qed.
Lemma lem5378441 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5378443 (x' : nat -> nat) (_69767 : nat) : (term311 x' _69767) = (term415 x' _69767).
Proof. exact (@lem5378441 (term336 x' _69767)). Qed.
Lemma lem5378446 (_69767 : nat) (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term415 x' _69767.
Proof. exact (EQ_MP (@lem5378443 x' _69767) (@lem5377971 _69767 n x s x' h1)). Qed.
Lemma lem5378447 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term278 n x s x') : term415 x' n.
Proof. exact (@lem5378446 n n x s x' h1). Qed.
Lemma lem5378450 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : False.
Proof. exact (@lem5378447 n x s x' h4 (@lem5378438 n x s x' h1 h2 h3 h4)). Qed.
Lemma lem5378451 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : term416.
Proof. exact (fun h0 : ~ False => @lem5378450 n x s x' h1 h2 h3 h4). Qed.
Lemma lem5378453 (p : Prop) : (term334 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5378454 : term416 = False.
Proof. exact (@lem5378453 False). Qed.
Lemma lem5378455 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : False.
Proof. exact (EQ_MP (@lem5378454) (@lem5378451 n x s x' h1 h2 h3 h4)). Qed.
Lemma lem5378456 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : term136 = False.
Proof. exact (prop_ext (fun h5 : term136 => @lem5378455 n x s x' h1 h2 h3 h4) (fun h5 : False => @lem5377869 h2)). Qed.
Lemma lem5378457 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : False.
Proof. exact (EQ_MP (@lem5378456 n x s x' h1 h2 h3 h4) (@lem5377869 h2)). Qed.
Lemma lem5378458 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : term150 = False.
Proof. exact (prop_ext (fun h5 : term150 => @lem5378457 n x s x' h1 h2 h3 h4) (fun h5 : False => @lem5377853 h3)). Qed.
Lemma lem5378459 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : False.
Proof. exact (EQ_MP (@lem5378458 n x s x' h1 h2 h3 h4) (@lem5377853 h3)). Qed.
Lemma lem5378460 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : (term278 n x s x') = False.
Proof. exact (prop_ext (fun h5 : term278 n x s x' => @lem5378459 n x s x' h1 h2 h3 h4) (fun h5 : False => @lem5377815 n x s x' h4)). Qed.
Lemma lem5378461 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : False.
Proof. exact (EQ_MP (@lem5378460 n x s x' h1 h2 h3 h4) (@lem5377815 n x s x' h4)). Qed.
Lemma lem5378462 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : term136 = False.
Proof. exact (prop_ext (fun h5 : term136 => @lem5378461 n x s x' h1 h2 h3 h4) (fun h5 : False => @lem5377745 h2)). Qed.
Lemma lem5378463 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : False.
Proof. exact (EQ_MP (@lem5378462 n x s x' h1 h2 h3 h4) (@lem5377745 h2)). Qed.
Lemma lem5378464 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : term150 = False.
Proof. exact (prop_ext (fun h5 : term150 => @lem5378463 n x s x' h1 h2 h3 h4) (fun h5 : False => @lem5377725 h3)). Qed.
Lemma lem5378465 (n : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term278 n x s x') : False.
Proof. exact (EQ_MP (@lem5378464 n x s x' h1 h2 h3 h4) (@lem5377725 h3)). Qed.
Lemma lem5378466 (n : nat) (x : nat) (s : nat -> Prop) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term281 n x s) : False.
Proof. exact (ex_elim (@lem5377680 n x s h4) (fun x' : nat -> nat => fun h0 : term280 n x s x' => @lem5378465 n x s x' h1 h2 h3 h0)). Qed.
Lemma lem5378467 (x : nat) (s : nat -> Prop) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term283 x s) : False.
Proof. exact (ex_elim (@lem5377679 x s h4) (fun n : nat => fun h0 : term282 x s n => @lem5378466 n x s h1 h2 h3 h0)). Qed.
Lemma lem5378468 (x : nat) (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term285 x) : False.
Proof. exact (ex_elim (@lem5377678 x h4) (fun s : nat -> Prop => fun h0 : term284 x s => @lem5378467 x s h1 h2 h3 h0)). Qed.
Lemma lem5378469 (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term129) : False.
Proof. exact (ex_elim (@lem5377513 h4) (fun x : nat => fun h0 : term286 x => @lem5378468 x h1 h2 h3 h0)). Qed.
Lemma lem5378470 (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term129) : term136 = False.
Proof. exact (prop_ext (fun h5 : term136 => @lem5378469 h1 h2 h3 h4) (fun h5 : False => @lem5377677 h2)). Qed.
Lemma lem5378471 (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term129) : False.
Proof. exact (EQ_MP (@lem5378470 h1 h2 h3 h4) (@lem5377677 h2)). Qed.
Lemma lem5378472 (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term129) : term150 = False.
Proof. exact (prop_ext (fun h5 : term150 => @lem5378471 h1 h2 h3 h4) (fun h5 : False => @lem5377609 h3)). Qed.
Lemma lem5378473 (h1 : term157) (h2 : term136) (h3 : term150) (h4 : term129) : False.
Proof. exact (EQ_MP (@lem5378472 h1 h2 h3 h4) (@lem5377609 h3)). Qed.
Lemma lem5378474 (h1 : term157) (h2 : term150) (h3 : term129) : term134.
Proof. exact (fun h0 : term136 => @lem5378473 h1 h0 h2 h3). Qed.
Lemma lem5378475 : term134 = term135.
Proof. exact (@lem69 term136). Qed.
Lemma lem5378476 (h1 : term157) (h2 : term150) (h3 : term129) : term135.
Proof. exact (EQ_MP (@lem5378475) (@lem5378474 h1 h2 h3)). Qed.
Lemma lem5378477 (h1 : term157) (h2 : term129) : term139.
Proof. exact (fun h0 : term150 => @lem5378476 h1 h0 h2). Qed.
Lemma lem5378478 (h1 : term129) : term142.
Proof. exact (fun h0 : term157 => @lem5378477 h0 h1). Qed.
Lemma lem5378479 : term144.
Proof. exact (fun h0 : term129 => @lem5378478 h0). Qed.
Lemma lem5378480 : term130.
Proof. exact (EQ_MP (@lem5377160) (@lem5378479)). Qed.
Lemma lem5378482 : term130.
Proof. exact (@lem5376834 (@lem5378480)). Qed.
Lemma lem5378483 (h1 : term129) : term141.
Proof. exact (@lem5378482 (@lem5376819 h1)). Qed.
Lemma lem5378484 (h1 : term129) : term138.
Proof. exact (@lem5378483 h1 (@lem93743)). Qed.
Lemma lem5378485 (h1 : term129) : term134.
Proof. exact (@lem5378484 h1 (@lem91603)). Qed.
Lemma lem5378486 (h1 : term129) : False.
Proof. exact (@lem5378485 h1 (@lem96155)). Qed.
Lemma lem5378487 (h1 : term129) : term129 = False.
Proof. exact (prop_ext (fun h2 : term129 => @lem5378486 h1) (fun h2 : False => @lem5376819 h1)). Qed.
Lemma lem5378488 (h1 : term129) : False.
Proof. exact (EQ_MP (@lem5378487 h1) (@lem5376819 h1)). Qed.
Lemma lem5378489 : term128.
Proof. exact (fun h0 : term129 => @lem5378488 h0). Qed.
Lemma lem5378490 : term125.
Proof. exact (EQ_MP (@lem5376818) (@lem5378489)). Qed.
Lemma lem5378491 : term86.
Proof. exact (EQ_MP (@lem5376814) (@lem5378490)). Qed.
Lemma lem5378492 : term93.
Proof. exact (@lem5376649 (@lem5378491)). Qed.
Lemma lem5378493 (s : nat -> Prop) : term417 s.
Proof. exact (@lem5378492 s). Qed.
Lemma lem5378494 (s : nat -> Prop) : (term417 s) = (term57 s).
Proof. exact (eq_refl (term417 s)). Qed.
Lemma lem5378495 (s : nat -> Prop) : term57 s.
Proof. exact (EQ_MP (@lem5378494 s) (@lem5378493 s)). Qed.
Lemma lem5378496 (s : nat -> Prop) : term56 s.
Proof. exact (EQ_MP (@lem5376616 s) (@lem5378495 s)). Qed.
Lemma lem5378498 (p : Prop) : p = (term127 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5378499 (s : nat -> Prop) : (term418 s) = (term419 s).
Proof. exact (@lem5378498 (term418 s)). Qed.
Lemma lem5378500 (s : nat -> Prop) : (term419 s) = (term418 s).
Proof. exact (SYM (@lem5378499 s)). Qed.
Lemma lem5378501 (s : nat -> Prop) (h1 : term420 s) : term420 s.
Proof. exact (h1). Qed.
Lemma lem5378502 : term421.
Proof. exact (@lem3599924 nat). Qed.
Lemma lem5378506 (s : nat -> Prop) (h1 : term422 s) : term422 s.
Proof. exact (h1). Qed.
Lemma lem5378507 (s : nat -> Prop) : term423 s.
Proof. exact (fun h0 : term422 s => @lem5378506 s h0). Qed.
Lemma lem5378508 (s : nat -> Prop) (h1 : term423 s) : term423 s.
Proof. exact (h1). Qed.
Lemma lem5378509 (s : nat -> Prop) (h1 : term422 s) : term422 s.
Proof. exact (h1). Qed.
Lemma lem5378510 (s : nat -> Prop) (h1 : term422 s) (h2 : term423 s) : term422 s.
Proof. exact (@lem5378508 s h2 (@lem5378509 s h1)). Qed.
Lemma lem5378511 (s : nat -> Prop) (h1 : term422 s) : term424 s.
Proof. exact (fun h0 : term423 s => @lem5378510 s h1 h0). Qed.
Lemma lem5378512 (s : nat -> Prop) (h1 : term423 s) : term423 s.
Proof. exact (h1). Qed.
Lemma lem5378513 (s : nat -> Prop) (h1 : term422 s) (h2 : term423 s) : term422 s.
Proof. exact (@lem5378511 s h1 (@lem5378512 s h2)). Qed.
Lemma lem5378514 (s : nat -> Prop) (h1 : term423 s) : term423 s.
Proof. exact (fun h0 : term422 s => @lem5378513 s h0 h1). Qed.
Lemma lem5378515 (s : nat -> Prop) : term425 s.
Proof. exact (fun h0 : term423 s => @lem5378514 s h0). Qed.
Lemma lem5378518 (s : nat -> Prop) : term423 s.
Proof. exact (@lem5378515 s (@lem5378507 s)). Qed.
Lemma lem5378542 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5378543 : term426 = term427.
Proof. exact (@lem5378542 term421). Qed.
Lemma lem5378556 : term428 = term428.
Proof. exact (eq_refl term428). Qed.
Lemma lem5378557 : term429 = term430.
Proof. exact (MK_COMB (@lem5378556) (@lem5378543)). Qed.
Lemma lem5378560 (s : nat -> Prop) : (term431 s) = (term431 s).
Proof. exact (eq_refl (term431 s)). Qed.
Lemma lem5378561 (s : nat -> Prop) : (term422 s) = (term432 s).
Proof. exact (MK_COMB (@lem5378560 s) (@lem5378557)). Qed.
Lemma lem5378564 : term433 = term434.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5378561 s)). Qed.
Lemma lem5378565 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378574 : term435 = term436.
Proof. exact (MK_COMB (@lem5378565) (@lem5378564)). Qed.
Lemma lem5378583 (t : nat -> Prop) (s : nat -> Prop) : (term437 t s) = (term437 t s).
Proof. exact (eq_refl (term437 t s)). Qed.
Lemma lem5378584 (s : nat -> Prop) : (term438 s) = (term438 s).
Proof. exact (fun_ext (fun t : nat -> Prop => @lem5378583 t s)). Qed.
Lemma lem5378585 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378586 (s : nat -> Prop) : (term439 s) = (term439 s).
Proof. exact (MK_COMB (@lem5378585) (@lem5378584 s)). Qed.
Lemma lem5378587 : term440 = term440.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5378586 s)). Qed.
Lemma lem5378588 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378589 : term421 = term421.
Proof. exact (MK_COMB (@lem5378588) (@lem5378587)). Qed.
Lemma lem5378590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5378591 : term427 = term427.
Proof. exact (MK_COMB (@lem5378590) (@lem5378589)). Qed.
Lemma lem5378592 (m : nat) (n : nat) : (term441 m n) = (term441 m n).
Proof. exact (eq_refl (term441 m n)). Qed.
Lemma lem5378593 (m : nat) : (term442 m) = (term442 m).
Proof. exact (fun_ext (fun n : nat => @lem5378592 m n)). Qed.
Lemma lem5378594 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5378595 (m : nat) : (term443 m) = (term443 m).
Proof. exact (MK_COMB (@lem5378594) (@lem5378593 m)). Qed.
Lemma lem5378596 : term444 = term444.
Proof. exact (fun_ext (fun m : nat => @lem5378595 m)). Qed.
Lemma lem5378597 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5378598 : term445 = term445.
Proof. exact (MK_COMB (@lem5378597) (@lem5378596)). Qed.
Lemma lem5378599 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5378600 : term428 = term428.
Proof. exact (MK_COMB (@lem5378599) (@lem5378598)). Qed.
Lemma lem5378601 : term430 = term430.
Proof. exact (MK_COMB (@lem5378600) (@lem5378591)). Qed.
Lemma lem5378602 (s : nat -> Prop) : (@FINITE nat s) = (@FINITE nat s).
Proof. exact (eq_refl (@FINITE nat s)). Qed.
Lemma lem5378603 (s : nat -> Prop) (n : nat) : (term38 s n) = (term38 s n).
Proof. exact (eq_refl (term38 s n)). Qed.
Lemma lem5378604 (s : nat -> Prop) : (term51 s) = (term51 s).
Proof. exact (fun_ext (fun n : nat => @lem5378603 s n)). Qed.
Lemma lem5378605 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5378606 (s : nat -> Prop) : (term53 s) = (term53 s).
Proof. exact (MK_COMB (@lem5378605) (@lem5378604 s)). Qed.
Lemma lem5378607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5378608 (s : nat -> Prop) : (term446 s) = (term446 s).
Proof. exact (MK_COMB (@lem5378607) (@lem5378606 s)). Qed.
Lemma lem5378609 (s : nat -> Prop) : (term418 s) = (term418 s).
Proof. exact (MK_COMB (@lem5378608 s) (@lem5378602 s)). Qed.
Lemma lem5378610 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5378611 (s : nat -> Prop) : (term420 s) = (term420 s).
Proof. exact (MK_COMB (@lem5378610) (@lem5378609 s)). Qed.
Lemma lem5378612 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5378613 (s : nat -> Prop) : (term431 s) = (term431 s).
Proof. exact (MK_COMB (@lem5378612) (@lem5378611 s)). Qed.
Lemma lem5378614 (s : nat -> Prop) : (term432 s) = (term432 s).
Proof. exact (MK_COMB (@lem5378613 s) (@lem5378601)). Qed.
Lemma lem5378615 : term434 = term434.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5378614 s)). Qed.
Lemma lem5378616 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378617 : term436 = term436.
Proof. exact (MK_COMB (@lem5378616) (@lem5378615)). Qed.
Lemma lem5378666 : term435 = term436.
Proof. exact (TRANS (@lem5378574) (@lem5378617)). Qed.
Lemma lem5378667 : term436 = term435.
Proof. exact (SYM (@lem5378666)). Qed.
Lemma lem5378668 (s : nat -> Prop) (h1 : term420 s) : term420 s.
Proof. exact (h1). Qed.
Lemma lem5378669 (h1 : term445) : term445.
Proof. exact (h1). Qed.
Lemma lem5378670 (h1 : term421) : term421.
Proof. exact (h1). Qed.
Lemma lem5378671 (s : nat -> Prop) (n : nat) : (term38 s n) = (term38 s n).
Proof. exact (eq_refl (term38 s n)). Qed.
Lemma lem5378672 (s : nat -> Prop) : (term51 s) = (term51 s).
Proof. exact (fun_ext (fun n : nat => @lem5378671 s n)). Qed.
Lemma lem5378673 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5378674 (s : nat -> Prop) : (term53 s) = (term53 s).
Proof. exact (MK_COMB (@lem5378673) (@lem5378672 s)). Qed.
Lemma lem5378675 (s : nat -> Prop) : (term447 s) = (term447 s).
Proof. exact (eq_refl (term447 s)). Qed.
Lemma lem5378676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5378677 (s : nat -> Prop) : (term448 s) = (term448 s).
Proof. exact (MK_COMB (@lem5378676) (@lem5378674 s)). Qed.
Lemma lem5378678 (s : nat -> Prop) : (term449 s) = (term449 s).
Proof. exact (MK_COMB (@lem5378677 s) (@lem5378675 s)). Qed.
Lemma lem5378679 (s : nat -> Prop) : (term420 s) = (term449 s).
Proof. exact (@lem17362 (term53 s) (@FINITE nat s)). Qed.
Lemma lem5378680 (s : nat -> Prop) : (term420 s) = (term449 s).
Proof. exact (TRANS (@lem5378679 s) (@lem5378678 s)). Qed.
Lemma lem5378687 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5378688 (P : nat -> Prop) (Q : Prop) : (term207 P Q) = (term208 P Q).
Proof. exact (@lem5378687 nat P Q). Qed.
Lemma lem5378689 (s : nat -> Prop) : (term450 s) = (term451 s).
Proof. exact (@lem5378688 (term51 s) (term447 s)). Qed.
Lemma lem5378690 (s : nat -> Prop) (n : nat) : (term452 s n) = (term38 s n).
Proof. exact (eq_refl (term452 s n)). Qed.
Lemma lem5378691 (s : nat -> Prop) : (term453 s) = (term51 s).
Proof. exact (fun_ext (fun n : nat => @lem5378690 s n)). Qed.
Lemma lem5378692 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5378693 (s : nat -> Prop) : (term454 s) = (term53 s).
Proof. exact (MK_COMB (@lem5378692) (@lem5378691 s)). Qed.
Lemma lem5378694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5378695 (s : nat -> Prop) : (term455 s) = (term448 s).
Proof. exact (MK_COMB (@lem5378694) (@lem5378693 s)). Qed.
Lemma lem5378696 (s : nat -> Prop) : (term447 s) = (term447 s).
Proof. exact (eq_refl (term447 s)). Qed.
Lemma lem5378697 (s : nat -> Prop) : (term450 s) = (term449 s).
Proof. exact (MK_COMB (@lem5378695 s) (@lem5378696 s)). Qed.
Lemma lem5378698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5378699 (s : nat -> Prop) : (term456 s) = (term457 s).
Proof. exact (MK_COMB (@lem5378698) (@lem5378697 s)). Qed.
Lemma lem5378700 (s : nat -> Prop) (n : nat) : (term452 s n) = (term38 s n).
Proof. exact (eq_refl (term452 s n)). Qed.
Lemma lem5378701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5378702 (s : nat -> Prop) (n : nat) : (term458 s n) = (term459 s n).
Proof. exact (MK_COMB (@lem5378701) (@lem5378700 s n)). Qed.
Lemma lem5378703 (s : nat -> Prop) : (term447 s) = (term447 s).
Proof. exact (eq_refl (term447 s)). Qed.
Lemma lem5378704 (n : nat) (s : nat -> Prop) : (term460 n s) = (term461 n s).
Proof. exact (MK_COMB (@lem5378702 s n) (@lem5378703 s)). Qed.
Lemma lem5378705 (s : nat -> Prop) : (term462 s) = (term463 s).
Proof. exact (fun_ext (fun n : nat => @lem5378704 n s)). Qed.
Lemma lem5378706 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5378707 (s : nat -> Prop) : (term451 s) = (term464 s).
Proof. exact (MK_COMB (@lem5378706) (@lem5378705 s)). Qed.
Lemma lem5378708 (s : nat -> Prop) : ((term450 s) = (term451 s)) = ((term449 s) = (term464 s)).
Proof. exact (MK_COMB (@lem5378699 s) (@lem5378707 s)). Qed.
Lemma lem5378710 (s : nat -> Prop) : (term449 s) = (term464 s).
Proof. exact (EQ_MP (@lem5378708 s) (@lem5378689 s)). Qed.
Lemma lem5378711 (s : nat -> Prop) : (term420 s) = (term464 s).
Proof. exact (TRANS (@lem5378680 s) (@lem5378710 s)). Qed.
Lemma lem5378712 (s : nat -> Prop) (h1 : term420 s) : term464 s.
Proof. exact (EQ_MP (@lem5378711 s) (@lem5378668 s h1)). Qed.
Lemma lem5378713 (m : nat) (n : nat) : (term441 m n) = (term441 m n).
Proof. exact (eq_refl (term441 m n)). Qed.
Lemma lem5378714 (m : nat) : (term442 m) = (term442 m).
Proof. exact (fun_ext (fun n : nat => @lem5378713 m n)). Qed.
Lemma lem5378715 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5378716 (m : nat) : (term443 m) = (term443 m).
Proof. exact (MK_COMB (@lem5378715) (@lem5378714 m)). Qed.
Lemma lem5378717 : term444 = term444.
Proof. exact (fun_ext (fun m : nat => @lem5378716 m)). Qed.
Lemma lem5378718 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5378731 : term445 = term445.
Proof. exact (MK_COMB (@lem5378718) (@lem5378717)). Qed.
Lemma lem5378732 (h1 : term445) : term445.
Proof. exact (EQ_MP (@lem5378731) (@lem5378669 h1)). Qed.
Lemma lem5378739 (s : nat -> Prop) (t : nat -> Prop) : (term465 s t) = (term466 s t).
Proof. exact (@lem17045 (@FINITE nat t) (@SUBSET nat s t)). Qed.
Lemma lem5378740 (s : nat -> Prop) : (@FINITE nat s) = (@FINITE nat s).
Proof. exact (eq_refl (@FINITE nat s)). Qed.
Lemma lem5378741 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5378742 (s : nat -> Prop) (t : nat -> Prop) : (term467 s t) = (term468 s t).
Proof. exact (MK_COMB (@lem5378741) (@lem5378739 s t)). Qed.
Lemma lem5378743 (t : nat -> Prop) (s : nat -> Prop) : (term469 t s) = (term470 t s).
Proof. exact (MK_COMB (@lem5378742 s t) (@lem5378740 s)). Qed.
Lemma lem5378744 (t : nat -> Prop) (s : nat -> Prop) : (term437 t s) = (term469 t s).
Proof. exact (@lem17265 (term471 s t) (@FINITE nat s)). Qed.
Lemma lem5378745 (t : nat -> Prop) (s : nat -> Prop) : (term437 t s) = (term470 t s).
Proof. exact (TRANS (@lem5378744 t s) (@lem5378743 t s)). Qed.
Lemma lem5378746 (s : nat -> Prop) : (term438 s) = (term472 s).
Proof. exact (fun_ext (fun t : nat -> Prop => @lem5378745 t s)). Qed.
Lemma lem5378747 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378748 (s : nat -> Prop) : (term439 s) = (term473 s).
Proof. exact (MK_COMB (@lem5378747) (@lem5378746 s)). Qed.
Lemma lem5378749 : term440 = term474.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5378748 s)). Qed.
Lemma lem5378750 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378751 : term421 = term475.
Proof. exact (MK_COMB (@lem5378750) (@lem5378749)). Qed.
Lemma lem5378777 {A : Type'} (P : A -> Prop) (Q : Prop) : (term476 A P Q) = (term477 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem5378778 (P : type993) (Q : Prop) : (term478 P Q) = (term479 P Q).
Proof. exact (@lem5378777 (nat -> Prop) P Q). Qed.
Lemma lem5378779 (s : nat -> Prop) : (term480 s) = (term481 s).
Proof. exact (@lem5378778 (term482 s) (@FINITE nat s)). Qed.
Lemma lem5378780 (s : nat -> Prop) (t : nat -> Prop) : (term483 s t) = (term466 s t).
Proof. exact (eq_refl (term483 s t)). Qed.
Lemma lem5378781 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5378782 (s : nat -> Prop) (t : nat -> Prop) : (term484 s t) = (term468 s t).
Proof. exact (MK_COMB (@lem5378781) (@lem5378780 s t)). Qed.
Lemma lem5378783 (s : nat -> Prop) : (@FINITE nat s) = (@FINITE nat s).
Proof. exact (eq_refl (@FINITE nat s)). Qed.
Lemma lem5378784 (t : nat -> Prop) (s : nat -> Prop) : (term485 t s) = (term470 t s).
Proof. exact (MK_COMB (@lem5378782 s t) (@lem5378783 s)). Qed.
Lemma lem5378785 (s : nat -> Prop) : (term486 s) = (term472 s).
Proof. exact (fun_ext (fun t : nat -> Prop => @lem5378784 t s)). Qed.
Lemma lem5378786 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378787 (s : nat -> Prop) : (term480 s) = (term473 s).
Proof. exact (MK_COMB (@lem5378786) (@lem5378785 s)). Qed.
Lemma lem5378788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5378789 (s : nat -> Prop) : (term487 s) = (term488 s).
Proof. exact (MK_COMB (@lem5378788) (@lem5378787 s)). Qed.
Lemma lem5378790 (s : nat -> Prop) (t : nat -> Prop) : (term483 s t) = (term466 s t).
Proof. exact (eq_refl (term483 s t)). Qed.
Lemma lem5378791 (s : nat -> Prop) : (term489 s) = (term482 s).
Proof. exact (fun_ext (fun t : nat -> Prop => @lem5378790 s t)). Qed.
Lemma lem5378792 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378793 (s : nat -> Prop) : (term490 s) = (term491 s).
Proof. exact (MK_COMB (@lem5378792) (@lem5378791 s)). Qed.
Lemma lem5378794 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5378795 (s : nat -> Prop) : (term492 s) = (term493 s).
Proof. exact (MK_COMB (@lem5378794) (@lem5378793 s)). Qed.
Lemma lem5378796 (s : nat -> Prop) : (@FINITE nat s) = (@FINITE nat s).
Proof. exact (eq_refl (@FINITE nat s)). Qed.
Lemma lem5378797 (s : nat -> Prop) : (term481 s) = (term494 s).
Proof. exact (MK_COMB (@lem5378795 s) (@lem5378796 s)). Qed.
Lemma lem5378798 (s : nat -> Prop) : ((term480 s) = (term481 s)) = ((term473 s) = (term494 s)).
Proof. exact (MK_COMB (@lem5378789 s) (@lem5378797 s)). Qed.
Lemma lem5378799 (s : nat -> Prop) : (term473 s) = (term494 s).
Proof. exact (EQ_MP (@lem5378798 s) (@lem5378779 s)). Qed.
Lemma lem5378848 : term474 = term495.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5378799 s)). Qed.
Lemma lem5378849 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378884 : term475 = term496.
Proof. exact (MK_COMB (@lem5378849) (@lem5378848)). Qed.
Lemma lem5378885 : term421 = term496.
Proof. exact (TRANS (@lem5378751) (@lem5378884)). Qed.
Lemma lem5378886 (h1 : term421) : term496.
Proof. exact (EQ_MP (@lem5378885) (@lem5378670 h1)). Qed.
Lemma lem5378894 (m : nat) (n : nat) : (term441 m n) = (term441 m n).
Proof. exact (eq_refl (term441 m n)). Qed.
Lemma lem5378895 (m : nat) : (term442 m) = (term442 m).
Proof. exact (fun_ext (fun n : nat => @lem5378894 m n)). Qed.
Lemma lem5378896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5378897 (m : nat) : (term443 m) = (term443 m).
Proof. exact (MK_COMB (@lem5378896) (@lem5378895 m)). Qed.
Lemma lem5378898 : term444 = term444.
Proof. exact (fun_ext (fun m : nat => @lem5378897 m)). Qed.
Lemma lem5378899 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5378900 : term445 = term445.
Proof. exact (MK_COMB (@lem5378899) (@lem5378898)). Qed.
Lemma lem5378901 (h1 : term445) : term445.
Proof. exact (EQ_MP (@lem5378900) (@lem5378732 h1)). Qed.
Lemma lem5378904 (s : nat -> Prop) : (@FINITE nat s) = (@FINITE nat s).
Proof. exact (eq_refl (@FINITE nat s)). Qed.
Lemma lem5378919 (s : nat -> Prop) (t : nat -> Prop) : (term466 s t) = (term466 s t).
Proof. exact (eq_refl (term466 s t)). Qed.
Lemma lem5378920 (s : nat -> Prop) : (term482 s) = (term482 s).
Proof. exact (fun_ext (fun t : nat -> Prop => @lem5378919 s t)). Qed.
Lemma lem5378921 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378922 (s : nat -> Prop) : (term491 s) = (term491 s).
Proof. exact (MK_COMB (@lem5378921) (@lem5378920 s)). Qed.
Lemma lem5378923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5378924 (s : nat -> Prop) : (term493 s) = (term493 s).
Proof. exact (MK_COMB (@lem5378923) (@lem5378922 s)). Qed.
Lemma lem5378925 (s : nat -> Prop) : (term494 s) = (term494 s).
Proof. exact (MK_COMB (@lem5378924 s) (@lem5378904 s)). Qed.
Lemma lem5378926 : term495 = term495.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5378925 s)). Qed.
Lemma lem5378927 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378928 : term496 = term496.
Proof. exact (MK_COMB (@lem5378927) (@lem5378926)). Qed.
Lemma lem5378929 (h1 : term421) : term496.
Proof. exact (EQ_MP (@lem5378928) (@lem5378886 h1)). Qed.
Lemma lem5378949 (n : nat) (s : nat -> Prop) (h1 : term461 n s) : term461 n s.
Proof. exact (h1). Qed.
Lemma lem5378953 (m : nat) (n : nat) : (term441 m n) = (term441 m n).
Proof. exact (eq_refl (term441 m n)). Qed.
Lemma lem5378954 (m : nat) : (term442 m) = (term442 m).
Proof. exact (fun_ext (fun n : nat => @lem5378953 m n)). Qed.
Lemma lem5378955 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5378956 (m : nat) : (term443 m) = (term443 m).
Proof. exact (MK_COMB (@lem5378955) (@lem5378954 m)). Qed.
Lemma lem5378957 : term444 = term444.
Proof. exact (fun_ext (fun m : nat => @lem5378956 m)). Qed.
Lemma lem5378958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5378960 : term445 = term445.
Proof. exact (MK_COMB (@lem5378958) (@lem5378957)). Qed.
Lemma lem5378961 (h1 : term445) : term445.
Proof. exact (EQ_MP (@lem5378960) (@lem5378901 h1)). Qed.
Lemma lem5378963 {A : Type'} (P : A -> Prop) (Q : Prop) : (term477 A P Q) = (term476 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5378964 (P : type993) (Q : Prop) : (term479 P Q) = (term478 P Q).
Proof. exact (@lem5378963 (nat -> Prop) P Q). Qed.
Lemma lem5378965 (s : nat -> Prop) : (term481 s) = (term480 s).
Proof. exact (@lem5378964 (term482 s) (@FINITE nat s)). Qed.
Lemma lem5378966 (s : nat -> Prop) (t : nat -> Prop) : (term483 s t) = (term466 s t).
Proof. exact (eq_refl (term483 s t)). Qed.
Lemma lem5378967 (s : nat -> Prop) : (term489 s) = (term482 s).
Proof. exact (fun_ext (fun t : nat -> Prop => @lem5378966 s t)). Qed.
Lemma lem5378968 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378969 (s : nat -> Prop) : (term490 s) = (term491 s).
Proof. exact (MK_COMB (@lem5378968) (@lem5378967 s)). Qed.
Lemma lem5378970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5378971 (s : nat -> Prop) : (term492 s) = (term493 s).
Proof. exact (MK_COMB (@lem5378970) (@lem5378969 s)). Qed.
Lemma lem5378972 (s : nat -> Prop) : (@FINITE nat s) = (@FINITE nat s).
Proof. exact (eq_refl (@FINITE nat s)). Qed.
Lemma lem5378973 (s : nat -> Prop) : (term481 s) = (term494 s).
Proof. exact (MK_COMB (@lem5378971 s) (@lem5378972 s)). Qed.
Lemma lem5378974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5378975 (s : nat -> Prop) : (term497 s) = (term498 s).
Proof. exact (MK_COMB (@lem5378974) (@lem5378973 s)). Qed.
Lemma lem5378976 (s : nat -> Prop) (t : nat -> Prop) : (term483 s t) = (term466 s t).
Proof. exact (eq_refl (term483 s t)). Qed.
Lemma lem5378977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5378978 (s : nat -> Prop) (t : nat -> Prop) : (term484 s t) = (term468 s t).
Proof. exact (MK_COMB (@lem5378977) (@lem5378976 s t)). Qed.
Lemma lem5378979 (s : nat -> Prop) : (@FINITE nat s) = (@FINITE nat s).
Proof. exact (eq_refl (@FINITE nat s)). Qed.
Lemma lem5378980 (t : nat -> Prop) (s : nat -> Prop) : (term485 t s) = (term470 t s).
Proof. exact (MK_COMB (@lem5378978 s t) (@lem5378979 s)). Qed.
Lemma lem5378981 (s : nat -> Prop) : (term486 s) = (term472 s).
Proof. exact (fun_ext (fun t : nat -> Prop => @lem5378980 t s)). Qed.
Lemma lem5378982 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378983 (s : nat -> Prop) : (term480 s) = (term473 s).
Proof. exact (MK_COMB (@lem5378982) (@lem5378981 s)). Qed.
Lemma lem5378984 (s : nat -> Prop) : ((term481 s) = (term480 s)) = ((term494 s) = (term473 s)).
Proof. exact (MK_COMB (@lem5378975 s) (@lem5378983 s)). Qed.
Lemma lem5378985 (s : nat -> Prop) : (term494 s) = (term473 s).
Proof. exact (EQ_MP (@lem5378984 s) (@lem5378965 s)). Qed.
Lemma lem5378986 : term495 = term474.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5378985 s)). Qed.
Lemma lem5378987 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5378988 : term496 = term475.
Proof. exact (MK_COMB (@lem5378987) (@lem5378986)). Qed.
Lemma lem5379001 (t : nat -> Prop) (s : nat -> Prop) : (term470 t s) = (term470 t s).
Proof. exact (eq_refl (term470 t s)). Qed.
Lemma lem5379002 (s : nat -> Prop) : (term472 s) = (term472 s).
Proof. exact (fun_ext (fun t : nat -> Prop => @lem5379001 t s)). Qed.
Lemma lem5379003 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5379004 (s : nat -> Prop) : (term473 s) = (term473 s).
Proof. exact (MK_COMB (@lem5379003) (@lem5379002 s)). Qed.
Lemma lem5379005 : term474 = term474.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5379004 s)). Qed.
Lemma lem5379006 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5379007 : term475 = term475.
Proof. exact (MK_COMB (@lem5379006) (@lem5379005)). Qed.
Lemma lem5379008 : term496 = term475.
Proof. exact (TRANS (@lem5378988) (@lem5379007)). Qed.
Lemma lem5379009 (h1 : term421) : term475.
Proof. exact (EQ_MP (@lem5379008) (@lem5378929 h1)). Qed.
Lemma lem5379018 (_69781 : nat) (h1 : term445) : term499 _69781.
Proof. exact (@lem5378961 h1 _69781). Qed.
Lemma lem5379019 (_69781 : nat) : (term499 _69781) = (term443 _69781).
Proof. exact (eq_refl (term499 _69781)). Qed.
Lemma lem5379020 (_69781 : nat) (h1 : term445) : term443 _69781.
Proof. exact (EQ_MP (@lem5379019 _69781) (@lem5379018 _69781 h1)). Qed.
Lemma lem5379021 (_69781 : nat) (_69782 : nat) (h1 : term445) : term500 _69781 _69782.
Proof. exact (@lem5379020 _69781 h1 _69782). Qed.
Lemma lem5379022 (_69781 : nat) (_69782 : nat) : (term500 _69781 _69782) = (term441 _69781 _69782).
Proof. exact (eq_refl (term500 _69781 _69782)). Qed.
Lemma lem5379024 (_69783 : nat -> Prop) (h1 : term421) : term501 _69783.
Proof. exact (@lem5379009 h1 _69783). Qed.
Lemma lem5379025 (_69783 : nat -> Prop) : (term501 _69783) = (term473 _69783).
Proof. exact (eq_refl (term501 _69783)). Qed.
Lemma lem5379026 (_69783 : nat -> Prop) (h1 : term421) : term473 _69783.
Proof. exact (EQ_MP (@lem5379025 _69783) (@lem5379024 _69783 h1)). Qed.
Lemma lem5379027 (_69783 : nat -> Prop) (_69784 : nat -> Prop) (h1 : term421) : term502 _69783 _69784.
Proof. exact (@lem5379026 _69783 h1 _69784). Qed.
Lemma lem5379028 (_69784 : nat -> Prop) (_69783 : nat -> Prop) : (term502 _69783 _69784) = (term470 _69784 _69783).
Proof. exact (eq_refl (term502 _69783 _69784)). Qed.
Lemma lem5379029 (_69784 : nat -> Prop) (_69783 : nat -> Prop) (h1 : term421) : term470 _69784 _69783.
Proof. exact (EQ_MP (@lem5379028 _69784 _69783) (@lem5379027 _69783 _69784 h1)). Qed.
Lemma lem5379042 (_69784 : nat -> Prop) (_69783 : nat -> Prop) : (term470 _69784 _69783) = (term503 _69784 _69783).
Proof. exact (@lem5376499 (term447 _69784) (term504 _69783 _69784) (@FINITE nat _69783)). Qed.
Lemma lem5379043 (_69784 : nat -> Prop) (_69783 : nat -> Prop) (h1 : term421) : term503 _69784 _69783.
Proof. exact (EQ_MP (@lem5379042 _69784 _69783) (@lem5379029 _69784 _69783 h1)). Qed.
Lemma lem5379047 (n : nat) (s : nat -> Prop) (h1 : term461 n s) : term447 s.
Proof. exact (proj2 (@lem5378949 n s h1)). Qed.
Lemma lem5379049 (_69781 : nat) (_69782 : nat) (h1 : term445) : term441 _69781 _69782.
Proof. exact (EQ_MP (@lem5379022 _69781 _69782) (@lem5379021 _69781 _69782 h1)). Qed.
Lemma lem5379050 (n : nat) (h1 : term445) : term505 n.
Proof. exact (@lem5379049 (NUMERAL 0) n h1). Qed.
Lemma lem5379051 (n : nat) (h1 : term445) : term506 n.
Proof. exact (fun h0 : term507 n => @lem5379050 n h1). Qed.
Lemma lem5379053 (p : Prop) : (term334 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5379054 (n : nat) : (term506 n) = (term505 n).
Proof. exact (@lem5379053 (term505 n)). Qed.
Lemma lem5379055 (n : nat) (h1 : term445) : term505 n.
Proof. exact (EQ_MP (@lem5379054 n) (@lem5379051 n h1)). Qed.
Lemma lem5379057 (n : nat) (s : nat -> Prop) (h1 : term461 n s) : term38 s n.
Proof. exact (proj1 (@lem5378949 n s h1)). Qed.
Lemma lem5379058 (n : nat) (s : nat -> Prop) (h1 : term461 n s) : term508 s n.
Proof. exact (fun h0 : term509 s n => @lem5379057 n s h1). Qed.
Lemma lem5379060 (p : Prop) : (term334 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5379061 (s : nat -> Prop) (n : nat) : (term508 s n) = (term38 s n).
Proof. exact (@lem5379060 (term38 s n)). Qed.
Lemma lem5379062 (n : nat) (s : nat -> Prop) (h1 : term461 n s) : term38 s n.
Proof. exact (EQ_MP (@lem5379061 s n) (@lem5379058 n s h1)). Qed.
Lemma lem5379078 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5379079 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term510 _69784 _69783) = (term511 _69783 _69784).
Proof. exact (@lem5379078 (@FINITE nat _69783) (term504 _69783 _69784)). Qed.
Lemma lem5379085 (_69784 : nat -> Prop) : (term512 _69784) = (term512 _69784).
Proof. exact (eq_refl (term512 _69784)). Qed.
Lemma lem5379086 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term503 _69784 _69783) = (term513 _69783 _69784).
Proof. exact (MK_COMB (@lem5379085 _69784) (@lem5379079 _69783 _69784)). Qed.
Lemma lem5379090 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5379091 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term513 _69783 _69784) = (term514 _69783 _69784).
Proof. exact (@lem5379090 (@FINITE nat _69783) (term447 _69784) (term504 _69783 _69784)). Qed.
Lemma lem5379107 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term503 _69784 _69783) = (term514 _69783 _69784).
Proof. exact (TRANS (@lem5379086 _69783 _69784) (@lem5379091 _69783 _69784)). Qed.
Lemma lem5379108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5379109 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term515 _69784 _69783) = (term516 _69783 _69784).
Proof. exact (MK_COMB (@lem5379108) (@lem5379107 _69783 _69784)). Qed.
Lemma lem5379125 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term514 _69783 _69784) = (term514 _69783 _69784).
Proof. exact (eq_refl (term514 _69783 _69784)). Qed.
Lemma lem5379126 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : ((term503 _69784 _69783) = (term514 _69783 _69784)) = ((term514 _69783 _69784) = (term514 _69783 _69784)).
Proof. exact (MK_COMB (@lem5379109 _69783 _69784) (@lem5379125 _69783 _69784)). Qed.
Lemma lem5379128 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5379129 (x : Prop) : (x = x) = True.
Proof. exact (@lem5379128 Prop x). Qed.
Lemma lem5379130 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : ((term514 _69783 _69784) = (term514 _69783 _69784)) = True.
Proof. exact (@lem5379129 (term514 _69783 _69784)). Qed.
Lemma lem5379131 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : ((term503 _69784 _69783) = (term514 _69783 _69784)) = True.
Proof. exact (TRANS (@lem5379126 _69783 _69784) (@lem5379130 _69783 _69784)). Qed.
Lemma lem5379132 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : True = ((term503 _69784 _69783) = (term514 _69783 _69784)).
Proof. exact (SYM (@lem5379131 _69783 _69784)). Qed.
Lemma lem5379133 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term503 _69784 _69783) = (term514 _69783 _69784).
Proof. exact (EQ_MP (@lem5379132 _69783 _69784) (@lem0)). Qed.
Lemma lem5379134 (_69783 : nat -> Prop) (_69784 : nat -> Prop) (h1 : term421) : term514 _69783 _69784.
Proof. exact (EQ_MP (@lem5379133 _69783 _69784) (@lem5379043 _69784 _69783 h1)). Qed.
Lemma lem5379136 (b : Prop) (a : Prop) : (a \/ b) = (term327 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5379137 (_69784 : nat -> Prop) (_69783 : nat -> Prop) : (term514 _69783 _69784) = (term517 _69784 _69783).
Proof. exact (@lem5379136 (term466 _69783 _69784) (@FINITE nat _69783)). Qed.
Lemma lem5379139 (a : Prop) (b : Prop) : (term347 a b) = (term348 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5379140 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term518 _69783 _69784) = (term519 _69783 _69784).
Proof. exact (@lem5379139 (term447 _69784) (term504 _69783 _69784)). Qed.
Lemma lem5379142 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5379143 (_69784 : nat -> Prop) : (term520 _69784) = (@FINITE nat _69784).
Proof. exact (@lem5379142 (@FINITE nat _69784)). Qed.
Lemma lem5379144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5379145 (_69784 : nat -> Prop) : (term521 _69784) = (term522 _69784).
Proof. exact (MK_COMB (@lem5379144) (@lem5379143 _69784)). Qed.
Lemma lem5379147 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5379148 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term523 _69783 _69784) = (@SUBSET nat _69783 _69784).
Proof. exact (@lem5379147 (@SUBSET nat _69783 _69784)). Qed.
Lemma lem5379149 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term519 _69783 _69784) = (term471 _69783 _69784).
Proof. exact (MK_COMB (@lem5379145 _69784) (@lem5379148 _69783 _69784)). Qed.
Lemma lem5379150 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term518 _69783 _69784) = (term471 _69783 _69784).
Proof. exact (TRANS (@lem5379140 _69783 _69784) (@lem5379149 _69783 _69784)). Qed.
Lemma lem5379151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5379152 (_69783 : nat -> Prop) (_69784 : nat -> Prop) : (term524 _69783 _69784) = (term525 _69783 _69784).
Proof. exact (MK_COMB (@lem5379151) (@lem5379150 _69783 _69784)). Qed.
Lemma lem5379153 (_69783 : nat -> Prop) : (@FINITE nat _69783) = (@FINITE nat _69783).
Proof. exact (eq_refl (@FINITE nat _69783)). Qed.
Lemma lem5379154 (_69784 : nat -> Prop) (_69783 : nat -> Prop) : (term517 _69784 _69783) = (term437 _69784 _69783).
Proof. exact (MK_COMB (@lem5379152 _69783 _69784) (@lem5379153 _69783)). Qed.
Lemma lem5379155 (_69784 : nat -> Prop) (_69783 : nat -> Prop) : (term514 _69783 _69784) = (term437 _69784 _69783).
Proof. exact (TRANS (@lem5379137 _69784 _69783) (@lem5379154 _69784 _69783)). Qed.
Lemma lem5379157 (n : nat) (s : nat -> Prop) (h1 : term445) (h2 : term461 n s) : term526 s n.
Proof. exact (conj (@lem5379055 n h1) (@lem5379062 n s h2)). Qed.
Lemma lem5379159 (_69784 : nat -> Prop) (_69783 : nat -> Prop) (h1 : term421) : term437 _69784 _69783.
Proof. exact (EQ_MP (@lem5379155 _69784 _69783) (@lem5379134 _69783 _69784 h1)). Qed.
Lemma lem5379160 (n : nat) (s : nat -> Prop) (h1 : term421) : term527 n s.
Proof. exact (@lem5379159 (term40 n) s h1). Qed.
Lemma lem5379163 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : @FINITE nat s.
Proof. exact (@lem5379160 n s h1 (@lem5379157 n s h2 h3)). Qed.
Lemma lem5379164 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : term528 s.
Proof. exact (fun h0 : term447 s => @lem5379163 n s h1 h2 h3). Qed.
Lemma lem5379166 (p : Prop) : (term334 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5379167 (s : nat -> Prop) : (term528 s) = (@FINITE nat s).
Proof. exact (@lem5379166 (@FINITE nat s)). Qed.
Lemma lem5379168 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : @FINITE nat s.
Proof. exact (EQ_MP (@lem5379167 s) (@lem5379164 n s h1 h2 h3)). Qed.
Lemma lem5379171 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5379173 (s : nat -> Prop) : (term447 s) = (term529 s).
Proof. exact (@lem5379171 (@FINITE nat s)). Qed.
Lemma lem5379176 (n : nat) (s : nat -> Prop) (h1 : term461 n s) : term529 s.
Proof. exact (EQ_MP (@lem5379173 s) (@lem5379047 n s h1)). Qed.
Lemma lem5379179 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : False.
Proof. exact (@lem5379176 n s h3 (@lem5379168 n s h1 h2 h3)). Qed.
Lemma lem5379180 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : term416.
Proof. exact (fun h0 : ~ False => @lem5379179 n s h1 h2 h3). Qed.
Lemma lem5379182 (p : Prop) : (term334 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5379183 : term416 = False.
Proof. exact (@lem5379182 False). Qed.
Lemma lem5379184 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : False.
Proof. exact (EQ_MP (@lem5379183) (@lem5379180 n s h1 h2 h3)). Qed.
Lemma lem5379185 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : term445 = False.
Proof. exact (prop_ext (fun h4 : term445 => @lem5379184 n s h1 h2 h3) (fun h4 : False => @lem5378961 h2)). Qed.
Lemma lem5379186 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : False.
Proof. exact (EQ_MP (@lem5379185 n s h1 h2 h3) (@lem5378961 h2)). Qed.
Lemma lem5379187 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : (term461 n s) = False.
Proof. exact (prop_ext (fun h4 : term461 n s => @lem5379186 n s h1 h2 h3) (fun h4 : False => @lem5378949 n s h3)). Qed.
Lemma lem5379188 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : False.
Proof. exact (EQ_MP (@lem5379187 n s h1 h2 h3) (@lem5378949 n s h3)). Qed.
Lemma lem5379189 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : term445 = False.
Proof. exact (prop_ext (fun h4 : term445 => @lem5379188 n s h1 h2 h3) (fun h4 : False => @lem5378901 h2)). Qed.
Lemma lem5379190 (n : nat) (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term461 n s) : False.
Proof. exact (EQ_MP (@lem5379189 n s h1 h2 h3) (@lem5378901 h2)). Qed.
Lemma lem5379191 (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term420 s) : False.
Proof. exact (ex_elim (@lem5378712 s h3) (fun n : nat => fun h0 : term463 s n => @lem5379190 n s h1 h2 h0)). Qed.
Lemma lem5379192 (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term420 s) : term445 = False.
Proof. exact (prop_ext (fun h4 : term445 => @lem5379191 s h1 h2 h3) (fun h4 : False => @lem5378732 h2)). Qed.
Lemma lem5379193 (s : nat -> Prop) (h1 : term421) (h2 : term445) (h3 : term420 s) : False.
Proof. exact (EQ_MP (@lem5379192 s h1 h2 h3) (@lem5378732 h2)). Qed.
Lemma lem5379194 (s : nat -> Prop) (h1 : term445) (h2 : term420 s) : term426.
Proof. exact (fun h0 : term421 => @lem5379193 s h0 h1 h2). Qed.
Lemma lem5379195 : term426 = term427.
Proof. exact (@lem69 term421). Qed.
Lemma lem5379196 (s : nat -> Prop) (h1 : term445) (h2 : term420 s) : term427.
Proof. exact (EQ_MP (@lem5379195) (@lem5379194 s h1 h2)). Qed.
Lemma lem5379197 (s : nat -> Prop) (h1 : term420 s) : term430.
Proof. exact (fun h0 : term445 => @lem5379196 s h0 h1). Qed.
Lemma lem5379198 (s : nat -> Prop) : term432 s.
Proof. exact (fun h0 : term420 s => @lem5379197 s h0). Qed.
Lemma lem5379203 : term436.
Proof. exact (fun s : nat -> Prop => @lem5379198 s). Qed.
Lemma lem5379204 : term435.
Proof. exact (EQ_MP (@lem5378667) (@lem5379203)). Qed.
Lemma lem5379205 (s : nat -> Prop) : term530 s.
Proof. exact (@lem5379204 s). Qed.
Lemma lem5379206 (s : nat -> Prop) : (term530 s) = (term422 s).
Proof. exact (eq_refl (term530 s)). Qed.
Lemma lem5379207 (s : nat -> Prop) : term422 s.
Proof. exact (EQ_MP (@lem5379206 s) (@lem5379205 s)). Qed.
Lemma lem5379209 (s : nat -> Prop) : term422 s.
Proof. exact (@lem5378518 s (@lem5379207 s)). Qed.
Lemma lem5379210 (s : nat -> Prop) (h1 : term420 s) : term429.
Proof. exact (@lem5379209 s (@lem5378501 s h1)). Qed.
Lemma lem5379211 (s : nat -> Prop) (h1 : term420 s) : term426.
Proof. exact (@lem5379210 s h1 (@lem5329299)). Qed.
Lemma lem5379212 (s : nat -> Prop) (h1 : term420 s) : False.
Proof. exact (@lem5379211 s h1 (@lem5378502)). Qed.
Lemma lem5379213 (s : nat -> Prop) (h1 : term420 s) : (term420 s) = False.
Proof. exact (prop_ext (fun h2 : term420 s => @lem5379212 s h1) (fun h2 : False => @lem5378501 s h1)). Qed.
Lemma lem5379214 (s : nat -> Prop) (h1 : term420 s) : False.
Proof. exact (EQ_MP (@lem5379213 s h1) (@lem5378501 s h1)). Qed.
Lemma lem5379215 (s : nat -> Prop) : term419 s.
Proof. exact (fun h0 : term420 s => @lem5379214 s h0). Qed.
Lemma lem5379216 (s : nat -> Prop) : term418 s.
Proof. exact (EQ_MP (@lem5378500 s) (@lem5379215 s)). Qed.
Lemma lem5379217 (s : nat -> Prop) : term531 s.
Proof. exact (conj (@lem5378496 s) (@lem5379216 s)). Qed.
Lemma lem5379218 (s : nat -> Prop) : (term531 s) = ((@FINITE nat s) = (term53 s)).
Proof. exact (@lem32 (@FINITE nat s) (term53 s)). Qed.
Lemma lem5379219 (s : nat -> Prop) : (@FINITE nat s) = (term53 s).
Proof. exact (EQ_MP (@lem5379218 s) (@lem5379217 s)). Qed.
Lemma lem5379224 : term532.
Proof. exact (fun s : nat -> Prop => @lem5379219 s). Qed.
