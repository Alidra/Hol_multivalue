Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_EQ_ODD_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_POW_EQ_ODD_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
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
Lemma lem1665332 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1665333 : term1 = term2.
Proof. exact (@lem1665332 term1). Qed.
Lemma lem1665334 : term2 = term1.
Proof. exact (SYM (@lem1665333)). Qed.
Lemma lem1665335 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1665338 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1665339 : term5.
Proof. exact (fun h0 : term4 => @lem1665338 h0). Qed.
Lemma lem1665340 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1665341 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1665342 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1665340 h2 (@lem1665341 h1)). Qed.
Lemma lem1665343 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1665342 h1 h0). Qed.
Lemma lem1665344 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1665345 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1665343 h1 (@lem1665344 h2)). Qed.
Lemma lem1665346 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1665345 h0 h1). Qed.
Lemma lem1665347 : term7.
Proof. exact (fun h0 : term5 => @lem1665346 h0). Qed.
Lemma lem1665350 : term5.
Proof. exact (@lem1665347 (@lem1665339)). Qed.
Lemma lem1665370 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1665371 : term8 = term9.
Proof. exact (@lem1665370 term10). Qed.
Lemma lem1665386 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1665393 : term4 = term12.
Proof. exact (MK_COMB (@lem1665386) (@lem1665371)). Qed.
Lemma lem1665402 (n : nat) (x : real) (y : real) : (term13 n x y) = (term13 n x y).
Proof. exact (eq_refl (term13 n x y)). Qed.
Lemma lem1665403 (n : nat) (x : real) : (term14 n x) = (term14 n x).
Proof. exact (fun_ext (fun y : real => @lem1665402 n x y)). Qed.
Lemma lem1665404 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665405 (n : nat) (x : real) : (term15 n x) = (term15 n x).
Proof. exact (MK_COMB (@lem1665404) (@lem1665403 n x)). Qed.
Lemma lem1665406 (n : nat) : (term16 n) = (term16 n).
Proof. exact (fun_ext (fun x : real => @lem1665405 n x)). Qed.
Lemma lem1665407 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665408 (n : nat) : (term17 n) = (term17 n).
Proof. exact (MK_COMB (@lem1665407) (@lem1665406 n)). Qed.
Lemma lem1665409 : term18 = term18.
Proof. exact (fun_ext (fun n : nat => @lem1665408 n)). Qed.
Lemma lem1665410 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1665411 : term10 = term10.
Proof. exact (MK_COMB (@lem1665410) (@lem1665409)). Qed.
Lemma lem1665412 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1665413 : term9 = term9.
Proof. exact (MK_COMB (@lem1665412) (@lem1665411)). Qed.
Lemma lem1665422 (n : nat) (x : real) (y : real) : (term19 n x y) = (term19 n x y).
Proof. exact (eq_refl (term19 n x y)). Qed.
Lemma lem1665423 (n : nat) (x : real) : (term20 n x) = (term20 n x).
Proof. exact (fun_ext (fun y : real => @lem1665422 n x y)). Qed.
Lemma lem1665424 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665425 (n : nat) (x : real) : (term21 n x) = (term21 n x).
Proof. exact (MK_COMB (@lem1665424) (@lem1665423 n x)). Qed.
Lemma lem1665426 (n : nat) : (term22 n) = (term22 n).
Proof. exact (fun_ext (fun x : real => @lem1665425 n x)). Qed.
Lemma lem1665427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665428 (n : nat) : (term23 n) = (term23 n).
Proof. exact (MK_COMB (@lem1665427) (@lem1665426 n)). Qed.
Lemma lem1665429 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem1665428 n)). Qed.
Lemma lem1665430 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1665431 : term1 = term1.
Proof. exact (MK_COMB (@lem1665430) (@lem1665429)). Qed.
Lemma lem1665432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1665433 : term3 = term3.
Proof. exact (MK_COMB (@lem1665432) (@lem1665431)). Qed.
Lemma lem1665434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1665435 : term11 = term11.
Proof. exact (MK_COMB (@lem1665434) (@lem1665433)). Qed.
Lemma lem1665436 : term12 = term12.
Proof. exact (MK_COMB (@lem1665435) (@lem1665413)). Qed.
Lemma lem1665483 : term4 = term12.
Proof. exact (TRANS (@lem1665393) (@lem1665436)). Qed.
Lemma lem1665484 : term12 = term4.
Proof. exact (SYM (@lem1665483)). Qed.
Lemma lem1665485 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1665486 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1665497 (n : nat) (x : real) (y : real) : (term25 n x y) = (term26 n x y).
Proof. exact (@lem17362 (term27 x y n) (x = y)). Qed.
Lemma lem1665498 (P : real -> Prop) : (term28 P) = (term29 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1665499 (n : nat) (x : real) : (term30 n x) = (term31 n x).
Proof. exact (@lem1665498 (term20 n x)). Qed.
Lemma lem1665500 (n : nat) (x : real) (y : real) : (term32 n x y) = (term19 n x y).
Proof. exact (eq_refl (term32 n x y)). Qed.
Lemma lem1665501 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1665502 (n : nat) (x : real) (y : real) : (term33 n x y) = (term25 n x y).
Proof. exact (MK_COMB (@lem1665501) (@lem1665500 n x y)). Qed.
Lemma lem1665503 (n : nat) (x : real) (y : real) : (term33 n x y) = (term26 n x y).
Proof. exact (TRANS (@lem1665502 n x y) (@lem1665497 n x y)). Qed.
Lemma lem1665504 (n : nat) (x : real) : (term34 n x) = (term35 n x).
Proof. exact (fun_ext (fun y : real => @lem1665503 n x y)). Qed.
Lemma lem1665505 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1665506 (n : nat) (x : real) : (term31 n x) = (term36 n x).
Proof. exact (MK_COMB (@lem1665505) (@lem1665504 n x)). Qed.
Lemma lem1665507 (n : nat) (x : real) : (term30 n x) = (term36 n x).
Proof. exact (TRANS (@lem1665499 n x) (@lem1665506 n x)). Qed.
Lemma lem1665508 (P : real -> Prop) : (term28 P) = (term29 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1665509 (n : nat) : (term37 n) = (term38 n).
Proof. exact (@lem1665508 (term22 n)). Qed.
Lemma lem1665510 (n : nat) (x : real) : (term39 n x) = (term21 n x).
Proof. exact (eq_refl (term39 n x)). Qed.
Lemma lem1665511 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1665512 (n : nat) (x : real) : (term40 n x) = (term30 n x).
Proof. exact (MK_COMB (@lem1665511) (@lem1665510 n x)). Qed.
Lemma lem1665513 (n : nat) (x : real) : (term40 n x) = (term36 n x).
Proof. exact (TRANS (@lem1665512 n x) (@lem1665507 n x)). Qed.
Lemma lem1665514 (n : nat) : (term41 n) = (term42 n).
Proof. exact (fun_ext (fun x : real => @lem1665513 n x)). Qed.
Lemma lem1665515 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1665516 (n : nat) : (term38 n) = (term43 n).
Proof. exact (MK_COMB (@lem1665515) (@lem1665514 n)). Qed.
Lemma lem1665517 (n : nat) : (term37 n) = (term43 n).
Proof. exact (TRANS (@lem1665509 n) (@lem1665516 n)). Qed.
Lemma lem1665518 (P : nat -> Prop) : (term44 P) = (term45 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1665519 : term3 = term46.
Proof. exact (@lem1665518 term24). Qed.
Lemma lem1665520 (n : nat) : (term47 n) = (term23 n).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem1665521 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1665522 (n : nat) : (term48 n) = (term37 n).
Proof. exact (MK_COMB (@lem1665521) (@lem1665520 n)). Qed.
Lemma lem1665523 (n : nat) : (term48 n) = (term43 n).
Proof. exact (TRANS (@lem1665522 n) (@lem1665517 n)). Qed.
Lemma lem1665524 : term49 = term50.
Proof. exact (fun_ext (fun n : nat => @lem1665523 n)). Qed.
Lemma lem1665525 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1665526 : term46 = term51.
Proof. exact (MK_COMB (@lem1665525) (@lem1665524)). Qed.
Lemma lem1665587 : term3 = term51.
Proof. exact (TRANS (@lem1665519) (@lem1665526)). Qed.
Lemma lem1665588 (h1 : term3) : term51.
Proof. exact (EQ_MP (@lem1665587) (@lem1665485 h1)). Qed.
Lemma lem1665604 (n : nat) (x : real) (y : real) : (((real_pow x n) = (real_pow y n)) = (x = y)) = (term52 n x y).
Proof. exact (@lem17784 ((real_pow x n) = (real_pow y n)) (x = y)). Qed.
Lemma lem1665606 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1665607 (n : nat) (x : real) (y : real) : (term54 n x y) = (term55 n x y).
Proof. exact (MK_COMB (@lem1665606 n) (@lem1665604 n x y)). Qed.
Lemma lem1665608 (n : nat) (x : real) (y : real) : (term13 n x y) = (term54 n x y).
Proof. exact (@lem17265 (Coq.Arith.PeanoNat.Nat.Odd n) (((real_pow x n) = (real_pow y n)) = (x = y))). Qed.
Lemma lem1665609 (n : nat) (x : real) (y : real) : (term13 n x y) = (term55 n x y).
Proof. exact (TRANS (@lem1665608 n x y) (@lem1665607 n x y)). Qed.
Lemma lem1665610 (n : nat) (x : real) : (term14 n x) = (term56 n x).
Proof. exact (fun_ext (fun y : real => @lem1665609 n x y)). Qed.
Lemma lem1665611 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665612 (n : nat) (x : real) : (term15 n x) = (term57 n x).
Proof. exact (MK_COMB (@lem1665611) (@lem1665610 n x)). Qed.
Lemma lem1665613 (n : nat) : (term16 n) = (term58 n).
Proof. exact (fun_ext (fun x : real => @lem1665612 n x)). Qed.
Lemma lem1665614 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665615 (n : nat) : (term17 n) = (term59 n).
Proof. exact (MK_COMB (@lem1665614) (@lem1665613 n)). Qed.
Lemma lem1665616 : term18 = term60.
Proof. exact (fun_ext (fun n : nat => @lem1665615 n)). Qed.
Lemma lem1665617 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1665618 : term10 = term61.
Proof. exact (MK_COMB (@lem1665617) (@lem1665616)). Qed.
Lemma lem1665628 {A : Type'} (P : Prop) (Q : A -> Prop) : (term62 A P Q) = (term63 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem1665629 (P : Prop) (Q : real -> Prop) : (term64 P Q) = (term65 P Q).
Proof. exact (@lem1665628 real P Q). Qed.
Lemma lem1665630 (n : nat) (x : real) : (term66 n x) = (term67 n x).
Proof. exact (@lem1665629 (term68 n) (term69 n x)). Qed.
Lemma lem1665631 (n : nat) (x : real) (y : real) : (term70 n x y) = (term52 n x y).
Proof. exact (eq_refl (term70 n x y)). Qed.
Lemma lem1665632 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1665633 (n : nat) (x : real) (y : real) : (term71 n x y) = (term55 n x y).
Proof. exact (MK_COMB (@lem1665632 n) (@lem1665631 n x y)). Qed.
Lemma lem1665634 (n : nat) (x : real) : (term72 n x) = (term56 n x).
Proof. exact (fun_ext (fun y : real => @lem1665633 n x y)). Qed.
Lemma lem1665635 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665636 (n : nat) (x : real) : (term66 n x) = (term57 n x).
Proof. exact (MK_COMB (@lem1665635) (@lem1665634 n x)). Qed.
Lemma lem1665637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1665638 (n : nat) (x : real) : (term73 n x) = (term74 n x).
Proof. exact (MK_COMB (@lem1665637) (@lem1665636 n x)). Qed.
Lemma lem1665639 (n : nat) (x : real) (y : real) : (term70 n x y) = (term52 n x y).
Proof. exact (eq_refl (term70 n x y)). Qed.
Lemma lem1665640 (n : nat) (x : real) : (term75 n x) = (term69 n x).
Proof. exact (fun_ext (fun y : real => @lem1665639 n x y)). Qed.
Lemma lem1665641 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665642 (n : nat) (x : real) : (term76 n x) = (term77 n x).
Proof. exact (MK_COMB (@lem1665641) (@lem1665640 n x)). Qed.
Lemma lem1665643 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1665644 (n : nat) (x : real) : (term67 n x) = (term78 n x).
Proof. exact (MK_COMB (@lem1665643 n) (@lem1665642 n x)). Qed.
Lemma lem1665645 (n : nat) (x : real) : ((term66 n x) = (term67 n x)) = ((term57 n x) = (term78 n x)).
Proof. exact (MK_COMB (@lem1665638 n x) (@lem1665644 n x)). Qed.
Lemma lem1665646 (n : nat) (x : real) : (term57 n x) = (term78 n x).
Proof. exact (EQ_MP (@lem1665645 n x) (@lem1665630 n x)). Qed.
Lemma lem1665648 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1665649 (P : real -> Prop) (Q : real -> Prop) : (term81 P Q) = (term82 P Q).
Proof. exact (@lem1665648 real P Q). Qed.
Lemma lem1665650 (n : nat) (x : real) : (term83 n x) = (term84 n x).
Proof. exact (@lem1665649 (term85 n x) (term86 n x)). Qed.
Lemma lem1665651 (n : nat) (x : real) (y : real) : (term87 n x y) = (term88 n x y).
Proof. exact (eq_refl (term87 n x y)). Qed.
Lemma lem1665652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1665653 (n : nat) (x : real) (y : real) : (term89 n x y) = (term90 n x y).
Proof. exact (MK_COMB (@lem1665652) (@lem1665651 n x y)). Qed.
Lemma lem1665654 (n : nat) (x : real) (y : real) : (term91 n x y) = (term92 n x y).
Proof. exact (eq_refl (term91 n x y)). Qed.
Lemma lem1665655 (n : nat) (x : real) (y : real) : (term93 n x y) = (term52 n x y).
Proof. exact (MK_COMB (@lem1665653 n x y) (@lem1665654 n x y)). Qed.
Lemma lem1665656 (n : nat) (x : real) : (term94 n x) = (term69 n x).
Proof. exact (fun_ext (fun y : real => @lem1665655 n x y)). Qed.
Lemma lem1665657 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665658 (n : nat) (x : real) : (term83 n x) = (term77 n x).
Proof. exact (MK_COMB (@lem1665657) (@lem1665656 n x)). Qed.
Lemma lem1665659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1665660 (n : nat) (x : real) : (term95 n x) = (term96 n x).
Proof. exact (MK_COMB (@lem1665659) (@lem1665658 n x)). Qed.
Lemma lem1665661 (n : nat) (x : real) (y : real) : (term87 n x y) = (term88 n x y).
Proof. exact (eq_refl (term87 n x y)). Qed.
Lemma lem1665662 (n : nat) (x : real) : (term97 n x) = (term85 n x).
Proof. exact (fun_ext (fun y : real => @lem1665661 n x y)). Qed.
Lemma lem1665663 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665664 (n : nat) (x : real) : (term98 n x) = (term99 n x).
Proof. exact (MK_COMB (@lem1665663) (@lem1665662 n x)). Qed.
Lemma lem1665665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1665666 (n : nat) (x : real) : (term100 n x) = (term101 n x).
Proof. exact (MK_COMB (@lem1665665) (@lem1665664 n x)). Qed.
Lemma lem1665667 (n : nat) (x : real) (y : real) : (term91 n x y) = (term92 n x y).
Proof. exact (eq_refl (term91 n x y)). Qed.
Lemma lem1665668 (n : nat) (x : real) : (term102 n x) = (term86 n x).
Proof. exact (fun_ext (fun y : real => @lem1665667 n x y)). Qed.
Lemma lem1665669 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665670 (n : nat) (x : real) : (term103 n x) = (term104 n x).
Proof. exact (MK_COMB (@lem1665669) (@lem1665668 n x)). Qed.
Lemma lem1665671 (n : nat) (x : real) : (term84 n x) = (term105 n x).
Proof. exact (MK_COMB (@lem1665666 n x) (@lem1665670 n x)). Qed.
Lemma lem1665672 (n : nat) (x : real) : ((term83 n x) = (term84 n x)) = ((term77 n x) = (term105 n x)).
Proof. exact (MK_COMB (@lem1665660 n x) (@lem1665671 n x)). Qed.
Lemma lem1665673 (n : nat) (x : real) : (term77 n x) = (term105 n x).
Proof. exact (EQ_MP (@lem1665672 n x) (@lem1665650 n x)). Qed.
Lemma lem1665770 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1665771 (n : nat) (x : real) : (term78 n x) = (term106 n x).
Proof. exact (MK_COMB (@lem1665770 n) (@lem1665673 n x)). Qed.
Lemma lem1665772 (n : nat) (x : real) : (term57 n x) = (term106 n x).
Proof. exact (TRANS (@lem1665646 n x) (@lem1665771 n x)). Qed.
Lemma lem1665773 (n : nat) : (term58 n) = (term107 n).
Proof. exact (fun_ext (fun x : real => @lem1665772 n x)). Qed.
Lemma lem1665774 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665775 (n : nat) : (term59 n) = (term108 n).
Proof. exact (MK_COMB (@lem1665774) (@lem1665773 n)). Qed.
Lemma lem1665777 {A : Type'} (P : Prop) (Q : A -> Prop) : (term62 A P Q) = (term63 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem1665778 (P : Prop) (Q : real -> Prop) : (term64 P Q) = (term65 P Q).
Proof. exact (@lem1665777 real P Q). Qed.
Lemma lem1665779 (n : nat) : (term109 n) = (term110 n).
Proof. exact (@lem1665778 (term68 n) (term111 n)). Qed.
Lemma lem1665780 (n : nat) (x : real) : (term112 n x) = (term105 n x).
Proof. exact (eq_refl (term112 n x)). Qed.
Lemma lem1665781 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1665782 (n : nat) (x : real) : (term113 n x) = (term106 n x).
Proof. exact (MK_COMB (@lem1665781 n) (@lem1665780 n x)). Qed.
Lemma lem1665783 (n : nat) : (term114 n) = (term107 n).
Proof. exact (fun_ext (fun x : real => @lem1665782 n x)). Qed.
Lemma lem1665784 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665785 (n : nat) : (term109 n) = (term108 n).
Proof. exact (MK_COMB (@lem1665784) (@lem1665783 n)). Qed.
Lemma lem1665786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1665787 (n : nat) : (term115 n) = (term116 n).
Proof. exact (MK_COMB (@lem1665786) (@lem1665785 n)). Qed.
Lemma lem1665788 (n : nat) (x : real) : (term112 n x) = (term105 n x).
Proof. exact (eq_refl (term112 n x)). Qed.
Lemma lem1665789 (n : nat) : (term117 n) = (term111 n).
Proof. exact (fun_ext (fun x : real => @lem1665788 n x)). Qed.
Lemma lem1665790 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665791 (n : nat) : (term118 n) = (term119 n).
Proof. exact (MK_COMB (@lem1665790) (@lem1665789 n)). Qed.
Lemma lem1665792 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1665793 (n : nat) : (term110 n) = (term120 n).
Proof. exact (MK_COMB (@lem1665792 n) (@lem1665791 n)). Qed.
Lemma lem1665794 (n : nat) : ((term109 n) = (term110 n)) = ((term108 n) = (term120 n)).
Proof. exact (MK_COMB (@lem1665787 n) (@lem1665793 n)). Qed.
Lemma lem1665795 (n : nat) : (term108 n) = (term120 n).
Proof. exact (EQ_MP (@lem1665794 n) (@lem1665779 n)). Qed.
Lemma lem1665797 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1665798 (P : real -> Prop) (Q : real -> Prop) : (term81 P Q) = (term82 P Q).
Proof. exact (@lem1665797 real P Q). Qed.
Lemma lem1665799 (n : nat) : (term121 n) = (term122 n).
Proof. exact (@lem1665798 (term123 n) (term124 n)). Qed.
Lemma lem1665800 (n : nat) (x : real) : (term125 n x) = (term99 n x).
Proof. exact (eq_refl (term125 n x)). Qed.
Lemma lem1665801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1665802 (n : nat) (x : real) : (term126 n x) = (term101 n x).
Proof. exact (MK_COMB (@lem1665801) (@lem1665800 n x)). Qed.
Lemma lem1665803 (n : nat) (x : real) : (term127 n x) = (term104 n x).
Proof. exact (eq_refl (term127 n x)). Qed.
Lemma lem1665804 (n : nat) (x : real) : (term128 n x) = (term105 n x).
Proof. exact (MK_COMB (@lem1665802 n x) (@lem1665803 n x)). Qed.
Lemma lem1665805 (n : nat) : (term129 n) = (term111 n).
Proof. exact (fun_ext (fun x : real => @lem1665804 n x)). Qed.
Lemma lem1665806 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665807 (n : nat) : (term121 n) = (term119 n).
Proof. exact (MK_COMB (@lem1665806) (@lem1665805 n)). Qed.
Lemma lem1665808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1665809 (n : nat) : (term130 n) = (term131 n).
Proof. exact (MK_COMB (@lem1665808) (@lem1665807 n)). Qed.
Lemma lem1665810 (n : nat) (x : real) : (term125 n x) = (term99 n x).
Proof. exact (eq_refl (term125 n x)). Qed.
Lemma lem1665811 (n : nat) : (term132 n) = (term123 n).
Proof. exact (fun_ext (fun x : real => @lem1665810 n x)). Qed.
Lemma lem1665812 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665813 (n : nat) : (term133 n) = (term134 n).
Proof. exact (MK_COMB (@lem1665812) (@lem1665811 n)). Qed.
Lemma lem1665814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1665815 (n : nat) : (term135 n) = (term136 n).
Proof. exact (MK_COMB (@lem1665814) (@lem1665813 n)). Qed.
Lemma lem1665816 (n : nat) (x : real) : (term127 n x) = (term104 n x).
Proof. exact (eq_refl (term127 n x)). Qed.
Lemma lem1665817 (n : nat) : (term137 n) = (term124 n).
Proof. exact (fun_ext (fun x : real => @lem1665816 n x)). Qed.
Lemma lem1665818 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1665819 (n : nat) : (term138 n) = (term139 n).
Proof. exact (MK_COMB (@lem1665818) (@lem1665817 n)). Qed.
Lemma lem1665820 (n : nat) : (term122 n) = (term140 n).
Proof. exact (MK_COMB (@lem1665815 n) (@lem1665819 n)). Qed.
Lemma lem1665821 (n : nat) : ((term121 n) = (term122 n)) = ((term119 n) = (term140 n)).
Proof. exact (MK_COMB (@lem1665809 n) (@lem1665820 n)). Qed.
Lemma lem1665822 (n : nat) : (term119 n) = (term140 n).
Proof. exact (EQ_MP (@lem1665821 n) (@lem1665799 n)). Qed.
Lemma lem1665927 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1665928 (n : nat) : (term120 n) = (term141 n).
Proof. exact (MK_COMB (@lem1665927 n) (@lem1665822 n)). Qed.
Lemma lem1665929 (n : nat) : (term108 n) = (term141 n).
Proof. exact (TRANS (@lem1665795 n) (@lem1665928 n)). Qed.
Lemma lem1665930 (n : nat) : (term59 n) = (term141 n).
Proof. exact (TRANS (@lem1665775 n) (@lem1665929 n)). Qed.
Lemma lem1665931 : term60 = term142.
Proof. exact (fun_ext (fun n : nat => @lem1665930 n)). Qed.
Lemma lem1665932 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1665983 : term61 = term143.
Proof. exact (MK_COMB (@lem1665932) (@lem1665931)). Qed.
Lemma lem1665984 : term10 = term143.
Proof. exact (TRANS (@lem1665618) (@lem1665983)). Qed.
Lemma lem1665985 (h1 : term10) : term143.
Proof. exact (EQ_MP (@lem1665984) (@lem1665486 h1)). Qed.
Lemma lem1665986 (n : nat) (h1 : term43 n) : term43 n.
Proof. exact (h1). Qed.
Lemma lem1665987 (n : nat) (x : real) (h1 : term36 n x) : term36 n x.
Proof. exact (h1). Qed.
Lemma lem1666011 (n : nat) (x : real) (y : real) : (term92 n x y) = (term92 n x y).
Proof. exact (eq_refl (term92 n x y)). Qed.
Lemma lem1666012 (n : nat) (x : real) : (term86 n x) = (term86 n x).
Proof. exact (fun_ext (fun y : real => @lem1666011 n x y)). Qed.
Lemma lem1666013 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666014 (n : nat) (x : real) : (term104 n x) = (term104 n x).
Proof. exact (MK_COMB (@lem1666013) (@lem1666012 n x)). Qed.
Lemma lem1666015 (n : nat) : (term124 n) = (term124 n).
Proof. exact (fun_ext (fun x : real => @lem1666014 n x)). Qed.
Lemma lem1666016 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666017 (n : nat) : (term139 n) = (term139 n).
Proof. exact (MK_COMB (@lem1666016) (@lem1666015 n)). Qed.
Lemma lem1666040 (n : nat) (x : real) (y : real) : (term88 n x y) = (term88 n x y).
Proof. exact (eq_refl (term88 n x y)). Qed.
Lemma lem1666041 (n : nat) (x : real) : (term85 n x) = (term85 n x).
Proof. exact (fun_ext (fun y : real => @lem1666040 n x y)). Qed.
Lemma lem1666042 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666043 (n : nat) (x : real) : (term99 n x) = (term99 n x).
Proof. exact (MK_COMB (@lem1666042) (@lem1666041 n x)). Qed.
Lemma lem1666044 (n : nat) : (term123 n) = (term123 n).
Proof. exact (fun_ext (fun x : real => @lem1666043 n x)). Qed.
Lemma lem1666045 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666046 (n : nat) : (term134 n) = (term134 n).
Proof. exact (MK_COMB (@lem1666045) (@lem1666044 n)). Qed.
Lemma lem1666047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1666048 (n : nat) : (term136 n) = (term136 n).
Proof. exact (MK_COMB (@lem1666047) (@lem1666046 n)). Qed.
Lemma lem1666049 (n : nat) : (term140 n) = (term140 n).
Proof. exact (MK_COMB (@lem1666048 n) (@lem1666017 n)). Qed.
Lemma lem1666056 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1666057 (n : nat) : (term141 n) = (term141 n).
Proof. exact (MK_COMB (@lem1666056 n) (@lem1666049 n)). Qed.
Lemma lem1666058 : term142 = term142.
Proof. exact (fun_ext (fun n : nat => @lem1666057 n)). Qed.
Lemma lem1666059 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1666060 : term143 = term143.
Proof. exact (MK_COMB (@lem1666059) (@lem1666058)). Qed.
Lemma lem1666061 (h1 : term10) : term143.
Proof. exact (EQ_MP (@lem1666060) (@lem1665985 h1)). Qed.
Lemma lem1666091 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : term26 n x y.
Proof. exact (h1). Qed.
Lemma lem1666093 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : term27 x y n.
Proof. exact (proj1 (@lem1666091 n x y h1)). Qed.
Lemma lem1666097 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem1666098 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term81 P Q).
Proof. exact (@lem1666097 real P Q). Qed.
Lemma lem1666099 (n : nat) : (term122 n) = (term121 n).
Proof. exact (@lem1666098 (term123 n) (term124 n)). Qed.
Lemma lem1666100 (n : nat) (x : real) : (term125 n x) = (term99 n x).
Proof. exact (eq_refl (term125 n x)). Qed.
Lemma lem1666101 (n : nat) : (term132 n) = (term123 n).
Proof. exact (fun_ext (fun x : real => @lem1666100 n x)). Qed.
Lemma lem1666102 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666103 (n : nat) : (term133 n) = (term134 n).
Proof. exact (MK_COMB (@lem1666102) (@lem1666101 n)). Qed.
Lemma lem1666104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1666105 (n : nat) : (term135 n) = (term136 n).
Proof. exact (MK_COMB (@lem1666104) (@lem1666103 n)). Qed.
Lemma lem1666106 (n : nat) (x : real) : (term127 n x) = (term104 n x).
Proof. exact (eq_refl (term127 n x)). Qed.
Lemma lem1666107 (n : nat) : (term137 n) = (term124 n).
Proof. exact (fun_ext (fun x : real => @lem1666106 n x)). Qed.
Lemma lem1666108 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666109 (n : nat) : (term138 n) = (term139 n).
Proof. exact (MK_COMB (@lem1666108) (@lem1666107 n)). Qed.
Lemma lem1666110 (n : nat) : (term122 n) = (term140 n).
Proof. exact (MK_COMB (@lem1666105 n) (@lem1666109 n)). Qed.
Lemma lem1666111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1666112 (n : nat) : (term144 n) = (term145 n).
Proof. exact (MK_COMB (@lem1666111) (@lem1666110 n)). Qed.
Lemma lem1666113 (n : nat) (x : real) : (term125 n x) = (term99 n x).
Proof. exact (eq_refl (term125 n x)). Qed.
Lemma lem1666114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1666115 (n : nat) (x : real) : (term126 n x) = (term101 n x).
Proof. exact (MK_COMB (@lem1666114) (@lem1666113 n x)). Qed.
Lemma lem1666116 (n : nat) (x : real) : (term127 n x) = (term104 n x).
Proof. exact (eq_refl (term127 n x)). Qed.
Lemma lem1666117 (n : nat) (x : real) : (term128 n x) = (term105 n x).
Proof. exact (MK_COMB (@lem1666115 n x) (@lem1666116 n x)). Qed.
Lemma lem1666118 (n : nat) : (term129 n) = (term111 n).
Proof. exact (fun_ext (fun x : real => @lem1666117 n x)). Qed.
Lemma lem1666119 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666120 (n : nat) : (term121 n) = (term119 n).
Proof. exact (MK_COMB (@lem1666119) (@lem1666118 n)). Qed.
Lemma lem1666121 (n : nat) : ((term122 n) = (term121 n)) = ((term140 n) = (term119 n)).
Proof. exact (MK_COMB (@lem1666112 n) (@lem1666120 n)). Qed.
Lemma lem1666122 (n : nat) : (term140 n) = (term119 n).
Proof. exact (EQ_MP (@lem1666121 n) (@lem1666099 n)). Qed.
Lemma lem1666124 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem1666125 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term81 P Q).
Proof. exact (@lem1666124 real P Q). Qed.
Lemma lem1666126 (n : nat) (x : real) : (term84 n x) = (term83 n x).
Proof. exact (@lem1666125 (term85 n x) (term86 n x)). Qed.
Lemma lem1666127 (n : nat) (x : real) (y : real) : (term87 n x y) = (term88 n x y).
Proof. exact (eq_refl (term87 n x y)). Qed.
Lemma lem1666128 (n : nat) (x : real) : (term97 n x) = (term85 n x).
Proof. exact (fun_ext (fun y : real => @lem1666127 n x y)). Qed.
Lemma lem1666129 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666130 (n : nat) (x : real) : (term98 n x) = (term99 n x).
Proof. exact (MK_COMB (@lem1666129) (@lem1666128 n x)). Qed.
Lemma lem1666131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1666132 (n : nat) (x : real) : (term100 n x) = (term101 n x).
Proof. exact (MK_COMB (@lem1666131) (@lem1666130 n x)). Qed.
Lemma lem1666133 (n : nat) (x : real) (y : real) : (term91 n x y) = (term92 n x y).
Proof. exact (eq_refl (term91 n x y)). Qed.
Lemma lem1666134 (n : nat) (x : real) : (term102 n x) = (term86 n x).
Proof. exact (fun_ext (fun y : real => @lem1666133 n x y)). Qed.
Lemma lem1666135 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666136 (n : nat) (x : real) : (term103 n x) = (term104 n x).
Proof. exact (MK_COMB (@lem1666135) (@lem1666134 n x)). Qed.
Lemma lem1666137 (n : nat) (x : real) : (term84 n x) = (term105 n x).
Proof. exact (MK_COMB (@lem1666132 n x) (@lem1666136 n x)). Qed.
Lemma lem1666138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1666139 (n : nat) (x : real) : (term146 n x) = (term147 n x).
Proof. exact (MK_COMB (@lem1666138) (@lem1666137 n x)). Qed.
Lemma lem1666140 (n : nat) (x : real) (y : real) : (term87 n x y) = (term88 n x y).
Proof. exact (eq_refl (term87 n x y)). Qed.
Lemma lem1666141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1666142 (n : nat) (x : real) (y : real) : (term89 n x y) = (term90 n x y).
Proof. exact (MK_COMB (@lem1666141) (@lem1666140 n x y)). Qed.
Lemma lem1666143 (n : nat) (x : real) (y : real) : (term91 n x y) = (term92 n x y).
Proof. exact (eq_refl (term91 n x y)). Qed.
Lemma lem1666144 (n : nat) (x : real) (y : real) : (term93 n x y) = (term52 n x y).
Proof. exact (MK_COMB (@lem1666142 n x y) (@lem1666143 n x y)). Qed.
Lemma lem1666145 (n : nat) (x : real) : (term94 n x) = (term69 n x).
Proof. exact (fun_ext (fun y : real => @lem1666144 n x y)). Qed.
Lemma lem1666146 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666147 (n : nat) (x : real) : (term83 n x) = (term77 n x).
Proof. exact (MK_COMB (@lem1666146) (@lem1666145 n x)). Qed.
Lemma lem1666148 (n : nat) (x : real) : ((term84 n x) = (term83 n x)) = ((term105 n x) = (term77 n x)).
Proof. exact (MK_COMB (@lem1666139 n x) (@lem1666147 n x)). Qed.
Lemma lem1666149 (n : nat) (x : real) : (term105 n x) = (term77 n x).
Proof. exact (EQ_MP (@lem1666148 n x) (@lem1666126 n x)). Qed.
Lemma lem1666150 (n : nat) : (term111 n) = (term148 n).
Proof. exact (fun_ext (fun x : real => @lem1666149 n x)). Qed.
Lemma lem1666151 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666152 (n : nat) : (term119 n) = (term149 n).
Proof. exact (MK_COMB (@lem1666151) (@lem1666150 n)). Qed.
Lemma lem1666153 (n : nat) : (term140 n) = (term149 n).
Proof. exact (TRANS (@lem1666122 n) (@lem1666152 n)). Qed.
Lemma lem1666154 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1666155 (n : nat) : (term141 n) = (term150 n).
Proof. exact (MK_COMB (@lem1666154 n) (@lem1666153 n)). Qed.
Lemma lem1666157 {A : Type'} (P : Prop) (Q : A -> Prop) : (term63 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1666158 (P : Prop) (Q : real -> Prop) : (term65 P Q) = (term64 P Q).
Proof. exact (@lem1666157 real P Q). Qed.
Lemma lem1666159 (n : nat) : (term151 n) = (term152 n).
Proof. exact (@lem1666158 (term68 n) (term148 n)). Qed.
Lemma lem1666160 (n : nat) (x : real) : (term153 n x) = (term77 n x).
Proof. exact (eq_refl (term153 n x)). Qed.
Lemma lem1666161 (n : nat) : (term154 n) = (term148 n).
Proof. exact (fun_ext (fun x : real => @lem1666160 n x)). Qed.
Lemma lem1666162 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666163 (n : nat) : (term155 n) = (term149 n).
Proof. exact (MK_COMB (@lem1666162) (@lem1666161 n)). Qed.
Lemma lem1666164 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1666165 (n : nat) : (term151 n) = (term150 n).
Proof. exact (MK_COMB (@lem1666164 n) (@lem1666163 n)). Qed.
Lemma lem1666166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1666167 (n : nat) : (term156 n) = (term157 n).
Proof. exact (MK_COMB (@lem1666166) (@lem1666165 n)). Qed.
Lemma lem1666168 (n : nat) (x : real) : (term153 n x) = (term77 n x).
Proof. exact (eq_refl (term153 n x)). Qed.
Lemma lem1666169 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1666170 (n : nat) (x : real) : (term158 n x) = (term78 n x).
Proof. exact (MK_COMB (@lem1666169 n) (@lem1666168 n x)). Qed.
Lemma lem1666171 (n : nat) : (term159 n) = (term160 n).
Proof. exact (fun_ext (fun x : real => @lem1666170 n x)). Qed.
Lemma lem1666172 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666173 (n : nat) : (term152 n) = (term161 n).
Proof. exact (MK_COMB (@lem1666172) (@lem1666171 n)). Qed.
Lemma lem1666174 (n : nat) : ((term151 n) = (term152 n)) = ((term150 n) = (term161 n)).
Proof. exact (MK_COMB (@lem1666167 n) (@lem1666173 n)). Qed.
Lemma lem1666175 (n : nat) : (term150 n) = (term161 n).
Proof. exact (EQ_MP (@lem1666174 n) (@lem1666159 n)). Qed.
Lemma lem1666177 {A : Type'} (P : Prop) (Q : A -> Prop) : (term63 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1666178 (P : Prop) (Q : real -> Prop) : (term65 P Q) = (term64 P Q).
Proof. exact (@lem1666177 real P Q). Qed.
Lemma lem1666179 (n : nat) (x : real) : (term67 n x) = (term66 n x).
Proof. exact (@lem1666178 (term68 n) (term69 n x)). Qed.
Lemma lem1666180 (n : nat) (x : real) (y : real) : (term70 n x y) = (term52 n x y).
Proof. exact (eq_refl (term70 n x y)). Qed.
Lemma lem1666181 (n : nat) (x : real) : (term75 n x) = (term69 n x).
Proof. exact (fun_ext (fun y : real => @lem1666180 n x y)). Qed.
Lemma lem1666182 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666183 (n : nat) (x : real) : (term76 n x) = (term77 n x).
Proof. exact (MK_COMB (@lem1666182) (@lem1666181 n x)). Qed.
Lemma lem1666184 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1666185 (n : nat) (x : real) : (term67 n x) = (term78 n x).
Proof. exact (MK_COMB (@lem1666184 n) (@lem1666183 n x)). Qed.
Lemma lem1666186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1666187 (n : nat) (x : real) : (term162 n x) = (term163 n x).
Proof. exact (MK_COMB (@lem1666186) (@lem1666185 n x)). Qed.
Lemma lem1666188 (n : nat) (x : real) (y : real) : (term70 n x y) = (term52 n x y).
Proof. exact (eq_refl (term70 n x y)). Qed.
Lemma lem1666189 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem1666190 (n : nat) (x : real) (y : real) : (term71 n x y) = (term55 n x y).
Proof. exact (MK_COMB (@lem1666189 n) (@lem1666188 n x y)). Qed.
Lemma lem1666191 (n : nat) (x : real) : (term72 n x) = (term56 n x).
Proof. exact (fun_ext (fun y : real => @lem1666190 n x y)). Qed.
Lemma lem1666192 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666193 (n : nat) (x : real) : (term66 n x) = (term57 n x).
Proof. exact (MK_COMB (@lem1666192) (@lem1666191 n x)). Qed.
Lemma lem1666194 (n : nat) (x : real) : ((term67 n x) = (term66 n x)) = ((term78 n x) = (term57 n x)).
Proof. exact (MK_COMB (@lem1666187 n x) (@lem1666193 n x)). Qed.
Lemma lem1666195 (n : nat) (x : real) : (term78 n x) = (term57 n x).
Proof. exact (EQ_MP (@lem1666194 n x) (@lem1666179 n x)). Qed.
Lemma lem1666196 (n : nat) : (term160 n) = (term58 n).
Proof. exact (fun_ext (fun x : real => @lem1666195 n x)). Qed.
Lemma lem1666197 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666198 (n : nat) : (term161 n) = (term59 n).
Proof. exact (MK_COMB (@lem1666197) (@lem1666196 n)). Qed.
Lemma lem1666199 (n : nat) : (term150 n) = (term59 n).
Proof. exact (TRANS (@lem1666175 n) (@lem1666198 n)). Qed.
Lemma lem1666200 (n : nat) : (term141 n) = (term59 n).
Proof. exact (TRANS (@lem1666155 n) (@lem1666199 n)). Qed.
Lemma lem1666201 : term142 = term60.
Proof. exact (fun_ext (fun n : nat => @lem1666200 n)). Qed.
Lemma lem1666202 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1666203 : term143 = term61.
Proof. exact (MK_COMB (@lem1666202) (@lem1666201)). Qed.
Lemma lem1666232 (n : nat) (x : real) (y : real) : (term55 n x y) = (term164 n x y).
Proof. exact (@lem19490 (term88 n x y) (term68 n) (term92 n x y)). Qed.
Lemma lem1666233 (n : nat) (x : real) : (term56 n x) = (term165 n x).
Proof. exact (fun_ext (fun y : real => @lem1666232 n x y)). Qed.
Lemma lem1666234 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666235 (n : nat) (x : real) : (term57 n x) = (term166 n x).
Proof. exact (MK_COMB (@lem1666234) (@lem1666233 n x)). Qed.
Lemma lem1666236 (n : nat) : (term58 n) = (term167 n).
Proof. exact (fun_ext (fun x : real => @lem1666235 n x)). Qed.
Lemma lem1666237 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1666238 (n : nat) : (term59 n) = (term168 n).
Proof. exact (MK_COMB (@lem1666237) (@lem1666236 n)). Qed.
Lemma lem1666239 : term60 = term169.
Proof. exact (fun_ext (fun n : nat => @lem1666238 n)). Qed.
Lemma lem1666240 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1666241 : term61 = term170.
Proof. exact (MK_COMB (@lem1666240) (@lem1666239)). Qed.
Lemma lem1666242 : term143 = term170.
Proof. exact (TRANS (@lem1666203) (@lem1666241)). Qed.
Lemma lem1666243 (h1 : term10) : term170.
Proof. exact (EQ_MP (@lem1666242) (@lem1666061 h1)). Qed.
Lemma lem1666256 (_25765 : nat) (h1 : term10) : term171 _25765.
Proof. exact (@lem1666243 h1 _25765). Qed.
Lemma lem1666257 (_25765 : nat) : (term171 _25765) = (term168 _25765).
Proof. exact (eq_refl (term171 _25765)). Qed.
Lemma lem1666258 (_25765 : nat) (h1 : term10) : term168 _25765.
Proof. exact (EQ_MP (@lem1666257 _25765) (@lem1666256 _25765 h1)). Qed.
Lemma lem1666259 (_25765 : nat) (_25766 : real) (h1 : term10) : term172 _25765 _25766.
Proof. exact (@lem1666258 _25765 h1 _25766). Qed.
Lemma lem1666260 (_25765 : nat) (_25766 : real) : (term172 _25765 _25766) = (term166 _25765 _25766).
Proof. exact (eq_refl (term172 _25765 _25766)). Qed.
Lemma lem1666261 (_25765 : nat) (_25766 : real) (h1 : term10) : term166 _25765 _25766.
Proof. exact (EQ_MP (@lem1666260 _25765 _25766) (@lem1666259 _25765 _25766 h1)). Qed.
Lemma lem1666262 (_25765 : nat) (_25766 : real) (_25767 : real) (h1 : term10) : term173 _25765 _25766 _25767.
Proof. exact (@lem1666261 _25765 _25766 h1 _25767). Qed.
Lemma lem1666263 (_25765 : nat) (_25766 : real) (_25767 : real) : (term173 _25765 _25766 _25767) = (term164 _25765 _25766 _25767).
Proof. exact (eq_refl (term173 _25765 _25766 _25767)). Qed.
Lemma lem1666264 (_25765 : nat) (_25766 : real) (_25767 : real) (h1 : term10) : term164 _25765 _25766 _25767.
Proof. exact (EQ_MP (@lem1666263 _25765 _25766 _25767) (@lem1666262 _25765 _25766 _25767 h1)). Qed.
Lemma lem1666268 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : term174 x y.
Proof. exact (proj2 (@lem1666091 n x y h1)). Qed.
Lemma lem1666292 (_25765 : nat) (_25766 : real) (_25767 : real) (h1 : term10) : term175 _25765 _25766 _25767.
Proof. exact (proj2 (@lem1666264 _25765 _25766 _25767 h1)). Qed.
Lemma lem1666325 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (proj1 (@lem1666093 n x y h1)). Qed.
Lemma lem1666326 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : term176 n.
Proof. exact (fun h0 : term68 n => @lem1666325 n x y h1). Qed.
Lemma lem1666328 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1666329 (n : nat) : (term176 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (@lem1666328 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem1666330 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (EQ_MP (@lem1666329 n) (@lem1666326 n x y h1)). Qed.
Lemma lem1666332 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : (real_pow x n) = (real_pow y n).
Proof. exact (proj2 (@lem1666093 n x y h1)). Qed.
Lemma lem1666333 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : term178 x y n.
Proof. exact (fun h0 : term179 x y n => @lem1666332 n x y h1). Qed.
Lemma lem1666335 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1666336 (x : real) (y : real) (n : nat) : (term178 x y n) = ((real_pow x n) = (real_pow y n)).
Proof. exact (@lem1666335 ((real_pow x n) = (real_pow y n))). Qed.
Lemma lem1666337 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : (real_pow x n) = (real_pow y n).
Proof. exact (EQ_MP (@lem1666336 x y n) (@lem1666333 n x y h1)). Qed.
Lemma lem1666343 (q : Prop) (p : Prop) (r : Prop) : (term180 p q r) = (term180 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1666344 (_25765 : nat) (_25766 : real) (_25767 : real) : (term175 _25765 _25766 _25767) = (term181 _25765 _25766 _25767).
Proof. exact (@lem1666343 (term179 _25766 _25767 _25765) (term68 _25765) (_25766 = _25767)). Qed.
Lemma lem1666360 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1666361 (_25766 : real) (_25767 : real) (_25765 : nat) : (term182 _25765 _25766 _25767) = (term183 _25766 _25767 _25765).
Proof. exact (@lem1666360 (_25766 = _25767) (term68 _25765)). Qed.
Lemma lem1666369 (_25766 : real) (_25767 : real) (_25765 : nat) : (term184 _25766 _25767 _25765) = (term184 _25766 _25767 _25765).
Proof. exact (eq_refl (term184 _25766 _25767 _25765)). Qed.
Lemma lem1666370 (_25766 : real) (_25767 : real) (_25765 : nat) : (term181 _25765 _25766 _25767) = (term185 _25766 _25767 _25765).
Proof. exact (MK_COMB (@lem1666369 _25766 _25767 _25765) (@lem1666361 _25766 _25767 _25765)). Qed.
Lemma lem1666374 (q : Prop) (p : Prop) (r : Prop) : (term180 p q r) = (term180 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1666375 (_25766 : real) (_25767 : real) (_25765 : nat) : (term185 _25766 _25767 _25765) = (term186 _25766 _25767 _25765).
Proof. exact (@lem1666374 (_25766 = _25767) (term179 _25766 _25767 _25765) (term68 _25765)). Qed.
Lemma lem1666395 (_25766 : real) (_25767 : real) (_25765 : nat) : (term181 _25765 _25766 _25767) = (term186 _25766 _25767 _25765).
Proof. exact (TRANS (@lem1666370 _25766 _25767 _25765) (@lem1666375 _25766 _25767 _25765)). Qed.
Lemma lem1666396 (_25766 : real) (_25767 : real) (_25765 : nat) : (term175 _25765 _25766 _25767) = (term186 _25766 _25767 _25765).
Proof. exact (TRANS (@lem1666344 _25765 _25766 _25767) (@lem1666395 _25766 _25767 _25765)). Qed.
Lemma lem1666397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1666398 (_25766 : real) (_25767 : real) (_25765 : nat) : (term187 _25765 _25766 _25767) = (term188 _25766 _25767 _25765).
Proof. exact (MK_COMB (@lem1666397) (@lem1666396 _25766 _25767 _25765)). Qed.
Lemma lem1666414 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1666415 (_25766 : real) (_25767 : real) (_25765 : nat) : (term189 _25766 _25767 _25765) = (term190 _25766 _25767 _25765).
Proof. exact (@lem1666414 (term179 _25766 _25767 _25765) (term68 _25765)). Qed.
Lemma lem1666423 (_25766 : real) (_25767 : real) : (term191 _25766 _25767) = (term191 _25766 _25767).
Proof. exact (eq_refl (term191 _25766 _25767)). Qed.
Lemma lem1666424 (_25766 : real) (_25767 : real) (_25765 : nat) : (term192 _25766 _25767 _25765) = (term186 _25766 _25767 _25765).
Proof. exact (MK_COMB (@lem1666423 _25766 _25767) (@lem1666415 _25766 _25767 _25765)). Qed.
Lemma lem1666435 (_25766 : real) (_25767 : real) (_25765 : nat) : ((term175 _25765 _25766 _25767) = (term192 _25766 _25767 _25765)) = ((term186 _25766 _25767 _25765) = (term186 _25766 _25767 _25765)).
Proof. exact (MK_COMB (@lem1666398 _25766 _25767 _25765) (@lem1666424 _25766 _25767 _25765)). Qed.
Lemma lem1666437 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1666438 (x : Prop) : (x = x) = True.
Proof. exact (@lem1666437 Prop x). Qed.
Lemma lem1666439 (_25766 : real) (_25767 : real) (_25765 : nat) : ((term186 _25766 _25767 _25765) = (term186 _25766 _25767 _25765)) = True.
Proof. exact (@lem1666438 (term186 _25766 _25767 _25765)). Qed.
Lemma lem1666440 (_25766 : real) (_25767 : real) (_25765 : nat) : ((term175 _25765 _25766 _25767) = (term192 _25766 _25767 _25765)) = True.
Proof. exact (TRANS (@lem1666435 _25766 _25767 _25765) (@lem1666439 _25766 _25767 _25765)). Qed.
Lemma lem1666441 (_25766 : real) (_25767 : real) (_25765 : nat) : True = ((term175 _25765 _25766 _25767) = (term192 _25766 _25767 _25765)).
Proof. exact (SYM (@lem1666440 _25766 _25767 _25765)). Qed.
Lemma lem1666442 (_25766 : real) (_25767 : real) (_25765 : nat) : (term175 _25765 _25766 _25767) = (term192 _25766 _25767 _25765).
Proof. exact (EQ_MP (@lem1666441 _25766 _25767 _25765) (@lem0)). Qed.
Lemma lem1666443 (_25766 : real) (_25767 : real) (_25765 : nat) (h1 : term10) : term192 _25766 _25767 _25765.
Proof. exact (EQ_MP (@lem1666442 _25766 _25767 _25765) (@lem1666292 _25765 _25766 _25767 h1)). Qed.
Lemma lem1666445 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1666446 (_25765 : nat) (_25766 : real) (_25767 : real) : (term192 _25766 _25767 _25765) = (term194 _25765 _25766 _25767).
Proof. exact (@lem1666445 (term189 _25766 _25767 _25765) (_25766 = _25767)). Qed.
Lemma lem1666448 (a : Prop) (b : Prop) : (term195 a b) = (term196 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1666449 (_25766 : real) (_25767 : real) (_25765 : nat) : (term197 _25766 _25767 _25765) = (term198 _25766 _25767 _25765).
Proof. exact (@lem1666448 (term68 _25765) (term179 _25766 _25767 _25765)). Qed.
Lemma lem1666451 (a : Prop) : (term199 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1666452 (_25765 : nat) : (term200 _25765) = (Coq.Arith.PeanoNat.Nat.Odd _25765).
Proof. exact (@lem1666451 (Coq.Arith.PeanoNat.Nat.Odd _25765)). Qed.
Lemma lem1666453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1666454 (_25765 : nat) : (term201 _25765) = (term202 _25765).
Proof. exact (MK_COMB (@lem1666453) (@lem1666452 _25765)). Qed.
Lemma lem1666456 (a : Prop) : (term199 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1666457 (_25766 : real) (_25767 : real) (_25765 : nat) : (term203 _25766 _25767 _25765) = ((real_pow _25766 _25765) = (real_pow _25767 _25765)).
Proof. exact (@lem1666456 ((real_pow _25766 _25765) = (real_pow _25767 _25765))). Qed.
Lemma lem1666458 (_25766 : real) (_25767 : real) (_25765 : nat) : (term198 _25766 _25767 _25765) = (term27 _25766 _25767 _25765).
Proof. exact (MK_COMB (@lem1666454 _25765) (@lem1666457 _25766 _25767 _25765)). Qed.
Lemma lem1666459 (_25766 : real) (_25767 : real) (_25765 : nat) : (term197 _25766 _25767 _25765) = (term27 _25766 _25767 _25765).
Proof. exact (TRANS (@lem1666449 _25766 _25767 _25765) (@lem1666458 _25766 _25767 _25765)). Qed.
Lemma lem1666460 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1666461 (_25766 : real) (_25767 : real) (_25765 : nat) : (term204 _25766 _25767 _25765) = (term205 _25766 _25767 _25765).
Proof. exact (MK_COMB (@lem1666460) (@lem1666459 _25766 _25767 _25765)). Qed.
Lemma lem1666462 (_25766 : real) (_25767 : real) : (_25766 = _25767) = (_25766 = _25767).
Proof. exact (eq_refl (_25766 = _25767)). Qed.
Lemma lem1666463 (_25765 : nat) (_25766 : real) (_25767 : real) : (term194 _25765 _25766 _25767) = (term19 _25765 _25766 _25767).
Proof. exact (MK_COMB (@lem1666461 _25766 _25767 _25765) (@lem1666462 _25766 _25767)). Qed.
Lemma lem1666464 (_25765 : nat) (_25766 : real) (_25767 : real) : (term192 _25766 _25767 _25765) = (term19 _25765 _25766 _25767).
Proof. exact (TRANS (@lem1666446 _25765 _25766 _25767) (@lem1666463 _25765 _25766 _25767)). Qed.
Lemma lem1666466 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : term27 x y n.
Proof. exact (conj (@lem1666330 n x y h1) (@lem1666337 n x y h1)). Qed.
Lemma lem1666468 (_25765 : nat) (_25766 : real) (_25767 : real) (h1 : term10) : term19 _25765 _25766 _25767.
Proof. exact (EQ_MP (@lem1666464 _25765 _25766 _25767) (@lem1666443 _25766 _25767 _25765 h1)). Qed.
Lemma lem1666469 (n : nat) (x : real) (y : real) (h1 : term10) : term19 n x y.
Proof. exact (@lem1666468 n x y h1). Qed.
Lemma lem1666472 (n : nat) (x : real) (y : real) (h1 : term10) (h2 : term26 n x y) : x = y.
Proof. exact (@lem1666469 n x y h1 (@lem1666466 n x y h2)). Qed.
Lemma lem1666473 (n : nat) (x : real) (y : real) (h1 : term10) (h2 : term26 n x y) : term206 x y.
Proof. exact (fun h0 : term174 x y => @lem1666472 n x y h1 h2). Qed.
Lemma lem1666475 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1666476 (x : real) (y : real) : (term206 x y) = (x = y).
Proof. exact (@lem1666475 (x = y)). Qed.
Lemma lem1666477 (n : nat) (x : real) (y : real) (h1 : term10) (h2 : term26 n x y) : x = y.
Proof. exact (EQ_MP (@lem1666476 x y) (@lem1666473 n x y h1 h2)). Qed.
Lemma lem1666480 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1666482 (x : real) (y : real) : (term174 x y) = (term207 x y).
Proof. exact (@lem1666480 (x = y)). Qed.
Lemma lem1666485 (n : nat) (x : real) (y : real) (h1 : term26 n x y) : term207 x y.
Proof. exact (EQ_MP (@lem1666482 x y) (@lem1666268 n x y h1)). Qed.
Lemma lem1666488 (n : nat) (x : real) (y : real) (h1 : term10) (h2 : term26 n x y) : False.
Proof. exact (@lem1666485 n x y h2 (@lem1666477 n x y h1 h2)). Qed.
Lemma lem1666489 (n : nat) (x : real) (y : real) (h1 : term10) (h2 : term26 n x y) : term208.
Proof. exact (fun h0 : ~ False => @lem1666488 n x y h1 h2). Qed.
Lemma lem1666491 (p : Prop) : (term177 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1666492 : term208 = False.
Proof. exact (@lem1666491 False). Qed.
Lemma lem1666493 (n : nat) (x : real) (y : real) (h1 : term10) (h2 : term26 n x y) : False.
Proof. exact (EQ_MP (@lem1666492) (@lem1666489 n x y h1 h2)). Qed.
Lemma lem1666494 (n : nat) (x : real) (y : real) (h1 : term10) (h2 : term26 n x y) : (term26 n x y) = False.
Proof. exact (prop_ext (fun h3 : term26 n x y => @lem1666493 n x y h1 h2) (fun h3 : False => @lem1666091 n x y h2)). Qed.
Lemma lem1666495 (n : nat) (x : real) (y : real) (h1 : term10) (h2 : term26 n x y) : False.
Proof. exact (EQ_MP (@lem1666494 n x y h1 h2) (@lem1666091 n x y h2)). Qed.
Lemma lem1666496 (n : nat) (x : real) (h1 : term10) (h2 : term36 n x) : False.
Proof. exact (ex_elim (@lem1665987 n x h2) (fun y : real => fun h0 : term35 n x y => @lem1666495 n x y h1 h0)). Qed.
Lemma lem1666497 (n : nat) (h1 : term10) (h2 : term43 n) : False.
Proof. exact (ex_elim (@lem1665986 n h2) (fun x : real => fun h0 : term42 n x => @lem1666496 n x h1 h0)). Qed.
Lemma lem1666498 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem1665588 h2) (fun n : nat => fun h0 : term50 n => @lem1666497 n h1 h0)). Qed.
Lemma lem1666499 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1666498 h0 h1). Qed.
Lemma lem1666500 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1666501 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem1666500) (@lem1666499 h1)). Qed.
Lemma lem1666502 : term12.
Proof. exact (fun h0 : term3 => @lem1666501 h0). Qed.
Lemma lem1666503 : term4.
Proof. exact (EQ_MP (@lem1665484) (@lem1666502)). Qed.
Lemma lem1666505 : term4.
Proof. exact (@lem1665350 (@lem1666503)). Qed.
Lemma lem1666506 (h1 : term3) : term8.
Proof. exact (@lem1666505 (@lem1665335 h1)). Qed.
Lemma lem1666507 (h1 : term3) : False.
Proof. exact (@lem1666506 h1 (@lem1665320)). Qed.
Lemma lem1666508 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1666507 h1) (fun h2 : False => @lem1665335 h1)). Qed.
Lemma lem1666509 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1666508 h1) (@lem1665335 h1)). Qed.
Lemma lem1666510 : term2.
Proof. exact (fun h0 : term3 => @lem1666509 h0). Qed.
Lemma lem1666511 : term1.
Proof. exact (EQ_MP (@lem1665334) (@lem1666510)). Qed.
