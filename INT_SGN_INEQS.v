Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_INEQS_term_abbrevs.
Require Import REAL_SGN_INEQS_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299924_spec.
Require Import thm2299925_spec.
Require Import thm2299930_spec.
Require Import thm2299931_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309506 : term0.
Proof. exact (proj2 (@lem1757961)). Qed.
Lemma lem2309507 : term1.
Proof. exact (proj2 (@lem2309506)). Qed.
Lemma lem2309508 : term2.
Proof. exact (proj2 (@lem2309507)). Qed.
Lemma lem2309509 : term3.
Proof. exact (proj2 (@lem2309508)). Qed.
Lemma lem2309510 : term4.
Proof. exact (proj2 (@lem2309509)). Qed.
Lemma lem2309511 : term5.
Proof. exact (proj2 (@lem2309510)). Qed.
Lemma lem2309512 : term6.
Proof. exact (proj2 (@lem2309511)). Qed.
Lemma lem2309513 : term7.
Proof. exact (proj2 (@lem2309512)). Qed.
Lemma lem2309514 : term8.
Proof. exact (proj2 (@lem2309513)). Qed.
Lemma lem2309515 (x : int) : term9 x.
Proof. exact (@lem2309514 (real_of_int x)). Qed.
Lemma lem2309516 (x : int) : (term9 x) = (((term10 x) = term11) = ((real_of_int x) = term11)).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2309517 (x : int) : ((term10 x) = term11) = ((real_of_int x) = term11).
Proof. exact (EQ_MP (@lem2309516 x) (@lem2309515 x)). Qed.
Lemma lem2309519 (x : int) : (term10 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309520 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309521 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2309520) (@lem2309519 x)). Qed.
Lemma lem2309523 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309524 : term11 = term16.
Proof. exact (@lem2309523 (NUMERAL 0)). Qed.
Lemma lem2309525 (x : int) : ((term10 x) = term11) = ((term12 x) = term16).
Proof. exact (MK_COMB (@lem2309521 x) (@lem2309524)). Qed.
Lemma lem2309527 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309528 (x : int) : ((term12 x) = term16) = ((int_sgn x) = term17).
Proof. exact (@lem2309527 (int_sgn x) term17). Qed.
Lemma lem2309529 (x : int) : ((term10 x) = term11) = ((int_sgn x) = term17).
Proof. exact (TRANS (@lem2309525 x) (@lem2309528 x)). Qed.
Lemma lem2309530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309531 (x : int) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem2309530) (@lem2309529 x)). Qed.
Lemma lem2309533 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309534 : term11 = term16.
Proof. exact (@lem2309533 (NUMERAL 0)). Qed.
Lemma lem2309535 (x : int) : (term20 x) = (term20 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem2309536 (x : int) : ((real_of_int x) = term11) = ((real_of_int x) = term16).
Proof. exact (MK_COMB (@lem2309535 x) (@lem2309534)). Qed.
Lemma lem2309538 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309539 (x : int) : ((real_of_int x) = term16) = (x = term17).
Proof. exact (@lem2309538 x term17). Qed.
Lemma lem2309540 (x : int) : ((real_of_int x) = term11) = (x = term17).
Proof. exact (TRANS (@lem2309536 x) (@lem2309539 x)). Qed.
Lemma lem2309541 (x : int) : (((term10 x) = term11) = ((real_of_int x) = term11)) = (((int_sgn x) = term17) = (x = term17)).
Proof. exact (MK_COMB (@lem2309531 x) (@lem2309540 x)). Qed.
Lemma lem2309542 (x : int) : ((int_sgn x) = term17) = (x = term17).
Proof. exact (EQ_MP (@lem2309541 x) (@lem2309517 x)). Qed.
Lemma lem2309543 : term21.
Proof. exact (fun x : int => @lem2309542 x). Qed.
Lemma lem2309544 : term22.
Proof. exact (proj1 (@lem2309513)). Qed.
Lemma lem2309545 (x : int) : term23 x.
Proof. exact (@lem2309544 (real_of_int x)). Qed.
Lemma lem2309546 (x : int) : (term23 x) = ((term24 x) = (term25 x)).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2309547 (x : int) : (term24 x) = (term25 x).
Proof. exact (EQ_MP (@lem2309546 x) (@lem2309545 x)). Qed.
Lemma lem2309549 (x : int) : (term10 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309550 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2309551 (x : int) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem2309550) (@lem2309549 x)). Qed.
Lemma lem2309553 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309554 : term11 = term16.
Proof. exact (@lem2309553 (NUMERAL 0)). Qed.
Lemma lem2309555 (x : int) : (term24 x) = (term28 x).
Proof. exact (MK_COMB (@lem2309551 x) (@lem2309554)). Qed.
Lemma lem2309557 (x : int) (y : int) : (term29 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2309558 (x : int) : (term28 x) = (term30 x).
Proof. exact (@lem2309557 (int_sgn x) term17). Qed.
Lemma lem2309559 (x : int) : (term24 x) = (term30 x).
Proof. exact (TRANS (@lem2309555 x) (@lem2309558 x)). Qed.
Lemma lem2309560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309561 (x : int) : (term31 x) = (term32 x).
Proof. exact (MK_COMB (@lem2309560) (@lem2309559 x)). Qed.
Lemma lem2309563 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309564 : term11 = term16.
Proof. exact (@lem2309563 (NUMERAL 0)). Qed.
Lemma lem2309565 (x : int) : (term33 x) = (term33 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem2309566 (x : int) : (term25 x) = (term34 x).
Proof. exact (MK_COMB (@lem2309565 x) (@lem2309564)). Qed.
Lemma lem2309568 (x : int) (y : int) : (term29 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2309569 (x : int) : (term34 x) = (term35 x).
Proof. exact (@lem2309568 x term17). Qed.
Lemma lem2309570 (x : int) : (term25 x) = (term35 x).
Proof. exact (TRANS (@lem2309566 x) (@lem2309569 x)). Qed.
Lemma lem2309571 (x : int) : ((term24 x) = (term25 x)) = ((term30 x) = (term35 x)).
Proof. exact (MK_COMB (@lem2309561 x) (@lem2309570 x)). Qed.
Lemma lem2309572 (x : int) : (term30 x) = (term35 x).
Proof. exact (EQ_MP (@lem2309571 x) (@lem2309547 x)). Qed.
Lemma lem2309573 : term36.
Proof. exact (fun x : int => @lem2309572 x). Qed.
Lemma lem2309574 : term37.
Proof. exact (conj (@lem2309573) (@lem2309543)). Qed.
Lemma lem2309575 : term38.
Proof. exact (proj1 (@lem2309512)). Qed.
Lemma lem2309576 (x : int) : term39 x.
Proof. exact (@lem2309575 (real_of_int x)). Qed.
Lemma lem2309577 (x : int) : (term39 x) = ((term40 x) = (term41 x)).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem2309578 (x : int) : (term40 x) = (term41 x).
Proof. exact (EQ_MP (@lem2309577 x) (@lem2309576 x)). Qed.
Lemma lem2309580 (x : int) : (term10 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309581 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2309582 (x : int) : (term42 x) = (term43 x).
Proof. exact (MK_COMB (@lem2309581) (@lem2309580 x)). Qed.
Lemma lem2309584 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309585 : term11 = term16.
Proof. exact (@lem2309584 (NUMERAL 0)). Qed.
Lemma lem2309586 (x : int) : (term40 x) = (term44 x).
Proof. exact (MK_COMB (@lem2309582 x) (@lem2309585)). Qed.
Lemma lem2309588 (x : int) (y : int) : (term45 x y) = (int_ge x y).
Proof. exact (EQ_MP (@lem2299931 x y) (@lem2299930 x y)). Qed.
Lemma lem2309589 (x : int) : (term44 x) = (term46 x).
Proof. exact (@lem2309588 (int_sgn x) term17). Qed.
Lemma lem2309590 (x : int) : (term40 x) = (term46 x).
Proof. exact (TRANS (@lem2309586 x) (@lem2309589 x)). Qed.
Lemma lem2309591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309592 (x : int) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem2309591) (@lem2309590 x)). Qed.
Lemma lem2309594 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309595 : term11 = term16.
Proof. exact (@lem2309594 (NUMERAL 0)). Qed.
Lemma lem2309596 (x : int) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem2309597 (x : int) : (term41 x) = (term50 x).
Proof. exact (MK_COMB (@lem2309596 x) (@lem2309595)). Qed.
Lemma lem2309599 (x : int) (y : int) : (term45 x y) = (int_ge x y).
Proof. exact (EQ_MP (@lem2299931 x y) (@lem2299930 x y)). Qed.
Lemma lem2309600 (x : int) : (term50 x) = (term51 x).
Proof. exact (@lem2309599 x term17). Qed.
Lemma lem2309601 (x : int) : (term41 x) = (term51 x).
Proof. exact (TRANS (@lem2309597 x) (@lem2309600 x)). Qed.
Lemma lem2309602 (x : int) : ((term40 x) = (term41 x)) = ((term46 x) = (term51 x)).
Proof. exact (MK_COMB (@lem2309592 x) (@lem2309601 x)). Qed.
Lemma lem2309603 (x : int) : (term46 x) = (term51 x).
Proof. exact (EQ_MP (@lem2309602 x) (@lem2309578 x)). Qed.
Lemma lem2309604 : term52.
Proof. exact (fun x : int => @lem2309603 x). Qed.
Lemma lem2309605 : term53.
Proof. exact (conj (@lem2309604) (@lem2309574)). Qed.
Lemma lem2309606 : term54.
Proof. exact (proj1 (@lem2309511)). Qed.
Lemma lem2309607 (x : int) : term55 x.
Proof. exact (@lem2309606 (real_of_int x)). Qed.
Lemma lem2309608 (x : int) : (term55 x) = ((term56 x) = (term57 x)).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem2309609 (x : int) : (term56 x) = (term57 x).
Proof. exact (EQ_MP (@lem2309608 x) (@lem2309607 x)). Qed.
Lemma lem2309611 (x : int) : (term10 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309612 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2309613 (x : int) : (term58 x) = (term59 x).
Proof. exact (MK_COMB (@lem2309612) (@lem2309611 x)). Qed.
Lemma lem2309615 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309616 : term11 = term16.
Proof. exact (@lem2309615 (NUMERAL 0)). Qed.
Lemma lem2309617 (x : int) : (term56 x) = (term60 x).
Proof. exact (MK_COMB (@lem2309613 x) (@lem2309616)). Qed.
Lemma lem2309619 (x : int) (y : int) : (term61 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309620 (x : int) : (term60 x) = (term62 x).
Proof. exact (@lem2309619 (int_sgn x) term17). Qed.
Lemma lem2309621 (x : int) : (term56 x) = (term62 x).
Proof. exact (TRANS (@lem2309617 x) (@lem2309620 x)). Qed.
Lemma lem2309622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309623 (x : int) : (term63 x) = (term64 x).
Proof. exact (MK_COMB (@lem2309622) (@lem2309621 x)). Qed.
Lemma lem2309625 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309626 : term11 = term16.
Proof. exact (@lem2309625 (NUMERAL 0)). Qed.
Lemma lem2309627 (x : int) : (term65 x) = (term65 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem2309628 (x : int) : (term57 x) = (term66 x).
Proof. exact (MK_COMB (@lem2309627 x) (@lem2309626)). Qed.
Lemma lem2309630 (x : int) (y : int) : (term61 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309631 (x : int) : (term66 x) = (term67 x).
Proof. exact (@lem2309630 x term17). Qed.
Lemma lem2309632 (x : int) : (term57 x) = (term67 x).
Proof. exact (TRANS (@lem2309628 x) (@lem2309631 x)). Qed.
Lemma lem2309633 (x : int) : ((term56 x) = (term57 x)) = ((term62 x) = (term67 x)).
Proof. exact (MK_COMB (@lem2309623 x) (@lem2309632 x)). Qed.
Lemma lem2309634 (x : int) : (term62 x) = (term67 x).
Proof. exact (EQ_MP (@lem2309633 x) (@lem2309609 x)). Qed.
Lemma lem2309635 : term68.
Proof. exact (fun x : int => @lem2309634 x). Qed.
Lemma lem2309636 : term69.
Proof. exact (conj (@lem2309635) (@lem2309605)). Qed.
Lemma lem2309637 : term70.
Proof. exact (proj1 (@lem2309510)). Qed.
Lemma lem2309638 (x : int) : term71 x.
Proof. exact (@lem2309637 (real_of_int x)). Qed.
Lemma lem2309639 (x : int) : (term71 x) = ((term72 x) = (term73 x)).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem2309640 (x : int) : (term72 x) = (term73 x).
Proof. exact (EQ_MP (@lem2309639 x) (@lem2309638 x)). Qed.
Lemma lem2309642 (x : int) : (term10 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309643 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2309644 (x : int) : (term74 x) = (term75 x).
Proof. exact (MK_COMB (@lem2309643) (@lem2309642 x)). Qed.
Lemma lem2309646 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309647 : term11 = term16.
Proof. exact (@lem2309646 (NUMERAL 0)). Qed.
Lemma lem2309648 (x : int) : (term72 x) = (term76 x).
Proof. exact (MK_COMB (@lem2309644 x) (@lem2309647)). Qed.
Lemma lem2309650 (x : int) (y : int) : (term77 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2309651 (x : int) : (term76 x) = (term78 x).
Proof. exact (@lem2309650 (int_sgn x) term17). Qed.
Lemma lem2309652 (x : int) : (term72 x) = (term78 x).
Proof. exact (TRANS (@lem2309648 x) (@lem2309651 x)). Qed.
Lemma lem2309653 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309654 (x : int) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem2309653) (@lem2309652 x)). Qed.
Lemma lem2309656 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309657 : term11 = term16.
Proof. exact (@lem2309656 (NUMERAL 0)). Qed.
Lemma lem2309658 (x : int) : (term81 x) = (term81 x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem2309659 (x : int) : (term73 x) = (term82 x).
Proof. exact (MK_COMB (@lem2309658 x) (@lem2309657)). Qed.
Lemma lem2309661 (x : int) (y : int) : (term77 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2309662 (x : int) : (term82 x) = (term83 x).
Proof. exact (@lem2309661 x term17). Qed.
Lemma lem2309663 (x : int) : (term73 x) = (term83 x).
Proof. exact (TRANS (@lem2309659 x) (@lem2309662 x)). Qed.
Lemma lem2309664 (x : int) : ((term72 x) = (term73 x)) = ((term78 x) = (term83 x)).
Proof. exact (MK_COMB (@lem2309654 x) (@lem2309663 x)). Qed.
Lemma lem2309665 (x : int) : (term78 x) = (term83 x).
Proof. exact (EQ_MP (@lem2309664 x) (@lem2309640 x)). Qed.
Lemma lem2309666 : term84.
Proof. exact (fun x : int => @lem2309665 x). Qed.
Lemma lem2309667 : term85.
Proof. exact (conj (@lem2309666) (@lem2309636)). Qed.
Lemma lem2309668 : term86.
Proof. exact (proj1 (@lem2309509)). Qed.
Lemma lem2309669 (x : int) : term87 x.
Proof. exact (@lem2309668 (real_of_int x)). Qed.
Lemma lem2309670 (x : int) : (term87 x) = ((term11 = (term10 x)) = (term11 = (real_of_int x))).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem2309671 (x : int) : (term11 = (term10 x)) = (term11 = (real_of_int x)).
Proof. exact (EQ_MP (@lem2309670 x) (@lem2309669 x)). Qed.
Lemma lem2309673 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309674 : term11 = term16.
Proof. exact (@lem2309673 (NUMERAL 0)). Qed.
Lemma lem2309675 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309676 : term88 = term89.
Proof. exact (MK_COMB (@lem2309675) (@lem2309674)). Qed.
Lemma lem2309678 (x : int) : (term10 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309679 (x : int) : (term11 = (term10 x)) = (term16 = (term12 x)).
Proof. exact (MK_COMB (@lem2309676) (@lem2309678 x)). Qed.
Lemma lem2309681 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309682 (x : int) : (term16 = (term12 x)) = (term17 = (int_sgn x)).
Proof. exact (@lem2309681 term17 (int_sgn x)). Qed.
Lemma lem2309683 (x : int) : (term11 = (term10 x)) = (term17 = (int_sgn x)).
Proof. exact (TRANS (@lem2309679 x) (@lem2309682 x)). Qed.
Lemma lem2309684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309685 (x : int) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem2309684) (@lem2309683 x)). Qed.
Lemma lem2309687 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309688 : term11 = term16.
Proof. exact (@lem2309687 (NUMERAL 0)). Qed.
Lemma lem2309689 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309690 : term88 = term89.
Proof. exact (MK_COMB (@lem2309689) (@lem2309688)). Qed.
Lemma lem2309691 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2309692 (x : int) : (term11 = (real_of_int x)) = (term16 = (real_of_int x)).
Proof. exact (MK_COMB (@lem2309690) (@lem2309691 x)). Qed.
Lemma lem2309694 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309695 (x : int) : (term16 = (real_of_int x)) = (term17 = x).
Proof. exact (@lem2309694 term17 x). Qed.
Lemma lem2309696 (x : int) : (term11 = (real_of_int x)) = (term17 = x).
Proof. exact (TRANS (@lem2309692 x) (@lem2309695 x)). Qed.
Lemma lem2309697 (x : int) : ((term11 = (term10 x)) = (term11 = (real_of_int x))) = ((term17 = (int_sgn x)) = (term17 = x)).
Proof. exact (MK_COMB (@lem2309685 x) (@lem2309696 x)). Qed.
Lemma lem2309698 (x : int) : (term17 = (int_sgn x)) = (term17 = x).
Proof. exact (EQ_MP (@lem2309697 x) (@lem2309671 x)). Qed.
Lemma lem2309699 : term92.
Proof. exact (fun x : int => @lem2309698 x). Qed.
Lemma lem2309700 : term93.
Proof. exact (conj (@lem2309699) (@lem2309667)). Qed.
Lemma lem2309701 : term94.
Proof. exact (proj1 (@lem2309508)). Qed.
Lemma lem2309702 (x : int) : term95 x.
Proof. exact (@lem2309701 (real_of_int x)). Qed.
Lemma lem2309703 (x : int) : (term95 x) = ((term96 x) = (term97 x)).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem2309704 (x : int) : (term96 x) = (term97 x).
Proof. exact (EQ_MP (@lem2309703 x) (@lem2309702 x)). Qed.
Lemma lem2309706 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309707 : term11 = term16.
Proof. exact (@lem2309706 (NUMERAL 0)). Qed.
Lemma lem2309708 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2309709 : term98 = term99.
Proof. exact (MK_COMB (@lem2309708) (@lem2309707)). Qed.
Lemma lem2309711 (x : int) : (term10 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309712 (x : int) : (term96 x) = (term100 x).
Proof. exact (MK_COMB (@lem2309709) (@lem2309711 x)). Qed.
Lemma lem2309714 (x : int) (y : int) : (term29 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2309715 (x : int) : (term100 x) = (term101 x).
Proof. exact (@lem2309714 term17 (int_sgn x)). Qed.
Lemma lem2309716 (x : int) : (term96 x) = (term101 x).
Proof. exact (TRANS (@lem2309712 x) (@lem2309715 x)). Qed.
Lemma lem2309717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309718 (x : int) : (term102 x) = (term103 x).
Proof. exact (MK_COMB (@lem2309717) (@lem2309716 x)). Qed.
Lemma lem2309720 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309721 : term11 = term16.
Proof. exact (@lem2309720 (NUMERAL 0)). Qed.
Lemma lem2309722 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2309723 : term98 = term99.
Proof. exact (MK_COMB (@lem2309722) (@lem2309721)). Qed.
Lemma lem2309724 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2309725 (x : int) : (term97 x) = (term104 x).
Proof. exact (MK_COMB (@lem2309723) (@lem2309724 x)). Qed.
Lemma lem2309727 (x : int) (y : int) : (term29 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2309728 (x : int) : (term104 x) = (term105 x).
Proof. exact (@lem2309727 term17 x). Qed.
Lemma lem2309729 (x : int) : (term97 x) = (term105 x).
Proof. exact (TRANS (@lem2309725 x) (@lem2309728 x)). Qed.
Lemma lem2309730 (x : int) : ((term96 x) = (term97 x)) = ((term101 x) = (term105 x)).
Proof. exact (MK_COMB (@lem2309718 x) (@lem2309729 x)). Qed.
Lemma lem2309731 (x : int) : (term101 x) = (term105 x).
Proof. exact (EQ_MP (@lem2309730 x) (@lem2309704 x)). Qed.
Lemma lem2309732 : term106.
Proof. exact (fun x : int => @lem2309731 x). Qed.
Lemma lem2309733 : term107.
Proof. exact (conj (@lem2309732) (@lem2309700)). Qed.
Lemma lem2309734 : term108.
Proof. exact (proj1 (@lem2309507)). Qed.
Lemma lem2309735 (x : int) : term109 x.
Proof. exact (@lem2309734 (real_of_int x)). Qed.
Lemma lem2309736 (x : int) : (term109 x) = ((term110 x) = (term111 x)).
Proof. exact (eq_refl (term109 x)). Qed.
Lemma lem2309737 (x : int) : (term110 x) = (term111 x).
Proof. exact (EQ_MP (@lem2309736 x) (@lem2309735 x)). Qed.
Lemma lem2309739 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309740 : term11 = term16.
Proof. exact (@lem2309739 (NUMERAL 0)). Qed.
Lemma lem2309741 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2309742 : term112 = term113.
Proof. exact (MK_COMB (@lem2309741) (@lem2309740)). Qed.
Lemma lem2309744 (x : int) : (term10 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309745 (x : int) : (term110 x) = (term114 x).
Proof. exact (MK_COMB (@lem2309742) (@lem2309744 x)). Qed.
Lemma lem2309747 (x : int) (y : int) : (term45 x y) = (int_ge x y).
Proof. exact (EQ_MP (@lem2299931 x y) (@lem2299930 x y)). Qed.
Lemma lem2309748 (x : int) : (term114 x) = (term115 x).
Proof. exact (@lem2309747 term17 (int_sgn x)). Qed.
Lemma lem2309749 (x : int) : (term110 x) = (term115 x).
Proof. exact (TRANS (@lem2309745 x) (@lem2309748 x)). Qed.
Lemma lem2309750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309751 (x : int) : (term116 x) = (term117 x).
Proof. exact (MK_COMB (@lem2309750) (@lem2309749 x)). Qed.
Lemma lem2309753 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309754 : term11 = term16.
Proof. exact (@lem2309753 (NUMERAL 0)). Qed.
Lemma lem2309755 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2309756 : term112 = term113.
Proof. exact (MK_COMB (@lem2309755) (@lem2309754)). Qed.
Lemma lem2309757 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2309758 (x : int) : (term111 x) = (term118 x).
Proof. exact (MK_COMB (@lem2309756) (@lem2309757 x)). Qed.
Lemma lem2309760 (x : int) (y : int) : (term45 x y) = (int_ge x y).
Proof. exact (EQ_MP (@lem2299931 x y) (@lem2299930 x y)). Qed.
Lemma lem2309761 (x : int) : (term118 x) = (term119 x).
Proof. exact (@lem2309760 term17 x). Qed.
Lemma lem2309762 (x : int) : (term111 x) = (term119 x).
Proof. exact (TRANS (@lem2309758 x) (@lem2309761 x)). Qed.
Lemma lem2309763 (x : int) : ((term110 x) = (term111 x)) = ((term115 x) = (term119 x)).
Proof. exact (MK_COMB (@lem2309751 x) (@lem2309762 x)). Qed.
Lemma lem2309764 (x : int) : (term115 x) = (term119 x).
Proof. exact (EQ_MP (@lem2309763 x) (@lem2309737 x)). Qed.
Lemma lem2309765 : term120.
Proof. exact (fun x : int => @lem2309764 x). Qed.
Lemma lem2309766 : term121.
Proof. exact (conj (@lem2309765) (@lem2309733)). Qed.
Lemma lem2309767 : term122.
Proof. exact (proj1 (@lem2309506)). Qed.
Lemma lem2309768 (x : int) : term123 x.
Proof. exact (@lem2309767 (real_of_int x)). Qed.
Lemma lem2309769 (x : int) : (term123 x) = ((term124 x) = (term125 x)).
Proof. exact (eq_refl (term123 x)). Qed.
Lemma lem2309770 (x : int) : (term124 x) = (term125 x).
Proof. exact (EQ_MP (@lem2309769 x) (@lem2309768 x)). Qed.
Lemma lem2309772 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309773 : term11 = term16.
Proof. exact (@lem2309772 (NUMERAL 0)). Qed.
Lemma lem2309774 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2309775 : term126 = term127.
Proof. exact (MK_COMB (@lem2309774) (@lem2309773)). Qed.
Lemma lem2309777 (x : int) : (term10 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309778 (x : int) : (term124 x) = (term128 x).
Proof. exact (MK_COMB (@lem2309775) (@lem2309777 x)). Qed.
Lemma lem2309780 (x : int) (y : int) : (term61 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309781 (x : int) : (term128 x) = (term129 x).
Proof. exact (@lem2309780 term17 (int_sgn x)). Qed.
Lemma lem2309782 (x : int) : (term124 x) = (term129 x).
Proof. exact (TRANS (@lem2309778 x) (@lem2309781 x)). Qed.
Lemma lem2309783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309784 (x : int) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem2309783) (@lem2309782 x)). Qed.
Lemma lem2309786 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309787 : term11 = term16.
Proof. exact (@lem2309786 (NUMERAL 0)). Qed.
Lemma lem2309788 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2309789 : term126 = term127.
Proof. exact (MK_COMB (@lem2309788) (@lem2309787)). Qed.
Lemma lem2309790 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2309791 (x : int) : (term125 x) = (term132 x).
Proof. exact (MK_COMB (@lem2309789) (@lem2309790 x)). Qed.
Lemma lem2309793 (x : int) (y : int) : (term61 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309794 (x : int) : (term132 x) = (term133 x).
Proof. exact (@lem2309793 term17 x). Qed.
Lemma lem2309795 (x : int) : (term125 x) = (term133 x).
Proof. exact (TRANS (@lem2309791 x) (@lem2309794 x)). Qed.
Lemma lem2309796 (x : int) : ((term124 x) = (term125 x)) = ((term129 x) = (term133 x)).
Proof. exact (MK_COMB (@lem2309784 x) (@lem2309795 x)). Qed.
Lemma lem2309797 (x : int) : (term129 x) = (term133 x).
Proof. exact (EQ_MP (@lem2309796 x) (@lem2309770 x)). Qed.
Lemma lem2309798 : term134.
Proof. exact (fun x : int => @lem2309797 x). Qed.
Lemma lem2309799 : term135.
Proof. exact (conj (@lem2309798) (@lem2309766)). Qed.
Lemma lem2309800 : term136.
Proof. exact (proj1 (@lem1757961)). Qed.
Lemma lem2309801 (x : int) : term137 x.
Proof. exact (@lem2309800 (real_of_int x)). Qed.
Lemma lem2309802 (x : int) : (term137 x) = ((term138 x) = (term139 x)).
Proof. exact (eq_refl (term137 x)). Qed.
Lemma lem2309803 (x : int) : (term138 x) = (term139 x).
Proof. exact (EQ_MP (@lem2309802 x) (@lem2309801 x)). Qed.
Lemma lem2309805 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309806 : term11 = term16.
Proof. exact (@lem2309805 (NUMERAL 0)). Qed.
Lemma lem2309807 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2309808 : term140 = term141.
Proof. exact (MK_COMB (@lem2309807) (@lem2309806)). Qed.
Lemma lem2309810 (x : int) : (term10 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309811 (x : int) : (term138 x) = (term142 x).
Proof. exact (MK_COMB (@lem2309808) (@lem2309810 x)). Qed.
Lemma lem2309813 (x : int) (y : int) : (term77 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2309814 (x : int) : (term142 x) = (term143 x).
Proof. exact (@lem2309813 term17 (int_sgn x)). Qed.
Lemma lem2309815 (x : int) : (term138 x) = (term143 x).
Proof. exact (TRANS (@lem2309811 x) (@lem2309814 x)). Qed.
Lemma lem2309816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309817 (x : int) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem2309816) (@lem2309815 x)). Qed.
Lemma lem2309819 (n : nat) : (real_of_num n) = (term15 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309820 : term11 = term16.
Proof. exact (@lem2309819 (NUMERAL 0)). Qed.
Lemma lem2309821 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2309822 : term140 = term141.
Proof. exact (MK_COMB (@lem2309821) (@lem2309820)). Qed.
Lemma lem2309823 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2309824 (x : int) : (term139 x) = (term146 x).
Proof. exact (MK_COMB (@lem2309822) (@lem2309823 x)). Qed.
Lemma lem2309826 (x : int) (y : int) : (term77 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2309827 (x : int) : (term146 x) = (term147 x).
Proof. exact (@lem2309826 term17 x). Qed.
Lemma lem2309828 (x : int) : (term139 x) = (term147 x).
Proof. exact (TRANS (@lem2309824 x) (@lem2309827 x)). Qed.
Lemma lem2309829 (x : int) : ((term138 x) = (term139 x)) = ((term143 x) = (term147 x)).
Proof. exact (MK_COMB (@lem2309817 x) (@lem2309828 x)). Qed.
Lemma lem2309830 (x : int) : (term143 x) = (term147 x).
Proof. exact (EQ_MP (@lem2309829 x) (@lem2309803 x)). Qed.
Lemma lem2309831 : term148.
Proof. exact (fun x : int => @lem2309830 x). Qed.
Lemma lem2309832 : term149.
Proof. exact (conj (@lem2309831) (@lem2309799)). Qed.
