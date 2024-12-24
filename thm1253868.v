Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1253868_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1253400 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1253401 (p : nat) (q : nat) : (Nat.add q p) = (Nat.add p q).
Proof. exact (@lem1253400 p q). Qed.
Lemma lem1253405 (p : nat) (q : nat) : (term0 p q) = (term0 p q).
Proof. exact (eq_refl (term0 p q)). Qed.
Lemma lem1253406 (p : nat) (q : nat) : ((Nat.add p q) = (Nat.add q p)) = ((Nat.add p q) = (Nat.add p q)).
Proof. exact (MK_COMB (@lem1253405 p q) (@lem1253401 p q)). Qed.
Lemma lem1253408 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1253409 (x : nat) : (x = x) = True.
Proof. exact (@lem1253408 nat x). Qed.
Lemma lem1253410 (p : nat) (q : nat) : ((Nat.add p q) = (Nat.add p q)) = True.
Proof. exact (@lem1253409 (Nat.add p q)). Qed.
Lemma lem1253411 (q : nat) (p : nat) : ((Nat.add p q) = (Nat.add q p)) = True.
Proof. exact (TRANS (@lem1253406 p q) (@lem1253410 p q)). Qed.
Lemma lem1253412 (q : nat) (p : nat) : True = ((Nat.add p q) = (Nat.add q p)).
Proof. exact (SYM (@lem1253411 q p)). Qed.
Lemma lem1253413 (q : nat) (p : nat) : (Nat.add p q) = (Nat.add q p).
Proof. exact (EQ_MP (@lem1253412 q p) (@lem0)). Qed.
Lemma lem1253417 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1253418 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 p q d' d'' d''') = (term4 p q d' d'' d''').
Proof. exact (@lem1253417 (Nat.add p d') (Nat.add q d'') (term5 d' d'' d''')). Qed.
Lemma lem1253420 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1253421 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 p q d' d'' d''') = (term6 p q d' d'' d''').
Proof. exact (@lem1253420 p d' (term7 q d' d'' d''')). Qed.
Lemma lem1253423 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253424 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term6 p q d' d'' d''') = (term8 p q d' d'' d''').
Proof. exact (@lem1253423 d' p (term7 q d' d'' d''')). Qed.
Lemma lem1253431 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 p q d' d'' d''') = (term8 p q d' d'' d''').
Proof. exact (TRANS (@lem1253421 p q d' d'' d''') (@lem1253424 p q d' d'' d''')). Qed.
Lemma lem1253432 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 p q d' d'' d''') = (term8 p q d' d'' d''').
Proof. exact (TRANS (@lem1253418 p q d' d'' d''') (@lem1253431 p q d' d'' d''')). Qed.
Lemma lem1253440 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1253441 (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 q d' d'' d''') = (term9 q d' d'' d''').
Proof. exact (@lem1253440 q d'' (term5 d' d'' d''')). Qed.
Lemma lem1253443 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253444 (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term9 q d' d'' d''') = (term10 q d' d'' d''').
Proof. exact (@lem1253443 d'' q (term5 d' d'' d''')). Qed.
Lemma lem1253451 (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 q d' d'' d''') = (term10 q d' d'' d''').
Proof. exact (TRANS (@lem1253441 q d' d'' d''') (@lem1253444 q d' d'' d''')). Qed.
Lemma lem1253459 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1253460 (d' : nat) (d'' : nat) (d''' : nat) : (term5 d' d'' d''') = (term11 d' d'' d''').
Proof. exact (@lem1253459 d' d'' (S d''')). Qed.
Lemma lem1253470 (q : nat) : (Nat.add q) = (Nat.add q).
Proof. exact (eq_refl (Nat.add q)). Qed.
Lemma lem1253471 (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term12 q d' d'' d''') = (term13 q d' d'' d''').
Proof. exact (MK_COMB (@lem1253470 q) (@lem1253460 d' d'' d''')). Qed.
Lemma lem1253473 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253474 (d' : nat) (q : nat) (d'' : nat) (d''' : nat) : (term13 q d' d'' d''') = (term13 d' q d'' d''').
Proof. exact (@lem1253473 d' q (term14 d'' d''')). Qed.
Lemma lem1253482 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253483 (d'' : nat) (q : nat) (d''' : nat) : (term11 q d'' d''') = (term11 d'' q d''').
Proof. exact (@lem1253482 d'' q (S d''')). Qed.
Lemma lem1253493 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253494 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 d' q d'' d''') = (term13 d' d'' q d''').
Proof. exact (MK_COMB (@lem1253493 d') (@lem1253483 d'' q d''')). Qed.
Lemma lem1253501 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 q d' d'' d''') = (term13 d' d'' q d''').
Proof. exact (TRANS (@lem1253474 d' q d'' d''') (@lem1253494 d' d'' q d''')). Qed.
Lemma lem1253502 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term12 q d' d'' d''') = (term13 d' d'' q d''').
Proof. exact (TRANS (@lem1253471 q d' d'' d''') (@lem1253501 d' d'' q d''')). Qed.
Lemma lem1253503 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1253504 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term10 q d' d'' d''') = (term15 d' d'' q d''').
Proof. exact (MK_COMB (@lem1253503 d'') (@lem1253502 d' d'' q d''')). Qed.
Lemma lem1253506 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253507 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term15 d' d'' q d''') = (term16 d' d'' q d''').
Proof. exact (@lem1253506 d' d'' (term11 d'' q d''')). Qed.
Lemma lem1253529 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term10 q d' d'' d''') = (term16 d' d'' q d''').
Proof. exact (TRANS (@lem1253504 d' d'' q d''') (@lem1253507 d' d'' q d''')). Qed.
Lemma lem1253530 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term7 q d' d'' d''') = (term16 d' d'' q d''').
Proof. exact (TRANS (@lem1253451 q d' d'' d''') (@lem1253529 d' d'' q d''')). Qed.
Lemma lem1253531 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1253532 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term17 p q d' d'' d''') = (term18 p d' d'' q d''').
Proof. exact (MK_COMB (@lem1253531 p) (@lem1253530 d' d'' q d''')). Qed.
Lemma lem1253534 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253535 (d' : nat) (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term18 p d' d'' q d''') = (term18 d' p d'' q d''').
Proof. exact (@lem1253534 d' p (term19 d'' q d''')). Qed.
Lemma lem1253543 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253544 (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term16 p d'' q d''') = (term15 p d'' q d''').
Proof. exact (@lem1253543 d'' p (term11 d'' q d''')). Qed.
Lemma lem1253552 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253553 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term13 p d'' q d''') = (term13 d'' p q d''').
Proof. exact (@lem1253552 d'' p (term14 q d''')). Qed.
Lemma lem1253569 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1253570 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term15 p d'' q d''') = (term20 d'' p q d''').
Proof. exact (MK_COMB (@lem1253569 d'') (@lem1253553 d'' p q d''')). Qed.
Lemma lem1253577 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term16 p d'' q d''') = (term20 d'' p q d''').
Proof. exact (TRANS (@lem1253544 p d'' q d''') (@lem1253570 d'' p q d''')). Qed.
Lemma lem1253578 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253579 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term18 d' p d'' q d''') = (term21 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1253578 d') (@lem1253577 d'' p q d''')). Qed.
Lemma lem1253586 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term18 p d' d'' q d''') = (term21 d' d'' p q d''').
Proof. exact (TRANS (@lem1253535 d' p d'' q d''') (@lem1253579 d' d'' p q d''')). Qed.
Lemma lem1253587 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term17 p q d' d'' d''') = (term21 d' d'' p q d''').
Proof. exact (TRANS (@lem1253532 p d' d'' q d''') (@lem1253586 d' d'' p q d''')). Qed.
Lemma lem1253588 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253589 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term8 p q d' d'' d''') = (term22 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1253588 d') (@lem1253587 d' d'' p q d''')). Qed.
Lemma lem1253596 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term3 p q d' d'' d''') = (term22 d' d'' p q d''').
Proof. exact (TRANS (@lem1253432 p q d' d'' d''') (@lem1253589 d' d'' p q d''')). Qed.
Lemma lem1253597 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1253598 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term23 p q d' d'' d''') = (term24 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1253597) (@lem1253596 d' d'' p q d''')). Qed.
Lemma lem1253600 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253601 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term25 q p d'' d' d''') = (term25 p q d'' d' d''').
Proof. exact (@lem1253600 p q (term26 d'' d' d''')). Qed.
Lemma lem1253609 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253610 (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term27 q d'' d' d''') = (term28 q d'' d' d''').
Proof. exact (@lem1253609 d'' q (term29 d'' d' d''')). Qed.
Lemma lem1253618 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253619 (d'' : nat) (q : nat) (d' : nat) (d''' : nat) : (term30 q d'' d' d''') = (term30 d'' q d' d''').
Proof. exact (@lem1253618 d'' q (term31 d' d''')). Qed.
Lemma lem1253627 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253628 (q : nat) (d' : nat) (d''' : nat) : (term29 q d' d''') = (term32 q d' d''').
Proof. exact (@lem1253627 d' q (term14 d' d''')). Qed.
Lemma lem1253636 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253637 (d' : nat) (q : nat) (d''' : nat) : (term11 q d' d''') = (term11 d' q d''').
Proof. exact (@lem1253636 d' q (S d''')). Qed.
Lemma lem1253647 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253648 (d' : nat) (q : nat) (d''' : nat) : (term32 q d' d''') = (term19 d' q d''').
Proof. exact (MK_COMB (@lem1253647 d') (@lem1253637 d' q d''')). Qed.
Lemma lem1253655 (d' : nat) (q : nat) (d''' : nat) : (term29 q d' d''') = (term19 d' q d''').
Proof. exact (TRANS (@lem1253628 q d' d''') (@lem1253648 d' q d''')). Qed.
Lemma lem1253656 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1253657 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term30 d'' q d' d''') = (term16 d'' d' q d''').
Proof. exact (MK_COMB (@lem1253656 d'') (@lem1253655 d' q d''')). Qed.
Lemma lem1253659 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253660 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term16 d'' d' q d''') = (term15 d'' d' q d''').
Proof. exact (@lem1253659 d' d'' (term11 d' q d''')). Qed.
Lemma lem1253668 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253669 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 d'' d' q d''') = (term13 d' d'' q d''').
Proof. exact (@lem1253668 d' d'' (term14 q d''')). Qed.
Lemma lem1253685 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253686 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term15 d'' d' q d''') = (term20 d' d'' q d''').
Proof. exact (MK_COMB (@lem1253685 d') (@lem1253669 d' d'' q d''')). Qed.
Lemma lem1253693 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term16 d'' d' q d''') = (term20 d' d'' q d''').
Proof. exact (TRANS (@lem1253660 d'' d' q d''') (@lem1253686 d' d'' q d''')). Qed.
Lemma lem1253694 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term30 d'' q d' d''') = (term20 d' d'' q d''').
Proof. exact (TRANS (@lem1253657 d'' d' q d''') (@lem1253693 d' d'' q d''')). Qed.
Lemma lem1253695 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term30 q d'' d' d''') = (term20 d' d'' q d''').
Proof. exact (TRANS (@lem1253619 d'' q d' d''') (@lem1253694 d' d'' q d''')). Qed.
Lemma lem1253696 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1253697 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term28 q d'' d' d''') = (term33 d' d'' q d''').
Proof. exact (MK_COMB (@lem1253696 d'') (@lem1253695 d' d'' q d''')). Qed.
Lemma lem1253699 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253700 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term33 d' d'' q d''') = (term34 d' d'' q d''').
Proof. exact (@lem1253699 d' d'' (term13 d' d'' q d''')). Qed.
Lemma lem1253708 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253709 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term15 d' d'' q d''') = (term16 d' d'' q d''').
Proof. exact (@lem1253708 d' d'' (term11 d'' q d''')). Qed.
Lemma lem1253731 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253732 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term34 d' d'' q d''') = (term35 d' d'' q d''').
Proof. exact (MK_COMB (@lem1253731 d') (@lem1253709 d' d'' q d''')). Qed.
Lemma lem1253739 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term33 d' d'' q d''') = (term35 d' d'' q d''').
Proof. exact (TRANS (@lem1253700 d' d'' q d''') (@lem1253732 d' d'' q d''')). Qed.
Lemma lem1253740 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term28 q d'' d' d''') = (term35 d' d'' q d''').
Proof. exact (TRANS (@lem1253697 d' d'' q d''') (@lem1253739 d' d'' q d''')). Qed.
Lemma lem1253741 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term27 q d'' d' d''') = (term35 d' d'' q d''').
Proof. exact (TRANS (@lem1253610 q d'' d' d''') (@lem1253740 d' d'' q d''')). Qed.
Lemma lem1253742 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1253743 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term25 p q d'' d' d''') = (term36 p d' d'' q d''').
Proof. exact (MK_COMB (@lem1253742 p) (@lem1253741 d' d'' q d''')). Qed.
Lemma lem1253745 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253746 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term36 p d' d'' q d''') = (term37 p d' d'' q d''').
Proof. exact (@lem1253745 d' p (term16 d' d'' q d''')). Qed.
Lemma lem1253754 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253755 (d' : nat) (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term18 p d' d'' q d''') = (term18 d' p d'' q d''').
Proof. exact (@lem1253754 d' p (term19 d'' q d''')). Qed.
Lemma lem1253763 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253764 (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term16 p d'' q d''') = (term15 p d'' q d''').
Proof. exact (@lem1253763 d'' p (term11 d'' q d''')). Qed.
Lemma lem1253772 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253773 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term13 p d'' q d''') = (term13 d'' p q d''').
Proof. exact (@lem1253772 d'' p (term14 q d''')). Qed.
Lemma lem1253789 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1253790 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term15 p d'' q d''') = (term20 d'' p q d''').
Proof. exact (MK_COMB (@lem1253789 d'') (@lem1253773 d'' p q d''')). Qed.
Lemma lem1253797 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term16 p d'' q d''') = (term20 d'' p q d''').
Proof. exact (TRANS (@lem1253764 p d'' q d''') (@lem1253790 d'' p q d''')). Qed.
Lemma lem1253798 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253799 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term18 d' p d'' q d''') = (term21 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1253798 d') (@lem1253797 d'' p q d''')). Qed.
Lemma lem1253806 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term18 p d' d'' q d''') = (term21 d' d'' p q d''').
Proof. exact (TRANS (@lem1253755 d' p d'' q d''') (@lem1253799 d' d'' p q d''')). Qed.
Lemma lem1253807 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253808 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term37 p d' d'' q d''') = (term22 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1253807 d') (@lem1253806 d' d'' p q d''')). Qed.
Lemma lem1253815 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term36 p d' d'' q d''') = (term22 d' d'' p q d''').
Proof. exact (TRANS (@lem1253746 p d' d'' q d''') (@lem1253808 d' d'' p q d''')). Qed.
Lemma lem1253816 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term25 p q d'' d' d''') = (term22 d' d'' p q d''').
Proof. exact (TRANS (@lem1253743 p d' d'' q d''') (@lem1253815 d' d'' p q d''')). Qed.
Lemma lem1253817 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term25 q p d'' d' d''') = (term22 d' d'' p q d''').
Proof. exact (TRANS (@lem1253601 p q d'' d' d''') (@lem1253816 d' d'' p q d''')). Qed.
Lemma lem1253818 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : ((term3 p q d' d'' d''') = (term25 q p d'' d' d''')) = ((term22 d' d'' p q d''') = (term22 d' d'' p q d''')).
Proof. exact (MK_COMB (@lem1253598 d' d'' p q d''') (@lem1253817 d' d'' p q d''')). Qed.
Lemma lem1253820 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1253821 (x : nat) : (x = x) = True.
Proof. exact (@lem1253820 nat x). Qed.
Lemma lem1253822 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : ((term22 d' d'' p q d''') = (term22 d' d'' p q d''')) = True.
Proof. exact (@lem1253821 (term22 d' d'' p q d''')). Qed.
Lemma lem1253823 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term3 p q d' d'' d''') = (term25 q p d'' d' d''')) = True.
Proof. exact (TRANS (@lem1253818 d' d'' p q d''') (@lem1253822 d' d'' p q d''')). Qed.
Lemma lem1253824 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term3 p q d' d'' d''') = (term25 q p d'' d' d''')).
Proof. exact (SYM (@lem1253823 q p d'' d' d''')). Qed.
Lemma lem1253825 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term3 p q d' d'' d''') = (term25 q p d'' d' d''').
Proof. exact (EQ_MP (@lem1253824 q p d'' d' d''') (@lem0)). Qed.
Lemma lem1253826 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1253827 (q : nat) (p : nat) : (term0 p q) = (term0 q p).
Proof. exact (MK_COMB (@lem1253826) (@lem1253413 q p)). Qed.
Lemma lem1253828 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add p q) = (term3 p q d' d'' d''')) = ((Nat.add q p) = (term25 q p d'' d' d''')).
Proof. exact (MK_COMB (@lem1253827 q p) (@lem1253825 q p d'' d' d''')). Qed.
Lemma lem1253829 (m : nat) : term38 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1253830 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem1253831 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem1253830 m) (@lem1253829 m)). Qed.
Lemma lem1253832 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem1253831 m n). Qed.
Lemma lem1253833 (m : nat) (n : nat) : (term40 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem1253841 (m : nat) : term41 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1253842 (m : nat) : (term41 m) = (term42 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem1253843 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem1253842 m) (@lem1253841 m)). Qed.
Lemma lem1253844 (m : nat) (n : nat) : term43 m n.
Proof. exact (@lem1253843 m n). Qed.
Lemma lem1253845 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem1253846 (m : nat) (n : nat) : term44 m n.
Proof. exact (EQ_MP (@lem1253845 m n) (@lem1253844 m n)). Qed.
Lemma lem1253847 (m : nat) (n : nat) (p : nat) : term45 m n p.
Proof. exact (@lem1253846 m n p). Qed.
Lemma lem1253848 (m : nat) (n : nat) (p : nat) : (term45 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term45 m n p)). Qed.
Lemma lem1253851 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1253848 m n p) (@lem1253847 m n p)). Qed.
Lemma lem1253852 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add q p) = (term25 q p d'' d' d''')) = (p = (term27 p d'' d' d''')).
Proof. exact (@lem1253851 q p (term27 p d'' d' d''')). Qed.
Lemma lem1253854 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1253833 m n) (@lem1253832 m n)). Qed.
Lemma lem1253859 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (p = (term27 p d'' d' d''')) = ((term26 d'' d' d''') = (NUMERAL 0)).
Proof. exact (@lem1253854 p (term26 d'' d' d''')). Qed.
Lemma lem1253860 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add q p) = (term25 q p d'' d' d''')) = ((term26 d'' d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1253852 q p d'' d' d''') (@lem1253859 p d'' d' d''')). Qed.
Lemma lem1253861 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term46 p q d' d'' d''') = (term46 p q d' d'' d''').
Proof. exact (eq_refl (term46 p q d' d'' d''')). Qed.
Lemma lem1253862 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (((Nat.add p q) = (term3 p q d' d'' d''')) = ((Nat.add q p) = (term25 q p d'' d' d'''))) = (((Nat.add p q) = (term3 p q d' d'' d''')) = ((term26 d'' d' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1253861 p q d' d'' d''') (@lem1253860 q p d'' d' d''')). Qed.
Lemma lem1253863 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add p q) = (term3 p q d' d'' d''')) = ((term26 d'' d' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1253862 p q d'' d' d''') (@lem1253828 q p d'' d' d''')). Qed.
Lemma lem1253864 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1253865 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term47 p q d' d'' d''') = (term48 d'' d' d''').
Proof. exact (MK_COMB (@lem1253864) (@lem1253863 p q d'' d' d''')). Qed.
Lemma lem1253866 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1253867 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term49 p q d' d'' d''') = (term50 d'' d' d''').
Proof. exact (MK_COMB (@lem1253865 p q d'' d' d''') (@lem1253866)). Qed.
Lemma lem1253868 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term50 d'' d' d''') = (term49 p q d' d'' d''').
Proof. exact (SYM (@lem1253867 p q d'' d' d''')). Qed.
