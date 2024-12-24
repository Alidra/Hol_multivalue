Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1981613_term_abbrevs.
Require Import REAL_INV_MUL_spec.
Require Import REAL_MUL_AC_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1981498 (n : real) (m : real) (p : real) : term0 n m p.
Proof. exact (proj2 (@lem1486340 n m p)). Qed.
Lemma lem1981502 (x : real) : term1 x.
Proof. exact (@lem1595294 x). Qed.
Lemma lem1981503 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1981504 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1981503 x) (@lem1981502 x)). Qed.
Lemma lem1981505 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1981504 x y). Qed.
Lemma lem1981506 (x : real) (y : real) : (term3 x y) = ((term4 x y) = (term5 x y)).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1981508 (x : real) : term6 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1981509 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1981510 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1981509 x) (@lem1981508 x)). Qed.
Lemma lem1981511 (x : real) (y : real) : term8 x y.
Proof. exact (@lem1981510 x y). Qed.
Lemma lem1981512 (x : real) (y : real) : (term8 x y) = ((real_div x y) = (term9 x y)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1981520 (x : real) (y : real) : (real_div x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1981512 x y) (@lem1981511 x y)). Qed.
Lemma lem1981521 (x1 : real) (y1 : real) : (real_div x1 y1) = (term9 x1 y1).
Proof. exact (@lem1981520 x1 y1). Qed.
Lemma lem1981525 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1981526 (x1 : real) (y1 : real) : (term10 x1 y1) = (term11 x1 y1).
Proof. exact (MK_COMB (@lem1981525) (@lem1981521 x1 y1)). Qed.
Lemma lem1981528 (x : real) (y : real) : (real_div x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1981512 x y) (@lem1981511 x y)). Qed.
Lemma lem1981529 (x2 : real) (y2 : real) : (real_div x2 y2) = (term9 x2 y2).
Proof. exact (@lem1981528 x2 y2). Qed.
Lemma lem1981533 (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term12 x1 y1 x2 y2) = (term13 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1981526 x1 y1) (@lem1981529 x2 y2)). Qed.
Lemma lem1981535 (m : real) (n : real) (p : real) : (term14 m n p) = (term15 m n p).
Proof. exact (proj1 (@lem1981498 n m p)). Qed.
Lemma lem1981536 (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term13 x1 y1 x2 y2) = (term16 x1 y1 x2 y2).
Proof. exact (@lem1981535 x1 (real_inv y1) (term9 x2 y2)). Qed.
Lemma lem1981544 (n : real) (m : real) (p : real) : (term15 m n p) = (term15 n m p).
Proof. exact (proj2 (@lem1981498 n m p)). Qed.
Lemma lem1981545 (x2 : real) (y1 : real) (y2 : real) : (term17 y1 x2 y2) = (term18 x2 y1 y2).
Proof. exact (@lem1981544 x2 (real_inv y1) (real_inv y2)). Qed.
Lemma lem1981555 (x1 : real) : (real_mul x1) = (real_mul x1).
Proof. exact (eq_refl (real_mul x1)). Qed.
Lemma lem1981556 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term16 x1 y1 x2 y2) = (term19 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1981555 x1) (@lem1981545 x2 y1 y2)). Qed.
Lemma lem1981563 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term13 x1 y1 x2 y2) = (term19 x1 x2 y1 y2).
Proof. exact (TRANS (@lem1981536 x1 y1 x2 y2) (@lem1981556 x1 x2 y1 y2)). Qed.
Lemma lem1981564 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term12 x1 y1 x2 y2) = (term19 x1 x2 y1 y2).
Proof. exact (TRANS (@lem1981533 x1 y1 x2 y2) (@lem1981563 x1 x2 y1 y2)). Qed.
Lemma lem1981565 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1981566 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term20 x1 y1 x2 y2) = (term21 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1981565) (@lem1981564 x1 x2 y1 y2)). Qed.
Lemma lem1981568 (x : real) (y : real) : (real_div x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1981512 x y) (@lem1981511 x y)). Qed.
Lemma lem1981569 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term22 x1 x2 y1 y2) = (term23 x1 x2 y1 y2).
Proof. exact (@lem1981568 (real_mul x1 x2) (real_mul y1 y2)). Qed.
Lemma lem1981571 (m : real) (n : real) (p : real) : (term14 m n p) = (term15 m n p).
Proof. exact (proj1 (@lem1981498 n m p)). Qed.
Lemma lem1981572 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term23 x1 x2 y1 y2) = (term24 x1 x2 y1 y2).
Proof. exact (@lem1981571 x1 x2 (term4 y1 y2)). Qed.
Lemma lem1981579 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term22 x1 x2 y1 y2) = (term24 x1 x2 y1 y2).
Proof. exact (TRANS (@lem1981569 x1 x2 y1 y2) (@lem1981572 x1 x2 y1 y2)). Qed.
Lemma lem1981584 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1981506 x y) (@lem1981505 x y)). Qed.
Lemma lem1981585 (y1 : real) (y2 : real) : (term4 y1 y2) = (term5 y1 y2).
Proof. exact (@lem1981584 y1 y2). Qed.
Lemma lem1981589 (x2 : real) : (real_mul x2) = (real_mul x2).
Proof. exact (eq_refl (real_mul x2)). Qed.
Lemma lem1981590 (x2 : real) (y1 : real) (y2 : real) : (term25 x2 y1 y2) = (term18 x2 y1 y2).
Proof. exact (MK_COMB (@lem1981589 x2) (@lem1981585 y1 y2)). Qed.
Lemma lem1981597 (x1 : real) : (real_mul x1) = (real_mul x1).
Proof. exact (eq_refl (real_mul x1)). Qed.
Lemma lem1981598 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term24 x1 x2 y1 y2) = (term19 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1981597 x1) (@lem1981590 x2 y1 y2)). Qed.
Lemma lem1981605 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term22 x1 x2 y1 y2) = (term19 x1 x2 y1 y2).
Proof. exact (TRANS (@lem1981579 x1 x2 y1 y2) (@lem1981598 x1 x2 y1 y2)). Qed.
Lemma lem1981606 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : ((term12 x1 y1 x2 y2) = (term22 x1 x2 y1 y2)) = ((term19 x1 x2 y1 y2) = (term19 x1 x2 y1 y2)).
Proof. exact (MK_COMB (@lem1981566 x1 x2 y1 y2) (@lem1981605 x1 x2 y1 y2)). Qed.
Lemma lem1981608 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1981609 (x : real) : (x = x) = True.
Proof. exact (@lem1981608 real x). Qed.
Lemma lem1981610 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : ((term19 x1 x2 y1 y2) = (term19 x1 x2 y1 y2)) = True.
Proof. exact (@lem1981609 (term19 x1 x2 y1 y2)). Qed.
Lemma lem1981611 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : ((term12 x1 y1 x2 y2) = (term22 x1 x2 y1 y2)) = True.
Proof. exact (TRANS (@lem1981606 x1 x2 y1 y2) (@lem1981610 x1 x2 y1 y2)). Qed.
Lemma lem1981612 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : True = ((term12 x1 y1 x2 y2) = (term22 x1 x2 y1 y2)).
Proof. exact (SYM (@lem1981611 x1 x2 y1 y2)). Qed.
Lemma lem1981613 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term12 x1 y1 x2 y2) = (term22 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1981612 x1 x2 y1 y2) (@lem0)). Qed.
