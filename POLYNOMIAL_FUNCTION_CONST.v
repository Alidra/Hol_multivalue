Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_CONST_term_abbrevs.
Require Import REAL_MUL_RID_spec.
Require Import SUM_SING_NUMSEG_spec.
Require Import polynomial_function_spec.
Require Import thm0_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem7553489 (x : real) : term0 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem7553490 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem7553497 (f : nat -> real) : term2 f.
Proof. exact (@lem7221565 f). Qed.
Lemma lem7553498 (f : nat -> real) : (term2 f) = (term3 f).
Proof. exact (eq_refl (term2 f)). Qed.
Lemma lem7553499 (f : nat -> real) : term3 f.
Proof. exact (EQ_MP (@lem7553498 f) (@lem7553497 f)). Qed.
Lemma lem7553500 (f : nat -> real) (n : nat) : term4 f n.
Proof. exact (@lem7553499 f n). Qed.
Lemma lem7553501 (f : nat -> real) (n : nat) : (term4 f n) = ((term5 n f) = (f n)).
Proof. exact (eq_refl (term4 f n)). Qed.
Lemma lem7553503 (p : real -> real) : term6 p.
Proof. exact (@lem7553488 p). Qed.
Lemma lem7553504 (p : real -> real) : (term6 p) = ((polynomial_function p) = (term7 p)).
Proof. exact (eq_refl (term6 p)). Qed.
Lemma lem7553507 (p : real -> real) : (polynomial_function p) = (term7 p).
Proof. exact (EQ_MP (@lem7553504 p) (@lem7553503 p)). Qed.
Lemma lem7553508 (c : real) : (term8 c) = (term9 c).
Proof. exact (@lem7553507 (term10 c)). Qed.
Lemma lem7553524 {A B : Type'} (f : A -> B) (y : A) : (term11 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7553525 (f : real -> real) (y : real) : (term12 f y) = (f y).
Proof. exact (@lem7553524 real real f y). Qed.
Lemma lem7553526 (c : real) (x : real) : (term13 c x) = (term14 c x).
Proof. exact (@lem7553525 (term10 c) x). Qed.
Lemma lem7553527 (x : real) (c : real) : (term14 c x) = c.
Proof. exact (eq_refl (term14 c x)). Qed.
Lemma lem7553528 (c : real) : (term15 c) = (term10 c).
Proof. exact (fun_ext (fun x : real => @lem7553527 x c)). Qed.
Lemma lem7553529 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7553530 (c : real) (x : real) : (term13 c x) = (term14 c x).
Proof. exact (MK_COMB (@lem7553528 c) (@lem7553529 x)). Qed.
Lemma lem7553531 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7553532 (c : real) (x : real) : (term16 c x) = (term17 c x).
Proof. exact (MK_COMB (@lem7553531) (@lem7553530 c x)). Qed.
Lemma lem7553533 (x : real) (c : real) : (term14 c x) = c.
Proof. exact (eq_refl (term14 c x)). Qed.
Lemma lem7553534 (x : real) (c : real) : ((term13 c x) = (term14 c x)) = ((term14 c x) = c).
Proof. exact (MK_COMB (@lem7553532 c x) (@lem7553533 x c)). Qed.
Lemma lem7553535 (x : real) (c : real) : (term14 c x) = c.
Proof. exact (EQ_MP (@lem7553534 x c) (@lem7553526 c x)). Qed.
Lemma lem7553536 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7553537 (x : real) (c : real) : (term17 c x) = (@eq real c).
Proof. exact (MK_COMB (@lem7553536) (@lem7553535 x c)). Qed.
Lemma lem7553538 (m : nat) (c : nat -> real) (x : real) : (term18 m c x) = (term18 m c x).
Proof. exact (eq_refl (term18 m c x)). Qed.
Lemma lem7553539 (c : real) (m : nat) (c' : nat -> real) (x : real) : ((term14 c x) = (term18 m c' x)) = (c = (term18 m c' x)).
Proof. exact (MK_COMB (@lem7553537 x c) (@lem7553538 m c' x)). Qed.
Lemma lem7553542 (c : real) (m : nat) (c' : nat -> real) : (term19 c m c') = (term20 c m c').
Proof. exact (fun_ext (fun x : real => @lem7553539 c m c' x)). Qed.
Lemma lem7553543 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7553544 (c : real) (m : nat) (c' : nat -> real) : (term21 c m c') = (term22 c m c').
Proof. exact (MK_COMB (@lem7553543) (@lem7553542 c m c')). Qed.
Lemma lem7553549 (c : real) (m : nat) : (term23 c m) = (term24 c m).
Proof. exact (fun_ext (fun c' : nat -> real => @lem7553544 c m c')). Qed.
Lemma lem7553550 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7553551 (c : real) (m : nat) : (term25 c m) = (term26 c m).
Proof. exact (MK_COMB (@lem7553550) (@lem7553549 c m)). Qed.
Lemma lem7553556 (c : real) : (term27 c) = (term28 c).
Proof. exact (fun_ext (fun m : nat => @lem7553551 c m)). Qed.
Lemma lem7553557 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7553558 (c : real) : (term9 c) = (term29 c).
Proof. exact (MK_COMB (@lem7553557) (@lem7553556 c)). Qed.
Lemma lem7553563 (c : real) : (term8 c) = (term29 c).
Proof. exact (TRANS (@lem7553508 c) (@lem7553558 c)). Qed.
Lemma lem7553564 (c : real) : (term29 c) = (term8 c).
Proof. exact (SYM (@lem7553563 c)). Qed.
Lemma lem7553572 (f : nat -> real) (n : nat) : (term5 n f) = (f n).
Proof. exact (EQ_MP (@lem7553501 f n) (@lem7553500 f n)). Qed.
Lemma lem7553573 (c : real) (x : real) : (term30 c x) = (term31 c x).
Proof. exact (@lem7553572 (term32 c x) (NUMERAL 0)). Qed.
Lemma lem7553575 {A B : Type'} (f : A -> B) (y : A) : (term11 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7553576 (f : nat -> real) (y : nat) : (term33 f y) = (f y).
Proof. exact (@lem7553575 nat real f y). Qed.
Lemma lem7553577 (c : real) (x : real) : (term34 c x) = (term31 c x).
Proof. exact (@lem7553576 (term32 c x) (NUMERAL 0)). Qed.
Lemma lem7553578 (c : real) (x : real) (i : nat) : (term35 c x i) = (term36 c x i).
Proof. exact (eq_refl (term35 c x i)). Qed.
Lemma lem7553579 (c : real) (x : real) : (term37 c x) = (term32 c x).
Proof. exact (fun_ext (fun i : nat => @lem7553578 c x i)). Qed.
Lemma lem7553580 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7553581 (c : real) (x : real) : (term34 c x) = (term31 c x).
Proof. exact (MK_COMB (@lem7553579 c x) (@lem7553580)). Qed.
Lemma lem7553582 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7553583 (c : real) (x : real) : (term38 c x) = (term39 c x).
Proof. exact (MK_COMB (@lem7553582) (@lem7553581 c x)). Qed.
Lemma lem7553584 (c : real) (x : real) : (term31 c x) = (term40 c x).
Proof. exact (eq_refl (term31 c x)). Qed.
Lemma lem7553585 (c : real) (x : real) : ((term34 c x) = (term31 c x)) = ((term31 c x) = (term40 c x)).
Proof. exact (MK_COMB (@lem7553583 c x) (@lem7553584 c x)). Qed.
Lemma lem7553586 (c : real) (x : real) : (term31 c x) = (term40 c x).
Proof. exact (EQ_MP (@lem7553585 c x) (@lem7553577 c x)). Qed.
Lemma lem7553587 (c : real) (x : real) : (term30 c x) = (term40 c x).
Proof. exact (TRANS (@lem7553573 c x) (@lem7553586 c x)). Qed.
Lemma lem7553589 {A B : Type'} (f : A -> B) (y : A) : (term11 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7553590 (f : nat -> real) (y : nat) : (term33 f y) = (f y).
Proof. exact (@lem7553589 nat real f y). Qed.
Lemma lem7553591 (c : real) : (term41 c) = (term42 c).
Proof. exact (@lem7553590 (term43 c) (NUMERAL 0)). Qed.
Lemma lem7553592 (i : nat) (c : real) : (term44 c i) = c.
Proof. exact (eq_refl (term44 c i)). Qed.
Lemma lem7553593 (c : real) : (term45 c) = (term43 c).
Proof. exact (fun_ext (fun i : nat => @lem7553592 i c)). Qed.
Lemma lem7553594 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7553595 (c : real) : (term41 c) = (term42 c).
Proof. exact (MK_COMB (@lem7553593 c) (@lem7553594)). Qed.
Lemma lem7553596 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7553597 (c : real) : (term46 c) = (term47 c).
Proof. exact (MK_COMB (@lem7553596) (@lem7553595 c)). Qed.
Lemma lem7553598 (c : real) : (term42 c) = c.
Proof. exact (eq_refl (term42 c)). Qed.
Lemma lem7553599 (c : real) : ((term41 c) = (term42 c)) = ((term42 c) = c).
Proof. exact (MK_COMB (@lem7553597 c) (@lem7553598 c)). Qed.
Lemma lem7553600 (c : real) : (term42 c) = c.
Proof. exact (EQ_MP (@lem7553599 c) (@lem7553591 c)). Qed.
Lemma lem7553601 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7553602 (c : real) : (term48 c) = (real_mul c).
Proof. exact (MK_COMB (@lem7553601) (@lem7553600 c)). Qed.
Lemma lem7553604 (x : real) : (term49 x) = term50.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem7553605 (x : real) (c : real) : (term40 c x) = (term1 c).
Proof. exact (MK_COMB (@lem7553602 c) (@lem7553604 x)). Qed.
Lemma lem7553607 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem7553490 x) (@lem7553489 x)). Qed.
Lemma lem7553608 (c : real) : (term1 c) = c.
Proof. exact (@lem7553607 c). Qed.
Lemma lem7553609 (x : real) (c : real) : (term40 c x) = c.
Proof. exact (TRANS (@lem7553605 x c) (@lem7553608 c)). Qed.
Lemma lem7553610 (x : real) (c : real) : (term30 c x) = c.
Proof. exact (TRANS (@lem7553587 c x) (@lem7553609 x c)). Qed.
Lemma lem7553611 (c : real) : (@eq real c) = (@eq real c).
Proof. exact (eq_refl (@eq real c)). Qed.
Lemma lem7553612 (x : real) (c : real) : (c = (term30 c x)) = (c = c).
Proof. exact (MK_COMB (@lem7553611 c) (@lem7553610 x c)). Qed.
Lemma lem7553614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7553615 (x : real) : (x = x) = True.
Proof. exact (@lem7553614 real x). Qed.
Lemma lem7553616 (c : real) : (c = c) = True.
Proof. exact (@lem7553615 c). Qed.
Lemma lem7553617 (c : real) (x : real) : (c = (term30 c x)) = True.
Proof. exact (TRANS (@lem7553612 x c) (@lem7553616 c)). Qed.
Lemma lem7553618 (c : real) : (term51 c) = term52.
Proof. exact (fun_ext (fun x : real => @lem7553617 c x)). Qed.
Lemma lem7553619 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7553620 (c : real) : (term53 c) = term54.
Proof. exact (MK_COMB (@lem7553619) (@lem7553618 c)). Qed.
Lemma lem7553622 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7553623 (t : Prop) : (term56 t) = t.
Proof. exact (@lem7553622 real t). Qed.
Lemma lem7553624 : term54 = True.
Proof. exact (@lem7553623 True). Qed.
Lemma lem7553625 (c : real) : (term53 c) = True.
Proof. exact (TRANS (@lem7553620 c) (@lem7553624)). Qed.
Lemma lem7553626 (c : real) : True = (term53 c).
Proof. exact (SYM (@lem7553625 c)). Qed.
Lemma lem7553627 (c : real) : term53 c.
Proof. exact (EQ_MP (@lem7553626 c) (@lem0)). Qed.
Lemma lem7553628 (c : real) : term57 c.
Proof. exact (ex_intro (term58 c) (term43 c) (@lem7553627 c)). Qed.
Lemma lem7553629 (c : real) : term29 c.
Proof. exact (ex_intro (term28 c) (NUMERAL 0) (@lem7553628 c)). Qed.
Lemma lem7553630 (c : real) : term8 c.
Proof. exact (EQ_MP (@lem7553564 c) (@lem7553629 c)). Qed.
Lemma lem7553635 : term59.
Proof. exact (fun c : real => @lem7553630 c). Qed.
