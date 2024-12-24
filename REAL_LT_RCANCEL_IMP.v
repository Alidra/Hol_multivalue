Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_RCANCEL_IMP_term_abbrevs.
Require Import REAL_LT_LCANCEL_IMP_spec.
Require Import thm0_spec.
Require Import thm1338712_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1598530 (x : real) : term0 x.
Proof. exact (@lem1598529 x). Qed.
Lemma lem1598531 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1598532 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1598531 x) (@lem1598530 x)). Qed.
Lemma lem1598533 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1598532 x y). Qed.
Lemma lem1598534 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1598535 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1598534 x y) (@lem1598533 x y)). Qed.
Lemma lem1598536 (x : real) (y : real) (z : real) : term4 x y z.
Proof. exact (@lem1598535 x y z). Qed.
Lemma lem1598537 (x : real) (y : real) (z : real) : (term4 x y z) = (term5 x y z).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem1598538 (x : real) (y : real) (z : real) : term5 x y z.
Proof. exact (EQ_MP (@lem1598537 x y z) (@lem1598536 x y z)). Qed.
Lemma lem1598539 (x : real) (y : real) (z : real) : (term5 x y z) = ((term5 x y z) = True).
Proof. exact (@lem7 (term5 x y z)). Qed.
Lemma lem1598541 (x : real) : term6 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1598542 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1598543 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1598542 x) (@lem1598541 x)). Qed.
Lemma lem1598544 (x : real) (y : real) : term8 x y.
Proof. exact (@lem1598543 x y). Qed.
Lemma lem1598545 (y : real) (x : real) : (term8 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1598564 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1598545 y x) (@lem1598544 x y)). Qed.
Lemma lem1598565 (z : real) (x : real) : (real_mul x z) = (real_mul z x).
Proof. exact (@lem1598564 z x). Qed.
Lemma lem1598566 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1598567 (z : real) (x : real) : (term9 x z) = (term9 z x).
Proof. exact (MK_COMB (@lem1598566) (@lem1598565 z x)). Qed.
Lemma lem1598569 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1598545 y x) (@lem1598544 x y)). Qed.
Lemma lem1598570 (z : real) (y : real) : (real_mul y z) = (real_mul z y).
Proof. exact (@lem1598569 z y). Qed.
Lemma lem1598571 (x : real) (z : real) (y : real) : (term10 x y z) = (term11 x z y).
Proof. exact (MK_COMB (@lem1598567 z x) (@lem1598570 z y)). Qed.
Lemma lem1598572 (z : real) : (term12 z) = (term12 z).
Proof. exact (eq_refl (term12 z)). Qed.
Lemma lem1598573 (x : real) (z : real) (y : real) : (term13 x y z) = (term14 x z y).
Proof. exact (MK_COMB (@lem1598572 z) (@lem1598571 x z y)). Qed.
Lemma lem1598574 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1598575 (x : real) (z : real) (y : real) : (term15 x y z) = (term16 x z y).
Proof. exact (MK_COMB (@lem1598574) (@lem1598573 x z y)). Qed.
Lemma lem1598576 (x : real) (y : real) : (real_lt x y) = (real_lt x y).
Proof. exact (eq_refl (real_lt x y)). Qed.
Lemma lem1598577 (z : real) (x : real) (y : real) : (term17 z x y) = (term5 z x y).
Proof. exact (MK_COMB (@lem1598575 x z y) (@lem1598576 x y)). Qed.
Lemma lem1598578 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (fun_ext (fun z : real => @lem1598577 z x y)). Qed.
Lemma lem1598579 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1598580 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1598579) (@lem1598578 x y)). Qed.
Lemma lem1598581 (x : real) : (term22 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1598580 x y)). Qed.
Lemma lem1598582 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1598583 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1598582) (@lem1598581 x)). Qed.
Lemma lem1598584 : term26 = term27.
Proof. exact (fun_ext (fun x : real => @lem1598583 x)). Qed.
Lemma lem1598585 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1598586 : term28 = term29.
Proof. exact (MK_COMB (@lem1598585) (@lem1598584)). Qed.
Lemma lem1598587 : term29 = term28.
Proof. exact (SYM (@lem1598586)). Qed.
Lemma lem1598601 (x : real) (y : real) (z : real) : (term5 x y z) = True.
Proof. exact (EQ_MP (@lem1598539 x y z) (@lem1598538 x y z)). Qed.
Lemma lem1598602 (z : real) (x : real) (y : real) : (term5 z x y) = True.
Proof. exact (@lem1598601 z x y). Qed.
Lemma lem1598603 (x : real) (y : real) : (term19 x y) = term30.
Proof. exact (fun_ext (fun z : real => @lem1598602 z x y)). Qed.
Lemma lem1598604 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1598605 (x : real) (y : real) : (term21 x y) = term31.
Proof. exact (MK_COMB (@lem1598604) (@lem1598603 x y)). Qed.
Lemma lem1598607 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1598608 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1598607 real t). Qed.
Lemma lem1598609 : term31 = True.
Proof. exact (@lem1598608 True). Qed.
Lemma lem1598610 (x : real) (y : real) : (term21 x y) = True.
Proof. exact (TRANS (@lem1598605 x y) (@lem1598609)). Qed.
Lemma lem1598611 (x : real) : (term23 x) = term30.
Proof. exact (fun_ext (fun y : real => @lem1598610 x y)). Qed.
Lemma lem1598612 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1598613 (x : real) : (term25 x) = term31.
Proof. exact (MK_COMB (@lem1598612) (@lem1598611 x)). Qed.
Lemma lem1598615 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1598616 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1598615 real t). Qed.
Lemma lem1598617 : term31 = True.
Proof. exact (@lem1598616 True). Qed.
Lemma lem1598618 (x : real) : (term25 x) = True.
Proof. exact (TRANS (@lem1598613 x) (@lem1598617)). Qed.
Lemma lem1598619 : term27 = term30.
Proof. exact (fun_ext (fun x : real => @lem1598618 x)). Qed.
Lemma lem1598620 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1598621 : term29 = term31.
Proof. exact (MK_COMB (@lem1598620) (@lem1598619)). Qed.
Lemma lem1598623 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1598624 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1598623 real t). Qed.
Lemma lem1598625 : term31 = True.
Proof. exact (@lem1598624 True). Qed.
Lemma lem1598626 : term29 = True.
Proof. exact (TRANS (@lem1598621) (@lem1598625)). Qed.
Lemma lem1598627 : True = term29.
Proof. exact (SYM (@lem1598626)). Qed.
Lemma lem1598628 : term29.
Proof. exact (EQ_MP (@lem1598627) (@lem0)). Qed.
Lemma lem1598629 : term28.
Proof. exact (EQ_MP (@lem1598587) (@lem1598628)). Qed.
