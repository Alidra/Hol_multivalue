Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_DIV_EQ_term_abbrevs.
Require Import INT_DIV_LE_EQ_spec.
Require Import INT_NOT_LE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem2611505 (y : int) (x : int) (h1 : (term0 x y) = (int_lt y x)) : (term0 x y) = (int_lt y x).
Proof. exact (h1). Qed.
Lemma lem2611506 (y : int) (x : int) (h1 : (term0 x y) = (int_lt y x)) : (int_lt y x) = (term0 x y).
Proof. exact (SYM (@lem2611505 y x h1)). Qed.
Lemma lem2611507 (x : int) (y : int) (h1 : (int_lt y x) = (term0 x y)) : (int_lt y x) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2611508 (x : int) (y : int) (h1 : (int_lt y x) = (term0 x y)) : (term0 x y) = (int_lt y x).
Proof. exact (SYM (@lem2611507 x y h1)). Qed.
Lemma lem2611509 (x : int) (y : int) : ((term0 x y) = (int_lt y x)) = ((int_lt y x) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (int_lt y x) => @lem2611506 y x h1) (fun h1 : (int_lt y x) = (term0 x y) => @lem2611508 x y h1)). Qed.
Lemma lem2611510 (x : int) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : int => @lem2611509 x y)). Qed.
Lemma lem2611511 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611512 (x : int) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2611511) (@lem2611510 x)). Qed.
Lemma lem2611513 : term5 = term6.
Proof. exact (fun_ext (fun x : int => @lem2611512 x)). Qed.
Lemma lem2611514 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611515 : term7 = term8.
Proof. exact (MK_COMB (@lem2611514) (@lem2611513)). Qed.
Lemma lem2611516 : term8.
Proof. exact (EQ_MP (@lem2611515) (@lem2306766)). Qed.
Lemma lem2611517 (a : int) : term9 a.
Proof. exact (@lem2611502 a). Qed.
Lemma lem2611518 (a : int) : (term9 a) = (term10 a).
Proof. exact (eq_refl (term9 a)). Qed.
Lemma lem2611519 (a : int) : term10 a.
Proof. exact (EQ_MP (@lem2611518 a) (@lem2611517 a)). Qed.
Lemma lem2611520 (a : int) (b : int) : term11 a b.
Proof. exact (@lem2611519 a b). Qed.
Lemma lem2611521 (b : int) (a : int) : (term11 a b) = (term12 b a).
Proof. exact (eq_refl (term11 a b)). Qed.
Lemma lem2611522 (b : int) (a : int) : term12 b a.
Proof. exact (EQ_MP (@lem2611521 b a) (@lem2611520 a b)). Qed.
Lemma lem2611523 (b : int) (a : int) (c : int) : term13 b a c.
Proof. exact (@lem2611522 b a c). Qed.
Lemma lem2611524 (b : int) (a : int) (c : int) : (term13 b a c) = (term14 b a c).
Proof. exact (eq_refl (term13 b a c)). Qed.
Lemma lem2611525 (b : int) (a : int) (c : int) : term14 b a c.
Proof. exact (EQ_MP (@lem2611524 b a c) (@lem2611523 b a c)). Qed.
Lemma lem2611526 (a : int) (h1 : term15 a) : term15 a.
Proof. exact (h1). Qed.
Lemma lem2611527 (b : int) (c : int) (a : int) (h1 : term15 a) : (term16 b a c) = (term17 b a c).
Proof. exact (@lem2611525 b a c (@lem2611526 a h1)). Qed.
Lemma lem2611533 (x : int) : term18 x.
Proof. exact (@lem2611516 x). Qed.
Lemma lem2611534 (x : int) : (term18 x) = (term4 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2611535 (x : int) : term4 x.
Proof. exact (EQ_MP (@lem2611534 x) (@lem2611533 x)). Qed.
Lemma lem2611536 (x : int) (y : int) : term19 x y.
Proof. exact (@lem2611535 x y). Qed.
Lemma lem2611537 (x : int) (y : int) : (term19 x y) = ((int_lt y x) = (term0 x y)).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem2611554 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term20 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem2611555 (p : Prop) (q : Prop) (p' : Prop) : term21 p q p'.
Proof. exact (fun q' : Prop => @lem2611554 p q p' q'). Qed.
Lemma lem2611556 (p : Prop) (q : Prop) : term22 p q.
Proof. exact (fun p' : Prop => @lem2611555 p q p'). Qed.
Lemma lem2611557 (a : int) (c : int) (b : int) : term23 a c b.
Proof. exact (@lem2611556 (term15 a) ((term24 c b a) = (term25 a c b))). Qed.
Lemma lem2611558 (a : int) (c : int) (b : int) (p' : Prop) : term26 a c b p'.
Proof. exact (@lem2611557 a c b p'). Qed.
Lemma lem2611559 (a : int) (c : int) (b : int) (p' : Prop) : (term26 a c b p') = (term27 a c b p').
Proof. exact (eq_refl (term26 a c b p')). Qed.
Lemma lem2611560 (a : int) (c : int) (b : int) (p' : Prop) : term27 a c b p'.
Proof. exact (EQ_MP (@lem2611559 a c b p') (@lem2611558 a c b p')). Qed.
Lemma lem2611561 (a : int) (c : int) (b : int) (p' : Prop) (q' : Prop) : term28 a c b p' q'.
Proof. exact (@lem2611560 a c b p' q'). Qed.
Lemma lem2611562 (a : int) (c : int) (b : int) (p' : Prop) (q' : Prop) : (term28 a c b p' q') = (term29 a c b p' q').
Proof. exact (eq_refl (term28 a c b p' q')). Qed.
Lemma lem2611563 (a : int) (c : int) (b : int) (p' : Prop) (q' : Prop) : term29 a c b p' q'.
Proof. exact (EQ_MP (@lem2611562 a c b p' q') (@lem2611561 a c b p' q')). Qed.
Lemma lem2611565 (x : int) (y : int) : (int_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem2611537 x y) (@lem2611536 x y)). Qed.
Lemma lem2611566 (a : int) : (term15 a) = (term30 a).
Proof. exact (@lem2611565 a term31). Qed.
Lemma lem2611567 (c : int) (b : int) (a : int) (q' : Prop) : term32 c b a q'.
Proof. exact (@lem2611563 a c b (term30 a) q'). Qed.
Lemma lem2611568 (c : int) (b : int) (a : int) (q' : Prop) : term33 c b a q'.
Proof. exact (@lem2611567 c b a q' (@lem2611566 a)). Qed.
Lemma lem2611569 (a : int) (h1 : term30 a) : term30 a.
Proof. exact (h1). Qed.
Lemma lem2611570 (a : int) : term34 a.
Proof. exact (@lem82 (term35 a)). Qed.
Lemma lem2611575 (x : int) (y : int) : (int_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem2611537 x y) (@lem2611536 x y)). Qed.
Lemma lem2611576 (b : int) (a : int) (c : int) : (term24 c b a) = (term36 b a c).
Proof. exact (@lem2611575 (div b a) c). Qed.
Lemma lem2611578 (b : int) (a : int) (c : int) : term14 b a c.
Proof. exact (fun h0 : term15 a => @lem2611527 b c a h0). Qed.
Lemma lem2611580 (x : int) (y : int) : (int_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem2611537 x y) (@lem2611536 x y)). Qed.
Lemma lem2611581 (a : int) : (term15 a) = (term30 a).
Proof. exact (@lem2611580 a term31). Qed.
Lemma lem2611583 (a : int) (h1 : term30 a) : (term35 a) = False.
Proof. exact (@lem2611570 a (@lem2611569 a h1)). Qed.
Lemma lem2611584 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2611585 (a : int) (h1 : term30 a) : (term30 a) = (~ False).
Proof. exact (MK_COMB (@lem2611584) (@lem2611583 a h1)). Qed.
Lemma lem2611587 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2611588 (a : int) (h1 : term30 a) : (term30 a) = True.
Proof. exact (TRANS (@lem2611585 a h1) (@lem2611587)). Qed.
Lemma lem2611589 (a : int) (h1 : term30 a) : (term15 a) = True.
Proof. exact (TRANS (@lem2611581 a) (@lem2611588 a h1)). Qed.
Lemma lem2611590 (a : int) (h1 : term30 a) : True = (term15 a).
Proof. exact (SYM (@lem2611589 a h1)). Qed.
Lemma lem2611591 (a : int) (h1 : term30 a) : term15 a.
Proof. exact (EQ_MP (@lem2611590 a h1) (@lem0)). Qed.
Lemma lem2611592 (b : int) (c : int) (a : int) (h1 : term30 a) : (term16 b a c) = (term17 b a c).
Proof. exact (@lem2611578 b a c (@lem2611591 a h1)). Qed.
Lemma lem2611594 (x : int) (y : int) : (int_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem2611537 x y) (@lem2611536 x y)). Qed.
Lemma lem2611595 (a : int) (c : int) (b : int) : (term17 b a c) = (term37 a c b).
Proof. exact (@lem2611594 (term38 a c) b). Qed.
Lemma lem2611596 (c : int) (b : int) (a : int) (h1 : term30 a) : (term16 b a c) = (term37 a c b).
Proof. exact (TRANS (@lem2611592 b c a h1) (@lem2611595 a c b)). Qed.
Lemma lem2611597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2611598 (c : int) (b : int) (a : int) (h1 : term30 a) : (term36 b a c) = (term39 a c b).
Proof. exact (MK_COMB (@lem2611597) (@lem2611596 c b a h1)). Qed.
Lemma lem2611600 (t : Prop) : (term40 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem2611601 (a : int) (c : int) (b : int) : (term39 a c b) = (term25 a c b).
Proof. exact (@lem2611600 (term25 a c b)). Qed.
Lemma lem2611602 (c : int) (b : int) (a : int) (h1 : term30 a) : (term36 b a c) = (term25 a c b).
Proof. exact (TRANS (@lem2611598 c b a h1) (@lem2611601 a c b)). Qed.
Lemma lem2611603 (c : int) (b : int) (a : int) (h1 : term30 a) : (term24 c b a) = (term25 a c b).
Proof. exact (TRANS (@lem2611576 b a c) (@lem2611602 c b a h1)). Qed.
Lemma lem2611604 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2611605 (c : int) (b : int) (a : int) (h1 : term30 a) : (term41 c b a) = (term42 a c b).
Proof. exact (MK_COMB (@lem2611604) (@lem2611603 c b a h1)). Qed.
Lemma lem2611606 (a : int) (c : int) (b : int) : (term25 a c b) = (term25 a c b).
Proof. exact (eq_refl (term25 a c b)). Qed.
Lemma lem2611607 (c : int) (b : int) (a : int) (h1 : term30 a) : ((term24 c b a) = (term25 a c b)) = ((term25 a c b) = (term25 a c b)).
Proof. exact (MK_COMB (@lem2611605 c b a h1) (@lem2611606 a c b)). Qed.
Lemma lem2611609 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2611610 (x : Prop) : (x = x) = True.
Proof. exact (@lem2611609 Prop x). Qed.
Lemma lem2611611 (a : int) (c : int) (b : int) : ((term25 a c b) = (term25 a c b)) = True.
Proof. exact (@lem2611610 (term25 a c b)). Qed.
Lemma lem2611612 (c : int) (b : int) (a : int) (h1 : term30 a) : ((term24 c b a) = (term25 a c b)) = True.
Proof. exact (TRANS (@lem2611607 c b a h1) (@lem2611611 a c b)). Qed.
Lemma lem2611613 (a : int) (c : int) (b : int) : term43 a c b.
Proof. exact (fun h0 : term30 a => @lem2611612 c b a h0). Qed.
Lemma lem2611614 (c : int) (b : int) (a : int) : term44 c b a.
Proof. exact (@lem2611568 c b a True). Qed.
Lemma lem2611615 (c : int) (b : int) (a : int) : (term45 a c b) = (term46 a).
Proof. exact (@lem2611614 c b a (@lem2611613 a c b)). Qed.
Lemma lem2611617 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem2611618 (a : int) : (term46 a) = True.
Proof. exact (@lem2611617 (term30 a)). Qed.
Lemma lem2611619 (a : int) (c : int) (b : int) : (term45 a c b) = True.
Proof. exact (TRANS (@lem2611615 c b a) (@lem2611618 a)). Qed.
Lemma lem2611620 (a : int) (b : int) : (term47 a b) = term48.
Proof. exact (fun_ext (fun c : int => @lem2611619 a c b)). Qed.
Lemma lem2611621 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611622 (a : int) (b : int) : (term49 a b) = term50.
Proof. exact (MK_COMB (@lem2611621) (@lem2611620 a b)). Qed.
Lemma lem2611624 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2611625 (t : Prop) : (term52 t) = t.
Proof. exact (@lem2611624 int t). Qed.
Lemma lem2611626 : term50 = True.
Proof. exact (@lem2611625 True). Qed.
Lemma lem2611627 (a : int) (b : int) : (term49 a b) = True.
Proof. exact (TRANS (@lem2611622 a b) (@lem2611626)). Qed.
Lemma lem2611628 (a : int) : (term53 a) = term48.
Proof. exact (fun_ext (fun b : int => @lem2611627 a b)). Qed.
Lemma lem2611629 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611630 (a : int) : (term54 a) = term50.
Proof. exact (MK_COMB (@lem2611629) (@lem2611628 a)). Qed.
Lemma lem2611632 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2611633 (t : Prop) : (term52 t) = t.
Proof. exact (@lem2611632 int t). Qed.
Lemma lem2611634 : term50 = True.
Proof. exact (@lem2611633 True). Qed.
Lemma lem2611635 (a : int) : (term54 a) = True.
Proof. exact (TRANS (@lem2611630 a) (@lem2611634)). Qed.
Lemma lem2611636 : term55 = term48.
Proof. exact (fun_ext (fun a : int => @lem2611635 a)). Qed.
Lemma lem2611637 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611638 : term56 = term50.
Proof. exact (MK_COMB (@lem2611637) (@lem2611636)). Qed.
Lemma lem2611640 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2611641 (t : Prop) : (term52 t) = t.
Proof. exact (@lem2611640 int t). Qed.
Lemma lem2611642 : term50 = True.
Proof. exact (@lem2611641 True). Qed.
Lemma lem2611643 : term56 = True.
Proof. exact (TRANS (@lem2611638) (@lem2611642)). Qed.
Lemma lem2611644 : True = term56.
Proof. exact (SYM (@lem2611643)). Qed.
Lemma lem2611645 : term56.
Proof. exact (EQ_MP (@lem2611644) (@lem0)). Qed.
