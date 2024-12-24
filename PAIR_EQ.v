Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIR_EQ_term_abbrevs.
Require Import COMMA_DEF_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FUN_EQ_THM_spec.
Require Import REP_ABS_PAIR_spec.
Require Import mk_pair_def_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21386_spec.
Require Import thm32_spec.
Lemma lem45479 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem45480 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem45481 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem45480 t1) (@lem45479 t1)). Qed.
Lemma lem45482 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem45481 t1 t2). Qed.
Lemma lem45483 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem45484 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem45483 t1 t2) (@lem45482 t1 t2)). Qed.
Lemma lem45485 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem45484 t1 t2 t3). Qed.
Lemma lem45486 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem45487 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem45486 t1 t2 t3) (@lem45485 t1 t2 t3)). Qed.
Lemma lem45488 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem45487 t1 t2 t3)). Qed.
Lemma lem45489 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem45490 {A B : Type'} (f : A -> B) : (term7 A B f) = (term8 A B f).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem45491 {A B : Type'} (f : A -> B) : term8 A B f.
Proof. exact (EQ_MP (@lem45490 A B f) (@lem45489 A B f)). Qed.
Lemma lem45492 {A B : Type'} (f : A -> B) (g : A -> B) : term9 A B f g.
Proof. exact (@lem45491 A B f g). Qed.
Lemma lem45493 {A B : Type'} (f : A -> B) (g : A -> B) : (term9 A B f g) = ((f = g) = (term10 A B f g)).
Proof. exact (eq_refl (term9 A B f g)). Qed.
Lemma lem45495 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem44172 A B x). Qed.
Lemma lem45496 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem45497 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem45496 A B x) (@lem45495 A B x)). Qed.
Lemma lem45498 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem45497 A B x y). Qed.
Lemma lem45499 {A B : Type'} (x : A) (y : B) : (term13 A B x y) = ((@mk_pair A B x y) = (term14 A B x y)).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem45501 {A B : Type'} (x : A) : term15 A B x.
Proof. exact (@lem45455 A B x). Qed.
Lemma lem45502 {A B : Type'} (x : A) : (term15 A B x) = (term16 A B x).
Proof. exact (eq_refl (term15 A B x)). Qed.
Lemma lem45503 {A B : Type'} (x : A) : term16 A B x.
Proof. exact (EQ_MP (@lem45502 A B x) (@lem45501 A B x)). Qed.
Lemma lem45504 {A B : Type'} (x : A) (y : B) : term17 A B x y.
Proof. exact (@lem45503 A B x y). Qed.
Lemma lem45505 {A B : Type'} (x : A) (y : B) : (term17 A B x y) = ((term18 A B x y) = (@mk_pair A B x y)).
Proof. exact (eq_refl (term17 A B x y)). Qed.
Lemma lem45507 {A B : Type'} : (@REP_prod A B) = (@REP_prod A B).
Proof. exact (eq_refl (@REP_prod A B)). Qed.
Lemma lem45508 {A B : Type'} (x : A) : term19 A B x.
Proof. exact (@lem45466 A B x). Qed.
Lemma lem45509 {A B : Type'} (x : A) : (term19 A B x) = (term20 A B x).
Proof. exact (eq_refl (term19 A B x)). Qed.
Lemma lem45510 {A B : Type'} (x : A) : term20 A B x.
Proof. exact (EQ_MP (@lem45509 A B x) (@lem45508 A B x)). Qed.
Lemma lem45511 {A B : Type'} (x : A) (y : B) : term21 A B x y.
Proof. exact (@lem45510 A B x y). Qed.
Lemma lem45512 {A B : Type'} (x : A) (y : B) : (term21 A B x y) = ((@pair A B x y) = (term22 A B x y)).
Proof. exact (eq_refl (term21 A B x y)). Qed.
Lemma lem45521 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (term22 A B x y).
Proof. exact (EQ_MP (@lem45512 A B x y) (@lem45511 A B x y)). Qed.
Lemma lem45522 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (term22 A B x y).
Proof. exact (@lem45521 A B x y). Qed.
Lemma lem45523 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem45524 {A B : Type'} (x : A) (y : B) : (term23 A B x y) = (term24 A B x y).
Proof. exact (MK_COMB (@lem45523 A B) (@lem45522 A B x y)). Qed.
Lemma lem45526 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (term22 A B x y).
Proof. exact (EQ_MP (@lem45512 A B x y) (@lem45511 A B x y)). Qed.
Lemma lem45527 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (term22 A B x y).
Proof. exact (@lem45526 A B x y). Qed.
Lemma lem45528 {A B : Type'} (a : A) (b : B) : (@pair A B a b) = (term22 A B a b).
Proof. exact (@lem45527 A B a b). Qed.
Lemma lem45529 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : ((@pair A B x y) = (@pair A B a b)) = ((term22 A B x y) = (term22 A B a b)).
Proof. exact (MK_COMB (@lem45524 A B x y) (@lem45528 A B a b)). Qed.
Lemma lem45532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem45533 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term25 A B x y a b) = (term26 A B x y a b).
Proof. exact (MK_COMB (@lem45532) (@lem45529 A B x y a b)). Qed.
Lemma lem45540 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term27 A B x a y b) = (term27 A B x a y b).
Proof. exact (eq_refl (term27 A B x a y b)). Qed.
Lemma lem45541 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term28 A B x a y b) = (term29 A B x a y b).
Proof. exact (MK_COMB (@lem45533 A B x y a b) (@lem45540 A B x a y b)). Qed.
Lemma lem45546 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term29 A B x a y b) = (term28 A B x a y b).
Proof. exact (SYM (@lem45541 A B x a y b)). Qed.
Lemma lem45547 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : (term22 A B x y) = (term22 A B a b)) : (term22 A B x y) = (term22 A B a b).
Proof. exact (h1). Qed.
Lemma lem45548 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : (term22 A B x y) = (term22 A B a b)) : (term18 A B x y) = (term18 A B a b).
Proof. exact (MK_COMB (@lem45507 A B) (@lem45547 A B x y a b h1)). Qed.
Lemma lem45556 {A B : Type'} (x : A) (y : B) : (term18 A B x y) = (@mk_pair A B x y).
Proof. exact (EQ_MP (@lem45505 A B x y) (@lem45504 A B x y)). Qed.
Lemma lem45557 {A B : Type'} (x : A) (y : B) : (term18 A B x y) = (@mk_pair A B x y).
Proof. exact (@lem45556 A B x y). Qed.
Lemma lem45558 {A B : Type'} : (@eq (A -> B -> Prop)) = (@eq (A -> B -> Prop)).
Proof. exact (eq_refl (@eq (A -> B -> Prop))). Qed.
Lemma lem45559 {A B : Type'} (x : A) (y : B) : (term30 A B x y) = (term31 A B x y).
Proof. exact (MK_COMB (@lem45558 A B) (@lem45557 A B x y)). Qed.
Lemma lem45561 {A B : Type'} (x : A) (y : B) : (term18 A B x y) = (@mk_pair A B x y).
Proof. exact (EQ_MP (@lem45505 A B x y) (@lem45504 A B x y)). Qed.
Lemma lem45562 {A B : Type'} (x : A) (y : B) : (term18 A B x y) = (@mk_pair A B x y).
Proof. exact (@lem45561 A B x y). Qed.
Lemma lem45563 {A B : Type'} (a : A) (b : B) : (term18 A B a b) = (@mk_pair A B a b).
Proof. exact (@lem45562 A B a b). Qed.
Lemma lem45564 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : ((term18 A B x y) = (term18 A B a b)) = ((@mk_pair A B x y) = (@mk_pair A B a b)).
Proof. exact (MK_COMB (@lem45559 A B x y) (@lem45563 A B a b)). Qed.
Lemma lem45567 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem45568 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term32 A B x y a b) = (term33 A B x y a b).
Proof. exact (MK_COMB (@lem45567) (@lem45564 A B x y a b)). Qed.
Lemma lem45575 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term27 A B x a y b) = (term27 A B x a y b).
Proof. exact (eq_refl (term27 A B x a y b)). Qed.
Lemma lem45576 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term34 A B x a y b) = (term35 A B x a y b).
Proof. exact (MK_COMB (@lem45568 A B x y a b) (@lem45575 A B x a y b)). Qed.
Lemma lem45581 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term35 A B x a y b) = (term34 A B x a y b).
Proof. exact (SYM (@lem45576 A B x a y b)). Qed.
Lemma lem45589 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term10 A B f g).
Proof. exact (EQ_MP (@lem45493 A B f g) (@lem45492 A B f g)). Qed.
Lemma lem45590 {A B : Type'} (f : type1413 A B) (g : type1413 A B) : (f = g) = (term36 A B f g).
Proof. exact (@lem45589 A (B -> Prop) f g). Qed.
Lemma lem45591 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : ((@mk_pair A B x y) = (@mk_pair A B a b)) = (term37 A B x y a b).
Proof. exact (@lem45590 A B (@mk_pair A B x y) (@mk_pair A B a b)). Qed.
Lemma lem45599 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term10 A B f g).
Proof. exact (EQ_MP (@lem45493 A B f g) (@lem45492 A B f g)). Qed.
Lemma lem45600 {B : Type'} (f : B -> Prop) (g : B -> Prop) : (f = g) = (term38 B f g).
Proof. exact (@lem45599 B Prop f g). Qed.
Lemma lem45601 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (x' : A) : ((@mk_pair A B x y x') = (@mk_pair A B a b x')) = (term39 A B x y a b x').
Proof. exact (@lem45600 B (@mk_pair A B x y x') (@mk_pair A B a b x')). Qed.
Lemma lem45611 {A B : Type'} (x : A) (y : B) : (@mk_pair A B x y) = (term14 A B x y).
Proof. exact (EQ_MP (@lem45499 A B x y) (@lem45498 A B x y)). Qed.
Lemma lem45612 {A B : Type'} (x : A) (y : B) : (@mk_pair A B x y) = (term14 A B x y).
Proof. exact (@lem45611 A B x y). Qed.
Lemma lem45623 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem45624 {A B : Type'} (x : A) (y : B) (x' : A) : (@mk_pair A B x y x') = (term40 A B x y x').
Proof. exact (MK_COMB (@lem45612 A B x y) (@lem45623 A x')). Qed.
Lemma lem45626 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem45627 {A B : Type'} (f : type1413 A B) (y : A) : (term42 A B f y) = (f y).
Proof. exact (@lem45626 A (B -> Prop) f y). Qed.
Lemma lem45628 {A B : Type'} (x : A) (y : B) (x' : A) : (term43 A B x y x') = (term40 A B x y x').
Proof. exact (@lem45627 A B (term14 A B x y) x'). Qed.
Lemma lem45629 {A B : Type'} (a : A) (x : A) (y : B) : (term40 A B x y a) = (term44 A B a x y).
Proof. exact (eq_refl (term40 A B x y a)). Qed.
Lemma lem45630 {A B : Type'} (x : A) (y : B) : (term45 A B x y) = (term14 A B x y).
Proof. exact (fun_ext (fun a : A => @lem45629 A B a x y)). Qed.
Lemma lem45631 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem45632 {A B : Type'} (x : A) (y : B) (x' : A) : (term43 A B x y x') = (term40 A B x y x').
Proof. exact (MK_COMB (@lem45630 A B x y) (@lem45631 A x')). Qed.
Lemma lem45633 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem45634 {A B : Type'} (x : A) (y : B) (x' : A) : (term46 A B x y x') = (term47 A B x y x').
Proof. exact (MK_COMB (@lem45633 B) (@lem45632 A B x y x')). Qed.
Lemma lem45635 {A B : Type'} (x' : A) (x : A) (y : B) : (term40 A B x y x') = (term44 A B x' x y).
Proof. exact (eq_refl (term40 A B x y x')). Qed.
Lemma lem45636 {A B : Type'} (x' : A) (x : A) (y : B) : ((term43 A B x y x') = (term40 A B x y x')) = ((term40 A B x y x') = (term44 A B x' x y)).
Proof. exact (MK_COMB (@lem45634 A B x y x') (@lem45635 A B x' x y)). Qed.
Lemma lem45637 {A B : Type'} (x' : A) (x : A) (y : B) : (term40 A B x y x') = (term44 A B x' x y).
Proof. exact (EQ_MP (@lem45636 A B x' x y) (@lem45628 A B x y x')). Qed.
Lemma lem45648 {A B : Type'} (x' : A) (x : A) (y : B) : (@mk_pair A B x y x') = (term44 A B x' x y).
Proof. exact (TRANS (@lem45624 A B x y x') (@lem45637 A B x' x y)). Qed.
Lemma lem45649 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem45650 {A B : Type'} (x' : A) (x : A) (y : B) (x'' : B) : (@mk_pair A B x y x' x'') = (term48 A B x' x y x'').
Proof. exact (MK_COMB (@lem45648 A B x' x y) (@lem45649 B x'')). Qed.
Lemma lem45652 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem45653 {B : Type'} (f : B -> Prop) (y : B) : (term49 B f y) = (f y).
Proof. exact (@lem45652 B Prop f y). Qed.
Lemma lem45654 {A B : Type'} (x' : A) (x : A) (y : B) (x'' : B) : (term50 A B x' x y x'') = (term48 A B x' x y x'').
Proof. exact (@lem45653 B (term44 A B x' x y) x''). Qed.
Lemma lem45655 {A B : Type'} (x' : A) (x : A) (b : B) (y : B) : (term48 A B x' x y b) = (term27 A B x' x b y).
Proof. exact (eq_refl (term48 A B x' x y b)). Qed.
Lemma lem45656 {A B : Type'} (x' : A) (x : A) (y : B) : (term51 A B x' x y) = (term44 A B x' x y).
Proof. exact (fun_ext (fun b : B => @lem45655 A B x' x b y)). Qed.
Lemma lem45657 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem45658 {A B : Type'} (x' : A) (x : A) (y : B) (x'' : B) : (term50 A B x' x y x'') = (term48 A B x' x y x'').
Proof. exact (MK_COMB (@lem45656 A B x' x y) (@lem45657 B x'')). Qed.
Lemma lem45659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem45660 {A B : Type'} (x' : A) (x : A) (y : B) (x'' : B) : (term52 A B x' x y x'') = (term53 A B x' x y x'').
Proof. exact (MK_COMB (@lem45659) (@lem45658 A B x' x y x'')). Qed.
Lemma lem45661 {A B : Type'} (x' : A) (x : A) (x'' : B) (y : B) : (term48 A B x' x y x'') = (term27 A B x' x x'' y).
Proof. exact (eq_refl (term48 A B x' x y x'')). Qed.
Lemma lem45662 {A B : Type'} (x' : A) (x : A) (x'' : B) (y : B) : ((term50 A B x' x y x'') = (term48 A B x' x y x'')) = ((term48 A B x' x y x'') = (term27 A B x' x x'' y)).
Proof. exact (MK_COMB (@lem45660 A B x' x y x'') (@lem45661 A B x' x x'' y)). Qed.
Lemma lem45663 {A B : Type'} (x' : A) (x : A) (x'' : B) (y : B) : (term48 A B x' x y x'') = (term27 A B x' x x'' y).
Proof. exact (EQ_MP (@lem45662 A B x' x x'' y) (@lem45654 A B x' x y x'')). Qed.
Lemma lem45674 {A B : Type'} (x' : A) (x : A) (x'' : B) (y : B) : (@mk_pair A B x y x' x'') = (term27 A B x' x x'' y).
Proof. exact (TRANS (@lem45650 A B x' x y x'') (@lem45663 A B x' x x'' y)). Qed.
Lemma lem45675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem45676 {A B : Type'} (x' : A) (x : A) (x'' : B) (y : B) : (term54 A B x y x' x'') = (term55 A B x' x x'' y).
Proof. exact (MK_COMB (@lem45675) (@lem45674 A B x' x x'' y)). Qed.
Lemma lem45678 {A B : Type'} (x : A) (y : B) : (@mk_pair A B x y) = (term14 A B x y).
Proof. exact (EQ_MP (@lem45499 A B x y) (@lem45498 A B x y)). Qed.
Lemma lem45679 {A B : Type'} (x : A) (y : B) : (@mk_pair A B x y) = (term14 A B x y).
Proof. exact (@lem45678 A B x y). Qed.
Lemma lem45680 {A B : Type'} (a : A) (b : B) : (@mk_pair A B a b) = (term14 A B a b).
Proof. exact (@lem45679 A B a b). Qed.
Lemma lem45691 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem45692 {A B : Type'} (a : A) (b : B) (x' : A) : (@mk_pair A B a b x') = (term40 A B a b x').
Proof. exact (MK_COMB (@lem45680 A B a b) (@lem45691 A x')). Qed.
Lemma lem45694 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem45695 {A B : Type'} (f : type1413 A B) (y : A) : (term42 A B f y) = (f y).
Proof. exact (@lem45694 A (B -> Prop) f y). Qed.
Lemma lem45696 {A B : Type'} (a : A) (b : B) (x' : A) : (term43 A B a b x') = (term40 A B a b x').
Proof. exact (@lem45695 A B (term14 A B a b) x'). Qed.
Lemma lem45697 {A B : Type'} (a' : A) (a : A) (b : B) : (term40 A B a b a') = (term44 A B a' a b).
Proof. exact (eq_refl (term40 A B a b a')). Qed.
Lemma lem45698 {A B : Type'} (a : A) (b : B) : (term45 A B a b) = (term14 A B a b).
Proof. exact (fun_ext (fun a' : A => @lem45697 A B a' a b)). Qed.
Lemma lem45699 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem45700 {A B : Type'} (a : A) (b : B) (x' : A) : (term43 A B a b x') = (term40 A B a b x').
Proof. exact (MK_COMB (@lem45698 A B a b) (@lem45699 A x')). Qed.
Lemma lem45701 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem45702 {A B : Type'} (a : A) (b : B) (x' : A) : (term46 A B a b x') = (term47 A B a b x').
Proof. exact (MK_COMB (@lem45701 B) (@lem45700 A B a b x')). Qed.
Lemma lem45703 {A B : Type'} (x' : A) (a : A) (b : B) : (term40 A B a b x') = (term44 A B x' a b).
Proof. exact (eq_refl (term40 A B a b x')). Qed.
Lemma lem45704 {A B : Type'} (x' : A) (a : A) (b : B) : ((term43 A B a b x') = (term40 A B a b x')) = ((term40 A B a b x') = (term44 A B x' a b)).
Proof. exact (MK_COMB (@lem45702 A B a b x') (@lem45703 A B x' a b)). Qed.
Lemma lem45705 {A B : Type'} (x' : A) (a : A) (b : B) : (term40 A B a b x') = (term44 A B x' a b).
Proof. exact (EQ_MP (@lem45704 A B x' a b) (@lem45696 A B a b x')). Qed.
Lemma lem45716 {A B : Type'} (x' : A) (a : A) (b : B) : (@mk_pair A B a b x') = (term44 A B x' a b).
Proof. exact (TRANS (@lem45692 A B a b x') (@lem45705 A B x' a b)). Qed.
Lemma lem45717 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem45718 {A B : Type'} (x' : A) (a : A) (b : B) (x : B) : (@mk_pair A B a b x' x) = (term48 A B x' a b x).
Proof. exact (MK_COMB (@lem45716 A B x' a b) (@lem45717 B x)). Qed.
Lemma lem45720 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem45721 {B : Type'} (f : B -> Prop) (y : B) : (term49 B f y) = (f y).
Proof. exact (@lem45720 B Prop f y). Qed.
Lemma lem45722 {A B : Type'} (x' : A) (a : A) (b : B) (x : B) : (term50 A B x' a b x) = (term48 A B x' a b x).
Proof. exact (@lem45721 B (term44 A B x' a b) x). Qed.
Lemma lem45723 {A B : Type'} (x' : A) (a : A) (b' : B) (b : B) : (term48 A B x' a b b') = (term27 A B x' a b' b).
Proof. exact (eq_refl (term48 A B x' a b b')). Qed.
Lemma lem45724 {A B : Type'} (x' : A) (a : A) (b : B) : (term51 A B x' a b) = (term44 A B x' a b).
Proof. exact (fun_ext (fun b' : B => @lem45723 A B x' a b' b)). Qed.
Lemma lem45725 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem45726 {A B : Type'} (x' : A) (a : A) (b : B) (x : B) : (term50 A B x' a b x) = (term48 A B x' a b x).
Proof. exact (MK_COMB (@lem45724 A B x' a b) (@lem45725 B x)). Qed.
Lemma lem45727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem45728 {A B : Type'} (x' : A) (a : A) (b : B) (x : B) : (term52 A B x' a b x) = (term53 A B x' a b x).
Proof. exact (MK_COMB (@lem45727) (@lem45726 A B x' a b x)). Qed.
Lemma lem45729 {A B : Type'} (x' : A) (a : A) (x : B) (b : B) : (term48 A B x' a b x) = (term27 A B x' a x b).
Proof. exact (eq_refl (term48 A B x' a b x)). Qed.
Lemma lem45730 {A B : Type'} (x' : A) (a : A) (x : B) (b : B) : ((term50 A B x' a b x) = (term48 A B x' a b x)) = ((term48 A B x' a b x) = (term27 A B x' a x b)).
Proof. exact (MK_COMB (@lem45728 A B x' a b x) (@lem45729 A B x' a x b)). Qed.
Lemma lem45731 {A B : Type'} (x' : A) (a : A) (x : B) (b : B) : (term48 A B x' a b x) = (term27 A B x' a x b).
Proof. exact (EQ_MP (@lem45730 A B x' a x b) (@lem45722 A B x' a b x)). Qed.
Lemma lem45742 {A B : Type'} (x' : A) (a : A) (x : B) (b : B) : (@mk_pair A B a b x' x) = (term27 A B x' a x b).
Proof. exact (TRANS (@lem45718 A B x' a b x) (@lem45731 A B x' a x b)). Qed.
Lemma lem45743 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : ((@mk_pair A B x y x' x'') = (@mk_pair A B a b x' x'')) = ((term27 A B x' x x'' y) = (term27 A B x' a x'' b)).
Proof. exact (MK_COMB (@lem45676 A B x' x x'' y) (@lem45742 A B x' a x'' b)). Qed.
Lemma lem45748 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term56 A B x y a b x') = (term57 A B x y x' a b).
Proof. exact (fun_ext (fun x'' : B => @lem45743 A B x y x' a x'' b)). Qed.
Lemma lem45749 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem45750 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term39 A B x y a b x') = (term58 A B x y x' a b).
Proof. exact (MK_COMB (@lem45749 B) (@lem45748 A B x y x' a b)). Qed.
Lemma lem45755 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : ((@mk_pair A B x y x') = (@mk_pair A B a b x')) = (term58 A B x y x' a b).
Proof. exact (TRANS (@lem45601 A B x y a b x') (@lem45750 A B x y x' a b)). Qed.
Lemma lem45756 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term59 A B x y a b) = (term60 A B x y a b).
Proof. exact (fun_ext (fun x' : A => @lem45755 A B x y x' a b)). Qed.
Lemma lem45757 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45758 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term37 A B x y a b) = (term61 A B x y a b).
Proof. exact (MK_COMB (@lem45757 A) (@lem45756 A B x y a b)). Qed.
Lemma lem45763 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : ((@mk_pair A B x y) = (@mk_pair A B a b)) = (term61 A B x y a b).
Proof. exact (TRANS (@lem45591 A B x y a b) (@lem45758 A B x y a b)). Qed.
Lemma lem45764 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem45765 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term33 A B x y a b) = (term62 A B x y a b).
Proof. exact (MK_COMB (@lem45764) (@lem45763 A B x y a b)). Qed.
Lemma lem45776 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term27 A B x a y b) = (term27 A B x a y b).
Proof. exact (eq_refl (term27 A B x a y b)). Qed.
Lemma lem45777 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term35 A B x a y b) = (term63 A B x a y b).
Proof. exact (MK_COMB (@lem45765 A B x y a b) (@lem45776 A B x a y b)). Qed.
Lemma lem45780 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term63 A B x a y b) = (term35 A B x a y b).
Proof. exact (SYM (@lem45777 A B x a y b)). Qed.
Lemma lem45782 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem45783 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term63 A B x a y b) = (term65 A B x a y b).
Proof. exact (@lem45782 (term63 A B x a y b)). Qed.
Lemma lem45784 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term65 A B x a y b) = (term63 A B x a y b).
Proof. exact (SYM (@lem45783 A B x a y b)). Qed.
Lemma lem45785 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term66 A B x a y b) : term66 A B x a y b.
Proof. exact (h1). Qed.
Lemma lem45788 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term65 A B x a y b) : term65 A B x a y b.
Proof. exact (h1). Qed.
Lemma lem45789 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term67 A B x a y b.
Proof. exact (fun h0 : term65 A B x a y b => @lem45788 A B x a y b h0). Qed.
Lemma lem45790 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term67 A B x a y b) : term67 A B x a y b.
Proof. exact (h1). Qed.
Lemma lem45791 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term65 A B x a y b) : term65 A B x a y b.
Proof. exact (h1). Qed.
Lemma lem45792 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term65 A B x a y b) (h2 : term67 A B x a y b) : term65 A B x a y b.
Proof. exact (@lem45790 A B x a y b h2 (@lem45791 A B x a y b h1)). Qed.
Lemma lem45793 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term65 A B x a y b) : term68 A B x a y b.
Proof. exact (fun h0 : term67 A B x a y b => @lem45792 A B x a y b h1 h0). Qed.
Lemma lem45794 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term67 A B x a y b) : term67 A B x a y b.
Proof. exact (h1). Qed.
Lemma lem45795 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term65 A B x a y b) (h2 : term67 A B x a y b) : term65 A B x a y b.
Proof. exact (@lem45793 A B x a y b h1 (@lem45794 A B x a y b h2)). Qed.
Lemma lem45796 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term67 A B x a y b) : term67 A B x a y b.
Proof. exact (fun h0 : term65 A B x a y b => @lem45795 A B x a y b h0 h1). Qed.
Lemma lem45797 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term69 A B x a y b.
Proof. exact (fun h0 : term67 A B x a y b => @lem45796 A B x a y b h0). Qed.
Lemma lem45800 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term67 A B x a y b.
Proof. exact (@lem45797 A B x a y b (@lem45789 A B x a y b)). Qed.
Lemma lem45801 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term67 A B x a y b.
Proof. exact (@lem45800 A B x a y b). Qed.
Lemma lem45819 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem45820 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term65 A B x a y b) = (term70 A B x a y b).
Proof. exact (@lem45819 (term66 A B x a y b)). Qed.
Lemma lem45822 (t : Prop) : (term71 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem45823 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term70 A B x a y b) = (term63 A B x a y b).
Proof. exact (@lem45822 (term63 A B x a y b)). Qed.
Lemma lem45826 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term65 A B x a y b) = (term63 A B x a y b).
Proof. exact (TRANS (@lem45820 A B x a y b) (@lem45823 A B x a y b)). Qed.
Lemma lem45841 {A B : Type'} (a : A) (y : B) (b : B) : (term72 A B a y b) = (term73 A B a y b).
Proof. exact (fun_ext (fun x : A => @lem45826 A B x a y b)). Qed.
Lemma lem45842 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45843 {A B : Type'} (a : A) (y : B) (b : B) : (term74 A B a y b) = (term75 A B a y b).
Proof. exact (MK_COMB (@lem45842 A) (@lem45841 A B a y b)). Qed.
Lemma lem45848 {A B : Type'} (y : B) (b : B) : (term76 A B y b) = (term77 A B y b).
Proof. exact (fun_ext (fun a : A => @lem45843 A B a y b)). Qed.
Lemma lem45849 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45850 {A B : Type'} (y : B) (b : B) : (term78 A B y b) = (term79 A B y b).
Proof. exact (MK_COMB (@lem45849 A) (@lem45848 A B y b)). Qed.
Lemma lem45855 {A B : Type'} (b : B) : (term80 A B b) = (term81 A B b).
Proof. exact (fun_ext (fun y : B => @lem45850 A B y b)). Qed.
Lemma lem45856 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem45857 {A B : Type'} (b : B) : (term82 A B b) = (term83 A B b).
Proof. exact (MK_COMB (@lem45856 B) (@lem45855 A B b)). Qed.
Lemma lem45862 {A B : Type'} : (term84 A B) = (term85 A B).
Proof. exact (fun_ext (fun b : B => @lem45857 A B b)). Qed.
Lemma lem45863 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem45872 {A B : Type'} : (term86 A B) = (term87 A B).
Proof. exact (MK_COMB (@lem45863 B) (@lem45862 A B)). Qed.
Lemma lem45877 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term27 A B x a y b) = (term27 A B x a y b).
Proof. exact (eq_refl (term27 A B x a y b)). Qed.
Lemma lem45890 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : ((term27 A B x' x x'' y) = (term27 A B x' a x'' b)) = ((term27 A B x' x x'' y) = (term27 A B x' a x'' b)).
Proof. exact (eq_refl ((term27 A B x' x x'' y) = (term27 A B x' a x'' b))). Qed.
Lemma lem45891 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term57 A B x y x' a b) = (term57 A B x y x' a b).
Proof. exact (fun_ext (fun x'' : B => @lem45890 A B x y x' a x'' b)). Qed.
Lemma lem45892 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem45893 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term58 A B x y x' a b) = (term58 A B x y x' a b).
Proof. exact (MK_COMB (@lem45892 B) (@lem45891 A B x y x' a b)). Qed.
Lemma lem45894 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term60 A B x y a b) = (term60 A B x y a b).
Proof. exact (fun_ext (fun x' : A => @lem45893 A B x y x' a b)). Qed.
Lemma lem45895 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45896 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term61 A B x y a b) = (term61 A B x y a b).
Proof. exact (MK_COMB (@lem45895 A) (@lem45894 A B x y a b)). Qed.
Lemma lem45897 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem45898 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term62 A B x y a b) = (term62 A B x y a b).
Proof. exact (MK_COMB (@lem45897) (@lem45896 A B x y a b)). Qed.
Lemma lem45899 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term63 A B x a y b) = (term63 A B x a y b).
Proof. exact (MK_COMB (@lem45898 A B x y a b) (@lem45877 A B x a y b)). Qed.
Lemma lem45900 {A B : Type'} (a : A) (y : B) (b : B) : (term73 A B a y b) = (term73 A B a y b).
Proof. exact (fun_ext (fun x : A => @lem45899 A B x a y b)). Qed.
Lemma lem45901 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45902 {A B : Type'} (a : A) (y : B) (b : B) : (term75 A B a y b) = (term75 A B a y b).
Proof. exact (MK_COMB (@lem45901 A) (@lem45900 A B a y b)). Qed.
Lemma lem45903 {A B : Type'} (y : B) (b : B) : (term77 A B y b) = (term77 A B y b).
Proof. exact (fun_ext (fun a : A => @lem45902 A B a y b)). Qed.
Lemma lem45904 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45905 {A B : Type'} (y : B) (b : B) : (term79 A B y b) = (term79 A B y b).
Proof. exact (MK_COMB (@lem45904 A) (@lem45903 A B y b)). Qed.
Lemma lem45906 {A B : Type'} (b : B) : (term81 A B b) = (term81 A B b).
Proof. exact (fun_ext (fun y : B => @lem45905 A B y b)). Qed.
Lemma lem45907 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem45908 {A B : Type'} (b : B) : (term83 A B b) = (term83 A B b).
Proof. exact (MK_COMB (@lem45907 B) (@lem45906 A B b)). Qed.
Lemma lem45909 {A B : Type'} : (term85 A B) = (term85 A B).
Proof. exact (fun_ext (fun b : B => @lem45908 A B b)). Qed.
Lemma lem45910 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem45911 {A B : Type'} : (term87 A B) = (term87 A B).
Proof. exact (MK_COMB (@lem45910 B) (@lem45909 A B)). Qed.
Lemma lem45958 {A B : Type'} : (term86 A B) = (term87 A B).
Proof. exact (TRANS (@lem45872 A B) (@lem45911 A B)). Qed.
Lemma lem45959 {A B : Type'} : (term87 A B) = (term86 A B).
Proof. exact (SYM (@lem45958 A B)). Qed.
Lemma lem45960 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term61 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem45962 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem45963 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term27 A B x a y b) = (term88 A B x a y b).
Proof. exact (@lem45962 (term27 A B x a y b)). Qed.
Lemma lem45964 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term88 A B x a y b) = (term27 A B x a y b).
Proof. exact (SYM (@lem45963 A B x a y b)). Qed.
Lemma lem45965 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term89 A B x a y b) : term89 A B x a y b.
Proof. exact (h1). Qed.
Lemma lem45974 {A B : Type'} (x' : A) (x : A) (x'' : B) (y : B) : (term89 A B x' x x'' y) = (term90 A B x' x x'' y).
Proof. exact (@lem17045 (x' = x) (x'' = y)). Qed.
Lemma lem45986 {A B : Type'} (x' : A) (a : A) (x : B) (b : B) : (term89 A B x' a x b) = (term90 A B x' a x b).
Proof. exact (@lem17045 (x' = a) (x = b)). Qed.
Lemma lem45989 {A B : Type'} (x' : A) (a : A) (x : B) (b : B) : (term27 A B x' a x b) = (term27 A B x' a x b).
Proof. exact (eq_refl (term27 A B x' a x b)). Qed.
Lemma lem45990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem45991 {A B : Type'} (x' : A) (x : A) (x'' : B) (y : B) : (term91 A B x' x x'' y) = (term92 A B x' x x'' y).
Proof. exact (MK_COMB (@lem45990) (@lem45974 A B x' x x'' y)). Qed.
Lemma lem45992 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term93 A B x y x' a x'' b) = (term94 A B x y x' a x'' b).
Proof. exact (MK_COMB (@lem45991 A B x' x x'' y) (@lem45989 A B x' a x'' b)). Qed.
Lemma lem45994 {A B : Type'} (x' : A) (x : A) (x'' : B) (y : B) : (term95 A B x' x x'' y) = (term95 A B x' x x'' y).
Proof. exact (eq_refl (term95 A B x' x x'' y)). Qed.
Lemma lem45995 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term96 A B x y x' a x'' b) = (term97 A B x y x' a x'' b).
Proof. exact (MK_COMB (@lem45994 A B x' x x'' y) (@lem45986 A B x' a x'' b)). Qed.
Lemma lem45996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem45997 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term98 A B x y x' a x'' b) = (term99 A B x y x' a x'' b).
Proof. exact (MK_COMB (@lem45996) (@lem45995 A B x y x' a x'' b)). Qed.
Lemma lem45998 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term100 A B x y x' a x'' b) = (term101 A B x y x' a x'' b).
Proof. exact (MK_COMB (@lem45997 A B x y x' a x'' b) (@lem45992 A B x y x' a x'' b)). Qed.
Lemma lem45999 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : ((term27 A B x' x x'' y) = (term27 A B x' a x'' b)) = (term100 A B x y x' a x'' b).
Proof. exact (@lem17784 (term27 A B x' x x'' y) (term27 A B x' a x'' b)). Qed.
Lemma lem46000 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : ((term27 A B x' x x'' y) = (term27 A B x' a x'' b)) = (term101 A B x y x' a x'' b).
Proof. exact (TRANS (@lem45999 A B x y x' a x'' b) (@lem45998 A B x y x' a x'' b)). Qed.
Lemma lem46001 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term57 A B x y x' a b) = (term102 A B x y x' a b).
Proof. exact (fun_ext (fun x'' : B => @lem46000 A B x y x' a x'' b)). Qed.
Lemma lem46002 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem46003 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term58 A B x y x' a b) = (term103 A B x y x' a b).
Proof. exact (MK_COMB (@lem46002 B) (@lem46001 A B x y x' a b)). Qed.
Lemma lem46004 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term60 A B x y a b) = (term104 A B x y a b).
Proof. exact (fun_ext (fun x' : A => @lem46003 A B x y x' a b)). Qed.
Lemma lem46005 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem46006 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term61 A B x y a b) = (term105 A B x y a b).
Proof. exact (MK_COMB (@lem46005 A) (@lem46004 A B x y a b)). Qed.
Lemma lem46012 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem46013 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term106 B P Q) = (term107 B P Q).
Proof. exact (@lem46012 B P Q). Qed.
Lemma lem46014 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term108 A B x y x' a b) = (term109 A B x y x' a b).
Proof. exact (@lem46013 B (term110 A B x y x' a b) (term111 A B x y x' a b)). Qed.
Lemma lem46015 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term112 A B x y x' a b x'') = (term97 A B x y x' a x'' b).
Proof. exact (eq_refl (term112 A B x y x' a b x'')). Qed.
Lemma lem46016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem46017 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term113 A B x y x' a b x'') = (term99 A B x y x' a x'' b).
Proof. exact (MK_COMB (@lem46016) (@lem46015 A B x y x' a x'' b)). Qed.
Lemma lem46018 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term114 A B x y x' a b x'') = (term94 A B x y x' a x'' b).
Proof. exact (eq_refl (term114 A B x y x' a b x'')). Qed.
Lemma lem46019 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term115 A B x y x' a b x'') = (term101 A B x y x' a x'' b).
Proof. exact (MK_COMB (@lem46017 A B x y x' a x'' b) (@lem46018 A B x y x' a x'' b)). Qed.
Lemma lem46020 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term116 A B x y x' a b) = (term102 A B x y x' a b).
Proof. exact (fun_ext (fun x'' : B => @lem46019 A B x y x' a x'' b)). Qed.
Lemma lem46021 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem46022 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term108 A B x y x' a b) = (term103 A B x y x' a b).
Proof. exact (MK_COMB (@lem46021 B) (@lem46020 A B x y x' a b)). Qed.
Lemma lem46023 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem46024 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term117 A B x y x' a b) = (term118 A B x y x' a b).
Proof. exact (MK_COMB (@lem46023) (@lem46022 A B x y x' a b)). Qed.
Lemma lem46025 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term112 A B x y x' a b x'') = (term97 A B x y x' a x'' b).
Proof. exact (eq_refl (term112 A B x y x' a b x'')). Qed.
Lemma lem46026 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term119 A B x y x' a b) = (term110 A B x y x' a b).
Proof. exact (fun_ext (fun x'' : B => @lem46025 A B x y x' a x'' b)). Qed.
Lemma lem46027 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem46028 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term120 A B x y x' a b) = (term121 A B x y x' a b).
Proof. exact (MK_COMB (@lem46027 B) (@lem46026 A B x y x' a b)). Qed.
Lemma lem46029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem46030 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term122 A B x y x' a b) = (term123 A B x y x' a b).
Proof. exact (MK_COMB (@lem46029) (@lem46028 A B x y x' a b)). Qed.
Lemma lem46031 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term114 A B x y x' a b x'') = (term94 A B x y x' a x'' b).
Proof. exact (eq_refl (term114 A B x y x' a b x'')). Qed.
Lemma lem46032 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term124 A B x y x' a b) = (term111 A B x y x' a b).
Proof. exact (fun_ext (fun x'' : B => @lem46031 A B x y x' a x'' b)). Qed.
Lemma lem46033 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem46034 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term125 A B x y x' a b) = (term126 A B x y x' a b).
Proof. exact (MK_COMB (@lem46033 B) (@lem46032 A B x y x' a b)). Qed.
Lemma lem46035 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term109 A B x y x' a b) = (term127 A B x y x' a b).
Proof. exact (MK_COMB (@lem46030 A B x y x' a b) (@lem46034 A B x y x' a b)). Qed.
Lemma lem46036 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : ((term108 A B x y x' a b) = (term109 A B x y x' a b)) = ((term103 A B x y x' a b) = (term127 A B x y x' a b)).
Proof. exact (MK_COMB (@lem46024 A B x y x' a b) (@lem46035 A B x y x' a b)). Qed.
Lemma lem46037 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term103 A B x y x' a b) = (term127 A B x y x' a b).
Proof. exact (EQ_MP (@lem46036 A B x y x' a b) (@lem46014 A B x y x' a b)). Qed.
Lemma lem46134 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term104 A B x y a b) = (term128 A B x y a b).
Proof. exact (fun_ext (fun x' : A => @lem46037 A B x y x' a b)). Qed.
Lemma lem46135 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem46136 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term105 A B x y a b) = (term129 A B x y a b).
Proof. exact (MK_COMB (@lem46135 A) (@lem46134 A B x y a b)). Qed.
Lemma lem46138 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem46139 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (@lem46138 A P Q). Qed.
Lemma lem46140 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term130 A B x y a b) = (term131 A B x y a b).
Proof. exact (@lem46139 A (term132 A B x y a b) (term133 A B x y a b)). Qed.
Lemma lem46141 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term134 A B x y a b x') = (term121 A B x y x' a b).
Proof. exact (eq_refl (term134 A B x y a b x')). Qed.
Lemma lem46142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem46143 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term135 A B x y a b x') = (term123 A B x y x' a b).
Proof. exact (MK_COMB (@lem46142) (@lem46141 A B x y x' a b)). Qed.
Lemma lem46144 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term136 A B x y a b x') = (term126 A B x y x' a b).
Proof. exact (eq_refl (term136 A B x y a b x')). Qed.
Lemma lem46145 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term137 A B x y a b x') = (term127 A B x y x' a b).
Proof. exact (MK_COMB (@lem46143 A B x y x' a b) (@lem46144 A B x y x' a b)). Qed.
Lemma lem46146 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term138 A B x y a b) = (term128 A B x y a b).
Proof. exact (fun_ext (fun x' : A => @lem46145 A B x y x' a b)). Qed.
Lemma lem46147 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem46148 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term130 A B x y a b) = (term129 A B x y a b).
Proof. exact (MK_COMB (@lem46147 A) (@lem46146 A B x y a b)). Qed.
Lemma lem46149 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem46150 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term139 A B x y a b) = (term140 A B x y a b).
Proof. exact (MK_COMB (@lem46149) (@lem46148 A B x y a b)). Qed.
Lemma lem46151 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term134 A B x y a b x') = (term121 A B x y x' a b).
Proof. exact (eq_refl (term134 A B x y a b x')). Qed.
Lemma lem46152 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term141 A B x y a b) = (term132 A B x y a b).
Proof. exact (fun_ext (fun x' : A => @lem46151 A B x y x' a b)). Qed.
Lemma lem46153 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem46154 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term142 A B x y a b) = (term143 A B x y a b).
Proof. exact (MK_COMB (@lem46153 A) (@lem46152 A B x y a b)). Qed.
Lemma lem46155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem46156 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term144 A B x y a b) = (term145 A B x y a b).
Proof. exact (MK_COMB (@lem46155) (@lem46154 A B x y a b)). Qed.
Lemma lem46157 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term136 A B x y a b x') = (term126 A B x y x' a b).
Proof. exact (eq_refl (term136 A B x y a b x')). Qed.
Lemma lem46158 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term146 A B x y a b) = (term133 A B x y a b).
Proof. exact (fun_ext (fun x' : A => @lem46157 A B x y x' a b)). Qed.
Lemma lem46159 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem46160 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term147 A B x y a b) = (term148 A B x y a b).
Proof. exact (MK_COMB (@lem46159 A) (@lem46158 A B x y a b)). Qed.
Lemma lem46161 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term131 A B x y a b) = (term149 A B x y a b).
Proof. exact (MK_COMB (@lem46156 A B x y a b) (@lem46160 A B x y a b)). Qed.
Lemma lem46162 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : ((term130 A B x y a b) = (term131 A B x y a b)) = ((term129 A B x y a b) = (term149 A B x y a b)).
Proof. exact (MK_COMB (@lem46150 A B x y a b) (@lem46161 A B x y a b)). Qed.
Lemma lem46163 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term129 A B x y a b) = (term149 A B x y a b).
Proof. exact (EQ_MP (@lem46162 A B x y a b) (@lem46140 A B x y a b)). Qed.
Lemma lem46270 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term105 A B x y a b) = (term149 A B x y a b).
Proof. exact (TRANS (@lem46136 A B x y a b) (@lem46163 A B x y a b)). Qed.
Lemma lem46271 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term61 A B x y a b) = (term149 A B x y a b).
Proof. exact (TRANS (@lem46006 A B x y a b) (@lem46270 A B x y a b)). Qed.
Lemma lem46272 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term149 A B x y a b.
Proof. exact (EQ_MP (@lem46271 A B x y a b) (@lem45960 A B x y a b h1)). Qed.
Lemma lem46283 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term89 A B x a y b) = (term90 A B x a y b).
Proof. exact (@lem17045 (x = a) (y = b)). Qed.
Lemma lem46317 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term94 A B x y x' a x'' b) = (term94 A B x y x' a x'' b).
Proof. exact (eq_refl (term94 A B x y x' a x'' b)). Qed.
Lemma lem46318 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term111 A B x y x' a b) = (term111 A B x y x' a b).
Proof. exact (fun_ext (fun x'' : B => @lem46317 A B x y x' a x'' b)). Qed.
Lemma lem46319 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem46320 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term126 A B x y x' a b) = (term126 A B x y x' a b).
Proof. exact (MK_COMB (@lem46319 B) (@lem46318 A B x y x' a b)). Qed.
Lemma lem46321 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term133 A B x y a b) = (term133 A B x y a b).
Proof. exact (fun_ext (fun x' : A => @lem46320 A B x y x' a b)). Qed.
Lemma lem46322 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem46323 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term148 A B x y a b) = (term148 A B x y a b).
Proof. exact (MK_COMB (@lem46322 A) (@lem46321 A B x y a b)). Qed.
Lemma lem46356 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (x'' : B) (b : B) : (term97 A B x y x' a x'' b) = (term97 A B x y x' a x'' b).
Proof. exact (eq_refl (term97 A B x y x' a x'' b)). Qed.
Lemma lem46357 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term110 A B x y x' a b) = (term110 A B x y x' a b).
Proof. exact (fun_ext (fun x'' : B => @lem46356 A B x y x' a x'' b)). Qed.
Lemma lem46358 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem46359 {A B : Type'} (x : A) (y : B) (x' : A) (a : A) (b : B) : (term121 A B x y x' a b) = (term121 A B x y x' a b).
Proof. exact (MK_COMB (@lem46358 B) (@lem46357 A B x y x' a b)). Qed.
Lemma lem46360 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term132 A B x y a b) = (term132 A B x y a b).
Proof. exact (fun_ext (fun x' : A => @lem46359 A B x y x' a b)). Qed.
Lemma lem46361 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem46362 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term143 A B x y a b) = (term143 A B x y a b).
Proof. exact (MK_COMB (@lem46361 A) (@lem46360 A B x y a b)). Qed.
Lemma lem46363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem46364 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term145 A B x y a b) = (term145 A B x y a b).
Proof. exact (MK_COMB (@lem46363) (@lem46362 A B x y a b)). Qed.
Lemma lem46365 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term149 A B x y a b) = (term149 A B x y a b).
Proof. exact (MK_COMB (@lem46364 A B x y a b) (@lem46323 A B x y a b)). Qed.
Lemma lem46366 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term149 A B x y a b.
Proof. exact (EQ_MP (@lem46365 A B x y a b) (@lem46272 A B x y a b h1)). Qed.
Lemma lem46384 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term89 A B x a y b) : term90 A B x a y b.
Proof. exact (EQ_MP (@lem46283 A B x a y b) (@lem45965 A B x a y b h1)). Qed.
Lemma lem46385 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term148 A B x y a b.
Proof. exact (proj2 (@lem46366 A B x y a b h1)). Qed.
Lemma lem46444 {A B : Type'} (a : A) (x' : A) (x : A) (y : B) (x'' : B) (b : B) : (term94 A B x y x' a x'' b) = (term150 A B a x' x y x'' b).
Proof. exact (@lem19490 (x' = a) (term90 A B x' x x'' y) (x'' = b)). Qed.
Lemma lem46445 {A B : Type'} (a : A) (x' : A) (x : A) (y : B) (b : B) : (term111 A B x y x' a b) = (term151 A B a x' x y b).
Proof. exact (fun_ext (fun x'' : B => @lem46444 A B a x' x y x'' b)). Qed.
Lemma lem46446 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem46447 {A B : Type'} (a : A) (x' : A) (x : A) (y : B) (b : B) : (term126 A B x y x' a b) = (term152 A B a x' x y b).
Proof. exact (MK_COMB (@lem46446 B) (@lem46445 A B a x' x y b)). Qed.
Lemma lem46448 {A B : Type'} (a : A) (x : A) (y : B) (b : B) : (term133 A B x y a b) = (term153 A B a x y b).
Proof. exact (fun_ext (fun x' : A => @lem46447 A B a x' x y b)). Qed.
Lemma lem46449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem46451 {A B : Type'} (a : A) (x : A) (y : B) (b : B) : (term148 A B x y a b) = (term154 A B a x y b).
Proof. exact (MK_COMB (@lem46449 A) (@lem46448 A B a x y b)). Qed.
Lemma lem46452 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term154 A B a x y b.
Proof. exact (EQ_MP (@lem46451 A B a x y b) (@lem46385 A B x y a b h1)). Qed.
Lemma lem46456 {A : Type'} (x : A) (a : A) (h1 : term155 A x a) : term155 A x a.
Proof. exact (h1). Qed.
Lemma lem46512 {A B : Type'} (a : A) (x' : A) (x : A) (y : B) (x'' : B) (b : B) : (term94 A B x y x' a x'' b) = (term150 A B a x' x y x'' b).
Proof. exact (@lem19490 (x' = a) (term90 A B x' x x'' y) (x'' = b)). Qed.
Lemma lem46513 {A B : Type'} (a : A) (x' : A) (x : A) (y : B) (b : B) : (term111 A B x y x' a b) = (term151 A B a x' x y b).
Proof. exact (fun_ext (fun x'' : B => @lem46512 A B a x' x y x'' b)). Qed.
Lemma lem46514 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem46515 {A B : Type'} (a : A) (x' : A) (x : A) (y : B) (b : B) : (term126 A B x y x' a b) = (term152 A B a x' x y b).
Proof. exact (MK_COMB (@lem46514 B) (@lem46513 A B a x' x y b)). Qed.
Lemma lem46516 {A B : Type'} (a : A) (x : A) (y : B) (b : B) : (term133 A B x y a b) = (term153 A B a x y b).
Proof. exact (fun_ext (fun x' : A => @lem46515 A B a x' x y b)). Qed.
Lemma lem46517 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem46519 {A B : Type'} (a : A) (x : A) (y : B) (b : B) : (term148 A B x y a b) = (term154 A B a x y b).
Proof. exact (MK_COMB (@lem46517 A) (@lem46516 A B a x y b)). Qed.
Lemma lem46520 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term154 A B a x y b.
Proof. exact (EQ_MP (@lem46519 A B a x y b) (@lem46385 A B x y a b h1)). Qed.
Lemma lem46524 {B : Type'} (y : B) (b : B) (h1 : term155 B y b) : term155 B y b.
Proof. exact (h1). Qed.
Lemma lem46531 {A B : Type'} (_1259 : A) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term156 A B a x y b _1259.
Proof. exact (@lem46452 A B x y a b h1 _1259). Qed.
Lemma lem46532 {A B : Type'} (a : A) (_1259 : A) (x : A) (y : B) (b : B) : (term156 A B a x y b _1259) = (term152 A B a _1259 x y b).
Proof. exact (eq_refl (term156 A B a x y b _1259)). Qed.
Lemma lem46533 {A B : Type'} (_1259 : A) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term152 A B a _1259 x y b.
Proof. exact (EQ_MP (@lem46532 A B a _1259 x y b) (@lem46531 A B _1259 x y a b h1)). Qed.
Lemma lem46534 {A B : Type'} (_1259 : A) (_1260 : B) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term157 A B a _1259 x y b _1260.
Proof. exact (@lem46533 A B _1259 x y a b h1 _1260). Qed.
Lemma lem46535 {A B : Type'} (a : A) (_1259 : A) (x : A) (y : B) (_1260 : B) (b : B) : (term157 A B a _1259 x y b _1260) = (term150 A B a _1259 x y _1260 b).
Proof. exact (eq_refl (term157 A B a _1259 x y b _1260)). Qed.
Lemma lem46536 {A B : Type'} (_1259 : A) (_1260 : B) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term150 A B a _1259 x y _1260 b.
Proof. exact (EQ_MP (@lem46535 A B a _1259 x y _1260 b) (@lem46534 A B _1259 _1260 x y a b h1)). Qed.
Lemma lem46543 {A B : Type'} (_1263 : A) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term156 A B a x y b _1263.
Proof. exact (@lem46520 A B x y a b h1 _1263). Qed.
Lemma lem46544 {A B : Type'} (a : A) (_1263 : A) (x : A) (y : B) (b : B) : (term156 A B a x y b _1263) = (term152 A B a _1263 x y b).
Proof. exact (eq_refl (term156 A B a x y b _1263)). Qed.
Lemma lem46545 {A B : Type'} (_1263 : A) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term152 A B a _1263 x y b.
Proof. exact (EQ_MP (@lem46544 A B a _1263 x y b) (@lem46543 A B _1263 x y a b h1)). Qed.
Lemma lem46546 {A B : Type'} (_1263 : A) (_1264 : B) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term157 A B a _1263 x y b _1264.
Proof. exact (@lem46545 A B _1263 x y a b h1 _1264). Qed.
Lemma lem46547 {A B : Type'} (a : A) (_1263 : A) (x : A) (y : B) (_1264 : B) (b : B) : (term157 A B a _1263 x y b _1264) = (term150 A B a _1263 x y _1264 b).
Proof. exact (eq_refl (term157 A B a _1263 x y b _1264)). Qed.
Lemma lem46548 {A B : Type'} (_1263 : A) (_1264 : B) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term150 A B a _1263 x y _1264 b.
Proof. exact (EQ_MP (@lem46547 A B a _1263 x y _1264 b) (@lem46546 A B _1263 _1264 x y a b h1)). Qed.
Lemma lem46550 {A B : Type'} (_1260 : B) (_1259 : A) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term158 A B x _1260 y _1259 a.
Proof. exact (proj1 (@lem46536 A B _1259 _1260 x y a b h1)). Qed.
Lemma lem46553 {A B : Type'} (_1263 : A) (_1264 : B) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term159 A B _1263 x y _1264 b.
Proof. exact (proj2 (@lem46548 A B _1263 _1264 x y a b h1)). Qed.
Lemma lem46558 {A : Type'} (x : A) (a : A) (h1 : term155 A x a) : term155 A x a.
Proof. exact (h1). Qed.
Lemma lem46569 {A B : Type'} (x : A) (_1260 : B) (y : B) (_1259 : A) (a : A) : (term158 A B x _1260 y _1259 a) = (term160 A B x _1260 y _1259 a).
Proof. exact (@lem45488 (term155 A _1259 x) (term155 B _1260 y) (_1259 = a)). Qed.
Lemma lem46570 {A B : Type'} (_1260 : B) (_1259 : A) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term160 A B x _1260 y _1259 a.
Proof. exact (EQ_MP (@lem46569 A B x _1260 y _1259 a) (@lem46550 A B _1260 _1259 x y a b h1)). Qed.
Lemma lem46604 {B : Type'} (y : B) (b : B) (h1 : term155 B y b) : term155 B y b.
Proof. exact (h1). Qed.
Lemma lem46627 {A B : Type'} (_1263 : A) (x : A) (y : B) (_1264 : B) (b : B) : (term159 A B _1263 x y _1264 b) = (term161 A B _1263 x y _1264 b).
Proof. exact (@lem45488 (term155 A _1263 x) (term155 B _1264 y) (_1264 = b)). Qed.
Lemma lem46628 {A B : Type'} (_1263 : A) (_1264 : B) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term161 A B _1263 x y _1264 b.
Proof. exact (EQ_MP (@lem46627 A B _1263 x y _1264 b) (@lem46553 A B _1263 _1264 x y a b h1)). Qed.
Lemma lem46654 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem46655 {A : Type'} (x : A) : x = x.
Proof. exact (@lem46654 A x). Qed.
Lemma lem46656 {A : Type'} (x : A) : term162 A x.
Proof. exact (fun h0 : term163 A x => @lem46655 A x). Qed.
Lemma lem46658 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem46659 {A : Type'} (x : A) : (term162 A x) = (x = x).
Proof. exact (@lem46658 (x = x)). Qed.
Lemma lem46660 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem46659 A x) (@lem46656 A x)). Qed.
Lemma lem46662 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem46663 {B : Type'} (x : B) : x = x.
Proof. exact (@lem46662 B x). Qed.
Lemma lem46664 {B : Type'} (y : B) : y = y.
Proof. exact (@lem46663 B y). Qed.
Lemma lem46665 {B : Type'} (y : B) : term162 B y.
Proof. exact (fun h0 : term163 B y => @lem46664 B y). Qed.
Lemma lem46667 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem46668 {B : Type'} (y : B) : (term162 B y) = (y = y).
Proof. exact (@lem46667 (y = y)). Qed.
Lemma lem46669 {B : Type'} (y : B) : y = y.
Proof. exact (EQ_MP (@lem46668 B y) (@lem46665 B y)). Qed.
Lemma lem46687 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem46688 {A B : Type'} (_1259 : A) (a : A) (_1260 : B) (y : B) : (term165 A B _1260 y _1259 a) = (term166 A B _1259 a _1260 y).
Proof. exact (@lem46687 (_1259 = a) (term155 B _1260 y)). Qed.
Lemma lem46698 {A : Type'} (_1259 : A) (x : A) : (term167 A _1259 x) = (term167 A _1259 x).
Proof. exact (eq_refl (term167 A _1259 x)). Qed.
Lemma lem46699 {A B : Type'} (x : A) (_1259 : A) (a : A) (_1260 : B) (y : B) : (term160 A B x _1260 y _1259 a) = (term168 A B x _1259 a _1260 y).
Proof. exact (MK_COMB (@lem46698 A _1259 x) (@lem46688 A B _1259 a _1260 y)). Qed.
Lemma lem46703 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem46704 {A B : Type'} (a : A) (_1259 : A) (x : A) (_1260 : B) (y : B) : (term168 A B x _1259 a _1260 y) = (term169 A B a _1259 x _1260 y).
Proof. exact (@lem46703 (_1259 = a) (term155 A _1259 x) (term155 B _1260 y)). Qed.
Lemma lem46726 {A B : Type'} (a : A) (_1259 : A) (x : A) (_1260 : B) (y : B) : (term160 A B x _1260 y _1259 a) = (term169 A B a _1259 x _1260 y).
Proof. exact (TRANS (@lem46699 A B x _1259 a _1260 y) (@lem46704 A B a _1259 x _1260 y)). Qed.
Lemma lem46727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem46728 {A B : Type'} (a : A) (_1259 : A) (x : A) (_1260 : B) (y : B) : (term170 A B x _1260 y _1259 a) = (term171 A B a _1259 x _1260 y).
Proof. exact (MK_COMB (@lem46727) (@lem46726 A B a _1259 x _1260 y)). Qed.
Lemma lem46750 {A B : Type'} (a : A) (_1259 : A) (x : A) (_1260 : B) (y : B) : (term169 A B a _1259 x _1260 y) = (term169 A B a _1259 x _1260 y).
Proof. exact (eq_refl (term169 A B a _1259 x _1260 y)). Qed.
Lemma lem46751 {A B : Type'} (a : A) (_1259 : A) (x : A) (_1260 : B) (y : B) : ((term160 A B x _1260 y _1259 a) = (term169 A B a _1259 x _1260 y)) = ((term169 A B a _1259 x _1260 y) = (term169 A B a _1259 x _1260 y)).
Proof. exact (MK_COMB (@lem46728 A B a _1259 x _1260 y) (@lem46750 A B a _1259 x _1260 y)). Qed.
Lemma lem46753 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem46754 (x : Prop) : (x = x) = True.
Proof. exact (@lem46753 Prop x). Qed.
Lemma lem46755 {A B : Type'} (a : A) (_1259 : A) (x : A) (_1260 : B) (y : B) : ((term169 A B a _1259 x _1260 y) = (term169 A B a _1259 x _1260 y)) = True.
Proof. exact (@lem46754 (term169 A B a _1259 x _1260 y)). Qed.
Lemma lem46756 {A B : Type'} (a : A) (_1259 : A) (x : A) (_1260 : B) (y : B) : ((term160 A B x _1260 y _1259 a) = (term169 A B a _1259 x _1260 y)) = True.
Proof. exact (TRANS (@lem46751 A B a _1259 x _1260 y) (@lem46755 A B a _1259 x _1260 y)). Qed.
Lemma lem46757 {A B : Type'} (a : A) (_1259 : A) (x : A) (_1260 : B) (y : B) : True = ((term160 A B x _1260 y _1259 a) = (term169 A B a _1259 x _1260 y)).
Proof. exact (SYM (@lem46756 A B a _1259 x _1260 y)). Qed.
Lemma lem46758 {A B : Type'} (a : A) (_1259 : A) (x : A) (_1260 : B) (y : B) : (term160 A B x _1260 y _1259 a) = (term169 A B a _1259 x _1260 y).
Proof. exact (EQ_MP (@lem46757 A B a _1259 x _1260 y) (@lem0)). Qed.
Lemma lem46759 {A B : Type'} (_1259 : A) (_1260 : B) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term169 A B a _1259 x _1260 y.
Proof. exact (EQ_MP (@lem46758 A B a _1259 x _1260 y) (@lem46570 A B _1260 _1259 x y a b h1)). Qed.
Lemma lem46761 (b : Prop) (a : Prop) : (a \/ b) = (term172 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem46762 {A B : Type'} (x : A) (_1260 : B) (y : B) (_1259 : A) (a : A) : (term169 A B a _1259 x _1260 y) = (term173 A B x _1260 y _1259 a).
Proof. exact (@lem46761 (term90 A B _1259 x _1260 y) (_1259 = a)). Qed.
Lemma lem46764 (a : Prop) (b : Prop) : (term174 a b) = (term175 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem46765 {A B : Type'} (_1259 : A) (x : A) (_1260 : B) (y : B) : (term176 A B _1259 x _1260 y) = (term177 A B _1259 x _1260 y).
Proof. exact (@lem46764 (term155 A _1259 x) (term155 B _1260 y)). Qed.
Lemma lem46767 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem46768 {A : Type'} (_1259 : A) (x : A) : (term178 A _1259 x) = (_1259 = x).
Proof. exact (@lem46767 (_1259 = x)). Qed.
Lemma lem46769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem46770 {A : Type'} (_1259 : A) (x : A) : (term179 A _1259 x) = (term180 A _1259 x).
Proof. exact (MK_COMB (@lem46769) (@lem46768 A _1259 x)). Qed.
Lemma lem46772 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem46773 {B : Type'} (_1260 : B) (y : B) : (term178 B _1260 y) = (_1260 = y).
Proof. exact (@lem46772 (_1260 = y)). Qed.
Lemma lem46774 {A B : Type'} (_1259 : A) (x : A) (_1260 : B) (y : B) : (term177 A B _1259 x _1260 y) = (term27 A B _1259 x _1260 y).
Proof. exact (MK_COMB (@lem46770 A _1259 x) (@lem46773 B _1260 y)). Qed.
Lemma lem46775 {A B : Type'} (_1259 : A) (x : A) (_1260 : B) (y : B) : (term176 A B _1259 x _1260 y) = (term27 A B _1259 x _1260 y).
Proof. exact (TRANS (@lem46765 A B _1259 x _1260 y) (@lem46774 A B _1259 x _1260 y)). Qed.
Lemma lem46776 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem46777 {A B : Type'} (_1259 : A) (x : A) (_1260 : B) (y : B) : (term181 A B _1259 x _1260 y) = (term182 A B _1259 x _1260 y).
Proof. exact (MK_COMB (@lem46776) (@lem46775 A B _1259 x _1260 y)). Qed.
Lemma lem46778 {A : Type'} (_1259 : A) (a : A) : (_1259 = a) = (_1259 = a).
Proof. exact (eq_refl (_1259 = a)). Qed.
Lemma lem46779 {A B : Type'} (x : A) (_1260 : B) (y : B) (_1259 : A) (a : A) : (term173 A B x _1260 y _1259 a) = (term183 A B x _1260 y _1259 a).
Proof. exact (MK_COMB (@lem46777 A B _1259 x _1260 y) (@lem46778 A _1259 a)). Qed.
Lemma lem46780 {A B : Type'} (x : A) (_1260 : B) (y : B) (_1259 : A) (a : A) : (term169 A B a _1259 x _1260 y) = (term183 A B x _1260 y _1259 a).
Proof. exact (TRANS (@lem46762 A B x _1260 y _1259 a) (@lem46779 A B x _1260 y _1259 a)). Qed.
Lemma lem46782 {A B : Type'} (x : A) (y : B) : term184 A B x y.
Proof. exact (conj (@lem46660 A x) (@lem46669 B y)). Qed.
Lemma lem46784 {A B : Type'} (_1260 : B) (_1259 : A) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term183 A B x _1260 y _1259 a.
Proof. exact (EQ_MP (@lem46780 A B x _1260 y _1259 a) (@lem46759 A B _1259 _1260 x y a b h1)). Qed.
Lemma lem46785 {A B : Type'} (_1260 : B) (_1259 : A) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term183 A B x _1260 y _1259 a.
Proof. exact (@lem46784 A B _1260 _1259 x y a b h1). Qed.
Lemma lem46786 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term185 A B y x a.
Proof. exact (@lem46785 A B y x x y a b h1). Qed.
Lemma lem46789 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : x = a.
Proof. exact (@lem46786 A B x y a b h1 (@lem46782 A B x y)). Qed.
Lemma lem46790 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term186 A x a.
Proof. exact (fun h0 : term155 A x a => @lem46789 A B x y a b h1). Qed.
Lemma lem46792 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem46793 {A : Type'} (x : A) (a : A) : (term186 A x a) = (x = a).
Proof. exact (@lem46792 (x = a)). Qed.
Lemma lem46794 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : x = a.
Proof. exact (EQ_MP (@lem46793 A x a) (@lem46790 A B x y a b h1)). Qed.
Lemma lem46797 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem46799 {A : Type'} (x : A) (a : A) : (term155 A x a) = (term187 A x a).
Proof. exact (@lem46797 (x = a)). Qed.
Lemma lem46802 {A : Type'} (x : A) (a : A) (h1 : term155 A x a) : term187 A x a.
Proof. exact (EQ_MP (@lem46799 A x a) (@lem46558 A x a h1)). Qed.
Lemma lem46805 {A B : Type'} (y : B) (b : B) (x : A) (a : A) (h1 : term61 A B x y a b) (h2 : term155 A x a) : False.
Proof. exact (@lem46802 A x a h2 (@lem46794 A B x y a b h1)). Qed.
Lemma lem46806 {A B : Type'} (y : B) (b : B) (x : A) (a : A) (h1 : term61 A B x y a b) (h2 : term155 A x a) : term188.
Proof. exact (fun h0 : ~ False => @lem46805 A B y b x a h1 h2). Qed.
Lemma lem46808 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem46809 : term188 = False.
Proof. exact (@lem46808 False). Qed.
Lemma lem46810 {A B : Type'} (y : B) (b : B) (x : A) (a : A) (h1 : term61 A B x y a b) (h2 : term155 A x a) : False.
Proof. exact (EQ_MP (@lem46809) (@lem46806 A B y b x a h1 h2)). Qed.
Lemma lem46816 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem46817 {A : Type'} (x : A) : x = x.
Proof. exact (@lem46816 A x). Qed.
Lemma lem46818 {A : Type'} (x : A) : term162 A x.
Proof. exact (fun h0 : term163 A x => @lem46817 A x). Qed.
Lemma lem46820 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem46821 {A : Type'} (x : A) : (term162 A x) = (x = x).
Proof. exact (@lem46820 (x = x)). Qed.
Lemma lem46822 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem46821 A x) (@lem46818 A x)). Qed.
Lemma lem46824 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem46825 {B : Type'} (x : B) : x = x.
Proof. exact (@lem46824 B x). Qed.
Lemma lem46826 {B : Type'} (y : B) : y = y.
Proof. exact (@lem46825 B y). Qed.
Lemma lem46827 {B : Type'} (y : B) : term162 B y.
Proof. exact (fun h0 : term163 B y => @lem46826 B y). Qed.
Lemma lem46829 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem46830 {B : Type'} (y : B) : (term162 B y) = (y = y).
Proof. exact (@lem46829 (y = y)). Qed.
Lemma lem46831 {B : Type'} (y : B) : y = y.
Proof. exact (EQ_MP (@lem46830 B y) (@lem46827 B y)). Qed.
Lemma lem46849 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem46850 {B : Type'} (b : B) (_1264 : B) (y : B) : (term189 B y _1264 b) = (term190 B b _1264 y).
Proof. exact (@lem46849 (_1264 = b) (term155 B _1264 y)). Qed.
Lemma lem46860 {A : Type'} (_1263 : A) (x : A) : (term167 A _1263 x) = (term167 A _1263 x).
Proof. exact (eq_refl (term167 A _1263 x)). Qed.
Lemma lem46861 {A B : Type'} (_1263 : A) (x : A) (b : B) (_1264 : B) (y : B) : (term161 A B _1263 x y _1264 b) = (term191 A B _1263 x b _1264 y).
Proof. exact (MK_COMB (@lem46860 A _1263 x) (@lem46850 B b _1264 y)). Qed.
Lemma lem46865 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem46866 {A B : Type'} (b : B) (_1263 : A) (x : A) (_1264 : B) (y : B) : (term191 A B _1263 x b _1264 y) = (term192 A B b _1263 x _1264 y).
Proof. exact (@lem46865 (_1264 = b) (term155 A _1263 x) (term155 B _1264 y)). Qed.
Lemma lem46888 {A B : Type'} (b : B) (_1263 : A) (x : A) (_1264 : B) (y : B) : (term161 A B _1263 x y _1264 b) = (term192 A B b _1263 x _1264 y).
Proof. exact (TRANS (@lem46861 A B _1263 x b _1264 y) (@lem46866 A B b _1263 x _1264 y)). Qed.
Lemma lem46889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem46890 {A B : Type'} (b : B) (_1263 : A) (x : A) (_1264 : B) (y : B) : (term193 A B _1263 x y _1264 b) = (term194 A B b _1263 x _1264 y).
Proof. exact (MK_COMB (@lem46889) (@lem46888 A B b _1263 x _1264 y)). Qed.
Lemma lem46912 {A B : Type'} (b : B) (_1263 : A) (x : A) (_1264 : B) (y : B) : (term192 A B b _1263 x _1264 y) = (term192 A B b _1263 x _1264 y).
Proof. exact (eq_refl (term192 A B b _1263 x _1264 y)). Qed.
Lemma lem46913 {A B : Type'} (b : B) (_1263 : A) (x : A) (_1264 : B) (y : B) : ((term161 A B _1263 x y _1264 b) = (term192 A B b _1263 x _1264 y)) = ((term192 A B b _1263 x _1264 y) = (term192 A B b _1263 x _1264 y)).
Proof. exact (MK_COMB (@lem46890 A B b _1263 x _1264 y) (@lem46912 A B b _1263 x _1264 y)). Qed.
Lemma lem46915 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem46916 (x : Prop) : (x = x) = True.
Proof. exact (@lem46915 Prop x). Qed.
Lemma lem46917 {A B : Type'} (b : B) (_1263 : A) (x : A) (_1264 : B) (y : B) : ((term192 A B b _1263 x _1264 y) = (term192 A B b _1263 x _1264 y)) = True.
Proof. exact (@lem46916 (term192 A B b _1263 x _1264 y)). Qed.
Lemma lem46918 {A B : Type'} (b : B) (_1263 : A) (x : A) (_1264 : B) (y : B) : ((term161 A B _1263 x y _1264 b) = (term192 A B b _1263 x _1264 y)) = True.
Proof. exact (TRANS (@lem46913 A B b _1263 x _1264 y) (@lem46917 A B b _1263 x _1264 y)). Qed.
Lemma lem46919 {A B : Type'} (b : B) (_1263 : A) (x : A) (_1264 : B) (y : B) : True = ((term161 A B _1263 x y _1264 b) = (term192 A B b _1263 x _1264 y)).
Proof. exact (SYM (@lem46918 A B b _1263 x _1264 y)). Qed.
Lemma lem46920 {A B : Type'} (b : B) (_1263 : A) (x : A) (_1264 : B) (y : B) : (term161 A B _1263 x y _1264 b) = (term192 A B b _1263 x _1264 y).
Proof. exact (EQ_MP (@lem46919 A B b _1263 x _1264 y) (@lem0)). Qed.
Lemma lem46921 {A B : Type'} (_1263 : A) (_1264 : B) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term192 A B b _1263 x _1264 y.
Proof. exact (EQ_MP (@lem46920 A B b _1263 x _1264 y) (@lem46628 A B _1263 _1264 x y a b h1)). Qed.
Lemma lem46923 (b : Prop) (a : Prop) : (a \/ b) = (term172 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem46924 {A B : Type'} (_1263 : A) (x : A) (y : B) (_1264 : B) (b : B) : (term192 A B b _1263 x _1264 y) = (term195 A B _1263 x y _1264 b).
Proof. exact (@lem46923 (term90 A B _1263 x _1264 y) (_1264 = b)). Qed.
Lemma lem46926 (a : Prop) (b : Prop) : (term174 a b) = (term175 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem46927 {A B : Type'} (_1263 : A) (x : A) (_1264 : B) (y : B) : (term176 A B _1263 x _1264 y) = (term177 A B _1263 x _1264 y).
Proof. exact (@lem46926 (term155 A _1263 x) (term155 B _1264 y)). Qed.
Lemma lem46929 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem46930 {A : Type'} (_1263 : A) (x : A) : (term178 A _1263 x) = (_1263 = x).
Proof. exact (@lem46929 (_1263 = x)). Qed.
Lemma lem46931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem46932 {A : Type'} (_1263 : A) (x : A) : (term179 A _1263 x) = (term180 A _1263 x).
Proof. exact (MK_COMB (@lem46931) (@lem46930 A _1263 x)). Qed.
Lemma lem46934 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem46935 {B : Type'} (_1264 : B) (y : B) : (term178 B _1264 y) = (_1264 = y).
Proof. exact (@lem46934 (_1264 = y)). Qed.
Lemma lem46936 {A B : Type'} (_1263 : A) (x : A) (_1264 : B) (y : B) : (term177 A B _1263 x _1264 y) = (term27 A B _1263 x _1264 y).
Proof. exact (MK_COMB (@lem46932 A _1263 x) (@lem46935 B _1264 y)). Qed.
Lemma lem46937 {A B : Type'} (_1263 : A) (x : A) (_1264 : B) (y : B) : (term176 A B _1263 x _1264 y) = (term27 A B _1263 x _1264 y).
Proof. exact (TRANS (@lem46927 A B _1263 x _1264 y) (@lem46936 A B _1263 x _1264 y)). Qed.
Lemma lem46938 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem46939 {A B : Type'} (_1263 : A) (x : A) (_1264 : B) (y : B) : (term181 A B _1263 x _1264 y) = (term182 A B _1263 x _1264 y).
Proof. exact (MK_COMB (@lem46938) (@lem46937 A B _1263 x _1264 y)). Qed.
Lemma lem46940 {B : Type'} (_1264 : B) (b : B) : (_1264 = b) = (_1264 = b).
Proof. exact (eq_refl (_1264 = b)). Qed.
Lemma lem46941 {A B : Type'} (_1263 : A) (x : A) (y : B) (_1264 : B) (b : B) : (term195 A B _1263 x y _1264 b) = (term196 A B _1263 x y _1264 b).
Proof. exact (MK_COMB (@lem46939 A B _1263 x _1264 y) (@lem46940 B _1264 b)). Qed.
Lemma lem46942 {A B : Type'} (_1263 : A) (x : A) (y : B) (_1264 : B) (b : B) : (term192 A B b _1263 x _1264 y) = (term196 A B _1263 x y _1264 b).
Proof. exact (TRANS (@lem46924 A B _1263 x y _1264 b) (@lem46941 A B _1263 x y _1264 b)). Qed.
Lemma lem46944 {A B : Type'} (x : A) (y : B) : term184 A B x y.
Proof. exact (conj (@lem46822 A x) (@lem46831 B y)). Qed.
Lemma lem46946 {A B : Type'} (_1263 : A) (_1264 : B) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term196 A B _1263 x y _1264 b.
Proof. exact (EQ_MP (@lem46942 A B _1263 x y _1264 b) (@lem46921 A B _1263 _1264 x y a b h1)). Qed.
Lemma lem46947 {A B : Type'} (_1263 : A) (_1264 : B) (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term196 A B _1263 x y _1264 b.
Proof. exact (@lem46946 A B _1263 _1264 x y a b h1). Qed.
Lemma lem46948 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term197 A B x y b.
Proof. exact (@lem46947 A B x y x y a b h1). Qed.
Lemma lem46951 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : y = b.
Proof. exact (@lem46948 A B x y a b h1 (@lem46944 A B x y)). Qed.
Lemma lem46952 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term186 B y b.
Proof. exact (fun h0 : term155 B y b => @lem46951 A B x y a b h1). Qed.
Lemma lem46954 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem46955 {B : Type'} (y : B) (b : B) : (term186 B y b) = (y = b).
Proof. exact (@lem46954 (y = b)). Qed.
Lemma lem46956 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : y = b.
Proof. exact (EQ_MP (@lem46955 B y b) (@lem46952 A B x y a b h1)). Qed.
Lemma lem46959 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem46961 {B : Type'} (y : B) (b : B) : (term155 B y b) = (term187 B y b).
Proof. exact (@lem46959 (y = b)). Qed.
Lemma lem46964 {B : Type'} (y : B) (b : B) (h1 : term155 B y b) : term187 B y b.
Proof. exact (EQ_MP (@lem46961 B y b) (@lem46604 B y b h1)). Qed.
Lemma lem46967 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term155 B y b) : False.
Proof. exact (@lem46964 B y b h2 (@lem46956 A B x y a b h1)). Qed.
Lemma lem46968 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term155 B y b) : term188.
Proof. exact (fun h0 : ~ False => @lem46967 A B x a y b h1 h2). Qed.
Lemma lem46970 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem46971 : term188 = False.
Proof. exact (@lem46970 False). Qed.
Lemma lem46972 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term155 B y b) : False.
Proof. exact (EQ_MP (@lem46971) (@lem46968 A B x a y b h1 h2)). Qed.
Lemma lem46973 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term155 B y b) : (term155 B y b) = False.
Proof. exact (prop_ext (fun h3 : term155 B y b => @lem46972 A B x a y b h1 h2) (fun h3 : False => @lem46604 B y b h2)). Qed.
Lemma lem46974 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term155 B y b) : False.
Proof. exact (EQ_MP (@lem46973 A B x a y b h1 h2) (@lem46604 B y b h2)). Qed.
Lemma lem46975 {A B : Type'} (y : B) (b : B) (x : A) (a : A) (h1 : term61 A B x y a b) (h2 : term155 A x a) : (term155 A x a) = False.
Proof. exact (prop_ext (fun h3 : term155 A x a => @lem46810 A B y b x a h1 h2) (fun h3 : False => @lem46558 A x a h2)). Qed.
Lemma lem46976 {A B : Type'} (y : B) (b : B) (x : A) (a : A) (h1 : term61 A B x y a b) (h2 : term155 A x a) : False.
Proof. exact (EQ_MP (@lem46975 A B y b x a h1 h2) (@lem46558 A x a h2)). Qed.
Lemma lem46977 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term155 B y b) : (term155 B y b) = False.
Proof. exact (prop_ext (fun h3 : term155 B y b => @lem46974 A B x a y b h1 h2) (fun h3 : False => @lem46524 B y b h2)). Qed.
Lemma lem46978 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term155 B y b) : False.
Proof. exact (EQ_MP (@lem46977 A B x a y b h1 h2) (@lem46524 B y b h2)). Qed.
Lemma lem46979 {A B : Type'} (y : B) (b : B) (x : A) (a : A) (h1 : term61 A B x y a b) (h2 : term155 A x a) : (term155 A x a) = False.
Proof. exact (prop_ext (fun h3 : term155 A x a => @lem46976 A B y b x a h1 h2) (fun h3 : False => @lem46456 A x a h2)). Qed.
Lemma lem46980 {A B : Type'} (y : B) (b : B) (x : A) (a : A) (h1 : term61 A B x y a b) (h2 : term155 A x a) : False.
Proof. exact (EQ_MP (@lem46979 A B y b x a h1 h2) (@lem46456 A x a h2)). Qed.
Lemma lem46981 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term155 B y b) : (term155 B y b) = False.
Proof. exact (prop_ext (fun h3 : term155 B y b => @lem46978 A B x a y b h1 h2) (fun h3 : False => @lem46524 B y b h2)). Qed.
Lemma lem46982 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term155 B y b) : False.
Proof. exact (EQ_MP (@lem46981 A B x a y b h1 h2) (@lem46524 B y b h2)). Qed.
Lemma lem46983 {A B : Type'} (y : B) (b : B) (x : A) (a : A) (h1 : term61 A B x y a b) (h2 : term155 A x a) : (term155 A x a) = False.
Proof. exact (prop_ext (fun h3 : term155 A x a => @lem46980 A B y b x a h1 h2) (fun h3 : False => @lem46456 A x a h2)). Qed.
Lemma lem46984 {A B : Type'} (y : B) (b : B) (x : A) (a : A) (h1 : term61 A B x y a b) (h2 : term155 A x a) : False.
Proof. exact (EQ_MP (@lem46983 A B y b x a h1 h2) (@lem46456 A x a h2)). Qed.
Lemma lem46985 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term89 A B x a y b) : False.
Proof. exact (or_elim (@lem46384 A B x a y b h2) (fun h0 : term155 A x a => @lem46984 A B y b x a h1 h0) (fun h0 : term155 B y b => @lem46982 A B x a y b h1 h0)). Qed.
Lemma lem46986 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term89 A B x a y b) : (term89 A B x a y b) = False.
Proof. exact (prop_ext (fun h3 : term89 A B x a y b => @lem46985 A B x a y b h1 h2) (fun h3 : False => @lem45965 A B x a y b h2)). Qed.
Lemma lem46987 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term61 A B x y a b) (h2 : term89 A B x a y b) : False.
Proof. exact (EQ_MP (@lem46986 A B x a y b h1 h2) (@lem45965 A B x a y b h2)). Qed.
Lemma lem46988 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term88 A B x a y b.
Proof. exact (fun h0 : term89 A B x a y b => @lem46987 A B x a y b h1 h0). Qed.
Lemma lem46989 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term61 A B x y a b) : term27 A B x a y b.
Proof. exact (EQ_MP (@lem45964 A B x a y b) (@lem46988 A B x y a b h1)). Qed.
Lemma lem46990 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term63 A B x a y b.
Proof. exact (fun h0 : term61 A B x y a b => @lem46989 A B x y a b h0). Qed.
Lemma lem46995 {A B : Type'} (a : A) (y : B) (b : B) : term75 A B a y b.
Proof. exact (fun x : A => @lem46990 A B x a y b). Qed.
Lemma lem47000 {A B : Type'} (y : B) (b : B) : term79 A B y b.
Proof. exact (fun a : A => @lem46995 A B a y b). Qed.
Lemma lem47005 {A B : Type'} (b : B) : term83 A B b.
Proof. exact (fun y : B => @lem47000 A B y b). Qed.
Lemma lem47010 {A B : Type'} : term87 A B.
Proof. exact (fun b : B => @lem47005 A B b). Qed.
Lemma lem47011 {A B : Type'} : term86 A B.
Proof. exact (EQ_MP (@lem45959 A B) (@lem47010 A B)). Qed.
Lemma lem47012 {A B : Type'} (b : B) : term198 A B b.
Proof. exact (@lem47011 A B b). Qed.
Lemma lem47013 {A B : Type'} (b : B) : (term198 A B b) = (term82 A B b).
Proof. exact (eq_refl (term198 A B b)). Qed.
Lemma lem47014 {A B : Type'} (b : B) : term82 A B b.
Proof. exact (EQ_MP (@lem47013 A B b) (@lem47012 A B b)). Qed.
Lemma lem47015 {A B : Type'} (b : B) (y : B) : term199 A B b y.
Proof. exact (@lem47014 A B b y). Qed.
Lemma lem47016 {A B : Type'} (y : B) (b : B) : (term199 A B b y) = (term78 A B y b).
Proof. exact (eq_refl (term199 A B b y)). Qed.
Lemma lem47017 {A B : Type'} (y : B) (b : B) : term78 A B y b.
Proof. exact (EQ_MP (@lem47016 A B y b) (@lem47015 A B b y)). Qed.
Lemma lem47018 {A B : Type'} (y : B) (b : B) (a : A) : term200 A B y b a.
Proof. exact (@lem47017 A B y b a). Qed.
Lemma lem47019 {A B : Type'} (a : A) (y : B) (b : B) : (term200 A B y b a) = (term74 A B a y b).
Proof. exact (eq_refl (term200 A B y b a)). Qed.
Lemma lem47020 {A B : Type'} (a : A) (y : B) (b : B) : term74 A B a y b.
Proof. exact (EQ_MP (@lem47019 A B a y b) (@lem47018 A B y b a)). Qed.
Lemma lem47021 {A B : Type'} (a : A) (y : B) (b : B) (x : A) : term201 A B a y b x.
Proof. exact (@lem47020 A B a y b x). Qed.
Lemma lem47022 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term201 A B a y b x) = (term65 A B x a y b).
Proof. exact (eq_refl (term201 A B a y b x)). Qed.
Lemma lem47023 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term65 A B x a y b.
Proof. exact (EQ_MP (@lem47022 A B x a y b) (@lem47021 A B a y b x)). Qed.
Lemma lem47025 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term65 A B x a y b.
Proof. exact (@lem45801 A B x a y b (@lem47023 A B x a y b)). Qed.
Lemma lem47026 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term66 A B x a y b) : False.
Proof. exact (@lem47025 A B x a y b (@lem45785 A B x a y b h1)). Qed.
Lemma lem47027 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term66 A B x a y b) : (term66 A B x a y b) = False.
Proof. exact (prop_ext (fun h2 : term66 A B x a y b => @lem47026 A B x a y b h1) (fun h2 : False => @lem45785 A B x a y b h1)). Qed.
Lemma lem47028 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term66 A B x a y b) : False.
Proof. exact (EQ_MP (@lem47027 A B x a y b h1) (@lem45785 A B x a y b h1)). Qed.
Lemma lem47029 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term65 A B x a y b.
Proof. exact (fun h0 : term66 A B x a y b => @lem47028 A B x a y b h0). Qed.
Lemma lem47030 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term63 A B x a y b.
Proof. exact (EQ_MP (@lem45784 A B x a y b) (@lem47029 A B x a y b)). Qed.
Lemma lem47032 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem47033 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term202 A B x y a b) = (term203 A B x y a b).
Proof. exact (@lem47032 (term202 A B x y a b)). Qed.
Lemma lem47034 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term203 A B x y a b) = (term202 A B x y a b).
Proof. exact (SYM (@lem47033 A B x y a b)). Qed.
Lemma lem47035 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term204 A B x y a b) : term204 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem47038 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term203 A B x y a b) : term203 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem47039 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : term205 A B x y a b.
Proof. exact (fun h0 : term203 A B x y a b => @lem47038 A B x y a b h0). Qed.
Lemma lem47040 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term205 A B x y a b) : term205 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem47041 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term203 A B x y a b) : term203 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem47042 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term203 A B x y a b) (h2 : term205 A B x y a b) : term203 A B x y a b.
Proof. exact (@lem47040 A B x y a b h2 (@lem47041 A B x y a b h1)). Qed.
Lemma lem47043 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term203 A B x y a b) : term206 A B x y a b.
Proof. exact (fun h0 : term205 A B x y a b => @lem47042 A B x y a b h1 h0). Qed.
Lemma lem47044 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term205 A B x y a b) : term205 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem47045 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term203 A B x y a b) (h2 : term205 A B x y a b) : term203 A B x y a b.
Proof. exact (@lem47043 A B x y a b h1 (@lem47044 A B x y a b h2)). Qed.
Lemma lem47046 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term205 A B x y a b) : term205 A B x y a b.
Proof. exact (fun h0 : term203 A B x y a b => @lem47045 A B x y a b h0 h1). Qed.
Lemma lem47047 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : term207 A B x y a b.
Proof. exact (fun h0 : term205 A B x y a b => @lem47046 A B x y a b h0). Qed.
Lemma lem47050 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : term205 A B x y a b.
Proof. exact (@lem47047 A B x y a b (@lem47039 A B x y a b)). Qed.
Lemma lem47051 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : term205 A B x y a b.
Proof. exact (@lem47050 A B x y a b). Qed.
Lemma lem47069 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem47070 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term203 A B x y a b) = (term208 A B x y a b).
Proof. exact (@lem47069 (term204 A B x y a b)). Qed.
Lemma lem47072 (t : Prop) : (term71 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem47073 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term208 A B x y a b) = (term202 A B x y a b).
Proof. exact (@lem47072 (term202 A B x y a b)). Qed.
Lemma lem47076 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term203 A B x y a b) = (term202 A B x y a b).
Proof. exact (TRANS (@lem47070 A B x y a b) (@lem47073 A B x y a b)). Qed.
Lemma lem47079 {A B : Type'} (y : B) (a : A) (b : B) : (term209 A B y a b) = (term210 A B y a b).
Proof. exact (fun_ext (fun x : A => @lem47076 A B x y a b)). Qed.
Lemma lem47080 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem47081 {A B : Type'} (y : B) (a : A) (b : B) : (term211 A B y a b) = (term212 A B y a b).
Proof. exact (MK_COMB (@lem47080 A) (@lem47079 A B y a b)). Qed.
Lemma lem47086 {A B : Type'} (a : A) (b : B) : (term213 A B a b) = (term214 A B a b).
Proof. exact (fun_ext (fun y : B => @lem47081 A B y a b)). Qed.
Lemma lem47087 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem47088 {A B : Type'} (a : A) (b : B) : (term215 A B a b) = (term216 A B a b).
Proof. exact (MK_COMB (@lem47087 B) (@lem47086 A B a b)). Qed.
Lemma lem47093 {A B : Type'} (b : B) : (term217 A B b) = (term218 A B b).
Proof. exact (fun_ext (fun a : A => @lem47088 A B a b)). Qed.
Lemma lem47094 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem47095 {A B : Type'} (b : B) : (term219 A B b) = (term220 A B b).
Proof. exact (MK_COMB (@lem47094 A) (@lem47093 A B b)). Qed.
Lemma lem47100 {A B : Type'} : (term221 A B) = (term222 A B).
Proof. exact (fun_ext (fun b : B => @lem47095 A B b)). Qed.
Lemma lem47101 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem47110 {A B : Type'} : (term223 A B) = (term224 A B).
Proof. exact (MK_COMB (@lem47101 B) (@lem47100 A B)). Qed.
Lemma lem47119 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term202 A B x y a b) = (term202 A B x y a b).
Proof. exact (eq_refl (term202 A B x y a b)). Qed.
Lemma lem47120 {A B : Type'} (y : B) (a : A) (b : B) : (term210 A B y a b) = (term210 A B y a b).
Proof. exact (fun_ext (fun x : A => @lem47119 A B x y a b)). Qed.
Lemma lem47121 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem47122 {A B : Type'} (y : B) (a : A) (b : B) : (term212 A B y a b) = (term212 A B y a b).
Proof. exact (MK_COMB (@lem47121 A) (@lem47120 A B y a b)). Qed.
Lemma lem47123 {A B : Type'} (a : A) (b : B) : (term214 A B a b) = (term214 A B a b).
Proof. exact (fun_ext (fun y : B => @lem47122 A B y a b)). Qed.
Lemma lem47124 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem47125 {A B : Type'} (a : A) (b : B) : (term216 A B a b) = (term216 A B a b).
Proof. exact (MK_COMB (@lem47124 B) (@lem47123 A B a b)). Qed.
Lemma lem47126 {A B : Type'} (b : B) : (term218 A B b) = (term218 A B b).
Proof. exact (fun_ext (fun a : A => @lem47125 A B a b)). Qed.
Lemma lem47127 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem47128 {A B : Type'} (b : B) : (term220 A B b) = (term220 A B b).
Proof. exact (MK_COMB (@lem47127 A) (@lem47126 A B b)). Qed.
Lemma lem47129 {A B : Type'} : (term222 A B) = (term222 A B).
Proof. exact (fun_ext (fun b : B => @lem47128 A B b)). Qed.
Lemma lem47130 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem47131 {A B : Type'} : (term224 A B) = (term224 A B).
Proof. exact (MK_COMB (@lem47130 B) (@lem47129 A B)). Qed.
Lemma lem47162 {A B : Type'} : (term223 A B) = (term224 A B).
Proof. exact (TRANS (@lem47110 A B) (@lem47131 A B)). Qed.
Lemma lem47163 {A B : Type'} : (term224 A B) = (term223 A B).
Proof. exact (SYM (@lem47162 A B)). Qed.
Lemma lem47166 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem47167 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term225 A B x y a b).
Proof. exact (@lem47166 ((@pair A B x y) = (@pair A B a b))). Qed.
Lemma lem47168 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term225 A B x y a b) = ((@pair A B x y) = (@pair A B a b)).
Proof. exact (SYM (@lem47167 A B x y a b)). Qed.
Lemma lem47169 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term226 A B x y a b) : term226 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem47179 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term27 A B x a y b) : term27 A B x a y b.
Proof. exact (h1). Qed.
Lemma lem47185 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term226 A B x y a b) : term226 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem47199 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term27 A B x a y b) : term27 A B x a y b.
Proof. exact (h1). Qed.
Lemma lem47215 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term226 A B x y a b) : term226 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem47221 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term226 A B x y a b) : term226 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem47231 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term226 A B x y a b) : term226 A B x y a b.
Proof. exact (h1). Qed.
Lemma lem47235 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term27 A B x a y b) : y = b.
Proof. exact (proj2 (@lem47199 A B x a y b h1)). Qed.
Lemma lem47250 {A B : Type'} (x : A) (a : A) (b : B) : (term227 A B x a b) = (term227 A B x a b).
Proof. exact (eq_refl (term227 A B x a b)). Qed.
Lemma lem47251 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term27 A B x a y b) : (term228 A B x a b y) = (term229 A B x a b).
Proof. exact (MK_COMB (@lem47250 A B x a b) (@lem47235 A B x a y b h1)). Qed.
Lemma lem47252 {A B : Type'} (x : A) (a : A) (b : B) : (term229 A B x a b) = (term230 A B x a b).
Proof. exact (eq_refl (term229 A B x a b)). Qed.
Lemma lem47253 {A B : Type'} (x : A) (a : A) (b : B) (y : B) : (term231 A B x a b y) = (term231 A B x a b y).
Proof. exact (eq_refl (term231 A B x a b y)). Qed.
Lemma lem47254 {A B : Type'} (y : B) (x : A) (a : A) (b : B) : ((term228 A B x a b y) = (term229 A B x a b)) = ((term228 A B x a b y) = (term230 A B x a b)).
Proof. exact (MK_COMB (@lem47253 A B x a b y) (@lem47252 A B x a b)). Qed.
Lemma lem47255 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term228 A B x a b y) = (term226 A B x y a b).
Proof. exact (eq_refl (term228 A B x a b y)). Qed.
Lemma lem47256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem47257 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term231 A B x a b y) = (term232 A B x y a b).
Proof. exact (MK_COMB (@lem47256) (@lem47255 A B x y a b)). Qed.
Lemma lem47258 {A B : Type'} (x : A) (a : A) (b : B) : (term230 A B x a b) = (term230 A B x a b).
Proof. exact (eq_refl (term230 A B x a b)). Qed.
Lemma lem47259 {A B : Type'} (y : B) (x : A) (a : A) (b : B) : ((term228 A B x a b y) = (term230 A B x a b)) = ((term226 A B x y a b) = (term230 A B x a b)).
Proof. exact (MK_COMB (@lem47257 A B x y a b) (@lem47258 A B x a b)). Qed.
Lemma lem47260 {A B : Type'} (y : B) (x : A) (a : A) (b : B) : ((term228 A B x a b y) = (term229 A B x a b)) = ((term226 A B x y a b) = (term230 A B x a b)).
Proof. exact (TRANS (@lem47254 A B y x a b) (@lem47259 A B y x a b)). Qed.
Lemma lem47261 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term27 A B x a y b) : (term226 A B x y a b) = (term230 A B x a b).
Proof. exact (EQ_MP (@lem47260 A B y x a b) (@lem47251 A B x a y b h1)). Qed.
Lemma lem47262 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : term230 A B x a b.
Proof. exact (EQ_MP (@lem47261 A B x a y b h2) (@lem47231 A B x y a b h1)). Qed.
Lemma lem47276 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term27 A B x a y b) : x = a.
Proof. exact (proj1 (@lem47199 A B x a y b h1)). Qed.
Lemma lem47291 {A B : Type'} (a : A) (b : B) : (term233 A B a b) = (term233 A B a b).
Proof. exact (eq_refl (term233 A B a b)). Qed.
Lemma lem47292 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term27 A B x a y b) : (term234 A B a b x) = (term235 A B b a).
Proof. exact (MK_COMB (@lem47291 A B a b) (@lem47276 A B x a y b h1)). Qed.
Lemma lem47293 {A B : Type'} (a : A) (b : B) : (term235 A B b a) = (term236 A B a b).
Proof. exact (eq_refl (term235 A B b a)). Qed.
Lemma lem47294 {A B : Type'} (a : A) (b : B) (x : A) : (term237 A B a b x) = (term237 A B a b x).
Proof. exact (eq_refl (term237 A B a b x)). Qed.
Lemma lem47295 {A B : Type'} (x : A) (a : A) (b : B) : ((term234 A B a b x) = (term235 A B b a)) = ((term234 A B a b x) = (term236 A B a b)).
Proof. exact (MK_COMB (@lem47294 A B a b x) (@lem47293 A B a b)). Qed.
Lemma lem47296 {A B : Type'} (x : A) (a : A) (b : B) : (term234 A B a b x) = (term230 A B x a b).
Proof. exact (eq_refl (term234 A B a b x)). Qed.
Lemma lem47297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem47298 {A B : Type'} (x : A) (a : A) (b : B) : (term237 A B a b x) = (term238 A B x a b).
Proof. exact (MK_COMB (@lem47297) (@lem47296 A B x a b)). Qed.
Lemma lem47299 {A B : Type'} (a : A) (b : B) : (term236 A B a b) = (term236 A B a b).
Proof. exact (eq_refl (term236 A B a b)). Qed.
Lemma lem47300 {A B : Type'} (x : A) (a : A) (b : B) : ((term234 A B a b x) = (term236 A B a b)) = ((term230 A B x a b) = (term236 A B a b)).
Proof. exact (MK_COMB (@lem47298 A B x a b) (@lem47299 A B a b)). Qed.
Lemma lem47301 {A B : Type'} (x : A) (a : A) (b : B) : ((term234 A B a b x) = (term235 A B b a)) = ((term230 A B x a b) = (term236 A B a b)).
Proof. exact (TRANS (@lem47295 A B x a b) (@lem47300 A B x a b)). Qed.
Lemma lem47302 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term27 A B x a y b) : (term230 A B x a b) = (term236 A B a b).
Proof. exact (EQ_MP (@lem47301 A B x a b) (@lem47292 A B x a y b h1)). Qed.
Lemma lem47303 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : term236 A B a b.
Proof. exact (EQ_MP (@lem47302 A B x a y b h2) (@lem47262 A B x a y b h1 h2)). Qed.
Lemma lem47326 {A B : Type'} (x : prod A B) : x = x.
Proof. exact (@lem21386 (prod A B) x). Qed.
Lemma lem47327 {A B : Type'} (x : prod A B) : x = x.
Proof. exact (@lem47326 A B x). Qed.
Lemma lem47328 {A B : Type'} (a : A) (b : B) : (@pair A B a b) = (@pair A B a b).
Proof. exact (@lem47327 A B (@pair A B a b)). Qed.
Lemma lem47329 {A B : Type'} (a : A) (b : B) : term239 A B a b.
Proof. exact (fun h0 : term236 A B a b => @lem47328 A B a b). Qed.
Lemma lem47331 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem47332 {A B : Type'} (a : A) (b : B) : (term239 A B a b) = ((@pair A B a b) = (@pair A B a b)).
Proof. exact (@lem47331 ((@pair A B a b) = (@pair A B a b))). Qed.
Lemma lem47333 {A B : Type'} (a : A) (b : B) : (@pair A B a b) = (@pair A B a b).
Proof. exact (EQ_MP (@lem47332 A B a b) (@lem47329 A B a b)). Qed.
Lemma lem47336 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem47338 {A B : Type'} (a : A) (b : B) : (term236 A B a b) = (term240 A B a b).
Proof. exact (@lem47336 ((@pair A B a b) = (@pair A B a b))). Qed.
Lemma lem47341 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : term240 A B a b.
Proof. exact (EQ_MP (@lem47338 A B a b) (@lem47303 A B x a y b h1 h2)). Qed.
Lemma lem47344 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : False.
Proof. exact (@lem47341 A B x a y b h1 h2 (@lem47333 A B a b)). Qed.
Lemma lem47345 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : term188.
Proof. exact (fun h0 : ~ False => @lem47344 A B x a y b h1 h2). Qed.
Lemma lem47347 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem47348 : term188 = False.
Proof. exact (@lem47347 False). Qed.
Lemma lem47351 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : False.
Proof. exact (EQ_MP (@lem47348) (@lem47345 A B x a y b h1 h2)). Qed.
Lemma lem47352 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : (term226 A B x y a b) = False.
Proof. exact (prop_ext (fun h3 : term226 A B x y a b => @lem47351 A B x a y b h1 h2) (fun h3 : False => @lem47231 A B x y a b h1)). Qed.
Lemma lem47353 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : False.
Proof. exact (EQ_MP (@lem47352 A B x a y b h1 h2) (@lem47231 A B x y a b h1)). Qed.
Lemma lem47354 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : (term226 A B x y a b) = False.
Proof. exact (prop_ext (fun h3 : term226 A B x y a b => @lem47353 A B x a y b h1 h2) (fun h3 : False => @lem47221 A B x y a b h1)). Qed.
Lemma lem47355 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : False.
Proof. exact (EQ_MP (@lem47354 A B x a y b h1 h2) (@lem47221 A B x y a b h1)). Qed.
Lemma lem47356 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : (term226 A B x y a b) = False.
Proof. exact (prop_ext (fun h3 : term226 A B x y a b => @lem47355 A B x a y b h1 h2) (fun h3 : False => @lem47221 A B x y a b h1)). Qed.
Lemma lem47357 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : False.
Proof. exact (EQ_MP (@lem47356 A B x a y b h1 h2) (@lem47221 A B x y a b h1)). Qed.
Lemma lem47358 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : (term226 A B x y a b) = False.
Proof. exact (prop_ext (fun h3 : term226 A B x y a b => @lem47357 A B x a y b h1 h2) (fun h3 : False => @lem47215 A B x y a b h1)). Qed.
Lemma lem47359 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : False.
Proof. exact (EQ_MP (@lem47358 A B x a y b h1 h2) (@lem47215 A B x y a b h1)). Qed.
Lemma lem47360 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : (term27 A B x a y b) = False.
Proof. exact (prop_ext (fun h3 : term27 A B x a y b => @lem47359 A B x a y b h1 h2) (fun h3 : False => @lem47199 A B x a y b h2)). Qed.
Lemma lem47361 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : False.
Proof. exact (EQ_MP (@lem47360 A B x a y b h1 h2) (@lem47199 A B x a y b h2)). Qed.
Lemma lem47362 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : (term226 A B x y a b) = False.
Proof. exact (prop_ext (fun h3 : term226 A B x y a b => @lem47361 A B x a y b h1 h2) (fun h3 : False => @lem47185 A B x y a b h1)). Qed.
Lemma lem47363 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : False.
Proof. exact (EQ_MP (@lem47362 A B x a y b h1 h2) (@lem47185 A B x y a b h1)). Qed.
Lemma lem47364 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : (term27 A B x a y b) = False.
Proof. exact (prop_ext (fun h3 : term27 A B x a y b => @lem47363 A B x a y b h1 h2) (fun h3 : False => @lem47179 A B x a y b h2)). Qed.
Lemma lem47365 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : False.
Proof. exact (EQ_MP (@lem47364 A B x a y b h1 h2) (@lem47179 A B x a y b h2)). Qed.
Lemma lem47366 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : (term226 A B x y a b) = False.
Proof. exact (prop_ext (fun h3 : term226 A B x y a b => @lem47365 A B x a y b h1 h2) (fun h3 : False => @lem47169 A B x y a b h1)). Qed.
Lemma lem47367 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term226 A B x y a b) (h2 : term27 A B x a y b) : False.
Proof. exact (EQ_MP (@lem47366 A B x a y b h1 h2) (@lem47169 A B x y a b h1)). Qed.
Lemma lem47368 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term27 A B x a y b) : term225 A B x y a b.
Proof. exact (fun h0 : term226 A B x y a b => @lem47367 A B x a y b h0 h1). Qed.
Lemma lem47369 {A B : Type'} (x : A) (a : A) (y : B) (b : B) (h1 : term27 A B x a y b) : (@pair A B x y) = (@pair A B a b).
Proof. exact (EQ_MP (@lem47168 A B x y a b) (@lem47368 A B x a y b h1)). Qed.
Lemma lem47370 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : term202 A B x y a b.
Proof. exact (fun h0 : term27 A B x a y b => @lem47369 A B x a y b h0). Qed.
Lemma lem47375 {A B : Type'} (y : B) (a : A) (b : B) : term212 A B y a b.
Proof. exact (fun x : A => @lem47370 A B x y a b). Qed.
Lemma lem47380 {A B : Type'} (a : A) (b : B) : term216 A B a b.
Proof. exact (fun y : B => @lem47375 A B y a b). Qed.
Lemma lem47385 {A B : Type'} (b : B) : term220 A B b.
Proof. exact (fun a : A => @lem47380 A B a b). Qed.
Lemma lem47390 {A B : Type'} : term224 A B.
Proof. exact (fun b : B => @lem47385 A B b). Qed.
Lemma lem47391 {A B : Type'} : term223 A B.
Proof. exact (EQ_MP (@lem47163 A B) (@lem47390 A B)). Qed.
Lemma lem47392 {A B : Type'} (b : B) : term241 A B b.
Proof. exact (@lem47391 A B b). Qed.
Lemma lem47393 {A B : Type'} (b : B) : (term241 A B b) = (term219 A B b).
Proof. exact (eq_refl (term241 A B b)). Qed.
Lemma lem47394 {A B : Type'} (b : B) : term219 A B b.
Proof. exact (EQ_MP (@lem47393 A B b) (@lem47392 A B b)). Qed.
Lemma lem47395 {A B : Type'} (b : B) (a : A) : term242 A B b a.
Proof. exact (@lem47394 A B b a). Qed.
Lemma lem47396 {A B : Type'} (a : A) (b : B) : (term242 A B b a) = (term215 A B a b).
Proof. exact (eq_refl (term242 A B b a)). Qed.
Lemma lem47397 {A B : Type'} (a : A) (b : B) : term215 A B a b.
Proof. exact (EQ_MP (@lem47396 A B a b) (@lem47395 A B b a)). Qed.
Lemma lem47398 {A B : Type'} (a : A) (b : B) (y : B) : term243 A B a b y.
Proof. exact (@lem47397 A B a b y). Qed.
Lemma lem47399 {A B : Type'} (y : B) (a : A) (b : B) : (term243 A B a b y) = (term211 A B y a b).
Proof. exact (eq_refl (term243 A B a b y)). Qed.
Lemma lem47400 {A B : Type'} (y : B) (a : A) (b : B) : term211 A B y a b.
Proof. exact (EQ_MP (@lem47399 A B y a b) (@lem47398 A B a b y)). Qed.
Lemma lem47401 {A B : Type'} (y : B) (a : A) (b : B) (x : A) : term244 A B y a b x.
Proof. exact (@lem47400 A B y a b x). Qed.
Lemma lem47402 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term244 A B y a b x) = (term203 A B x y a b).
Proof. exact (eq_refl (term244 A B y a b x)). Qed.
Lemma lem47403 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : term203 A B x y a b.
Proof. exact (EQ_MP (@lem47402 A B x y a b) (@lem47401 A B y a b x)). Qed.
Lemma lem47405 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : term203 A B x y a b.
Proof. exact (@lem47051 A B x y a b (@lem47403 A B x y a b)). Qed.
Lemma lem47406 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term204 A B x y a b) : False.
Proof. exact (@lem47405 A B x y a b (@lem47035 A B x y a b h1)). Qed.
Lemma lem47407 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term204 A B x y a b) : (term204 A B x y a b) = False.
Proof. exact (prop_ext (fun h2 : term204 A B x y a b => @lem47406 A B x y a b h1) (fun h2 : False => @lem47035 A B x y a b h1)). Qed.
Lemma lem47408 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : term204 A B x y a b) : False.
Proof. exact (EQ_MP (@lem47407 A B x y a b h1) (@lem47035 A B x y a b h1)). Qed.
Lemma lem47409 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : term203 A B x y a b.
Proof. exact (fun h0 : term204 A B x y a b => @lem47408 A B x y a b h0). Qed.
Lemma lem47410 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : term202 A B x y a b.
Proof. exact (EQ_MP (@lem47034 A B x y a b) (@lem47409 A B x y a b)). Qed.
Lemma lem47411 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term35 A B x a y b.
Proof. exact (EQ_MP (@lem45780 A B x a y b) (@lem47030 A B x a y b)). Qed.
Lemma lem47412 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term34 A B x a y b.
Proof. exact (EQ_MP (@lem45581 A B x a y b) (@lem47411 A B x a y b)). Qed.
Lemma lem47413 {A B : Type'} (x : A) (y : B) (a : A) (b : B) (h1 : (term22 A B x y) = (term22 A B a b)) : term27 A B x a y b.
Proof. exact (@lem47412 A B x a y b (@lem45548 A B x y a b h1)). Qed.
Lemma lem47414 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term29 A B x a y b.
Proof. exact (fun h0 : (term22 A B x y) = (term22 A B a b) => @lem47413 A B x y a b h0). Qed.
Lemma lem47415 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term28 A B x a y b.
Proof. exact (EQ_MP (@lem45546 A B x a y b) (@lem47414 A B x a y b)). Qed.
Lemma lem47416 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : term245 A B x y a b.
Proof. exact (conj (@lem47415 A B x a y b) (@lem47410 A B x y a b)). Qed.
Lemma lem47417 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term245 A B x y a b) = (((@pair A B x y) = (@pair A B a b)) = (term27 A B x a y b)).
Proof. exact (@lem32 ((@pair A B x y) = (@pair A B a b)) (term27 A B x a y b)). Qed.
Lemma lem47418 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term27 A B x a y b).
Proof. exact (EQ_MP (@lem47417 A B x a y b) (@lem47416 A B x y a b)). Qed.
Lemma lem47423 {A B : Type'} (x : A) (a : A) (y : B) : term246 A B x a y.
Proof. exact (fun b : B => @lem47418 A B x a y b). Qed.
Lemma lem47428 {A B : Type'} (x : A) (y : B) : term247 A B x y.
Proof. exact (fun a : A => @lem47423 A B x a y). Qed.
Lemma lem47433 {A B : Type'} (x : A) : term248 A B x.
Proof. exact (fun y : B => @lem47428 A B x y). Qed.
Lemma lem47438 {A B : Type'} : term249 A B.
Proof. exact (fun x : A => @lem47433 A B x). Qed.
