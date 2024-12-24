Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUP_EQ_INF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_EMPTY_spec.
Require Import INF_spec.
Require Import INF_INSERT_FINITE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ABS_BOUNDS_spec.
Require Import SUP_spec.
Require Import SUP_INSERT_FINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339379_spec.
Require Import thm15249_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5259531 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5259532 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5259533 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5259532 t1) (@lem5259531 t1)). Qed.
Lemma lem5259534 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5259533 t1 t2). Qed.
Lemma lem5259535 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5259536 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5259535 t1 t2) (@lem5259534 t1 t2)). Qed.
Lemma lem5259537 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5259536 t1 t2 t3). Qed.
Lemma lem5259538 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5259539 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5259538 t1 t2 t3) (@lem5259537 t1 t2 t3)). Qed.
Lemma lem5259540 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5259539 t1 t2 t3)). Qed.
Lemma lem5259543 (x : real) (y : real) (h1 : (term7 y x) = (x = y)) : (term7 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem5259544 (x : real) (y : real) (h1 : (term7 y x) = (x = y)) : (x = y) = (term7 y x).
Proof. exact (SYM (@lem5259543 x y h1)). Qed.
Lemma lem5259545 (y : real) (x : real) (h1 : (x = y) = (term7 y x)) : (x = y) = (term7 y x).
Proof. exact (h1). Qed.
Lemma lem5259546 (y : real) (x : real) (h1 : (x = y) = (term7 y x)) : (term7 y x) = (x = y).
Proof. exact (SYM (@lem5259545 y x h1)). Qed.
Lemma lem5259547 (y : real) (x : real) : ((term7 y x) = (x = y)) = ((x = y) = (term7 y x)).
Proof. exact (prop_ext (fun h1 : (term7 y x) = (x = y) => @lem5259544 x y h1) (fun h1 : (x = y) = (term7 y x) => @lem5259546 y x h1)). Qed.
Lemma lem5259548 (x : real) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : real => @lem5259547 y x)). Qed.
Lemma lem5259549 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5259550 (x : real) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem5259549) (@lem5259548 x)). Qed.
Lemma lem5259551 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem5259550 x)). Qed.
Lemma lem5259552 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5259553 : term14 = term15.
Proof. exact (MK_COMB (@lem5259552) (@lem5259551)). Qed.
Lemma lem5259554 : term15.
Proof. exact (EQ_MP (@lem5259553) (@lem1339379)). Qed.
Lemma lem5259572 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term16 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5259573 {_117066 : Type'} (s : _117066 -> Prop) (t : _117066 -> Prop) : (s = t) = (term16 _117066 s t).
Proof. exact (@lem5259572 _117066 s t). Qed.
Lemma lem5259574 {_117066 : Type'} (s : _117066 -> Prop) : (s = (@EMPTY _117066)) = (term17 _117066 s).
Proof. exact (@lem5259573 _117066 s (@EMPTY _117066)). Qed.
Lemma lem5259583 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5259584 {_117066 : Type'} (s : _117066 -> Prop) : (term18 _117066 s) = (term19 _117066 s).
Proof. exact (MK_COMB (@lem5259583) (@lem5259574 _117066 s)). Qed.
Lemma lem5259585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5259586 {_117066 : Type'} (s : _117066 -> Prop) : (term20 _117066 s) = (term21 _117066 s).
Proof. exact (MK_COMB (@lem5259585) (@lem5259584 _117066 s)). Qed.
Lemma lem5259597 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term22 _117066 s a) = (term22 _117066 s a).
Proof. exact (eq_refl (term22 _117066 s a)). Qed.
Lemma lem5259598 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term23 _117066 s a) = (term24 _117066 s a).
Proof. exact (MK_COMB (@lem5259586 _117066 s) (@lem5259597 _117066 s a)). Qed.
Lemma lem5259601 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5259602 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term25 _117066 s a) = (term26 _117066 s a).
Proof. exact (MK_COMB (@lem5259601) (@lem5259598 _117066 s a)). Qed.
Lemma lem5259606 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term16 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5259607 {_117066 : Type'} (s : _117066 -> Prop) (t : _117066 -> Prop) : (s = t) = (term16 _117066 s t).
Proof. exact (@lem5259606 _117066 s t). Qed.
Lemma lem5259608 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (s = (@INSERT _117066 a (@EMPTY _117066))) = (term27 _117066 s a).
Proof. exact (@lem5259607 _117066 s (@INSERT _117066 a (@EMPTY _117066))). Qed.
Lemma lem5259617 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term28 _117066 s a) = (term29 _117066 s a).
Proof. exact (MK_COMB (@lem5259602 _117066 s a) (@lem5259608 _117066 s a)). Qed.
Lemma lem5259620 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term29 _117066 s a) = (term28 _117066 s a).
Proof. exact (SYM (@lem5259617 _117066 s a)). Qed.
Lemma lem5259632 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5259633 {_117066 : Type'} (P : _117066 -> Prop) (x : _117066) : (@IN _117066 x P) = (P x).
Proof. exact (@lem5259632 _117066 P x). Qed.
Lemma lem5259634 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (@IN _117066 x s) = (s x).
Proof. exact (@lem5259633 _117066 s x). Qed.
Lemma lem5259635 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5259636 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term30 _117066 x s) = (term31 _117066 s x).
Proof. exact (MK_COMB (@lem5259635) (@lem5259634 _117066 s x)). Qed.
Lemma lem5259638 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5259639 {_117066 : Type'} (x : _117066) : (@IN _117066 x (@EMPTY _117066)) = False.
Proof. exact (@lem5259638 _117066 x). Qed.
Lemma lem5259640 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : ((@IN _117066 x s) = (@IN _117066 x (@EMPTY _117066))) = ((s x) = False).
Proof. exact (MK_COMB (@lem5259636 _117066 s x) (@lem5259639 _117066 x)). Qed.
Lemma lem5259642 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5259643 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : ((s x) = False) = (term32 _117066 s x).
Proof. exact (@lem5259642 (s x)). Qed.
Lemma lem5259644 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : ((@IN _117066 x s) = (@IN _117066 x (@EMPTY _117066))) = (term32 _117066 s x).
Proof. exact (TRANS (@lem5259640 _117066 s x) (@lem5259643 _117066 s x)). Qed.
Lemma lem5259645 {_117066 : Type'} (s : _117066 -> Prop) : (term33 _117066 s) = (term34 _117066 s).
Proof. exact (fun_ext (fun x : _117066 => @lem5259644 _117066 s x)). Qed.
Lemma lem5259646 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5259647 {_117066 : Type'} (s : _117066 -> Prop) : (term17 _117066 s) = (term35 _117066 s).
Proof. exact (MK_COMB (@lem5259646 _117066) (@lem5259645 _117066 s)). Qed.
Lemma lem5259652 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5259653 {_117066 : Type'} (s : _117066 -> Prop) : (term19 _117066 s) = (term36 _117066 s).
Proof. exact (MK_COMB (@lem5259652) (@lem5259647 _117066 s)). Qed.
Lemma lem5259654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5259655 {_117066 : Type'} (s : _117066 -> Prop) : (term21 _117066 s) = (term37 _117066 s).
Proof. exact (MK_COMB (@lem5259654) (@lem5259653 _117066 s)). Qed.
Lemma lem5259663 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5259664 {_117066 : Type'} (P : _117066 -> Prop) (x : _117066) : (@IN _117066 x P) = (P x).
Proof. exact (@lem5259663 _117066 P x). Qed.
Lemma lem5259665 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (@IN _117066 x s) = (s x).
Proof. exact (@lem5259664 _117066 s x). Qed.
Lemma lem5259666 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5259667 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term38 _117066 x s) = (term39 _117066 s x).
Proof. exact (MK_COMB (@lem5259666) (@lem5259665 _117066 s x)). Qed.
Lemma lem5259670 {_117066 : Type'} (x : _117066) (a : _117066) : (x = a) = (x = a).
Proof. exact (eq_refl (x = a)). Qed.
Lemma lem5259671 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : (term40 _117066 s x a) = (term41 _117066 s x a).
Proof. exact (MK_COMB (@lem5259667 _117066 s x) (@lem5259670 _117066 x a)). Qed.
Lemma lem5259674 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term42 _117066 s a) = (term43 _117066 s a).
Proof. exact (fun_ext (fun x : _117066 => @lem5259671 _117066 s x a)). Qed.
Lemma lem5259675 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5259676 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term22 _117066 s a) = (term44 _117066 s a).
Proof. exact (MK_COMB (@lem5259675 _117066) (@lem5259674 _117066 s a)). Qed.
Lemma lem5259681 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term24 _117066 s a) = (term45 _117066 s a).
Proof. exact (MK_COMB (@lem5259655 _117066 s) (@lem5259676 _117066 s a)). Qed.
Lemma lem5259684 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5259685 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term26 _117066 s a) = (term46 _117066 s a).
Proof. exact (MK_COMB (@lem5259684) (@lem5259681 _117066 s a)). Qed.
Lemma lem5259693 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5259694 {_117066 : Type'} (P : _117066 -> Prop) (x : _117066) : (@IN _117066 x P) = (P x).
Proof. exact (@lem5259693 _117066 P x). Qed.
Lemma lem5259695 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (@IN _117066 x s) = (s x).
Proof. exact (@lem5259694 _117066 s x). Qed.
Lemma lem5259696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5259697 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term30 _117066 x s) = (term31 _117066 s x).
Proof. exact (MK_COMB (@lem5259696) (@lem5259695 _117066 s x)). Qed.
Lemma lem5259699 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term47 A x y s) = (term48 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5259700 {_117066 : Type'} (y : _117066) (x : _117066) (s : _117066 -> Prop) : (term47 _117066 x y s) = (term48 _117066 y x s).
Proof. exact (@lem5259699 _117066 y x s). Qed.
Lemma lem5259701 {_117066 : Type'} (a : _117066) (x : _117066) : (term49 _117066 x a) = (term50 _117066 a x).
Proof. exact (@lem5259700 _117066 a x (@EMPTY _117066)). Qed.
Lemma lem5259707 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5259708 {_117066 : Type'} (x : _117066) : (@IN _117066 x (@EMPTY _117066)) = False.
Proof. exact (@lem5259707 _117066 x). Qed.
Lemma lem5259709 {_117066 : Type'} (x : _117066) (a : _117066) : (term51 _117066 x a) = (term51 _117066 x a).
Proof. exact (eq_refl (term51 _117066 x a)). Qed.
Lemma lem5259710 {_117066 : Type'} (x : _117066) (a : _117066) : (term50 _117066 a x) = (term52 _117066 x a).
Proof. exact (MK_COMB (@lem5259709 _117066 x a) (@lem5259708 _117066 x)). Qed.
Lemma lem5259712 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5259713 {_117066 : Type'} (x : _117066) (a : _117066) : (term52 _117066 x a) = (x = a).
Proof. exact (@lem5259712 (x = a)). Qed.
Lemma lem5259716 {_117066 : Type'} (x : _117066) (a : _117066) : (term50 _117066 a x) = (x = a).
Proof. exact (TRANS (@lem5259710 _117066 x a) (@lem5259713 _117066 x a)). Qed.
Lemma lem5259717 {_117066 : Type'} (x : _117066) (a : _117066) : (term49 _117066 x a) = (x = a).
Proof. exact (TRANS (@lem5259701 _117066 a x) (@lem5259716 _117066 x a)). Qed.
Lemma lem5259718 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : ((@IN _117066 x s) = (term49 _117066 x a)) = ((s x) = (x = a)).
Proof. exact (MK_COMB (@lem5259697 _117066 s x) (@lem5259717 _117066 x a)). Qed.
Lemma lem5259721 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term53 _117066 s a) = (term54 _117066 s a).
Proof. exact (fun_ext (fun x : _117066 => @lem5259718 _117066 s x a)). Qed.
Lemma lem5259722 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5259723 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term27 _117066 s a) = (term55 _117066 s a).
Proof. exact (MK_COMB (@lem5259722 _117066) (@lem5259721 _117066 s a)). Qed.
Lemma lem5259728 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term29 _117066 s a) = (term56 _117066 s a).
Proof. exact (MK_COMB (@lem5259685 _117066 s a) (@lem5259723 _117066 s a)). Qed.
Lemma lem5259731 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term56 _117066 s a) = (term29 _117066 s a).
Proof. exact (SYM (@lem5259728 _117066 s a)). Qed.
Lemma lem5259733 (p : Prop) : p = (term57 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5259734 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term56 _117066 s a) = (term58 _117066 s a).
Proof. exact (@lem5259733 (term56 _117066 s a)). Qed.
Lemma lem5259735 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term58 _117066 s a) = (term56 _117066 s a).
Proof. exact (SYM (@lem5259734 _117066 s a)). Qed.
Lemma lem5259736 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term59 _117066 s a) : term59 _117066 s a.
Proof. exact (h1). Qed.
Lemma lem5259739 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term58 _117066 s a) : term58 _117066 s a.
Proof. exact (h1). Qed.
Lemma lem5259740 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term60 _117066 s a.
Proof. exact (fun h0 : term58 _117066 s a => @lem5259739 _117066 s a h0). Qed.
Lemma lem5259741 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term60 _117066 s a) : term60 _117066 s a.
Proof. exact (h1). Qed.
Lemma lem5259742 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term58 _117066 s a) : term58 _117066 s a.
Proof. exact (h1). Qed.
Lemma lem5259743 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term58 _117066 s a) (h2 : term60 _117066 s a) : term58 _117066 s a.
Proof. exact (@lem5259741 _117066 s a h2 (@lem5259742 _117066 s a h1)). Qed.
Lemma lem5259744 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term58 _117066 s a) : term61 _117066 s a.
Proof. exact (fun h0 : term60 _117066 s a => @lem5259743 _117066 s a h1 h0). Qed.
Lemma lem5259745 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term60 _117066 s a) : term60 _117066 s a.
Proof. exact (h1). Qed.
Lemma lem5259746 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term58 _117066 s a) (h2 : term60 _117066 s a) : term58 _117066 s a.
Proof. exact (@lem5259744 _117066 s a h1 (@lem5259745 _117066 s a h2)). Qed.
Lemma lem5259747 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term60 _117066 s a) : term60 _117066 s a.
Proof. exact (fun h0 : term58 _117066 s a => @lem5259746 _117066 s a h0 h1). Qed.
Lemma lem5259748 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term62 _117066 s a.
Proof. exact (fun h0 : term60 _117066 s a => @lem5259747 _117066 s a h0). Qed.
Lemma lem5259751 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term60 _117066 s a.
Proof. exact (@lem5259748 _117066 s a (@lem5259740 _117066 s a)). Qed.
Lemma lem5259752 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term60 _117066 s a.
Proof. exact (@lem5259751 _117066 s a). Qed.
Lemma lem5259762 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5259763 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term58 _117066 s a) = (term63 _117066 s a).
Proof. exact (@lem5259762 (term59 _117066 s a)). Qed.
Lemma lem5259765 (t : Prop) : (term64 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5259766 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term63 _117066 s a) = (term56 _117066 s a).
Proof. exact (@lem5259765 (term56 _117066 s a)). Qed.
Lemma lem5259769 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term58 _117066 s a) = (term56 _117066 s a).
Proof. exact (TRANS (@lem5259763 _117066 s a) (@lem5259766 _117066 s a)). Qed.
Lemma lem5259786 {_117066 : Type'} (a : _117066) : (term65 _117066 a) = (term66 _117066 a).
Proof. exact (fun_ext (fun s : _117066 -> Prop => @lem5259769 _117066 s a)). Qed.
Lemma lem5259787 {_117066 : Type'} : (@all (_117066 -> Prop)) = (@all (_117066 -> Prop)).
Proof. exact (eq_refl (@all (_117066 -> Prop))). Qed.
Lemma lem5259788 {_117066 : Type'} (a : _117066) : (term67 _117066 a) = (term68 _117066 a).
Proof. exact (MK_COMB (@lem5259787 _117066) (@lem5259786 _117066 a)). Qed.
Lemma lem5259793 {_117066 : Type'} : (term69 _117066) = (term70 _117066).
Proof. exact (fun_ext (fun a : _117066 => @lem5259788 _117066 a)). Qed.
Lemma lem5259794 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5259803 {_117066 : Type'} : (term71 _117066) = (term72 _117066).
Proof. exact (MK_COMB (@lem5259794 _117066) (@lem5259793 _117066)). Qed.
Lemma lem5259808 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : ((s x) = (x = a)) = ((s x) = (x = a)).
Proof. exact (eq_refl ((s x) = (x = a))). Qed.
Lemma lem5259809 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term54 _117066 s a) = (term54 _117066 s a).
Proof. exact (fun_ext (fun x : _117066 => @lem5259808 _117066 s x a)). Qed.
Lemma lem5259810 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5259811 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term55 _117066 s a) = (term55 _117066 s a).
Proof. exact (MK_COMB (@lem5259810 _117066) (@lem5259809 _117066 s a)). Qed.
Lemma lem5259816 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : (term41 _117066 s x a) = (term41 _117066 s x a).
Proof. exact (eq_refl (term41 _117066 s x a)). Qed.
Lemma lem5259817 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term43 _117066 s a) = (term43 _117066 s a).
Proof. exact (fun_ext (fun x : _117066 => @lem5259816 _117066 s x a)). Qed.
Lemma lem5259818 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5259819 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term44 _117066 s a) = (term44 _117066 s a).
Proof. exact (MK_COMB (@lem5259818 _117066) (@lem5259817 _117066 s a)). Qed.
Lemma lem5259822 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term32 _117066 s x) = (term32 _117066 s x).
Proof. exact (eq_refl (term32 _117066 s x)). Qed.
Lemma lem5259823 {_117066 : Type'} (s : _117066 -> Prop) : (term34 _117066 s) = (term34 _117066 s).
Proof. exact (fun_ext (fun x : _117066 => @lem5259822 _117066 s x)). Qed.
Lemma lem5259824 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5259825 {_117066 : Type'} (s : _117066 -> Prop) : (term35 _117066 s) = (term35 _117066 s).
Proof. exact (MK_COMB (@lem5259824 _117066) (@lem5259823 _117066 s)). Qed.
Lemma lem5259826 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5259827 {_117066 : Type'} (s : _117066 -> Prop) : (term36 _117066 s) = (term36 _117066 s).
Proof. exact (MK_COMB (@lem5259826) (@lem5259825 _117066 s)). Qed.
Lemma lem5259828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5259829 {_117066 : Type'} (s : _117066 -> Prop) : (term37 _117066 s) = (term37 _117066 s).
Proof. exact (MK_COMB (@lem5259828) (@lem5259827 _117066 s)). Qed.
Lemma lem5259830 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term45 _117066 s a) = (term45 _117066 s a).
Proof. exact (MK_COMB (@lem5259829 _117066 s) (@lem5259819 _117066 s a)). Qed.
Lemma lem5259831 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5259832 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term46 _117066 s a) = (term46 _117066 s a).
Proof. exact (MK_COMB (@lem5259831) (@lem5259830 _117066 s a)). Qed.
Lemma lem5259833 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term56 _117066 s a) = (term56 _117066 s a).
Proof. exact (MK_COMB (@lem5259832 _117066 s a) (@lem5259811 _117066 s a)). Qed.
Lemma lem5259834 {_117066 : Type'} (a : _117066) : (term66 _117066 a) = (term66 _117066 a).
Proof. exact (fun_ext (fun s : _117066 -> Prop => @lem5259833 _117066 s a)). Qed.
Lemma lem5259835 {_117066 : Type'} : (@all (_117066 -> Prop)) = (@all (_117066 -> Prop)).
Proof. exact (eq_refl (@all (_117066 -> Prop))). Qed.
Lemma lem5259836 {_117066 : Type'} (a : _117066) : (term68 _117066 a) = (term68 _117066 a).
Proof. exact (MK_COMB (@lem5259835 _117066) (@lem5259834 _117066 a)). Qed.
Lemma lem5259837 {_117066 : Type'} : (term70 _117066) = (term70 _117066).
Proof. exact (fun_ext (fun a : _117066 => @lem5259836 _117066 a)). Qed.
Lemma lem5259838 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5259839 {_117066 : Type'} : (term72 _117066) = (term72 _117066).
Proof. exact (MK_COMB (@lem5259838 _117066) (@lem5259837 _117066)). Qed.
Lemma lem5259878 {_117066 : Type'} : (term71 _117066) = (term72 _117066).
Proof. exact (TRANS (@lem5259803 _117066) (@lem5259839 _117066)). Qed.
Lemma lem5259879 {_117066 : Type'} : (term72 _117066) = (term71 _117066).
Proof. exact (SYM (@lem5259878 _117066)). Qed.
Lemma lem5259880 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term45 _117066 s a) : term45 _117066 s a.
Proof. exact (h1). Qed.
Lemma lem5259882 (p : Prop) : p = (term57 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5259883 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : ((s x) = (x = a)) = (term73 _117066 s x a).
Proof. exact (@lem5259882 ((s x) = (x = a))). Qed.
Lemma lem5259884 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : (term73 _117066 s x a) = ((s x) = (x = a)).
Proof. exact (SYM (@lem5259883 _117066 s x a)). Qed.
Lemma lem5259885 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term74 _117066 s x a) : term74 _117066 s x a.
Proof. exact (h1). Qed.
Lemma lem5259888 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term75 _117066 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem5259889 {_117066 : Type'} (P : _117066 -> Prop) : (term76 _117066 P) = (term77 _117066 P).
Proof. exact (@lem18392 _117066 P). Qed.
Lemma lem5259890 {_117066 : Type'} (s : _117066 -> Prop) : (term36 _117066 s) = (term78 _117066 s).
Proof. exact (@lem5259889 _117066 (term34 _117066 s)). Qed.
Lemma lem5259891 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term79 _117066 s x) = (term32 _117066 s x).
Proof. exact (eq_refl (term79 _117066 s x)). Qed.
Lemma lem5259892 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5259893 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term80 _117066 s x) = (term75 _117066 s x).
Proof. exact (MK_COMB (@lem5259892) (@lem5259891 _117066 s x)). Qed.
Lemma lem5259894 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term80 _117066 s x) = (s x).
Proof. exact (TRANS (@lem5259893 _117066 s x) (@lem5259888 _117066 s x)). Qed.
Lemma lem5259895 {_117066 : Type'} (s : _117066 -> Prop) : (term81 _117066 s) = (term82 _117066 s).
Proof. exact (fun_ext (fun x : _117066 => @lem5259894 _117066 s x)). Qed.
Lemma lem5259896 {_117066 : Type'} : (@ex _117066) = (@ex _117066).
Proof. exact (eq_refl (@ex _117066)). Qed.
Lemma lem5259897 {_117066 : Type'} (s : _117066 -> Prop) : (term78 _117066 s) = (term83 _117066 s).
Proof. exact (MK_COMB (@lem5259896 _117066) (@lem5259895 _117066 s)). Qed.
Lemma lem5259898 {_117066 : Type'} (s : _117066 -> Prop) : (term36 _117066 s) = (term83 _117066 s).
Proof. exact (TRANS (@lem5259890 _117066 s) (@lem5259897 _117066 s)). Qed.
Lemma lem5259905 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : (term41 _117066 s x a) = (term84 _117066 s x a).
Proof. exact (@lem17265 (s x) (x = a)). Qed.
Lemma lem5259906 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term43 _117066 s a) = (term85 _117066 s a).
Proof. exact (fun_ext (fun x : _117066 => @lem5259905 _117066 s x a)). Qed.
Lemma lem5259907 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5259908 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term44 _117066 s a) = (term86 _117066 s a).
Proof. exact (MK_COMB (@lem5259907 _117066) (@lem5259906 _117066 s a)). Qed.
Lemma lem5259909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5259910 {_117066 : Type'} (s : _117066 -> Prop) : (term37 _117066 s) = (term87 _117066 s).
Proof. exact (MK_COMB (@lem5259909) (@lem5259898 _117066 s)). Qed.
Lemma lem5259911 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term45 _117066 s a) = (term88 _117066 s a).
Proof. exact (MK_COMB (@lem5259910 _117066 s) (@lem5259908 _117066 s a)). Qed.
Lemma lem5259966 {A : Type'} (P : A -> Prop) (Q : Prop) : (term89 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5259967 {_117066 : Type'} (P : _117066 -> Prop) (Q : Prop) : (term89 _117066 P Q) = (term90 _117066 P Q).
Proof. exact (@lem5259966 _117066 P Q). Qed.
Lemma lem5259969 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term88 _117066 s a) = (term91 _117066 s a).
Proof. exact (@lem5259967 _117066 s (term86 _117066 s a)). Qed.
Lemma lem5259970 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term45 _117066 s a) = (term91 _117066 s a).
Proof. exact (TRANS (@lem5259911 _117066 s a) (@lem5259969 _117066 s a)). Qed.
Lemma lem5259971 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term45 _117066 s a) : term91 _117066 s a.
Proof. exact (EQ_MP (@lem5259970 _117066 s a) (@lem5259880 _117066 s a h1)). Qed.
Lemma lem5259990 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : (term74 _117066 s x a) = (term92 _117066 s x a).
Proof. exact (@lem17646 (s x) (x = a)). Qed.
Lemma lem5259992 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term93 _117066 x' s a.
Proof. exact (h1). Qed.
Lemma lem5260022 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term74 _117066 s x a) : term92 _117066 s x a.
Proof. exact (EQ_MP (@lem5259990 _117066 s x a) (@lem5259885 _117066 s x a h1)). Qed.
Lemma lem5260035 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : (term84 _117066 s x a) = (term84 _117066 s x a).
Proof. exact (eq_refl (term84 _117066 s x a)). Qed.
Lemma lem5260036 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term85 _117066 s a) = (term85 _117066 s a).
Proof. exact (fun_ext (fun x : _117066 => @lem5260035 _117066 s x a)). Qed.
Lemma lem5260037 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5260038 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term86 _117066 s a) = (term86 _117066 s a).
Proof. exact (MK_COMB (@lem5260037 _117066) (@lem5260036 _117066 s a)). Qed.
Lemma lem5260043 {_117066 : Type'} (s : _117066 -> Prop) (x' : _117066) : (term94 _117066 s x') = (term94 _117066 s x').
Proof. exact (eq_refl (term94 _117066 s x')). Qed.
Lemma lem5260044 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) : (term93 _117066 x' s a) = (term93 _117066 x' s a).
Proof. exact (MK_COMB (@lem5260043 _117066 s x') (@lem5260038 _117066 s a)). Qed.
Lemma lem5260045 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term93 _117066 x' s a.
Proof. exact (EQ_MP (@lem5260044 _117066 x' s a) (@lem5259992 _117066 x' s a h1)). Qed.
Lemma lem5260046 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term86 _117066 s a.
Proof. exact (proj2 (@lem5260045 _117066 x' s a h1)). Qed.
Lemma lem5260048 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term95 _117066 s x a) : term95 _117066 s x a.
Proof. exact (h1). Qed.
Lemma lem5260049 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term96 _117066 s x a) : term96 _117066 s x a.
Proof. exact (h1). Qed.
Lemma lem5260065 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : (term84 _117066 s x a) = (term84 _117066 s x a).
Proof. exact (eq_refl (term84 _117066 s x a)). Qed.
Lemma lem5260066 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term85 _117066 s a) = (term85 _117066 s a).
Proof. exact (fun_ext (fun x : _117066 => @lem5260065 _117066 s x a)). Qed.
Lemma lem5260067 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5260069 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term86 _117066 s a) = (term86 _117066 s a).
Proof. exact (MK_COMB (@lem5260067 _117066) (@lem5260066 _117066 s a)). Qed.
Lemma lem5260070 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term86 _117066 s a.
Proof. exact (EQ_MP (@lem5260069 _117066 s a) (@lem5260046 _117066 x' s a h1)). Qed.
Lemma lem5260090 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) : (term84 _117066 s x a) = (term84 _117066 s x a).
Proof. exact (eq_refl (term84 _117066 s x a)). Qed.
Lemma lem5260091 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term85 _117066 s a) = (term85 _117066 s a).
Proof. exact (fun_ext (fun x : _117066 => @lem5260090 _117066 s x a)). Qed.
Lemma lem5260092 {_117066 : Type'} : (@all _117066) = (@all _117066).
Proof. exact (eq_refl (@all _117066)). Qed.
Lemma lem5260094 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term86 _117066 s a) = (term86 _117066 s a).
Proof. exact (MK_COMB (@lem5260092 _117066) (@lem5260091 _117066 s a)). Qed.
Lemma lem5260095 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term86 _117066 s a.
Proof. exact (EQ_MP (@lem5260094 _117066 s a) (@lem5260046 _117066 x' s a h1)). Qed.
Lemma lem5260104 {_117066 : Type'} (_68856 : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term97 _117066 s a _68856.
Proof. exact (@lem5260070 _117066 x' s a h1 _68856). Qed.
Lemma lem5260105 {_117066 : Type'} (s : _117066 -> Prop) (_68856 : _117066) (a : _117066) : (term97 _117066 s a _68856) = (term84 _117066 s _68856 a).
Proof. exact (eq_refl (term97 _117066 s a _68856)). Qed.
Lemma lem5260107 {_117066 : Type'} (_68857 : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term97 _117066 s a _68857.
Proof. exact (@lem5260095 _117066 x' s a h1 _68857). Qed.
Lemma lem5260108 {_117066 : Type'} (s : _117066 -> Prop) (_68857 : _117066) (a : _117066) : (term97 _117066 s a _68857) = (term84 _117066 s _68857 a).
Proof. exact (eq_refl (term97 _117066 s a _68857)). Qed.
Lemma lem5260117 {_117066 : Type'} (_68856 : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term84 _117066 s _68856 a.
Proof. exact (EQ_MP (@lem5260105 _117066 s _68856 a) (@lem5260104 _117066 _68856 x' s a h1)). Qed.
Lemma lem5260121 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term95 _117066 s x a) : term98 _117066 x a.
Proof. exact (proj2 (@lem5260048 _117066 s x a h1)). Qed.
Lemma lem5260131 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term96 _117066 s x a) : term32 _117066 s x.
Proof. exact (proj1 (@lem5260049 _117066 s x a h1)). Qed.
Lemma lem5260133 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term96 _117066 s x a) : x = a.
Proof. exact (proj2 (@lem5260049 _117066 s x a h1)). Qed.
Lemma lem5260175 {_117066 : Type'} (_68857 : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term84 _117066 s _68857 a.
Proof. exact (EQ_MP (@lem5260108 _117066 s _68857 a) (@lem5260107 _117066 _68857 x' s a h1)). Qed.
Lemma lem5260176 {_117066 : Type'} (s : _117066 -> Prop) : (term34 _117066 s) = (term34 _117066 s).
Proof. exact (eq_refl (term34 _117066 s)). Qed.
Lemma lem5260177 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term96 _117066 s x a) : (term79 _117066 s x) = (term79 _117066 s a).
Proof. exact (MK_COMB (@lem5260176 _117066 s) (@lem5260133 _117066 s x a h1)). Qed.
Lemma lem5260178 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term79 _117066 s a) = (term32 _117066 s a).
Proof. exact (eq_refl (term79 _117066 s a)). Qed.
Lemma lem5260179 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term99 _117066 s x) = (term99 _117066 s x).
Proof. exact (eq_refl (term99 _117066 s x)). Qed.
Lemma lem5260180 {_117066 : Type'} (x : _117066) (s : _117066 -> Prop) (a : _117066) : ((term79 _117066 s x) = (term79 _117066 s a)) = ((term79 _117066 s x) = (term32 _117066 s a)).
Proof. exact (MK_COMB (@lem5260179 _117066 s x) (@lem5260178 _117066 s a)). Qed.
Lemma lem5260181 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term79 _117066 s x) = (term32 _117066 s x).
Proof. exact (eq_refl (term79 _117066 s x)). Qed.
Lemma lem5260182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5260183 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term99 _117066 s x) = (term100 _117066 s x).
Proof. exact (MK_COMB (@lem5260182) (@lem5260181 _117066 s x)). Qed.
Lemma lem5260184 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term32 _117066 s a) = (term32 _117066 s a).
Proof. exact (eq_refl (term32 _117066 s a)). Qed.
Lemma lem5260185 {_117066 : Type'} (x : _117066) (s : _117066 -> Prop) (a : _117066) : ((term79 _117066 s x) = (term32 _117066 s a)) = ((term32 _117066 s x) = (term32 _117066 s a)).
Proof. exact (MK_COMB (@lem5260183 _117066 s x) (@lem5260184 _117066 s a)). Qed.
Lemma lem5260186 {_117066 : Type'} (x : _117066) (s : _117066 -> Prop) (a : _117066) : ((term79 _117066 s x) = (term79 _117066 s a)) = ((term32 _117066 s x) = (term32 _117066 s a)).
Proof. exact (TRANS (@lem5260180 _117066 x s a) (@lem5260185 _117066 x s a)). Qed.
Lemma lem5260187 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term96 _117066 s x a) : (term32 _117066 s x) = (term32 _117066 s a).
Proof. exact (EQ_MP (@lem5260186 _117066 x s a) (@lem5260177 _117066 s x a h1)). Qed.
Lemma lem5260188 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term96 _117066 s x a) : term32 _117066 s a.
Proof. exact (EQ_MP (@lem5260187 _117066 s x a h1) (@lem5260131 _117066 s x a h1)). Qed.
Lemma lem5260204 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term95 _117066 s x a) : s x.
Proof. exact (proj1 (@lem5260048 _117066 s x a h1)). Qed.
Lemma lem5260205 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term95 _117066 s x a) : term101 _117066 s x.
Proof. exact (fun h0 : term32 _117066 s x => @lem5260204 _117066 s x a h1). Qed.
Lemma lem5260207 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5260208 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) : (term101 _117066 s x) = (s x).
Proof. exact (@lem5260207 (s x)). Qed.
Lemma lem5260209 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term95 _117066 s x a) : s x.
Proof. exact (EQ_MP (@lem5260208 _117066 s x) (@lem5260205 _117066 s x a h1)). Qed.
Lemma lem5260215 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5260216 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68856 : _117066) : (term84 _117066 s _68856 a) = (term103 _117066 a s _68856).
Proof. exact (@lem5260215 (_68856 = a) (term32 _117066 s _68856)). Qed.
Lemma lem5260224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5260225 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68856 : _117066) : (term104 _117066 s _68856 a) = (term105 _117066 a s _68856).
Proof. exact (MK_COMB (@lem5260224) (@lem5260216 _117066 a s _68856)). Qed.
Lemma lem5260233 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68856 : _117066) : (term103 _117066 a s _68856) = (term103 _117066 a s _68856).
Proof. exact (eq_refl (term103 _117066 a s _68856)). Qed.
Lemma lem5260234 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68856 : _117066) : ((term84 _117066 s _68856 a) = (term103 _117066 a s _68856)) = ((term103 _117066 a s _68856) = (term103 _117066 a s _68856)).
Proof. exact (MK_COMB (@lem5260225 _117066 a s _68856) (@lem5260233 _117066 a s _68856)). Qed.
Lemma lem5260236 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5260237 (x : Prop) : (x = x) = True.
Proof. exact (@lem5260236 Prop x). Qed.
Lemma lem5260238 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68856 : _117066) : ((term103 _117066 a s _68856) = (term103 _117066 a s _68856)) = True.
Proof. exact (@lem5260237 (term103 _117066 a s _68856)). Qed.
Lemma lem5260239 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68856 : _117066) : ((term84 _117066 s _68856 a) = (term103 _117066 a s _68856)) = True.
Proof. exact (TRANS (@lem5260234 _117066 a s _68856) (@lem5260238 _117066 a s _68856)). Qed.
Lemma lem5260240 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68856 : _117066) : True = ((term84 _117066 s _68856 a) = (term103 _117066 a s _68856)).
Proof. exact (SYM (@lem5260239 _117066 a s _68856)). Qed.
Lemma lem5260241 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68856 : _117066) : (term84 _117066 s _68856 a) = (term103 _117066 a s _68856).
Proof. exact (EQ_MP (@lem5260240 _117066 a s _68856) (@lem0)). Qed.
Lemma lem5260242 {_117066 : Type'} (_68856 : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term103 _117066 a s _68856.
Proof. exact (EQ_MP (@lem5260241 _117066 a s _68856) (@lem5260117 _117066 _68856 x' s a h1)). Qed.
Lemma lem5260244 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5260245 {_117066 : Type'} (s : _117066 -> Prop) (_68856 : _117066) (a : _117066) : (term103 _117066 a s _68856) = (term107 _117066 s _68856 a).
Proof. exact (@lem5260244 (term32 _117066 s _68856) (_68856 = a)). Qed.
Lemma lem5260247 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5260248 {_117066 : Type'} (s : _117066 -> Prop) (_68856 : _117066) : (term75 _117066 s _68856) = (s _68856).
Proof. exact (@lem5260247 (s _68856)). Qed.
Lemma lem5260249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260250 {_117066 : Type'} (s : _117066 -> Prop) (_68856 : _117066) : (term108 _117066 s _68856) = (term39 _117066 s _68856).
Proof. exact (MK_COMB (@lem5260249) (@lem5260248 _117066 s _68856)). Qed.
Lemma lem5260251 {_117066 : Type'} (_68856 : _117066) (a : _117066) : (_68856 = a) = (_68856 = a).
Proof. exact (eq_refl (_68856 = a)). Qed.
Lemma lem5260252 {_117066 : Type'} (s : _117066 -> Prop) (_68856 : _117066) (a : _117066) : (term107 _117066 s _68856 a) = (term41 _117066 s _68856 a).
Proof. exact (MK_COMB (@lem5260250 _117066 s _68856) (@lem5260251 _117066 _68856 a)). Qed.
Lemma lem5260253 {_117066 : Type'} (s : _117066 -> Prop) (_68856 : _117066) (a : _117066) : (term103 _117066 a s _68856) = (term41 _117066 s _68856 a).
Proof. exact (TRANS (@lem5260245 _117066 s _68856 a) (@lem5260252 _117066 s _68856 a)). Qed.
Lemma lem5260256 {_117066 : Type'} (_68856 : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term41 _117066 s _68856 a.
Proof. exact (EQ_MP (@lem5260253 _117066 s _68856 a) (@lem5260242 _117066 _68856 x' s a h1)). Qed.
Lemma lem5260257 {_117066 : Type'} (_68856 : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term41 _117066 s _68856 a.
Proof. exact (@lem5260256 _117066 _68856 x' s a h1). Qed.
Lemma lem5260258 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term41 _117066 s x a.
Proof. exact (@lem5260257 _117066 x x' s a h1). Qed.
Lemma lem5260261 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term95 _117066 s x a) (h2 : term93 _117066 x' s a) : x = a.
Proof. exact (@lem5260258 _117066 x x' s a h2 (@lem5260209 _117066 s x a h1)). Qed.
Lemma lem5260262 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term95 _117066 s x a) (h2 : term93 _117066 x' s a) : term109 _117066 x a.
Proof. exact (fun h0 : term98 _117066 x a => @lem5260261 _117066 x x' s a h1 h2). Qed.
Lemma lem5260264 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5260265 {_117066 : Type'} (x : _117066) (a : _117066) : (term109 _117066 x a) = (x = a).
Proof. exact (@lem5260264 (x = a)). Qed.
Lemma lem5260266 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term95 _117066 s x a) (h2 : term93 _117066 x' s a) : x = a.
Proof. exact (EQ_MP (@lem5260265 _117066 x a) (@lem5260262 _117066 x x' s a h1 h2)). Qed.
Lemma lem5260269 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5260271 {_117066 : Type'} (x : _117066) (a : _117066) : (term98 _117066 x a) = (term110 _117066 x a).
Proof. exact (@lem5260269 (x = a)). Qed.
Lemma lem5260274 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term95 _117066 s x a) : term110 _117066 x a.
Proof. exact (EQ_MP (@lem5260271 _117066 x a) (@lem5260121 _117066 s x a h1)). Qed.
Lemma lem5260277 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term95 _117066 s x a) (h2 : term93 _117066 x' s a) : False.
Proof. exact (@lem5260274 _117066 s x a h1 (@lem5260266 _117066 x x' s a h1 h2)). Qed.
Lemma lem5260278 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term95 _117066 s x a) (h2 : term93 _117066 x' s a) : term111.
Proof. exact (fun h0 : ~ False => @lem5260277 _117066 x x' s a h1 h2). Qed.
Lemma lem5260280 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5260281 : term111 = False.
Proof. exact (@lem5260280 False). Qed.
Lemma lem5260282 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term95 _117066 s x a) (h2 : term93 _117066 x' s a) : False.
Proof. exact (EQ_MP (@lem5260281) (@lem5260278 _117066 x x' s a h1 h2)). Qed.
Lemma lem5260283 {_117066 : Type'} (s : _117066 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5260284 {_117066 : Type'} (_68868 : _117066) (_68869 : _117066) (h1 : _68868 = _68869) : _68868 = _68869.
Proof. exact (h1). Qed.
Lemma lem5260285 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) (_68869 : _117066) (h1 : _68868 = _68869) : (s _68868) = (s _68869).
Proof. exact (MK_COMB (@lem5260283 _117066 s) (@lem5260284 _117066 _68868 _68869 h1)). Qed.
Lemma lem5260287 (b : Prop) (a : Prop) : term112 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5260288 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : term113 _117066 _68869 s _68868.
Proof. exact (@lem5260287 (s _68869) (s _68868)). Qed.
Lemma lem5260289 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) (_68869 : _117066) (h1 : _68868 = _68869) : term114 _117066 _68869 s _68868.
Proof. exact (@lem5260288 _117066 _68869 s _68868 (@lem5260285 _117066 s _68868 _68869 h1)). Qed.
Lemma lem5260290 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : term115 _117066 _68869 s _68868.
Proof. exact (fun h0 : _68868 = _68869 => @lem5260289 _117066 s _68868 _68869 h0). Qed.
Lemma lem5260292 (a : Prop) (b : Prop) : (a -> b) = (term116 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5260293 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : (term115 _117066 _68869 s _68868) = (term117 _117066 _68869 s _68868).
Proof. exact (@lem5260292 (_68868 = _68869) (term114 _117066 _68869 s _68868)). Qed.
Lemma lem5260294 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : term117 _117066 _68869 s _68868.
Proof. exact (EQ_MP (@lem5260293 _117066 _68869 s _68868) (@lem5260290 _117066 _68869 s _68868)). Qed.
Lemma lem5260298 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : s x'.
Proof. exact (proj1 (@lem5260045 _117066 x' s a h1)). Qed.
Lemma lem5260299 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term101 _117066 s x'.
Proof. exact (fun h0 : term32 _117066 s x' => @lem5260298 _117066 x' s a h1). Qed.
Lemma lem5260301 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5260302 {_117066 : Type'} (s : _117066 -> Prop) (x' : _117066) : (term101 _117066 s x') = (s x').
Proof. exact (@lem5260301 (s x')). Qed.
Lemma lem5260303 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : s x'.
Proof. exact (EQ_MP (@lem5260302 _117066 s x') (@lem5260299 _117066 x' s a h1)). Qed.
Lemma lem5260309 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5260310 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68857 : _117066) : (term84 _117066 s _68857 a) = (term103 _117066 a s _68857).
Proof. exact (@lem5260309 (_68857 = a) (term32 _117066 s _68857)). Qed.
Lemma lem5260318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5260319 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68857 : _117066) : (term104 _117066 s _68857 a) = (term105 _117066 a s _68857).
Proof. exact (MK_COMB (@lem5260318) (@lem5260310 _117066 a s _68857)). Qed.
Lemma lem5260327 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68857 : _117066) : (term103 _117066 a s _68857) = (term103 _117066 a s _68857).
Proof. exact (eq_refl (term103 _117066 a s _68857)). Qed.
Lemma lem5260328 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68857 : _117066) : ((term84 _117066 s _68857 a) = (term103 _117066 a s _68857)) = ((term103 _117066 a s _68857) = (term103 _117066 a s _68857)).
Proof. exact (MK_COMB (@lem5260319 _117066 a s _68857) (@lem5260327 _117066 a s _68857)). Qed.
Lemma lem5260330 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5260331 (x : Prop) : (x = x) = True.
Proof. exact (@lem5260330 Prop x). Qed.
Lemma lem5260332 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68857 : _117066) : ((term103 _117066 a s _68857) = (term103 _117066 a s _68857)) = True.
Proof. exact (@lem5260331 (term103 _117066 a s _68857)). Qed.
Lemma lem5260333 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68857 : _117066) : ((term84 _117066 s _68857 a) = (term103 _117066 a s _68857)) = True.
Proof. exact (TRANS (@lem5260328 _117066 a s _68857) (@lem5260332 _117066 a s _68857)). Qed.
Lemma lem5260334 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68857 : _117066) : True = ((term84 _117066 s _68857 a) = (term103 _117066 a s _68857)).
Proof. exact (SYM (@lem5260333 _117066 a s _68857)). Qed.
Lemma lem5260335 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) (_68857 : _117066) : (term84 _117066 s _68857 a) = (term103 _117066 a s _68857).
Proof. exact (EQ_MP (@lem5260334 _117066 a s _68857) (@lem0)). Qed.
Lemma lem5260336 {_117066 : Type'} (_68857 : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term103 _117066 a s _68857.
Proof. exact (EQ_MP (@lem5260335 _117066 a s _68857) (@lem5260175 _117066 _68857 x' s a h1)). Qed.
Lemma lem5260338 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5260339 {_117066 : Type'} (s : _117066 -> Prop) (_68857 : _117066) (a : _117066) : (term103 _117066 a s _68857) = (term107 _117066 s _68857 a).
Proof. exact (@lem5260338 (term32 _117066 s _68857) (_68857 = a)). Qed.
Lemma lem5260341 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5260342 {_117066 : Type'} (s : _117066 -> Prop) (_68857 : _117066) : (term75 _117066 s _68857) = (s _68857).
Proof. exact (@lem5260341 (s _68857)). Qed.
Lemma lem5260343 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260344 {_117066 : Type'} (s : _117066 -> Prop) (_68857 : _117066) : (term108 _117066 s _68857) = (term39 _117066 s _68857).
Proof. exact (MK_COMB (@lem5260343) (@lem5260342 _117066 s _68857)). Qed.
Lemma lem5260345 {_117066 : Type'} (_68857 : _117066) (a : _117066) : (_68857 = a) = (_68857 = a).
Proof. exact (eq_refl (_68857 = a)). Qed.
Lemma lem5260346 {_117066 : Type'} (s : _117066 -> Prop) (_68857 : _117066) (a : _117066) : (term107 _117066 s _68857 a) = (term41 _117066 s _68857 a).
Proof. exact (MK_COMB (@lem5260344 _117066 s _68857) (@lem5260345 _117066 _68857 a)). Qed.
Lemma lem5260347 {_117066 : Type'} (s : _117066 -> Prop) (_68857 : _117066) (a : _117066) : (term103 _117066 a s _68857) = (term41 _117066 s _68857 a).
Proof. exact (TRANS (@lem5260339 _117066 s _68857 a) (@lem5260346 _117066 s _68857 a)). Qed.
Lemma lem5260350 {_117066 : Type'} (_68857 : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term41 _117066 s _68857 a.
Proof. exact (EQ_MP (@lem5260347 _117066 s _68857 a) (@lem5260336 _117066 _68857 x' s a h1)). Qed.
Lemma lem5260351 {_117066 : Type'} (_68857 : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term41 _117066 s _68857 a.
Proof. exact (@lem5260350 _117066 _68857 x' s a h1). Qed.
Lemma lem5260352 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term41 _117066 s x' a.
Proof. exact (@lem5260351 _117066 x' x' s a h1). Qed.
Lemma lem5260355 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : x' = a.
Proof. exact (@lem5260352 _117066 x' s a h1 (@lem5260303 _117066 x' s a h1)). Qed.
Lemma lem5260356 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term109 _117066 x' a.
Proof. exact (fun h0 : term98 _117066 x' a => @lem5260355 _117066 x' s a h1). Qed.
Lemma lem5260358 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5260359 {_117066 : Type'} (x' : _117066) (a : _117066) : (term109 _117066 x' a) = (x' = a).
Proof. exact (@lem5260358 (x' = a)). Qed.
Lemma lem5260360 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : x' = a.
Proof. exact (EQ_MP (@lem5260359 _117066 x' a) (@lem5260356 _117066 x' s a h1)). Qed.
Lemma lem5260362 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : s x'.
Proof. exact (proj1 (@lem5260045 _117066 x' s a h1)). Qed.
Lemma lem5260363 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term101 _117066 s x'.
Proof. exact (fun h0 : term32 _117066 s x' => @lem5260362 _117066 x' s a h1). Qed.
Lemma lem5260365 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5260366 {_117066 : Type'} (s : _117066 -> Prop) (x' : _117066) : (term101 _117066 s x') = (s x').
Proof. exact (@lem5260365 (s x')). Qed.
Lemma lem5260367 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : s x'.
Proof. exact (EQ_MP (@lem5260366 _117066 s x') (@lem5260363 _117066 x' s a h1)). Qed.
Lemma lem5260373 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5260374 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : (term117 _117066 _68869 s _68868) = (term118 _117066 _68869 s _68868).
Proof. exact (@lem5260373 (s _68869) (term98 _117066 _68868 _68869) (term32 _117066 s _68868)). Qed.
Lemma lem5260388 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5260389 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) (_68869 : _117066) : (term119 _117066 _68869 s _68868) = (term120 _117066 s _68868 _68869).
Proof. exact (@lem5260388 (term32 _117066 s _68868) (term98 _117066 _68868 _68869)). Qed.
Lemma lem5260397 {_117066 : Type'} (s : _117066 -> Prop) (_68869 : _117066) : (term121 _117066 s _68869) = (term121 _117066 s _68869).
Proof. exact (eq_refl (term121 _117066 s _68869)). Qed.
Lemma lem5260398 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) (_68869 : _117066) : (term118 _117066 _68869 s _68868) = (term122 _117066 s _68868 _68869).
Proof. exact (MK_COMB (@lem5260397 _117066 s _68869) (@lem5260389 _117066 s _68868 _68869)). Qed.
Lemma lem5260409 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) (_68869 : _117066) : (term117 _117066 _68869 s _68868) = (term122 _117066 s _68868 _68869).
Proof. exact (TRANS (@lem5260374 _117066 _68869 s _68868) (@lem5260398 _117066 s _68868 _68869)). Qed.
Lemma lem5260410 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5260411 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) (_68869 : _117066) : (term123 _117066 _68869 s _68868) = (term124 _117066 s _68868 _68869).
Proof. exact (MK_COMB (@lem5260410) (@lem5260409 _117066 s _68868 _68869)). Qed.
Lemma lem5260425 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5260426 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) (_68869 : _117066) : (term119 _117066 _68869 s _68868) = (term120 _117066 s _68868 _68869).
Proof. exact (@lem5260425 (term32 _117066 s _68868) (term98 _117066 _68868 _68869)). Qed.
Lemma lem5260434 {_117066 : Type'} (s : _117066 -> Prop) (_68869 : _117066) : (term121 _117066 s _68869) = (term121 _117066 s _68869).
Proof. exact (eq_refl (term121 _117066 s _68869)). Qed.
Lemma lem5260435 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) (_68869 : _117066) : (term118 _117066 _68869 s _68868) = (term122 _117066 s _68868 _68869).
Proof. exact (MK_COMB (@lem5260434 _117066 s _68869) (@lem5260426 _117066 s _68868 _68869)). Qed.
Lemma lem5260446 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) (_68869 : _117066) : ((term117 _117066 _68869 s _68868) = (term118 _117066 _68869 s _68868)) = ((term122 _117066 s _68868 _68869) = (term122 _117066 s _68868 _68869)).
Proof. exact (MK_COMB (@lem5260411 _117066 s _68868 _68869) (@lem5260435 _117066 s _68868 _68869)). Qed.
Lemma lem5260448 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5260449 (x : Prop) : (x = x) = True.
Proof. exact (@lem5260448 Prop x). Qed.
Lemma lem5260450 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) (_68869 : _117066) : ((term122 _117066 s _68868 _68869) = (term122 _117066 s _68868 _68869)) = True.
Proof. exact (@lem5260449 (term122 _117066 s _68868 _68869)). Qed.
Lemma lem5260451 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : ((term117 _117066 _68869 s _68868) = (term118 _117066 _68869 s _68868)) = True.
Proof. exact (TRANS (@lem5260446 _117066 s _68868 _68869) (@lem5260450 _117066 s _68868 _68869)). Qed.
Lemma lem5260452 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : True = ((term117 _117066 _68869 s _68868) = (term118 _117066 _68869 s _68868)).
Proof. exact (SYM (@lem5260451 _117066 _68869 s _68868)). Qed.
Lemma lem5260453 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : (term117 _117066 _68869 s _68868) = (term118 _117066 _68869 s _68868).
Proof. exact (EQ_MP (@lem5260452 _117066 _68869 s _68868) (@lem0)). Qed.
Lemma lem5260454 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : term118 _117066 _68869 s _68868.
Proof. exact (EQ_MP (@lem5260453 _117066 _68869 s _68868) (@lem5260294 _117066 _68869 s _68868)). Qed.
Lemma lem5260456 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5260457 {_117066 : Type'} (_68868 : _117066) (s : _117066 -> Prop) (_68869 : _117066) : (term118 _117066 _68869 s _68868) = (term125 _117066 _68868 s _68869).
Proof. exact (@lem5260456 (term119 _117066 _68869 s _68868) (s _68869)). Qed.
Lemma lem5260459 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5260460 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : (term128 _117066 _68869 s _68868) = (term129 _117066 _68869 s _68868).
Proof. exact (@lem5260459 (term98 _117066 _68868 _68869) (term32 _117066 s _68868)). Qed.
Lemma lem5260462 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5260463 {_117066 : Type'} (_68868 : _117066) (_68869 : _117066) : (term130 _117066 _68868 _68869) = (_68868 = _68869).
Proof. exact (@lem5260462 (_68868 = _68869)). Qed.
Lemma lem5260464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5260465 {_117066 : Type'} (_68868 : _117066) (_68869 : _117066) : (term131 _117066 _68868 _68869) = (term132 _117066 _68868 _68869).
Proof. exact (MK_COMB (@lem5260464) (@lem5260463 _117066 _68868 _68869)). Qed.
Lemma lem5260467 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5260468 {_117066 : Type'} (s : _117066 -> Prop) (_68868 : _117066) : (term75 _117066 s _68868) = (s _68868).
Proof. exact (@lem5260467 (s _68868)). Qed.
Lemma lem5260469 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : (term129 _117066 _68869 s _68868) = (term133 _117066 _68869 s _68868).
Proof. exact (MK_COMB (@lem5260465 _117066 _68868 _68869) (@lem5260468 _117066 s _68868)). Qed.
Lemma lem5260470 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : (term128 _117066 _68869 s _68868) = (term133 _117066 _68869 s _68868).
Proof. exact (TRANS (@lem5260460 _117066 _68869 s _68868) (@lem5260469 _117066 _68869 s _68868)). Qed.
Lemma lem5260471 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260472 {_117066 : Type'} (_68869 : _117066) (s : _117066 -> Prop) (_68868 : _117066) : (term134 _117066 _68869 s _68868) = (term135 _117066 _68869 s _68868).
Proof. exact (MK_COMB (@lem5260471) (@lem5260470 _117066 _68869 s _68868)). Qed.
Lemma lem5260473 {_117066 : Type'} (s : _117066 -> Prop) (_68869 : _117066) : (s _68869) = (s _68869).
Proof. exact (eq_refl (s _68869)). Qed.
Lemma lem5260474 {_117066 : Type'} (_68868 : _117066) (s : _117066 -> Prop) (_68869 : _117066) : (term125 _117066 _68868 s _68869) = (term136 _117066 _68868 s _68869).
Proof. exact (MK_COMB (@lem5260472 _117066 _68869 s _68868) (@lem5260473 _117066 s _68869)). Qed.
Lemma lem5260475 {_117066 : Type'} (_68868 : _117066) (s : _117066 -> Prop) (_68869 : _117066) : (term118 _117066 _68869 s _68868) = (term136 _117066 _68868 s _68869).
Proof. exact (TRANS (@lem5260457 _117066 _68868 s _68869) (@lem5260474 _117066 _68868 s _68869)). Qed.
Lemma lem5260477 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term133 _117066 a s x'.
Proof. exact (conj (@lem5260360 _117066 x' s a h1) (@lem5260367 _117066 x' s a h1)). Qed.
Lemma lem5260479 {_117066 : Type'} (_68868 : _117066) (s : _117066 -> Prop) (_68869 : _117066) : term136 _117066 _68868 s _68869.
Proof. exact (EQ_MP (@lem5260475 _117066 _68868 s _68869) (@lem5260454 _117066 _68869 s _68868)). Qed.
Lemma lem5260480 {_117066 : Type'} (_68868 : _117066) (s : _117066 -> Prop) (_68869 : _117066) : term136 _117066 _68868 s _68869.
Proof. exact (@lem5260479 _117066 _68868 s _68869). Qed.
Lemma lem5260481 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) : term136 _117066 x' s a.
Proof. exact (@lem5260480 _117066 x' s a). Qed.
Lemma lem5260484 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : s a.
Proof. exact (@lem5260481 _117066 x' s a (@lem5260477 _117066 x' s a h1)). Qed.
Lemma lem5260485 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : term101 _117066 s a.
Proof. exact (fun h0 : term32 _117066 s a => @lem5260484 _117066 x' s a h1). Qed.
Lemma lem5260487 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5260488 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term101 _117066 s a) = (s a).
Proof. exact (@lem5260487 (s a)). Qed.
Lemma lem5260489 {_117066 : Type'} (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term93 _117066 x' s a) : s a.
Proof. exact (EQ_MP (@lem5260488 _117066 s a) (@lem5260485 _117066 x' s a h1)). Qed.
Lemma lem5260492 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5260494 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term32 _117066 s a) = (term137 _117066 s a).
Proof. exact (@lem5260492 (s a)). Qed.
Lemma lem5260497 {_117066 : Type'} (s : _117066 -> Prop) (x : _117066) (a : _117066) (h1 : term96 _117066 s x a) : term137 _117066 s a.
Proof. exact (EQ_MP (@lem5260494 _117066 s a) (@lem5260188 _117066 s x a h1)). Qed.
Lemma lem5260500 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term96 _117066 s x a) (h2 : term93 _117066 x' s a) : False.
Proof. exact (@lem5260497 _117066 s x a h1 (@lem5260489 _117066 x' s a h2)). Qed.
Lemma lem5260501 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term96 _117066 s x a) (h2 : term93 _117066 x' s a) : term111.
Proof. exact (fun h0 : ~ False => @lem5260500 _117066 x x' s a h1 h2). Qed.
Lemma lem5260503 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5260504 : term111 = False.
Proof. exact (@lem5260503 False). Qed.
Lemma lem5260506 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term96 _117066 s x a) (h2 : term93 _117066 x' s a) : False.
Proof. exact (EQ_MP (@lem5260504) (@lem5260501 _117066 x x' s a h1 h2)). Qed.
Lemma lem5260507 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term74 _117066 s x a) (h2 : term93 _117066 x' s a) : False.
Proof. exact (or_elim (@lem5260022 _117066 s x a h1) (fun h0 : term95 _117066 s x a => @lem5260282 _117066 x x' s a h0 h2) (fun h0 : term96 _117066 s x a => @lem5260506 _117066 x x' s a h0 h2)). Qed.
Lemma lem5260508 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term74 _117066 s x a) (h2 : term93 _117066 x' s a) : (term93 _117066 x' s a) = False.
Proof. exact (prop_ext (fun h3 : term93 _117066 x' s a => @lem5260507 _117066 x x' s a h1 h2) (fun h3 : False => @lem5260045 _117066 x' s a h2)). Qed.
Lemma lem5260509 {_117066 : Type'} (x : _117066) (x' : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term74 _117066 s x a) (h2 : term93 _117066 x' s a) : False.
Proof. exact (EQ_MP (@lem5260508 _117066 x x' s a h1 h2) (@lem5260045 _117066 x' s a h2)). Qed.
Lemma lem5260510 {_117066 : Type'} (x : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term74 _117066 s x a) (h2 : term45 _117066 s a) : False.
Proof. exact (ex_elim (@lem5259971 _117066 s a h2) (fun x' : _117066 => fun h0 : term138 _117066 s a x' => @lem5260509 _117066 x x' s a h1 h0)). Qed.
Lemma lem5260511 {_117066 : Type'} (x : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term74 _117066 s x a) (h2 : term45 _117066 s a) : (term74 _117066 s x a) = False.
Proof. exact (prop_ext (fun h3 : term74 _117066 s x a => @lem5260510 _117066 x s a h1 h2) (fun h3 : False => @lem5259885 _117066 s x a h1)). Qed.
Lemma lem5260512 {_117066 : Type'} (x : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term74 _117066 s x a) (h2 : term45 _117066 s a) : False.
Proof. exact (EQ_MP (@lem5260511 _117066 x s a h1 h2) (@lem5259885 _117066 s x a h1)). Qed.
Lemma lem5260513 {_117066 : Type'} (x : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term45 _117066 s a) : term73 _117066 s x a.
Proof. exact (fun h0 : term74 _117066 s x a => @lem5260512 _117066 x s a h0 h1). Qed.
Lemma lem5260514 {_117066 : Type'} (x : _117066) (s : _117066 -> Prop) (a : _117066) (h1 : term45 _117066 s a) : (s x) = (x = a).
Proof. exact (EQ_MP (@lem5259884 _117066 s x a) (@lem5260513 _117066 x s a h1)). Qed.
Lemma lem5260519 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term45 _117066 s a) : term55 _117066 s a.
Proof. exact (fun x : _117066 => @lem5260514 _117066 x s a h1). Qed.
Lemma lem5260520 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term56 _117066 s a.
Proof. exact (fun h0 : term45 _117066 s a => @lem5260519 _117066 s a h0). Qed.
Lemma lem5260525 {_117066 : Type'} (a : _117066) : term68 _117066 a.
Proof. exact (fun s : _117066 -> Prop => @lem5260520 _117066 s a). Qed.
Lemma lem5260530 {_117066 : Type'} : term72 _117066.
Proof. exact (fun a : _117066 => @lem5260525 _117066 a). Qed.
Lemma lem5260531 {_117066 : Type'} : term71 _117066.
Proof. exact (EQ_MP (@lem5259879 _117066) (@lem5260530 _117066)). Qed.
Lemma lem5260532 {_117066 : Type'} (a : _117066) : term139 _117066 a.
Proof. exact (@lem5260531 _117066 a). Qed.
Lemma lem5260533 {_117066 : Type'} (a : _117066) : (term139 _117066 a) = (term67 _117066 a).
Proof. exact (eq_refl (term139 _117066 a)). Qed.
Lemma lem5260534 {_117066 : Type'} (a : _117066) : term67 _117066 a.
Proof. exact (EQ_MP (@lem5260533 _117066 a) (@lem5260532 _117066 a)). Qed.
Lemma lem5260535 {_117066 : Type'} (a : _117066) (s : _117066 -> Prop) : term140 _117066 a s.
Proof. exact (@lem5260534 _117066 a s). Qed.
Lemma lem5260536 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : (term140 _117066 a s) = (term58 _117066 s a).
Proof. exact (eq_refl (term140 _117066 a s)). Qed.
Lemma lem5260537 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term58 _117066 s a.
Proof. exact (EQ_MP (@lem5260536 _117066 s a) (@lem5260535 _117066 a s)). Qed.
Lemma lem5260539 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term58 _117066 s a.
Proof. exact (@lem5259752 _117066 s a (@lem5260537 _117066 s a)). Qed.
Lemma lem5260540 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term59 _117066 s a) : False.
Proof. exact (@lem5260539 _117066 s a (@lem5259736 _117066 s a h1)). Qed.
Lemma lem5260541 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term59 _117066 s a) : (term59 _117066 s a) = False.
Proof. exact (prop_ext (fun h2 : term59 _117066 s a => @lem5260540 _117066 s a h1) (fun h2 : False => @lem5259736 _117066 s a h1)). Qed.
Lemma lem5260542 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term59 _117066 s a) : False.
Proof. exact (EQ_MP (@lem5260541 _117066 s a h1) (@lem5259736 _117066 s a h1)). Qed.
Lemma lem5260543 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term58 _117066 s a.
Proof. exact (fun h0 : term59 _117066 s a => @lem5260542 _117066 s a h0). Qed.
Lemma lem5260544 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term56 _117066 s a.
Proof. exact (EQ_MP (@lem5259735 _117066 s a) (@lem5260543 _117066 s a)). Qed.
Lemma lem5260545 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term29 _117066 s a.
Proof. exact (EQ_MP (@lem5259731 _117066 s a) (@lem5260544 _117066 s a)). Qed.
Lemma lem5260546 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term28 _117066 s a.
Proof. exact (EQ_MP (@lem5259620 _117066 s a) (@lem5260545 _117066 s a)). Qed.
Lemma lem5260547 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term28 _117066 s a) : term28 _117066 s a.
Proof. exact (h1). Qed.
Lemma lem5260548 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term23 _117066 s a) : term23 _117066 s a.
Proof. exact (h1). Qed.
Lemma lem5260549 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term23 _117066 s a) (h2 : term28 _117066 s a) : s = (@INSERT _117066 a (@EMPTY _117066)).
Proof. exact (@lem5260547 _117066 s a h2 (@lem5260548 _117066 s a h1)). Qed.
Lemma lem5260550 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term23 _117066 s a) : term141 _117066 s a.
Proof. exact (fun h0 : term28 _117066 s a => @lem5260549 _117066 s a h1 h0). Qed.
Lemma lem5260551 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term28 _117066 s a) : term28 _117066 s a.
Proof. exact (h1). Qed.
Lemma lem5260552 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term23 _117066 s a) (h2 : term28 _117066 s a) : s = (@INSERT _117066 a (@EMPTY _117066)).
Proof. exact (@lem5260550 _117066 s a h1 (@lem5260551 _117066 s a h2)). Qed.
Lemma lem5260553 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) (h1 : term28 _117066 s a) : term28 _117066 s a.
Proof. exact (fun h0 : term23 _117066 s a => @lem5260552 _117066 s a h0 h1). Qed.
Lemma lem5260554 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term142 _117066 s a.
Proof. exact (fun h0 : term28 _117066 s a => @lem5260553 _117066 s a h0). Qed.
Lemma lem5260556 (s : real -> Prop) (h1 : term143 s) : term143 s.
Proof. exact (h1). Qed.
Lemma lem5260557 (s : real -> Prop) (h1 : term144 s) : term144 s.
Proof. exact (h1). Qed.
Lemma lem5260558 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5260559 (s : real -> Prop) (B : real) (h1 : term146 s B) : term146 s B.
Proof. exact (h1). Qed.
Lemma lem5260560 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (sup s) = (inf s).
Proof. exact (h1). Qed.
Lemma lem5260562 {_117066 : Type'} (s : _117066 -> Prop) (a : _117066) : term28 _117066 s a.
Proof. exact (@lem5260554 _117066 s a (@lem5260546 _117066 s a)). Qed.
Lemma lem5260563 (s : real -> Prop) (a : real) : term147 s a.
Proof. exact (@lem5260562 real s a). Qed.
Lemma lem5260564 (s : real -> Prop) : term148 s.
Proof. exact (@lem5260563 s (sup s)). Qed.
Lemma lem5260565 (x : real) : term149 x.
Proof. exact (@lem5259554 x). Qed.
Lemma lem5260566 (x : real) : (term149 x) = (term11 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem5260567 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem5260566 x) (@lem5260565 x)). Qed.
Lemma lem5260568 (x : real) (y : real) : term150 x y.
Proof. exact (@lem5260567 x y). Qed.
Lemma lem5260569 (y : real) (x : real) : (term150 x y) = ((x = y) = (term7 y x)).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem5260571 (s : real -> Prop) : term151 s.
Proof. exact (@lem82 (s = (@EMPTY real))). Qed.
Lemma lem5260592 (s : real -> Prop) (h1 : term145 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5260571 s (@lem5260558 s h1)). Qed.
Lemma lem5260593 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5260594 (s : real -> Prop) (h1 : term145 s) : (term145 s) = (~ False).
Proof. exact (MK_COMB (@lem5260593) (@lem5260592 s h1)). Qed.
Lemma lem5260596 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5260597 (s : real -> Prop) (h1 : term145 s) : (term145 s) = True.
Proof. exact (TRANS (@lem5260594 s h1) (@lem5260596)). Qed.
Lemma lem5260598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5260599 (s : real -> Prop) (h1 : term145 s) : (term152 s) = (and True).
Proof. exact (MK_COMB (@lem5260598) (@lem5260597 s h1)). Qed.
Lemma lem5260609 (y : real) (x : real) : (x = y) = (term7 y x).
Proof. exact (EQ_MP (@lem5260569 y x) (@lem5260568 x y)). Qed.
Lemma lem5260610 (s : real -> Prop) (x : real) : (x = (sup s)) = (term153 s x).
Proof. exact (@lem5260609 (sup s) x). Qed.
Lemma lem5260614 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (sup s) = (inf s).
Proof. exact (h1). Qed.
Lemma lem5260615 (x : real) : (real_le x) = (real_le x).
Proof. exact (eq_refl (real_le x)). Qed.
Lemma lem5260616 (x : real) (s : real -> Prop) (h1 : (sup s) = (inf s)) : (term154 x s) = (term155 x s).
Proof. exact (MK_COMB (@lem5260615 x) (@lem5260614 s h1)). Qed.
Lemma lem5260617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5260618 (x : real) (s : real -> Prop) (h1 : (sup s) = (inf s)) : (term156 x s) = (term157 x s).
Proof. exact (MK_COMB (@lem5260617) (@lem5260616 x s h1)). Qed.
Lemma lem5260620 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (sup s) = (inf s).
Proof. exact (h1). Qed.
Lemma lem5260621 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5260622 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (term158 s) = (term159 s).
Proof. exact (MK_COMB (@lem5260621) (@lem5260620 s h1)). Qed.
Lemma lem5260623 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5260624 (x : real) (s : real -> Prop) (h1 : (sup s) = (inf s)) : (term160 s x) = (term161 s x).
Proof. exact (MK_COMB (@lem5260622 s h1) (@lem5260623 x)). Qed.
Lemma lem5260625 (x : real) (s : real -> Prop) (h1 : (sup s) = (inf s)) : (term153 s x) = (term162 s x).
Proof. exact (MK_COMB (@lem5260618 x s h1) (@lem5260624 x s h1)). Qed.
Lemma lem5260628 (x : real) (s : real -> Prop) (h1 : (sup s) = (inf s)) : (x = (sup s)) = (term162 s x).
Proof. exact (TRANS (@lem5260610 s x) (@lem5260625 x s h1)). Qed.
Lemma lem5260629 (x : real) (s : real -> Prop) : (term163 x s) = (term163 x s).
Proof. exact (eq_refl (term163 x s)). Qed.
Lemma lem5260630 (x : real) (s : real -> Prop) (h1 : (sup s) = (inf s)) : (term164 x s) = (term165 s x).
Proof. exact (MK_COMB (@lem5260629 x s) (@lem5260628 x s h1)). Qed.
Lemma lem5260633 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (term166 s) = (term167 s).
Proof. exact (fun_ext (fun x : real => @lem5260630 x s h1)). Qed.
Lemma lem5260634 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260635 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (term168 s) = (term169 s).
Proof. exact (MK_COMB (@lem5260634) (@lem5260633 s h1)). Qed.
Lemma lem5260640 (s : real -> Prop) (h1 : term145 s) (h2 : (sup s) = (inf s)) : (term170 s) = (term171 s).
Proof. exact (MK_COMB (@lem5260599 s h1) (@lem5260635 s h2)). Qed.
Lemma lem5260642 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5260643 (s : real -> Prop) : (term171 s) = (term169 s).
Proof. exact (@lem5260642 (term169 s)). Qed.
Lemma lem5260652 (s : real -> Prop) (h1 : term145 s) (h2 : (sup s) = (inf s)) : (term170 s) = (term169 s).
Proof. exact (TRANS (@lem5260640 s h1 h2) (@lem5260643 s)). Qed.
Lemma lem5260653 (s : real -> Prop) (h1 : term145 s) (h2 : (sup s) = (inf s)) : (term169 s) = (term170 s).
Proof. exact (SYM (@lem5260652 s h1 h2)). Qed.
Lemma lem5260655 (p : Prop) : p = (term57 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5260656 (s : real -> Prop) : (term169 s) = (term172 s).
Proof. exact (@lem5260655 (term169 s)). Qed.
Lemma lem5260657 (s : real -> Prop) : (term172 s) = (term169 s).
Proof. exact (SYM (@lem5260656 s)). Qed.
Lemma lem5260658 (s : real -> Prop) (h1 : term173 s) : term173 s.
Proof. exact (h1). Qed.
Lemma lem5260661 (B : real) (s : real -> Prop) (h1 : term174 B s) : term174 B s.
Proof. exact (h1). Qed.
Lemma lem5260662 (B : real) (s : real -> Prop) : term175 B s.
Proof. exact (fun h0 : term174 B s => @lem5260661 B s h0). Qed.
Lemma lem5260663 (B : real) (s : real -> Prop) (h1 : term175 B s) : term175 B s.
Proof. exact (h1). Qed.
Lemma lem5260664 (B : real) (s : real -> Prop) (h1 : term174 B s) : term174 B s.
Proof. exact (h1). Qed.
Lemma lem5260665 (B : real) (s : real -> Prop) (h1 : term174 B s) (h2 : term175 B s) : term174 B s.
Proof. exact (@lem5260663 B s h2 (@lem5260664 B s h1)). Qed.
Lemma lem5260666 (B : real) (s : real -> Prop) (h1 : term174 B s) : term176 B s.
Proof. exact (fun h0 : term175 B s => @lem5260665 B s h1 h0). Qed.
Lemma lem5260667 (B : real) (s : real -> Prop) (h1 : term175 B s) : term175 B s.
Proof. exact (h1). Qed.
Lemma lem5260668 (B : real) (s : real -> Prop) (h1 : term174 B s) (h2 : term175 B s) : term174 B s.
Proof. exact (@lem5260666 B s h1 (@lem5260667 B s h2)). Qed.
Lemma lem5260669 (B : real) (s : real -> Prop) (h1 : term175 B s) : term175 B s.
Proof. exact (fun h0 : term174 B s => @lem5260668 B s h0 h1). Qed.
Lemma lem5260670 (B : real) (s : real -> Prop) : term177 B s.
Proof. exact (fun h0 : term175 B s => @lem5260669 B s h0). Qed.
Lemma lem5260673 (B : real) (s : real -> Prop) : term175 B s.
Proof. exact (@lem5260670 B s (@lem5260662 B s)). Qed.
Lemma lem5260757 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5260758 : term178 = term179.
Proof. exact (@lem5260757 term180). Qed.
Lemma lem5260797 : term181 = term181.
Proof. exact (eq_refl term181). Qed.
Lemma lem5260798 : term182 = term183.
Proof. exact (MK_COMB (@lem5260797) (@lem5260758)). Qed.
Lemma lem5260801 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem5260802 : term185 = term186.
Proof. exact (MK_COMB (@lem5260801) (@lem5260798)). Qed.
Lemma lem5260805 (s : real -> Prop) : (term187 s) = (term187 s).
Proof. exact (eq_refl (term187 s)). Qed.
Lemma lem5260806 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (MK_COMB (@lem5260805 s) (@lem5260802)). Qed.
Lemma lem5260809 (s : real -> Prop) : (term190 s) = (term190 s).
Proof. exact (eq_refl (term190 s)). Qed.
Lemma lem5260810 (s : real -> Prop) : (term191 s) = (term192 s).
Proof. exact (MK_COMB (@lem5260809 s) (@lem5260806 s)). Qed.
Lemma lem5260813 (s : real -> Prop) (B : real) : (term193 s B) = (term193 s B).
Proof. exact (eq_refl (term193 s B)). Qed.
Lemma lem5260814 (B : real) (s : real -> Prop) : (term194 B s) = (term195 B s).
Proof. exact (MK_COMB (@lem5260813 s B) (@lem5260810 s)). Qed.
Lemma lem5260817 (s : real -> Prop) : (term196 s) = (term196 s).
Proof. exact (eq_refl (term196 s)). Qed.
Lemma lem5260818 (B : real) (s : real -> Prop) : (term174 B s) = (term197 B s).
Proof. exact (MK_COMB (@lem5260817 s) (@lem5260814 B s)). Qed.
Lemma lem5260821 (s : real -> Prop) : (term198 s) = (term199 s).
Proof. exact (fun_ext (fun B : real => @lem5260818 B s)). Qed.
Lemma lem5260822 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260823 (s : real -> Prop) : (term200 s) = (term201 s).
Proof. exact (MK_COMB (@lem5260822) (@lem5260821 s)). Qed.
Lemma lem5260828 : term202 = term203.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5260823 s)). Qed.
Lemma lem5260829 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5260838 : term204 = term205.
Proof. exact (MK_COMB (@lem5260829) (@lem5260828)). Qed.
Lemma lem5260839 (s : real -> Prop) (b : real) : (term160 s b) = (term160 s b).
Proof. exact (eq_refl (term160 s b)). Qed.
Lemma lem5260844 (s : real -> Prop) (x : real) (b : real) : (term206 s x b) = (term206 s x b).
Proof. exact (eq_refl (term206 s x b)). Qed.
Lemma lem5260845 (s : real -> Prop) (b : real) : (term207 s b) = (term207 s b).
Proof. exact (fun_ext (fun x : real => @lem5260844 s x b)). Qed.
Lemma lem5260846 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260847 (s : real -> Prop) (b : real) : (term208 s b) = (term208 s b).
Proof. exact (MK_COMB (@lem5260846) (@lem5260845 s b)). Qed.
Lemma lem5260848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260849 (s : real -> Prop) (b : real) : (term209 s b) = (term209 s b).
Proof. exact (MK_COMB (@lem5260848) (@lem5260847 s b)). Qed.
Lemma lem5260850 (s : real -> Prop) (b : real) : (term210 s b) = (term210 s b).
Proof. exact (MK_COMB (@lem5260849 s b) (@lem5260839 s b)). Qed.
Lemma lem5260851 (s : real -> Prop) : (term211 s) = (term211 s).
Proof. exact (fun_ext (fun b : real => @lem5260850 s b)). Qed.
Lemma lem5260852 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260853 (s : real -> Prop) : (term212 s) = (term212 s).
Proof. exact (MK_COMB (@lem5260852) (@lem5260851 s)). Qed.
Lemma lem5260858 (x : real) (s : real -> Prop) : (term213 x s) = (term213 x s).
Proof. exact (eq_refl (term213 x s)). Qed.
Lemma lem5260859 (s : real -> Prop) : (term214 s) = (term214 s).
Proof. exact (fun_ext (fun x : real => @lem5260858 x s)). Qed.
Lemma lem5260860 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260861 (s : real -> Prop) : (term215 s) = (term215 s).
Proof. exact (MK_COMB (@lem5260860) (@lem5260859 s)). Qed.
Lemma lem5260862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5260863 (s : real -> Prop) : (term216 s) = (term216 s).
Proof. exact (MK_COMB (@lem5260862) (@lem5260861 s)). Qed.
Lemma lem5260864 (s : real -> Prop) : (term217 s) = (term217 s).
Proof. exact (MK_COMB (@lem5260863 s) (@lem5260853 s)). Qed.
Lemma lem5260869 (s : real -> Prop) (x : real) (b : real) : (term206 s x b) = (term206 s x b).
Proof. exact (eq_refl (term206 s x b)). Qed.
Lemma lem5260870 (s : real -> Prop) (b : real) : (term207 s b) = (term207 s b).
Proof. exact (fun_ext (fun x : real => @lem5260869 s x b)). Qed.
Lemma lem5260871 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260872 (s : real -> Prop) (b : real) : (term208 s b) = (term208 s b).
Proof. exact (MK_COMB (@lem5260871) (@lem5260870 s b)). Qed.
Lemma lem5260873 (s : real -> Prop) : (term218 s) = (term218 s).
Proof. exact (fun_ext (fun b : real => @lem5260872 s b)). Qed.
Lemma lem5260874 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5260875 (s : real -> Prop) : (term219 s) = (term219 s).
Proof. exact (MK_COMB (@lem5260874) (@lem5260873 s)). Qed.
Lemma lem5260880 (s : real -> Prop) : (term152 s) = (term152 s).
Proof. exact (eq_refl (term152 s)). Qed.
Lemma lem5260881 (s : real -> Prop) : (term220 s) = (term220 s).
Proof. exact (MK_COMB (@lem5260880 s) (@lem5260875 s)). Qed.
Lemma lem5260882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260883 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (MK_COMB (@lem5260882) (@lem5260881 s)). Qed.
Lemma lem5260884 (s : real -> Prop) : (term222 s) = (term222 s).
Proof. exact (MK_COMB (@lem5260883 s) (@lem5260864 s)). Qed.
Lemma lem5260885 : term223 = term223.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5260884 s)). Qed.
Lemma lem5260886 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5260887 : term180 = term180.
Proof. exact (MK_COMB (@lem5260886) (@lem5260885)). Qed.
Lemma lem5260888 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5260889 : term179 = term179.
Proof. exact (MK_COMB (@lem5260888) (@lem5260887)). Qed.
Lemma lem5260898 (x : real) (k : real) : ((term224 x k) = (term225 x k)) = ((term224 x k) = (term225 x k)).
Proof. exact (eq_refl ((term224 x k) = (term225 x k))). Qed.
Lemma lem5260899 (x : real) : (term226 x) = (term226 x).
Proof. exact (fun_ext (fun k : real => @lem5260898 x k)). Qed.
Lemma lem5260900 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260901 (x : real) : (term227 x) = (term227 x).
Proof. exact (MK_COMB (@lem5260900) (@lem5260899 x)). Qed.
Lemma lem5260902 : term228 = term228.
Proof. exact (fun_ext (fun x : real => @lem5260901 x)). Qed.
Lemma lem5260903 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260904 : term229 = term229.
Proof. exact (MK_COMB (@lem5260903) (@lem5260902)). Qed.
Lemma lem5260905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260906 : term181 = term181.
Proof. exact (MK_COMB (@lem5260905) (@lem5260904)). Qed.
Lemma lem5260907 : term183 = term183.
Proof. exact (MK_COMB (@lem5260906) (@lem5260889)). Qed.
Lemma lem5260908 (b : real) (s : real -> Prop) : (term155 b s) = (term155 b s).
Proof. exact (eq_refl (term155 b s)). Qed.
Lemma lem5260913 (s : real -> Prop) (b : real) (x : real) : (term230 s b x) = (term230 s b x).
Proof. exact (eq_refl (term230 s b x)). Qed.
Lemma lem5260914 (s : real -> Prop) (b : real) : (term231 s b) = (term231 s b).
Proof. exact (fun_ext (fun x : real => @lem5260913 s b x)). Qed.
Lemma lem5260915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260916 (s : real -> Prop) (b : real) : (term232 s b) = (term232 s b).
Proof. exact (MK_COMB (@lem5260915) (@lem5260914 s b)). Qed.
Lemma lem5260917 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260918 (s : real -> Prop) (b : real) : (term233 s b) = (term233 s b).
Proof. exact (MK_COMB (@lem5260917) (@lem5260916 s b)). Qed.
Lemma lem5260919 (b : real) (s : real -> Prop) : (term234 b s) = (term234 b s).
Proof. exact (MK_COMB (@lem5260918 s b) (@lem5260908 b s)). Qed.
Lemma lem5260920 (s : real -> Prop) : (term235 s) = (term235 s).
Proof. exact (fun_ext (fun b : real => @lem5260919 b s)). Qed.
Lemma lem5260921 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260922 (s : real -> Prop) : (term236 s) = (term236 s).
Proof. exact (MK_COMB (@lem5260921) (@lem5260920 s)). Qed.
Lemma lem5260927 (s : real -> Prop) (x : real) : (term237 s x) = (term237 s x).
Proof. exact (eq_refl (term237 s x)). Qed.
Lemma lem5260928 (s : real -> Prop) : (term238 s) = (term238 s).
Proof. exact (fun_ext (fun x : real => @lem5260927 s x)). Qed.
Lemma lem5260929 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260930 (s : real -> Prop) : (term239 s) = (term239 s).
Proof. exact (MK_COMB (@lem5260929) (@lem5260928 s)). Qed.
Lemma lem5260931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5260932 (s : real -> Prop) : (term240 s) = (term240 s).
Proof. exact (MK_COMB (@lem5260931) (@lem5260930 s)). Qed.
Lemma lem5260933 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (MK_COMB (@lem5260932 s) (@lem5260922 s)). Qed.
Lemma lem5260938 (s : real -> Prop) (b : real) (x : real) : (term230 s b x) = (term230 s b x).
Proof. exact (eq_refl (term230 s b x)). Qed.
Lemma lem5260939 (s : real -> Prop) (b : real) : (term231 s b) = (term231 s b).
Proof. exact (fun_ext (fun x : real => @lem5260938 s b x)). Qed.
Lemma lem5260940 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260941 (s : real -> Prop) (b : real) : (term232 s b) = (term232 s b).
Proof. exact (MK_COMB (@lem5260940) (@lem5260939 s b)). Qed.
Lemma lem5260942 (s : real -> Prop) : (term242 s) = (term242 s).
Proof. exact (fun_ext (fun b : real => @lem5260941 s b)). Qed.
Lemma lem5260943 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5260944 (s : real -> Prop) : (term243 s) = (term243 s).
Proof. exact (MK_COMB (@lem5260943) (@lem5260942 s)). Qed.
Lemma lem5260949 (s : real -> Prop) : (term152 s) = (term152 s).
Proof. exact (eq_refl (term152 s)). Qed.
Lemma lem5260950 (s : real -> Prop) : (term244 s) = (term244 s).
Proof. exact (MK_COMB (@lem5260949 s) (@lem5260944 s)). Qed.
Lemma lem5260951 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260952 (s : real -> Prop) : (term245 s) = (term245 s).
Proof. exact (MK_COMB (@lem5260951) (@lem5260950 s)). Qed.
Lemma lem5260953 (s : real -> Prop) : (term246 s) = (term246 s).
Proof. exact (MK_COMB (@lem5260952 s) (@lem5260933 s)). Qed.
Lemma lem5260954 : term247 = term247.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5260953 s)). Qed.
Lemma lem5260955 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5260956 : term248 = term248.
Proof. exact (MK_COMB (@lem5260955) (@lem5260954)). Qed.
Lemma lem5260957 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260958 : term184 = term184.
Proof. exact (MK_COMB (@lem5260957) (@lem5260956)). Qed.
Lemma lem5260959 : term186 = term186.
Proof. exact (MK_COMB (@lem5260958) (@lem5260907)). Qed.
Lemma lem5260968 (s : real -> Prop) (x : real) : (term165 s x) = (term165 s x).
Proof. exact (eq_refl (term165 s x)). Qed.
Lemma lem5260969 (s : real -> Prop) : (term167 s) = (term167 s).
Proof. exact (fun_ext (fun x : real => @lem5260968 s x)). Qed.
Lemma lem5260970 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260971 (s : real -> Prop) : (term169 s) = (term169 s).
Proof. exact (MK_COMB (@lem5260970) (@lem5260969 s)). Qed.
Lemma lem5260972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5260973 (s : real -> Prop) : (term173 s) = (term173 s).
Proof. exact (MK_COMB (@lem5260972) (@lem5260971 s)). Qed.
Lemma lem5260974 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260975 (s : real -> Prop) : (term187 s) = (term187 s).
Proof. exact (MK_COMB (@lem5260974) (@lem5260973 s)). Qed.
Lemma lem5260976 (s : real -> Prop) : (term189 s) = (term189 s).
Proof. exact (MK_COMB (@lem5260975 s) (@lem5260959)). Qed.
Lemma lem5260979 (s : real -> Prop) : (term190 s) = (term190 s).
Proof. exact (eq_refl (term190 s)). Qed.
Lemma lem5260980 (s : real -> Prop) : (term192 s) = (term192 s).
Proof. exact (MK_COMB (@lem5260979 s) (@lem5260976 s)). Qed.
Lemma lem5260985 (s : real -> Prop) (x : real) (B : real) : (term249 s x B) = (term249 s x B).
Proof. exact (eq_refl (term249 s x B)). Qed.
Lemma lem5260986 (s : real -> Prop) (B : real) : (term250 s B) = (term250 s B).
Proof. exact (fun_ext (fun x : real => @lem5260985 s x B)). Qed.
Lemma lem5260987 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5260988 (s : real -> Prop) (B : real) : (term146 s B) = (term146 s B).
Proof. exact (MK_COMB (@lem5260987) (@lem5260986 s B)). Qed.
Lemma lem5260989 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5260990 (s : real -> Prop) (B : real) : (term193 s B) = (term193 s B).
Proof. exact (MK_COMB (@lem5260989) (@lem5260988 s B)). Qed.
Lemma lem5260991 (B : real) (s : real -> Prop) : (term195 B s) = (term195 B s).
Proof. exact (MK_COMB (@lem5260990 s B) (@lem5260980 s)). Qed.
Lemma lem5260996 (s : real -> Prop) : (term196 s) = (term196 s).
Proof. exact (eq_refl (term196 s)). Qed.
Lemma lem5260997 (B : real) (s : real -> Prop) : (term197 B s) = (term197 B s).
Proof. exact (MK_COMB (@lem5260996 s) (@lem5260991 B s)). Qed.
Lemma lem5260998 (s : real -> Prop) : (term199 s) = (term199 s).
Proof. exact (fun_ext (fun B : real => @lem5260997 B s)). Qed.
Lemma lem5260999 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261000 (s : real -> Prop) : (term201 s) = (term201 s).
Proof. exact (MK_COMB (@lem5260999) (@lem5260998 s)). Qed.
Lemma lem5261001 : term203 = term203.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5261000 s)). Qed.
Lemma lem5261002 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5261003 : term205 = term205.
Proof. exact (MK_COMB (@lem5261002) (@lem5261001)). Qed.
Lemma lem5261162 : term204 = term205.
Proof. exact (TRANS (@lem5260838) (@lem5261003)). Qed.
Lemma lem5261163 : term205 = term204.
Proof. exact (SYM (@lem5261162)). Qed.
Lemma lem5261165 (s : real -> Prop) (B : real) (h1 : term146 s B) : term146 s B.
Proof. exact (h1). Qed.
Lemma lem5261167 (s : real -> Prop) (h1 : term173 s) : term173 s.
Proof. exact (h1). Qed.
Lemma lem5261168 (h1 : term248) : term248.
Proof. exact (h1). Qed.
Lemma lem5261169 (h1 : term229) : term229.
Proof. exact (h1). Qed.
Lemma lem5261170 (h1 : term180) : term180.
Proof. exact (h1). Qed.
Lemma lem5261176 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5261183 (s : real -> Prop) (x : real) (B : real) : (term249 s x B) = (term251 s x B).
Proof. exact (@lem17265 (@IN real x s) (term224 x B)). Qed.
Lemma lem5261184 (s : real -> Prop) (B : real) : (term250 s B) = (term252 s B).
Proof. exact (fun_ext (fun x : real => @lem5261183 s x B)). Qed.
Lemma lem5261185 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261238 (s : real -> Prop) (B : real) : (term146 s B) = (term253 s B).
Proof. exact (MK_COMB (@lem5261185) (@lem5261184 s B)). Qed.
Lemma lem5261239 (s : real -> Prop) (B : real) (h1 : term146 s B) : term253 s B.
Proof. exact (EQ_MP (@lem5261238 s B) (@lem5261165 s B h1)). Qed.
Lemma lem5261245 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (sup s) = (inf s).
Proof. exact (h1). Qed.
Lemma lem5261253 (s : real -> Prop) (x : real) : (term254 s x) = (term255 s x).
Proof. exact (@lem17045 (term155 x s) (term161 s x)). Qed.
Lemma lem5261255 (x : real) (s : real -> Prop) : (term256 x s) = (term256 x s).
Proof. exact (eq_refl (term256 x s)). Qed.
Lemma lem5261256 (s : real -> Prop) (x : real) : (term257 s x) = (term258 s x).
Proof. exact (MK_COMB (@lem5261255 x s) (@lem5261253 s x)). Qed.
Lemma lem5261257 (s : real -> Prop) (x : real) : (term259 s x) = (term257 s x).
Proof. exact (@lem17362 (@IN real x s) (term162 s x)). Qed.
Lemma lem5261258 (s : real -> Prop) (x : real) : (term259 s x) = (term258 s x).
Proof. exact (TRANS (@lem5261257 s x) (@lem5261256 s x)). Qed.
Lemma lem5261259 (P : real -> Prop) : (term260 P) = (term261 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5261260 (s : real -> Prop) : (term173 s) = (term262 s).
Proof. exact (@lem5261259 (term167 s)). Qed.
Lemma lem5261261 (s : real -> Prop) (x : real) : (term263 s x) = (term165 s x).
Proof. exact (eq_refl (term263 s x)). Qed.
Lemma lem5261262 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5261263 (s : real -> Prop) (x : real) : (term264 s x) = (term259 s x).
Proof. exact (MK_COMB (@lem5261262) (@lem5261261 s x)). Qed.
Lemma lem5261264 (s : real -> Prop) (x : real) : (term264 s x) = (term258 s x).
Proof. exact (TRANS (@lem5261263 s x) (@lem5261258 s x)). Qed.
Lemma lem5261265 (s : real -> Prop) : (term265 s) = (term266 s).
Proof. exact (fun_ext (fun x : real => @lem5261264 s x)). Qed.
Lemma lem5261266 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5261267 (s : real -> Prop) : (term262 s) = (term267 s).
Proof. exact (MK_COMB (@lem5261266) (@lem5261265 s)). Qed.
Lemma lem5261320 (s : real -> Prop) : (term173 s) = (term267 s).
Proof. exact (TRANS (@lem5261260 s) (@lem5261267 s)). Qed.
Lemma lem5261321 (s : real -> Prop) (h1 : term173 s) : term267 s.
Proof. exact (EQ_MP (@lem5261320 s) (@lem5261167 s h1)). Qed.
Lemma lem5261324 (s : real -> Prop) : (term268 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5261331 (s : real -> Prop) (b : real) (x : real) : (term269 s b x) = (term270 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5261332 (P : real -> Prop) : (term260 P) = (term261 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5261333 (s : real -> Prop) (b : real) : (term271 s b) = (term272 s b).
Proof. exact (@lem5261332 (term231 s b)). Qed.
Lemma lem5261334 (s : real -> Prop) (b : real) (x : real) : (term273 s b x) = (term230 s b x).
Proof. exact (eq_refl (term273 s b x)). Qed.
Lemma lem5261335 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5261336 (s : real -> Prop) (b : real) (x : real) : (term274 s b x) = (term269 s b x).
Proof. exact (MK_COMB (@lem5261335) (@lem5261334 s b x)). Qed.
Lemma lem5261337 (s : real -> Prop) (b : real) (x : real) : (term274 s b x) = (term270 s b x).
Proof. exact (TRANS (@lem5261336 s b x) (@lem5261331 s b x)). Qed.
Lemma lem5261338 (s : real -> Prop) (b : real) : (term275 s b) = (term276 s b).
Proof. exact (fun_ext (fun x : real => @lem5261337 s b x)). Qed.
Lemma lem5261339 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5261340 (s : real -> Prop) (b : real) : (term272 s b) = (term277 s b).
Proof. exact (MK_COMB (@lem5261339) (@lem5261338 s b)). Qed.
Lemma lem5261341 (s : real -> Prop) (b : real) : (term271 s b) = (term277 s b).
Proof. exact (TRANS (@lem5261333 s b) (@lem5261340 s b)). Qed.
Lemma lem5261342 (P : real -> Prop) : (term278 P) = (term279 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5261343 (s : real -> Prop) : (term280 s) = (term281 s).
Proof. exact (@lem5261342 (term242 s)). Qed.
Lemma lem5261344 (s : real -> Prop) (b : real) : (term282 s b) = (term232 s b).
Proof. exact (eq_refl (term282 s b)). Qed.
Lemma lem5261345 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5261346 (s : real -> Prop) (b : real) : (term283 s b) = (term271 s b).
Proof. exact (MK_COMB (@lem5261345) (@lem5261344 s b)). Qed.
Lemma lem5261347 (s : real -> Prop) (b : real) : (term283 s b) = (term277 s b).
Proof. exact (TRANS (@lem5261346 s b) (@lem5261341 s b)). Qed.
Lemma lem5261348 (s : real -> Prop) : (term284 s) = (term285 s).
Proof. exact (fun_ext (fun b : real => @lem5261347 s b)). Qed.
Lemma lem5261349 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261350 (s : real -> Prop) : (term281 s) = (term286 s).
Proof. exact (MK_COMB (@lem5261349) (@lem5261348 s)). Qed.
Lemma lem5261351 (s : real -> Prop) : (term280 s) = (term286 s).
Proof. exact (TRANS (@lem5261343 s) (@lem5261350 s)). Qed.
Lemma lem5261352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5261353 (s : real -> Prop) : (term287 s) = (term288 s).
Proof. exact (MK_COMB (@lem5261352) (@lem5261324 s)). Qed.
Lemma lem5261354 (s : real -> Prop) : (term289 s) = (term290 s).
Proof. exact (MK_COMB (@lem5261353 s) (@lem5261351 s)). Qed.
Lemma lem5261355 (s : real -> Prop) : (term291 s) = (term289 s).
Proof. exact (@lem17045 (term145 s) (term243 s)). Qed.
Lemma lem5261356 (s : real -> Prop) : (term291 s) = (term290 s).
Proof. exact (TRANS (@lem5261355 s) (@lem5261354 s)). Qed.
Lemma lem5261363 (s : real -> Prop) (x : real) : (term237 s x) = (term292 s x).
Proof. exact (@lem17265 (@IN real x s) (term161 s x)). Qed.
Lemma lem5261364 (s : real -> Prop) : (term238 s) = (term293 s).
Proof. exact (fun_ext (fun x : real => @lem5261363 s x)). Qed.
Lemma lem5261365 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261366 (s : real -> Prop) : (term239 s) = (term294 s).
Proof. exact (MK_COMB (@lem5261365) (@lem5261364 s)). Qed.
Lemma lem5261373 (s : real -> Prop) (b : real) (x : real) : (term269 s b x) = (term270 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5261374 (P : real -> Prop) : (term260 P) = (term261 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5261375 (s : real -> Prop) (b : real) : (term271 s b) = (term272 s b).
Proof. exact (@lem5261374 (term231 s b)). Qed.
Lemma lem5261376 (s : real -> Prop) (b : real) (x : real) : (term273 s b x) = (term230 s b x).
Proof. exact (eq_refl (term273 s b x)). Qed.
Lemma lem5261377 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5261378 (s : real -> Prop) (b : real) (x : real) : (term274 s b x) = (term269 s b x).
Proof. exact (MK_COMB (@lem5261377) (@lem5261376 s b x)). Qed.
Lemma lem5261379 (s : real -> Prop) (b : real) (x : real) : (term274 s b x) = (term270 s b x).
Proof. exact (TRANS (@lem5261378 s b x) (@lem5261373 s b x)). Qed.
Lemma lem5261380 (s : real -> Prop) (b : real) : (term275 s b) = (term276 s b).
Proof. exact (fun_ext (fun x : real => @lem5261379 s b x)). Qed.
Lemma lem5261381 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5261382 (s : real -> Prop) (b : real) : (term272 s b) = (term277 s b).
Proof. exact (MK_COMB (@lem5261381) (@lem5261380 s b)). Qed.
Lemma lem5261383 (s : real -> Prop) (b : real) : (term271 s b) = (term277 s b).
Proof. exact (TRANS (@lem5261375 s b) (@lem5261382 s b)). Qed.
Lemma lem5261384 (b : real) (s : real -> Prop) : (term155 b s) = (term155 b s).
Proof. exact (eq_refl (term155 b s)). Qed.
Lemma lem5261385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5261386 (s : real -> Prop) (b : real) : (term295 s b) = (term296 s b).
Proof. exact (MK_COMB (@lem5261385) (@lem5261383 s b)). Qed.
Lemma lem5261387 (b : real) (s : real -> Prop) : (term297 b s) = (term298 b s).
Proof. exact (MK_COMB (@lem5261386 s b) (@lem5261384 b s)). Qed.
Lemma lem5261388 (b : real) (s : real -> Prop) : (term234 b s) = (term297 b s).
Proof. exact (@lem17265 (term232 s b) (term155 b s)). Qed.
Lemma lem5261389 (b : real) (s : real -> Prop) : (term234 b s) = (term298 b s).
Proof. exact (TRANS (@lem5261388 b s) (@lem5261387 b s)). Qed.
Lemma lem5261390 (s : real -> Prop) : (term235 s) = (term299 s).
Proof. exact (fun_ext (fun b : real => @lem5261389 b s)). Qed.
Lemma lem5261391 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261392 (s : real -> Prop) : (term236 s) = (term300 s).
Proof. exact (MK_COMB (@lem5261391) (@lem5261390 s)). Qed.
Lemma lem5261393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5261394 (s : real -> Prop) : (term240 s) = (term301 s).
Proof. exact (MK_COMB (@lem5261393) (@lem5261366 s)). Qed.
Lemma lem5261395 (s : real -> Prop) : (term241 s) = (term302 s).
Proof. exact (MK_COMB (@lem5261394 s) (@lem5261392 s)). Qed.
Lemma lem5261396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5261397 (s : real -> Prop) : (term303 s) = (term304 s).
Proof. exact (MK_COMB (@lem5261396) (@lem5261356 s)). Qed.
Lemma lem5261398 (s : real -> Prop) : (term305 s) = (term306 s).
Proof. exact (MK_COMB (@lem5261397 s) (@lem5261395 s)). Qed.
Lemma lem5261399 (s : real -> Prop) : (term246 s) = (term305 s).
Proof. exact (@lem17265 (term244 s) (term241 s)). Qed.
Lemma lem5261400 (s : real -> Prop) : (term246 s) = (term306 s).
Proof. exact (TRANS (@lem5261399 s) (@lem5261398 s)). Qed.
Lemma lem5261401 : term247 = term307.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5261400 s)). Qed.
Lemma lem5261402 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5261403 : term248 = term308.
Proof. exact (MK_COMB (@lem5261402) (@lem5261401)). Qed.
Lemma lem5261650 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5261651 (P : type1626) : (term311 P) = (term312 P).
Proof. exact (@lem5261650 real real P). Qed.
Lemma lem5261652 (s : real -> Prop) : (term313 s) = (term314 s).
Proof. exact (@lem5261651 (term315 s)). Qed.
Lemma lem5261653 (s : real -> Prop) (b : real) : (term316 s b) = (term276 s b).
Proof. exact (eq_refl (term316 s b)). Qed.
Lemma lem5261654 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5261655 (s : real -> Prop) (b : real) (x : real) : (term317 s b x) = (term318 s b x).
Proof. exact (MK_COMB (@lem5261653 s b) (@lem5261654 x)). Qed.
Lemma lem5261656 (s : real -> Prop) (b : real) (x : real) : (term318 s b x) = (term270 s b x).
Proof. exact (eq_refl (term318 s b x)). Qed.
Lemma lem5261657 (s : real -> Prop) (b : real) (x : real) : (term317 s b x) = (term270 s b x).
Proof. exact (TRANS (@lem5261655 s b x) (@lem5261656 s b x)). Qed.
Lemma lem5261658 (s : real -> Prop) (b : real) : (term319 s b) = (term276 s b).
Proof. exact (fun_ext (fun x : real => @lem5261657 s b x)). Qed.
Lemma lem5261659 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5261660 (s : real -> Prop) (b : real) : (term320 s b) = (term277 s b).
Proof. exact (MK_COMB (@lem5261659) (@lem5261658 s b)). Qed.
Lemma lem5261661 (s : real -> Prop) : (term321 s) = (term285 s).
Proof. exact (fun_ext (fun b : real => @lem5261660 s b)). Qed.
Lemma lem5261662 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261663 (s : real -> Prop) : (term313 s) = (term286 s).
Proof. exact (MK_COMB (@lem5261662) (@lem5261661 s)). Qed.
Lemma lem5261664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5261665 (s : real -> Prop) : (term322 s) = (term323 s).
Proof. exact (MK_COMB (@lem5261664) (@lem5261663 s)). Qed.
Lemma lem5261666 (s : real -> Prop) (b : real) : (term316 s b) = (term276 s b).
Proof. exact (eq_refl (term316 s b)). Qed.
Lemma lem5261667 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5261668 (s : real -> Prop) (x : real -> real) (b : real) : (term324 s x b) = (term325 s x b).
Proof. exact (MK_COMB (@lem5261666 s b) (@lem5261667 x b)). Qed.
Lemma lem5261669 (s : real -> Prop) (x : real -> real) (b : real) : (term325 s x b) = (term326 s x b).
Proof. exact (eq_refl (term325 s x b)). Qed.
Lemma lem5261670 (s : real -> Prop) (x : real -> real) (b : real) : (term324 s x b) = (term326 s x b).
Proof. exact (TRANS (@lem5261668 s x b) (@lem5261669 s x b)). Qed.
Lemma lem5261671 (s : real -> Prop) (x : real -> real) : (term327 s x) = (term328 s x).
Proof. exact (fun_ext (fun b : real => @lem5261670 s x b)). Qed.
Lemma lem5261672 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261673 (s : real -> Prop) (x : real -> real) : (term329 s x) = (term330 s x).
Proof. exact (MK_COMB (@lem5261672) (@lem5261671 s x)). Qed.
Lemma lem5261674 (s : real -> Prop) : (term331 s) = (term332 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5261673 s x)). Qed.
Lemma lem5261675 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5261676 (s : real -> Prop) : (term314 s) = (term333 s).
Proof. exact (MK_COMB (@lem5261675) (@lem5261674 s)). Qed.
Lemma lem5261677 (s : real -> Prop) : ((term313 s) = (term314 s)) = ((term286 s) = (term333 s)).
Proof. exact (MK_COMB (@lem5261665 s) (@lem5261676 s)). Qed.
Lemma lem5261678 (s : real -> Prop) : (term286 s) = (term333 s).
Proof. exact (EQ_MP (@lem5261677 s) (@lem5261652 s)). Qed.
Lemma lem5261679 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5261680 (s : real -> Prop) : (term290 s) = (term334 s).
Proof. exact (MK_COMB (@lem5261679 s) (@lem5261678 s)). Qed.
Lemma lem5261682 {A : Type'} (P : Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5261683 (P : Prop) (Q : type1028) : (term337 P Q) = (term338 P Q).
Proof. exact (@lem5261682 (real -> real) P Q). Qed.
Lemma lem5261684 (s : real -> Prop) : (term339 s) = (term340 s).
Proof. exact (@lem5261683 (s = (@EMPTY real)) (term332 s)). Qed.
Lemma lem5261685 (s : real -> Prop) (x : real -> real) : (term341 s x) = (term330 s x).
Proof. exact (eq_refl (term341 s x)). Qed.
Lemma lem5261686 (s : real -> Prop) : (term342 s) = (term332 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5261685 s x)). Qed.
Lemma lem5261687 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5261688 (s : real -> Prop) : (term343 s) = (term333 s).
Proof. exact (MK_COMB (@lem5261687) (@lem5261686 s)). Qed.
Lemma lem5261689 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5261690 (s : real -> Prop) : (term339 s) = (term334 s).
Proof. exact (MK_COMB (@lem5261689 s) (@lem5261688 s)). Qed.
Lemma lem5261691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5261692 (s : real -> Prop) : (term344 s) = (term345 s).
Proof. exact (MK_COMB (@lem5261691) (@lem5261690 s)). Qed.
Lemma lem5261693 (s : real -> Prop) (x : real -> real) : (term341 s x) = (term330 s x).
Proof. exact (eq_refl (term341 s x)). Qed.
Lemma lem5261694 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5261695 (s : real -> Prop) (x : real -> real) : (term346 s x) = (term347 s x).
Proof. exact (MK_COMB (@lem5261694 s) (@lem5261693 s x)). Qed.
Lemma lem5261696 (s : real -> Prop) : (term348 s) = (term349 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5261695 s x)). Qed.
Lemma lem5261697 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5261698 (s : real -> Prop) : (term340 s) = (term350 s).
Proof. exact (MK_COMB (@lem5261697) (@lem5261696 s)). Qed.
Lemma lem5261699 (s : real -> Prop) : ((term339 s) = (term340 s)) = ((term334 s) = (term350 s)).
Proof. exact (MK_COMB (@lem5261692 s) (@lem5261698 s)). Qed.
Lemma lem5261700 (s : real -> Prop) : (term334 s) = (term350 s).
Proof. exact (EQ_MP (@lem5261699 s) (@lem5261684 s)). Qed.
Lemma lem5261701 (s : real -> Prop) : (term290 s) = (term350 s).
Proof. exact (TRANS (@lem5261680 s) (@lem5261700 s)). Qed.
Lemma lem5261702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5261703 (s : real -> Prop) : (term304 s) = (term351 s).
Proof. exact (MK_COMB (@lem5261702) (@lem5261701 s)). Qed.
Lemma lem5261705 {A : Type'} (P : A -> Prop) (Q : Prop) : (term352 A P Q) = (term353 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5261706 (P : real -> Prop) (Q : Prop) : (term354 P Q) = (term355 P Q).
Proof. exact (@lem5261705 real P Q). Qed.
Lemma lem5261707 (b : real) (s : real -> Prop) : (term356 b s) = (term357 b s).
Proof. exact (@lem5261706 (term276 s b) (term155 b s)). Qed.
Lemma lem5261708 (s : real -> Prop) (b : real) (x : real) : (term318 s b x) = (term270 s b x).
Proof. exact (eq_refl (term318 s b x)). Qed.
Lemma lem5261709 (s : real -> Prop) (b : real) : (term358 s b) = (term276 s b).
Proof. exact (fun_ext (fun x : real => @lem5261708 s b x)). Qed.
Lemma lem5261710 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5261711 (s : real -> Prop) (b : real) : (term359 s b) = (term277 s b).
Proof. exact (MK_COMB (@lem5261710) (@lem5261709 s b)). Qed.
Lemma lem5261712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5261713 (s : real -> Prop) (b : real) : (term360 s b) = (term296 s b).
Proof. exact (MK_COMB (@lem5261712) (@lem5261711 s b)). Qed.
Lemma lem5261714 (b : real) (s : real -> Prop) : (term155 b s) = (term155 b s).
Proof. exact (eq_refl (term155 b s)). Qed.
Lemma lem5261715 (b : real) (s : real -> Prop) : (term356 b s) = (term298 b s).
Proof. exact (MK_COMB (@lem5261713 s b) (@lem5261714 b s)). Qed.
Lemma lem5261716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5261717 (b : real) (s : real -> Prop) : (term361 b s) = (term362 b s).
Proof. exact (MK_COMB (@lem5261716) (@lem5261715 b s)). Qed.
Lemma lem5261718 (s : real -> Prop) (b : real) (x : real) : (term318 s b x) = (term270 s b x).
Proof. exact (eq_refl (term318 s b x)). Qed.
Lemma lem5261719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5261720 (s : real -> Prop) (b : real) (x : real) : (term363 s b x) = (term364 s b x).
Proof. exact (MK_COMB (@lem5261719) (@lem5261718 s b x)). Qed.
Lemma lem5261721 (b : real) (s : real -> Prop) : (term155 b s) = (term155 b s).
Proof. exact (eq_refl (term155 b s)). Qed.
Lemma lem5261722 (x : real) (b : real) (s : real -> Prop) : (term365 x b s) = (term366 x b s).
Proof. exact (MK_COMB (@lem5261720 s b x) (@lem5261721 b s)). Qed.
Lemma lem5261723 (b : real) (s : real -> Prop) : (term367 b s) = (term368 b s).
Proof. exact (fun_ext (fun x : real => @lem5261722 x b s)). Qed.
Lemma lem5261724 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5261725 (b : real) (s : real -> Prop) : (term357 b s) = (term369 b s).
Proof. exact (MK_COMB (@lem5261724) (@lem5261723 b s)). Qed.
Lemma lem5261726 (b : real) (s : real -> Prop) : ((term356 b s) = (term357 b s)) = ((term298 b s) = (term369 b s)).
Proof. exact (MK_COMB (@lem5261717 b s) (@lem5261725 b s)). Qed.
Lemma lem5261727 (b : real) (s : real -> Prop) : (term298 b s) = (term369 b s).
Proof. exact (EQ_MP (@lem5261726 b s) (@lem5261707 b s)). Qed.
Lemma lem5261728 (s : real -> Prop) : (term299 s) = (term370 s).
Proof. exact (fun_ext (fun b : real => @lem5261727 b s)). Qed.
Lemma lem5261729 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261730 (s : real -> Prop) : (term300 s) = (term371 s).
Proof. exact (MK_COMB (@lem5261729) (@lem5261728 s)). Qed.
Lemma lem5261732 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5261733 (P : type1626) : (term311 P) = (term312 P).
Proof. exact (@lem5261732 real real P). Qed.
Lemma lem5261734 (s : real -> Prop) : (term372 s) = (term373 s).
Proof. exact (@lem5261733 (term374 s)). Qed.
Lemma lem5261735 (b : real) (s : real -> Prop) : (term375 s b) = (term368 b s).
Proof. exact (eq_refl (term375 s b)). Qed.
Lemma lem5261736 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5261737 (b : real) (s : real -> Prop) (x : real) : (term376 s b x) = (term377 b s x).
Proof. exact (MK_COMB (@lem5261735 b s) (@lem5261736 x)). Qed.
Lemma lem5261738 (x : real) (b : real) (s : real -> Prop) : (term377 b s x) = (term366 x b s).
Proof. exact (eq_refl (term377 b s x)). Qed.
Lemma lem5261739 (x : real) (b : real) (s : real -> Prop) : (term376 s b x) = (term366 x b s).
Proof. exact (TRANS (@lem5261737 b s x) (@lem5261738 x b s)). Qed.
Lemma lem5261740 (b : real) (s : real -> Prop) : (term378 s b) = (term368 b s).
Proof. exact (fun_ext (fun x : real => @lem5261739 x b s)). Qed.
Lemma lem5261741 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5261742 (b : real) (s : real -> Prop) : (term379 s b) = (term369 b s).
Proof. exact (MK_COMB (@lem5261741) (@lem5261740 b s)). Qed.
Lemma lem5261743 (s : real -> Prop) : (term380 s) = (term370 s).
Proof. exact (fun_ext (fun b : real => @lem5261742 b s)). Qed.
Lemma lem5261744 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261745 (s : real -> Prop) : (term372 s) = (term371 s).
Proof. exact (MK_COMB (@lem5261744) (@lem5261743 s)). Qed.
Lemma lem5261746 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5261747 (s : real -> Prop) : (term381 s) = (term382 s).
Proof. exact (MK_COMB (@lem5261746) (@lem5261745 s)). Qed.
Lemma lem5261748 (b : real) (s : real -> Prop) : (term375 s b) = (term368 b s).
Proof. exact (eq_refl (term375 s b)). Qed.
Lemma lem5261749 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5261750 (s : real -> Prop) (x : real -> real) (b : real) : (term383 s x b) = (term384 s x b).
Proof. exact (MK_COMB (@lem5261748 b s) (@lem5261749 x b)). Qed.
Lemma lem5261751 (x : real -> real) (b : real) (s : real -> Prop) : (term384 s x b) = (term385 x b s).
Proof. exact (eq_refl (term384 s x b)). Qed.
Lemma lem5261752 (x : real -> real) (b : real) (s : real -> Prop) : (term383 s x b) = (term385 x b s).
Proof. exact (TRANS (@lem5261750 s x b) (@lem5261751 x b s)). Qed.
Lemma lem5261753 (x : real -> real) (s : real -> Prop) : (term386 s x) = (term387 x s).
Proof. exact (fun_ext (fun b : real => @lem5261752 x b s)). Qed.
Lemma lem5261754 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261755 (x : real -> real) (s : real -> Prop) : (term388 s x) = (term389 x s).
Proof. exact (MK_COMB (@lem5261754) (@lem5261753 x s)). Qed.
Lemma lem5261756 (s : real -> Prop) : (term390 s) = (term391 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5261755 x s)). Qed.
Lemma lem5261757 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5261758 (s : real -> Prop) : (term373 s) = (term392 s).
Proof. exact (MK_COMB (@lem5261757) (@lem5261756 s)). Qed.
Lemma lem5261759 (s : real -> Prop) : ((term372 s) = (term373 s)) = ((term371 s) = (term392 s)).
Proof. exact (MK_COMB (@lem5261747 s) (@lem5261758 s)). Qed.
Lemma lem5261760 (s : real -> Prop) : (term371 s) = (term392 s).
Proof. exact (EQ_MP (@lem5261759 s) (@lem5261734 s)). Qed.
Lemma lem5261761 (s : real -> Prop) : (term300 s) = (term392 s).
Proof. exact (TRANS (@lem5261730 s) (@lem5261760 s)). Qed.
Lemma lem5261762 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5261763 (s : real -> Prop) : (term302 s) = (term393 s).
Proof. exact (MK_COMB (@lem5261762 s) (@lem5261761 s)). Qed.
Lemma lem5261765 {A : Type'} (P : Prop) (Q : A -> Prop) : (term394 A P Q) = (term395 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5261766 (P : Prop) (Q : type1028) : (term396 P Q) = (term397 P Q).
Proof. exact (@lem5261765 (real -> real) P Q). Qed.
Lemma lem5261767 (s : real -> Prop) : (term398 s) = (term399 s).
Proof. exact (@lem5261766 (term294 s) (term391 s)). Qed.
Lemma lem5261768 (x : real -> real) (s : real -> Prop) : (term400 s x) = (term389 x s).
Proof. exact (eq_refl (term400 s x)). Qed.
Lemma lem5261769 (s : real -> Prop) : (term401 s) = (term391 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5261768 x s)). Qed.
Lemma lem5261770 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5261771 (s : real -> Prop) : (term402 s) = (term392 s).
Proof. exact (MK_COMB (@lem5261770) (@lem5261769 s)). Qed.
Lemma lem5261772 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5261773 (s : real -> Prop) : (term398 s) = (term393 s).
Proof. exact (MK_COMB (@lem5261772 s) (@lem5261771 s)). Qed.
Lemma lem5261774 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5261775 (s : real -> Prop) : (term403 s) = (term404 s).
Proof. exact (MK_COMB (@lem5261774) (@lem5261773 s)). Qed.
Lemma lem5261776 (x : real -> real) (s : real -> Prop) : (term400 s x) = (term389 x s).
Proof. exact (eq_refl (term400 s x)). Qed.
Lemma lem5261777 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5261778 (x : real -> real) (s : real -> Prop) : (term405 s x) = (term406 x s).
Proof. exact (MK_COMB (@lem5261777 s) (@lem5261776 x s)). Qed.
Lemma lem5261779 (s : real -> Prop) : (term407 s) = (term408 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5261778 x s)). Qed.
Lemma lem5261780 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5261781 (s : real -> Prop) : (term399 s) = (term409 s).
Proof. exact (MK_COMB (@lem5261780) (@lem5261779 s)). Qed.
Lemma lem5261782 (s : real -> Prop) : ((term398 s) = (term399 s)) = ((term393 s) = (term409 s)).
Proof. exact (MK_COMB (@lem5261775 s) (@lem5261781 s)). Qed.
Lemma lem5261783 (s : real -> Prop) : (term393 s) = (term409 s).
Proof. exact (EQ_MP (@lem5261782 s) (@lem5261767 s)). Qed.
Lemma lem5261784 (s : real -> Prop) : (term302 s) = (term409 s).
Proof. exact (TRANS (@lem5261763 s) (@lem5261783 s)). Qed.
Lemma lem5261785 (s : real -> Prop) : (term306 s) = (term410 s).
Proof. exact (MK_COMB (@lem5261703 s) (@lem5261784 s)). Qed.
Lemma lem5261787 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5261788 (P : type1028) (Q : type1028) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem5261787 (real -> real) P Q). Qed.
Lemma lem5261789 (s : real -> Prop) : (term415 s) = (term416 s).
Proof. exact (@lem5261788 (term349 s) (term408 s)). Qed.
Lemma lem5261790 (s : real -> Prop) (x : real -> real) : (term417 s x) = (term347 s x).
Proof. exact (eq_refl (term417 s x)). Qed.
Lemma lem5261791 (s : real -> Prop) : (term418 s) = (term349 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5261790 s x)). Qed.
Lemma lem5261792 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5261793 (s : real -> Prop) : (term419 s) = (term350 s).
Proof. exact (MK_COMB (@lem5261792) (@lem5261791 s)). Qed.
Lemma lem5261794 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5261795 (s : real -> Prop) : (term420 s) = (term351 s).
Proof. exact (MK_COMB (@lem5261794) (@lem5261793 s)). Qed.
Lemma lem5261796 (x : real -> real) (s : real -> Prop) : (term421 s x) = (term406 x s).
Proof. exact (eq_refl (term421 s x)). Qed.
Lemma lem5261797 (s : real -> Prop) : (term422 s) = (term408 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5261796 x s)). Qed.
Lemma lem5261798 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5261799 (s : real -> Prop) : (term423 s) = (term409 s).
Proof. exact (MK_COMB (@lem5261798) (@lem5261797 s)). Qed.
Lemma lem5261800 (s : real -> Prop) : (term415 s) = (term410 s).
Proof. exact (MK_COMB (@lem5261795 s) (@lem5261799 s)). Qed.
Lemma lem5261801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5261802 (s : real -> Prop) : (term424 s) = (term425 s).
Proof. exact (MK_COMB (@lem5261801) (@lem5261800 s)). Qed.
Lemma lem5261803 (s : real -> Prop) (x : real -> real) : (term417 s x) = (term347 s x).
Proof. exact (eq_refl (term417 s x)). Qed.
Lemma lem5261804 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5261805 (s : real -> Prop) (x : real -> real) : (term426 s x) = (term427 s x).
Proof. exact (MK_COMB (@lem5261804) (@lem5261803 s x)). Qed.
Lemma lem5261806 (x : real -> real) (s : real -> Prop) : (term421 s x) = (term406 x s).
Proof. exact (eq_refl (term421 s x)). Qed.
Lemma lem5261807 (x : real -> real) (s : real -> Prop) : (term428 s x) = (term429 x s).
Proof. exact (MK_COMB (@lem5261805 s x) (@lem5261806 x s)). Qed.
Lemma lem5261808 (s : real -> Prop) : (term430 s) = (term431 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5261807 x s)). Qed.
Lemma lem5261809 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5261810 (s : real -> Prop) : (term416 s) = (term432 s).
Proof. exact (MK_COMB (@lem5261809) (@lem5261808 s)). Qed.
Lemma lem5261811 (s : real -> Prop) : ((term415 s) = (term416 s)) = ((term410 s) = (term432 s)).
Proof. exact (MK_COMB (@lem5261802 s) (@lem5261810 s)). Qed.
Lemma lem5261812 (s : real -> Prop) : (term410 s) = (term432 s).
Proof. exact (EQ_MP (@lem5261811 s) (@lem5261789 s)). Qed.
Lemma lem5261813 (s : real -> Prop) : (term306 s) = (term432 s).
Proof. exact (TRANS (@lem5261785 s) (@lem5261812 s)). Qed.
Lemma lem5261814 : term307 = term433.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5261813 s)). Qed.
Lemma lem5261815 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5261816 : term308 = term434.
Proof. exact (MK_COMB (@lem5261815) (@lem5261814)). Qed.
Lemma lem5261818 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5261819 (P : type1017) : (term435 P) = (term436 P).
Proof. exact (@lem5261818 (real -> Prop) (real -> real) P). Qed.
Lemma lem5261820 : term437 = term438.
Proof. exact (@lem5261819 term439). Qed.
Lemma lem5261821 (s : real -> Prop) : (term440 s) = (term431 s).
Proof. exact (eq_refl (term440 s)). Qed.
Lemma lem5261822 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5261823 (s : real -> Prop) (x : real -> real) : (term441 s x) = (term442 s x).
Proof. exact (MK_COMB (@lem5261821 s) (@lem5261822 x)). Qed.
Lemma lem5261824 (x : real -> real) (s : real -> Prop) : (term442 s x) = (term429 x s).
Proof. exact (eq_refl (term442 s x)). Qed.
Lemma lem5261825 (x : real -> real) (s : real -> Prop) : (term441 s x) = (term429 x s).
Proof. exact (TRANS (@lem5261823 s x) (@lem5261824 x s)). Qed.
Lemma lem5261826 (s : real -> Prop) : (term443 s) = (term431 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5261825 x s)). Qed.
Lemma lem5261827 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5261828 (s : real -> Prop) : (term444 s) = (term432 s).
Proof. exact (MK_COMB (@lem5261827) (@lem5261826 s)). Qed.
Lemma lem5261829 : term445 = term433.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5261828 s)). Qed.
Lemma lem5261830 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5261831 : term437 = term434.
Proof. exact (MK_COMB (@lem5261830) (@lem5261829)). Qed.
Lemma lem5261832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5261833 : term446 = term447.
Proof. exact (MK_COMB (@lem5261832) (@lem5261831)). Qed.
Lemma lem5261834 (s : real -> Prop) : (term440 s) = (term431 s).
Proof. exact (eq_refl (term440 s)). Qed.
Lemma lem5261835 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5261836 (x : type1021) (s : real -> Prop) : (term448 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5261834 s) (@lem5261835 x s)). Qed.
Lemma lem5261837 (x : type1021) (s : real -> Prop) : (term449 x s) = (term450 x s).
Proof. exact (eq_refl (term449 x s)). Qed.
Lemma lem5261838 (x : type1021) (s : real -> Prop) : (term448 x s) = (term450 x s).
Proof. exact (TRANS (@lem5261836 x s) (@lem5261837 x s)). Qed.
Lemma lem5261839 (x : type1021) : (term451 x) = (term452 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5261838 x s)). Qed.
Lemma lem5261840 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5261841 (x : type1021) : (term453 x) = (term454 x).
Proof. exact (MK_COMB (@lem5261840) (@lem5261839 x)). Qed.
Lemma lem5261842 : term455 = term456.
Proof. exact (fun_ext (fun x : type1021 => @lem5261841 x)). Qed.
Lemma lem5261843 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5261844 : term438 = term457.
Proof. exact (MK_COMB (@lem5261843) (@lem5261842)). Qed.
Lemma lem5261845 : (term437 = term438) = (term434 = term457).
Proof. exact (MK_COMB (@lem5261833) (@lem5261844)). Qed.
Lemma lem5261846 : term434 = term457.
Proof. exact (EQ_MP (@lem5261845) (@lem5261820)). Qed.
Lemma lem5261848 : term308 = term457.
Proof. exact (TRANS (@lem5261816) (@lem5261846)). Qed.
Lemma lem5261849 : term248 = term457.
Proof. exact (TRANS (@lem5261403) (@lem5261848)). Qed.
Lemma lem5261850 (h1 : term248) : term457.
Proof. exact (EQ_MP (@lem5261849) (@lem5261168 h1)). Qed.
Lemma lem5261861 (x : real) (k : real) : (term458 x k) = (term459 x k).
Proof. exact (@lem17045 (term460 k x) (real_le x k)). Qed.
Lemma lem5261867 (x : real) (k : real) : (term461 x k) = (term461 x k).
Proof. exact (eq_refl (term461 x k)). Qed.
Lemma lem5261869 (x : real) (k : real) : (term462 x k) = (term462 x k).
Proof. exact (eq_refl (term462 x k)). Qed.
Lemma lem5261870 (x : real) (k : real) : (term463 x k) = (term464 x k).
Proof. exact (MK_COMB (@lem5261869 x k) (@lem5261861 x k)). Qed.
Lemma lem5261871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5261872 (x : real) (k : real) : (term465 x k) = (term466 x k).
Proof. exact (MK_COMB (@lem5261871) (@lem5261870 x k)). Qed.
Lemma lem5261873 (x : real) (k : real) : (term467 x k) = (term468 x k).
Proof. exact (MK_COMB (@lem5261872 x k) (@lem5261867 x k)). Qed.
Lemma lem5261874 (x : real) (k : real) : ((term224 x k) = (term225 x k)) = (term467 x k).
Proof. exact (@lem17784 (term224 x k) (term225 x k)). Qed.
Lemma lem5261875 (x : real) (k : real) : ((term224 x k) = (term225 x k)) = (term468 x k).
Proof. exact (TRANS (@lem5261874 x k) (@lem5261873 x k)). Qed.
Lemma lem5261876 (x : real) : (term226 x) = (term469 x).
Proof. exact (fun_ext (fun k : real => @lem5261875 x k)). Qed.
Lemma lem5261877 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261878 (x : real) : (term227 x) = (term470 x).
Proof. exact (MK_COMB (@lem5261877) (@lem5261876 x)). Qed.
Lemma lem5261879 : term228 = term471.
Proof. exact (fun_ext (fun x : real => @lem5261878 x)). Qed.
Lemma lem5261880 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261881 : term229 = term472.
Proof. exact (MK_COMB (@lem5261880) (@lem5261879)). Qed.
Lemma lem5261887 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term473 A P Q) = (term474 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5261888 (P : real -> Prop) (Q : real -> Prop) : (term475 P Q) = (term476 P Q).
Proof. exact (@lem5261887 real P Q). Qed.
Lemma lem5261889 (x : real) : (term477 x) = (term478 x).
Proof. exact (@lem5261888 (term479 x) (term480 x)). Qed.
Lemma lem5261890 (x : real) (k : real) : (term481 x k) = (term464 x k).
Proof. exact (eq_refl (term481 x k)). Qed.
Lemma lem5261891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5261892 (x : real) (k : real) : (term482 x k) = (term466 x k).
Proof. exact (MK_COMB (@lem5261891) (@lem5261890 x k)). Qed.
Lemma lem5261893 (x : real) (k : real) : (term483 x k) = (term461 x k).
Proof. exact (eq_refl (term483 x k)). Qed.
Lemma lem5261894 (x : real) (k : real) : (term484 x k) = (term468 x k).
Proof. exact (MK_COMB (@lem5261892 x k) (@lem5261893 x k)). Qed.
Lemma lem5261895 (x : real) : (term485 x) = (term469 x).
Proof. exact (fun_ext (fun k : real => @lem5261894 x k)). Qed.
Lemma lem5261896 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261897 (x : real) : (term477 x) = (term470 x).
Proof. exact (MK_COMB (@lem5261896) (@lem5261895 x)). Qed.
Lemma lem5261898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5261899 (x : real) : (term486 x) = (term487 x).
Proof. exact (MK_COMB (@lem5261898) (@lem5261897 x)). Qed.
Lemma lem5261900 (x : real) (k : real) : (term481 x k) = (term464 x k).
Proof. exact (eq_refl (term481 x k)). Qed.
Lemma lem5261901 (x : real) : (term488 x) = (term479 x).
Proof. exact (fun_ext (fun k : real => @lem5261900 x k)). Qed.
Lemma lem5261902 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261903 (x : real) : (term489 x) = (term490 x).
Proof. exact (MK_COMB (@lem5261902) (@lem5261901 x)). Qed.
Lemma lem5261904 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5261905 (x : real) : (term491 x) = (term492 x).
Proof. exact (MK_COMB (@lem5261904) (@lem5261903 x)). Qed.
Lemma lem5261906 (x : real) (k : real) : (term483 x k) = (term461 x k).
Proof. exact (eq_refl (term483 x k)). Qed.
Lemma lem5261907 (x : real) : (term493 x) = (term480 x).
Proof. exact (fun_ext (fun k : real => @lem5261906 x k)). Qed.
Lemma lem5261908 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5261909 (x : real) : (term494 x) = (term495 x).
Proof. exact (MK_COMB (@lem5261908) (@lem5261907 x)). Qed.
Lemma lem5261910 (x : real) : (term478 x) = (term496 x).
Proof. exact (MK_COMB (@lem5261905 x) (@lem5261909 x)). Qed.
Lemma lem5261911 (x : real) : ((term477 x) = (term478 x)) = ((term470 x) = (term496 x)).
Proof. exact (MK_COMB (@lem5261899 x) (@lem5261910 x)). Qed.
Lemma lem5261912 (x : real) : (term470 x) = (term496 x).
Proof. exact (EQ_MP (@lem5261911 x) (@lem5261889 x)). Qed.
Lemma lem5262009 : term471 = term497.
Proof. exact (fun_ext (fun x : real => @lem5261912 x)). Qed.
Lemma lem5262010 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262011 : term472 = term498.
Proof. exact (MK_COMB (@lem5262010) (@lem5262009)). Qed.
Lemma lem5262013 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term473 A P Q) = (term474 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5262014 (P : real -> Prop) (Q : real -> Prop) : (term475 P Q) = (term476 P Q).
Proof. exact (@lem5262013 real P Q). Qed.
Lemma lem5262015 : term499 = term500.
Proof. exact (@lem5262014 term501 term502). Qed.
Lemma lem5262016 (x : real) : (term503 x) = (term490 x).
Proof. exact (eq_refl (term503 x)). Qed.
Lemma lem5262017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5262018 (x : real) : (term504 x) = (term492 x).
Proof. exact (MK_COMB (@lem5262017) (@lem5262016 x)). Qed.
Lemma lem5262019 (x : real) : (term505 x) = (term495 x).
Proof. exact (eq_refl (term505 x)). Qed.
Lemma lem5262020 (x : real) : (term506 x) = (term496 x).
Proof. exact (MK_COMB (@lem5262018 x) (@lem5262019 x)). Qed.
Lemma lem5262021 : term507 = term497.
Proof. exact (fun_ext (fun x : real => @lem5262020 x)). Qed.
Lemma lem5262022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262023 : term499 = term498.
Proof. exact (MK_COMB (@lem5262022) (@lem5262021)). Qed.
Lemma lem5262024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5262025 : term508 = term509.
Proof. exact (MK_COMB (@lem5262024) (@lem5262023)). Qed.
Lemma lem5262026 (x : real) : (term503 x) = (term490 x).
Proof. exact (eq_refl (term503 x)). Qed.
Lemma lem5262027 : term510 = term501.
Proof. exact (fun_ext (fun x : real => @lem5262026 x)). Qed.
Lemma lem5262028 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262029 : term511 = term512.
Proof. exact (MK_COMB (@lem5262028) (@lem5262027)). Qed.
Lemma lem5262030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5262031 : term513 = term514.
Proof. exact (MK_COMB (@lem5262030) (@lem5262029)). Qed.
Lemma lem5262032 (x : real) : (term505 x) = (term495 x).
Proof. exact (eq_refl (term505 x)). Qed.
Lemma lem5262033 : term515 = term502.
Proof. exact (fun_ext (fun x : real => @lem5262032 x)). Qed.
Lemma lem5262034 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262035 : term516 = term517.
Proof. exact (MK_COMB (@lem5262034) (@lem5262033)). Qed.
Lemma lem5262036 : term500 = term518.
Proof. exact (MK_COMB (@lem5262031) (@lem5262035)). Qed.
Lemma lem5262037 : (term499 = term500) = (term498 = term518).
Proof. exact (MK_COMB (@lem5262025) (@lem5262036)). Qed.
Lemma lem5262038 : term498 = term518.
Proof. exact (EQ_MP (@lem5262037) (@lem5262015)). Qed.
Lemma lem5262145 : term472 = term518.
Proof. exact (TRANS (@lem5262011) (@lem5262038)). Qed.
Lemma lem5262146 : term229 = term518.
Proof. exact (TRANS (@lem5261881) (@lem5262145)). Qed.
Lemma lem5262147 (h1 : term229) : term518.
Proof. exact (EQ_MP (@lem5262146) (@lem5261169 h1)). Qed.
Lemma lem5262150 (s : real -> Prop) : (term268 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5262157 (s : real -> Prop) (x : real) (b : real) : (term519 s x b) = (term520 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5262158 (P : real -> Prop) : (term260 P) = (term261 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5262159 (s : real -> Prop) (b : real) : (term521 s b) = (term522 s b).
Proof. exact (@lem5262158 (term207 s b)). Qed.
Lemma lem5262160 (s : real -> Prop) (x : real) (b : real) : (term523 s b x) = (term206 s x b).
Proof. exact (eq_refl (term523 s b x)). Qed.
Lemma lem5262161 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5262162 (s : real -> Prop) (x : real) (b : real) : (term524 s b x) = (term519 s x b).
Proof. exact (MK_COMB (@lem5262161) (@lem5262160 s x b)). Qed.
Lemma lem5262163 (s : real -> Prop) (x : real) (b : real) : (term524 s b x) = (term520 s x b).
Proof. exact (TRANS (@lem5262162 s x b) (@lem5262157 s x b)). Qed.
Lemma lem5262164 (s : real -> Prop) (b : real) : (term525 s b) = (term526 s b).
Proof. exact (fun_ext (fun x : real => @lem5262163 s x b)). Qed.
Lemma lem5262165 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5262166 (s : real -> Prop) (b : real) : (term522 s b) = (term527 s b).
Proof. exact (MK_COMB (@lem5262165) (@lem5262164 s b)). Qed.
Lemma lem5262167 (s : real -> Prop) (b : real) : (term521 s b) = (term527 s b).
Proof. exact (TRANS (@lem5262159 s b) (@lem5262166 s b)). Qed.
Lemma lem5262168 (P : real -> Prop) : (term278 P) = (term279 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5262169 (s : real -> Prop) : (term528 s) = (term529 s).
Proof. exact (@lem5262168 (term218 s)). Qed.
Lemma lem5262170 (s : real -> Prop) (b : real) : (term530 s b) = (term208 s b).
Proof. exact (eq_refl (term530 s b)). Qed.
Lemma lem5262171 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5262172 (s : real -> Prop) (b : real) : (term531 s b) = (term521 s b).
Proof. exact (MK_COMB (@lem5262171) (@lem5262170 s b)). Qed.
Lemma lem5262173 (s : real -> Prop) (b : real) : (term531 s b) = (term527 s b).
Proof. exact (TRANS (@lem5262172 s b) (@lem5262167 s b)). Qed.
Lemma lem5262174 (s : real -> Prop) : (term532 s) = (term533 s).
Proof. exact (fun_ext (fun b : real => @lem5262173 s b)). Qed.
Lemma lem5262175 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262176 (s : real -> Prop) : (term529 s) = (term534 s).
Proof. exact (MK_COMB (@lem5262175) (@lem5262174 s)). Qed.
Lemma lem5262177 (s : real -> Prop) : (term528 s) = (term534 s).
Proof. exact (TRANS (@lem5262169 s) (@lem5262176 s)). Qed.
Lemma lem5262178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5262179 (s : real -> Prop) : (term287 s) = (term288 s).
Proof. exact (MK_COMB (@lem5262178) (@lem5262150 s)). Qed.
Lemma lem5262180 (s : real -> Prop) : (term535 s) = (term536 s).
Proof. exact (MK_COMB (@lem5262179 s) (@lem5262177 s)). Qed.
Lemma lem5262181 (s : real -> Prop) : (term537 s) = (term535 s).
Proof. exact (@lem17045 (term145 s) (term219 s)). Qed.
Lemma lem5262182 (s : real -> Prop) : (term537 s) = (term536 s).
Proof. exact (TRANS (@lem5262181 s) (@lem5262180 s)). Qed.
Lemma lem5262189 (x : real) (s : real -> Prop) : (term213 x s) = (term538 x s).
Proof. exact (@lem17265 (@IN real x s) (term154 x s)). Qed.
Lemma lem5262190 (s : real -> Prop) : (term214 s) = (term539 s).
Proof. exact (fun_ext (fun x : real => @lem5262189 x s)). Qed.
Lemma lem5262191 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262192 (s : real -> Prop) : (term215 s) = (term540 s).
Proof. exact (MK_COMB (@lem5262191) (@lem5262190 s)). Qed.
Lemma lem5262199 (s : real -> Prop) (x : real) (b : real) : (term519 s x b) = (term520 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5262200 (P : real -> Prop) : (term260 P) = (term261 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5262201 (s : real -> Prop) (b : real) : (term521 s b) = (term522 s b).
Proof. exact (@lem5262200 (term207 s b)). Qed.
Lemma lem5262202 (s : real -> Prop) (x : real) (b : real) : (term523 s b x) = (term206 s x b).
Proof. exact (eq_refl (term523 s b x)). Qed.
Lemma lem5262203 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5262204 (s : real -> Prop) (x : real) (b : real) : (term524 s b x) = (term519 s x b).
Proof. exact (MK_COMB (@lem5262203) (@lem5262202 s x b)). Qed.
Lemma lem5262205 (s : real -> Prop) (x : real) (b : real) : (term524 s b x) = (term520 s x b).
Proof. exact (TRANS (@lem5262204 s x b) (@lem5262199 s x b)). Qed.
Lemma lem5262206 (s : real -> Prop) (b : real) : (term525 s b) = (term526 s b).
Proof. exact (fun_ext (fun x : real => @lem5262205 s x b)). Qed.
Lemma lem5262207 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5262208 (s : real -> Prop) (b : real) : (term522 s b) = (term527 s b).
Proof. exact (MK_COMB (@lem5262207) (@lem5262206 s b)). Qed.
Lemma lem5262209 (s : real -> Prop) (b : real) : (term521 s b) = (term527 s b).
Proof. exact (TRANS (@lem5262201 s b) (@lem5262208 s b)). Qed.
Lemma lem5262210 (s : real -> Prop) (b : real) : (term160 s b) = (term160 s b).
Proof. exact (eq_refl (term160 s b)). Qed.
Lemma lem5262211 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5262212 (s : real -> Prop) (b : real) : (term541 s b) = (term542 s b).
Proof. exact (MK_COMB (@lem5262211) (@lem5262209 s b)). Qed.
Lemma lem5262213 (s : real -> Prop) (b : real) : (term543 s b) = (term544 s b).
Proof. exact (MK_COMB (@lem5262212 s b) (@lem5262210 s b)). Qed.
Lemma lem5262214 (s : real -> Prop) (b : real) : (term210 s b) = (term543 s b).
Proof. exact (@lem17265 (term208 s b) (term160 s b)). Qed.
Lemma lem5262215 (s : real -> Prop) (b : real) : (term210 s b) = (term544 s b).
Proof. exact (TRANS (@lem5262214 s b) (@lem5262213 s b)). Qed.
Lemma lem5262216 (s : real -> Prop) : (term211 s) = (term545 s).
Proof. exact (fun_ext (fun b : real => @lem5262215 s b)). Qed.
Lemma lem5262217 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262218 (s : real -> Prop) : (term212 s) = (term546 s).
Proof. exact (MK_COMB (@lem5262217) (@lem5262216 s)). Qed.
Lemma lem5262219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5262220 (s : real -> Prop) : (term216 s) = (term547 s).
Proof. exact (MK_COMB (@lem5262219) (@lem5262192 s)). Qed.
Lemma lem5262221 (s : real -> Prop) : (term217 s) = (term548 s).
Proof. exact (MK_COMB (@lem5262220 s) (@lem5262218 s)). Qed.
Lemma lem5262222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5262223 (s : real -> Prop) : (term549 s) = (term550 s).
Proof. exact (MK_COMB (@lem5262222) (@lem5262182 s)). Qed.
Lemma lem5262224 (s : real -> Prop) : (term551 s) = (term552 s).
Proof. exact (MK_COMB (@lem5262223 s) (@lem5262221 s)). Qed.
Lemma lem5262225 (s : real -> Prop) : (term222 s) = (term551 s).
Proof. exact (@lem17265 (term220 s) (term217 s)). Qed.
Lemma lem5262226 (s : real -> Prop) : (term222 s) = (term552 s).
Proof. exact (TRANS (@lem5262225 s) (@lem5262224 s)). Qed.
Lemma lem5262227 : term223 = term553.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5262226 s)). Qed.
Lemma lem5262228 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5262229 : term180 = term554.
Proof. exact (MK_COMB (@lem5262228) (@lem5262227)). Qed.
Lemma lem5262476 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5262477 (P : type1626) : (term311 P) = (term312 P).
Proof. exact (@lem5262476 real real P). Qed.
Lemma lem5262478 (s : real -> Prop) : (term555 s) = (term556 s).
Proof. exact (@lem5262477 (term557 s)). Qed.
Lemma lem5262479 (s : real -> Prop) (b : real) : (term558 s b) = (term526 s b).
Proof. exact (eq_refl (term558 s b)). Qed.
Lemma lem5262480 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5262481 (s : real -> Prop) (b : real) (x : real) : (term559 s b x) = (term560 s b x).
Proof. exact (MK_COMB (@lem5262479 s b) (@lem5262480 x)). Qed.
Lemma lem5262482 (s : real -> Prop) (x : real) (b : real) : (term560 s b x) = (term520 s x b).
Proof. exact (eq_refl (term560 s b x)). Qed.
Lemma lem5262483 (s : real -> Prop) (x : real) (b : real) : (term559 s b x) = (term520 s x b).
Proof. exact (TRANS (@lem5262481 s b x) (@lem5262482 s x b)). Qed.
Lemma lem5262484 (s : real -> Prop) (b : real) : (term561 s b) = (term526 s b).
Proof. exact (fun_ext (fun x : real => @lem5262483 s x b)). Qed.
Lemma lem5262485 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5262486 (s : real -> Prop) (b : real) : (term562 s b) = (term527 s b).
Proof. exact (MK_COMB (@lem5262485) (@lem5262484 s b)). Qed.
Lemma lem5262487 (s : real -> Prop) : (term563 s) = (term533 s).
Proof. exact (fun_ext (fun b : real => @lem5262486 s b)). Qed.
Lemma lem5262488 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262489 (s : real -> Prop) : (term555 s) = (term534 s).
Proof. exact (MK_COMB (@lem5262488) (@lem5262487 s)). Qed.
Lemma lem5262490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5262491 (s : real -> Prop) : (term564 s) = (term565 s).
Proof. exact (MK_COMB (@lem5262490) (@lem5262489 s)). Qed.
Lemma lem5262492 (s : real -> Prop) (b : real) : (term558 s b) = (term526 s b).
Proof. exact (eq_refl (term558 s b)). Qed.
Lemma lem5262493 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5262494 (s : real -> Prop) (x : real -> real) (b : real) : (term566 s x b) = (term567 s x b).
Proof. exact (MK_COMB (@lem5262492 s b) (@lem5262493 x b)). Qed.
Lemma lem5262495 (s : real -> Prop) (x : real -> real) (b : real) : (term567 s x b) = (term568 s x b).
Proof. exact (eq_refl (term567 s x b)). Qed.
Lemma lem5262496 (s : real -> Prop) (x : real -> real) (b : real) : (term566 s x b) = (term568 s x b).
Proof. exact (TRANS (@lem5262494 s x b) (@lem5262495 s x b)). Qed.
Lemma lem5262497 (s : real -> Prop) (x : real -> real) : (term569 s x) = (term570 s x).
Proof. exact (fun_ext (fun b : real => @lem5262496 s x b)). Qed.
Lemma lem5262498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262499 (s : real -> Prop) (x : real -> real) : (term571 s x) = (term572 s x).
Proof. exact (MK_COMB (@lem5262498) (@lem5262497 s x)). Qed.
Lemma lem5262500 (s : real -> Prop) : (term573 s) = (term574 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5262499 s x)). Qed.
Lemma lem5262501 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5262502 (s : real -> Prop) : (term556 s) = (term575 s).
Proof. exact (MK_COMB (@lem5262501) (@lem5262500 s)). Qed.
Lemma lem5262503 (s : real -> Prop) : ((term555 s) = (term556 s)) = ((term534 s) = (term575 s)).
Proof. exact (MK_COMB (@lem5262491 s) (@lem5262502 s)). Qed.
Lemma lem5262504 (s : real -> Prop) : (term534 s) = (term575 s).
Proof. exact (EQ_MP (@lem5262503 s) (@lem5262478 s)). Qed.
Lemma lem5262505 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5262506 (s : real -> Prop) : (term536 s) = (term576 s).
Proof. exact (MK_COMB (@lem5262505 s) (@lem5262504 s)). Qed.
Lemma lem5262508 {A : Type'} (P : Prop) (Q : A -> Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5262509 (P : Prop) (Q : type1028) : (term337 P Q) = (term338 P Q).
Proof. exact (@lem5262508 (real -> real) P Q). Qed.
Lemma lem5262510 (s : real -> Prop) : (term577 s) = (term578 s).
Proof. exact (@lem5262509 (s = (@EMPTY real)) (term574 s)). Qed.
Lemma lem5262511 (s : real -> Prop) (x : real -> real) : (term579 s x) = (term572 s x).
Proof. exact (eq_refl (term579 s x)). Qed.
Lemma lem5262512 (s : real -> Prop) : (term580 s) = (term574 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5262511 s x)). Qed.
Lemma lem5262513 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5262514 (s : real -> Prop) : (term581 s) = (term575 s).
Proof. exact (MK_COMB (@lem5262513) (@lem5262512 s)). Qed.
Lemma lem5262515 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5262516 (s : real -> Prop) : (term577 s) = (term576 s).
Proof. exact (MK_COMB (@lem5262515 s) (@lem5262514 s)). Qed.
Lemma lem5262517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5262518 (s : real -> Prop) : (term582 s) = (term583 s).
Proof. exact (MK_COMB (@lem5262517) (@lem5262516 s)). Qed.
Lemma lem5262519 (s : real -> Prop) (x : real -> real) : (term579 s x) = (term572 s x).
Proof. exact (eq_refl (term579 s x)). Qed.
Lemma lem5262520 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5262521 (s : real -> Prop) (x : real -> real) : (term584 s x) = (term585 s x).
Proof. exact (MK_COMB (@lem5262520 s) (@lem5262519 s x)). Qed.
Lemma lem5262522 (s : real -> Prop) : (term586 s) = (term587 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5262521 s x)). Qed.
Lemma lem5262523 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5262524 (s : real -> Prop) : (term578 s) = (term588 s).
Proof. exact (MK_COMB (@lem5262523) (@lem5262522 s)). Qed.
Lemma lem5262525 (s : real -> Prop) : ((term577 s) = (term578 s)) = ((term576 s) = (term588 s)).
Proof. exact (MK_COMB (@lem5262518 s) (@lem5262524 s)). Qed.
Lemma lem5262526 (s : real -> Prop) : (term576 s) = (term588 s).
Proof. exact (EQ_MP (@lem5262525 s) (@lem5262510 s)). Qed.
Lemma lem5262527 (s : real -> Prop) : (term536 s) = (term588 s).
Proof. exact (TRANS (@lem5262506 s) (@lem5262526 s)). Qed.
Lemma lem5262528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5262529 (s : real -> Prop) : (term550 s) = (term589 s).
Proof. exact (MK_COMB (@lem5262528) (@lem5262527 s)). Qed.
Lemma lem5262531 {A : Type'} (P : A -> Prop) (Q : Prop) : (term352 A P Q) = (term353 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5262532 (P : real -> Prop) (Q : Prop) : (term354 P Q) = (term355 P Q).
Proof. exact (@lem5262531 real P Q). Qed.
Lemma lem5262533 (s : real -> Prop) (b : real) : (term590 s b) = (term591 s b).
Proof. exact (@lem5262532 (term526 s b) (term160 s b)). Qed.
Lemma lem5262534 (s : real -> Prop) (x : real) (b : real) : (term560 s b x) = (term520 s x b).
Proof. exact (eq_refl (term560 s b x)). Qed.
Lemma lem5262535 (s : real -> Prop) (b : real) : (term592 s b) = (term526 s b).
Proof. exact (fun_ext (fun x : real => @lem5262534 s x b)). Qed.
Lemma lem5262536 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5262537 (s : real -> Prop) (b : real) : (term593 s b) = (term527 s b).
Proof. exact (MK_COMB (@lem5262536) (@lem5262535 s b)). Qed.
Lemma lem5262538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5262539 (s : real -> Prop) (b : real) : (term594 s b) = (term542 s b).
Proof. exact (MK_COMB (@lem5262538) (@lem5262537 s b)). Qed.
Lemma lem5262540 (s : real -> Prop) (b : real) : (term160 s b) = (term160 s b).
Proof. exact (eq_refl (term160 s b)). Qed.
Lemma lem5262541 (s : real -> Prop) (b : real) : (term590 s b) = (term544 s b).
Proof. exact (MK_COMB (@lem5262539 s b) (@lem5262540 s b)). Qed.
Lemma lem5262542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5262543 (s : real -> Prop) (b : real) : (term595 s b) = (term596 s b).
Proof. exact (MK_COMB (@lem5262542) (@lem5262541 s b)). Qed.
Lemma lem5262544 (s : real -> Prop) (x : real) (b : real) : (term560 s b x) = (term520 s x b).
Proof. exact (eq_refl (term560 s b x)). Qed.
Lemma lem5262545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5262546 (s : real -> Prop) (x : real) (b : real) : (term597 s b x) = (term598 s x b).
Proof. exact (MK_COMB (@lem5262545) (@lem5262544 s x b)). Qed.
Lemma lem5262547 (s : real -> Prop) (b : real) : (term160 s b) = (term160 s b).
Proof. exact (eq_refl (term160 s b)). Qed.
Lemma lem5262548 (x : real) (s : real -> Prop) (b : real) : (term599 x s b) = (term600 x s b).
Proof. exact (MK_COMB (@lem5262546 s x b) (@lem5262547 s b)). Qed.
Lemma lem5262549 (s : real -> Prop) (b : real) : (term601 s b) = (term602 s b).
Proof. exact (fun_ext (fun x : real => @lem5262548 x s b)). Qed.
Lemma lem5262550 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5262551 (s : real -> Prop) (b : real) : (term591 s b) = (term603 s b).
Proof. exact (MK_COMB (@lem5262550) (@lem5262549 s b)). Qed.
Lemma lem5262552 (s : real -> Prop) (b : real) : ((term590 s b) = (term591 s b)) = ((term544 s b) = (term603 s b)).
Proof. exact (MK_COMB (@lem5262543 s b) (@lem5262551 s b)). Qed.
Lemma lem5262553 (s : real -> Prop) (b : real) : (term544 s b) = (term603 s b).
Proof. exact (EQ_MP (@lem5262552 s b) (@lem5262533 s b)). Qed.
Lemma lem5262554 (s : real -> Prop) : (term545 s) = (term604 s).
Proof. exact (fun_ext (fun b : real => @lem5262553 s b)). Qed.
Lemma lem5262555 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262556 (s : real -> Prop) : (term546 s) = (term605 s).
Proof. exact (MK_COMB (@lem5262555) (@lem5262554 s)). Qed.
Lemma lem5262558 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5262559 (P : type1626) : (term311 P) = (term312 P).
Proof. exact (@lem5262558 real real P). Qed.
Lemma lem5262560 (s : real -> Prop) : (term606 s) = (term607 s).
Proof. exact (@lem5262559 (term608 s)). Qed.
Lemma lem5262561 (s : real -> Prop) (b : real) : (term609 s b) = (term602 s b).
Proof. exact (eq_refl (term609 s b)). Qed.
Lemma lem5262562 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5262563 (s : real -> Prop) (b : real) (x : real) : (term610 s b x) = (term611 s b x).
Proof. exact (MK_COMB (@lem5262561 s b) (@lem5262562 x)). Qed.
Lemma lem5262564 (x : real) (s : real -> Prop) (b : real) : (term611 s b x) = (term600 x s b).
Proof. exact (eq_refl (term611 s b x)). Qed.
Lemma lem5262565 (x : real) (s : real -> Prop) (b : real) : (term610 s b x) = (term600 x s b).
Proof. exact (TRANS (@lem5262563 s b x) (@lem5262564 x s b)). Qed.
Lemma lem5262566 (s : real -> Prop) (b : real) : (term612 s b) = (term602 s b).
Proof. exact (fun_ext (fun x : real => @lem5262565 x s b)). Qed.
Lemma lem5262567 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5262568 (s : real -> Prop) (b : real) : (term613 s b) = (term603 s b).
Proof. exact (MK_COMB (@lem5262567) (@lem5262566 s b)). Qed.
Lemma lem5262569 (s : real -> Prop) : (term614 s) = (term604 s).
Proof. exact (fun_ext (fun b : real => @lem5262568 s b)). Qed.
Lemma lem5262570 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262571 (s : real -> Prop) : (term606 s) = (term605 s).
Proof. exact (MK_COMB (@lem5262570) (@lem5262569 s)). Qed.
Lemma lem5262572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5262573 (s : real -> Prop) : (term615 s) = (term616 s).
Proof. exact (MK_COMB (@lem5262572) (@lem5262571 s)). Qed.
Lemma lem5262574 (s : real -> Prop) (b : real) : (term609 s b) = (term602 s b).
Proof. exact (eq_refl (term609 s b)). Qed.
Lemma lem5262575 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5262576 (s : real -> Prop) (x : real -> real) (b : real) : (term617 s x b) = (term618 s x b).
Proof. exact (MK_COMB (@lem5262574 s b) (@lem5262575 x b)). Qed.
Lemma lem5262577 (x : real -> real) (s : real -> Prop) (b : real) : (term618 s x b) = (term619 x s b).
Proof. exact (eq_refl (term618 s x b)). Qed.
Lemma lem5262578 (x : real -> real) (s : real -> Prop) (b : real) : (term617 s x b) = (term619 x s b).
Proof. exact (TRANS (@lem5262576 s x b) (@lem5262577 x s b)). Qed.
Lemma lem5262579 (x : real -> real) (s : real -> Prop) : (term620 s x) = (term621 x s).
Proof. exact (fun_ext (fun b : real => @lem5262578 x s b)). Qed.
Lemma lem5262580 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262581 (x : real -> real) (s : real -> Prop) : (term622 s x) = (term623 x s).
Proof. exact (MK_COMB (@lem5262580) (@lem5262579 x s)). Qed.
Lemma lem5262582 (s : real -> Prop) : (term624 s) = (term625 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5262581 x s)). Qed.
Lemma lem5262583 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5262584 (s : real -> Prop) : (term607 s) = (term626 s).
Proof. exact (MK_COMB (@lem5262583) (@lem5262582 s)). Qed.
Lemma lem5262585 (s : real -> Prop) : ((term606 s) = (term607 s)) = ((term605 s) = (term626 s)).
Proof. exact (MK_COMB (@lem5262573 s) (@lem5262584 s)). Qed.
Lemma lem5262586 (s : real -> Prop) : (term605 s) = (term626 s).
Proof. exact (EQ_MP (@lem5262585 s) (@lem5262560 s)). Qed.
Lemma lem5262587 (s : real -> Prop) : (term546 s) = (term626 s).
Proof. exact (TRANS (@lem5262556 s) (@lem5262586 s)). Qed.
Lemma lem5262588 (s : real -> Prop) : (term547 s) = (term547 s).
Proof. exact (eq_refl (term547 s)). Qed.
Lemma lem5262589 (s : real -> Prop) : (term548 s) = (term627 s).
Proof. exact (MK_COMB (@lem5262588 s) (@lem5262587 s)). Qed.
Lemma lem5262591 {A : Type'} (P : Prop) (Q : A -> Prop) : (term394 A P Q) = (term395 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5262592 (P : Prop) (Q : type1028) : (term396 P Q) = (term397 P Q).
Proof. exact (@lem5262591 (real -> real) P Q). Qed.
Lemma lem5262593 (s : real -> Prop) : (term628 s) = (term629 s).
Proof. exact (@lem5262592 (term540 s) (term625 s)). Qed.
Lemma lem5262594 (x : real -> real) (s : real -> Prop) : (term630 s x) = (term623 x s).
Proof. exact (eq_refl (term630 s x)). Qed.
Lemma lem5262595 (s : real -> Prop) : (term631 s) = (term625 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5262594 x s)). Qed.
Lemma lem5262596 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5262597 (s : real -> Prop) : (term632 s) = (term626 s).
Proof. exact (MK_COMB (@lem5262596) (@lem5262595 s)). Qed.
Lemma lem5262598 (s : real -> Prop) : (term547 s) = (term547 s).
Proof. exact (eq_refl (term547 s)). Qed.
Lemma lem5262599 (s : real -> Prop) : (term628 s) = (term627 s).
Proof. exact (MK_COMB (@lem5262598 s) (@lem5262597 s)). Qed.
Lemma lem5262600 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5262601 (s : real -> Prop) : (term633 s) = (term634 s).
Proof. exact (MK_COMB (@lem5262600) (@lem5262599 s)). Qed.
Lemma lem5262602 (x : real -> real) (s : real -> Prop) : (term630 s x) = (term623 x s).
Proof. exact (eq_refl (term630 s x)). Qed.
Lemma lem5262603 (s : real -> Prop) : (term547 s) = (term547 s).
Proof. exact (eq_refl (term547 s)). Qed.
Lemma lem5262604 (x : real -> real) (s : real -> Prop) : (term635 s x) = (term636 x s).
Proof. exact (MK_COMB (@lem5262603 s) (@lem5262602 x s)). Qed.
Lemma lem5262605 (s : real -> Prop) : (term637 s) = (term638 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5262604 x s)). Qed.
Lemma lem5262606 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5262607 (s : real -> Prop) : (term629 s) = (term639 s).
Proof. exact (MK_COMB (@lem5262606) (@lem5262605 s)). Qed.
Lemma lem5262608 (s : real -> Prop) : ((term628 s) = (term629 s)) = ((term627 s) = (term639 s)).
Proof. exact (MK_COMB (@lem5262601 s) (@lem5262607 s)). Qed.
Lemma lem5262609 (s : real -> Prop) : (term627 s) = (term639 s).
Proof. exact (EQ_MP (@lem5262608 s) (@lem5262593 s)). Qed.
Lemma lem5262610 (s : real -> Prop) : (term548 s) = (term639 s).
Proof. exact (TRANS (@lem5262589 s) (@lem5262609 s)). Qed.
Lemma lem5262611 (s : real -> Prop) : (term552 s) = (term640 s).
Proof. exact (MK_COMB (@lem5262529 s) (@lem5262610 s)). Qed.
Lemma lem5262613 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5262614 (P : type1028) (Q : type1028) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem5262613 (real -> real) P Q). Qed.
Lemma lem5262615 (s : real -> Prop) : (term641 s) = (term642 s).
Proof. exact (@lem5262614 (term587 s) (term638 s)). Qed.
Lemma lem5262616 (s : real -> Prop) (x : real -> real) : (term643 s x) = (term585 s x).
Proof. exact (eq_refl (term643 s x)). Qed.
Lemma lem5262617 (s : real -> Prop) : (term644 s) = (term587 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5262616 s x)). Qed.
Lemma lem5262618 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5262619 (s : real -> Prop) : (term645 s) = (term588 s).
Proof. exact (MK_COMB (@lem5262618) (@lem5262617 s)). Qed.
Lemma lem5262620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5262621 (s : real -> Prop) : (term646 s) = (term589 s).
Proof. exact (MK_COMB (@lem5262620) (@lem5262619 s)). Qed.
Lemma lem5262622 (x : real -> real) (s : real -> Prop) : (term647 s x) = (term636 x s).
Proof. exact (eq_refl (term647 s x)). Qed.
Lemma lem5262623 (s : real -> Prop) : (term648 s) = (term638 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5262622 x s)). Qed.
Lemma lem5262624 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5262625 (s : real -> Prop) : (term649 s) = (term639 s).
Proof. exact (MK_COMB (@lem5262624) (@lem5262623 s)). Qed.
Lemma lem5262626 (s : real -> Prop) : (term641 s) = (term640 s).
Proof. exact (MK_COMB (@lem5262621 s) (@lem5262625 s)). Qed.
Lemma lem5262627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5262628 (s : real -> Prop) : (term650 s) = (term651 s).
Proof. exact (MK_COMB (@lem5262627) (@lem5262626 s)). Qed.
Lemma lem5262629 (s : real -> Prop) (x : real -> real) : (term643 s x) = (term585 s x).
Proof. exact (eq_refl (term643 s x)). Qed.
Lemma lem5262630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5262631 (s : real -> Prop) (x : real -> real) : (term652 s x) = (term653 s x).
Proof. exact (MK_COMB (@lem5262630) (@lem5262629 s x)). Qed.
Lemma lem5262632 (x : real -> real) (s : real -> Prop) : (term647 s x) = (term636 x s).
Proof. exact (eq_refl (term647 s x)). Qed.
Lemma lem5262633 (x : real -> real) (s : real -> Prop) : (term654 s x) = (term655 x s).
Proof. exact (MK_COMB (@lem5262631 s x) (@lem5262632 x s)). Qed.
Lemma lem5262634 (s : real -> Prop) : (term656 s) = (term657 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5262633 x s)). Qed.
Lemma lem5262635 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5262636 (s : real -> Prop) : (term642 s) = (term658 s).
Proof. exact (MK_COMB (@lem5262635) (@lem5262634 s)). Qed.
Lemma lem5262637 (s : real -> Prop) : ((term641 s) = (term642 s)) = ((term640 s) = (term658 s)).
Proof. exact (MK_COMB (@lem5262628 s) (@lem5262636 s)). Qed.
Lemma lem5262638 (s : real -> Prop) : (term640 s) = (term658 s).
Proof. exact (EQ_MP (@lem5262637 s) (@lem5262615 s)). Qed.
Lemma lem5262639 (s : real -> Prop) : (term552 s) = (term658 s).
Proof. exact (TRANS (@lem5262611 s) (@lem5262638 s)). Qed.
Lemma lem5262640 : term553 = term659.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5262639 s)). Qed.
Lemma lem5262641 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5262642 : term554 = term660.
Proof. exact (MK_COMB (@lem5262641) (@lem5262640)). Qed.
Lemma lem5262644 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5262645 (P : type1017) : (term435 P) = (term436 P).
Proof. exact (@lem5262644 (real -> Prop) (real -> real) P). Qed.
Lemma lem5262646 : term661 = term662.
Proof. exact (@lem5262645 term663). Qed.
Lemma lem5262647 (s : real -> Prop) : (term664 s) = (term657 s).
Proof. exact (eq_refl (term664 s)). Qed.
Lemma lem5262648 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5262649 (s : real -> Prop) (x : real -> real) : (term665 s x) = (term666 s x).
Proof. exact (MK_COMB (@lem5262647 s) (@lem5262648 x)). Qed.
Lemma lem5262650 (x : real -> real) (s : real -> Prop) : (term666 s x) = (term655 x s).
Proof. exact (eq_refl (term666 s x)). Qed.
Lemma lem5262651 (x : real -> real) (s : real -> Prop) : (term665 s x) = (term655 x s).
Proof. exact (TRANS (@lem5262649 s x) (@lem5262650 x s)). Qed.
Lemma lem5262652 (s : real -> Prop) : (term667 s) = (term657 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5262651 x s)). Qed.
Lemma lem5262653 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5262654 (s : real -> Prop) : (term668 s) = (term658 s).
Proof. exact (MK_COMB (@lem5262653) (@lem5262652 s)). Qed.
Lemma lem5262655 : term669 = term659.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5262654 s)). Qed.
Lemma lem5262656 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5262657 : term661 = term660.
Proof. exact (MK_COMB (@lem5262656) (@lem5262655)). Qed.
Lemma lem5262658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5262659 : term670 = term671.
Proof. exact (MK_COMB (@lem5262658) (@lem5262657)). Qed.
Lemma lem5262660 (s : real -> Prop) : (term664 s) = (term657 s).
Proof. exact (eq_refl (term664 s)). Qed.
Lemma lem5262661 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5262662 (x : type1021) (s : real -> Prop) : (term672 x s) = (term673 x s).
Proof. exact (MK_COMB (@lem5262660 s) (@lem5262661 x s)). Qed.
Lemma lem5262663 (x : type1021) (s : real -> Prop) : (term673 x s) = (term674 x s).
Proof. exact (eq_refl (term673 x s)). Qed.
Lemma lem5262664 (x : type1021) (s : real -> Prop) : (term672 x s) = (term674 x s).
Proof. exact (TRANS (@lem5262662 x s) (@lem5262663 x s)). Qed.
Lemma lem5262665 (x : type1021) : (term675 x) = (term676 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5262664 x s)). Qed.
Lemma lem5262666 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5262667 (x : type1021) : (term677 x) = (term678 x).
Proof. exact (MK_COMB (@lem5262666) (@lem5262665 x)). Qed.
Lemma lem5262668 : term679 = term680.
Proof. exact (fun_ext (fun x : type1021 => @lem5262667 x)). Qed.
Lemma lem5262669 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5262670 : term662 = term681.
Proof. exact (MK_COMB (@lem5262669) (@lem5262668)). Qed.
Lemma lem5262671 : (term661 = term662) = (term660 = term681).
Proof. exact (MK_COMB (@lem5262659) (@lem5262670)). Qed.
Lemma lem5262672 : term660 = term681.
Proof. exact (EQ_MP (@lem5262671) (@lem5262646)). Qed.
Lemma lem5262674 : term554 = term681.
Proof. exact (TRANS (@lem5262642) (@lem5262672)). Qed.
Lemma lem5262675 : term180 = term681.
Proof. exact (TRANS (@lem5262229) (@lem5262674)). Qed.
Lemma lem5262676 (h1 : term180) : term681.
Proof. exact (EQ_MP (@lem5262675) (@lem5261170 h1)). Qed.
Lemma lem5262677 (x : type1021) (h1 : term678 x) : term678 x.
Proof. exact (h1). Qed.
Lemma lem5262678 (x' : type1021) (h1 : term454 x') : term454 x'.
Proof. exact (h1). Qed.
Lemma lem5262687 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5262704 (s : real -> Prop) (x : real) (B : real) : (term251 s x B) = (term251 s x B).
Proof. exact (eq_refl (term251 s x B)). Qed.
Lemma lem5262705 (s : real -> Prop) (B : real) : (term252 s B) = (term252 s B).
Proof. exact (fun_ext (fun x : real => @lem5262704 s x B)). Qed.
Lemma lem5262706 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262707 (s : real -> Prop) (B : real) : (term253 s B) = (term253 s B).
Proof. exact (MK_COMB (@lem5262706) (@lem5262705 s B)). Qed.
Lemma lem5262708 (s : real -> Prop) (B : real) (h1 : term146 s B) : term253 s B.
Proof. exact (EQ_MP (@lem5262707 s B) (@lem5261239 s B h1)). Qed.
Lemma lem5262718 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (sup s) = (inf s).
Proof. exact (h1). Qed.
Lemma lem5262745 (x : real) (k : real) : (term461 x k) = (term461 x k).
Proof. exact (eq_refl (term461 x k)). Qed.
Lemma lem5262746 (x : real) : (term480 x) = (term480 x).
Proof. exact (fun_ext (fun k : real => @lem5262745 x k)). Qed.
Lemma lem5262747 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262748 (x : real) : (term495 x) = (term495 x).
Proof. exact (MK_COMB (@lem5262747) (@lem5262746 x)). Qed.
Lemma lem5262749 : term502 = term502.
Proof. exact (fun_ext (fun x : real => @lem5262748 x)). Qed.
Lemma lem5262750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262751 : term517 = term517.
Proof. exact (MK_COMB (@lem5262750) (@lem5262749)). Qed.
Lemma lem5262780 (x : real) (k : real) : (term464 x k) = (term464 x k).
Proof. exact (eq_refl (term464 x k)). Qed.
Lemma lem5262781 (x : real) : (term479 x) = (term479 x).
Proof. exact (fun_ext (fun k : real => @lem5262780 x k)). Qed.
Lemma lem5262782 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262783 (x : real) : (term490 x) = (term490 x).
Proof. exact (MK_COMB (@lem5262782) (@lem5262781 x)). Qed.
Lemma lem5262784 : term501 = term501.
Proof. exact (fun_ext (fun x : real => @lem5262783 x)). Qed.
Lemma lem5262785 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262786 : term512 = term512.
Proof. exact (MK_COMB (@lem5262785) (@lem5262784)). Qed.
Lemma lem5262787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5262788 : term514 = term514.
Proof. exact (MK_COMB (@lem5262787) (@lem5262786)). Qed.
Lemma lem5262789 : term518 = term518.
Proof. exact (MK_COMB (@lem5262788) (@lem5262751)). Qed.
Lemma lem5262790 (h1 : term229) : term518.
Proof. exact (EQ_MP (@lem5262789) (@lem5262147 h1)). Qed.
Lemma lem5262823 (x : type1021) (s : real -> Prop) (b : real) : (term682 x s b) = (term682 x s b).
Proof. exact (eq_refl (term682 x s b)). Qed.
Lemma lem5262824 (x : type1021) (s : real -> Prop) : (term683 x s) = (term683 x s).
Proof. exact (fun_ext (fun b : real => @lem5262823 x s b)). Qed.
Lemma lem5262825 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262826 (x : type1021) (s : real -> Prop) : (term684 x s) = (term684 x s).
Proof. exact (MK_COMB (@lem5262825) (@lem5262824 x s)). Qed.
Lemma lem5262843 (x : real) (s : real -> Prop) : (term538 x s) = (term538 x s).
Proof. exact (eq_refl (term538 x s)). Qed.
Lemma lem5262844 (s : real -> Prop) : (term539 s) = (term539 s).
Proof. exact (fun_ext (fun x : real => @lem5262843 x s)). Qed.
Lemma lem5262845 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262846 (s : real -> Prop) : (term540 s) = (term540 s).
Proof. exact (MK_COMB (@lem5262845) (@lem5262844 s)). Qed.
Lemma lem5262847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5262848 (s : real -> Prop) : (term547 s) = (term547 s).
Proof. exact (MK_COMB (@lem5262847) (@lem5262846 s)). Qed.
Lemma lem5262849 (x : type1021) (s : real -> Prop) : (term685 x s) = (term685 x s).
Proof. exact (MK_COMB (@lem5262848 s) (@lem5262826 x s)). Qed.
Lemma lem5262872 (x : type1021) (s : real -> Prop) (b : real) : (term686 x s b) = (term686 x s b).
Proof. exact (eq_refl (term686 x s b)). Qed.
Lemma lem5262873 (x : type1021) (s : real -> Prop) : (term687 x s) = (term687 x s).
Proof. exact (fun_ext (fun b : real => @lem5262872 x s b)). Qed.
Lemma lem5262874 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262875 (x : type1021) (s : real -> Prop) : (term688 x s) = (term688 x s).
Proof. exact (MK_COMB (@lem5262874) (@lem5262873 x s)). Qed.
Lemma lem5262882 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5262883 (x : type1021) (s : real -> Prop) : (term689 x s) = (term689 x s).
Proof. exact (MK_COMB (@lem5262882 s) (@lem5262875 x s)). Qed.
Lemma lem5262884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5262885 (x : type1021) (s : real -> Prop) : (term690 x s) = (term690 x s).
Proof. exact (MK_COMB (@lem5262884) (@lem5262883 x s)). Qed.
Lemma lem5262886 (x : type1021) (s : real -> Prop) : (term674 x s) = (term674 x s).
Proof. exact (MK_COMB (@lem5262885 x s) (@lem5262849 x s)). Qed.
Lemma lem5262887 (x : type1021) : (term676 x) = (term676 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5262886 x s)). Qed.
Lemma lem5262888 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5262889 (x : type1021) : (term678 x) = (term678 x).
Proof. exact (MK_COMB (@lem5262888) (@lem5262887 x)). Qed.
Lemma lem5262890 (x : type1021) (h1 : term678 x) : term678 x.
Proof. exact (EQ_MP (@lem5262889 x) (@lem5262677 x h1)). Qed.
Lemma lem5262923 (x' : type1021) (b : real) (s : real -> Prop) : (term691 x' b s) = (term691 x' b s).
Proof. exact (eq_refl (term691 x' b s)). Qed.
Lemma lem5262924 (x' : type1021) (s : real -> Prop) : (term692 x' s) = (term692 x' s).
Proof. exact (fun_ext (fun b : real => @lem5262923 x' b s)). Qed.
Lemma lem5262925 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262926 (x' : type1021) (s : real -> Prop) : (term693 x' s) = (term693 x' s).
Proof. exact (MK_COMB (@lem5262925) (@lem5262924 x' s)). Qed.
Lemma lem5262943 (s : real -> Prop) (x : real) : (term292 s x) = (term292 s x).
Proof. exact (eq_refl (term292 s x)). Qed.
Lemma lem5262944 (s : real -> Prop) : (term293 s) = (term293 s).
Proof. exact (fun_ext (fun x : real => @lem5262943 s x)). Qed.
Lemma lem5262945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262946 (s : real -> Prop) : (term294 s) = (term294 s).
Proof. exact (MK_COMB (@lem5262945) (@lem5262944 s)). Qed.
Lemma lem5262947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5262948 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (MK_COMB (@lem5262947) (@lem5262946 s)). Qed.
Lemma lem5262949 (x' : type1021) (s : real -> Prop) : (term694 x' s) = (term694 x' s).
Proof. exact (MK_COMB (@lem5262948 s) (@lem5262926 x' s)). Qed.
Lemma lem5262972 (x' : type1021) (s : real -> Prop) (b : real) : (term695 x' s b) = (term695 x' s b).
Proof. exact (eq_refl (term695 x' s b)). Qed.
Lemma lem5262973 (x' : type1021) (s : real -> Prop) : (term696 x' s) = (term696 x' s).
Proof. exact (fun_ext (fun b : real => @lem5262972 x' s b)). Qed.
Lemma lem5262974 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5262975 (x' : type1021) (s : real -> Prop) : (term697 x' s) = (term697 x' s).
Proof. exact (MK_COMB (@lem5262974) (@lem5262973 x' s)). Qed.
Lemma lem5262982 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5262983 (x' : type1021) (s : real -> Prop) : (term698 x' s) = (term698 x' s).
Proof. exact (MK_COMB (@lem5262982 s) (@lem5262975 x' s)). Qed.
Lemma lem5262984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5262985 (x' : type1021) (s : real -> Prop) : (term699 x' s) = (term699 x' s).
Proof. exact (MK_COMB (@lem5262984) (@lem5262983 x' s)). Qed.
Lemma lem5262986 (x' : type1021) (s : real -> Prop) : (term450 x' s) = (term450 x' s).
Proof. exact (MK_COMB (@lem5262985 x' s) (@lem5262949 x' s)). Qed.
Lemma lem5262987 (x' : type1021) : (term452 x') = (term452 x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5262986 x' s)). Qed.
Lemma lem5262988 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5262989 (x' : type1021) : (term454 x') = (term454 x').
Proof. exact (MK_COMB (@lem5262988) (@lem5262987 x')). Qed.
Lemma lem5262990 (x' : type1021) (h1 : term454 x') : term454 x'.
Proof. exact (EQ_MP (@lem5262989 x') (@lem5262678 x' h1)). Qed.
Lemma lem5263020 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : term258 s x''.
Proof. exact (h1). Qed.
Lemma lem5263021 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : term255 s x''.
Proof. exact (proj2 (@lem5263020 s x'' h1)). Qed.
Lemma lem5263023 (h1 : term229) : term517.
Proof. exact (proj2 (@lem5262790 h1)). Qed.
Lemma lem5263030 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5263038 (s : real -> Prop) (x : real) (B : real) : (term251 s x B) = (term251 s x B).
Proof. exact (eq_refl (term251 s x B)). Qed.
Lemma lem5263039 (s : real -> Prop) (B : real) : (term252 s B) = (term252 s B).
Proof. exact (fun_ext (fun x : real => @lem5263038 s x B)). Qed.
Lemma lem5263040 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263042 (s : real -> Prop) (B : real) : (term253 s B) = (term253 s B).
Proof. exact (MK_COMB (@lem5263040) (@lem5263039 s B)). Qed.
Lemma lem5263043 (s : real -> Prop) (B : real) (h1 : term146 s B) : term253 s B.
Proof. exact (EQ_MP (@lem5263042 s B) (@lem5262708 s B h1)). Qed.
Lemma lem5263047 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (sup s) = (inf s).
Proof. exact (h1). Qed.
Lemma lem5263049 {A : Type'} (P : Prop) (Q : A -> Prop) : (term700 A P Q) = (term701 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5263050 (P : Prop) (Q : real -> Prop) : (term702 P Q) = (term703 P Q).
Proof. exact (@lem5263049 real P Q). Qed.
Lemma lem5263051 (x : type1021) (s : real -> Prop) : (term704 x s) = (term705 x s).
Proof. exact (@lem5263050 (s = (@EMPTY real)) (term687 x s)). Qed.
Lemma lem5263052 (x : type1021) (s : real -> Prop) (b : real) : (term706 x s b) = (term686 x s b).
Proof. exact (eq_refl (term706 x s b)). Qed.
Lemma lem5263053 (x : type1021) (s : real -> Prop) : (term707 x s) = (term687 x s).
Proof. exact (fun_ext (fun b : real => @lem5263052 x s b)). Qed.
Lemma lem5263054 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263055 (x : type1021) (s : real -> Prop) : (term708 x s) = (term688 x s).
Proof. exact (MK_COMB (@lem5263054) (@lem5263053 x s)). Qed.
Lemma lem5263056 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5263057 (x : type1021) (s : real -> Prop) : (term704 x s) = (term689 x s).
Proof. exact (MK_COMB (@lem5263056 s) (@lem5263055 x s)). Qed.
Lemma lem5263058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5263059 (x : type1021) (s : real -> Prop) : (term709 x s) = (term710 x s).
Proof. exact (MK_COMB (@lem5263058) (@lem5263057 x s)). Qed.
Lemma lem5263060 (x : type1021) (s : real -> Prop) (b : real) : (term706 x s b) = (term686 x s b).
Proof. exact (eq_refl (term706 x s b)). Qed.
Lemma lem5263061 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5263062 (x : type1021) (s : real -> Prop) (b : real) : (term711 x s b) = (term712 x s b).
Proof. exact (MK_COMB (@lem5263061 s) (@lem5263060 x s b)). Qed.
Lemma lem5263063 (x : type1021) (s : real -> Prop) : (term713 x s) = (term714 x s).
Proof. exact (fun_ext (fun b : real => @lem5263062 x s b)). Qed.
Lemma lem5263064 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263065 (x : type1021) (s : real -> Prop) : (term705 x s) = (term715 x s).
Proof. exact (MK_COMB (@lem5263064) (@lem5263063 x s)). Qed.
Lemma lem5263066 (x : type1021) (s : real -> Prop) : ((term704 x s) = (term705 x s)) = ((term689 x s) = (term715 x s)).
Proof. exact (MK_COMB (@lem5263059 x s) (@lem5263065 x s)). Qed.
Lemma lem5263067 (x : type1021) (s : real -> Prop) : (term689 x s) = (term715 x s).
Proof. exact (EQ_MP (@lem5263066 x s) (@lem5263051 x s)). Qed.
Lemma lem5263068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5263069 (x : type1021) (s : real -> Prop) : (term690 x s) = (term716 x s).
Proof. exact (MK_COMB (@lem5263068) (@lem5263067 x s)). Qed.
Lemma lem5263071 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term474 A P Q) = (term473 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5263072 (P : real -> Prop) (Q : real -> Prop) : (term476 P Q) = (term475 P Q).
Proof. exact (@lem5263071 real P Q). Qed.
Lemma lem5263073 (x : type1021) (s : real -> Prop) : (term717 x s) = (term718 x s).
Proof. exact (@lem5263072 (term539 s) (term683 x s)). Qed.
Lemma lem5263074 (b : real) (s : real -> Prop) : (term719 s b) = (term538 b s).
Proof. exact (eq_refl (term719 s b)). Qed.
Lemma lem5263075 (s : real -> Prop) : (term720 s) = (term539 s).
Proof. exact (fun_ext (fun b : real => @lem5263074 b s)). Qed.
Lemma lem5263076 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263077 (s : real -> Prop) : (term721 s) = (term540 s).
Proof. exact (MK_COMB (@lem5263076) (@lem5263075 s)). Qed.
Lemma lem5263078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5263079 (s : real -> Prop) : (term722 s) = (term547 s).
Proof. exact (MK_COMB (@lem5263078) (@lem5263077 s)). Qed.
Lemma lem5263080 (x : type1021) (s : real -> Prop) (b : real) : (term723 x s b) = (term682 x s b).
Proof. exact (eq_refl (term723 x s b)). Qed.
Lemma lem5263081 (x : type1021) (s : real -> Prop) : (term724 x s) = (term683 x s).
Proof. exact (fun_ext (fun b : real => @lem5263080 x s b)). Qed.
Lemma lem5263082 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263083 (x : type1021) (s : real -> Prop) : (term725 x s) = (term684 x s).
Proof. exact (MK_COMB (@lem5263082) (@lem5263081 x s)). Qed.
Lemma lem5263084 (x : type1021) (s : real -> Prop) : (term717 x s) = (term685 x s).
Proof. exact (MK_COMB (@lem5263079 s) (@lem5263083 x s)). Qed.
Lemma lem5263085 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5263086 (x : type1021) (s : real -> Prop) : (term726 x s) = (term727 x s).
Proof. exact (MK_COMB (@lem5263085) (@lem5263084 x s)). Qed.
Lemma lem5263087 (b : real) (s : real -> Prop) : (term719 s b) = (term538 b s).
Proof. exact (eq_refl (term719 s b)). Qed.
Lemma lem5263088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5263089 (b : real) (s : real -> Prop) : (term728 s b) = (term729 b s).
Proof. exact (MK_COMB (@lem5263088) (@lem5263087 b s)). Qed.
Lemma lem5263090 (x : type1021) (s : real -> Prop) (b : real) : (term723 x s b) = (term682 x s b).
Proof. exact (eq_refl (term723 x s b)). Qed.
Lemma lem5263091 (x : type1021) (s : real -> Prop) (b : real) : (term730 x s b) = (term731 x s b).
Proof. exact (MK_COMB (@lem5263089 b s) (@lem5263090 x s b)). Qed.
Lemma lem5263092 (x : type1021) (s : real -> Prop) : (term732 x s) = (term733 x s).
Proof. exact (fun_ext (fun b : real => @lem5263091 x s b)). Qed.
Lemma lem5263093 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263094 (x : type1021) (s : real -> Prop) : (term718 x s) = (term734 x s).
Proof. exact (MK_COMB (@lem5263093) (@lem5263092 x s)). Qed.
Lemma lem5263095 (x : type1021) (s : real -> Prop) : ((term717 x s) = (term718 x s)) = ((term685 x s) = (term734 x s)).
Proof. exact (MK_COMB (@lem5263086 x s) (@lem5263094 x s)). Qed.
Lemma lem5263096 (x : type1021) (s : real -> Prop) : (term685 x s) = (term734 x s).
Proof. exact (EQ_MP (@lem5263095 x s) (@lem5263073 x s)). Qed.
Lemma lem5263099 (x : type1021) (s : real -> Prop) : (term735 x s) = (term735 x s).
Proof. exact (eq_refl (term735 x s)). Qed.
Lemma lem5263100 (x : type1021) (s : real -> Prop) : (term735 x s) = ((term685 x s) = (term734 x s)).
Proof. exact (eq_refl (term735 x s)). Qed.
Lemma lem5263101 (x : type1021) (s : real -> Prop) : (term736 x s) = (term736 x s).
Proof. exact (eq_refl (term736 x s)). Qed.
Lemma lem5263102 (x : type1021) (s : real -> Prop) : ((term735 x s) = (term735 x s)) = ((term735 x s) = ((term685 x s) = (term734 x s))).
Proof. exact (MK_COMB (@lem5263101 x s) (@lem5263100 x s)). Qed.
Lemma lem5263103 (x : type1021) (s : real -> Prop) : (term735 x s) = ((term685 x s) = (term734 x s)).
Proof. exact (eq_refl (term735 x s)). Qed.
Lemma lem5263104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5263105 (x : type1021) (s : real -> Prop) : (term736 x s) = (term737 x s).
Proof. exact (MK_COMB (@lem5263104) (@lem5263103 x s)). Qed.
Lemma lem5263106 (x : type1021) (s : real -> Prop) : ((term685 x s) = (term734 x s)) = ((term685 x s) = (term734 x s)).
Proof. exact (eq_refl ((term685 x s) = (term734 x s))). Qed.
Lemma lem5263107 (x : type1021) (s : real -> Prop) : ((term735 x s) = ((term685 x s) = (term734 x s))) = (((term685 x s) = (term734 x s)) = ((term685 x s) = (term734 x s))).
Proof. exact (MK_COMB (@lem5263105 x s) (@lem5263106 x s)). Qed.
Lemma lem5263108 (x : type1021) (s : real -> Prop) : ((term735 x s) = (term735 x s)) = (((term685 x s) = (term734 x s)) = ((term685 x s) = (term734 x s))).
Proof. exact (TRANS (@lem5263102 x s) (@lem5263107 x s)). Qed.
Lemma lem5263109 (x : type1021) (s : real -> Prop) : ((term685 x s) = (term734 x s)) = ((term685 x s) = (term734 x s)).
Proof. exact (EQ_MP (@lem5263108 x s) (@lem5263099 x s)). Qed.
Lemma lem5263110 (x : type1021) (s : real -> Prop) : (term685 x s) = (term734 x s).
Proof. exact (EQ_MP (@lem5263109 x s) (@lem5263096 x s)). Qed.
Lemma lem5263111 (x : type1021) (s : real -> Prop) : (term674 x s) = (term738 x s).
Proof. exact (MK_COMB (@lem5263069 x s) (@lem5263110 x s)). Qed.
Lemma lem5263113 {A : Type'} (P : A -> Prop) (Q : Prop) : (term739 A P Q) = (term740 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5263114 (P : real -> Prop) (Q : Prop) : (term741 P Q) = (term742 P Q).
Proof. exact (@lem5263113 real P Q). Qed.
Lemma lem5263115 (x : type1021) (s : real -> Prop) : (term743 x s) = (term744 x s).
Proof. exact (@lem5263114 (term714 x s) (term734 x s)). Qed.
Lemma lem5263116 (x : type1021) (s : real -> Prop) (b : real) : (term745 x s b) = (term712 x s b).
Proof. exact (eq_refl (term745 x s b)). Qed.
Lemma lem5263117 (x : type1021) (s : real -> Prop) : (term746 x s) = (term714 x s).
Proof. exact (fun_ext (fun b : real => @lem5263116 x s b)). Qed.
Lemma lem5263118 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263119 (x : type1021) (s : real -> Prop) : (term747 x s) = (term715 x s).
Proof. exact (MK_COMB (@lem5263118) (@lem5263117 x s)). Qed.
Lemma lem5263120 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5263121 (x : type1021) (s : real -> Prop) : (term748 x s) = (term716 x s).
Proof. exact (MK_COMB (@lem5263120) (@lem5263119 x s)). Qed.
Lemma lem5263122 (x : type1021) (s : real -> Prop) : (term734 x s) = (term734 x s).
Proof. exact (eq_refl (term734 x s)). Qed.
Lemma lem5263123 (x : type1021) (s : real -> Prop) : (term743 x s) = (term738 x s).
Proof. exact (MK_COMB (@lem5263121 x s) (@lem5263122 x s)). Qed.
Lemma lem5263124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5263125 (x : type1021) (s : real -> Prop) : (term749 x s) = (term750 x s).
Proof. exact (MK_COMB (@lem5263124) (@lem5263123 x s)). Qed.
Lemma lem5263126 (x : type1021) (s : real -> Prop) (b : real) : (term745 x s b) = (term712 x s b).
Proof. exact (eq_refl (term745 x s b)). Qed.
Lemma lem5263127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5263128 (x : type1021) (s : real -> Prop) (b : real) : (term751 x s b) = (term752 x s b).
Proof. exact (MK_COMB (@lem5263127) (@lem5263126 x s b)). Qed.
Lemma lem5263129 (x : type1021) (s : real -> Prop) : (term734 x s) = (term734 x s).
Proof. exact (eq_refl (term734 x s)). Qed.
Lemma lem5263130 (b : real) (x : type1021) (s : real -> Prop) : (term753 b x s) = (term754 b x s).
Proof. exact (MK_COMB (@lem5263128 x s b) (@lem5263129 x s)). Qed.
Lemma lem5263131 (x : type1021) (s : real -> Prop) : (term755 x s) = (term756 x s).
Proof. exact (fun_ext (fun b : real => @lem5263130 b x s)). Qed.
Lemma lem5263132 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263133 (x : type1021) (s : real -> Prop) : (term744 x s) = (term757 x s).
Proof. exact (MK_COMB (@lem5263132) (@lem5263131 x s)). Qed.
Lemma lem5263134 (x : type1021) (s : real -> Prop) : ((term743 x s) = (term744 x s)) = ((term738 x s) = (term757 x s)).
Proof. exact (MK_COMB (@lem5263125 x s) (@lem5263133 x s)). Qed.
Lemma lem5263135 (x : type1021) (s : real -> Prop) : (term738 x s) = (term757 x s).
Proof. exact (EQ_MP (@lem5263134 x s) (@lem5263115 x s)). Qed.
Lemma lem5263137 {A : Type'} (P : Prop) (Q : A -> Prop) : (term700 A P Q) = (term701 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5263138 (P : Prop) (Q : real -> Prop) : (term702 P Q) = (term703 P Q).
Proof. exact (@lem5263137 real P Q). Qed.
Lemma lem5263139 (b : real) (x : type1021) (s : real -> Prop) : (term758 b x s) = (term759 b x s).
Proof. exact (@lem5263138 (term712 x s b) (term733 x s)). Qed.
Lemma lem5263140 (x : type1021) (s : real -> Prop) (b : real) : (term760 x s b) = (term731 x s b).
Proof. exact (eq_refl (term760 x s b)). Qed.
Lemma lem5263141 (x : type1021) (s : real -> Prop) : (term761 x s) = (term733 x s).
Proof. exact (fun_ext (fun b : real => @lem5263140 x s b)). Qed.
Lemma lem5263142 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263143 (x : type1021) (s : real -> Prop) : (term762 x s) = (term734 x s).
Proof. exact (MK_COMB (@lem5263142) (@lem5263141 x s)). Qed.
Lemma lem5263144 (x : type1021) (s : real -> Prop) (b : real) : (term752 x s b) = (term752 x s b).
Proof. exact (eq_refl (term752 x s b)). Qed.
Lemma lem5263145 (b : real) (x : type1021) (s : real -> Prop) : (term758 b x s) = (term754 b x s).
Proof. exact (MK_COMB (@lem5263144 x s b) (@lem5263143 x s)). Qed.
Lemma lem5263146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5263147 (b : real) (x : type1021) (s : real -> Prop) : (term763 b x s) = (term764 b x s).
Proof. exact (MK_COMB (@lem5263146) (@lem5263145 b x s)). Qed.
Lemma lem5263148 (x : type1021) (s : real -> Prop) (b' : real) : (term760 x s b') = (term731 x s b').
Proof. exact (eq_refl (term760 x s b')). Qed.
Lemma lem5263149 (x : type1021) (s : real -> Prop) (b : real) : (term752 x s b) = (term752 x s b).
Proof. exact (eq_refl (term752 x s b)). Qed.
Lemma lem5263150 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term765 b x s b') = (term766 b x s b').
Proof. exact (MK_COMB (@lem5263149 x s b) (@lem5263148 x s b')). Qed.
Lemma lem5263151 (b : real) (x : type1021) (s : real -> Prop) : (term767 b x s) = (term768 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5263150 b x s b')). Qed.
Lemma lem5263152 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263153 (b : real) (x : type1021) (s : real -> Prop) : (term759 b x s) = (term769 b x s).
Proof. exact (MK_COMB (@lem5263152) (@lem5263151 b x s)). Qed.
Lemma lem5263154 (b : real) (x : type1021) (s : real -> Prop) : ((term758 b x s) = (term759 b x s)) = ((term754 b x s) = (term769 b x s)).
Proof. exact (MK_COMB (@lem5263147 b x s) (@lem5263153 b x s)). Qed.
Lemma lem5263155 (b : real) (x : type1021) (s : real -> Prop) : (term754 b x s) = (term769 b x s).
Proof. exact (EQ_MP (@lem5263154 b x s) (@lem5263139 b x s)). Qed.
Lemma lem5263156 (x : type1021) (s : real -> Prop) : (term756 x s) = (term770 x s).
Proof. exact (fun_ext (fun b : real => @lem5263155 b x s)). Qed.
Lemma lem5263157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263158 (x : type1021) (s : real -> Prop) : (term757 x s) = (term771 x s).
Proof. exact (MK_COMB (@lem5263157) (@lem5263156 x s)). Qed.
Lemma lem5263159 (x : type1021) (s : real -> Prop) : (term738 x s) = (term771 x s).
Proof. exact (TRANS (@lem5263135 x s) (@lem5263158 x s)). Qed.
Lemma lem5263160 (x : type1021) (s : real -> Prop) : (term674 x s) = (term771 x s).
Proof. exact (TRANS (@lem5263111 x s) (@lem5263159 x s)). Qed.
Lemma lem5263161 (x : type1021) : (term676 x) = (term772 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5263160 x s)). Qed.
Lemma lem5263162 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5263163 (x : type1021) : (term678 x) = (term773 x).
Proof. exact (MK_COMB (@lem5263162) (@lem5263161 x)). Qed.
Lemma lem5263180 (x : type1021) (s : real -> Prop) (b' : real) : (term682 x s b') = (term774 x s b').
Proof. exact (@lem19699 (term775 x b' s) (term776 x s b') (term160 s b')). Qed.
Lemma lem5263189 (b' : real) (s : real -> Prop) : (term729 b' s) = (term729 b' s).
Proof. exact (eq_refl (term729 b' s)). Qed.
Lemma lem5263190 (x : type1021) (s : real -> Prop) (b' : real) : (term731 x s b') = (term777 x s b').
Proof. exact (MK_COMB (@lem5263189 b' s) (@lem5263180 x s b')). Qed.
Lemma lem5263207 (x : type1021) (s : real -> Prop) (b : real) : (term712 x s b) = (term778 x s b).
Proof. exact (@lem19490 (term775 x b s) (s = (@EMPTY real)) (term776 x s b)). Qed.
Lemma lem5263208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5263209 (x : type1021) (s : real -> Prop) (b : real) : (term752 x s b) = (term779 x s b).
Proof. exact (MK_COMB (@lem5263208) (@lem5263207 x s b)). Qed.
Lemma lem5263210 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term766 b x s b') = (term780 b x s b').
Proof. exact (MK_COMB (@lem5263209 x s b) (@lem5263190 x s b')). Qed.
Lemma lem5263211 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term780 b x s b') = (term781 b x s b').
Proof. exact (@lem19490 (term538 b' s) (term778 x s b) (term774 x s b')). Qed.
Lemma lem5263212 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term782 b x s b') = (term783 b x s b').
Proof. exact (@lem19490 (term784 x s b') (term778 x s b) (term785 x s b')). Qed.
Lemma lem5263219 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term786 b x s b') = (term787 b x s b').
Proof. exact (@lem19699 (term788 x b s) (term789 x s b) (term785 x s b')). Qed.
Lemma lem5263226 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term790 b x s b') = (term791 b x s b').
Proof. exact (@lem19699 (term788 x b s) (term789 x s b) (term784 x s b')). Qed.
Lemma lem5263227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5263228 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term792 b x s b') = (term793 b x s b').
Proof. exact (MK_COMB (@lem5263227) (@lem5263226 b x s b')). Qed.
Lemma lem5263229 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term783 b x s b') = (term794 b x s b').
Proof. exact (MK_COMB (@lem5263228 b x s b') (@lem5263219 b x s b')). Qed.
Lemma lem5263230 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term782 b x s b') = (term794 b x s b').
Proof. exact (TRANS (@lem5263212 b x s b') (@lem5263229 b x s b')). Qed.
Lemma lem5263237 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term795 x b b' s) = (term796 x b b' s).
Proof. exact (@lem19699 (term788 x b s) (term789 x s b) (term538 b' s)). Qed.
Lemma lem5263238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5263239 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term797 x b b' s) = (term798 x b b' s).
Proof. exact (MK_COMB (@lem5263238) (@lem5263237 x b b' s)). Qed.
Lemma lem5263240 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term781 b x s b') = (term799 b x s b').
Proof. exact (MK_COMB (@lem5263239 x b b' s) (@lem5263230 b x s b')). Qed.
Lemma lem5263241 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term780 b x s b') = (term799 b x s b').
Proof. exact (TRANS (@lem5263211 b x s b') (@lem5263240 b x s b')). Qed.
Lemma lem5263242 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term766 b x s b') = (term799 b x s b').
Proof. exact (TRANS (@lem5263210 b x s b') (@lem5263241 b x s b')). Qed.
Lemma lem5263243 (b : real) (x : type1021) (s : real -> Prop) : (term768 b x s) = (term800 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5263242 b x s b')). Qed.
Lemma lem5263244 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263245 (b : real) (x : type1021) (s : real -> Prop) : (term769 b x s) = (term801 b x s).
Proof. exact (MK_COMB (@lem5263244) (@lem5263243 b x s)). Qed.
Lemma lem5263246 (x : type1021) (s : real -> Prop) : (term770 x s) = (term802 x s).
Proof. exact (fun_ext (fun b : real => @lem5263245 b x s)). Qed.
Lemma lem5263247 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263248 (x : type1021) (s : real -> Prop) : (term771 x s) = (term803 x s).
Proof. exact (MK_COMB (@lem5263247) (@lem5263246 x s)). Qed.
Lemma lem5263249 (x : type1021) : (term772 x) = (term804 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5263248 x s)). Qed.
Lemma lem5263250 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5263251 (x : type1021) : (term773 x) = (term805 x).
Proof. exact (MK_COMB (@lem5263250) (@lem5263249 x)). Qed.
Lemma lem5263252 (x : type1021) : (term678 x) = (term805 x).
Proof. exact (TRANS (@lem5263163 x) (@lem5263251 x)). Qed.
Lemma lem5263253 (x : type1021) (h1 : term678 x) : term805 x.
Proof. exact (EQ_MP (@lem5263252 x) (@lem5262890 x h1)). Qed.
Lemma lem5263503 (x : real) (k : real) : (term461 x k) = (term806 x k).
Proof. exact (@lem19490 (term460 k x) (term807 x k) (real_le x k)). Qed.
Lemma lem5263504 (x : real) : (term480 x) = (term808 x).
Proof. exact (fun_ext (fun k : real => @lem5263503 x k)). Qed.
Lemma lem5263505 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263506 (x : real) : (term495 x) = (term809 x).
Proof. exact (MK_COMB (@lem5263505) (@lem5263504 x)). Qed.
Lemma lem5263507 : term502 = term810.
Proof. exact (fun_ext (fun x : real => @lem5263506 x)). Qed.
Lemma lem5263508 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263510 : term517 = term811.
Proof. exact (MK_COMB (@lem5263508) (@lem5263507)). Qed.
Lemma lem5263511 (h1 : term229) : term811.
Proof. exact (EQ_MP (@lem5263510) (@lem5263023 h1)). Qed.
Lemma lem5263515 (x'' : real) (s : real -> Prop) (h1 : term812 x'' s) : term812 x'' s.
Proof. exact (h1). Qed.
Lemma lem5263519 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5263527 (s : real -> Prop) (x : real) (B : real) : (term251 s x B) = (term251 s x B).
Proof. exact (eq_refl (term251 s x B)). Qed.
Lemma lem5263528 (s : real -> Prop) (B : real) : (term252 s B) = (term252 s B).
Proof. exact (fun_ext (fun x : real => @lem5263527 s x B)). Qed.
Lemma lem5263529 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263531 (s : real -> Prop) (B : real) : (term253 s B) = (term253 s B).
Proof. exact (MK_COMB (@lem5263529) (@lem5263528 s B)). Qed.
Lemma lem5263532 (s : real -> Prop) (B : real) (h1 : term146 s B) : term253 s B.
Proof. exact (EQ_MP (@lem5263531 s B) (@lem5262708 s B h1)). Qed.
Lemma lem5263744 {A : Type'} (P : Prop) (Q : A -> Prop) : (term700 A P Q) = (term701 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5263745 (P : Prop) (Q : real -> Prop) : (term702 P Q) = (term703 P Q).
Proof. exact (@lem5263744 real P Q). Qed.
Lemma lem5263746 (x' : type1021) (s : real -> Prop) : (term813 x' s) = (term814 x' s).
Proof. exact (@lem5263745 (s = (@EMPTY real)) (term696 x' s)). Qed.
Lemma lem5263747 (x' : type1021) (s : real -> Prop) (b : real) : (term815 x' s b) = (term695 x' s b).
Proof. exact (eq_refl (term815 x' s b)). Qed.
Lemma lem5263748 (x' : type1021) (s : real -> Prop) : (term816 x' s) = (term696 x' s).
Proof. exact (fun_ext (fun b : real => @lem5263747 x' s b)). Qed.
Lemma lem5263749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263750 (x' : type1021) (s : real -> Prop) : (term817 x' s) = (term697 x' s).
Proof. exact (MK_COMB (@lem5263749) (@lem5263748 x' s)). Qed.
Lemma lem5263751 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5263752 (x' : type1021) (s : real -> Prop) : (term813 x' s) = (term698 x' s).
Proof. exact (MK_COMB (@lem5263751 s) (@lem5263750 x' s)). Qed.
Lemma lem5263753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5263754 (x' : type1021) (s : real -> Prop) : (term818 x' s) = (term819 x' s).
Proof. exact (MK_COMB (@lem5263753) (@lem5263752 x' s)). Qed.
Lemma lem5263755 (x' : type1021) (s : real -> Prop) (b : real) : (term815 x' s b) = (term695 x' s b).
Proof. exact (eq_refl (term815 x' s b)). Qed.
Lemma lem5263756 (s : real -> Prop) : (term288 s) = (term288 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5263757 (x' : type1021) (s : real -> Prop) (b : real) : (term820 x' s b) = (term821 x' s b).
Proof. exact (MK_COMB (@lem5263756 s) (@lem5263755 x' s b)). Qed.
Lemma lem5263758 (x' : type1021) (s : real -> Prop) : (term822 x' s) = (term823 x' s).
Proof. exact (fun_ext (fun b : real => @lem5263757 x' s b)). Qed.
Lemma lem5263759 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263760 (x' : type1021) (s : real -> Prop) : (term814 x' s) = (term824 x' s).
Proof. exact (MK_COMB (@lem5263759) (@lem5263758 x' s)). Qed.
Lemma lem5263761 (x' : type1021) (s : real -> Prop) : ((term813 x' s) = (term814 x' s)) = ((term698 x' s) = (term824 x' s)).
Proof. exact (MK_COMB (@lem5263754 x' s) (@lem5263760 x' s)). Qed.
Lemma lem5263762 (x' : type1021) (s : real -> Prop) : (term698 x' s) = (term824 x' s).
Proof. exact (EQ_MP (@lem5263761 x' s) (@lem5263746 x' s)). Qed.
Lemma lem5263763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5263764 (x' : type1021) (s : real -> Prop) : (term699 x' s) = (term825 x' s).
Proof. exact (MK_COMB (@lem5263763) (@lem5263762 x' s)). Qed.
Lemma lem5263766 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term474 A P Q) = (term473 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5263767 (P : real -> Prop) (Q : real -> Prop) : (term476 P Q) = (term475 P Q).
Proof. exact (@lem5263766 real P Q). Qed.
Lemma lem5263768 (x' : type1021) (s : real -> Prop) : (term826 x' s) = (term827 x' s).
Proof. exact (@lem5263767 (term293 s) (term692 x' s)). Qed.
Lemma lem5263769 (s : real -> Prop) (b : real) : (term828 s b) = (term292 s b).
Proof. exact (eq_refl (term828 s b)). Qed.
Lemma lem5263770 (s : real -> Prop) : (term829 s) = (term293 s).
Proof. exact (fun_ext (fun b : real => @lem5263769 s b)). Qed.
Lemma lem5263771 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263772 (s : real -> Prop) : (term830 s) = (term294 s).
Proof. exact (MK_COMB (@lem5263771) (@lem5263770 s)). Qed.
Lemma lem5263773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5263774 (s : real -> Prop) : (term831 s) = (term301 s).
Proof. exact (MK_COMB (@lem5263773) (@lem5263772 s)). Qed.
Lemma lem5263775 (x' : type1021) (b : real) (s : real -> Prop) : (term832 x' s b) = (term691 x' b s).
Proof. exact (eq_refl (term832 x' s b)). Qed.
Lemma lem5263776 (x' : type1021) (s : real -> Prop) : (term833 x' s) = (term692 x' s).
Proof. exact (fun_ext (fun b : real => @lem5263775 x' b s)). Qed.
Lemma lem5263777 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263778 (x' : type1021) (s : real -> Prop) : (term834 x' s) = (term693 x' s).
Proof. exact (MK_COMB (@lem5263777) (@lem5263776 x' s)). Qed.
Lemma lem5263779 (x' : type1021) (s : real -> Prop) : (term826 x' s) = (term694 x' s).
Proof. exact (MK_COMB (@lem5263774 s) (@lem5263778 x' s)). Qed.
Lemma lem5263780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5263781 (x' : type1021) (s : real -> Prop) : (term835 x' s) = (term836 x' s).
Proof. exact (MK_COMB (@lem5263780) (@lem5263779 x' s)). Qed.
Lemma lem5263782 (s : real -> Prop) (b : real) : (term828 s b) = (term292 s b).
Proof. exact (eq_refl (term828 s b)). Qed.
Lemma lem5263783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5263784 (s : real -> Prop) (b : real) : (term837 s b) = (term838 s b).
Proof. exact (MK_COMB (@lem5263783) (@lem5263782 s b)). Qed.
Lemma lem5263785 (x' : type1021) (b : real) (s : real -> Prop) : (term832 x' s b) = (term691 x' b s).
Proof. exact (eq_refl (term832 x' s b)). Qed.
Lemma lem5263786 (x' : type1021) (b : real) (s : real -> Prop) : (term839 x' s b) = (term840 x' b s).
Proof. exact (MK_COMB (@lem5263784 s b) (@lem5263785 x' b s)). Qed.
Lemma lem5263787 (x' : type1021) (s : real -> Prop) : (term841 x' s) = (term842 x' s).
Proof. exact (fun_ext (fun b : real => @lem5263786 x' b s)). Qed.
Lemma lem5263788 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263789 (x' : type1021) (s : real -> Prop) : (term827 x' s) = (term843 x' s).
Proof. exact (MK_COMB (@lem5263788) (@lem5263787 x' s)). Qed.
Lemma lem5263790 (x' : type1021) (s : real -> Prop) : ((term826 x' s) = (term827 x' s)) = ((term694 x' s) = (term843 x' s)).
Proof. exact (MK_COMB (@lem5263781 x' s) (@lem5263789 x' s)). Qed.
Lemma lem5263791 (x' : type1021) (s : real -> Prop) : (term694 x' s) = (term843 x' s).
Proof. exact (EQ_MP (@lem5263790 x' s) (@lem5263768 x' s)). Qed.
Lemma lem5263794 (x' : type1021) (s : real -> Prop) : (term844 x' s) = (term844 x' s).
Proof. exact (eq_refl (term844 x' s)). Qed.
Lemma lem5263795 (x' : type1021) (s : real -> Prop) : (term844 x' s) = ((term694 x' s) = (term843 x' s)).
Proof. exact (eq_refl (term844 x' s)). Qed.
Lemma lem5263796 (x' : type1021) (s : real -> Prop) : (term845 x' s) = (term845 x' s).
Proof. exact (eq_refl (term845 x' s)). Qed.
Lemma lem5263797 (x' : type1021) (s : real -> Prop) : ((term844 x' s) = (term844 x' s)) = ((term844 x' s) = ((term694 x' s) = (term843 x' s))).
Proof. exact (MK_COMB (@lem5263796 x' s) (@lem5263795 x' s)). Qed.
Lemma lem5263798 (x' : type1021) (s : real -> Prop) : (term844 x' s) = ((term694 x' s) = (term843 x' s)).
Proof. exact (eq_refl (term844 x' s)). Qed.
Lemma lem5263799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5263800 (x' : type1021) (s : real -> Prop) : (term845 x' s) = (term846 x' s).
Proof. exact (MK_COMB (@lem5263799) (@lem5263798 x' s)). Qed.
Lemma lem5263801 (x' : type1021) (s : real -> Prop) : ((term694 x' s) = (term843 x' s)) = ((term694 x' s) = (term843 x' s)).
Proof. exact (eq_refl ((term694 x' s) = (term843 x' s))). Qed.
Lemma lem5263802 (x' : type1021) (s : real -> Prop) : ((term844 x' s) = ((term694 x' s) = (term843 x' s))) = (((term694 x' s) = (term843 x' s)) = ((term694 x' s) = (term843 x' s))).
Proof. exact (MK_COMB (@lem5263800 x' s) (@lem5263801 x' s)). Qed.
Lemma lem5263803 (x' : type1021) (s : real -> Prop) : ((term844 x' s) = (term844 x' s)) = (((term694 x' s) = (term843 x' s)) = ((term694 x' s) = (term843 x' s))).
Proof. exact (TRANS (@lem5263797 x' s) (@lem5263802 x' s)). Qed.
Lemma lem5263804 (x' : type1021) (s : real -> Prop) : ((term694 x' s) = (term843 x' s)) = ((term694 x' s) = (term843 x' s)).
Proof. exact (EQ_MP (@lem5263803 x' s) (@lem5263794 x' s)). Qed.
Lemma lem5263805 (x' : type1021) (s : real -> Prop) : (term694 x' s) = (term843 x' s).
Proof. exact (EQ_MP (@lem5263804 x' s) (@lem5263791 x' s)). Qed.
Lemma lem5263806 (x' : type1021) (s : real -> Prop) : (term450 x' s) = (term847 x' s).
Proof. exact (MK_COMB (@lem5263764 x' s) (@lem5263805 x' s)). Qed.
Lemma lem5263808 {A : Type'} (P : A -> Prop) (Q : Prop) : (term739 A P Q) = (term740 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5263809 (P : real -> Prop) (Q : Prop) : (term741 P Q) = (term742 P Q).
Proof. exact (@lem5263808 real P Q). Qed.
Lemma lem5263810 (x' : type1021) (s : real -> Prop) : (term848 x' s) = (term849 x' s).
Proof. exact (@lem5263809 (term823 x' s) (term843 x' s)). Qed.
Lemma lem5263811 (x' : type1021) (s : real -> Prop) (b : real) : (term850 x' s b) = (term821 x' s b).
Proof. exact (eq_refl (term850 x' s b)). Qed.
Lemma lem5263812 (x' : type1021) (s : real -> Prop) : (term851 x' s) = (term823 x' s).
Proof. exact (fun_ext (fun b : real => @lem5263811 x' s b)). Qed.
Lemma lem5263813 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263814 (x' : type1021) (s : real -> Prop) : (term852 x' s) = (term824 x' s).
Proof. exact (MK_COMB (@lem5263813) (@lem5263812 x' s)). Qed.
Lemma lem5263815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5263816 (x' : type1021) (s : real -> Prop) : (term853 x' s) = (term825 x' s).
Proof. exact (MK_COMB (@lem5263815) (@lem5263814 x' s)). Qed.
Lemma lem5263817 (x' : type1021) (s : real -> Prop) : (term843 x' s) = (term843 x' s).
Proof. exact (eq_refl (term843 x' s)). Qed.
Lemma lem5263818 (x' : type1021) (s : real -> Prop) : (term848 x' s) = (term847 x' s).
Proof. exact (MK_COMB (@lem5263816 x' s) (@lem5263817 x' s)). Qed.
Lemma lem5263819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5263820 (x' : type1021) (s : real -> Prop) : (term854 x' s) = (term855 x' s).
Proof. exact (MK_COMB (@lem5263819) (@lem5263818 x' s)). Qed.
Lemma lem5263821 (x' : type1021) (s : real -> Prop) (b : real) : (term850 x' s b) = (term821 x' s b).
Proof. exact (eq_refl (term850 x' s b)). Qed.
Lemma lem5263822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5263823 (x' : type1021) (s : real -> Prop) (b : real) : (term856 x' s b) = (term857 x' s b).
Proof. exact (MK_COMB (@lem5263822) (@lem5263821 x' s b)). Qed.
Lemma lem5263824 (x' : type1021) (s : real -> Prop) : (term843 x' s) = (term843 x' s).
Proof. exact (eq_refl (term843 x' s)). Qed.
Lemma lem5263825 (b : real) (x' : type1021) (s : real -> Prop) : (term858 b x' s) = (term859 b x' s).
Proof. exact (MK_COMB (@lem5263823 x' s b) (@lem5263824 x' s)). Qed.
Lemma lem5263826 (x' : type1021) (s : real -> Prop) : (term860 x' s) = (term861 x' s).
Proof. exact (fun_ext (fun b : real => @lem5263825 b x' s)). Qed.
Lemma lem5263827 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263828 (x' : type1021) (s : real -> Prop) : (term849 x' s) = (term862 x' s).
Proof. exact (MK_COMB (@lem5263827) (@lem5263826 x' s)). Qed.
Lemma lem5263829 (x' : type1021) (s : real -> Prop) : ((term848 x' s) = (term849 x' s)) = ((term847 x' s) = (term862 x' s)).
Proof. exact (MK_COMB (@lem5263820 x' s) (@lem5263828 x' s)). Qed.
Lemma lem5263830 (x' : type1021) (s : real -> Prop) : (term847 x' s) = (term862 x' s).
Proof. exact (EQ_MP (@lem5263829 x' s) (@lem5263810 x' s)). Qed.
Lemma lem5263832 {A : Type'} (P : Prop) (Q : A -> Prop) : (term700 A P Q) = (term701 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5263833 (P : Prop) (Q : real -> Prop) : (term702 P Q) = (term703 P Q).
Proof. exact (@lem5263832 real P Q). Qed.
Lemma lem5263834 (b : real) (x' : type1021) (s : real -> Prop) : (term863 b x' s) = (term864 b x' s).
Proof. exact (@lem5263833 (term821 x' s b) (term842 x' s)). Qed.
Lemma lem5263835 (x' : type1021) (b : real) (s : real -> Prop) : (term865 x' s b) = (term840 x' b s).
Proof. exact (eq_refl (term865 x' s b)). Qed.
Lemma lem5263836 (x' : type1021) (s : real -> Prop) : (term866 x' s) = (term842 x' s).
Proof. exact (fun_ext (fun b : real => @lem5263835 x' b s)). Qed.
Lemma lem5263837 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263838 (x' : type1021) (s : real -> Prop) : (term867 x' s) = (term843 x' s).
Proof. exact (MK_COMB (@lem5263837) (@lem5263836 x' s)). Qed.
Lemma lem5263839 (x' : type1021) (s : real -> Prop) (b : real) : (term857 x' s b) = (term857 x' s b).
Proof. exact (eq_refl (term857 x' s b)). Qed.
Lemma lem5263840 (b : real) (x' : type1021) (s : real -> Prop) : (term863 b x' s) = (term859 b x' s).
Proof. exact (MK_COMB (@lem5263839 x' s b) (@lem5263838 x' s)). Qed.
Lemma lem5263841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5263842 (b : real) (x' : type1021) (s : real -> Prop) : (term868 b x' s) = (term869 b x' s).
Proof. exact (MK_COMB (@lem5263841) (@lem5263840 b x' s)). Qed.
Lemma lem5263843 (x' : type1021) (b' : real) (s : real -> Prop) : (term865 x' s b') = (term840 x' b' s).
Proof. exact (eq_refl (term865 x' s b')). Qed.
Lemma lem5263844 (x' : type1021) (s : real -> Prop) (b : real) : (term857 x' s b) = (term857 x' s b).
Proof. exact (eq_refl (term857 x' s b)). Qed.
Lemma lem5263845 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term870 b x' s b') = (term871 b x' b' s).
Proof. exact (MK_COMB (@lem5263844 x' s b) (@lem5263843 x' b' s)). Qed.
Lemma lem5263846 (b : real) (x' : type1021) (s : real -> Prop) : (term872 b x' s) = (term873 b x' s).
Proof. exact (fun_ext (fun b' : real => @lem5263845 b x' b' s)). Qed.
Lemma lem5263847 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263848 (b : real) (x' : type1021) (s : real -> Prop) : (term864 b x' s) = (term874 b x' s).
Proof. exact (MK_COMB (@lem5263847) (@lem5263846 b x' s)). Qed.
Lemma lem5263849 (b : real) (x' : type1021) (s : real -> Prop) : ((term863 b x' s) = (term864 b x' s)) = ((term859 b x' s) = (term874 b x' s)).
Proof. exact (MK_COMB (@lem5263842 b x' s) (@lem5263848 b x' s)). Qed.
Lemma lem5263850 (b : real) (x' : type1021) (s : real -> Prop) : (term859 b x' s) = (term874 b x' s).
Proof. exact (EQ_MP (@lem5263849 b x' s) (@lem5263834 b x' s)). Qed.
Lemma lem5263851 (x' : type1021) (s : real -> Prop) : (term861 x' s) = (term875 x' s).
Proof. exact (fun_ext (fun b : real => @lem5263850 b x' s)). Qed.
Lemma lem5263852 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263853 (x' : type1021) (s : real -> Prop) : (term862 x' s) = (term876 x' s).
Proof. exact (MK_COMB (@lem5263852) (@lem5263851 x' s)). Qed.
Lemma lem5263854 (x' : type1021) (s : real -> Prop) : (term847 x' s) = (term876 x' s).
Proof. exact (TRANS (@lem5263830 x' s) (@lem5263853 x' s)). Qed.
Lemma lem5263855 (x' : type1021) (s : real -> Prop) : (term450 x' s) = (term876 x' s).
Proof. exact (TRANS (@lem5263806 x' s) (@lem5263854 x' s)). Qed.
Lemma lem5263856 (x' : type1021) : (term452 x') = (term877 x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5263855 x' s)). Qed.
Lemma lem5263857 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5263858 (x' : type1021) : (term454 x') = (term878 x').
Proof. exact (MK_COMB (@lem5263857) (@lem5263856 x')). Qed.
Lemma lem5263875 (x' : type1021) (b' : real) (s : real -> Prop) : (term691 x' b' s) = (term879 x' b' s).
Proof. exact (@lem19699 (term775 x' b' s) (term880 x' s b') (term155 b' s)). Qed.
Lemma lem5263884 (s : real -> Prop) (b' : real) : (term838 s b') = (term838 s b').
Proof. exact (eq_refl (term838 s b')). Qed.
Lemma lem5263885 (x' : type1021) (b' : real) (s : real -> Prop) : (term840 x' b' s) = (term881 x' b' s).
Proof. exact (MK_COMB (@lem5263884 s b') (@lem5263875 x' b' s)). Qed.
Lemma lem5263902 (x' : type1021) (s : real -> Prop) (b : real) : (term821 x' s b) = (term882 x' s b).
Proof. exact (@lem19490 (term775 x' b s) (s = (@EMPTY real)) (term880 x' s b)). Qed.
Lemma lem5263903 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5263904 (x' : type1021) (s : real -> Prop) (b : real) : (term857 x' s b) = (term883 x' s b).
Proof. exact (MK_COMB (@lem5263903) (@lem5263902 x' s b)). Qed.
Lemma lem5263905 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term871 b x' b' s) = (term884 b x' b' s).
Proof. exact (MK_COMB (@lem5263904 x' s b) (@lem5263885 x' b' s)). Qed.
Lemma lem5263906 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term884 b x' b' s) = (term885 b x' b' s).
Proof. exact (@lem19490 (term292 s b') (term882 x' s b) (term879 x' b' s)). Qed.
Lemma lem5263907 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term886 b x' b' s) = (term887 b x' b' s).
Proof. exact (@lem19490 (term888 x' b' s) (term882 x' s b) (term889 x' b' s)). Qed.
Lemma lem5263914 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term890 b x' b' s) = (term891 b x' b' s).
Proof. exact (@lem19699 (term788 x' b s) (term892 x' s b) (term889 x' b' s)). Qed.
Lemma lem5263921 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term893 b x' b' s) = (term894 b x' b' s).
Proof. exact (@lem19699 (term788 x' b s) (term892 x' s b) (term888 x' b' s)). Qed.
Lemma lem5263922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5263923 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term895 b x' b' s) = (term896 b x' b' s).
Proof. exact (MK_COMB (@lem5263922) (@lem5263921 b x' b' s)). Qed.
Lemma lem5263924 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term887 b x' b' s) = (term897 b x' b' s).
Proof. exact (MK_COMB (@lem5263923 b x' b' s) (@lem5263914 b x' b' s)). Qed.
Lemma lem5263925 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term886 b x' b' s) = (term897 b x' b' s).
Proof. exact (TRANS (@lem5263907 b x' b' s) (@lem5263924 b x' b' s)). Qed.
Lemma lem5263932 (x' : type1021) (b : real) (s : real -> Prop) (b' : real) : (term898 x' b s b') = (term899 x' b s b').
Proof. exact (@lem19699 (term788 x' b s) (term892 x' s b) (term292 s b')). Qed.
Lemma lem5263933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5263934 (x' : type1021) (b : real) (s : real -> Prop) (b' : real) : (term900 x' b s b') = (term901 x' b s b').
Proof. exact (MK_COMB (@lem5263933) (@lem5263932 x' b s b')). Qed.
Lemma lem5263935 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term885 b x' b' s) = (term902 b x' b' s).
Proof. exact (MK_COMB (@lem5263934 x' b s b') (@lem5263925 b x' b' s)). Qed.
Lemma lem5263936 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term884 b x' b' s) = (term902 b x' b' s).
Proof. exact (TRANS (@lem5263906 b x' b' s) (@lem5263935 b x' b' s)). Qed.
Lemma lem5263937 (b : real) (x' : type1021) (b' : real) (s : real -> Prop) : (term871 b x' b' s) = (term902 b x' b' s).
Proof. exact (TRANS (@lem5263905 b x' b' s) (@lem5263936 b x' b' s)). Qed.
Lemma lem5263938 (b : real) (x' : type1021) (s : real -> Prop) : (term873 b x' s) = (term903 b x' s).
Proof. exact (fun_ext (fun b' : real => @lem5263937 b x' b' s)). Qed.
Lemma lem5263939 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263940 (b : real) (x' : type1021) (s : real -> Prop) : (term874 b x' s) = (term904 b x' s).
Proof. exact (MK_COMB (@lem5263939) (@lem5263938 b x' s)). Qed.
Lemma lem5263941 (x' : type1021) (s : real -> Prop) : (term875 x' s) = (term905 x' s).
Proof. exact (fun_ext (fun b : real => @lem5263940 b x' s)). Qed.
Lemma lem5263942 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263943 (x' : type1021) (s : real -> Prop) : (term876 x' s) = (term906 x' s).
Proof. exact (MK_COMB (@lem5263942) (@lem5263941 x' s)). Qed.
Lemma lem5263944 (x' : type1021) : (term877 x') = (term907 x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5263943 x' s)). Qed.
Lemma lem5263945 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5263946 (x' : type1021) : (term878 x') = (term908 x').
Proof. exact (MK_COMB (@lem5263945) (@lem5263944 x')). Qed.
Lemma lem5263947 (x' : type1021) : (term454 x') = (term908 x').
Proof. exact (TRANS (@lem5263858 x') (@lem5263946 x')). Qed.
Lemma lem5263948 (x' : type1021) (h1 : term454 x') : term908 x'.
Proof. exact (EQ_MP (@lem5263947 x') (@lem5262990 x' h1)). Qed.
Lemma lem5263992 (x : real) (k : real) : (term461 x k) = (term806 x k).
Proof. exact (@lem19490 (term460 k x) (term807 x k) (real_le x k)). Qed.
Lemma lem5263993 (x : real) : (term480 x) = (term808 x).
Proof. exact (fun_ext (fun k : real => @lem5263992 x k)). Qed.
Lemma lem5263994 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263995 (x : real) : (term495 x) = (term809 x).
Proof. exact (MK_COMB (@lem5263994) (@lem5263993 x)). Qed.
Lemma lem5263996 : term502 = term810.
Proof. exact (fun_ext (fun x : real => @lem5263995 x)). Qed.
Lemma lem5263997 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5263999 : term517 = term811.
Proof. exact (MK_COMB (@lem5263997) (@lem5263996)). Qed.
Lemma lem5264000 (h1 : term229) : term811.
Proof. exact (EQ_MP (@lem5263999) (@lem5263023 h1)). Qed.
Lemma lem5264004 (s : real -> Prop) (x'' : real) (h1 : term909 s x'') : term909 s x''.
Proof. exact (h1). Qed.
Lemma lem5264005 (_68878 : real) (s : real -> Prop) (B : real) (h1 : term146 s B) : term910 s B _68878.
Proof. exact (@lem5263043 s B h1 _68878). Qed.
Lemma lem5264006 (s : real -> Prop) (_68878 : real) (B : real) : (term910 s B _68878) = (term251 s _68878 B).
Proof. exact (eq_refl (term910 s B _68878)). Qed.
Lemma lem5264008 (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term911 x _68879.
Proof. exact (@lem5263253 x h1 _68879). Qed.
Lemma lem5264009 (x : type1021) (_68879 : real -> Prop) : (term911 x _68879) = (term803 x _68879).
Proof. exact (eq_refl (term911 x _68879)). Qed.
Lemma lem5264010 (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term803 x _68879.
Proof. exact (EQ_MP (@lem5264009 x _68879) (@lem5264008 _68879 x h1)). Qed.
Lemma lem5264011 (_68879 : real -> Prop) (_68880 : real) (x : type1021) (h1 : term678 x) : term912 x _68879 _68880.
Proof. exact (@lem5264010 _68879 x h1 _68880). Qed.
Lemma lem5264012 (_68880 : real) (x : type1021) (_68879 : real -> Prop) : (term912 x _68879 _68880) = (term801 _68880 x _68879).
Proof. exact (eq_refl (term912 x _68879 _68880)). Qed.
Lemma lem5264013 (_68880 : real) (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term801 _68880 x _68879.
Proof. exact (EQ_MP (@lem5264012 _68880 x _68879) (@lem5264011 _68879 _68880 x h1)). Qed.
Lemma lem5264014 (_68880 : real) (_68879 : real -> Prop) (_68881 : real) (x : type1021) (h1 : term678 x) : term913 _68880 x _68879 _68881.
Proof. exact (@lem5264013 _68880 _68879 x h1 _68881). Qed.
Lemma lem5264015 (_68880 : real) (x : type1021) (_68879 : real -> Prop) (_68881 : real) : (term913 _68880 x _68879 _68881) = (term799 _68880 x _68879 _68881).
Proof. exact (eq_refl (term913 _68880 x _68879 _68881)). Qed.
Lemma lem5264016 (_68880 : real) (_68879 : real -> Prop) (_68881 : real) (x : type1021) (h1 : term678 x) : term799 _68880 x _68879 _68881.
Proof. exact (EQ_MP (@lem5264015 _68880 x _68879 _68881) (@lem5264014 _68880 _68879 _68881 x h1)). Qed.
Lemma lem5264032 (_68887 : real) (h1 : term229) : term914 _68887.
Proof. exact (@lem5263511 h1 _68887). Qed.
Lemma lem5264033 (_68887 : real) : (term914 _68887) = (term809 _68887).
Proof. exact (eq_refl (term914 _68887)). Qed.
Lemma lem5264034 (_68887 : real) (h1 : term229) : term809 _68887.
Proof. exact (EQ_MP (@lem5264033 _68887) (@lem5264032 _68887 h1)). Qed.
Lemma lem5264035 (_68887 : real) (_68888 : real) (h1 : term229) : term915 _68887 _68888.
Proof. exact (@lem5264034 _68887 h1 _68888). Qed.
Lemma lem5264036 (_68887 : real) (_68888 : real) : (term915 _68887 _68888) = (term806 _68887 _68888).
Proof. exact (eq_refl (term915 _68887 _68888)). Qed.
Lemma lem5264037 (_68887 : real) (_68888 : real) (h1 : term229) : term806 _68887 _68888.
Proof. exact (EQ_MP (@lem5264036 _68887 _68888) (@lem5264035 _68887 _68888 h1)). Qed.
Lemma lem5264038 (_68889 : real) (s : real -> Prop) (B : real) (h1 : term146 s B) : term910 s B _68889.
Proof. exact (@lem5263532 s B h1 _68889). Qed.
Lemma lem5264039 (s : real -> Prop) (_68889 : real) (B : real) : (term910 s B _68889) = (term251 s _68889 B).
Proof. exact (eq_refl (term910 s B _68889)). Qed.
Lemma lem5264050 (_68893 : real -> Prop) (x' : type1021) (h1 : term454 x') : term916 x' _68893.
Proof. exact (@lem5263948 x' h1 _68893). Qed.
Lemma lem5264051 (x' : type1021) (_68893 : real -> Prop) : (term916 x' _68893) = (term906 x' _68893).
Proof. exact (eq_refl (term916 x' _68893)). Qed.
Lemma lem5264052 (_68893 : real -> Prop) (x' : type1021) (h1 : term454 x') : term906 x' _68893.
Proof. exact (EQ_MP (@lem5264051 x' _68893) (@lem5264050 _68893 x' h1)). Qed.
Lemma lem5264053 (_68893 : real -> Prop) (_68894 : real) (x' : type1021) (h1 : term454 x') : term917 x' _68893 _68894.
Proof. exact (@lem5264052 _68893 x' h1 _68894). Qed.
Lemma lem5264054 (_68894 : real) (x' : type1021) (_68893 : real -> Prop) : (term917 x' _68893 _68894) = (term904 _68894 x' _68893).
Proof. exact (eq_refl (term917 x' _68893 _68894)). Qed.
Lemma lem5264055 (_68894 : real) (_68893 : real -> Prop) (x' : type1021) (h1 : term454 x') : term904 _68894 x' _68893.
Proof. exact (EQ_MP (@lem5264054 _68894 x' _68893) (@lem5264053 _68893 _68894 x' h1)). Qed.
Lemma lem5264056 (_68894 : real) (_68893 : real -> Prop) (_68895 : real) (x' : type1021) (h1 : term454 x') : term918 _68894 x' _68893 _68895.
Proof. exact (@lem5264055 _68894 _68893 x' h1 _68895). Qed.
Lemma lem5264057 (_68894 : real) (x' : type1021) (_68895 : real) (_68893 : real -> Prop) : (term918 _68894 x' _68893 _68895) = (term902 _68894 x' _68895 _68893).
Proof. exact (eq_refl (term918 _68894 x' _68893 _68895)). Qed.
Lemma lem5264058 (_68894 : real) (_68895 : real) (_68893 : real -> Prop) (x' : type1021) (h1 : term454 x') : term902 _68894 x' _68895 _68893.
Proof. exact (EQ_MP (@lem5264057 _68894 x' _68895 _68893) (@lem5264056 _68894 _68893 _68895 x' h1)). Qed.
Lemma lem5264065 (_68898 : real) (h1 : term229) : term914 _68898.
Proof. exact (@lem5264000 h1 _68898). Qed.
Lemma lem5264066 (_68898 : real) : (term914 _68898) = (term809 _68898).
Proof. exact (eq_refl (term914 _68898)). Qed.
Lemma lem5264067 (_68898 : real) (h1 : term229) : term809 _68898.
Proof. exact (EQ_MP (@lem5264066 _68898) (@lem5264065 _68898 h1)). Qed.
Lemma lem5264068 (_68898 : real) (_68899 : real) (h1 : term229) : term915 _68898 _68899.
Proof. exact (@lem5264067 _68898 h1 _68899). Qed.
Lemma lem5264069 (_68898 : real) (_68899 : real) : (term915 _68898 _68899) = (term806 _68898 _68899).
Proof. exact (eq_refl (term915 _68898 _68899)). Qed.
Lemma lem5264070 (_68898 : real) (_68899 : real) (h1 : term229) : term806 _68898 _68899.
Proof. exact (EQ_MP (@lem5264069 _68898 _68899) (@lem5264068 _68898 _68899 h1)). Qed.
Lemma lem5264084 (_68880 : real) (_68881 : real) (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term796 x _68880 _68881 _68879.
Proof. exact (proj1 (@lem5264016 _68880 _68879 _68881 x h1)). Qed.
Lemma lem5264091 (_68880 : real) (_68881 : real) (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term919 x _68880 _68881 _68879.
Proof. exact (proj2 (@lem5264084 _68880 _68881 _68879 x h1)). Qed.
Lemma lem5264092 (_68880 : real) (_68881 : real) (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term920 x _68880 _68881 _68879.
Proof. exact (proj1 (@lem5264084 _68880 _68881 _68879 x h1)). Qed.
Lemma lem5264096 (_68894 : real) (_68893 : real -> Prop) (_68895 : real) (x' : type1021) (h1 : term454 x') : term899 x' _68894 _68893 _68895.
Proof. exact (proj1 (@lem5264058 _68894 _68895 _68893 x' h1)). Qed.
Lemma lem5264103 (_68894 : real) (_68893 : real -> Prop) (_68895 : real) (x' : type1021) (h1 : term454 x') : term921 x' _68894 _68893 _68895.
Proof. exact (proj2 (@lem5264096 _68894 _68893 _68895 x' h1)). Qed.
Lemma lem5264104 (_68894 : real) (_68893 : real -> Prop) (_68895 : real) (x' : type1021) (h1 : term454 x') : term922 x' _68894 _68893 _68895.
Proof. exact (proj1 (@lem5264096 _68894 _68893 _68895 x' h1)). Qed.
Lemma lem5264116 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5264122 (_68878 : real) (s : real -> Prop) (B : real) (h1 : term146 s B) : term251 s _68878 B.
Proof. exact (EQ_MP (@lem5264006 s _68878 B) (@lem5264005 _68878 s B h1)). Qed.
Lemma lem5264124 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (sup s) = (inf s).
Proof. exact (h1). Qed.
Lemma lem5264138 (x'' : real) (s : real -> Prop) (h1 : term812 x'' s) : term812 x'' s.
Proof. exact (h1). Qed.
Lemma lem5264150 (_68887 : real) (_68888 : real) (h1 : term229) : term923 _68887 _68888.
Proof. exact (proj2 (@lem5264037 _68887 _68888 h1)). Qed.
Lemma lem5264325 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term920 x _68880 _68881 _68879) = (term924 x _68880 _68881 _68879).
Proof. exact (@lem5259540 (_68879 = (@EMPTY real)) (term775 x _68880 _68879) (term538 _68881 _68879)). Qed.
Lemma lem5264326 (_68880 : real) (_68881 : real) (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term924 x _68880 _68881 _68879.
Proof. exact (EQ_MP (@lem5264325 x _68880 _68881 _68879) (@lem5264092 _68880 _68881 _68879 x h1)). Qed.
Lemma lem5264341 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term919 x _68880 _68881 _68879) = (term925 x _68880 _68881 _68879).
Proof. exact (@lem5259540 (_68879 = (@EMPTY real)) (term776 x _68879 _68880) (term538 _68881 _68879)). Qed.
Lemma lem5264342 (_68880 : real) (_68881 : real) (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term925 x _68880 _68881 _68879.
Proof. exact (EQ_MP (@lem5264341 x _68880 _68881 _68879) (@lem5264091 _68880 _68881 _68879 x h1)). Qed.
Lemma lem5264344 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5264350 (_68889 : real) (s : real -> Prop) (B : real) (h1 : term146 s B) : term251 s _68889 B.
Proof. exact (EQ_MP (@lem5264039 s _68889 B) (@lem5264038 _68889 s B h1)). Qed.
Lemma lem5264366 (s : real -> Prop) (x'' : real) (h1 : term909 s x'') : term909 s x''.
Proof. exact (h1). Qed.
Lemma lem5264372 (_68899 : real) (_68898 : real) (h1 : term229) : term926 _68899 _68898.
Proof. exact (proj1 (@lem5264070 _68898 _68899 h1)). Qed.
Lemma lem5264457 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) (_68895 : real) : (term922 x' _68894 _68893 _68895) = (term927 x' _68894 _68893 _68895).
Proof. exact (@lem5259540 (_68893 = (@EMPTY real)) (term775 x' _68894 _68893) (term292 _68893 _68895)). Qed.
Lemma lem5264458 (_68894 : real) (_68893 : real -> Prop) (_68895 : real) (x' : type1021) (h1 : term454 x') : term927 x' _68894 _68893 _68895.
Proof. exact (EQ_MP (@lem5264457 x' _68894 _68893 _68895) (@lem5264104 _68894 _68893 _68895 x' h1)). Qed.
Lemma lem5264473 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) (_68895 : real) : (term921 x' _68894 _68893 _68895) = (term928 x' _68894 _68893 _68895).
Proof. exact (@lem5259540 (_68893 = (@EMPTY real)) (term880 x' _68893 _68894) (term292 _68893 _68895)). Qed.
Lemma lem5264474 (_68894 : real) (_68893 : real -> Prop) (_68895 : real) (x' : type1021) (h1 : term454 x') : term928 x' _68894 _68893 _68895.
Proof. exact (EQ_MP (@lem5264473 x' _68894 _68893 _68895) (@lem5264103 _68894 _68893 _68895 x' h1)). Qed.
Lemma lem5264590 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5264591 (_68904 : real) (_68906 : real) (h1 : _68904 = _68906) : _68904 = _68906.
Proof. exact (h1). Qed.
Lemma lem5264592 (_68905 : real) (_68907 : real) (h1 : _68905 = _68907) : _68905 = _68907.
Proof. exact (h1). Qed.
Lemma lem5264593 (_68904 : real) (_68906 : real) (h1 : _68904 = _68906) : (real_le _68904) = (real_le _68906).
Proof. exact (MK_COMB (@lem5264590) (@lem5264591 _68904 _68906 h1)). Qed.
Lemma lem5264594 (_68904 : real) (_68906 : real) (_68905 : real) (_68907 : real) (h1 : _68904 = _68906) (h2 : _68905 = _68907) : (real_le _68904 _68905) = (real_le _68906 _68907).
Proof. exact (MK_COMB (@lem5264593 _68904 _68906 h1) (@lem5264592 _68905 _68907 h2)). Qed.
Lemma lem5264596 (b : Prop) (a : Prop) : term112 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5264597 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : term929 _68906 _68907 _68904 _68905.
Proof. exact (@lem5264596 (real_le _68906 _68907) (real_le _68904 _68905)). Qed.
Lemma lem5264598 (_68904 : real) (_68906 : real) (_68905 : real) (_68907 : real) (h1 : _68904 = _68906) (h2 : _68905 = _68907) : term930 _68906 _68907 _68904 _68905.
Proof. exact (@lem5264597 _68906 _68907 _68904 _68905 (@lem5264594 _68904 _68906 _68905 _68907 h1 h2)). Qed.
Lemma lem5264599 (_68907 : real) (_68905 : real) (_68904 : real) (_68906 : real) (h1 : _68904 = _68906) : term931 _68906 _68907 _68904 _68905.
Proof. exact (fun h0 : _68905 = _68907 => @lem5264598 _68904 _68906 _68905 _68907 h1 h0). Qed.
Lemma lem5264601 (a : Prop) (b : Prop) : (a -> b) = (term116 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5264602 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term931 _68906 _68907 _68904 _68905) = (term932 _68906 _68907 _68904 _68905).
Proof. exact (@lem5264601 (_68905 = _68907) (term930 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5264603 (_68907 : real) (_68905 : real) (_68904 : real) (_68906 : real) (h1 : _68904 = _68906) : term932 _68906 _68907 _68904 _68905.
Proof. exact (EQ_MP (@lem5264602 _68906 _68907 _68904 _68905) (@lem5264599 _68907 _68905 _68904 _68906 h1)). Qed.
Lemma lem5264604 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : term933 _68906 _68907 _68904 _68905.
Proof. exact (fun h0 : _68904 = _68906 => @lem5264603 _68907 _68905 _68904 _68906 h0). Qed.
Lemma lem5264606 (a : Prop) (b : Prop) : (a -> b) = (term116 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5264607 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term933 _68906 _68907 _68904 _68905) = (term934 _68906 _68907 _68904 _68905).
Proof. exact (@lem5264606 (_68904 = _68906) (term932 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5264608 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : term934 _68906 _68907 _68904 _68905.
Proof. exact (EQ_MP (@lem5264607 _68906 _68907 _68904 _68905) (@lem5264604 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5264676 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5264677 (x'' : real) : x'' = x''.
Proof. exact (@lem5264676 x''). Qed.
Lemma lem5264678 (x'' : real) : term935 x''.
Proof. exact (fun h0 : term936 x'' => @lem5264677 x''). Qed.
Lemma lem5264680 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5264681 (x'' : real) : (term935 x'') = (x'' = x'').
Proof. exact (@lem5264680 (x'' = x'')). Qed.
Lemma lem5264682 (x'' : real) : x'' = x''.
Proof. exact (EQ_MP (@lem5264681 x'') (@lem5264678 x'')). Qed.
Lemma lem5264684 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (sup s) = (inf s).
Proof. exact (h1). Qed.
Lemma lem5264685 (s : real -> Prop) (h1 : (sup s) = (inf s)) : term937 s.
Proof. exact (fun h0 : term938 s => @lem5264684 s h1). Qed.
Lemma lem5264687 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5264688 (s : real -> Prop) : (term937 s) = ((sup s) = (inf s)).
Proof. exact (@lem5264687 ((sup s) = (inf s))). Qed.
Lemma lem5264689 (s : real -> Prop) (h1 : (sup s) = (inf s)) : (sup s) = (inf s).
Proof. exact (EQ_MP (@lem5264688 s) (@lem5264685 s h1)). Qed.
Lemma lem5264691 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5264692 (s : real -> Prop) (h1 : term145 s) : term939 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5264691 s h1). Qed.
Lemma lem5264694 (p : Prop) : (term940 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5264695 (s : real -> Prop) : (term939 s) = (term145 s).
Proof. exact (@lem5264694 (s = (@EMPTY real))). Qed.
Lemma lem5264696 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (EQ_MP (@lem5264695 s) (@lem5264692 s h1)). Qed.
Lemma lem5264698 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5264699 (s : real -> Prop) (h1 : term145 s) : term939 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5264698 s h1). Qed.
Lemma lem5264701 (p : Prop) : (term940 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5264702 (s : real -> Prop) : (term939 s) = (term145 s).
Proof. exact (@lem5264701 (s = (@EMPTY real))). Qed.
Lemma lem5264703 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (EQ_MP (@lem5264702 s) (@lem5264699 s h1)). Qed.
Lemma lem5264705 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : @IN real x'' s.
Proof. exact (proj1 (@lem5263020 s x'' h1)). Qed.
Lemma lem5264706 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : term941 x'' s.
Proof. exact (fun h0 : term942 x'' s => @lem5264705 s x'' h1). Qed.
Lemma lem5264708 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5264709 (x'' : real) (s : real -> Prop) : (term941 x'' s) = (@IN real x'' s).
Proof. exact (@lem5264708 (@IN real x'' s)). Qed.
Lemma lem5264710 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : @IN real x'' s.
Proof. exact (EQ_MP (@lem5264709 x'' s) (@lem5264706 s x'' h1)). Qed.
Lemma lem5264713 (x'' : real) (s : real -> Prop) (h1 : term943 x'' s) : term943 x'' s.
Proof. exact (h1). Qed.
Lemma lem5264714 (x'' : real) (s : real -> Prop) (h1 : term943 x'' s) : term944 x'' s.
Proof. exact (fun h0 : term154 x'' s => @lem5264713 x'' s h1). Qed.
Lemma lem5264716 (p : Prop) : (term940 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5264717 (x'' : real) (s : real -> Prop) : (term944 x'' s) = (term943 x'' s).
Proof. exact (@lem5264716 (term154 x'' s)). Qed.
Lemma lem5264718 (x'' : real) (s : real -> Prop) (h1 : term943 x'' s) : term943 x'' s.
Proof. exact (EQ_MP (@lem5264717 x'' s) (@lem5264714 x'' s h1)). Qed.
Lemma lem5264746 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5264747 (_68881 : real) (_68879 : real -> Prop) : (term538 _68881 _68879) = (term945 _68881 _68879).
Proof. exact (@lem5264746 (term154 _68881 _68879) (term942 _68881 _68879)). Qed.
Lemma lem5264753 (x : type1021) (_68880 : real) (_68879 : real -> Prop) : (term946 x _68880 _68879) = (term946 x _68880 _68879).
Proof. exact (eq_refl (term946 x _68880 _68879)). Qed.
Lemma lem5264754 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term947 x _68880 _68881 _68879) = (term948 x _68880 _68881 _68879).
Proof. exact (MK_COMB (@lem5264753 x _68880 _68879) (@lem5264747 _68881 _68879)). Qed.
Lemma lem5264765 (_68879 : real -> Prop) : (term288 _68879) = (term288 _68879).
Proof. exact (eq_refl (term288 _68879)). Qed.
Lemma lem5264766 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term924 x _68880 _68881 _68879) = (term949 x _68880 _68881 _68879).
Proof. exact (MK_COMB (@lem5264765 _68879) (@lem5264754 x _68880 _68881 _68879)). Qed.
Lemma lem5264777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5264778 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term950 x _68880 _68881 _68879) = (term951 x _68880 _68881 _68879).
Proof. exact (MK_COMB (@lem5264777) (@lem5264766 x _68880 _68881 _68879)). Qed.
Lemma lem5264782 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5264783 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term952 x _68880 _68881 _68879) = (term924 x _68880 _68881 _68879).
Proof. exact (@lem5264782 (_68879 = (@EMPTY real)) (term775 x _68880 _68879) (term538 _68881 _68879)). Qed.
Lemma lem5264809 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5264810 (_68881 : real) (_68879 : real -> Prop) : (term538 _68881 _68879) = (term945 _68881 _68879).
Proof. exact (@lem5264809 (term154 _68881 _68879) (term942 _68881 _68879)). Qed.
Lemma lem5264816 (x : type1021) (_68880 : real) (_68879 : real -> Prop) : (term946 x _68880 _68879) = (term946 x _68880 _68879).
Proof. exact (eq_refl (term946 x _68880 _68879)). Qed.
Lemma lem5264817 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term947 x _68880 _68881 _68879) = (term948 x _68880 _68881 _68879).
Proof. exact (MK_COMB (@lem5264816 x _68880 _68879) (@lem5264810 _68881 _68879)). Qed.
Lemma lem5264828 (_68879 : real -> Prop) : (term288 _68879) = (term288 _68879).
Proof. exact (eq_refl (term288 _68879)). Qed.
Lemma lem5264829 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term924 x _68880 _68881 _68879) = (term949 x _68880 _68881 _68879).
Proof. exact (MK_COMB (@lem5264828 _68879) (@lem5264817 x _68880 _68881 _68879)). Qed.
Lemma lem5264840 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term952 x _68880 _68881 _68879) = (term949 x _68880 _68881 _68879).
Proof. exact (TRANS (@lem5264783 x _68880 _68881 _68879) (@lem5264829 x _68880 _68881 _68879)). Qed.
Lemma lem5264841 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : ((term924 x _68880 _68881 _68879) = (term952 x _68880 _68881 _68879)) = ((term949 x _68880 _68881 _68879) = (term949 x _68880 _68881 _68879)).
Proof. exact (MK_COMB (@lem5264778 x _68880 _68881 _68879) (@lem5264840 x _68880 _68881 _68879)). Qed.
Lemma lem5264843 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5264844 (x : Prop) : (x = x) = True.
Proof. exact (@lem5264843 Prop x). Qed.
Lemma lem5264845 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : ((term949 x _68880 _68881 _68879) = (term949 x _68880 _68881 _68879)) = True.
Proof. exact (@lem5264844 (term949 x _68880 _68881 _68879)). Qed.
Lemma lem5264846 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : ((term924 x _68880 _68881 _68879) = (term952 x _68880 _68881 _68879)) = True.
Proof. exact (TRANS (@lem5264841 x _68880 _68881 _68879) (@lem5264845 x _68880 _68881 _68879)). Qed.
Lemma lem5264847 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : True = ((term924 x _68880 _68881 _68879) = (term952 x _68880 _68881 _68879)).
Proof. exact (SYM (@lem5264846 x _68880 _68881 _68879)). Qed.
Lemma lem5264848 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term924 x _68880 _68881 _68879) = (term952 x _68880 _68881 _68879).
Proof. exact (EQ_MP (@lem5264847 x _68880 _68881 _68879) (@lem0)). Qed.
Lemma lem5264849 (_68880 : real) (_68881 : real) (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term952 x _68880 _68881 _68879.
Proof. exact (EQ_MP (@lem5264848 x _68880 _68881 _68879) (@lem5264326 _68880 _68881 _68879 x h1)). Qed.
Lemma lem5264851 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5264852 (_68881 : real) (x : type1021) (_68880 : real) (_68879 : real -> Prop) : (term952 x _68880 _68881 _68879) = (term953 _68881 x _68880 _68879).
Proof. exact (@lem5264851 (term954 _68881 _68879) (term775 x _68880 _68879)). Qed.
Lemma lem5264854 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5264855 (_68881 : real) (_68879 : real -> Prop) : (term955 _68881 _68879) = (term956 _68881 _68879).
Proof. exact (@lem5264854 (_68879 = (@EMPTY real)) (term538 _68881 _68879)). Qed.
Lemma lem5264857 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5264858 (_68881 : real) (_68879 : real -> Prop) : (term957 _68881 _68879) = (term958 _68881 _68879).
Proof. exact (@lem5264857 (term942 _68881 _68879) (term154 _68881 _68879)). Qed.
Lemma lem5264860 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5264861 (_68881 : real) (_68879 : real -> Prop) : (term959 _68881 _68879) = (@IN real _68881 _68879).
Proof. exact (@lem5264860 (@IN real _68881 _68879)). Qed.
Lemma lem5264862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5264863 (_68881 : real) (_68879 : real -> Prop) : (term960 _68881 _68879) = (term256 _68881 _68879).
Proof. exact (MK_COMB (@lem5264862) (@lem5264861 _68881 _68879)). Qed.
Lemma lem5264864 (_68881 : real) (_68879 : real -> Prop) : (term943 _68881 _68879) = (term943 _68881 _68879).
Proof. exact (eq_refl (term943 _68881 _68879)). Qed.
Lemma lem5264865 (_68881 : real) (_68879 : real -> Prop) : (term958 _68881 _68879) = (term961 _68881 _68879).
Proof. exact (MK_COMB (@lem5264863 _68881 _68879) (@lem5264864 _68881 _68879)). Qed.
Lemma lem5264866 (_68881 : real) (_68879 : real -> Prop) : (term957 _68881 _68879) = (term961 _68881 _68879).
Proof. exact (TRANS (@lem5264858 _68881 _68879) (@lem5264865 _68881 _68879)). Qed.
Lemma lem5264867 (_68879 : real -> Prop) : (term152 _68879) = (term152 _68879).
Proof. exact (eq_refl (term152 _68879)). Qed.
Lemma lem5264868 (_68881 : real) (_68879 : real -> Prop) : (term956 _68881 _68879) = (term962 _68881 _68879).
Proof. exact (MK_COMB (@lem5264867 _68879) (@lem5264866 _68881 _68879)). Qed.
Lemma lem5264869 (_68881 : real) (_68879 : real -> Prop) : (term955 _68881 _68879) = (term962 _68881 _68879).
Proof. exact (TRANS (@lem5264855 _68881 _68879) (@lem5264868 _68881 _68879)). Qed.
Lemma lem5264870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5264871 (_68881 : real) (_68879 : real -> Prop) : (term963 _68881 _68879) = (term964 _68881 _68879).
Proof. exact (MK_COMB (@lem5264870) (@lem5264869 _68881 _68879)). Qed.
Lemma lem5264872 (x : type1021) (_68880 : real) (_68879 : real -> Prop) : (term775 x _68880 _68879) = (term775 x _68880 _68879).
Proof. exact (eq_refl (term775 x _68880 _68879)). Qed.
Lemma lem5264873 (_68881 : real) (x : type1021) (_68880 : real) (_68879 : real -> Prop) : (term953 _68881 x _68880 _68879) = (term965 _68881 x _68880 _68879).
Proof. exact (MK_COMB (@lem5264871 _68881 _68879) (@lem5264872 x _68880 _68879)). Qed.
Lemma lem5264874 (_68881 : real) (x : type1021) (_68880 : real) (_68879 : real -> Prop) : (term952 x _68880 _68881 _68879) = (term965 _68881 x _68880 _68879).
Proof. exact (TRANS (@lem5264852 _68881 x _68880 _68879) (@lem5264873 _68881 x _68880 _68879)). Qed.
Lemma lem5264876 (s : real -> Prop) (x'' : real) (h1 : term943 x'' s) (h2 : term258 s x'') : term961 x'' s.
Proof. exact (conj (@lem5264710 s x'' h2) (@lem5264718 x'' s h1)). Qed.
Lemma lem5264877 (s : real -> Prop) (x'' : real) (h1 : term145 s) (h2 : term943 x'' s) (h3 : term258 s x'') : term962 x'' s.
Proof. exact (conj (@lem5264703 s h1) (@lem5264876 s x'' h2 h3)). Qed.
Lemma lem5264879 (_68881 : real) (_68880 : real) (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term965 _68881 x _68880 _68879.
Proof. exact (EQ_MP (@lem5264874 _68881 x _68880 _68879) (@lem5264849 _68880 _68881 _68879 x h1)). Qed.
Lemma lem5264880 (x'' : real) (_68880 : real) (s : real -> Prop) (x : type1021) (h1 : term678 x) : term965 x'' x _68880 s.
Proof. exact (@lem5264879 x'' _68880 s x h1). Qed.
Lemma lem5264883 (_68880 : real) (x : type1021) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term145 s) (h3 : term943 x'' s) (h4 : term258 s x'') : term775 x _68880 s.
Proof. exact (@lem5264880 x'' _68880 s x h1 (@lem5264877 s x'' h2 h3 h4)). Qed.
Lemma lem5264884 (B : real) (x : type1021) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term145 s) (h3 : term943 x'' s) (h4 : term258 s x'') : term775 x B s.
Proof. exact (@lem5264883 B x s x'' h1 h2 h3 h4). Qed.
Lemma lem5264885 (B : real) (x : type1021) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term145 s) (h3 : term943 x'' s) (h4 : term258 s x'') : term966 x B s.
Proof. exact (fun h0 : term967 x B s => @lem5264884 B x s x'' h1 h2 h3 h4). Qed.
Lemma lem5264887 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5264888 (x : type1021) (B : real) (s : real -> Prop) : (term966 x B s) = (term775 x B s).
Proof. exact (@lem5264887 (term775 x B s)). Qed.
Lemma lem5264889 (B : real) (x : type1021) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term145 s) (h3 : term943 x'' s) (h4 : term258 s x'') : term775 x B s.
Proof. exact (EQ_MP (@lem5264888 x B s) (@lem5264885 B x s x'' h1 h2 h3 h4)). Qed.
Lemma lem5264895 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5264896 (B : real) (_68878 : real) (s : real -> Prop) : (term251 s _68878 B) = (term968 B _68878 s).
Proof. exact (@lem5264895 (term224 _68878 B) (term942 _68878 s)). Qed.
Lemma lem5264902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5264903 (B : real) (_68878 : real) (s : real -> Prop) : (term969 s _68878 B) = (term970 B _68878 s).
Proof. exact (MK_COMB (@lem5264902) (@lem5264896 B _68878 s)). Qed.
Lemma lem5264909 (B : real) (_68878 : real) (s : real -> Prop) : (term968 B _68878 s) = (term968 B _68878 s).
Proof. exact (eq_refl (term968 B _68878 s)). Qed.
Lemma lem5264910 (B : real) (_68878 : real) (s : real -> Prop) : ((term251 s _68878 B) = (term968 B _68878 s)) = ((term968 B _68878 s) = (term968 B _68878 s)).
Proof. exact (MK_COMB (@lem5264903 B _68878 s) (@lem5264909 B _68878 s)). Qed.
Lemma lem5264912 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5264913 (x : Prop) : (x = x) = True.
Proof. exact (@lem5264912 Prop x). Qed.
Lemma lem5264914 (B : real) (_68878 : real) (s : real -> Prop) : ((term968 B _68878 s) = (term968 B _68878 s)) = True.
Proof. exact (@lem5264913 (term968 B _68878 s)). Qed.
Lemma lem5264915 (B : real) (_68878 : real) (s : real -> Prop) : ((term251 s _68878 B) = (term968 B _68878 s)) = True.
Proof. exact (TRANS (@lem5264910 B _68878 s) (@lem5264914 B _68878 s)). Qed.
Lemma lem5264916 (B : real) (_68878 : real) (s : real -> Prop) : True = ((term251 s _68878 B) = (term968 B _68878 s)).
Proof. exact (SYM (@lem5264915 B _68878 s)). Qed.
Lemma lem5264917 (B : real) (_68878 : real) (s : real -> Prop) : (term251 s _68878 B) = (term968 B _68878 s).
Proof. exact (EQ_MP (@lem5264916 B _68878 s) (@lem0)). Qed.
Lemma lem5264918 (_68878 : real) (s : real -> Prop) (B : real) (h1 : term146 s B) : term968 B _68878 s.
Proof. exact (EQ_MP (@lem5264917 B _68878 s) (@lem5264122 _68878 s B h1)). Qed.
Lemma lem5264920 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5264921 (s : real -> Prop) (_68878 : real) (B : real) : (term968 B _68878 s) = (term971 s _68878 B).
Proof. exact (@lem5264920 (term942 _68878 s) (term224 _68878 B)). Qed.
Lemma lem5264923 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5264924 (_68878 : real) (s : real -> Prop) : (term959 _68878 s) = (@IN real _68878 s).
Proof. exact (@lem5264923 (@IN real _68878 s)). Qed.
Lemma lem5264925 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5264926 (_68878 : real) (s : real -> Prop) : (term972 _68878 s) = (term163 _68878 s).
Proof. exact (MK_COMB (@lem5264925) (@lem5264924 _68878 s)). Qed.
Lemma lem5264927 (_68878 : real) (B : real) : (term224 _68878 B) = (term224 _68878 B).
Proof. exact (eq_refl (term224 _68878 B)). Qed.
Lemma lem5264928 (s : real -> Prop) (_68878 : real) (B : real) : (term971 s _68878 B) = (term249 s _68878 B).
Proof. exact (MK_COMB (@lem5264926 _68878 s) (@lem5264927 _68878 B)). Qed.
Lemma lem5264929 (s : real -> Prop) (_68878 : real) (B : real) : (term968 B _68878 s) = (term249 s _68878 B).
Proof. exact (TRANS (@lem5264921 s _68878 B) (@lem5264928 s _68878 B)). Qed.
Lemma lem5264932 (_68878 : real) (s : real -> Prop) (B : real) (h1 : term146 s B) : term249 s _68878 B.
Proof. exact (EQ_MP (@lem5264929 s _68878 B) (@lem5264918 _68878 s B h1)). Qed.
Lemma lem5264933 (x : type1021) (s : real -> Prop) (B : real) (h1 : term146 s B) : term973 x s B.
Proof. exact (@lem5264932 (x s B) s B h1). Qed.
Lemma lem5264936 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term146 s B) (h3 : term145 s) (h4 : term943 x'' s) (h5 : term258 s x'') : term974 x s B.
Proof. exact (@lem5264933 x s B h2 (@lem5264889 B x s x'' h1 h3 h4 h5)). Qed.
Lemma lem5264937 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term146 s B) (h3 : term145 s) (h4 : term943 x'' s) (h5 : term258 s x'') : term975 x s B.
Proof. exact (fun h0 : term976 x s B => @lem5264936 x B s x'' h1 h2 h3 h4 h5). Qed.
Lemma lem5264939 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5264940 (x : type1021) (s : real -> Prop) (B : real) : (term975 x s B) = (term974 x s B).
Proof. exact (@lem5264939 (term974 x s B)). Qed.
Lemma lem5264941 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term146 s B) (h3 : term145 s) (h4 : term943 x'' s) (h5 : term258 s x'') : term974 x s B.
Proof. exact (EQ_MP (@lem5264940 x s B) (@lem5264937 x B s x'' h1 h2 h3 h4 h5)). Qed.
Lemma lem5264947 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5264948 (_68887 : real) (_68888 : real) : (term923 _68887 _68888) = (term977 _68887 _68888).
Proof. exact (@lem5264947 (real_le _68887 _68888) (term807 _68887 _68888)). Qed.
Lemma lem5264954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5264955 (_68887 : real) (_68888 : real) : (term978 _68887 _68888) = (term979 _68887 _68888).
Proof. exact (MK_COMB (@lem5264954) (@lem5264948 _68887 _68888)). Qed.
Lemma lem5264961 (_68887 : real) (_68888 : real) : (term977 _68887 _68888) = (term977 _68887 _68888).
Proof. exact (eq_refl (term977 _68887 _68888)). Qed.
Lemma lem5264962 (_68887 : real) (_68888 : real) : ((term923 _68887 _68888) = (term977 _68887 _68888)) = ((term977 _68887 _68888) = (term977 _68887 _68888)).
Proof. exact (MK_COMB (@lem5264955 _68887 _68888) (@lem5264961 _68887 _68888)). Qed.
Lemma lem5264964 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5264965 (x : Prop) : (x = x) = True.
Proof. exact (@lem5264964 Prop x). Qed.
Lemma lem5264966 (_68887 : real) (_68888 : real) : ((term977 _68887 _68888) = (term977 _68887 _68888)) = True.
Proof. exact (@lem5264965 (term977 _68887 _68888)). Qed.
Lemma lem5264967 (_68887 : real) (_68888 : real) : ((term923 _68887 _68888) = (term977 _68887 _68888)) = True.
Proof. exact (TRANS (@lem5264962 _68887 _68888) (@lem5264966 _68887 _68888)). Qed.
Lemma lem5264968 (_68887 : real) (_68888 : real) : True = ((term923 _68887 _68888) = (term977 _68887 _68888)).
Proof. exact (SYM (@lem5264967 _68887 _68888)). Qed.
Lemma lem5264969 (_68887 : real) (_68888 : real) : (term923 _68887 _68888) = (term977 _68887 _68888).
Proof. exact (EQ_MP (@lem5264968 _68887 _68888) (@lem0)). Qed.
Lemma lem5264970 (_68887 : real) (_68888 : real) (h1 : term229) : term977 _68887 _68888.
Proof. exact (EQ_MP (@lem5264969 _68887 _68888) (@lem5264150 _68887 _68888 h1)). Qed.
Lemma lem5264972 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5264973 (_68887 : real) (_68888 : real) : (term977 _68887 _68888) = (term980 _68887 _68888).
Proof. exact (@lem5264972 (term807 _68887 _68888) (real_le _68887 _68888)). Qed.
Lemma lem5264975 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5264976 (_68887 : real) (_68888 : real) : (term981 _68887 _68888) = (term224 _68887 _68888).
Proof. exact (@lem5264975 (term224 _68887 _68888)). Qed.
Lemma lem5264977 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5264978 (_68887 : real) (_68888 : real) : (term982 _68887 _68888) = (term983 _68887 _68888).
Proof. exact (MK_COMB (@lem5264977) (@lem5264976 _68887 _68888)). Qed.
Lemma lem5264979 (_68887 : real) (_68888 : real) : (real_le _68887 _68888) = (real_le _68887 _68888).
Proof. exact (eq_refl (real_le _68887 _68888)). Qed.
Lemma lem5264980 (_68887 : real) (_68888 : real) : (term980 _68887 _68888) = (term984 _68887 _68888).
Proof. exact (MK_COMB (@lem5264978 _68887 _68888) (@lem5264979 _68887 _68888)). Qed.
Lemma lem5264981 (_68887 : real) (_68888 : real) : (term977 _68887 _68888) = (term984 _68887 _68888).
Proof. exact (TRANS (@lem5264973 _68887 _68888) (@lem5264980 _68887 _68888)). Qed.
Lemma lem5264984 (_68887 : real) (_68888 : real) (h1 : term229) : term984 _68887 _68888.
Proof. exact (EQ_MP (@lem5264981 _68887 _68888) (@lem5264970 _68887 _68888 h1)). Qed.
Lemma lem5264985 (x : type1021) (s : real -> Prop) (B : real) (h1 : term229) : term985 x s B.
Proof. exact (@lem5264984 (x s B) B h1). Qed.
Lemma lem5264988 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term943 x'' s) (h6 : term258 s x'') : term986 x s B.
Proof. exact (@lem5264985 x s B h2 (@lem5264941 x B s x'' h1 h3 h4 h5 h6)). Qed.
Lemma lem5264989 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term943 x'' s) (h6 : term258 s x'') : term987 x s B.
Proof. exact (fun h0 : term776 x s B => @lem5264988 x B s x'' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5264991 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5264992 (x : type1021) (s : real -> Prop) (B : real) : (term987 x s B) = (term986 x s B).
Proof. exact (@lem5264991 (term986 x s B)). Qed.
Lemma lem5264993 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term943 x'' s) (h6 : term258 s x'') : term986 x s B.
Proof. exact (EQ_MP (@lem5264992 x s B) (@lem5264989 x B s x'' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5264995 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : @IN real x'' s.
Proof. exact (proj1 (@lem5263020 s x'' h1)). Qed.
Lemma lem5264996 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : term941 x'' s.
Proof. exact (fun h0 : term942 x'' s => @lem5264995 s x'' h1). Qed.
Lemma lem5264998 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5264999 (x'' : real) (s : real -> Prop) : (term941 x'' s) = (@IN real x'' s).
Proof. exact (@lem5264998 (@IN real x'' s)). Qed.
Lemma lem5265000 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : @IN real x'' s.
Proof. exact (EQ_MP (@lem5264999 x'' s) (@lem5264996 s x'' h1)). Qed.
Lemma lem5265018 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5265019 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term988 x _68880 _68881 _68879) = (term989 x _68880 _68881 _68879).
Proof. exact (@lem5265018 (term942 _68881 _68879) (term776 x _68879 _68880) (term154 _68881 _68879)). Qed.
Lemma lem5265033 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5265034 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term990 x _68880 _68881 _68879) = (term991 _68881 x _68879 _68880).
Proof. exact (@lem5265033 (term154 _68881 _68879) (term776 x _68879 _68880)). Qed.
Lemma lem5265040 (_68881 : real) (_68879 : real -> Prop) : (term992 _68881 _68879) = (term992 _68881 _68879).
Proof. exact (eq_refl (term992 _68881 _68879)). Qed.
Lemma lem5265041 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term989 x _68880 _68881 _68879) = (term993 _68881 x _68879 _68880).
Proof. exact (MK_COMB (@lem5265040 _68881 _68879) (@lem5265034 _68881 x _68879 _68880)). Qed.
Lemma lem5265045 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5265046 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term993 _68881 x _68879 _68880) = (term994 _68881 x _68879 _68880).
Proof. exact (@lem5265045 (term154 _68881 _68879) (term942 _68881 _68879) (term776 x _68879 _68880)). Qed.
Lemma lem5265062 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term989 x _68880 _68881 _68879) = (term994 _68881 x _68879 _68880).
Proof. exact (TRANS (@lem5265041 _68881 x _68879 _68880) (@lem5265046 _68881 x _68879 _68880)). Qed.
Lemma lem5265063 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term988 x _68880 _68881 _68879) = (term994 _68881 x _68879 _68880).
Proof. exact (TRANS (@lem5265019 x _68880 _68881 _68879) (@lem5265062 _68881 x _68879 _68880)). Qed.
Lemma lem5265064 (_68879 : real -> Prop) : (term288 _68879) = (term288 _68879).
Proof. exact (eq_refl (term288 _68879)). Qed.
Lemma lem5265065 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term925 x _68880 _68881 _68879) = (term995 _68881 x _68879 _68880).
Proof. exact (MK_COMB (@lem5265064 _68879) (@lem5265063 _68881 x _68879 _68880)). Qed.
Lemma lem5265076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5265077 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term996 x _68880 _68881 _68879) = (term997 _68881 x _68879 _68880).
Proof. exact (MK_COMB (@lem5265076) (@lem5265065 _68881 x _68879 _68880)). Qed.
Lemma lem5265081 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5265082 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term998 x _68880 _68881 _68879) = (term999 x _68880 _68881 _68879).
Proof. exact (@lem5265081 (_68879 = (@EMPTY real)) (term154 _68881 _68879) (term1000 x _68880 _68881 _68879)). Qed.
Lemma lem5265108 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5265109 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term1000 x _68880 _68881 _68879) = (term1001 _68881 x _68879 _68880).
Proof. exact (@lem5265108 (term942 _68881 _68879) (term776 x _68879 _68880)). Qed.
Lemma lem5265115 (_68881 : real) (_68879 : real -> Prop) : (term1002 _68881 _68879) = (term1002 _68881 _68879).
Proof. exact (eq_refl (term1002 _68881 _68879)). Qed.
Lemma lem5265116 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term1003 x _68880 _68881 _68879) = (term994 _68881 x _68879 _68880).
Proof. exact (MK_COMB (@lem5265115 _68881 _68879) (@lem5265109 _68881 x _68879 _68880)). Qed.
Lemma lem5265127 (_68879 : real -> Prop) : (term288 _68879) = (term288 _68879).
Proof. exact (eq_refl (term288 _68879)). Qed.
Lemma lem5265128 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term999 x _68880 _68881 _68879) = (term995 _68881 x _68879 _68880).
Proof. exact (MK_COMB (@lem5265127 _68879) (@lem5265116 _68881 x _68879 _68880)). Qed.
Lemma lem5265139 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term998 x _68880 _68881 _68879) = (term995 _68881 x _68879 _68880).
Proof. exact (TRANS (@lem5265082 x _68880 _68881 _68879) (@lem5265128 _68881 x _68879 _68880)). Qed.
Lemma lem5265140 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : ((term925 x _68880 _68881 _68879) = (term998 x _68880 _68881 _68879)) = ((term995 _68881 x _68879 _68880) = (term995 _68881 x _68879 _68880)).
Proof. exact (MK_COMB (@lem5265077 _68881 x _68879 _68880) (@lem5265139 _68881 x _68879 _68880)). Qed.
Lemma lem5265142 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5265143 (x : Prop) : (x = x) = True.
Proof. exact (@lem5265142 Prop x). Qed.
Lemma lem5265144 (_68881 : real) (x : type1021) (_68879 : real -> Prop) (_68880 : real) : ((term995 _68881 x _68879 _68880) = (term995 _68881 x _68879 _68880)) = True.
Proof. exact (@lem5265143 (term995 _68881 x _68879 _68880)). Qed.
Lemma lem5265145 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : ((term925 x _68880 _68881 _68879) = (term998 x _68880 _68881 _68879)) = True.
Proof. exact (TRANS (@lem5265140 _68881 x _68879 _68880) (@lem5265144 _68881 x _68879 _68880)). Qed.
Lemma lem5265146 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : True = ((term925 x _68880 _68881 _68879) = (term998 x _68880 _68881 _68879)).
Proof. exact (SYM (@lem5265145 x _68880 _68881 _68879)). Qed.
Lemma lem5265147 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term925 x _68880 _68881 _68879) = (term998 x _68880 _68881 _68879).
Proof. exact (EQ_MP (@lem5265146 x _68880 _68881 _68879) (@lem0)). Qed.
Lemma lem5265148 (_68880 : real) (_68881 : real) (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term998 x _68880 _68881 _68879.
Proof. exact (EQ_MP (@lem5265147 x _68880 _68881 _68879) (@lem5264342 _68880 _68881 _68879 x h1)). Qed.
Lemma lem5265150 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5265151 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term998 x _68880 _68881 _68879) = (term1004 x _68880 _68881 _68879).
Proof. exact (@lem5265150 (term1005 x _68880 _68881 _68879) (term154 _68881 _68879)). Qed.
Lemma lem5265153 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5265154 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term1006 x _68880 _68881 _68879) = (term1007 x _68880 _68881 _68879).
Proof. exact (@lem5265153 (_68879 = (@EMPTY real)) (term1000 x _68880 _68881 _68879)). Qed.
Lemma lem5265156 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5265157 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term1008 x _68880 _68881 _68879) = (term1009 x _68880 _68881 _68879).
Proof. exact (@lem5265156 (term776 x _68879 _68880) (term942 _68881 _68879)). Qed.
Lemma lem5265159 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5265160 (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term1010 x _68879 _68880) = (term986 x _68879 _68880).
Proof. exact (@lem5265159 (term986 x _68879 _68880)). Qed.
Lemma lem5265161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5265162 (x : type1021) (_68879 : real -> Prop) (_68880 : real) : (term1011 x _68879 _68880) = (term1012 x _68879 _68880).
Proof. exact (MK_COMB (@lem5265161) (@lem5265160 x _68879 _68880)). Qed.
Lemma lem5265164 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5265165 (_68881 : real) (_68879 : real -> Prop) : (term959 _68881 _68879) = (@IN real _68881 _68879).
Proof. exact (@lem5265164 (@IN real _68881 _68879)). Qed.
Lemma lem5265166 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term1009 x _68880 _68881 _68879) = (term1013 x _68880 _68881 _68879).
Proof. exact (MK_COMB (@lem5265162 x _68879 _68880) (@lem5265165 _68881 _68879)). Qed.
Lemma lem5265167 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term1008 x _68880 _68881 _68879) = (term1013 x _68880 _68881 _68879).
Proof. exact (TRANS (@lem5265157 x _68880 _68881 _68879) (@lem5265166 x _68880 _68881 _68879)). Qed.
Lemma lem5265168 (_68879 : real -> Prop) : (term152 _68879) = (term152 _68879).
Proof. exact (eq_refl (term152 _68879)). Qed.
Lemma lem5265169 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term1007 x _68880 _68881 _68879) = (term1014 x _68880 _68881 _68879).
Proof. exact (MK_COMB (@lem5265168 _68879) (@lem5265167 x _68880 _68881 _68879)). Qed.
Lemma lem5265170 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term1006 x _68880 _68881 _68879) = (term1014 x _68880 _68881 _68879).
Proof. exact (TRANS (@lem5265154 x _68880 _68881 _68879) (@lem5265169 x _68880 _68881 _68879)). Qed.
Lemma lem5265171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5265172 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term1015 x _68880 _68881 _68879) = (term1016 x _68880 _68881 _68879).
Proof. exact (MK_COMB (@lem5265171) (@lem5265170 x _68880 _68881 _68879)). Qed.
Lemma lem5265173 (_68881 : real) (_68879 : real -> Prop) : (term154 _68881 _68879) = (term154 _68881 _68879).
Proof. exact (eq_refl (term154 _68881 _68879)). Qed.
Lemma lem5265174 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term1004 x _68880 _68881 _68879) = (term1017 x _68880 _68881 _68879).
Proof. exact (MK_COMB (@lem5265172 x _68880 _68881 _68879) (@lem5265173 _68881 _68879)). Qed.
Lemma lem5265175 (x : type1021) (_68880 : real) (_68881 : real) (_68879 : real -> Prop) : (term998 x _68880 _68881 _68879) = (term1017 x _68880 _68881 _68879).
Proof. exact (TRANS (@lem5265151 x _68880 _68881 _68879) (@lem5265174 x _68880 _68881 _68879)). Qed.
Lemma lem5265177 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term943 x'' s) (h6 : term258 s x'') : term1013 x B x'' s.
Proof. exact (conj (@lem5264993 x B s x'' h1 h2 h3 h4 h5 h6) (@lem5265000 s x'' h6)). Qed.
Lemma lem5265178 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term943 x'' s) (h6 : term258 s x'') : term1014 x B x'' s.
Proof. exact (conj (@lem5264696 s h4) (@lem5265177 x B s x'' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5265180 (_68880 : real) (_68881 : real) (_68879 : real -> Prop) (x : type1021) (h1 : term678 x) : term1017 x _68880 _68881 _68879.
Proof. exact (EQ_MP (@lem5265175 x _68880 _68881 _68879) (@lem5265148 _68880 _68881 _68879 x h1)). Qed.
Lemma lem5265181 (B : real) (x'' : real) (s : real -> Prop) (x : type1021) (h1 : term678 x) : term1017 x B x'' s.
Proof. exact (@lem5265180 B x'' s x h1). Qed.
Lemma lem5265184 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term943 x'' s) (h6 : term258 s x'') : term154 x'' s.
Proof. exact (@lem5265181 B x'' s x h1 (@lem5265178 x B s x'' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5265185 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term258 s x'') : term1018 x'' s.
Proof. exact (fun h0 : term943 x'' s => @lem5265184 x B s x'' h1 h2 h3 h4 h0 h5). Qed.
Lemma lem5265187 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5265188 (x'' : real) (s : real -> Prop) : (term1018 x'' s) = (term154 x'' s).
Proof. exact (@lem5265187 (term154 x'' s)). Qed.
Lemma lem5265189 (x : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term258 s x'') : term154 x'' s.
Proof. exact (EQ_MP (@lem5265188 x'' s) (@lem5265185 x B s x'' h1 h2 h3 h4 h5)). Qed.
Lemma lem5265207 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5265208 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term932 _68906 _68907 _68904 _68905) = (term1019 _68906 _68907 _68904 _68905).
Proof. exact (@lem5265207 (real_le _68906 _68907) (term1020 _68905 _68907) (term1021 _68904 _68905)). Qed.
Lemma lem5265226 (_68904 : real) (_68906 : real) : (term1022 _68904 _68906) = (term1022 _68904 _68906).
Proof. exact (eq_refl (term1022 _68904 _68906)). Qed.
Lemma lem5265227 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term934 _68906 _68907 _68904 _68905) = (term1023 _68906 _68907 _68904 _68905).
Proof. exact (MK_COMB (@lem5265226 _68904 _68906) (@lem5265208 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265231 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5265232 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term1023 _68906 _68907 _68904 _68905) = (term1024 _68906 _68907 _68904 _68905).
Proof. exact (@lem5265231 (real_le _68906 _68907) (term1020 _68904 _68906) (term1025 _68907 _68904 _68905)). Qed.
Lemma lem5265262 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term934 _68906 _68907 _68904 _68905) = (term1024 _68906 _68907 _68904 _68905).
Proof. exact (TRANS (@lem5265227 _68906 _68907 _68904 _68905) (@lem5265232 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5265264 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term1026 _68906 _68907 _68904 _68905) = (term1027 _68906 _68907 _68904 _68905).
Proof. exact (MK_COMB (@lem5265263) (@lem5265262 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265294 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term1024 _68906 _68907 _68904 _68905) = (term1024 _68906 _68907 _68904 _68905).
Proof. exact (eq_refl (term1024 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265295 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : ((term934 _68906 _68907 _68904 _68905) = (term1024 _68906 _68907 _68904 _68905)) = ((term1024 _68906 _68907 _68904 _68905) = (term1024 _68906 _68907 _68904 _68905)).
Proof. exact (MK_COMB (@lem5265264 _68906 _68907 _68904 _68905) (@lem5265294 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265297 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5265298 (x : Prop) : (x = x) = True.
Proof. exact (@lem5265297 Prop x). Qed.
Lemma lem5265299 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : ((term1024 _68906 _68907 _68904 _68905) = (term1024 _68906 _68907 _68904 _68905)) = True.
Proof. exact (@lem5265298 (term1024 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265300 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : ((term934 _68906 _68907 _68904 _68905) = (term1024 _68906 _68907 _68904 _68905)) = True.
Proof. exact (TRANS (@lem5265295 _68906 _68907 _68904 _68905) (@lem5265299 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265301 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : True = ((term934 _68906 _68907 _68904 _68905) = (term1024 _68906 _68907 _68904 _68905)).
Proof. exact (SYM (@lem5265300 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265302 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term934 _68906 _68907 _68904 _68905) = (term1024 _68906 _68907 _68904 _68905).
Proof. exact (EQ_MP (@lem5265301 _68906 _68907 _68904 _68905) (@lem0)). Qed.
Lemma lem5265303 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : term1024 _68906 _68907 _68904 _68905.
Proof. exact (EQ_MP (@lem5265302 _68906 _68907 _68904 _68905) (@lem5264608 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265305 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5265306 (_68904 : real) (_68905 : real) (_68906 : real) (_68907 : real) : (term1024 _68906 _68907 _68904 _68905) = (term1028 _68904 _68905 _68906 _68907).
Proof. exact (@lem5265305 (term1029 _68906 _68907 _68904 _68905) (real_le _68906 _68907)). Qed.
Lemma lem5265308 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5265309 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term1030 _68906 _68907 _68904 _68905) = (term1031 _68906 _68907 _68904 _68905).
Proof. exact (@lem5265308 (term1020 _68904 _68906) (term1025 _68907 _68904 _68905)). Qed.
Lemma lem5265311 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5265312 (_68904 : real) (_68906 : real) : (term1032 _68904 _68906) = (_68904 = _68906).
Proof. exact (@lem5265311 (_68904 = _68906)). Qed.
Lemma lem5265313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5265314 (_68904 : real) (_68906 : real) : (term1033 _68904 _68906) = (term1034 _68904 _68906).
Proof. exact (MK_COMB (@lem5265313) (@lem5265312 _68904 _68906)). Qed.
Lemma lem5265316 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5265317 (_68907 : real) (_68904 : real) (_68905 : real) : (term1035 _68907 _68904 _68905) = (term1036 _68907 _68904 _68905).
Proof. exact (@lem5265316 (term1020 _68905 _68907) (term1021 _68904 _68905)). Qed.
Lemma lem5265319 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5265320 (_68905 : real) (_68907 : real) : (term1032 _68905 _68907) = (_68905 = _68907).
Proof. exact (@lem5265319 (_68905 = _68907)). Qed.
Lemma lem5265321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5265322 (_68905 : real) (_68907 : real) : (term1033 _68905 _68907) = (term1034 _68905 _68907).
Proof. exact (MK_COMB (@lem5265321) (@lem5265320 _68905 _68907)). Qed.
Lemma lem5265324 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5265325 (_68904 : real) (_68905 : real) : (term1037 _68904 _68905) = (real_le _68904 _68905).
Proof. exact (@lem5265324 (real_le _68904 _68905)). Qed.
Lemma lem5265326 (_68907 : real) (_68904 : real) (_68905 : real) : (term1036 _68907 _68904 _68905) = (term1038 _68907 _68904 _68905).
Proof. exact (MK_COMB (@lem5265322 _68905 _68907) (@lem5265325 _68904 _68905)). Qed.
Lemma lem5265327 (_68907 : real) (_68904 : real) (_68905 : real) : (term1035 _68907 _68904 _68905) = (term1038 _68907 _68904 _68905).
Proof. exact (TRANS (@lem5265317 _68907 _68904 _68905) (@lem5265326 _68907 _68904 _68905)). Qed.
Lemma lem5265328 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term1031 _68906 _68907 _68904 _68905) = (term1039 _68906 _68907 _68904 _68905).
Proof. exact (MK_COMB (@lem5265314 _68904 _68906) (@lem5265327 _68907 _68904 _68905)). Qed.
Lemma lem5265329 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term1030 _68906 _68907 _68904 _68905) = (term1039 _68906 _68907 _68904 _68905).
Proof. exact (TRANS (@lem5265309 _68906 _68907 _68904 _68905) (@lem5265328 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5265331 (_68906 : real) (_68907 : real) (_68904 : real) (_68905 : real) : (term1040 _68906 _68907 _68904 _68905) = (term1041 _68906 _68907 _68904 _68905).
Proof. exact (MK_COMB (@lem5265330) (@lem5265329 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265332 (_68906 : real) (_68907 : real) : (real_le _68906 _68907) = (real_le _68906 _68907).
Proof. exact (eq_refl (real_le _68906 _68907)). Qed.
Lemma lem5265333 (_68904 : real) (_68905 : real) (_68906 : real) (_68907 : real) : (term1028 _68904 _68905 _68906 _68907) = (term1042 _68904 _68905 _68906 _68907).
Proof. exact (MK_COMB (@lem5265331 _68906 _68907 _68904 _68905) (@lem5265332 _68906 _68907)). Qed.
Lemma lem5265334 (_68904 : real) (_68905 : real) (_68906 : real) (_68907 : real) : (term1024 _68906 _68907 _68904 _68905) = (term1042 _68904 _68905 _68906 _68907).
Proof. exact (TRANS (@lem5265306 _68904 _68905 _68906 _68907) (@lem5265333 _68904 _68905 _68906 _68907)). Qed.
Lemma lem5265336 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term258 s x'') (h6 : (sup s) = (inf s)) : term1043 x'' s.
Proof. exact (conj (@lem5264689 s h6) (@lem5265189 x B s x'' h1 h2 h3 h4 h5)). Qed.
Lemma lem5265337 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term258 s x'') (h6 : (sup s) = (inf s)) : term1044 x'' s.
Proof. exact (conj (@lem5264682 x'') (@lem5265336 x B x'' s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5265339 (_68904 : real) (_68905 : real) (_68906 : real) (_68907 : real) : term1042 _68904 _68905 _68906 _68907.
Proof. exact (EQ_MP (@lem5265334 _68904 _68905 _68906 _68907) (@lem5265303 _68906 _68907 _68904 _68905)). Qed.
Lemma lem5265340 (x'' : real) (s : real -> Prop) : term1045 x'' s.
Proof. exact (@lem5265339 x'' (sup s) x'' (inf s)). Qed.
Lemma lem5265343 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term258 s x'') (h6 : (sup s) = (inf s)) : term155 x'' s.
Proof. exact (@lem5265340 x'' s (@lem5265337 x B x'' s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5265344 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term258 s x'') (h6 : (sup s) = (inf s)) : term1046 x'' s.
Proof. exact (fun h0 : term812 x'' s => @lem5265343 x B x'' s h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5265346 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5265347 (x'' : real) (s : real -> Prop) : (term1046 x'' s) = (term155 x'' s).
Proof. exact (@lem5265346 (term155 x'' s)). Qed.
Lemma lem5265348 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term258 s x'') (h6 : (sup s) = (inf s)) : term155 x'' s.
Proof. exact (EQ_MP (@lem5265347 x'' s) (@lem5265344 x B x'' s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5265351 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5265353 (x'' : real) (s : real -> Prop) : (term812 x'' s) = (term1047 x'' s).
Proof. exact (@lem5265351 (term155 x'' s)). Qed.
Lemma lem5265356 (x'' : real) (s : real -> Prop) (h1 : term812 x'' s) : term1047 x'' s.
Proof. exact (EQ_MP (@lem5265353 x'' s) (@lem5264138 x'' s h1)). Qed.
Lemma lem5265359 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (@lem5265356 x'' s h5 (@lem5265348 x B x'' s h1 h2 h3 h4 h6 h7)). Qed.
Lemma lem5265360 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : term111.
Proof. exact (fun h0 : ~ False => @lem5265359 x B x'' s h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem5265362 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5265363 : term111 = False.
Proof. exact (@lem5265362 False). Qed.
Lemma lem5265364 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5265363) (@lem5265360 x B x'' s h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5265470 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5265471 (s : real -> Prop) (h1 : term145 s) : term939 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5265470 s h1). Qed.
Lemma lem5265473 (p : Prop) : (term940 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5265474 (s : real -> Prop) : (term939 s) = (term145 s).
Proof. exact (@lem5265473 (s = (@EMPTY real))). Qed.
Lemma lem5265475 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (EQ_MP (@lem5265474 s) (@lem5265471 s h1)). Qed.
Lemma lem5265477 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (h1). Qed.
Lemma lem5265478 (s : real -> Prop) (h1 : term145 s) : term939 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5265477 s h1). Qed.
Lemma lem5265480 (p : Prop) : (term940 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5265481 (s : real -> Prop) : (term939 s) = (term145 s).
Proof. exact (@lem5265480 (s = (@EMPTY real))). Qed.
Lemma lem5265482 (s : real -> Prop) (h1 : term145 s) : term145 s.
Proof. exact (EQ_MP (@lem5265481 s) (@lem5265478 s h1)). Qed.
Lemma lem5265484 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : @IN real x'' s.
Proof. exact (proj1 (@lem5263020 s x'' h1)). Qed.
Lemma lem5265485 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : term941 x'' s.
Proof. exact (fun h0 : term942 x'' s => @lem5265484 s x'' h1). Qed.
Lemma lem5265487 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5265488 (x'' : real) (s : real -> Prop) : (term941 x'' s) = (@IN real x'' s).
Proof. exact (@lem5265487 (@IN real x'' s)). Qed.
Lemma lem5265489 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : @IN real x'' s.
Proof. exact (EQ_MP (@lem5265488 x'' s) (@lem5265485 s x'' h1)). Qed.
Lemma lem5265492 (s : real -> Prop) (x'' : real) (h1 : term909 s x'') : term909 s x''.
Proof. exact (h1). Qed.
Lemma lem5265493 (s : real -> Prop) (x'' : real) (h1 : term909 s x'') : term1048 s x''.
Proof. exact (fun h0 : term161 s x'' => @lem5265492 s x'' h1). Qed.
Lemma lem5265495 (p : Prop) : (term940 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5265496 (s : real -> Prop) (x'' : real) : (term1048 s x'') = (term909 s x'').
Proof. exact (@lem5265495 (term161 s x'')). Qed.
Lemma lem5265497 (s : real -> Prop) (x'' : real) (h1 : term909 s x'') : term909 s x''.
Proof. exact (EQ_MP (@lem5265496 s x'') (@lem5265493 s x'' h1)). Qed.
Lemma lem5265525 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5265526 (_68895 : real) (_68893 : real -> Prop) : (term292 _68893 _68895) = (term1049 _68895 _68893).
Proof. exact (@lem5265525 (term161 _68893 _68895) (term942 _68895 _68893)). Qed.
Lemma lem5265532 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) : (term946 x' _68894 _68893) = (term946 x' _68894 _68893).
Proof. exact (eq_refl (term946 x' _68894 _68893)). Qed.
Lemma lem5265533 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1050 x' _68894 _68893 _68895) = (term1051 x' _68894 _68895 _68893).
Proof. exact (MK_COMB (@lem5265532 x' _68894 _68893) (@lem5265526 _68895 _68893)). Qed.
Lemma lem5265544 (_68893 : real -> Prop) : (term288 _68893) = (term288 _68893).
Proof. exact (eq_refl (term288 _68893)). Qed.
Lemma lem5265545 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term927 x' _68894 _68893 _68895) = (term1052 x' _68894 _68895 _68893).
Proof. exact (MK_COMB (@lem5265544 _68893) (@lem5265533 x' _68894 _68895 _68893)). Qed.
Lemma lem5265556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5265557 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1053 x' _68894 _68893 _68895) = (term1054 x' _68894 _68895 _68893).
Proof. exact (MK_COMB (@lem5265556) (@lem5265545 x' _68894 _68895 _68893)). Qed.
Lemma lem5265561 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5265562 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) (_68895 : real) : (term1055 x' _68894 _68893 _68895) = (term927 x' _68894 _68893 _68895).
Proof. exact (@lem5265561 (_68893 = (@EMPTY real)) (term775 x' _68894 _68893) (term292 _68893 _68895)). Qed.
Lemma lem5265588 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5265589 (_68895 : real) (_68893 : real -> Prop) : (term292 _68893 _68895) = (term1049 _68895 _68893).
Proof. exact (@lem5265588 (term161 _68893 _68895) (term942 _68895 _68893)). Qed.
Lemma lem5265595 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) : (term946 x' _68894 _68893) = (term946 x' _68894 _68893).
Proof. exact (eq_refl (term946 x' _68894 _68893)). Qed.
Lemma lem5265596 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1050 x' _68894 _68893 _68895) = (term1051 x' _68894 _68895 _68893).
Proof. exact (MK_COMB (@lem5265595 x' _68894 _68893) (@lem5265589 _68895 _68893)). Qed.
Lemma lem5265607 (_68893 : real -> Prop) : (term288 _68893) = (term288 _68893).
Proof. exact (eq_refl (term288 _68893)). Qed.
Lemma lem5265608 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term927 x' _68894 _68893 _68895) = (term1052 x' _68894 _68895 _68893).
Proof. exact (MK_COMB (@lem5265607 _68893) (@lem5265596 x' _68894 _68895 _68893)). Qed.
Lemma lem5265619 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1055 x' _68894 _68893 _68895) = (term1052 x' _68894 _68895 _68893).
Proof. exact (TRANS (@lem5265562 x' _68894 _68893 _68895) (@lem5265608 x' _68894 _68895 _68893)). Qed.
Lemma lem5265620 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : ((term927 x' _68894 _68893 _68895) = (term1055 x' _68894 _68893 _68895)) = ((term1052 x' _68894 _68895 _68893) = (term1052 x' _68894 _68895 _68893)).
Proof. exact (MK_COMB (@lem5265557 x' _68894 _68895 _68893) (@lem5265619 x' _68894 _68895 _68893)). Qed.
Lemma lem5265622 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5265623 (x : Prop) : (x = x) = True.
Proof. exact (@lem5265622 Prop x). Qed.
Lemma lem5265624 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : ((term1052 x' _68894 _68895 _68893) = (term1052 x' _68894 _68895 _68893)) = True.
Proof. exact (@lem5265623 (term1052 x' _68894 _68895 _68893)). Qed.
Lemma lem5265625 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) (_68895 : real) : ((term927 x' _68894 _68893 _68895) = (term1055 x' _68894 _68893 _68895)) = True.
Proof. exact (TRANS (@lem5265620 x' _68894 _68895 _68893) (@lem5265624 x' _68894 _68895 _68893)). Qed.
Lemma lem5265626 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) (_68895 : real) : True = ((term927 x' _68894 _68893 _68895) = (term1055 x' _68894 _68893 _68895)).
Proof. exact (SYM (@lem5265625 x' _68894 _68893 _68895)). Qed.
Lemma lem5265627 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) (_68895 : real) : (term927 x' _68894 _68893 _68895) = (term1055 x' _68894 _68893 _68895).
Proof. exact (EQ_MP (@lem5265626 x' _68894 _68893 _68895) (@lem0)). Qed.
Lemma lem5265628 (_68894 : real) (_68893 : real -> Prop) (_68895 : real) (x' : type1021) (h1 : term454 x') : term1055 x' _68894 _68893 _68895.
Proof. exact (EQ_MP (@lem5265627 x' _68894 _68893 _68895) (@lem5264458 _68894 _68893 _68895 x' h1)). Qed.
Lemma lem5265630 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5265631 (_68895 : real) (x' : type1021) (_68894 : real) (_68893 : real -> Prop) : (term1055 x' _68894 _68893 _68895) = (term1056 _68895 x' _68894 _68893).
Proof. exact (@lem5265630 (term1057 _68893 _68895) (term775 x' _68894 _68893)). Qed.
Lemma lem5265633 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5265634 (_68893 : real -> Prop) (_68895 : real) : (term1058 _68893 _68895) = (term1059 _68893 _68895).
Proof. exact (@lem5265633 (_68893 = (@EMPTY real)) (term292 _68893 _68895)). Qed.
Lemma lem5265636 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5265637 (_68893 : real -> Prop) (_68895 : real) : (term1060 _68893 _68895) = (term1061 _68893 _68895).
Proof. exact (@lem5265636 (term942 _68895 _68893) (term161 _68893 _68895)). Qed.
Lemma lem5265639 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5265640 (_68895 : real) (_68893 : real -> Prop) : (term959 _68895 _68893) = (@IN real _68895 _68893).
Proof. exact (@lem5265639 (@IN real _68895 _68893)). Qed.
Lemma lem5265641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5265642 (_68895 : real) (_68893 : real -> Prop) : (term960 _68895 _68893) = (term256 _68895 _68893).
Proof. exact (MK_COMB (@lem5265641) (@lem5265640 _68895 _68893)). Qed.
Lemma lem5265643 (_68893 : real -> Prop) (_68895 : real) : (term909 _68893 _68895) = (term909 _68893 _68895).
Proof. exact (eq_refl (term909 _68893 _68895)). Qed.
Lemma lem5265644 (_68893 : real -> Prop) (_68895 : real) : (term1061 _68893 _68895) = (term1062 _68893 _68895).
Proof. exact (MK_COMB (@lem5265642 _68895 _68893) (@lem5265643 _68893 _68895)). Qed.
Lemma lem5265645 (_68893 : real -> Prop) (_68895 : real) : (term1060 _68893 _68895) = (term1062 _68893 _68895).
Proof. exact (TRANS (@lem5265637 _68893 _68895) (@lem5265644 _68893 _68895)). Qed.
Lemma lem5265646 (_68893 : real -> Prop) : (term152 _68893) = (term152 _68893).
Proof. exact (eq_refl (term152 _68893)). Qed.
Lemma lem5265647 (_68893 : real -> Prop) (_68895 : real) : (term1059 _68893 _68895) = (term1063 _68893 _68895).
Proof. exact (MK_COMB (@lem5265646 _68893) (@lem5265645 _68893 _68895)). Qed.
Lemma lem5265648 (_68893 : real -> Prop) (_68895 : real) : (term1058 _68893 _68895) = (term1063 _68893 _68895).
Proof. exact (TRANS (@lem5265634 _68893 _68895) (@lem5265647 _68893 _68895)). Qed.
Lemma lem5265649 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5265650 (_68893 : real -> Prop) (_68895 : real) : (term1064 _68893 _68895) = (term1065 _68893 _68895).
Proof. exact (MK_COMB (@lem5265649) (@lem5265648 _68893 _68895)). Qed.
Lemma lem5265651 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) : (term775 x' _68894 _68893) = (term775 x' _68894 _68893).
Proof. exact (eq_refl (term775 x' _68894 _68893)). Qed.
Lemma lem5265652 (_68895 : real) (x' : type1021) (_68894 : real) (_68893 : real -> Prop) : (term1056 _68895 x' _68894 _68893) = (term1066 _68895 x' _68894 _68893).
Proof. exact (MK_COMB (@lem5265650 _68893 _68895) (@lem5265651 x' _68894 _68893)). Qed.
Lemma lem5265653 (_68895 : real) (x' : type1021) (_68894 : real) (_68893 : real -> Prop) : (term1055 x' _68894 _68893 _68895) = (term1066 _68895 x' _68894 _68893).
Proof. exact (TRANS (@lem5265631 _68895 x' _68894 _68893) (@lem5265652 _68895 x' _68894 _68893)). Qed.
Lemma lem5265655 (s : real -> Prop) (x'' : real) (h1 : term909 s x'') (h2 : term258 s x'') : term1062 s x''.
Proof. exact (conj (@lem5265489 s x'' h2) (@lem5265497 s x'' h1)). Qed.
Lemma lem5265656 (s : real -> Prop) (x'' : real) (h1 : term145 s) (h2 : term909 s x'') (h3 : term258 s x'') : term1063 s x''.
Proof. exact (conj (@lem5265482 s h1) (@lem5265655 s x'' h2 h3)). Qed.
Lemma lem5265658 (_68895 : real) (_68894 : real) (_68893 : real -> Prop) (x' : type1021) (h1 : term454 x') : term1066 _68895 x' _68894 _68893.
Proof. exact (EQ_MP (@lem5265653 _68895 x' _68894 _68893) (@lem5265628 _68894 _68893 _68895 x' h1)). Qed.
Lemma lem5265659 (x'' : real) (_68894 : real) (s : real -> Prop) (x' : type1021) (h1 : term454 x') : term1066 x'' x' _68894 s.
Proof. exact (@lem5265658 x'' _68894 s x' h1). Qed.
Lemma lem5265662 (_68894 : real) (x' : type1021) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term145 s) (h3 : term909 s x'') (h4 : term258 s x'') : term775 x' _68894 s.
Proof. exact (@lem5265659 x'' _68894 s x' h1 (@lem5265656 s x'' h2 h3 h4)). Qed.
Lemma lem5265663 (B : real) (x' : type1021) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term145 s) (h3 : term909 s x'') (h4 : term258 s x'') : term1067 x' B s.
Proof. exact (@lem5265662 (real_neg B) x' s x'' h1 h2 h3 h4). Qed.
Lemma lem5265664 (B : real) (x' : type1021) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term145 s) (h3 : term909 s x'') (h4 : term258 s x'') : term1068 x' B s.
Proof. exact (fun h0 : term1069 x' B s => @lem5265663 B x' s x'' h1 h2 h3 h4). Qed.
Lemma lem5265666 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5265667 (x' : type1021) (B : real) (s : real -> Prop) : (term1068 x' B s) = (term1067 x' B s).
Proof. exact (@lem5265666 (term1067 x' B s)). Qed.
Lemma lem5265668 (B : real) (x' : type1021) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term145 s) (h3 : term909 s x'') (h4 : term258 s x'') : term1067 x' B s.
Proof. exact (EQ_MP (@lem5265667 x' B s) (@lem5265664 B x' s x'' h1 h2 h3 h4)). Qed.
Lemma lem5265674 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5265675 (B : real) (_68889 : real) (s : real -> Prop) : (term251 s _68889 B) = (term968 B _68889 s).
Proof. exact (@lem5265674 (term224 _68889 B) (term942 _68889 s)). Qed.
Lemma lem5265681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5265682 (B : real) (_68889 : real) (s : real -> Prop) : (term969 s _68889 B) = (term970 B _68889 s).
Proof. exact (MK_COMB (@lem5265681) (@lem5265675 B _68889 s)). Qed.
Lemma lem5265688 (B : real) (_68889 : real) (s : real -> Prop) : (term968 B _68889 s) = (term968 B _68889 s).
Proof. exact (eq_refl (term968 B _68889 s)). Qed.
Lemma lem5265689 (B : real) (_68889 : real) (s : real -> Prop) : ((term251 s _68889 B) = (term968 B _68889 s)) = ((term968 B _68889 s) = (term968 B _68889 s)).
Proof. exact (MK_COMB (@lem5265682 B _68889 s) (@lem5265688 B _68889 s)). Qed.
Lemma lem5265691 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5265692 (x : Prop) : (x = x) = True.
Proof. exact (@lem5265691 Prop x). Qed.
Lemma lem5265693 (B : real) (_68889 : real) (s : real -> Prop) : ((term968 B _68889 s) = (term968 B _68889 s)) = True.
Proof. exact (@lem5265692 (term968 B _68889 s)). Qed.
Lemma lem5265694 (B : real) (_68889 : real) (s : real -> Prop) : ((term251 s _68889 B) = (term968 B _68889 s)) = True.
Proof. exact (TRANS (@lem5265689 B _68889 s) (@lem5265693 B _68889 s)). Qed.
Lemma lem5265695 (B : real) (_68889 : real) (s : real -> Prop) : True = ((term251 s _68889 B) = (term968 B _68889 s)).
Proof. exact (SYM (@lem5265694 B _68889 s)). Qed.
Lemma lem5265696 (B : real) (_68889 : real) (s : real -> Prop) : (term251 s _68889 B) = (term968 B _68889 s).
Proof. exact (EQ_MP (@lem5265695 B _68889 s) (@lem0)). Qed.
Lemma lem5265697 (_68889 : real) (s : real -> Prop) (B : real) (h1 : term146 s B) : term968 B _68889 s.
Proof. exact (EQ_MP (@lem5265696 B _68889 s) (@lem5264350 _68889 s B h1)). Qed.
Lemma lem5265699 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5265700 (s : real -> Prop) (_68889 : real) (B : real) : (term968 B _68889 s) = (term971 s _68889 B).
Proof. exact (@lem5265699 (term942 _68889 s) (term224 _68889 B)). Qed.
Lemma lem5265702 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5265703 (_68889 : real) (s : real -> Prop) : (term959 _68889 s) = (@IN real _68889 s).
Proof. exact (@lem5265702 (@IN real _68889 s)). Qed.
Lemma lem5265704 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5265705 (_68889 : real) (s : real -> Prop) : (term972 _68889 s) = (term163 _68889 s).
Proof. exact (MK_COMB (@lem5265704) (@lem5265703 _68889 s)). Qed.
Lemma lem5265706 (_68889 : real) (B : real) : (term224 _68889 B) = (term224 _68889 B).
Proof. exact (eq_refl (term224 _68889 B)). Qed.
Lemma lem5265707 (s : real -> Prop) (_68889 : real) (B : real) : (term971 s _68889 B) = (term249 s _68889 B).
Proof. exact (MK_COMB (@lem5265705 _68889 s) (@lem5265706 _68889 B)). Qed.
Lemma lem5265708 (s : real -> Prop) (_68889 : real) (B : real) : (term968 B _68889 s) = (term249 s _68889 B).
Proof. exact (TRANS (@lem5265700 s _68889 B) (@lem5265707 s _68889 B)). Qed.
Lemma lem5265711 (_68889 : real) (s : real -> Prop) (B : real) (h1 : term146 s B) : term249 s _68889 B.
Proof. exact (EQ_MP (@lem5265708 s _68889 B) (@lem5265697 _68889 s B h1)). Qed.
Lemma lem5265712 (x' : type1021) (s : real -> Prop) (B : real) (h1 : term146 s B) : term1070 x' s B.
Proof. exact (@lem5265711 (term1071 x' s B) s B h1). Qed.
Lemma lem5265715 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term146 s B) (h3 : term145 s) (h4 : term909 s x'') (h5 : term258 s x'') : term1072 x' s B.
Proof. exact (@lem5265712 x' s B h2 (@lem5265668 B x' s x'' h1 h3 h4 h5)). Qed.
Lemma lem5265716 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term146 s B) (h3 : term145 s) (h4 : term909 s x'') (h5 : term258 s x'') : term1073 x' s B.
Proof. exact (fun h0 : term1074 x' s B => @lem5265715 x' B s x'' h1 h2 h3 h4 h5). Qed.
Lemma lem5265718 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5265719 (x' : type1021) (s : real -> Prop) (B : real) : (term1073 x' s B) = (term1072 x' s B).
Proof. exact (@lem5265718 (term1072 x' s B)). Qed.
Lemma lem5265720 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term146 s B) (h3 : term145 s) (h4 : term909 s x'') (h5 : term258 s x'') : term1072 x' s B.
Proof. exact (EQ_MP (@lem5265719 x' s B) (@lem5265716 x' B s x'' h1 h2 h3 h4 h5)). Qed.
Lemma lem5265726 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5265727 (_68898 : real) (_68899 : real) : (term926 _68899 _68898) = (term1075 _68898 _68899).
Proof. exact (@lem5265726 (term460 _68899 _68898) (term807 _68898 _68899)). Qed.
Lemma lem5265733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5265734 (_68898 : real) (_68899 : real) : (term1076 _68899 _68898) = (term1077 _68898 _68899).
Proof. exact (MK_COMB (@lem5265733) (@lem5265727 _68898 _68899)). Qed.
Lemma lem5265740 (_68898 : real) (_68899 : real) : (term1075 _68898 _68899) = (term1075 _68898 _68899).
Proof. exact (eq_refl (term1075 _68898 _68899)). Qed.
Lemma lem5265741 (_68898 : real) (_68899 : real) : ((term926 _68899 _68898) = (term1075 _68898 _68899)) = ((term1075 _68898 _68899) = (term1075 _68898 _68899)).
Proof. exact (MK_COMB (@lem5265734 _68898 _68899) (@lem5265740 _68898 _68899)). Qed.
Lemma lem5265743 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5265744 (x : Prop) : (x = x) = True.
Proof. exact (@lem5265743 Prop x). Qed.
Lemma lem5265745 (_68898 : real) (_68899 : real) : ((term1075 _68898 _68899) = (term1075 _68898 _68899)) = True.
Proof. exact (@lem5265744 (term1075 _68898 _68899)). Qed.
Lemma lem5265746 (_68898 : real) (_68899 : real) : ((term926 _68899 _68898) = (term1075 _68898 _68899)) = True.
Proof. exact (TRANS (@lem5265741 _68898 _68899) (@lem5265745 _68898 _68899)). Qed.
Lemma lem5265747 (_68898 : real) (_68899 : real) : True = ((term926 _68899 _68898) = (term1075 _68898 _68899)).
Proof. exact (SYM (@lem5265746 _68898 _68899)). Qed.
Lemma lem5265748 (_68898 : real) (_68899 : real) : (term926 _68899 _68898) = (term1075 _68898 _68899).
Proof. exact (EQ_MP (@lem5265747 _68898 _68899) (@lem0)). Qed.
Lemma lem5265749 (_68898 : real) (_68899 : real) (h1 : term229) : term1075 _68898 _68899.
Proof. exact (EQ_MP (@lem5265748 _68898 _68899) (@lem5264372 _68899 _68898 h1)). Qed.
Lemma lem5265751 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5265752 (_68899 : real) (_68898 : real) : (term1075 _68898 _68899) = (term1078 _68899 _68898).
Proof. exact (@lem5265751 (term807 _68898 _68899) (term460 _68899 _68898)). Qed.
Lemma lem5265754 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5265755 (_68898 : real) (_68899 : real) : (term981 _68898 _68899) = (term224 _68898 _68899).
Proof. exact (@lem5265754 (term224 _68898 _68899)). Qed.
Lemma lem5265756 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5265757 (_68898 : real) (_68899 : real) : (term982 _68898 _68899) = (term983 _68898 _68899).
Proof. exact (MK_COMB (@lem5265756) (@lem5265755 _68898 _68899)). Qed.
Lemma lem5265758 (_68899 : real) (_68898 : real) : (term460 _68899 _68898) = (term460 _68899 _68898).
Proof. exact (eq_refl (term460 _68899 _68898)). Qed.
Lemma lem5265759 (_68899 : real) (_68898 : real) : (term1078 _68899 _68898) = (term1079 _68899 _68898).
Proof. exact (MK_COMB (@lem5265757 _68898 _68899) (@lem5265758 _68899 _68898)). Qed.
Lemma lem5265760 (_68899 : real) (_68898 : real) : (term1075 _68898 _68899) = (term1079 _68899 _68898).
Proof. exact (TRANS (@lem5265752 _68899 _68898) (@lem5265759 _68899 _68898)). Qed.
Lemma lem5265763 (_68899 : real) (_68898 : real) (h1 : term229) : term1079 _68899 _68898.
Proof. exact (EQ_MP (@lem5265760 _68899 _68898) (@lem5265749 _68898 _68899 h1)). Qed.
Lemma lem5265764 (x' : type1021) (s : real -> Prop) (B : real) (h1 : term229) : term1080 x' s B.
Proof. exact (@lem5265763 B (term1071 x' s B) h1). Qed.
Lemma lem5265767 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : term1081 x' s B.
Proof. exact (@lem5265764 x' s B h2 (@lem5265720 x' B s x'' h1 h3 h4 h5 h6)). Qed.
Lemma lem5265768 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : term1082 x' s B.
Proof. exact (fun h0 : term1083 x' s B => @lem5265767 x' B s x'' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5265770 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5265771 (x' : type1021) (s : real -> Prop) (B : real) : (term1082 x' s B) = (term1081 x' s B).
Proof. exact (@lem5265770 (term1081 x' s B)). Qed.
Lemma lem5265772 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : term1081 x' s B.
Proof. exact (EQ_MP (@lem5265771 x' s B) (@lem5265768 x' B s x'' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5265774 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : @IN real x'' s.
Proof. exact (proj1 (@lem5263020 s x'' h1)). Qed.
Lemma lem5265775 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : term941 x'' s.
Proof. exact (fun h0 : term942 x'' s => @lem5265774 s x'' h1). Qed.
Lemma lem5265777 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5265778 (x'' : real) (s : real -> Prop) : (term941 x'' s) = (@IN real x'' s).
Proof. exact (@lem5265777 (@IN real x'' s)). Qed.
Lemma lem5265779 (s : real -> Prop) (x'' : real) (h1 : term258 s x'') : @IN real x'' s.
Proof. exact (EQ_MP (@lem5265778 x'' s) (@lem5265775 s x'' h1)). Qed.
Lemma lem5265797 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5265798 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) (_68895 : real) : (term1084 x' _68894 _68893 _68895) = (term1085 x' _68894 _68893 _68895).
Proof. exact (@lem5265797 (term942 _68895 _68893) (term880 x' _68893 _68894) (term161 _68893 _68895)). Qed.
Lemma lem5265812 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5265813 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1086 x' _68894 _68893 _68895) = (term1087 _68895 x' _68893 _68894).
Proof. exact (@lem5265812 (term161 _68893 _68895) (term880 x' _68893 _68894)). Qed.
Lemma lem5265819 (_68895 : real) (_68893 : real -> Prop) : (term992 _68895 _68893) = (term992 _68895 _68893).
Proof. exact (eq_refl (term992 _68895 _68893)). Qed.
Lemma lem5265820 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1085 x' _68894 _68893 _68895) = (term1088 _68895 x' _68893 _68894).
Proof. exact (MK_COMB (@lem5265819 _68895 _68893) (@lem5265813 _68895 x' _68893 _68894)). Qed.
Lemma lem5265824 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5265825 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1088 _68895 x' _68893 _68894) = (term1089 _68895 x' _68893 _68894).
Proof. exact (@lem5265824 (term161 _68893 _68895) (term942 _68895 _68893) (term880 x' _68893 _68894)). Qed.
Lemma lem5265841 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1085 x' _68894 _68893 _68895) = (term1089 _68895 x' _68893 _68894).
Proof. exact (TRANS (@lem5265820 _68895 x' _68893 _68894) (@lem5265825 _68895 x' _68893 _68894)). Qed.
Lemma lem5265842 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1084 x' _68894 _68893 _68895) = (term1089 _68895 x' _68893 _68894).
Proof. exact (TRANS (@lem5265798 x' _68894 _68893 _68895) (@lem5265841 _68895 x' _68893 _68894)). Qed.
Lemma lem5265843 (_68893 : real -> Prop) : (term288 _68893) = (term288 _68893).
Proof. exact (eq_refl (term288 _68893)). Qed.
Lemma lem5265844 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term928 x' _68894 _68893 _68895) = (term1090 _68895 x' _68893 _68894).
Proof. exact (MK_COMB (@lem5265843 _68893) (@lem5265842 _68895 x' _68893 _68894)). Qed.
Lemma lem5265855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5265856 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1091 x' _68894 _68893 _68895) = (term1092 _68895 x' _68893 _68894).
Proof. exact (MK_COMB (@lem5265855) (@lem5265844 _68895 x' _68893 _68894)). Qed.
Lemma lem5265860 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5265861 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1093 x' _68894 _68895 _68893) = (term1094 x' _68894 _68895 _68893).
Proof. exact (@lem5265860 (_68893 = (@EMPTY real)) (term161 _68893 _68895) (term1095 x' _68894 _68895 _68893)). Qed.
Lemma lem5265887 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5265888 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1095 x' _68894 _68895 _68893) = (term1096 _68895 x' _68893 _68894).
Proof. exact (@lem5265887 (term942 _68895 _68893) (term880 x' _68893 _68894)). Qed.
Lemma lem5265894 (_68893 : real -> Prop) (_68895 : real) : (term1097 _68893 _68895) = (term1097 _68893 _68895).
Proof. exact (eq_refl (term1097 _68893 _68895)). Qed.
Lemma lem5265895 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1098 x' _68894 _68895 _68893) = (term1089 _68895 x' _68893 _68894).
Proof. exact (MK_COMB (@lem5265894 _68893 _68895) (@lem5265888 _68895 x' _68893 _68894)). Qed.
Lemma lem5265906 (_68893 : real -> Prop) : (term288 _68893) = (term288 _68893).
Proof. exact (eq_refl (term288 _68893)). Qed.
Lemma lem5265907 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1094 x' _68894 _68895 _68893) = (term1090 _68895 x' _68893 _68894).
Proof. exact (MK_COMB (@lem5265906 _68893) (@lem5265895 _68895 x' _68893 _68894)). Qed.
Lemma lem5265918 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1093 x' _68894 _68895 _68893) = (term1090 _68895 x' _68893 _68894).
Proof. exact (TRANS (@lem5265861 x' _68894 _68895 _68893) (@lem5265907 _68895 x' _68893 _68894)). Qed.
Lemma lem5265919 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : ((term928 x' _68894 _68893 _68895) = (term1093 x' _68894 _68895 _68893)) = ((term1090 _68895 x' _68893 _68894) = (term1090 _68895 x' _68893 _68894)).
Proof. exact (MK_COMB (@lem5265856 _68895 x' _68893 _68894) (@lem5265918 _68895 x' _68893 _68894)). Qed.
Lemma lem5265921 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5265922 (x : Prop) : (x = x) = True.
Proof. exact (@lem5265921 Prop x). Qed.
Lemma lem5265923 (_68895 : real) (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : ((term1090 _68895 x' _68893 _68894) = (term1090 _68895 x' _68893 _68894)) = True.
Proof. exact (@lem5265922 (term1090 _68895 x' _68893 _68894)). Qed.
Lemma lem5265924 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : ((term928 x' _68894 _68893 _68895) = (term1093 x' _68894 _68895 _68893)) = True.
Proof. exact (TRANS (@lem5265919 _68895 x' _68893 _68894) (@lem5265923 _68895 x' _68893 _68894)). Qed.
Lemma lem5265925 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : True = ((term928 x' _68894 _68893 _68895) = (term1093 x' _68894 _68895 _68893)).
Proof. exact (SYM (@lem5265924 x' _68894 _68895 _68893)). Qed.
Lemma lem5265926 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term928 x' _68894 _68893 _68895) = (term1093 x' _68894 _68895 _68893).
Proof. exact (EQ_MP (@lem5265925 x' _68894 _68895 _68893) (@lem0)). Qed.
Lemma lem5265927 (_68894 : real) (_68895 : real) (_68893 : real -> Prop) (x' : type1021) (h1 : term454 x') : term1093 x' _68894 _68895 _68893.
Proof. exact (EQ_MP (@lem5265926 x' _68894 _68895 _68893) (@lem5264474 _68894 _68893 _68895 x' h1)). Qed.
Lemma lem5265929 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5265930 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) (_68895 : real) : (term1093 x' _68894 _68895 _68893) = (term1099 x' _68894 _68893 _68895).
Proof. exact (@lem5265929 (term1100 x' _68894 _68895 _68893) (term161 _68893 _68895)). Qed.
Lemma lem5265932 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5265933 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1101 x' _68894 _68895 _68893) = (term1102 x' _68894 _68895 _68893).
Proof. exact (@lem5265932 (_68893 = (@EMPTY real)) (term1095 x' _68894 _68895 _68893)). Qed.
Lemma lem5265935 (a : Prop) (b : Prop) : (term126 a b) = (term127 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5265936 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1103 x' _68894 _68895 _68893) = (term1104 x' _68894 _68895 _68893).
Proof. exact (@lem5265935 (term880 x' _68893 _68894) (term942 _68895 _68893)). Qed.
Lemma lem5265938 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5265939 (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1105 x' _68893 _68894) = (term1106 x' _68893 _68894).
Proof. exact (@lem5265938 (term1106 x' _68893 _68894)). Qed.
Lemma lem5265940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5265941 (x' : type1021) (_68893 : real -> Prop) (_68894 : real) : (term1107 x' _68893 _68894) = (term1108 x' _68893 _68894).
Proof. exact (MK_COMB (@lem5265940) (@lem5265939 x' _68893 _68894)). Qed.
Lemma lem5265943 (a : Prop) : (term64 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5265944 (_68895 : real) (_68893 : real -> Prop) : (term959 _68895 _68893) = (@IN real _68895 _68893).
Proof. exact (@lem5265943 (@IN real _68895 _68893)). Qed.
Lemma lem5265945 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1104 x' _68894 _68895 _68893) = (term1109 x' _68894 _68895 _68893).
Proof. exact (MK_COMB (@lem5265941 x' _68893 _68894) (@lem5265944 _68895 _68893)). Qed.
Lemma lem5265946 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1103 x' _68894 _68895 _68893) = (term1109 x' _68894 _68895 _68893).
Proof. exact (TRANS (@lem5265936 x' _68894 _68895 _68893) (@lem5265945 x' _68894 _68895 _68893)). Qed.
Lemma lem5265947 (_68893 : real -> Prop) : (term152 _68893) = (term152 _68893).
Proof. exact (eq_refl (term152 _68893)). Qed.
Lemma lem5265948 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1102 x' _68894 _68895 _68893) = (term1110 x' _68894 _68895 _68893).
Proof. exact (MK_COMB (@lem5265947 _68893) (@lem5265946 x' _68894 _68895 _68893)). Qed.
Lemma lem5265949 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1101 x' _68894 _68895 _68893) = (term1110 x' _68894 _68895 _68893).
Proof. exact (TRANS (@lem5265933 x' _68894 _68895 _68893) (@lem5265948 x' _68894 _68895 _68893)). Qed.
Lemma lem5265950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5265951 (x' : type1021) (_68894 : real) (_68895 : real) (_68893 : real -> Prop) : (term1111 x' _68894 _68895 _68893) = (term1112 x' _68894 _68895 _68893).
Proof. exact (MK_COMB (@lem5265950) (@lem5265949 x' _68894 _68895 _68893)). Qed.
Lemma lem5265952 (_68893 : real -> Prop) (_68895 : real) : (term161 _68893 _68895) = (term161 _68893 _68895).
Proof. exact (eq_refl (term161 _68893 _68895)). Qed.
Lemma lem5265953 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) (_68895 : real) : (term1099 x' _68894 _68893 _68895) = (term1113 x' _68894 _68893 _68895).
Proof. exact (MK_COMB (@lem5265951 x' _68894 _68895 _68893) (@lem5265952 _68893 _68895)). Qed.
Lemma lem5265954 (x' : type1021) (_68894 : real) (_68893 : real -> Prop) (_68895 : real) : (term1093 x' _68894 _68895 _68893) = (term1113 x' _68894 _68893 _68895).
Proof. exact (TRANS (@lem5265930 x' _68894 _68893 _68895) (@lem5265953 x' _68894 _68893 _68895)). Qed.
Lemma lem5265956 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : term1114 x' B x'' s.
Proof. exact (conj (@lem5265772 x' B s x'' h1 h2 h3 h4 h5 h6) (@lem5265779 s x'' h6)). Qed.
Lemma lem5265957 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : term1115 x' B x'' s.
Proof. exact (conj (@lem5265475 s h4) (@lem5265956 x' B s x'' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5265959 (_68894 : real) (_68893 : real -> Prop) (_68895 : real) (x' : type1021) (h1 : term454 x') : term1113 x' _68894 _68893 _68895.
Proof. exact (EQ_MP (@lem5265954 x' _68894 _68893 _68895) (@lem5265927 _68894 _68895 _68893 x' h1)). Qed.
Lemma lem5265960 (B : real) (s : real -> Prop) (x'' : real) (x' : type1021) (h1 : term454 x') : term1116 x' B s x''.
Proof. exact (@lem5265959 (real_neg B) s x'' x' h1). Qed.
Lemma lem5265963 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : term161 s x''.
Proof. exact (@lem5265960 B s x'' x' h1 (@lem5265957 x' B s x'' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5265964 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term258 s x'') : term1117 s x''.
Proof. exact (fun h0 : term909 s x'' => @lem5265963 x' B s x'' h1 h2 h3 h4 h0 h5). Qed.
Lemma lem5265966 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5265967 (s : real -> Prop) (x'' : real) : (term1117 s x'') = (term161 s x'').
Proof. exact (@lem5265966 (term161 s x'')). Qed.
Lemma lem5265968 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term258 s x'') : term161 s x''.
Proof. exact (EQ_MP (@lem5265967 s x'') (@lem5265964 x' B s x'' h1 h2 h3 h4 h5)). Qed.
Lemma lem5265971 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5265973 (s : real -> Prop) (x'' : real) : (term909 s x'') = (term1118 s x'').
Proof. exact (@lem5265971 (term161 s x'')). Qed.
Lemma lem5265976 (s : real -> Prop) (x'' : real) (h1 : term909 s x'') : term1118 s x''.
Proof. exact (EQ_MP (@lem5265973 s x'') (@lem5264366 s x'' h1)). Qed.
Lemma lem5265979 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : False.
Proof. exact (@lem5265976 s x'' h5 (@lem5265968 x' B s x'' h1 h2 h3 h4 h6)). Qed.
Lemma lem5265980 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : term111.
Proof. exact (fun h0 : ~ False => @lem5265979 x' B s x'' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5265982 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5265983 : term111 = False.
Proof. exact (@lem5265982 False). Qed.
Lemma lem5265984 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : False.
Proof. exact (EQ_MP (@lem5265983) (@lem5265980 x' B s x'' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5265985 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : (term909 s x'') = False.
Proof. exact (prop_ext (fun h7 : term909 s x'' => @lem5265984 x' B s x'' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5264366 s x'' h5)). Qed.
Lemma lem5265986 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : False.
Proof. exact (EQ_MP (@lem5265985 x' B s x'' h1 h2 h3 h4 h5 h6) (@lem5264366 s x'' h5)). Qed.
Lemma lem5265987 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : (term145 s) = False.
Proof. exact (prop_ext (fun h7 : term145 s => @lem5265986 x' B s x'' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5264344 s h4)). Qed.
Lemma lem5265988 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : False.
Proof. exact (EQ_MP (@lem5265987 x' B s x'' h1 h2 h3 h4 h5 h6) (@lem5264344 s h4)). Qed.
Lemma lem5265989 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : (term812 x'' s) = False.
Proof. exact (prop_ext (fun h8 : term812 x'' s => @lem5265364 x B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5264138 x'' s h5)). Qed.
Lemma lem5265990 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5265989 x B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5264138 x'' s h5)). Qed.
Lemma lem5265991 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : ((sup s) = (inf s)) = False.
Proof. exact (prop_ext (fun h8 : (sup s) = (inf s) => @lem5265990 x B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5264124 s h7)). Qed.
Lemma lem5265992 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5265991 x B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5264124 s h7)). Qed.
Lemma lem5265993 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : (term145 s) = False.
Proof. exact (prop_ext (fun h8 : term145 s => @lem5265992 x B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5264116 s h4)). Qed.
Lemma lem5265994 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5265993 x B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5264116 s h4)). Qed.
Lemma lem5265995 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : (term909 s x'') = False.
Proof. exact (prop_ext (fun h7 : term909 s x'' => @lem5265988 x' B s x'' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5264004 s x'' h5)). Qed.
Lemma lem5265996 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : False.
Proof. exact (EQ_MP (@lem5265995 x' B s x'' h1 h2 h3 h4 h5 h6) (@lem5264004 s x'' h5)). Qed.
Lemma lem5265997 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : (term145 s) = False.
Proof. exact (prop_ext (fun h7 : term145 s => @lem5265996 x' B s x'' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5263519 s h4)). Qed.
Lemma lem5265998 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : False.
Proof. exact (EQ_MP (@lem5265997 x' B s x'' h1 h2 h3 h4 h5 h6) (@lem5263519 s h4)). Qed.
Lemma lem5265999 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : (term812 x'' s) = False.
Proof. exact (prop_ext (fun h8 : term812 x'' s => @lem5265994 x B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5263515 x'' s h5)). Qed.
Lemma lem5266000 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5265999 x B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5263515 x'' s h5)). Qed.
Lemma lem5266001 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : ((sup s) = (inf s)) = False.
Proof. exact (prop_ext (fun h8 : (sup s) = (inf s) => @lem5266000 x B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5263047 s h7)). Qed.
Lemma lem5266002 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266001 x B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5263047 s h7)). Qed.
Lemma lem5266003 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : (term145 s) = False.
Proof. exact (prop_ext (fun h8 : term145 s => @lem5266002 x B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5263030 s h4)). Qed.
Lemma lem5266004 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266003 x B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5263030 s h4)). Qed.
Lemma lem5266005 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : (term909 s x'') = False.
Proof. exact (prop_ext (fun h7 : term909 s x'' => @lem5265998 x' B s x'' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5264004 s x'' h5)). Qed.
Lemma lem5266006 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : False.
Proof. exact (EQ_MP (@lem5266005 x' B s x'' h1 h2 h3 h4 h5 h6) (@lem5264004 s x'' h5)). Qed.
Lemma lem5266007 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : (term145 s) = False.
Proof. exact (prop_ext (fun h7 : term145 s => @lem5266006 x' B s x'' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5263519 s h4)). Qed.
Lemma lem5266008 (x' : type1021) (B : real) (s : real -> Prop) (x'' : real) (h1 : term454 x') (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term909 s x'') (h6 : term258 s x'') : False.
Proof. exact (EQ_MP (@lem5266007 x' B s x'' h1 h2 h3 h4 h5 h6) (@lem5263519 s h4)). Qed.
Lemma lem5266009 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : (term812 x'' s) = False.
Proof. exact (prop_ext (fun h8 : term812 x'' s => @lem5266004 x B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5263515 x'' s h5)). Qed.
Lemma lem5266010 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266009 x B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5263515 x'' s h5)). Qed.
Lemma lem5266011 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : ((sup s) = (inf s)) = False.
Proof. exact (prop_ext (fun h8 : (sup s) = (inf s) => @lem5266010 x B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5263047 s h7)). Qed.
Lemma lem5266012 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266011 x B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5263047 s h7)). Qed.
Lemma lem5266013 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : (term145 s) = False.
Proof. exact (prop_ext (fun h8 : term145 s => @lem5266012 x B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5263030 s h4)). Qed.
Lemma lem5266014 (x : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term229) (h3 : term146 s B) (h4 : term145 s) (h5 : term812 x'' s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266013 x B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5263030 s h4)). Qed.
Lemma lem5266015 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (or_elim (@lem5263021 s x'' h6) (fun h0 : term812 x'' s => @lem5266014 x B x'' s h1 h3 h4 h5 h0 h6 h7) (fun h0 : term909 s x'' => @lem5266008 x' B s x'' h2 h3 h4 h5 h0 h6)). Qed.
Lemma lem5266016 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : (term258 s x'') = False.
Proof. exact (prop_ext (fun h8 : term258 s x'' => @lem5266015 x x' B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5263020 s x'' h6)). Qed.
Lemma lem5266017 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266016 x x' B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5263020 s x'' h6)). Qed.
Lemma lem5266018 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : (term454 x') = False.
Proof. exact (prop_ext (fun h8 : term454 x' => @lem5266017 x x' B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5262990 x' h2)). Qed.
Lemma lem5266019 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266018 x x' B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5262990 x' h2)). Qed.
Lemma lem5266020 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : (term678 x) = False.
Proof. exact (prop_ext (fun h8 : term678 x => @lem5266019 x x' B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5262890 x h1)). Qed.
Lemma lem5266021 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266020 x x' B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5262890 x h1)). Qed.
Lemma lem5266022 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : ((sup s) = (inf s)) = False.
Proof. exact (prop_ext (fun h8 : (sup s) = (inf s) => @lem5266021 x x' B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5262718 s h7)). Qed.
Lemma lem5266023 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266022 x x' B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5262718 s h7)). Qed.
Lemma lem5266024 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : (term145 s) = False.
Proof. exact (prop_ext (fun h8 : term145 s => @lem5266023 x x' B x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5262687 s h5)). Qed.
Lemma lem5266025 (x : type1021) (x' : type1021) (B : real) (x'' : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term145 s) (h6 : term258 s x'') (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266024 x x' B x'' s h1 h2 h3 h4 h5 h6 h7) (@lem5262687 s h5)). Qed.
Lemma lem5266026 (x : type1021) (x' : type1021) (B : real) (s : real -> Prop) (h1 : term678 x) (h2 : term454 x') (h3 : term229) (h4 : term146 s B) (h5 : term173 s) (h6 : term145 s) (h7 : (sup s) = (inf s)) : False.
Proof. exact (ex_elim (@lem5261321 s h5) (fun x'' : real => fun h0 : term266 s x'' => @lem5266025 x x' B x'' s h1 h2 h3 h4 h6 h0 h7)). Qed.
Lemma lem5266027 (x : type1021) (B : real) (s : real -> Prop) (h1 : term248) (h2 : term678 x) (h3 : term229) (h4 : term146 s B) (h5 : term173 s) (h6 : term145 s) (h7 : (sup s) = (inf s)) : False.
Proof. exact (ex_elim (@lem5261850 h1) (fun x' : type1021 => fun h0 : term456 x' => @lem5266026 x x' B s h2 h0 h3 h4 h5 h6 h7)). Qed.
Lemma lem5266028 (B : real) (s : real -> Prop) (h1 : term180) (h2 : term248) (h3 : term229) (h4 : term146 s B) (h5 : term173 s) (h6 : term145 s) (h7 : (sup s) = (inf s)) : False.
Proof. exact (ex_elim (@lem5262676 h1) (fun x : type1021 => fun h0 : term680 x => @lem5266027 x B s h2 h0 h3 h4 h5 h6 h7)). Qed.
Lemma lem5266029 (B : real) (s : real -> Prop) (h1 : term180) (h2 : term248) (h3 : term229) (h4 : term146 s B) (h5 : term173 s) (h6 : term145 s) (h7 : (sup s) = (inf s)) : ((sup s) = (inf s)) = False.
Proof. exact (prop_ext (fun h8 : (sup s) = (inf s) => @lem5266028 B s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5261245 s h7)). Qed.
Lemma lem5266030 (B : real) (s : real -> Prop) (h1 : term180) (h2 : term248) (h3 : term229) (h4 : term146 s B) (h5 : term173 s) (h6 : term145 s) (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266029 B s h1 h2 h3 h4 h5 h6 h7) (@lem5261245 s h7)). Qed.
Lemma lem5266031 (B : real) (s : real -> Prop) (h1 : term180) (h2 : term248) (h3 : term229) (h4 : term146 s B) (h5 : term173 s) (h6 : term145 s) (h7 : (sup s) = (inf s)) : (term145 s) = False.
Proof. exact (prop_ext (fun h8 : term145 s => @lem5266030 B s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5261176 s h6)). Qed.
Lemma lem5266032 (B : real) (s : real -> Prop) (h1 : term180) (h2 : term248) (h3 : term229) (h4 : term146 s B) (h5 : term173 s) (h6 : term145 s) (h7 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266031 B s h1 h2 h3 h4 h5 h6 h7) (@lem5261176 s h6)). Qed.
Lemma lem5266033 (B : real) (s : real -> Prop) (h1 : term248) (h2 : term229) (h3 : term146 s B) (h4 : term173 s) (h5 : term145 s) (h6 : (sup s) = (inf s)) : term178.
Proof. exact (fun h0 : term180 => @lem5266032 B s h0 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5266034 : term178 = term179.
Proof. exact (@lem69 term180). Qed.
Lemma lem5266035 (B : real) (s : real -> Prop) (h1 : term248) (h2 : term229) (h3 : term146 s B) (h4 : term173 s) (h5 : term145 s) (h6 : (sup s) = (inf s)) : term179.
Proof. exact (EQ_MP (@lem5266034) (@lem5266033 B s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5266036 (B : real) (s : real -> Prop) (h1 : term248) (h2 : term146 s B) (h3 : term173 s) (h4 : term145 s) (h5 : (sup s) = (inf s)) : term183.
Proof. exact (fun h0 : term229 => @lem5266035 B s h1 h0 h2 h3 h4 h5). Qed.
Lemma lem5266037 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term173 s) (h3 : term145 s) (h4 : (sup s) = (inf s)) : term186.
Proof. exact (fun h0 : term248 => @lem5266036 B s h0 h1 h2 h3 h4). Qed.
Lemma lem5266038 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) (h3 : (sup s) = (inf s)) : term189 s.
Proof. exact (fun h0 : term173 s => @lem5266037 B s h1 h0 h2 h3). Qed.
Lemma lem5266039 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) : term192 s.
Proof. exact (fun h0 : (sup s) = (inf s) => @lem5266038 B s h1 h2 h0). Qed.
Lemma lem5266040 (B : real) (s : real -> Prop) (h1 : term145 s) : term195 B s.
Proof. exact (fun h0 : term146 s B => @lem5266039 B s h0 h1). Qed.
Lemma lem5266041 (B : real) (s : real -> Prop) : term197 B s.
Proof. exact (fun h0 : term145 s => @lem5266040 B s h0). Qed.
Lemma lem5266046 (s : real -> Prop) : term201 s.
Proof. exact (fun B : real => @lem5266041 B s). Qed.
Lemma lem5266051 : term205.
Proof. exact (fun s : real -> Prop => @lem5266046 s). Qed.
Lemma lem5266052 : term204.
Proof. exact (EQ_MP (@lem5261163) (@lem5266051)). Qed.
Lemma lem5266053 (s : real -> Prop) : term1119 s.
Proof. exact (@lem5266052 s). Qed.
Lemma lem5266054 (s : real -> Prop) : (term1119 s) = (term200 s).
Proof. exact (eq_refl (term1119 s)). Qed.
Lemma lem5266055 (s : real -> Prop) : term200 s.
Proof. exact (EQ_MP (@lem5266054 s) (@lem5266053 s)). Qed.
Lemma lem5266056 (s : real -> Prop) (B : real) : term1120 s B.
Proof. exact (@lem5266055 s B). Qed.
Lemma lem5266057 (B : real) (s : real -> Prop) : (term1120 s B) = (term174 B s).
Proof. exact (eq_refl (term1120 s B)). Qed.
Lemma lem5266058 (B : real) (s : real -> Prop) : term174 B s.
Proof. exact (EQ_MP (@lem5266057 B s) (@lem5266056 s B)). Qed.
Lemma lem5266060 (B : real) (s : real -> Prop) : term174 B s.
Proof. exact (@lem5260673 B s (@lem5266058 B s)). Qed.
Lemma lem5266061 (B : real) (s : real -> Prop) (h1 : term145 s) : term194 B s.
Proof. exact (@lem5266060 B s (@lem5260558 s h1)). Qed.
Lemma lem5266062 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) : term191 s.
Proof. exact (@lem5266061 B s h2 (@lem5260559 s B h1)). Qed.
Lemma lem5266063 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) (h3 : (sup s) = (inf s)) : term188 s.
Proof. exact (@lem5266062 B s h1 h2 (@lem5260560 s h3)). Qed.
Lemma lem5266064 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term173 s) (h3 : term145 s) (h4 : (sup s) = (inf s)) : term185.
Proof. exact (@lem5266063 B s h1 h3 h4 (@lem5260658 s h2)). Qed.
Lemma lem5266065 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term173 s) (h3 : term145 s) (h4 : (sup s) = (inf s)) : term182.
Proof. exact (@lem5266064 B s h1 h2 h3 h4 (@lem5214027)). Qed.
Lemma lem5266066 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term173 s) (h3 : term145 s) (h4 : (sup s) = (inf s)) : term178.
Proof. exact (@lem5266065 B s h1 h2 h3 h4 (@lem1552321)). Qed.
Lemma lem5266067 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term173 s) (h3 : term145 s) (h4 : (sup s) = (inf s)) : False.
Proof. exact (@lem5266066 B s h1 h2 h3 h4 (@lem5136700)). Qed.
Lemma lem5266068 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term173 s) (h3 : term145 s) (h4 : (sup s) = (inf s)) : (term173 s) = False.
Proof. exact (prop_ext (fun h5 : term173 s => @lem5266067 B s h1 h2 h3 h4) (fun h5 : False => @lem5260658 s h2)). Qed.
Lemma lem5266069 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term173 s) (h3 : term145 s) (h4 : (sup s) = (inf s)) : False.
Proof. exact (EQ_MP (@lem5266068 B s h1 h2 h3 h4) (@lem5260658 s h2)). Qed.
Lemma lem5266070 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) (h3 : (sup s) = (inf s)) : term172 s.
Proof. exact (fun h0 : term173 s => @lem5266069 B s h1 h0 h2 h3). Qed.
Lemma lem5266071 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) (h3 : (sup s) = (inf s)) : term169 s.
Proof. exact (EQ_MP (@lem5260657 s) (@lem5266070 B s h1 h2 h3)). Qed.
Lemma lem5266072 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) (h3 : (sup s) = (inf s)) : term170 s.
Proof. exact (EQ_MP (@lem5260653 s h2 h3) (@lem5266071 B s h1 h2 h3)). Qed.
Lemma lem5266073 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) (h3 : (sup s) = (inf s)) : s = (term1121 s).
Proof. exact (@lem5260564 s (@lem5266072 B s h1 h2 h3)). Qed.
Lemma lem5266074 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) (h3 : (sup s) = (inf s)) : term1122 s.
Proof. exact (ex_intro (term1123 s) (sup s) (@lem5266073 B s h1 h2 h3)). Qed.
Lemma lem5266075 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) : term1124 s.
Proof. exact (fun h0 : (sup s) = (inf s) => @lem5266074 B s h1 h2 h0). Qed.
Lemma lem5266076 (s : real -> Prop) (h1 : term1122 s) : term1122 s.
Proof. exact (h1). Qed.
Lemma lem5266077 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : s = (@INSERT real a (@EMPTY real)).
Proof. exact (h1). Qed.
Lemma lem5266078 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem5266080 (x : real) : term1125 x.
Proof. exact (@lem5256773 x). Qed.
Lemma lem5266081 (x : real) : (term1125 x) = (term1126 x).
Proof. exact (eq_refl (term1125 x)). Qed.
Lemma lem5266082 (x : real) : term1126 x.
Proof. exact (EQ_MP (@lem5266081 x) (@lem5266080 x)). Qed.
Lemma lem5266083 (x : real) (s : real -> Prop) : term1127 x s.
Proof. exact (@lem5266082 x s). Qed.
Lemma lem5266084 (x : real) (s : real -> Prop) : (term1127 x s) = (term1128 x s).
Proof. exact (eq_refl (term1127 x s)). Qed.
Lemma lem5266085 (x : real) (s : real -> Prop) : term1128 x s.
Proof. exact (EQ_MP (@lem5266084 x s) (@lem5266083 x s)). Qed.
Lemma lem5266086 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5266087 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term1129 x s) = (term1130 x s).
Proof. exact (@lem5266085 x s (@lem5266086 s h1)). Qed.
Lemma lem5266093 (x : real) : term1131 x.
Proof. exact (@lem5178187 x). Qed.
Lemma lem5266094 (x : real) : (term1131 x) = (term1132 x).
Proof. exact (eq_refl (term1131 x)). Qed.
Lemma lem5266095 (x : real) : term1132 x.
Proof. exact (EQ_MP (@lem5266094 x) (@lem5266093 x)). Qed.
Lemma lem5266096 (x : real) (s : real -> Prop) : term1133 x s.
Proof. exact (@lem5266095 x s). Qed.
Lemma lem5266097 (x : real) (s : real -> Prop) : (term1133 x s) = (term1134 x s).
Proof. exact (eq_refl (term1133 x s)). Qed.
Lemma lem5266098 (x : real) (s : real -> Prop) : term1134 x s.
Proof. exact (EQ_MP (@lem5266097 x s) (@lem5266096 x s)). Qed.
Lemma lem5266099 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5266100 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term1135 x s) = (term1136 x s).
Proof. exact (@lem5266098 x s (@lem5266099 s h1)). Qed.
Lemma lem5266134 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : s = (@INSERT real a (@EMPTY real)).
Proof. exact (h1). Qed.
Lemma lem5266135 : sup = sup.
Proof. exact (eq_refl sup). Qed.
Lemma lem5266136 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : (sup s) = (term1137 a).
Proof. exact (MK_COMB (@lem5266135) (@lem5266134 s a h1)). Qed.
Lemma lem5266138 (x : real) (s : real -> Prop) : term1134 x s.
Proof. exact (fun h0 : @FINITE real s => @lem5266100 x s h0). Qed.
Lemma lem5266139 (a : real) : term1138 a.
Proof. exact (@lem5266138 a (@EMPTY real)). Qed.
Lemma lem5266141 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem5266078 _92140) (@lem3596285 _92140)). Qed.
Lemma lem5266142 : (@FINITE real (@EMPTY real)) = True.
Proof. exact (@lem5266141 real). Qed.
Lemma lem5266143 : True = (@FINITE real (@EMPTY real)).
Proof. exact (SYM (@lem5266142)). Qed.
Lemma lem5266144 : @FINITE real (@EMPTY real).
Proof. exact (EQ_MP (@lem5266143) (@lem0)). Qed.
Lemma lem5266145 (a : real) : (term1137 a) = (term1139 a).
Proof. exact (@lem5266139 a (@lem5266144)). Qed.
Lemma lem5266147 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term1140 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem5266148 (x : real -> Prop) (z : real) (y : real) : (term1141 x y z) = y.
Proof. exact (@lem5266147 real (real -> Prop) x z y). Qed.
Lemma lem5266149 (a : real) : (term1139 a) = a.
Proof. exact (@lem5266148 (@EMPTY real) (term1142 a) a). Qed.
Lemma lem5266150 (a : real) : (term1137 a) = a.
Proof. exact (TRANS (@lem5266145 a) (@lem5266149 a)). Qed.
Lemma lem5266151 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : (sup s) = a.
Proof. exact (TRANS (@lem5266136 s a h1) (@lem5266150 a)). Qed.
Lemma lem5266152 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5266153 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : (term1143 s) = (@eq real a).
Proof. exact (MK_COMB (@lem5266152) (@lem5266151 s a h1)). Qed.
Lemma lem5266155 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : s = (@INSERT real a (@EMPTY real)).
Proof. exact (h1). Qed.
Lemma lem5266156 : inf = inf.
Proof. exact (eq_refl inf). Qed.
Lemma lem5266157 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : (inf s) = (term1144 a).
Proof. exact (MK_COMB (@lem5266156) (@lem5266155 s a h1)). Qed.
Lemma lem5266159 (x : real) (s : real -> Prop) : term1128 x s.
Proof. exact (fun h0 : @FINITE real s => @lem5266087 x s h0). Qed.
Lemma lem5266160 (a : real) : term1145 a.
Proof. exact (@lem5266159 a (@EMPTY real)). Qed.
Lemma lem5266162 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem5266078 _92140) (@lem3596285 _92140)). Qed.
Lemma lem5266163 : (@FINITE real (@EMPTY real)) = True.
Proof. exact (@lem5266162 real). Qed.
Lemma lem5266164 : True = (@FINITE real (@EMPTY real)).
Proof. exact (SYM (@lem5266163)). Qed.
Lemma lem5266165 : @FINITE real (@EMPTY real).
Proof. exact (EQ_MP (@lem5266164) (@lem0)). Qed.
Lemma lem5266166 (a : real) : (term1144 a) = (term1146 a).
Proof. exact (@lem5266160 a (@lem5266165)). Qed.
Lemma lem5266168 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term1140 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem5266169 (x : real -> Prop) (z : real) (y : real) : (term1141 x y z) = y.
Proof. exact (@lem5266168 real (real -> Prop) x z y). Qed.
Lemma lem5266170 (a : real) : (term1146 a) = a.
Proof. exact (@lem5266169 (@EMPTY real) (term1147 a) a). Qed.
Lemma lem5266171 (a : real) : (term1144 a) = a.
Proof. exact (TRANS (@lem5266166 a) (@lem5266170 a)). Qed.
Lemma lem5266172 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : (inf s) = a.
Proof. exact (TRANS (@lem5266157 s a h1) (@lem5266171 a)). Qed.
Lemma lem5266173 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : ((sup s) = (inf s)) = (a = a).
Proof. exact (MK_COMB (@lem5266153 s a h1) (@lem5266172 s a h1)). Qed.
Lemma lem5266175 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5266176 (x : real) : (x = x) = True.
Proof. exact (@lem5266175 real x). Qed.
Lemma lem5266177 (a : real) : (a = a) = True.
Proof. exact (@lem5266176 a). Qed.
Lemma lem5266178 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : ((sup s) = (inf s)) = True.
Proof. exact (TRANS (@lem5266173 s a h1) (@lem5266177 a)). Qed.
Lemma lem5266179 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : True = ((sup s) = (inf s)).
Proof. exact (SYM (@lem5266178 s a h1)). Qed.
Lemma lem5266180 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : (sup s) = (inf s).
Proof. exact (EQ_MP (@lem5266179 s a h1) (@lem0)). Qed.
Lemma lem5266181 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : (s = (@INSERT real a (@EMPTY real))) = ((sup s) = (inf s)).
Proof. exact (prop_ext (fun h2 : s = (@INSERT real a (@EMPTY real)) => @lem5266180 s a h1) (fun h2 : (sup s) = (inf s) => @lem5266077 s a h1)). Qed.
Lemma lem5266182 (s : real -> Prop) (a : real) (h1 : s = (@INSERT real a (@EMPTY real))) : (sup s) = (inf s).
Proof. exact (EQ_MP (@lem5266181 s a h1) (@lem5266077 s a h1)). Qed.
Lemma lem5266183 (s : real -> Prop) (h1 : term1122 s) : (sup s) = (inf s).
Proof. exact (ex_elim (@lem5266076 s h1) (fun a : real => fun h0 : term1123 s a => @lem5266182 s a h0)). Qed.
Lemma lem5266184 (s : real -> Prop) : term1148 s.
Proof. exact (fun h0 : term1122 s => @lem5266183 s h0). Qed.
Lemma lem5266185 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) : term1149 s.
Proof. exact (conj (@lem5266075 B s h1 h2) (@lem5266184 s)). Qed.
Lemma lem5266186 (s : real -> Prop) : (term1149 s) = (((sup s) = (inf s)) = (term1122 s)).
Proof. exact (@lem32 ((sup s) = (inf s)) (term1122 s)). Qed.
Lemma lem5266187 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) : ((sup s) = (inf s)) = (term1122 s).
Proof. exact (EQ_MP (@lem5266186 s) (@lem5266185 B s h1 h2)). Qed.
Lemma lem5266188 (s : real -> Prop) (h1 : term143 s) : term144 s.
Proof. exact (proj2 (@lem5260556 s h1)). Qed.
Lemma lem5266189 (s : real -> Prop) (h1 : term143 s) : term145 s.
Proof. exact (proj1 (@lem5260556 s h1)). Qed.
Lemma lem5266190 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) : (term146 s B) = (((sup s) = (inf s)) = (term1122 s)).
Proof. exact (prop_ext (fun h3 : term146 s B => @lem5266187 B s h1 h2) (fun h3 : ((sup s) = (inf s)) = (term1122 s) => @lem5260559 s B h1)). Qed.
Lemma lem5266191 (B : real) (s : real -> Prop) (h1 : term146 s B) (h2 : term145 s) : ((sup s) = (inf s)) = (term1122 s).
Proof. exact (EQ_MP (@lem5266190 B s h1 h2) (@lem5260559 s B h1)). Qed.
Lemma lem5266192 (s : real -> Prop) (h1 : term144 s) (h2 : term145 s) : ((sup s) = (inf s)) = (term1122 s).
Proof. exact (ex_elim (@lem5260557 s h1) (fun B : real => fun h0 : term1150 s B => @lem5266191 B s h0 h2)). Qed.
Lemma lem5266193 (s : real -> Prop) (h1 : term144 s) (h2 : term145 s) : (term145 s) = (((sup s) = (inf s)) = (term1122 s)).
Proof. exact (prop_ext (fun h3 : term145 s => @lem5266192 s h1 h2) (fun h3 : ((sup s) = (inf s)) = (term1122 s) => @lem5260558 s h2)). Qed.
Lemma lem5266194 (s : real -> Prop) (h1 : term144 s) (h2 : term145 s) : ((sup s) = (inf s)) = (term1122 s).
Proof. exact (EQ_MP (@lem5266193 s h1 h2) (@lem5260558 s h2)). Qed.
Lemma lem5266195 (s : real -> Prop) (h1 : term145 s) (h2 : term143 s) : (term144 s) = (((sup s) = (inf s)) = (term1122 s)).
Proof. exact (prop_ext (fun h3 : term144 s => @lem5266194 s h3 h1) (fun h3 : ((sup s) = (inf s)) = (term1122 s) => @lem5266188 s h2)). Qed.
Lemma lem5266196 (s : real -> Prop) (h1 : term145 s) (h2 : term143 s) : ((sup s) = (inf s)) = (term1122 s).
Proof. exact (EQ_MP (@lem5266195 s h1 h2) (@lem5266188 s h2)). Qed.
Lemma lem5266197 (s : real -> Prop) (h1 : term143 s) : (term145 s) = (((sup s) = (inf s)) = (term1122 s)).
Proof. exact (prop_ext (fun h2 : term145 s => @lem5266196 s h2 h1) (fun h2 : ((sup s) = (inf s)) = (term1122 s) => @lem5266189 s h1)). Qed.
Lemma lem5266198 (s : real -> Prop) (h1 : term143 s) : ((sup s) = (inf s)) = (term1122 s).
Proof. exact (EQ_MP (@lem5266197 s h1) (@lem5266189 s h1)). Qed.
Lemma lem5266199 (s : real -> Prop) : term1151 s.
Proof. exact (fun h0 : term143 s => @lem5266198 s h0). Qed.
Lemma lem5266204 : term1152.
Proof. exact (fun s : real -> Prop => @lem5266199 s). Qed.
