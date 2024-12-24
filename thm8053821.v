Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8053821_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
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
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm8048867_spec.
Require Import thm8048949_spec.
Lemma lem8051510 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8051511 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8051512 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8051511 t1) (@lem8051510 t1)). Qed.
Lemma lem8051513 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8051512 t1 t2). Qed.
Lemma lem8051514 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8051515 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8051514 t1 t2) (@lem8051513 t1 t2)). Qed.
Lemma lem8051516 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8051515 t1 t2 t3). Qed.
Lemma lem8051517 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8051518 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8051517 t1 t2 t3) (@lem8051516 t1 t2 t3)). Qed.
Lemma lem8051519 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8051518 t1 t2 t3)). Qed.
Lemma lem8051520 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term7 _142951 _142952 f) (h2 : term7 _142951 _142953 g) : term8 _142951 _142952 _142953 g f.
Proof. exact (conj (@lem8048949 _142951 _142953 g h2) (@lem8048867 _142951 _142952 f h1)). Qed.
Lemma lem8051528 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8051529 {_142951 _142953 : Type'} (s : type56 _142951 _142953) (t : type56 _142951 _142953) : (s = t) = (term10 _142951 _142953 s t).
Proof. exact (@lem8051528 (type24 _142951 _142953) s t). Qed.
Lemma lem8051530 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (g = (@EMPTY ((cart _142951 _142953) -> Prop))) = (term11 _142951 _142953 g).
Proof. exact (@lem8051529 _142951 _142953 g (@EMPTY ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051539 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8051540 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term7 _142951 _142953 g) = (term12 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051539) (@lem8051530 _142951 _142953 g)). Qed.
Lemma lem8051541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051542 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term13 _142951 _142953 g) = (term14 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051541) (@lem8051540 _142951 _142953 g)). Qed.
Lemma lem8051546 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8051547 {_142951 _142952 : Type'} (s : type56 _142951 _142952) (t : type56 _142951 _142952) : (s = t) = (term10 _142951 _142952 s t).
Proof. exact (@lem8051546 (type24 _142951 _142952) s t). Qed.
Lemma lem8051548 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (f = (@EMPTY ((cart _142951 _142952) -> Prop))) = (term11 _142951 _142952 f).
Proof. exact (@lem8051547 _142951 _142952 f (@EMPTY ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051557 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8051558 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term7 _142951 _142952 f) = (term12 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051557) (@lem8051548 _142951 _142952 f)). Qed.
Lemma lem8051559 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term8 _142951 _142952 _142953 g f) = (term15 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051542 _142951 _142953 g) (@lem8051558 _142951 _142952 f)). Qed.
Lemma lem8051562 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051563 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term16 _142951 _142952 _142953 g f) = (term17 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051562) (@lem8051559 _142951 _142952 _142953 g f)). Qed.
Lemma lem8051592 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term18 _142951 _142952 _142953 f g) = (term18 _142951 _142952 _142953 f g).
Proof. exact (eq_refl (term18 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051593 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term19 _142951 _142952 _142953 f g) = (term20 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8051563 _142951 _142952 _142953 g f) (@lem8051592 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051596 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term20 _142951 _142952 _142953 f g) = (term19 _142951 _142952 _142953 f g).
Proof. exact (SYM (@lem8051593 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051608 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051609 {_142951 _142953 : Type'} (P : type56 _142951 _142953) (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x P) = (P x).
Proof. exact (@lem8051608 (type24 _142951 _142953) P x). Qed.
Lemma lem8051610 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x g) = (g x).
Proof. exact (@lem8051609 _142951 _142953 g x). Qed.
Lemma lem8051611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8051612 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : (term21 _142951 _142953 x g) = (term22 _142951 _142953 g x).
Proof. exact (MK_COMB (@lem8051611) (@lem8051610 _142951 _142953 g x)). Qed.
Lemma lem8051614 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8051615 {_142951 _142953 : Type'} (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x (@EMPTY ((cart _142951 _142953) -> Prop))) = False.
Proof. exact (@lem8051614 (type24 _142951 _142953) x). Qed.
Lemma lem8051616 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : ((@IN ((cart _142951 _142953) -> Prop) x g) = (@IN ((cart _142951 _142953) -> Prop) x (@EMPTY ((cart _142951 _142953) -> Prop)))) = ((g x) = False).
Proof. exact (MK_COMB (@lem8051612 _142951 _142953 g x) (@lem8051615 _142951 _142953 x)). Qed.
Lemma lem8051618 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8051619 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : ((g x) = False) = (term23 _142951 _142953 g x).
Proof. exact (@lem8051618 (g x)). Qed.
Lemma lem8051620 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : ((@IN ((cart _142951 _142953) -> Prop) x g) = (@IN ((cart _142951 _142953) -> Prop) x (@EMPTY ((cart _142951 _142953) -> Prop)))) = (term23 _142951 _142953 g x).
Proof. exact (TRANS (@lem8051616 _142951 _142953 g x) (@lem8051619 _142951 _142953 g x)). Qed.
Lemma lem8051621 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term24 _142951 _142953 g) = (term25 _142951 _142953 g).
Proof. exact (fun_ext (fun x : type24 _142951 _142953 => @lem8051620 _142951 _142953 g x)). Qed.
Lemma lem8051622 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051623 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term11 _142951 _142953 g) = (term26 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051622 _142951 _142953) (@lem8051621 _142951 _142953 g)). Qed.
Lemma lem8051628 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8051629 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term12 _142951 _142953 g) = (term27 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051628) (@lem8051623 _142951 _142953 g)). Qed.
Lemma lem8051630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051631 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term14 _142951 _142953 g) = (term28 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051630) (@lem8051629 _142951 _142953 g)). Qed.
Lemma lem8051639 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051640 {_142951 _142952 : Type'} (P : type56 _142951 _142952) (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x P) = (P x).
Proof. exact (@lem8051639 (type24 _142951 _142952) P x). Qed.
Lemma lem8051641 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x f) = (f x).
Proof. exact (@lem8051640 _142951 _142952 f x). Qed.
Lemma lem8051642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8051643 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (term21 _142951 _142952 x f) = (term22 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051642) (@lem8051641 _142951 _142952 f x)). Qed.
Lemma lem8051645 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8051646 {_142951 _142952 : Type'} (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x (@EMPTY ((cart _142951 _142952) -> Prop))) = False.
Proof. exact (@lem8051645 (type24 _142951 _142952) x). Qed.
Lemma lem8051647 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : ((@IN ((cart _142951 _142952) -> Prop) x f) = (@IN ((cart _142951 _142952) -> Prop) x (@EMPTY ((cart _142951 _142952) -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem8051643 _142951 _142952 f x) (@lem8051646 _142951 _142952 x)). Qed.
Lemma lem8051649 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8051650 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : ((f x) = False) = (term23 _142951 _142952 f x).
Proof. exact (@lem8051649 (f x)). Qed.
Lemma lem8051651 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : ((@IN ((cart _142951 _142952) -> Prop) x f) = (@IN ((cart _142951 _142952) -> Prop) x (@EMPTY ((cart _142951 _142952) -> Prop)))) = (term23 _142951 _142952 f x).
Proof. exact (TRANS (@lem8051647 _142951 _142952 f x) (@lem8051650 _142951 _142952 f x)). Qed.
Lemma lem8051652 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term24 _142951 _142952 f) = (term25 _142951 _142952 f).
Proof. exact (fun_ext (fun x : type24 _142951 _142952 => @lem8051651 _142951 _142952 f x)). Qed.
Lemma lem8051653 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051654 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term11 _142951 _142952 f) = (term26 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051653 _142951 _142952) (@lem8051652 _142951 _142952 f)). Qed.
Lemma lem8051659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8051660 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term12 _142951 _142952 f) = (term27 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051659) (@lem8051654 _142951 _142952 f)). Qed.
Lemma lem8051661 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term15 _142951 _142952 _142953 g f) = (term29 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051631 _142951 _142953 g) (@lem8051660 _142951 _142952 f)). Qed.
Lemma lem8051664 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051665 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term17 _142951 _142952 _142953 g f) = (term30 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051664) (@lem8051661 _142951 _142952 _142953 g f)). Qed.
Lemma lem8051679 {A : Type'} (s : type686 A) (x : A) : (term31 A x s) = (term32 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem8051680 {_142951 _142952 : Type'} (s : type56 _142951 _142952) (x : cart _142951 _142952) : (term33 _142951 _142952 x s) = (term34 _142951 _142952 s x).
Proof. exact (@lem8051679 (cart _142951 _142952) s x). Qed.
Lemma lem8051681 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term33 _142951 _142952 x f) = (term34 _142951 _142952 f x).
Proof. exact (@lem8051680 _142951 _142952 f x). Qed.
Lemma lem8051689 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051690 {_142951 _142952 : Type'} (P : type56 _142951 _142952) (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x P) = (P x).
Proof. exact (@lem8051689 (type24 _142951 _142952) P x). Qed.
Lemma lem8051691 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) t f) = (f t).
Proof. exact (@lem8051690 _142951 _142952 f t). Qed.
Lemma lem8051692 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051693 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) : (term35 _142951 _142952 t f) = (term36 _142951 _142952 f t).
Proof. exact (MK_COMB (@lem8051692) (@lem8051691 _142951 _142952 f t)). Qed.
Lemma lem8051695 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051696 {_142951 _142952 : Type'} (P : type24 _142951 _142952) (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x P) = (P x).
Proof. exact (@lem8051695 (cart _142951 _142952) P x). Qed.
Lemma lem8051697 {_142951 _142952 : Type'} (t : type24 _142951 _142952) (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x t) = (t x).
Proof. exact (@lem8051696 _142951 _142952 t x). Qed.
Lemma lem8051698 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term37 _142951 _142952 f x t) = (term38 _142951 _142952 f t x).
Proof. exact (MK_COMB (@lem8051693 _142951 _142952 f t) (@lem8051697 _142951 _142952 t x)). Qed.
Lemma lem8051701 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term39 _142951 _142952 f x) = (term40 _142951 _142952 f x).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8051698 _142951 _142952 f t x)). Qed.
Lemma lem8051702 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051703 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term34 _142951 _142952 f x) = (term41 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051702 _142951 _142952) (@lem8051701 _142951 _142952 f x)). Qed.
Lemma lem8051708 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term33 _142951 _142952 x f) = (term41 _142951 _142952 f x).
Proof. exact (TRANS (@lem8051681 _142951 _142952 f x) (@lem8051703 _142951 _142952 f x)). Qed.
Lemma lem8051709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051710 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term42 _142951 _142952 x f) = (term43 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051709) (@lem8051708 _142951 _142952 f x)). Qed.
Lemma lem8051712 {A : Type'} (s : type686 A) (x : A) : (term31 A x s) = (term32 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem8051713 {_142951 _142953 : Type'} (s : type56 _142951 _142953) (x : cart _142951 _142953) : (term33 _142951 _142953 x s) = (term34 _142951 _142953 s x).
Proof. exact (@lem8051712 (cart _142951 _142953) s x). Qed.
Lemma lem8051714 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term33 _142951 _142953 y g) = (term34 _142951 _142953 g y).
Proof. exact (@lem8051713 _142951 _142953 g y). Qed.
Lemma lem8051722 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051723 {_142951 _142953 : Type'} (P : type56 _142951 _142953) (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x P) = (P x).
Proof. exact (@lem8051722 (type24 _142951 _142953) P x). Qed.
Lemma lem8051724 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) t g) = (g t).
Proof. exact (@lem8051723 _142951 _142953 g t). Qed.
Lemma lem8051725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051726 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term35 _142951 _142953 t g) = (term36 _142951 _142953 g t).
Proof. exact (MK_COMB (@lem8051725) (@lem8051724 _142951 _142953 g t)). Qed.
Lemma lem8051728 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051729 {_142951 _142953 : Type'} (P : type24 _142951 _142953) (x : cart _142951 _142953) : (@IN (cart _142951 _142953) x P) = (P x).
Proof. exact (@lem8051728 (cart _142951 _142953) P x). Qed.
Lemma lem8051730 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (@IN (cart _142951 _142953) y t) = (t y).
Proof. exact (@lem8051729 _142951 _142953 t y). Qed.
Lemma lem8051731 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term37 _142951 _142953 g y t) = (term38 _142951 _142953 g t y).
Proof. exact (MK_COMB (@lem8051726 _142951 _142953 g t) (@lem8051730 _142951 _142953 t y)). Qed.
Lemma lem8051734 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term39 _142951 _142953 g y) = (term40 _142951 _142953 g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8051731 _142951 _142953 g t y)). Qed.
Lemma lem8051735 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051736 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term34 _142951 _142953 g y) = (term41 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8051735 _142951 _142953) (@lem8051734 _142951 _142953 g y)). Qed.
Lemma lem8051741 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term33 _142951 _142953 y g) = (term41 _142951 _142953 g y).
Proof. exact (TRANS (@lem8051714 _142951 _142953 g y) (@lem8051736 _142951 _142953 g y)). Qed.
Lemma lem8051742 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term44 _142951 _142952 _142953 x f y g) = (term45 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8051710 _142951 _142952 f x) (@lem8051741 _142951 _142953 g y)). Qed.
Lemma lem8051745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8051746 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term46 _142951 _142952 _142953 x f y g) = (term47 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8051745) (@lem8051742 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8051760 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051761 {_142951 _142952 : Type'} (P : type56 _142951 _142952) (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x P) = (P x).
Proof. exact (@lem8051760 (type24 _142951 _142952) P x). Qed.
Lemma lem8051762 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) s f) = (f s).
Proof. exact (@lem8051761 _142951 _142952 f s). Qed.
Lemma lem8051763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051764 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (term48 _142951 _142952 s f) = (term49 _142951 _142952 f s).
Proof. exact (MK_COMB (@lem8051763) (@lem8051762 _142951 _142952 f s)). Qed.
Lemma lem8051766 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051767 {_142951 _142953 : Type'} (P : type56 _142951 _142953) (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x P) = (P x).
Proof. exact (@lem8051766 (type24 _142951 _142953) P x). Qed.
Lemma lem8051768 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) t g) = (g t).
Proof. exact (@lem8051767 _142951 _142953 g t). Qed.
Lemma lem8051769 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term50 _142951 _142952 _142953 s f t g) = (term51 _142951 _142952 _142953 f s g t).
Proof. exact (MK_COMB (@lem8051764 _142951 _142952 f s) (@lem8051768 _142951 _142953 g t)). Qed.
Lemma lem8051772 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051773 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term52 _142951 _142952 _142953 s f t g) = (term53 _142951 _142952 _142953 f s g t).
Proof. exact (MK_COMB (@lem8051772) (@lem8051769 _142951 _142952 _142953 f s g t)). Qed.
Lemma lem8051777 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051778 {_142951 _142952 : Type'} (P : type24 _142951 _142952) (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x P) = (P x).
Proof. exact (@lem8051777 (cart _142951 _142952) P x). Qed.
Lemma lem8051779 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x s) = (s x).
Proof. exact (@lem8051778 _142951 _142952 s x). Qed.
Lemma lem8051780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051781 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term54 _142951 _142952 x s) = (term55 _142951 _142952 s x).
Proof. exact (MK_COMB (@lem8051780) (@lem8051779 _142951 _142952 s x)). Qed.
Lemma lem8051783 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051784 {_142951 _142953 : Type'} (P : type24 _142951 _142953) (x : cart _142951 _142953) : (@IN (cart _142951 _142953) x P) = (P x).
Proof. exact (@lem8051783 (cart _142951 _142953) P x). Qed.
Lemma lem8051785 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (@IN (cart _142951 _142953) y t) = (t y).
Proof. exact (@lem8051784 _142951 _142953 t y). Qed.
Lemma lem8051786 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term56 _142951 _142952 _142953 x s y t) = (term57 _142951 _142952 _142953 s x t y).
Proof. exact (MK_COMB (@lem8051781 _142951 _142952 s x) (@lem8051785 _142951 _142953 t y)). Qed.
Lemma lem8051789 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term58 _142951 _142952 _142953 f g x s y t) = (term59 _142951 _142952 _142953 f g s x t y).
Proof. exact (MK_COMB (@lem8051773 _142951 _142952 _142953 f s g t) (@lem8051786 _142951 _142952 _142953 s x t y)). Qed.
Lemma lem8051792 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term60 _142951 _142952 _142953 f g x s y) = (term61 _142951 _142952 _142953 f g s x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8051789 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8051793 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051794 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term62 _142951 _142952 _142953 f g x s y) = (term63 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8051793 _142951 _142953) (@lem8051792 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8051799 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term64 _142951 _142952 _142953 f g x y) = (term65 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8051794 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8051800 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051801 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term66 _142951 _142952 _142953 f g x y) = (term67 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8051800 _142951 _142952) (@lem8051799 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8051806 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term44 _142951 _142952 _142953 x f y g) = (term66 _142951 _142952 _142953 f g x y)) = ((term45 _142951 _142952 _142953 f x g y) = (term67 _142951 _142952 _142953 f g x y)).
Proof. exact (MK_COMB (@lem8051746 _142951 _142952 _142953 f x g y) (@lem8051801 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8051809 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) : (term68 _142951 _142952 _142953 f g x) = (term69 _142951 _142952 _142953 f g x).
Proof. exact (fun_ext (fun y : cart _142951 _142953 => @lem8051806 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8051810 {_142951 _142953 : Type'} : (@all (cart _142951 _142953)) = (@all (cart _142951 _142953)).
Proof. exact (eq_refl (@all (cart _142951 _142953))). Qed.
Lemma lem8051811 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) : (term70 _142951 _142952 _142953 f g x) = (term71 _142951 _142952 _142953 f g x).
Proof. exact (MK_COMB (@lem8051810 _142951 _142953) (@lem8051809 _142951 _142952 _142953 f g x)). Qed.
Lemma lem8051816 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term72 _142951 _142952 _142953 f g) = (term73 _142951 _142952 _142953 f g).
Proof. exact (fun_ext (fun x : cart _142951 _142952 => @lem8051811 _142951 _142952 _142953 f g x)). Qed.
Lemma lem8051817 {_142951 _142952 : Type'} : (@all (cart _142951 _142952)) = (@all (cart _142951 _142952)).
Proof. exact (eq_refl (@all (cart _142951 _142952))). Qed.
Lemma lem8051818 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term18 _142951 _142952 _142953 f g) = (term74 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8051817 _142951 _142952) (@lem8051816 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051823 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term20 _142951 _142952 _142953 f g) = (term75 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8051665 _142951 _142952 _142953 g f) (@lem8051818 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051826 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term75 _142951 _142952 _142953 f g) = (term20 _142951 _142952 _142953 f g).
Proof. exact (SYM (@lem8051823 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051828 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8051829 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term75 _142951 _142952 _142953 f g) = (term77 _142951 _142952 _142953 f g).
Proof. exact (@lem8051828 (term75 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051830 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term77 _142951 _142952 _142953 f g) = (term75 _142951 _142952 _142953 f g).
Proof. exact (SYM (@lem8051829 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051831 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term78 _142951 _142952 _142953 f g) : term78 _142951 _142952 _142953 f g.
Proof. exact (h1). Qed.
Lemma lem8051834 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term77 _142951 _142952 _142953 f g) : term77 _142951 _142952 _142953 f g.
Proof. exact (h1). Qed.
Lemma lem8051835 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term79 _142951 _142952 _142953 f g.
Proof. exact (fun h0 : term77 _142951 _142952 _142953 f g => @lem8051834 _142951 _142952 _142953 f g h0). Qed.
Lemma lem8051836 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term79 _142951 _142952 _142953 f g) : term79 _142951 _142952 _142953 f g.
Proof. exact (h1). Qed.
Lemma lem8051837 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term77 _142951 _142952 _142953 f g) : term77 _142951 _142952 _142953 f g.
Proof. exact (h1). Qed.
Lemma lem8051838 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term77 _142951 _142952 _142953 f g) (h2 : term79 _142951 _142952 _142953 f g) : term77 _142951 _142952 _142953 f g.
Proof. exact (@lem8051836 _142951 _142952 _142953 f g h2 (@lem8051837 _142951 _142952 _142953 f g h1)). Qed.
Lemma lem8051839 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term77 _142951 _142952 _142953 f g) : term80 _142951 _142952 _142953 f g.
Proof. exact (fun h0 : term79 _142951 _142952 _142953 f g => @lem8051838 _142951 _142952 _142953 f g h1 h0). Qed.
Lemma lem8051840 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term79 _142951 _142952 _142953 f g) : term79 _142951 _142952 _142953 f g.
Proof. exact (h1). Qed.
Lemma lem8051841 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term77 _142951 _142952 _142953 f g) (h2 : term79 _142951 _142952 _142953 f g) : term77 _142951 _142952 _142953 f g.
Proof. exact (@lem8051839 _142951 _142952 _142953 f g h1 (@lem8051840 _142951 _142952 _142953 f g h2)). Qed.
Lemma lem8051842 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term79 _142951 _142952 _142953 f g) : term79 _142951 _142952 _142953 f g.
Proof. exact (fun h0 : term77 _142951 _142952 _142953 f g => @lem8051841 _142951 _142952 _142953 f g h0 h1). Qed.
Lemma lem8051843 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term81 _142951 _142952 _142953 f g.
Proof. exact (fun h0 : term79 _142951 _142952 _142953 f g => @lem8051842 _142951 _142952 _142953 f g h0). Qed.
Lemma lem8051846 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term79 _142951 _142952 _142953 f g.
Proof. exact (@lem8051843 _142951 _142952 _142953 f g (@lem8051835 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051847 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term79 _142951 _142952 _142953 f g.
Proof. exact (@lem8051846 _142951 _142952 _142953 f g). Qed.
Lemma lem8051857 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8051858 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term77 _142951 _142952 _142953 f g) = (term82 _142951 _142952 _142953 f g).
Proof. exact (@lem8051857 (term78 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051860 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8051861 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term82 _142951 _142952 _142953 f g) = (term75 _142951 _142952 _142953 f g).
Proof. exact (@lem8051860 (term75 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051864 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term77 _142951 _142952 _142953 f g) = (term75 _142951 _142952 _142953 f g).
Proof. exact (TRANS (@lem8051858 _142951 _142952 _142953 f g) (@lem8051861 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051911 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term84 _142951 _142952 _142953 g) = (term85 _142951 _142952 _142953 g).
Proof. exact (fun_ext (fun f : type56 _142951 _142952 => @lem8051864 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051912 {_142951 _142952 : Type'} : (@all (((cart _142951 _142952) -> Prop) -> Prop)) = (@all (((cart _142951 _142952) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((cart _142951 _142952) -> Prop) -> Prop))). Qed.
Lemma lem8051913 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term86 _142951 _142952 _142953 g) = (term87 _142951 _142952 _142953 g).
Proof. exact (MK_COMB (@lem8051912 _142951 _142952) (@lem8051911 _142951 _142952 _142953 g)). Qed.
Lemma lem8051918 {_142951 _142952 _142953 : Type'} : (term88 _142951 _142952 _142953) = (term89 _142951 _142952 _142953).
Proof. exact (fun_ext (fun g : type56 _142951 _142953 => @lem8051913 _142951 _142952 _142953 g)). Qed.
Lemma lem8051919 {_142951 _142953 : Type'} : (@all (((cart _142951 _142953) -> Prop) -> Prop)) = (@all (((cart _142951 _142953) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((cart _142951 _142953) -> Prop) -> Prop))). Qed.
Lemma lem8051928 {_142951 _142952 _142953 : Type'} : (term90 _142951 _142952 _142953) = (term91 _142951 _142952 _142953).
Proof. exact (MK_COMB (@lem8051919 _142951 _142953) (@lem8051918 _142951 _142952 _142953)). Qed.
Lemma lem8051941 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term59 _142951 _142952 _142953 f g s x t y) = (term59 _142951 _142952 _142953 f g s x t y).
Proof. exact (eq_refl (term59 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8051942 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term61 _142951 _142952 _142953 f g s x y) = (term61 _142951 _142952 _142953 f g s x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8051941 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8051943 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051944 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term63 _142951 _142952 _142953 f g s x y) = (term63 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8051943 _142951 _142953) (@lem8051942 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8051945 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term65 _142951 _142952 _142953 f g x y) = (term65 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8051944 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8051946 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051947 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term67 _142951 _142952 _142953 f g x y) = (term67 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8051946 _142951 _142952) (@lem8051945 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8051952 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term38 _142951 _142953 g t y) = (term38 _142951 _142953 g t y).
Proof. exact (eq_refl (term38 _142951 _142953 g t y)). Qed.
Lemma lem8051953 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term40 _142951 _142953 g y) = (term40 _142951 _142953 g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8051952 _142951 _142953 g t y)). Qed.
Lemma lem8051954 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051955 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term41 _142951 _142953 g y) = (term41 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8051954 _142951 _142953) (@lem8051953 _142951 _142953 g y)). Qed.
Lemma lem8051960 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term38 _142951 _142952 f t x) = (term38 _142951 _142952 f t x).
Proof. exact (eq_refl (term38 _142951 _142952 f t x)). Qed.
Lemma lem8051961 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term40 _142951 _142952 f x) = (term40 _142951 _142952 f x).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8051960 _142951 _142952 f t x)). Qed.
Lemma lem8051962 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051963 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term41 _142951 _142952 f x) = (term41 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051962 _142951 _142952) (@lem8051961 _142951 _142952 f x)). Qed.
Lemma lem8051964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051965 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term43 _142951 _142952 f x) = (term43 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051964) (@lem8051963 _142951 _142952 f x)). Qed.
Lemma lem8051966 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term45 _142951 _142952 _142953 f x g y) = (term45 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8051965 _142951 _142952 f x) (@lem8051955 _142951 _142953 g y)). Qed.
Lemma lem8051967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8051968 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term47 _142951 _142952 _142953 f x g y) = (term47 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8051967) (@lem8051966 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8051969 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term45 _142951 _142952 _142953 f x g y) = (term67 _142951 _142952 _142953 f g x y)) = ((term45 _142951 _142952 _142953 f x g y) = (term67 _142951 _142952 _142953 f g x y)).
Proof. exact (MK_COMB (@lem8051968 _142951 _142952 _142953 f x g y) (@lem8051947 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8051970 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) : (term69 _142951 _142952 _142953 f g x) = (term69 _142951 _142952 _142953 f g x).
Proof. exact (fun_ext (fun y : cart _142951 _142953 => @lem8051969 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8051971 {_142951 _142953 : Type'} : (@all (cart _142951 _142953)) = (@all (cart _142951 _142953)).
Proof. exact (eq_refl (@all (cart _142951 _142953))). Qed.
Lemma lem8051972 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) : (term71 _142951 _142952 _142953 f g x) = (term71 _142951 _142952 _142953 f g x).
Proof. exact (MK_COMB (@lem8051971 _142951 _142953) (@lem8051970 _142951 _142952 _142953 f g x)). Qed.
Lemma lem8051973 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term73 _142951 _142952 _142953 f g) = (term73 _142951 _142952 _142953 f g).
Proof. exact (fun_ext (fun x : cart _142951 _142952 => @lem8051972 _142951 _142952 _142953 f g x)). Qed.
Lemma lem8051974 {_142951 _142952 : Type'} : (@all (cart _142951 _142952)) = (@all (cart _142951 _142952)).
Proof. exact (eq_refl (@all (cart _142951 _142952))). Qed.
Lemma lem8051975 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term74 _142951 _142952 _142953 f g) = (term74 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8051974 _142951 _142952) (@lem8051973 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051978 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (term23 _142951 _142952 f x) = (term23 _142951 _142952 f x).
Proof. exact (eq_refl (term23 _142951 _142952 f x)). Qed.
Lemma lem8051979 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term25 _142951 _142952 f) = (term25 _142951 _142952 f).
Proof. exact (fun_ext (fun x : type24 _142951 _142952 => @lem8051978 _142951 _142952 f x)). Qed.
Lemma lem8051980 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051981 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term26 _142951 _142952 f) = (term26 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051980 _142951 _142952) (@lem8051979 _142951 _142952 f)). Qed.
Lemma lem8051982 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8051983 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term27 _142951 _142952 f) = (term27 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051982) (@lem8051981 _142951 _142952 f)). Qed.
Lemma lem8051986 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : (term23 _142951 _142953 g x) = (term23 _142951 _142953 g x).
Proof. exact (eq_refl (term23 _142951 _142953 g x)). Qed.
Lemma lem8051987 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term25 _142951 _142953 g) = (term25 _142951 _142953 g).
Proof. exact (fun_ext (fun x : type24 _142951 _142953 => @lem8051986 _142951 _142953 g x)). Qed.
Lemma lem8051988 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051989 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term26 _142951 _142953 g) = (term26 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051988 _142951 _142953) (@lem8051987 _142951 _142953 g)). Qed.
Lemma lem8051990 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8051991 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term27 _142951 _142953 g) = (term27 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051990) (@lem8051989 _142951 _142953 g)). Qed.
Lemma lem8051992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051993 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term28 _142951 _142953 g) = (term28 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051992) (@lem8051991 _142951 _142953 g)). Qed.
Lemma lem8051994 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term29 _142951 _142952 _142953 g f) = (term29 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051993 _142951 _142953 g) (@lem8051983 _142951 _142952 f)). Qed.
Lemma lem8051995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051996 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term30 _142951 _142952 _142953 g f) = (term30 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051995) (@lem8051994 _142951 _142952 _142953 g f)). Qed.
Lemma lem8051997 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term75 _142951 _142952 _142953 f g) = (term75 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8051996 _142951 _142952 _142953 g f) (@lem8051975 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051998 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term85 _142951 _142952 _142953 g) = (term85 _142951 _142952 _142953 g).
Proof. exact (fun_ext (fun f : type56 _142951 _142952 => @lem8051997 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051999 {_142951 _142952 : Type'} : (@all (((cart _142951 _142952) -> Prop) -> Prop)) = (@all (((cart _142951 _142952) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((cart _142951 _142952) -> Prop) -> Prop))). Qed.
Lemma lem8052000 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term87 _142951 _142952 _142953 g) = (term87 _142951 _142952 _142953 g).
Proof. exact (MK_COMB (@lem8051999 _142951 _142952) (@lem8051998 _142951 _142952 _142953 g)). Qed.
Lemma lem8052001 {_142951 _142952 _142953 : Type'} : (term89 _142951 _142952 _142953) = (term89 _142951 _142952 _142953).
Proof. exact (fun_ext (fun g : type56 _142951 _142953 => @lem8052000 _142951 _142952 _142953 g)). Qed.
Lemma lem8052002 {_142951 _142953 : Type'} : (@all (((cart _142951 _142953) -> Prop) -> Prop)) = (@all (((cart _142951 _142953) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((cart _142951 _142953) -> Prop) -> Prop))). Qed.
Lemma lem8052003 {_142951 _142952 _142953 : Type'} : (term91 _142951 _142952 _142953) = (term91 _142951 _142952 _142953).
Proof. exact (MK_COMB (@lem8052002 _142951 _142953) (@lem8052001 _142951 _142952 _142953)). Qed.
Lemma lem8052082 {_142951 _142952 _142953 : Type'} : (term90 _142951 _142952 _142953) = (term91 _142951 _142952 _142953).
Proof. exact (TRANS (@lem8051928 _142951 _142952 _142953) (@lem8052003 _142951 _142952 _142953)). Qed.
Lemma lem8052083 {_142951 _142952 _142953 : Type'} : (term91 _142951 _142952 _142953) = (term90 _142951 _142952 _142953).
Proof. exact (SYM (@lem8052082 _142951 _142952 _142953)). Qed.
Lemma lem8052084 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term29 _142951 _142952 _142953 g f) : term29 _142951 _142952 _142953 g f.
Proof. exact (h1). Qed.
Lemma lem8052086 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8052087 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term45 _142951 _142952 _142953 f x g y) = (term67 _142951 _142952 _142953 f g x y)) = (term92 _142951 _142952 _142953 f g x y).
Proof. exact (@lem8052086 ((term45 _142951 _142952 _142953 f x g y) = (term67 _142951 _142952 _142953 f g x y))). Qed.
Lemma lem8052088 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term92 _142951 _142952 _142953 f g x y) = ((term45 _142951 _142952 _142953 f x g y) = (term67 _142951 _142952 _142953 f g x y)).
Proof. exact (SYM (@lem8052087 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052089 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term93 _142951 _142952 _142953 f g x y) : term93 _142951 _142952 _142953 f g x y.
Proof. exact (h1). Qed.
Lemma lem8052092 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : (term94 _142951 _142953 g x) = (g x).
Proof. exact (@lem16933 (g x)). Qed.
Lemma lem8052093 {_142951 _142953 : Type'} (P : type56 _142951 _142953) : (term95 _142951 _142953 P) = (term96 _142951 _142953 P).
Proof. exact (@lem18392 (type24 _142951 _142953) P). Qed.
Lemma lem8052094 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term27 _142951 _142953 g) = (term97 _142951 _142953 g).
Proof. exact (@lem8052093 _142951 _142953 (term25 _142951 _142953 g)). Qed.
Lemma lem8052095 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : (term98 _142951 _142953 g x) = (term23 _142951 _142953 g x).
Proof. exact (eq_refl (term98 _142951 _142953 g x)). Qed.
Lemma lem8052096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052097 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : (term99 _142951 _142953 g x) = (term94 _142951 _142953 g x).
Proof. exact (MK_COMB (@lem8052096) (@lem8052095 _142951 _142953 g x)). Qed.
Lemma lem8052098 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : (term99 _142951 _142953 g x) = (g x).
Proof. exact (TRANS (@lem8052097 _142951 _142953 g x) (@lem8052092 _142951 _142953 g x)). Qed.
Lemma lem8052099 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term100 _142951 _142953 g) = (term101 _142951 _142953 g).
Proof. exact (fun_ext (fun x : type24 _142951 _142953 => @lem8052098 _142951 _142953 g x)). Qed.
Lemma lem8052100 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052101 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term97 _142951 _142953 g) = (term102 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8052100 _142951 _142953) (@lem8052099 _142951 _142953 g)). Qed.
Lemma lem8052102 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term27 _142951 _142953 g) = (term102 _142951 _142953 g).
Proof. exact (TRANS (@lem8052094 _142951 _142953 g) (@lem8052101 _142951 _142953 g)). Qed.
Lemma lem8052105 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (term94 _142951 _142952 f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem8052106 {_142951 _142952 : Type'} (P : type56 _142951 _142952) : (term95 _142951 _142952 P) = (term96 _142951 _142952 P).
Proof. exact (@lem18392 (type24 _142951 _142952) P). Qed.
Lemma lem8052107 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term27 _142951 _142952 f) = (term97 _142951 _142952 f).
Proof. exact (@lem8052106 _142951 _142952 (term25 _142951 _142952 f)). Qed.
Lemma lem8052108 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (term98 _142951 _142952 f x) = (term23 _142951 _142952 f x).
Proof. exact (eq_refl (term98 _142951 _142952 f x)). Qed.
Lemma lem8052109 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052110 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (term99 _142951 _142952 f x) = (term94 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8052109) (@lem8052108 _142951 _142952 f x)). Qed.
Lemma lem8052111 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (term99 _142951 _142952 f x) = (f x).
Proof. exact (TRANS (@lem8052110 _142951 _142952 f x) (@lem8052105 _142951 _142952 f x)). Qed.
Lemma lem8052112 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term100 _142951 _142952 f) = (term101 _142951 _142952 f).
Proof. exact (fun_ext (fun x : type24 _142951 _142952 => @lem8052111 _142951 _142952 f x)). Qed.
Lemma lem8052113 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052114 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term97 _142951 _142952 f) = (term102 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8052113 _142951 _142952) (@lem8052112 _142951 _142952 f)). Qed.
Lemma lem8052115 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term27 _142951 _142952 f) = (term102 _142951 _142952 f).
Proof. exact (TRANS (@lem8052107 _142951 _142952 f) (@lem8052114 _142951 _142952 f)). Qed.
Lemma lem8052116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052117 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term28 _142951 _142953 g) = (term103 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8052116) (@lem8052102 _142951 _142953 g)). Qed.
Lemma lem8052118 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term29 _142951 _142952 _142953 g f) = (term104 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8052117 _142951 _142953 g) (@lem8052115 _142951 _142952 f)). Qed.
Lemma lem8052129 {A : Type'} (P : A -> Prop) (Q : Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8052130 {_142951 _142953 : Type'} (P : type56 _142951 _142953) (Q : Prop) : (term107 _142951 _142953 P Q) = (term108 _142951 _142953 P Q).
Proof. exact (@lem8052129 (type24 _142951 _142953) P Q). Qed.
Lemma lem8052131 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term104 _142951 _142952 _142953 g f) = (term109 _142951 _142952 _142953 g f).
Proof. exact (@lem8052130 _142951 _142953 g (term102 _142951 _142952 f)). Qed.
Lemma lem8052133 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8052134 {_142951 _142952 : Type'} (P : Prop) (Q : type56 _142951 _142952) : (term112 _142951 _142952 P Q) = (term113 _142951 _142952 P Q).
Proof. exact (@lem8052133 (type24 _142951 _142952) P Q). Qed.
Lemma lem8052135 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) (f : type56 _142951 _142952) : (term114 _142951 _142952 _142953 g x f) = (term115 _142951 _142952 _142953 g x f).
Proof. exact (@lem8052134 _142951 _142952 (g x) f). Qed.
Lemma lem8052136 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term116 _142951 _142952 _142953 g f) = (term117 _142951 _142952 _142953 g f).
Proof. exact (fun_ext (fun x : type24 _142951 _142953 => @lem8052135 _142951 _142952 _142953 g x f)). Qed.
Lemma lem8052137 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052138 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term109 _142951 _142952 _142953 g f) = (term118 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8052137 _142951 _142953) (@lem8052136 _142951 _142952 _142953 g f)). Qed.
Lemma lem8052140 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term104 _142951 _142952 _142953 g f) = (term118 _142951 _142952 _142953 g f).
Proof. exact (TRANS (@lem8052131 _142951 _142952 _142953 g f) (@lem8052138 _142951 _142952 _142953 g f)). Qed.
Lemma lem8052141 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term29 _142951 _142952 _142953 g f) = (term118 _142951 _142952 _142953 g f).
Proof. exact (TRANS (@lem8052118 _142951 _142952 _142953 g f) (@lem8052140 _142951 _142952 _142953 g f)). Qed.
Lemma lem8052142 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term29 _142951 _142952 _142953 g f) : term118 _142951 _142952 _142953 g f.
Proof. exact (EQ_MP (@lem8052141 _142951 _142952 _142953 g f) (@lem8052084 _142951 _142952 _142953 g f h1)). Qed.
Lemma lem8052151 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term119 _142951 _142952 f t x) = (term120 _142951 _142952 f t x).
Proof. exact (@lem17362 (f t) (t x)). Qed.
Lemma lem8052156 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term38 _142951 _142952 f t x) = (term121 _142951 _142952 f t x).
Proof. exact (@lem17265 (f t) (t x)). Qed.
Lemma lem8052157 {_142951 _142952 : Type'} (P : type56 _142951 _142952) : (term95 _142951 _142952 P) = (term96 _142951 _142952 P).
Proof. exact (@lem18392 (type24 _142951 _142952) P). Qed.
Lemma lem8052158 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term122 _142951 _142952 f x) = (term123 _142951 _142952 f x).
Proof. exact (@lem8052157 _142951 _142952 (term40 _142951 _142952 f x)). Qed.
Lemma lem8052159 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term124 _142951 _142952 f x t) = (term38 _142951 _142952 f t x).
Proof. exact (eq_refl (term124 _142951 _142952 f x t)). Qed.
Lemma lem8052160 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052161 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term125 _142951 _142952 f x t) = (term119 _142951 _142952 f t x).
Proof. exact (MK_COMB (@lem8052160) (@lem8052159 _142951 _142952 f t x)). Qed.
Lemma lem8052162 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term125 _142951 _142952 f x t) = (term120 _142951 _142952 f t x).
Proof. exact (TRANS (@lem8052161 _142951 _142952 f t x) (@lem8052151 _142951 _142952 f t x)). Qed.
Lemma lem8052163 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term126 _142951 _142952 f x) = (term127 _142951 _142952 f x).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8052162 _142951 _142952 f t x)). Qed.
Lemma lem8052164 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052165 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term123 _142951 _142952 f x) = (term128 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8052164 _142951 _142952) (@lem8052163 _142951 _142952 f x)). Qed.
Lemma lem8052166 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term122 _142951 _142952 f x) = (term128 _142951 _142952 f x).
Proof. exact (TRANS (@lem8052158 _142951 _142952 f x) (@lem8052165 _142951 _142952 f x)). Qed.
Lemma lem8052167 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term40 _142951 _142952 f x) = (term129 _142951 _142952 f x).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8052156 _142951 _142952 f t x)). Qed.
Lemma lem8052168 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052169 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term41 _142951 _142952 f x) = (term130 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8052168 _142951 _142952) (@lem8052167 _142951 _142952 f x)). Qed.
Lemma lem8052178 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term119 _142951 _142953 g t y) = (term120 _142951 _142953 g t y).
Proof. exact (@lem17362 (g t) (t y)). Qed.
Lemma lem8052183 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term38 _142951 _142953 g t y) = (term121 _142951 _142953 g t y).
Proof. exact (@lem17265 (g t) (t y)). Qed.
Lemma lem8052184 {_142951 _142953 : Type'} (P : type56 _142951 _142953) : (term95 _142951 _142953 P) = (term96 _142951 _142953 P).
Proof. exact (@lem18392 (type24 _142951 _142953) P). Qed.
Lemma lem8052185 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term122 _142951 _142953 g y) = (term123 _142951 _142953 g y).
Proof. exact (@lem8052184 _142951 _142953 (term40 _142951 _142953 g y)). Qed.
Lemma lem8052186 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term124 _142951 _142953 g y t) = (term38 _142951 _142953 g t y).
Proof. exact (eq_refl (term124 _142951 _142953 g y t)). Qed.
Lemma lem8052187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052188 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term125 _142951 _142953 g y t) = (term119 _142951 _142953 g t y).
Proof. exact (MK_COMB (@lem8052187) (@lem8052186 _142951 _142953 g t y)). Qed.
Lemma lem8052189 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term125 _142951 _142953 g y t) = (term120 _142951 _142953 g t y).
Proof. exact (TRANS (@lem8052188 _142951 _142953 g t y) (@lem8052178 _142951 _142953 g t y)). Qed.
Lemma lem8052190 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term126 _142951 _142953 g y) = (term127 _142951 _142953 g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052189 _142951 _142953 g t y)). Qed.
Lemma lem8052191 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052192 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term123 _142951 _142953 g y) = (term128 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8052191 _142951 _142953) (@lem8052190 _142951 _142953 g y)). Qed.
Lemma lem8052193 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term122 _142951 _142953 g y) = (term128 _142951 _142953 g y).
Proof. exact (TRANS (@lem8052185 _142951 _142953 g y) (@lem8052192 _142951 _142953 g y)). Qed.
Lemma lem8052194 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term40 _142951 _142953 g y) = (term129 _142951 _142953 g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052183 _142951 _142953 g t y)). Qed.
Lemma lem8052195 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052196 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term41 _142951 _142953 g y) = (term130 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8052195 _142951 _142953) (@lem8052194 _142951 _142953 g y)). Qed.
Lemma lem8052197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052198 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term131 _142951 _142952 f x) = (term132 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8052197) (@lem8052166 _142951 _142952 f x)). Qed.
Lemma lem8052199 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term133 _142951 _142952 _142953 f x g y) = (term134 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052198 _142951 _142952 f x) (@lem8052193 _142951 _142953 g y)). Qed.
Lemma lem8052200 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term135 _142951 _142952 _142953 f x g y) = (term133 _142951 _142952 _142953 f x g y).
Proof. exact (@lem17045 (term41 _142951 _142952 f x) (term41 _142951 _142953 g y)). Qed.
Lemma lem8052201 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term135 _142951 _142952 _142953 f x g y) = (term134 _142951 _142952 _142953 f x g y).
Proof. exact (TRANS (@lem8052200 _142951 _142952 _142953 f x g y) (@lem8052199 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052203 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term43 _142951 _142952 f x) = (term136 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8052202) (@lem8052169 _142951 _142952 f x)). Qed.
Lemma lem8052204 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term45 _142951 _142952 _142953 f x g y) = (term137 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052203 _142951 _142952 f x) (@lem8052196 _142951 _142953 g y)). Qed.
Lemma lem8052213 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term138 _142951 _142952 _142953 f s g t) = (term139 _142951 _142952 _142953 f s g t).
Proof. exact (@lem17045 (f s) (g t)). Qed.
Lemma lem8052225 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term140 _142951 _142952 _142953 s x t y) = (term141 _142951 _142952 _142953 s x t y).
Proof. exact (@lem17045 (s x) (t y)). Qed.
Lemma lem8052228 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term57 _142951 _142952 _142953 s x t y) = (term57 _142951 _142952 _142953 s x t y).
Proof. exact (eq_refl (term57 _142951 _142952 _142953 s x t y)). Qed.
Lemma lem8052230 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term142 _142951 _142952 _142953 f s g t) = (term142 _142951 _142952 _142953 f s g t).
Proof. exact (eq_refl (term142 _142951 _142952 _142953 f s g t)). Qed.
Lemma lem8052231 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term143 _142951 _142952 _142953 f g s x t y) = (term144 _142951 _142952 _142953 f g s x t y).
Proof. exact (MK_COMB (@lem8052230 _142951 _142952 _142953 f s g t) (@lem8052225 _142951 _142952 _142953 s x t y)). Qed.
Lemma lem8052232 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term145 _142951 _142952 _142953 f g s x t y) = (term143 _142951 _142952 _142953 f g s x t y).
Proof. exact (@lem17362 (term51 _142951 _142952 _142953 f s g t) (term57 _142951 _142952 _142953 s x t y)). Qed.
Lemma lem8052233 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term145 _142951 _142952 _142953 f g s x t y) = (term144 _142951 _142952 _142953 f g s x t y).
Proof. exact (TRANS (@lem8052232 _142951 _142952 _142953 f g s x t y) (@lem8052231 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052235 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term146 _142951 _142952 _142953 f s g t) = (term147 _142951 _142952 _142953 f s g t).
Proof. exact (MK_COMB (@lem8052234) (@lem8052213 _142951 _142952 _142953 f s g t)). Qed.
Lemma lem8052236 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term148 _142951 _142952 _142953 f g s x t y) = (term149 _142951 _142952 _142953 f g s x t y).
Proof. exact (MK_COMB (@lem8052235 _142951 _142952 _142953 f s g t) (@lem8052228 _142951 _142952 _142953 s x t y)). Qed.
Lemma lem8052237 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term59 _142951 _142952 _142953 f g s x t y) = (term148 _142951 _142952 _142953 f g s x t y).
Proof. exact (@lem17265 (term51 _142951 _142952 _142953 f s g t) (term57 _142951 _142952 _142953 s x t y)). Qed.
Lemma lem8052238 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term59 _142951 _142952 _142953 f g s x t y) = (term149 _142951 _142952 _142953 f g s x t y).
Proof. exact (TRANS (@lem8052237 _142951 _142952 _142953 f g s x t y) (@lem8052236 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052239 {_142951 _142953 : Type'} (P : type56 _142951 _142953) : (term95 _142951 _142953 P) = (term96 _142951 _142953 P).
Proof. exact (@lem18392 (type24 _142951 _142953) P). Qed.
Lemma lem8052240 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term150 _142951 _142952 _142953 f g s x y) = (term151 _142951 _142952 _142953 f g s x y).
Proof. exact (@lem8052239 _142951 _142953 (term61 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052241 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term152 _142951 _142952 _142953 f g s x y t) = (term59 _142951 _142952 _142953 f g s x t y).
Proof. exact (eq_refl (term152 _142951 _142952 _142953 f g s x y t)). Qed.
Lemma lem8052242 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052243 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term153 _142951 _142952 _142953 f g s x y t) = (term145 _142951 _142952 _142953 f g s x t y).
Proof. exact (MK_COMB (@lem8052242) (@lem8052241 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052244 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term153 _142951 _142952 _142953 f g s x y t) = (term144 _142951 _142952 _142953 f g s x t y).
Proof. exact (TRANS (@lem8052243 _142951 _142952 _142953 f g s x t y) (@lem8052233 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052245 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term154 _142951 _142952 _142953 f g s x y) = (term155 _142951 _142952 _142953 f g s x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052244 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052246 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052247 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term151 _142951 _142952 _142953 f g s x y) = (term156 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052246 _142951 _142953) (@lem8052245 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052248 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term150 _142951 _142952 _142953 f g s x y) = (term156 _142951 _142952 _142953 f g s x y).
Proof. exact (TRANS (@lem8052240 _142951 _142952 _142953 f g s x y) (@lem8052247 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052249 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term61 _142951 _142952 _142953 f g s x y) = (term157 _142951 _142952 _142953 f g s x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052238 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052250 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052251 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term63 _142951 _142952 _142953 f g s x y) = (term158 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052250 _142951 _142953) (@lem8052249 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052252 {_142951 _142952 : Type'} (P : type56 _142951 _142952) : (term95 _142951 _142952 P) = (term96 _142951 _142952 P).
Proof. exact (@lem18392 (type24 _142951 _142952) P). Qed.
Lemma lem8052253 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term159 _142951 _142952 _142953 f g x y) = (term160 _142951 _142952 _142953 f g x y).
Proof. exact (@lem8052252 _142951 _142952 (term65 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052254 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term161 _142951 _142952 _142953 f g x y s) = (term63 _142951 _142952 _142953 f g s x y).
Proof. exact (eq_refl (term161 _142951 _142952 _142953 f g x y s)). Qed.
Lemma lem8052255 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052256 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term162 _142951 _142952 _142953 f g x y s) = (term150 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052255) (@lem8052254 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052257 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term162 _142951 _142952 _142953 f g x y s) = (term156 _142951 _142952 _142953 f g s x y).
Proof. exact (TRANS (@lem8052256 _142951 _142952 _142953 f g s x y) (@lem8052248 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052258 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term163 _142951 _142952 _142953 f g x y) = (term164 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8052257 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052259 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052260 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term160 _142951 _142952 _142953 f g x y) = (term165 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052259 _142951 _142952) (@lem8052258 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052261 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term159 _142951 _142952 _142953 f g x y) = (term165 _142951 _142952 _142953 f g x y).
Proof. exact (TRANS (@lem8052253 _142951 _142952 _142953 f g x y) (@lem8052260 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052262 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term65 _142951 _142952 _142953 f g x y) = (term166 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8052251 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052263 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052264 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term67 _142951 _142952 _142953 f g x y) = (term167 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052263 _142951 _142952) (@lem8052262 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052266 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term168 _142951 _142952 _142953 f x g y) = (term169 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052265) (@lem8052201 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052267 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term170 _142951 _142952 _142953 f g x y) = (term171 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052266 _142951 _142952 _142953 f x g y) (@lem8052264 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052269 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term172 _142951 _142952 _142953 f x g y) = (term173 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052268) (@lem8052204 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052270 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term174 _142951 _142952 _142953 f g x y) = (term175 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052269 _142951 _142952 _142953 f x g y) (@lem8052261 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052272 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term176 _142951 _142952 _142953 f g x y) = (term177 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052271) (@lem8052270 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052273 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term178 _142951 _142952 _142953 f g x y) = (term179 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052272 _142951 _142952 _142953 f g x y) (@lem8052267 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052274 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term93 _142951 _142952 _142953 f g x y) = (term178 _142951 _142952 _142953 f g x y).
Proof. exact (@lem17646 (term45 _142951 _142952 _142953 f x g y) (term67 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052275 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term93 _142951 _142952 _142953 f g x y) = (term179 _142951 _142952 _142953 f g x y).
Proof. exact (TRANS (@lem8052274 _142951 _142952 _142953 f g x y) (@lem8052273 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052534 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8052535 {_142951 _142952 : Type'} (P : Prop) (Q : type56 _142951 _142952) : (term112 _142951 _142952 P Q) = (term113 _142951 _142952 P Q).
Proof. exact (@lem8052534 (type24 _142951 _142952) P Q). Qed.
Lemma lem8052536 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term180 _142951 _142952 _142953 f g x y) = (term181 _142951 _142952 _142953 f g x y).
Proof. exact (@lem8052535 _142951 _142952 (term137 _142951 _142952 _142953 f x g y) (term164 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052537 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term182 _142951 _142952 _142953 f g x y s) = (term156 _142951 _142952 _142953 f g s x y).
Proof. exact (eq_refl (term182 _142951 _142952 _142953 f g x y s)). Qed.
Lemma lem8052538 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term183 _142951 _142952 _142953 f g x y) = (term164 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8052537 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052539 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052540 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term184 _142951 _142952 _142953 f g x y) = (term165 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052539 _142951 _142952) (@lem8052538 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052541 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term173 _142951 _142952 _142953 f x g y) = (term173 _142951 _142952 _142953 f x g y).
Proof. exact (eq_refl (term173 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052542 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term180 _142951 _142952 _142953 f g x y) = (term175 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052541 _142951 _142952 _142953 f x g y) (@lem8052540 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8052544 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term185 _142951 _142952 _142953 f g x y) = (term186 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052543) (@lem8052542 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052545 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term182 _142951 _142952 _142953 f g x y s) = (term156 _142951 _142952 _142953 f g s x y).
Proof. exact (eq_refl (term182 _142951 _142952 _142953 f g x y s)). Qed.
Lemma lem8052546 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term173 _142951 _142952 _142953 f x g y) = (term173 _142951 _142952 _142953 f x g y).
Proof. exact (eq_refl (term173 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052547 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term187 _142951 _142952 _142953 f g x y s) = (term188 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052546 _142951 _142952 _142953 f x g y) (@lem8052545 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052548 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term189 _142951 _142952 _142953 f g x y) = (term190 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8052547 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052549 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052550 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term181 _142951 _142952 _142953 f g x y) = (term191 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052549 _142951 _142952) (@lem8052548 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052551 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term180 _142951 _142952 _142953 f g x y) = (term181 _142951 _142952 _142953 f g x y)) = ((term175 _142951 _142952 _142953 f g x y) = (term191 _142951 _142952 _142953 f g x y)).
Proof. exact (MK_COMB (@lem8052544 _142951 _142952 _142953 f g x y) (@lem8052550 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052552 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term175 _142951 _142952 _142953 f g x y) = (term191 _142951 _142952 _142953 f g x y).
Proof. exact (EQ_MP (@lem8052551 _142951 _142952 _142953 f g x y) (@lem8052536 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052554 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8052555 {_142951 _142953 : Type'} (P : Prop) (Q : type56 _142951 _142953) : (term112 _142951 _142953 P Q) = (term113 _142951 _142953 P Q).
Proof. exact (@lem8052554 (type24 _142951 _142953) P Q). Qed.
Lemma lem8052556 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term192 _142951 _142952 _142953 f g s x y) = (term193 _142951 _142952 _142953 f g s x y).
Proof. exact (@lem8052555 _142951 _142953 (term137 _142951 _142952 _142953 f x g y) (term155 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052557 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term194 _142951 _142952 _142953 f g s x y t) = (term144 _142951 _142952 _142953 f g s x t y).
Proof. exact (eq_refl (term194 _142951 _142952 _142953 f g s x y t)). Qed.
Lemma lem8052558 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term195 _142951 _142952 _142953 f g s x y) = (term155 _142951 _142952 _142953 f g s x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052557 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052559 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052560 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term196 _142951 _142952 _142953 f g s x y) = (term156 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052559 _142951 _142953) (@lem8052558 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052561 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term173 _142951 _142952 _142953 f x g y) = (term173 _142951 _142952 _142953 f x g y).
Proof. exact (eq_refl (term173 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052562 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term192 _142951 _142952 _142953 f g s x y) = (term188 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052561 _142951 _142952 _142953 f x g y) (@lem8052560 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8052564 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term197 _142951 _142952 _142953 f g s x y) = (term198 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052563) (@lem8052562 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052565 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term194 _142951 _142952 _142953 f g s x y t) = (term144 _142951 _142952 _142953 f g s x t y).
Proof. exact (eq_refl (term194 _142951 _142952 _142953 f g s x y t)). Qed.
Lemma lem8052566 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term173 _142951 _142952 _142953 f x g y) = (term173 _142951 _142952 _142953 f x g y).
Proof. exact (eq_refl (term173 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052567 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term199 _142951 _142952 _142953 f g s x y t) = (term200 _142951 _142952 _142953 f g s x t y).
Proof. exact (MK_COMB (@lem8052566 _142951 _142952 _142953 f x g y) (@lem8052565 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052568 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term201 _142951 _142952 _142953 f g s x y) = (term202 _142951 _142952 _142953 f g s x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052567 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052569 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052570 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term193 _142951 _142952 _142953 f g s x y) = (term203 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052569 _142951 _142953) (@lem8052568 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052571 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term192 _142951 _142952 _142953 f g s x y) = (term193 _142951 _142952 _142953 f g s x y)) = ((term188 _142951 _142952 _142953 f g s x y) = (term203 _142951 _142952 _142953 f g s x y)).
Proof. exact (MK_COMB (@lem8052564 _142951 _142952 _142953 f g s x y) (@lem8052570 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052572 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term188 _142951 _142952 _142953 f g s x y) = (term203 _142951 _142952 _142953 f g s x y).
Proof. exact (EQ_MP (@lem8052571 _142951 _142952 _142953 f g s x y) (@lem8052556 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052573 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term190 _142951 _142952 _142953 f g x y) = (term204 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8052572 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052574 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052575 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term191 _142951 _142952 _142953 f g x y) = (term205 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052574 _142951 _142952) (@lem8052573 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052576 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term175 _142951 _142952 _142953 f g x y) = (term205 _142951 _142952 _142953 f g x y).
Proof. exact (TRANS (@lem8052552 _142951 _142952 _142953 f g x y) (@lem8052575 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052578 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term177 _142951 _142952 _142953 f g x y) = (term206 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052577) (@lem8052576 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052582 {A : Type'} (P : A -> Prop) (Q : Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8052583 {_142951 _142952 : Type'} (P : type56 _142951 _142952) (Q : Prop) : (term209 _142951 _142952 P Q) = (term210 _142951 _142952 P Q).
Proof. exact (@lem8052582 (type24 _142951 _142952) P Q). Qed.
Lemma lem8052584 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term211 _142951 _142952 _142953 f x g y) = (term212 _142951 _142952 _142953 f x g y).
Proof. exact (@lem8052583 _142951 _142952 (term127 _142951 _142952 f x) (term128 _142951 _142953 g y)). Qed.
Lemma lem8052585 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term213 _142951 _142952 f x t) = (term120 _142951 _142952 f t x).
Proof. exact (eq_refl (term213 _142951 _142952 f x t)). Qed.
Lemma lem8052586 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term214 _142951 _142952 f x) = (term127 _142951 _142952 f x).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8052585 _142951 _142952 f t x)). Qed.
Lemma lem8052587 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052588 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term215 _142951 _142952 f x) = (term128 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8052587 _142951 _142952) (@lem8052586 _142951 _142952 f x)). Qed.
Lemma lem8052589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052590 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term216 _142951 _142952 f x) = (term132 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8052589) (@lem8052588 _142951 _142952 f x)). Qed.
Lemma lem8052591 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term128 _142951 _142953 g y) = (term128 _142951 _142953 g y).
Proof. exact (eq_refl (term128 _142951 _142953 g y)). Qed.
Lemma lem8052592 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term211 _142951 _142952 _142953 f x g y) = (term134 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052590 _142951 _142952 f x) (@lem8052591 _142951 _142953 g y)). Qed.
Lemma lem8052593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8052594 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term217 _142951 _142952 _142953 f x g y) = (term218 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052593) (@lem8052592 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052595 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term213 _142951 _142952 f x t) = (term120 _142951 _142952 f t x).
Proof. exact (eq_refl (term213 _142951 _142952 f x t)). Qed.
Lemma lem8052596 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052597 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term219 _142951 _142952 f x t) = (term220 _142951 _142952 f t x).
Proof. exact (MK_COMB (@lem8052596) (@lem8052595 _142951 _142952 f t x)). Qed.
Lemma lem8052598 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term128 _142951 _142953 g y) = (term128 _142951 _142953 g y).
Proof. exact (eq_refl (term128 _142951 _142953 g y)). Qed.
Lemma lem8052599 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term221 _142951 _142952 _142953 f x t g y) = (term222 _142951 _142952 _142953 f t x g y).
Proof. exact (MK_COMB (@lem8052597 _142951 _142952 f t x) (@lem8052598 _142951 _142953 g y)). Qed.
Lemma lem8052600 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term223 _142951 _142952 _142953 f x g y) = (term224 _142951 _142952 _142953 f x g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8052599 _142951 _142952 _142953 f t x g y)). Qed.
Lemma lem8052601 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052602 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term212 _142951 _142952 _142953 f x g y) = (term225 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052601 _142951 _142952) (@lem8052600 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052603 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : ((term211 _142951 _142952 _142953 f x g y) = (term212 _142951 _142952 _142953 f x g y)) = ((term134 _142951 _142952 _142953 f x g y) = (term225 _142951 _142952 _142953 f x g y)).
Proof. exact (MK_COMB (@lem8052594 _142951 _142952 _142953 f x g y) (@lem8052602 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052604 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term134 _142951 _142952 _142953 f x g y) = (term225 _142951 _142952 _142953 f x g y).
Proof. exact (EQ_MP (@lem8052603 _142951 _142952 _142953 f x g y) (@lem8052584 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052606 {A : Type'} (P : Prop) (Q : A -> Prop) : (term226 A P Q) = (term227 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8052607 {_142951 _142953 : Type'} (P : Prop) (Q : type56 _142951 _142953) : (term228 _142951 _142953 P Q) = (term229 _142951 _142953 P Q).
Proof. exact (@lem8052606 (type24 _142951 _142953) P Q). Qed.
Lemma lem8052608 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term230 _142951 _142952 _142953 f t x g y) = (term231 _142951 _142952 _142953 f t x g y).
Proof. exact (@lem8052607 _142951 _142953 (term120 _142951 _142952 f t x) (term127 _142951 _142953 g y)). Qed.
Lemma lem8052609 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term213 _142951 _142953 g y t) = (term120 _142951 _142953 g t y).
Proof. exact (eq_refl (term213 _142951 _142953 g y t)). Qed.
Lemma lem8052610 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term214 _142951 _142953 g y) = (term127 _142951 _142953 g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052609 _142951 _142953 g t y)). Qed.
Lemma lem8052611 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052612 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term215 _142951 _142953 g y) = (term128 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8052611 _142951 _142953) (@lem8052610 _142951 _142953 g y)). Qed.
Lemma lem8052613 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term220 _142951 _142952 f t x) = (term220 _142951 _142952 f t x).
Proof. exact (eq_refl (term220 _142951 _142952 f t x)). Qed.
Lemma lem8052614 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term230 _142951 _142952 _142953 f t x g y) = (term222 _142951 _142952 _142953 f t x g y).
Proof. exact (MK_COMB (@lem8052613 _142951 _142952 f t x) (@lem8052612 _142951 _142953 g y)). Qed.
Lemma lem8052615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8052616 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term232 _142951 _142952 _142953 f t x g y) = (term233 _142951 _142952 _142953 f t x g y).
Proof. exact (MK_COMB (@lem8052615) (@lem8052614 _142951 _142952 _142953 f t x g y)). Qed.
Lemma lem8052617 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term213 _142951 _142953 g y t) = (term120 _142951 _142953 g t y).
Proof. exact (eq_refl (term213 _142951 _142953 g y t)). Qed.
Lemma lem8052618 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term220 _142951 _142952 f t x) = (term220 _142951 _142952 f t x).
Proof. exact (eq_refl (term220 _142951 _142952 f t x)). Qed.
Lemma lem8052619 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (t' : type24 _142951 _142953) (y : cart _142951 _142953) : (term234 _142951 _142952 _142953 f t x g y t') = (term235 _142951 _142952 _142953 f t x g t' y).
Proof. exact (MK_COMB (@lem8052618 _142951 _142952 f t x) (@lem8052617 _142951 _142953 g t' y)). Qed.
Lemma lem8052620 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term236 _142951 _142952 _142953 f t x g y) = (term237 _142951 _142952 _142953 f t x g y).
Proof. exact (fun_ext (fun t' : type24 _142951 _142953 => @lem8052619 _142951 _142952 _142953 f t x g t' y)). Qed.
Lemma lem8052621 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052622 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term231 _142951 _142952 _142953 f t x g y) = (term238 _142951 _142952 _142953 f t x g y).
Proof. exact (MK_COMB (@lem8052621 _142951 _142953) (@lem8052620 _142951 _142952 _142953 f t x g y)). Qed.
Lemma lem8052623 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : ((term230 _142951 _142952 _142953 f t x g y) = (term231 _142951 _142952 _142953 f t x g y)) = ((term222 _142951 _142952 _142953 f t x g y) = (term238 _142951 _142952 _142953 f t x g y)).
Proof. exact (MK_COMB (@lem8052616 _142951 _142952 _142953 f t x g y) (@lem8052622 _142951 _142952 _142953 f t x g y)). Qed.
Lemma lem8052624 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term222 _142951 _142952 _142953 f t x g y) = (term238 _142951 _142952 _142953 f t x g y).
Proof. exact (EQ_MP (@lem8052623 _142951 _142952 _142953 f t x g y) (@lem8052608 _142951 _142952 _142953 f t x g y)). Qed.
Lemma lem8052625 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term224 _142951 _142952 _142953 f x g y) = (term239 _142951 _142952 _142953 f x g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8052624 _142951 _142952 _142953 f t x g y)). Qed.
Lemma lem8052626 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052627 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term225 _142951 _142952 _142953 f x g y) = (term240 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052626 _142951 _142952) (@lem8052625 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052628 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term134 _142951 _142952 _142953 f x g y) = (term240 _142951 _142952 _142953 f x g y).
Proof. exact (TRANS (@lem8052604 _142951 _142952 _142953 f x g y) (@lem8052627 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052630 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term169 _142951 _142952 _142953 f x g y) = (term241 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052629) (@lem8052628 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052631 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term167 _142951 _142952 _142953 f g x y) = (term167 _142951 _142952 _142953 f g x y).
Proof. exact (eq_refl (term167 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052632 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term171 _142951 _142952 _142953 f g x y) = (term242 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052630 _142951 _142952 _142953 f x g y) (@lem8052631 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052634 {A : Type'} (P : A -> Prop) (Q : Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8052635 {_142951 _142952 : Type'} (P : type56 _142951 _142952) (Q : Prop) : (term107 _142951 _142952 P Q) = (term108 _142951 _142952 P Q).
Proof. exact (@lem8052634 (type24 _142951 _142952) P Q). Qed.
Lemma lem8052636 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term243 _142951 _142952 _142953 f g x y) = (term244 _142951 _142952 _142953 f g x y).
Proof. exact (@lem8052635 _142951 _142952 (term239 _142951 _142952 _142953 f x g y) (term167 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052637 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term245 _142951 _142952 _142953 f x g y t) = (term238 _142951 _142952 _142953 f t x g y).
Proof. exact (eq_refl (term245 _142951 _142952 _142953 f x g y t)). Qed.
Lemma lem8052638 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term246 _142951 _142952 _142953 f x g y) = (term239 _142951 _142952 _142953 f x g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8052637 _142951 _142952 _142953 f t x g y)). Qed.
Lemma lem8052639 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052640 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term247 _142951 _142952 _142953 f x g y) = (term240 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052639 _142951 _142952) (@lem8052638 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052642 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term248 _142951 _142952 _142953 f x g y) = (term241 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052641) (@lem8052640 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052643 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term167 _142951 _142952 _142953 f g x y) = (term167 _142951 _142952 _142953 f g x y).
Proof. exact (eq_refl (term167 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052644 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term243 _142951 _142952 _142953 f g x y) = (term242 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052642 _142951 _142952 _142953 f x g y) (@lem8052643 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8052646 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term249 _142951 _142952 _142953 f g x y) = (term250 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052645) (@lem8052644 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052647 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term245 _142951 _142952 _142953 f x g y t) = (term238 _142951 _142952 _142953 f t x g y).
Proof. exact (eq_refl (term245 _142951 _142952 _142953 f x g y t)). Qed.
Lemma lem8052648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052649 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term251 _142951 _142952 _142953 f x g y t) = (term252 _142951 _142952 _142953 f t x g y).
Proof. exact (MK_COMB (@lem8052648) (@lem8052647 _142951 _142952 _142953 f t x g y)). Qed.
Lemma lem8052650 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term167 _142951 _142952 _142953 f g x y) = (term167 _142951 _142952 _142953 f g x y).
Proof. exact (eq_refl (term167 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052651 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term253 _142951 _142952 _142953 t f g x y) = (term254 _142951 _142952 _142953 t f g x y).
Proof. exact (MK_COMB (@lem8052649 _142951 _142952 _142953 f t x g y) (@lem8052650 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052652 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term255 _142951 _142952 _142953 f g x y) = (term256 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8052651 _142951 _142952 _142953 t f g x y)). Qed.
Lemma lem8052653 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052654 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term244 _142951 _142952 _142953 f g x y) = (term257 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052653 _142951 _142952) (@lem8052652 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052655 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term243 _142951 _142952 _142953 f g x y) = (term244 _142951 _142952 _142953 f g x y)) = ((term242 _142951 _142952 _142953 f g x y) = (term257 _142951 _142952 _142953 f g x y)).
Proof. exact (MK_COMB (@lem8052646 _142951 _142952 _142953 f g x y) (@lem8052654 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052656 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term242 _142951 _142952 _142953 f g x y) = (term257 _142951 _142952 _142953 f g x y).
Proof. exact (EQ_MP (@lem8052655 _142951 _142952 _142953 f g x y) (@lem8052636 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052658 {A : Type'} (P : A -> Prop) (Q : Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8052659 {_142951 _142953 : Type'} (P : type56 _142951 _142953) (Q : Prop) : (term107 _142951 _142953 P Q) = (term108 _142951 _142953 P Q).
Proof. exact (@lem8052658 (type24 _142951 _142953) P Q). Qed.
Lemma lem8052660 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term258 _142951 _142952 _142953 t f g x y) = (term259 _142951 _142952 _142953 t f g x y).
Proof. exact (@lem8052659 _142951 _142953 (term237 _142951 _142952 _142953 f t x g y) (term167 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052661 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (t' : type24 _142951 _142953) (y : cart _142951 _142953) : (term260 _142951 _142952 _142953 f t x g y t') = (term235 _142951 _142952 _142953 f t x g t' y).
Proof. exact (eq_refl (term260 _142951 _142952 _142953 f t x g y t')). Qed.
Lemma lem8052662 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term261 _142951 _142952 _142953 f t x g y) = (term237 _142951 _142952 _142953 f t x g y).
Proof. exact (fun_ext (fun t' : type24 _142951 _142953 => @lem8052661 _142951 _142952 _142953 f t x g t' y)). Qed.
Lemma lem8052663 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052664 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term262 _142951 _142952 _142953 f t x g y) = (term238 _142951 _142952 _142953 f t x g y).
Proof. exact (MK_COMB (@lem8052663 _142951 _142953) (@lem8052662 _142951 _142952 _142953 f t x g y)). Qed.
Lemma lem8052665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052666 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term263 _142951 _142952 _142953 f t x g y) = (term252 _142951 _142952 _142953 f t x g y).
Proof. exact (MK_COMB (@lem8052665) (@lem8052664 _142951 _142952 _142953 f t x g y)). Qed.
Lemma lem8052667 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term167 _142951 _142952 _142953 f g x y) = (term167 _142951 _142952 _142953 f g x y).
Proof. exact (eq_refl (term167 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052668 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term258 _142951 _142952 _142953 t f g x y) = (term254 _142951 _142952 _142953 t f g x y).
Proof. exact (MK_COMB (@lem8052666 _142951 _142952 _142953 f t x g y) (@lem8052667 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8052670 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term264 _142951 _142952 _142953 t f g x y) = (term265 _142951 _142952 _142953 t f g x y).
Proof. exact (MK_COMB (@lem8052669) (@lem8052668 _142951 _142952 _142953 t f g x y)). Qed.
Lemma lem8052671 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (t' : type24 _142951 _142953) (y : cart _142951 _142953) : (term260 _142951 _142952 _142953 f t x g y t') = (term235 _142951 _142952 _142953 f t x g t' y).
Proof. exact (eq_refl (term260 _142951 _142952 _142953 f t x g y t')). Qed.
Lemma lem8052672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052673 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (t' : type24 _142951 _142953) (y : cart _142951 _142953) : (term266 _142951 _142952 _142953 f t x g y t') = (term267 _142951 _142952 _142953 f t x g t' y).
Proof. exact (MK_COMB (@lem8052672) (@lem8052671 _142951 _142952 _142953 f t x g t' y)). Qed.
Lemma lem8052674 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term167 _142951 _142952 _142953 f g x y) = (term167 _142951 _142952 _142953 f g x y).
Proof. exact (eq_refl (term167 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052675 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142952) (t' : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term268 _142951 _142952 _142953 t t' f g x y) = (term269 _142951 _142952 _142953 t t' f g x y).
Proof. exact (MK_COMB (@lem8052673 _142951 _142952 _142953 f t x g t' y) (@lem8052674 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052676 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term270 _142951 _142952 _142953 t f g x y) = (term271 _142951 _142952 _142953 t f g x y).
Proof. exact (fun_ext (fun t' : type24 _142951 _142953 => @lem8052675 _142951 _142952 _142953 t t' f g x y)). Qed.
Lemma lem8052677 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052678 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term259 _142951 _142952 _142953 t f g x y) = (term272 _142951 _142952 _142953 t f g x y).
Proof. exact (MK_COMB (@lem8052677 _142951 _142953) (@lem8052676 _142951 _142952 _142953 t f g x y)). Qed.
Lemma lem8052679 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term258 _142951 _142952 _142953 t f g x y) = (term259 _142951 _142952 _142953 t f g x y)) = ((term254 _142951 _142952 _142953 t f g x y) = (term272 _142951 _142952 _142953 t f g x y)).
Proof. exact (MK_COMB (@lem8052670 _142951 _142952 _142953 t f g x y) (@lem8052678 _142951 _142952 _142953 t f g x y)). Qed.
Lemma lem8052680 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term254 _142951 _142952 _142953 t f g x y) = (term272 _142951 _142952 _142953 t f g x y).
Proof. exact (EQ_MP (@lem8052679 _142951 _142952 _142953 t f g x y) (@lem8052660 _142951 _142952 _142953 t f g x y)). Qed.
Lemma lem8052681 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term256 _142951 _142952 _142953 f g x y) = (term273 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8052680 _142951 _142952 _142953 t f g x y)). Qed.
Lemma lem8052682 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052683 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term257 _142951 _142952 _142953 f g x y) = (term274 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052682 _142951 _142952) (@lem8052681 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052684 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term242 _142951 _142952 _142953 f g x y) = (term274 _142951 _142952 _142953 f g x y).
Proof. exact (TRANS (@lem8052656 _142951 _142952 _142953 f g x y) (@lem8052683 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052685 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term171 _142951 _142952 _142953 f g x y) = (term274 _142951 _142952 _142953 f g x y).
Proof. exact (TRANS (@lem8052632 _142951 _142952 _142953 f g x y) (@lem8052684 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052686 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term179 _142951 _142952 _142953 f g x y) = (term275 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052578 _142951 _142952 _142953 f g x y) (@lem8052685 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052688 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8052689 {_142951 _142952 : Type'} (P : type56 _142951 _142952) (Q : type56 _142951 _142952) : (term278 _142951 _142952 P Q) = (term279 _142951 _142952 P Q).
Proof. exact (@lem8052688 (type24 _142951 _142952) P Q). Qed.
Lemma lem8052690 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term280 _142951 _142952 _142953 f g x y) = (term281 _142951 _142952 _142953 f g x y).
Proof. exact (@lem8052689 _142951 _142952 (term204 _142951 _142952 _142953 f g x y) (term273 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052691 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term282 _142951 _142952 _142953 f g x y s) = (term203 _142951 _142952 _142953 f g s x y).
Proof. exact (eq_refl (term282 _142951 _142952 _142953 f g x y s)). Qed.
Lemma lem8052692 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term283 _142951 _142952 _142953 f g x y) = (term204 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8052691 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052693 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052694 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term284 _142951 _142952 _142953 f g x y) = (term205 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052693 _142951 _142952) (@lem8052692 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052696 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term285 _142951 _142952 _142953 f g x y) = (term206 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052695) (@lem8052694 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052697 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term286 _142951 _142952 _142953 f g x y s) = (term272 _142951 _142952 _142953 s f g x y).
Proof. exact (eq_refl (term286 _142951 _142952 _142953 f g x y s)). Qed.
Lemma lem8052698 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term287 _142951 _142952 _142953 f g x y) = (term273 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8052697 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052699 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052700 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term288 _142951 _142952 _142953 f g x y) = (term274 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052699 _142951 _142952) (@lem8052698 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052701 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term280 _142951 _142952 _142953 f g x y) = (term275 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052696 _142951 _142952 _142953 f g x y) (@lem8052700 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8052703 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term289 _142951 _142952 _142953 f g x y) = (term290 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052702) (@lem8052701 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052704 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term282 _142951 _142952 _142953 f g x y s) = (term203 _142951 _142952 _142953 f g s x y).
Proof. exact (eq_refl (term282 _142951 _142952 _142953 f g x y s)). Qed.
Lemma lem8052705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052706 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term291 _142951 _142952 _142953 f g x y s) = (term292 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052705) (@lem8052704 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052707 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term286 _142951 _142952 _142953 f g x y s) = (term272 _142951 _142952 _142953 s f g x y).
Proof. exact (eq_refl (term286 _142951 _142952 _142953 f g x y s)). Qed.
Lemma lem8052708 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term293 _142951 _142952 _142953 f g x y s) = (term294 _142951 _142952 _142953 s f g x y).
Proof. exact (MK_COMB (@lem8052706 _142951 _142952 _142953 f g s x y) (@lem8052707 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052709 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term295 _142951 _142952 _142953 f g x y) = (term296 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8052708 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052710 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052711 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term281 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052710 _142951 _142952) (@lem8052709 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052712 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term280 _142951 _142952 _142953 f g x y) = (term281 _142951 _142952 _142953 f g x y)) = ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y)).
Proof. exact (MK_COMB (@lem8052703 _142951 _142952 _142953 f g x y) (@lem8052711 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052713 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y).
Proof. exact (EQ_MP (@lem8052712 _142951 _142952 _142953 f g x y) (@lem8052690 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052716 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term298 _142951 _142952 _142953 f g x y) = (term298 _142951 _142952 _142953 f g x y).
Proof. exact (eq_refl (term298 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052717 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term298 _142951 _142952 _142953 f g x y) = ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y)).
Proof. exact (eq_refl (term298 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052718 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term299 _142951 _142952 _142953 f g x y) = (term299 _142951 _142952 _142953 f g x y).
Proof. exact (eq_refl (term299 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052719 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term298 _142951 _142952 _142953 f g x y) = (term298 _142951 _142952 _142953 f g x y)) = ((term298 _142951 _142952 _142953 f g x y) = ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y))).
Proof. exact (MK_COMB (@lem8052718 _142951 _142952 _142953 f g x y) (@lem8052717 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052720 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term298 _142951 _142952 _142953 f g x y) = ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y)).
Proof. exact (eq_refl (term298 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8052722 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term299 _142951 _142952 _142953 f g x y) = (term300 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052721) (@lem8052720 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052723 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y)) = ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y)).
Proof. exact (eq_refl ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y))). Qed.
Lemma lem8052724 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term298 _142951 _142952 _142953 f g x y) = ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y))) = (((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y)) = ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y))).
Proof. exact (MK_COMB (@lem8052722 _142951 _142952 _142953 f g x y) (@lem8052723 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052725 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term298 _142951 _142952 _142953 f g x y) = (term298 _142951 _142952 _142953 f g x y)) = (((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y)) = ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y))).
Proof. exact (TRANS (@lem8052719 _142951 _142952 _142953 f g x y) (@lem8052724 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052726 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y)) = ((term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y)).
Proof. exact (EQ_MP (@lem8052725 _142951 _142952 _142953 f g x y) (@lem8052716 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052727 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term275 _142951 _142952 _142953 f g x y) = (term297 _142951 _142952 _142953 f g x y).
Proof. exact (EQ_MP (@lem8052726 _142951 _142952 _142953 f g x y) (@lem8052713 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052729 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8052730 {_142951 _142953 : Type'} (P : type56 _142951 _142953) (Q : type56 _142951 _142953) : (term278 _142951 _142953 P Q) = (term279 _142951 _142953 P Q).
Proof. exact (@lem8052729 (type24 _142951 _142953) P Q). Qed.
Lemma lem8052731 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term301 _142951 _142952 _142953 s f g x y) = (term302 _142951 _142952 _142953 s f g x y).
Proof. exact (@lem8052730 _142951 _142953 (term202 _142951 _142952 _142953 f g s x y) (term271 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052732 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term303 _142951 _142952 _142953 f g s x y t) = (term200 _142951 _142952 _142953 f g s x t y).
Proof. exact (eq_refl (term303 _142951 _142952 _142953 f g s x y t)). Qed.
Lemma lem8052733 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term304 _142951 _142952 _142953 f g s x y) = (term202 _142951 _142952 _142953 f g s x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052732 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052734 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052735 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term305 _142951 _142952 _142953 f g s x y) = (term203 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052734 _142951 _142953) (@lem8052733 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052737 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term306 _142951 _142952 _142953 f g s x y) = (term292 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052736) (@lem8052735 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052738 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term307 _142951 _142952 _142953 s f g x y t) = (term269 _142951 _142952 _142953 s t f g x y).
Proof. exact (eq_refl (term307 _142951 _142952 _142953 s f g x y t)). Qed.
Lemma lem8052739 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term308 _142951 _142952 _142953 s f g x y) = (term271 _142951 _142952 _142953 s f g x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052738 _142951 _142952 _142953 s t f g x y)). Qed.
Lemma lem8052740 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052741 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term309 _142951 _142952 _142953 s f g x y) = (term272 _142951 _142952 _142953 s f g x y).
Proof. exact (MK_COMB (@lem8052740 _142951 _142953) (@lem8052739 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052742 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term301 _142951 _142952 _142953 s f g x y) = (term294 _142951 _142952 _142953 s f g x y).
Proof. exact (MK_COMB (@lem8052737 _142951 _142952 _142953 f g s x y) (@lem8052741 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8052744 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term310 _142951 _142952 _142953 s f g x y) = (term311 _142951 _142952 _142953 s f g x y).
Proof. exact (MK_COMB (@lem8052743) (@lem8052742 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052745 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term303 _142951 _142952 _142953 f g s x y t) = (term200 _142951 _142952 _142953 f g s x t y).
Proof. exact (eq_refl (term303 _142951 _142952 _142953 f g s x y t)). Qed.
Lemma lem8052746 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052747 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term312 _142951 _142952 _142953 f g s x y t) = (term313 _142951 _142952 _142953 f g s x t y).
Proof. exact (MK_COMB (@lem8052746) (@lem8052745 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052748 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term307 _142951 _142952 _142953 s f g x y t) = (term269 _142951 _142952 _142953 s t f g x y).
Proof. exact (eq_refl (term307 _142951 _142952 _142953 s f g x y t)). Qed.
Lemma lem8052749 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term314 _142951 _142952 _142953 s f g x y t) = (term315 _142951 _142952 _142953 s t f g x y).
Proof. exact (MK_COMB (@lem8052747 _142951 _142952 _142953 f g s x t y) (@lem8052748 _142951 _142952 _142953 s t f g x y)). Qed.
Lemma lem8052750 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term316 _142951 _142952 _142953 s f g x y) = (term317 _142951 _142952 _142953 s f g x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052749 _142951 _142952 _142953 s t f g x y)). Qed.
Lemma lem8052751 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052752 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term302 _142951 _142952 _142953 s f g x y) = (term318 _142951 _142952 _142953 s f g x y).
Proof. exact (MK_COMB (@lem8052751 _142951 _142953) (@lem8052750 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052753 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term301 _142951 _142952 _142953 s f g x y) = (term302 _142951 _142952 _142953 s f g x y)) = ((term294 _142951 _142952 _142953 s f g x y) = (term318 _142951 _142952 _142953 s f g x y)).
Proof. exact (MK_COMB (@lem8052744 _142951 _142952 _142953 s f g x y) (@lem8052752 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052754 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term294 _142951 _142952 _142953 s f g x y) = (term318 _142951 _142952 _142953 s f g x y).
Proof. exact (EQ_MP (@lem8052753 _142951 _142952 _142953 s f g x y) (@lem8052731 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052755 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term296 _142951 _142952 _142953 f g x y) = (term319 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8052754 _142951 _142952 _142953 s f g x y)). Qed.
Lemma lem8052756 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052757 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term297 _142951 _142952 _142953 f g x y) = (term320 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052756 _142951 _142952) (@lem8052755 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052758 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term275 _142951 _142952 _142953 f g x y) = (term320 _142951 _142952 _142953 f g x y).
Proof. exact (TRANS (@lem8052727 _142951 _142952 _142953 f g x y) (@lem8052757 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052760 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term179 _142951 _142952 _142953 f g x y) = (term320 _142951 _142952 _142953 f g x y).
Proof. exact (TRANS (@lem8052686 _142951 _142952 _142953 f g x y) (@lem8052758 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052761 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term93 _142951 _142952 _142953 f g x y) = (term320 _142951 _142952 _142953 f g x y).
Proof. exact (TRANS (@lem8052275 _142951 _142952 _142953 f g x y) (@lem8052760 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052762 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term93 _142951 _142952 _142953 f g x y) : term320 _142951 _142952 _142953 f g x y.
Proof. exact (EQ_MP (@lem8052761 _142951 _142952 _142953 f g x y) (@lem8052089 _142951 _142952 _142953 f g x y h1)). Qed.
Lemma lem8052763 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term318 _142951 _142952 _142953 s f g x y) : term318 _142951 _142952 _142953 s f g x y.
Proof. exact (h1). Qed.
Lemma lem8052764 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term315 _142951 _142952 _142953 s t f g x y) : term315 _142951 _142952 _142953 s t f g x y.
Proof. exact (h1). Qed.
Lemma lem8052765 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (h1 : term115 _142951 _142952 _142953 g x' f) : term115 _142951 _142952 _142953 g x' f.
Proof. exact (h1). Qed.
Lemma lem8052766 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) (h1 : term321 _142951 _142952 _142953 g x' f x'') : term321 _142951 _142952 _142953 g x' f x''.
Proof. exact (h1). Qed.
Lemma lem8052771 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052772 {_142951 _142953 : Type'} (f : type24 _142951 _142953) (x : cart _142951 _142953) : (f x) = (@I ((cart _142951 _142953) -> Prop) f x).
Proof. exact (@lem8052771 (cart _142951 _142953) Prop f x). Qed.
Lemma lem8052774 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (t y) = (@I ((cart _142951 _142953) -> Prop) t y).
Proof. exact (@lem8052772 _142951 _142953 t y). Qed.
Lemma lem8052779 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052780 {_142951 _142952 : Type'} (f : type24 _142951 _142952) (x : cart _142951 _142952) : (f x) = (@I ((cart _142951 _142952) -> Prop) f x).
Proof. exact (@lem8052779 (cart _142951 _142952) Prop f x). Qed.
Lemma lem8052782 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (s x) = (@I ((cart _142951 _142952) -> Prop) s x).
Proof. exact (@lem8052780 _142951 _142952 s x). Qed.
Lemma lem8052783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052784 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term55 _142951 _142952 s x) = (term322 _142951 _142952 s x).
Proof. exact (MK_COMB (@lem8052783) (@lem8052782 _142951 _142952 s x)). Qed.
Lemma lem8052785 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term57 _142951 _142952 _142953 s x t y) = (term323 _142951 _142952 _142953 s x t y).
Proof. exact (MK_COMB (@lem8052784 _142951 _142952 s x) (@lem8052774 _142951 _142953 t y)). Qed.
Lemma lem8052786 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052791 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052792 {_142951 _142953 : Type'} (f : type56 _142951 _142953) (x : type24 _142951 _142953) : (f x) = (@I (((cart _142951 _142953) -> Prop) -> Prop) f x).
Proof. exact (@lem8052791 (type24 _142951 _142953) Prop f x). Qed.
Lemma lem8052794 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (g t) = (@I (((cart _142951 _142953) -> Prop) -> Prop) g t).
Proof. exact (@lem8052792 _142951 _142953 g t). Qed.
Lemma lem8052795 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term23 _142951 _142953 g t) = (term324 _142951 _142953 g t).
Proof. exact (MK_COMB (@lem8052786) (@lem8052794 _142951 _142953 g t)). Qed.
Lemma lem8052796 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052801 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052802 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (f x) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f x).
Proof. exact (@lem8052801 (type24 _142951 _142952) Prop f x). Qed.
Lemma lem8052804 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (f s) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f s).
Proof. exact (@lem8052802 _142951 _142952 f s). Qed.
Lemma lem8052805 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (term23 _142951 _142952 f s) = (term324 _142951 _142952 f s).
Proof. exact (MK_COMB (@lem8052796) (@lem8052804 _142951 _142952 f s)). Qed.
Lemma lem8052806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052807 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (term325 _142951 _142952 f s) = (term326 _142951 _142952 f s).
Proof. exact (MK_COMB (@lem8052806) (@lem8052805 _142951 _142952 f s)). Qed.
Lemma lem8052808 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term139 _142951 _142952 _142953 f s g t) = (term327 _142951 _142952 _142953 f s g t).
Proof. exact (MK_COMB (@lem8052807 _142951 _142952 f s) (@lem8052795 _142951 _142953 g t)). Qed.
Lemma lem8052809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052810 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term147 _142951 _142952 _142953 f s g t) = (term328 _142951 _142952 _142953 f s g t).
Proof. exact (MK_COMB (@lem8052809) (@lem8052808 _142951 _142952 _142953 f s g t)). Qed.
Lemma lem8052811 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term149 _142951 _142952 _142953 f g s x t y) = (term329 _142951 _142952 _142953 f g s x t y).
Proof. exact (MK_COMB (@lem8052810 _142951 _142952 _142953 f s g t) (@lem8052785 _142951 _142952 _142953 s x t y)). Qed.
Lemma lem8052812 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term157 _142951 _142952 _142953 f g s x y) = (term330 _142951 _142952 _142953 f g s x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052811 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052813 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052814 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term158 _142951 _142952 _142953 f g s x y) = (term331 _142951 _142952 _142953 f g s x y).
Proof. exact (MK_COMB (@lem8052813 _142951 _142953) (@lem8052812 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052815 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term166 _142951 _142952 _142953 f g x y) = (term332 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8052814 _142951 _142952 _142953 f g s x y)). Qed.
Lemma lem8052816 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052817 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term167 _142951 _142952 _142953 f g x y) = (term333 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8052816 _142951 _142952) (@lem8052815 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052818 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052823 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052824 {_142951 _142953 : Type'} (f : type24 _142951 _142953) (x : cart _142951 _142953) : (f x) = (@I ((cart _142951 _142953) -> Prop) f x).
Proof. exact (@lem8052823 (cart _142951 _142953) Prop f x). Qed.
Lemma lem8052826 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (t y) = (@I ((cart _142951 _142953) -> Prop) t y).
Proof. exact (@lem8052824 _142951 _142953 t y). Qed.
Lemma lem8052827 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term334 _142951 _142953 t y) = (term335 _142951 _142953 t y).
Proof. exact (MK_COMB (@lem8052818) (@lem8052826 _142951 _142953 t y)). Qed.
Lemma lem8052832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052833 {_142951 _142953 : Type'} (f : type56 _142951 _142953) (x : type24 _142951 _142953) : (f x) = (@I (((cart _142951 _142953) -> Prop) -> Prop) f x).
Proof. exact (@lem8052832 (type24 _142951 _142953) Prop f x). Qed.
Lemma lem8052835 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (g t) = (@I (((cart _142951 _142953) -> Prop) -> Prop) g t).
Proof. exact (@lem8052833 _142951 _142953 g t). Qed.
Lemma lem8052836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052837 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term49 _142951 _142953 g t) = (term336 _142951 _142953 g t).
Proof. exact (MK_COMB (@lem8052836) (@lem8052835 _142951 _142953 g t)). Qed.
Lemma lem8052838 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term120 _142951 _142953 g t y) = (term337 _142951 _142953 g t y).
Proof. exact (MK_COMB (@lem8052837 _142951 _142953 g t) (@lem8052827 _142951 _142953 t y)). Qed.
Lemma lem8052839 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052844 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052845 {_142951 _142952 : Type'} (f : type24 _142951 _142952) (x : cart _142951 _142952) : (f x) = (@I ((cart _142951 _142952) -> Prop) f x).
Proof. exact (@lem8052844 (cart _142951 _142952) Prop f x). Qed.
Lemma lem8052847 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (s x) = (@I ((cart _142951 _142952) -> Prop) s x).
Proof. exact (@lem8052845 _142951 _142952 s x). Qed.
Lemma lem8052848 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term334 _142951 _142952 s x) = (term335 _142951 _142952 s x).
Proof. exact (MK_COMB (@lem8052839) (@lem8052847 _142951 _142952 s x)). Qed.
Lemma lem8052853 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052854 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (f x) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f x).
Proof. exact (@lem8052853 (type24 _142951 _142952) Prop f x). Qed.
Lemma lem8052856 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (f s) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f s).
Proof. exact (@lem8052854 _142951 _142952 f s). Qed.
Lemma lem8052857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052858 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (term49 _142951 _142952 f s) = (term336 _142951 _142952 f s).
Proof. exact (MK_COMB (@lem8052857) (@lem8052856 _142951 _142952 f s)). Qed.
Lemma lem8052859 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term120 _142951 _142952 f s x) = (term337 _142951 _142952 f s x).
Proof. exact (MK_COMB (@lem8052858 _142951 _142952 f s) (@lem8052848 _142951 _142952 s x)). Qed.
Lemma lem8052860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052861 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term220 _142951 _142952 f s x) = (term338 _142951 _142952 f s x).
Proof. exact (MK_COMB (@lem8052860) (@lem8052859 _142951 _142952 f s x)). Qed.
Lemma lem8052862 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term235 _142951 _142952 _142953 f s x g t y) = (term339 _142951 _142952 _142953 f s x g t y).
Proof. exact (MK_COMB (@lem8052861 _142951 _142952 f s x) (@lem8052838 _142951 _142953 g t y)). Qed.
Lemma lem8052863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052864 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term267 _142951 _142952 _142953 f s x g t y) = (term340 _142951 _142952 _142953 f s x g t y).
Proof. exact (MK_COMB (@lem8052863) (@lem8052862 _142951 _142952 _142953 f s x g t y)). Qed.
Lemma lem8052865 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term269 _142951 _142952 _142953 s t f g x y) = (term341 _142951 _142952 _142953 s t f g x y).
Proof. exact (MK_COMB (@lem8052864 _142951 _142952 _142953 f s x g t y) (@lem8052817 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8052866 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052871 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052872 {_142951 _142953 : Type'} (f : type24 _142951 _142953) (x : cart _142951 _142953) : (f x) = (@I ((cart _142951 _142953) -> Prop) f x).
Proof. exact (@lem8052871 (cart _142951 _142953) Prop f x). Qed.
Lemma lem8052874 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (t y) = (@I ((cart _142951 _142953) -> Prop) t y).
Proof. exact (@lem8052872 _142951 _142953 t y). Qed.
Lemma lem8052875 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term334 _142951 _142953 t y) = (term335 _142951 _142953 t y).
Proof. exact (MK_COMB (@lem8052866) (@lem8052874 _142951 _142953 t y)). Qed.
Lemma lem8052876 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052881 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052882 {_142951 _142952 : Type'} (f : type24 _142951 _142952) (x : cart _142951 _142952) : (f x) = (@I ((cart _142951 _142952) -> Prop) f x).
Proof. exact (@lem8052881 (cart _142951 _142952) Prop f x). Qed.
Lemma lem8052884 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (s x) = (@I ((cart _142951 _142952) -> Prop) s x).
Proof. exact (@lem8052882 _142951 _142952 s x). Qed.
Lemma lem8052885 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term334 _142951 _142952 s x) = (term335 _142951 _142952 s x).
Proof. exact (MK_COMB (@lem8052876) (@lem8052884 _142951 _142952 s x)). Qed.
Lemma lem8052886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052887 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term342 _142951 _142952 s x) = (term343 _142951 _142952 s x).
Proof. exact (MK_COMB (@lem8052886) (@lem8052885 _142951 _142952 s x)). Qed.
Lemma lem8052888 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term141 _142951 _142952 _142953 s x t y) = (term344 _142951 _142952 _142953 s x t y).
Proof. exact (MK_COMB (@lem8052887 _142951 _142952 s x) (@lem8052875 _142951 _142953 t y)). Qed.
Lemma lem8052893 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052894 {_142951 _142953 : Type'} (f : type56 _142951 _142953) (x : type24 _142951 _142953) : (f x) = (@I (((cart _142951 _142953) -> Prop) -> Prop) f x).
Proof. exact (@lem8052893 (type24 _142951 _142953) Prop f x). Qed.
Lemma lem8052896 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (g t) = (@I (((cart _142951 _142953) -> Prop) -> Prop) g t).
Proof. exact (@lem8052894 _142951 _142953 g t). Qed.
Lemma lem8052901 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052902 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (f x) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f x).
Proof. exact (@lem8052901 (type24 _142951 _142952) Prop f x). Qed.
Lemma lem8052904 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (f s) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f s).
Proof. exact (@lem8052902 _142951 _142952 f s). Qed.
Lemma lem8052905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052906 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (term49 _142951 _142952 f s) = (term336 _142951 _142952 f s).
Proof. exact (MK_COMB (@lem8052905) (@lem8052904 _142951 _142952 f s)). Qed.
Lemma lem8052907 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term51 _142951 _142952 _142953 f s g t) = (term345 _142951 _142952 _142953 f s g t).
Proof. exact (MK_COMB (@lem8052906 _142951 _142952 f s) (@lem8052896 _142951 _142953 g t)). Qed.
Lemma lem8052908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052909 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term142 _142951 _142952 _142953 f s g t) = (term346 _142951 _142952 _142953 f s g t).
Proof. exact (MK_COMB (@lem8052908) (@lem8052907 _142951 _142952 _142953 f s g t)). Qed.
Lemma lem8052910 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term144 _142951 _142952 _142953 f g s x t y) = (term347 _142951 _142952 _142953 f g s x t y).
Proof. exact (MK_COMB (@lem8052909 _142951 _142952 _142953 f s g t) (@lem8052888 _142951 _142952 _142953 s x t y)). Qed.
Lemma lem8052915 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052916 {_142951 _142953 : Type'} (f : type24 _142951 _142953) (x : cart _142951 _142953) : (f x) = (@I ((cart _142951 _142953) -> Prop) f x).
Proof. exact (@lem8052915 (cart _142951 _142953) Prop f x). Qed.
Lemma lem8052918 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (t y) = (@I ((cart _142951 _142953) -> Prop) t y).
Proof. exact (@lem8052916 _142951 _142953 t y). Qed.
Lemma lem8052919 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052924 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052925 {_142951 _142953 : Type'} (f : type56 _142951 _142953) (x : type24 _142951 _142953) : (f x) = (@I (((cart _142951 _142953) -> Prop) -> Prop) f x).
Proof. exact (@lem8052924 (type24 _142951 _142953) Prop f x). Qed.
Lemma lem8052927 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (g t) = (@I (((cart _142951 _142953) -> Prop) -> Prop) g t).
Proof. exact (@lem8052925 _142951 _142953 g t). Qed.
Lemma lem8052928 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term23 _142951 _142953 g t) = (term324 _142951 _142953 g t).
Proof. exact (MK_COMB (@lem8052919) (@lem8052927 _142951 _142953 g t)). Qed.
Lemma lem8052929 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052930 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term325 _142951 _142953 g t) = (term326 _142951 _142953 g t).
Proof. exact (MK_COMB (@lem8052929) (@lem8052928 _142951 _142953 g t)). Qed.
Lemma lem8052931 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term121 _142951 _142953 g t y) = (term348 _142951 _142953 g t y).
Proof. exact (MK_COMB (@lem8052930 _142951 _142953 g t) (@lem8052918 _142951 _142953 t y)). Qed.
Lemma lem8052932 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term129 _142951 _142953 g y) = (term349 _142951 _142953 g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8052931 _142951 _142953 g t y)). Qed.
Lemma lem8052933 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8052934 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term130 _142951 _142953 g y) = (term350 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8052933 _142951 _142953) (@lem8052932 _142951 _142953 g y)). Qed.
Lemma lem8052939 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052940 {_142951 _142952 : Type'} (f : type24 _142951 _142952) (x : cart _142951 _142952) : (f x) = (@I ((cart _142951 _142952) -> Prop) f x).
Proof. exact (@lem8052939 (cart _142951 _142952) Prop f x). Qed.
Lemma lem8052942 {_142951 _142952 : Type'} (t : type24 _142951 _142952) (x : cart _142951 _142952) : (t x) = (@I ((cart _142951 _142952) -> Prop) t x).
Proof. exact (@lem8052940 _142951 _142952 t x). Qed.
Lemma lem8052943 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8052948 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052949 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (f x) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f x).
Proof. exact (@lem8052948 (type24 _142951 _142952) Prop f x). Qed.
Lemma lem8052951 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) : (f t) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f t).
Proof. exact (@lem8052949 _142951 _142952 f t). Qed.
Lemma lem8052952 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) : (term23 _142951 _142952 f t) = (term324 _142951 _142952 f t).
Proof. exact (MK_COMB (@lem8052943) (@lem8052951 _142951 _142952 f t)). Qed.
Lemma lem8052953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052954 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) : (term325 _142951 _142952 f t) = (term326 _142951 _142952 f t).
Proof. exact (MK_COMB (@lem8052953) (@lem8052952 _142951 _142952 f t)). Qed.
Lemma lem8052955 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term121 _142951 _142952 f t x) = (term348 _142951 _142952 f t x).
Proof. exact (MK_COMB (@lem8052954 _142951 _142952 f t) (@lem8052942 _142951 _142952 t x)). Qed.
Lemma lem8052956 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term129 _142951 _142952 f x) = (term349 _142951 _142952 f x).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8052955 _142951 _142952 f t x)). Qed.
Lemma lem8052957 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8052958 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term130 _142951 _142952 f x) = (term350 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8052957 _142951 _142952) (@lem8052956 _142951 _142952 f x)). Qed.
Lemma lem8052959 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052960 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term136 _142951 _142952 f x) = (term351 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8052959) (@lem8052958 _142951 _142952 f x)). Qed.
Lemma lem8052961 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term137 _142951 _142952 _142953 f x g y) = (term352 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052960 _142951 _142952 f x) (@lem8052934 _142951 _142953 g y)). Qed.
Lemma lem8052962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052963 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term173 _142951 _142952 _142953 f x g y) = (term353 _142951 _142952 _142953 f x g y).
Proof. exact (MK_COMB (@lem8052962) (@lem8052961 _142951 _142952 _142953 f x g y)). Qed.
Lemma lem8052964 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term200 _142951 _142952 _142953 f g s x t y) = (term354 _142951 _142952 _142953 f g s x t y).
Proof. exact (MK_COMB (@lem8052963 _142951 _142952 _142953 f x g y) (@lem8052910 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8052966 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term313 _142951 _142952 _142953 f g s x t y) = (term355 _142951 _142952 _142953 f g s x t y).
Proof. exact (MK_COMB (@lem8052965) (@lem8052964 _142951 _142952 _142953 f g s x t y)). Qed.
Lemma lem8052967 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term315 _142951 _142952 _142953 s t f g x y) = (term356 _142951 _142952 _142953 s t f g x y).
Proof. exact (MK_COMB (@lem8052966 _142951 _142952 _142953 f g s x t y) (@lem8052865 _142951 _142952 _142953 s t f g x y)). Qed.
Lemma lem8052968 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term315 _142951 _142952 _142953 s t f g x y) : term356 _142951 _142952 _142953 s t f g x y.
Proof. exact (EQ_MP (@lem8052967 _142951 _142952 _142953 s t f g x y) (@lem8052764 _142951 _142952 _142953 s t f g x y h1)). Qed.
Lemma lem8052973 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052974 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (f x) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f x).
Proof. exact (@lem8052973 (type24 _142951 _142952) Prop f x). Qed.
Lemma lem8052976 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) : (f x'') = (@I (((cart _142951 _142952) -> Prop) -> Prop) f x'').
Proof. exact (@lem8052974 _142951 _142952 f x''). Qed.
Lemma lem8052981 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8052982 {_142951 _142953 : Type'} (f : type56 _142951 _142953) (x : type24 _142951 _142953) : (f x) = (@I (((cart _142951 _142953) -> Prop) -> Prop) f x).
Proof. exact (@lem8052981 (type24 _142951 _142953) Prop f x). Qed.
Lemma lem8052984 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) : (g x') = (@I (((cart _142951 _142953) -> Prop) -> Prop) g x').
Proof. exact (@lem8052982 _142951 _142953 g x'). Qed.
Lemma lem8052985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8052986 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) : (term49 _142951 _142953 g x') = (term336 _142951 _142953 g x').
Proof. exact (MK_COMB (@lem8052985) (@lem8052984 _142951 _142953 g x')). Qed.
Lemma lem8052987 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) : (term321 _142951 _142952 _142953 g x' f x'') = (term357 _142951 _142952 _142953 g x' f x'').
Proof. exact (MK_COMB (@lem8052986 _142951 _142953 g x') (@lem8052976 _142951 _142952 f x'')). Qed.
Lemma lem8052988 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) (h1 : term321 _142951 _142952 _142953 g x' f x'') : term357 _142951 _142952 _142953 g x' f x''.
Proof. exact (EQ_MP (@lem8052987 _142951 _142952 _142953 g x' f x'') (@lem8052766 _142951 _142952 _142953 g x' f x'' h1)). Qed.
Lemma lem8052991 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term354 _142951 _142952 _142953 f g s x t y.
Proof. exact (h1). Qed.
Lemma lem8052992 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term341 _142951 _142952 _142953 s t f g x y.
Proof. exact (h1). Qed.
Lemma lem8052993 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term347 _142951 _142952 _142953 f g s x t y.
Proof. exact (proj2 (@lem8052991 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8052994 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term352 _142951 _142952 _142953 f x g y.
Proof. exact (proj1 (@lem8052991 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8052995 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term344 _142951 _142952 _142953 s x t y.
Proof. exact (proj2 (@lem8052993 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8052996 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term345 _142951 _142952 _142953 f s g t.
Proof. exact (proj1 (@lem8052993 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8052999 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term350 _142951 _142953 g y.
Proof. exact (proj2 (@lem8052994 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053000 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term350 _142951 _142952 f x.
Proof. exact (proj1 (@lem8052994 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053003 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term333 _142951 _142952 _142953 f g x y.
Proof. exact (proj2 (@lem8052992 _142951 _142952 _142953 s t f g x y h1)). Qed.
Lemma lem8053004 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term339 _142951 _142952 _142953 f s x g t y.
Proof. exact (proj1 (@lem8052992 _142951 _142952 _142953 s t f g x y h1)). Qed.
Lemma lem8053005 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) (h1 : term337 _142951 _142952 f s x) : term337 _142951 _142952 f s x.
Proof. exact (h1). Qed.
Lemma lem8053006 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term337 _142951 _142953 g t y) : term337 _142951 _142953 g t y.
Proof. exact (h1). Qed.
Lemma lem8053034 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term348 _142951 _142952 f t x) = (term348 _142951 _142952 f t x).
Proof. exact (eq_refl (term348 _142951 _142952 f t x)). Qed.
Lemma lem8053035 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term349 _142951 _142952 f x) = (term349 _142951 _142952 f x).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8053034 _142951 _142952 f t x)). Qed.
Lemma lem8053036 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8053038 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term350 _142951 _142952 f x) = (term350 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8053036 _142951 _142952) (@lem8053035 _142951 _142952 f x)). Qed.
Lemma lem8053039 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term350 _142951 _142952 f x.
Proof. exact (EQ_MP (@lem8053038 _142951 _142952 f x) (@lem8053000 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053056 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) (h1 : term335 _142951 _142952 s x) : term335 _142951 _142952 s x.
Proof. exact (h1). Qed.
Lemma lem8053093 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term348 _142951 _142953 g t y) = (term348 _142951 _142953 g t y).
Proof. exact (eq_refl (term348 _142951 _142953 g t y)). Qed.
Lemma lem8053094 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term349 _142951 _142953 g y) = (term349 _142951 _142953 g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8053093 _142951 _142953 g t y)). Qed.
Lemma lem8053095 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8053097 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term350 _142951 _142953 g y) = (term350 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8053095 _142951 _142953) (@lem8053094 _142951 _142953 g y)). Qed.
Lemma lem8053098 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term350 _142951 _142953 g y.
Proof. exact (EQ_MP (@lem8053097 _142951 _142953 g y) (@lem8052999 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053102 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) : term335 _142951 _142953 t y.
Proof. exact (h1). Qed.
Lemma lem8053134 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term329 _142951 _142952 _142953 f g s x t y) = (term358 _142951 _142952 _142953 x f s g t y).
Proof. exact (@lem19490 (@I ((cart _142951 _142952) -> Prop) s x) (term327 _142951 _142952 _142953 f s g t) (@I ((cart _142951 _142953) -> Prop) t y)). Qed.
Lemma lem8053135 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term330 _142951 _142952 _142953 f g s x y) = (term359 _142951 _142952 _142953 x f s g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8053134 _142951 _142952 _142953 x f s g t y)). Qed.
Lemma lem8053136 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8053137 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term331 _142951 _142952 _142953 f g s x y) = (term360 _142951 _142952 _142953 x f s g y).
Proof. exact (MK_COMB (@lem8053136 _142951 _142953) (@lem8053135 _142951 _142952 _142953 x f s g y)). Qed.
Lemma lem8053138 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term332 _142951 _142952 _142953 f g x y) = (term361 _142951 _142952 _142953 x f g y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8053137 _142951 _142952 _142953 x f s g y)). Qed.
Lemma lem8053139 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8053141 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term333 _142951 _142952 _142953 f g x y) = (term362 _142951 _142952 _142953 x f g y).
Proof. exact (MK_COMB (@lem8053139 _142951 _142952) (@lem8053138 _142951 _142952 _142953 x f g y)). Qed.
Lemma lem8053142 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term362 _142951 _142952 _142953 x f g y.
Proof. exact (EQ_MP (@lem8053141 _142951 _142952 _142953 x f g y) (@lem8053003 _142951 _142952 _142953 s t f g x y h1)). Qed.
Lemma lem8053182 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term329 _142951 _142952 _142953 f g s x t y) = (term358 _142951 _142952 _142953 x f s g t y).
Proof. exact (@lem19490 (@I ((cart _142951 _142952) -> Prop) s x) (term327 _142951 _142952 _142953 f s g t) (@I ((cart _142951 _142953) -> Prop) t y)). Qed.
Lemma lem8053183 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term330 _142951 _142952 _142953 f g s x y) = (term359 _142951 _142952 _142953 x f s g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8053182 _142951 _142952 _142953 x f s g t y)). Qed.
Lemma lem8053184 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8053185 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (s : type24 _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term331 _142951 _142952 _142953 f g s x y) = (term360 _142951 _142952 _142953 x f s g y).
Proof. exact (MK_COMB (@lem8053184 _142951 _142953) (@lem8053183 _142951 _142952 _142953 x f s g y)). Qed.
Lemma lem8053186 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term332 _142951 _142952 _142953 f g x y) = (term361 _142951 _142952 _142953 x f g y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8053185 _142951 _142952 _142953 x f s g y)). Qed.
Lemma lem8053187 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8053189 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term333 _142951 _142952 _142953 f g x y) = (term362 _142951 _142952 _142953 x f g y).
Proof. exact (MK_COMB (@lem8053187 _142951 _142952) (@lem8053186 _142951 _142952 _142953 x f g y)). Qed.
Lemma lem8053190 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term362 _142951 _142952 _142953 x f g y.
Proof. exact (EQ_MP (@lem8053189 _142951 _142952 _142953 x f g y) (@lem8053003 _142951 _142952 _142953 s t f g x y h1)). Qed.
Lemma lem8053199 {_142951 _142952 _142953 : Type'} (_106201 : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term363 _142951 _142952 f x _106201.
Proof. exact (@lem8053039 _142951 _142952 _142953 f g s x t y h1 _106201). Qed.
Lemma lem8053200 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) (x : cart _142951 _142952) : (term363 _142951 _142952 f x _106201) = (term348 _142951 _142952 f _106201 x).
Proof. exact (eq_refl (term363 _142951 _142952 f x _106201)). Qed.
Lemma lem8053208 {_142951 _142952 _142953 : Type'} (_106204 : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term363 _142951 _142953 g y _106204.
Proof. exact (@lem8053098 _142951 _142952 _142953 f g s x t y h1 _106204). Qed.
Lemma lem8053209 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) (y : cart _142951 _142953) : (term363 _142951 _142953 g y _106204) = (term348 _142951 _142953 g _106204 y).
Proof. exact (eq_refl (term363 _142951 _142953 g y _106204)). Qed.
Lemma lem8053211 {_142951 _142952 _142953 : Type'} (_106205 : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term364 _142951 _142952 _142953 x f g y _106205.
Proof. exact (@lem8053142 _142951 _142952 _142953 s t f g x y h1 _106205). Qed.
Lemma lem8053212 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term364 _142951 _142952 _142953 x f g y _106205) = (term360 _142951 _142952 _142953 x f _106205 g y).
Proof. exact (eq_refl (term364 _142951 _142952 _142953 x f g y _106205)). Qed.
Lemma lem8053213 {_142951 _142952 _142953 : Type'} (_106205 : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term360 _142951 _142952 _142953 x f _106205 g y.
Proof. exact (EQ_MP (@lem8053212 _142951 _142952 _142953 x f _106205 g y) (@lem8053211 _142951 _142952 _142953 _106205 s t f g x y h1)). Qed.
Lemma lem8053214 {_142951 _142952 _142953 : Type'} (_106205 : type24 _142951 _142952) (_106206 : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term365 _142951 _142952 _142953 x f _106205 g y _106206.
Proof. exact (@lem8053213 _142951 _142952 _142953 _106205 s t f g x y h1 _106206). Qed.
Lemma lem8053215 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) (y : cart _142951 _142953) : (term365 _142951 _142952 _142953 x f _106205 g y _106206) = (term358 _142951 _142952 _142953 x f _106205 g _106206 y).
Proof. exact (eq_refl (term365 _142951 _142952 _142953 x f _106205 g y _106206)). Qed.
Lemma lem8053216 {_142951 _142952 _142953 : Type'} (_106205 : type24 _142951 _142952) (_106206 : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term358 _142951 _142952 _142953 x f _106205 g _106206 y.
Proof. exact (EQ_MP (@lem8053215 _142951 _142952 _142953 x f _106205 g _106206 y) (@lem8053214 _142951 _142952 _142953 _106205 _106206 s t f g x y h1)). Qed.
Lemma lem8053217 {_142951 _142952 _142953 : Type'} (_106207 : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term364 _142951 _142952 _142953 x f g y _106207.
Proof. exact (@lem8053190 _142951 _142952 _142953 s t f g x y h1 _106207). Qed.
Lemma lem8053218 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term364 _142951 _142952 _142953 x f g y _106207) = (term360 _142951 _142952 _142953 x f _106207 g y).
Proof. exact (eq_refl (term364 _142951 _142952 _142953 x f g y _106207)). Qed.
Lemma lem8053219 {_142951 _142952 _142953 : Type'} (_106207 : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term360 _142951 _142952 _142953 x f _106207 g y.
Proof. exact (EQ_MP (@lem8053218 _142951 _142952 _142953 x f _106207 g y) (@lem8053217 _142951 _142952 _142953 _106207 s t f g x y h1)). Qed.
Lemma lem8053220 {_142951 _142952 _142953 : Type'} (_106207 : type24 _142951 _142952) (_106208 : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term365 _142951 _142952 _142953 x f _106207 g y _106208.
Proof. exact (@lem8053219 _142951 _142952 _142953 _106207 s t f g x y h1 _106208). Qed.
Lemma lem8053221 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) (y : cart _142951 _142953) : (term365 _142951 _142952 _142953 x f _106207 g y _106208) = (term358 _142951 _142952 _142953 x f _106207 g _106208 y).
Proof. exact (eq_refl (term365 _142951 _142952 _142953 x f _106207 g y _106208)). Qed.
Lemma lem8053222 {_142951 _142952 _142953 : Type'} (_106207 : type24 _142951 _142952) (_106208 : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term358 _142951 _142952 _142953 x f _106207 g _106208 y.
Proof. exact (EQ_MP (@lem8053221 _142951 _142952 _142953 x f _106207 g _106208 y) (@lem8053220 _142951 _142952 _142953 _106207 _106208 s t f g x y h1)). Qed.
Lemma lem8053224 {_142951 _142952 _142953 : Type'} (_106206 : type24 _142951 _142953) (_106205 : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term366 _142951 _142952 _142953 f g _106206 _106205 x.
Proof. exact (proj1 (@lem8053216 _142951 _142952 _142953 _106205 _106206 s t f g x y h1)). Qed.
Lemma lem8053225 {_142951 _142952 _142953 : Type'} (_106207 : type24 _142951 _142952) (_106208 : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term367 _142951 _142952 _142953 f _106207 g _106208 y.
Proof. exact (proj2 (@lem8053222 _142951 _142952 _142953 _106207 _106208 s t f g x y h1)). Qed.
Lemma lem8053240 {_142951 _142952 _142953 : Type'} (_106201 : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term348 _142951 _142952 f _106201 x.
Proof. exact (EQ_MP (@lem8053200 _142951 _142952 f _106201 x) (@lem8053199 _142951 _142952 _142953 _106201 f g s x t y h1)). Qed.
Lemma lem8053248 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) (h1 : term335 _142951 _142952 s x) : term335 _142951 _142952 s x.
Proof. exact (h1). Qed.
Lemma lem8053268 {_142951 _142952 _142953 : Type'} (_106204 : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term348 _142951 _142953 g _106204 y.
Proof. exact (EQ_MP (@lem8053209 _142951 _142953 g _106204 y) (@lem8053208 _142951 _142952 _142953 _106204 f g s x t y h1)). Qed.
Lemma lem8053270 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) : term335 _142951 _142953 t y.
Proof. exact (h1). Qed.
Lemma lem8053278 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) (h1 : term337 _142951 _142952 f s x) : term335 _142951 _142952 s x.
Proof. exact (proj2 (@lem8053005 _142951 _142952 f s x h1)). Qed.
Lemma lem8053289 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) (_106205 : type24 _142951 _142952) (x : cart _142951 _142952) : (term366 _142951 _142952 _142953 f g _106206 _106205 x) = (term368 _142951 _142952 _142953 f g _106206 _106205 x).
Proof. exact (@lem8051519 (term324 _142951 _142952 f _106205) (term324 _142951 _142953 g _106206) (@I ((cart _142951 _142952) -> Prop) _106205 x)). Qed.
Lemma lem8053290 {_142951 _142952 _142953 : Type'} (_106206 : type24 _142951 _142953) (_106205 : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term368 _142951 _142952 _142953 f g _106206 _106205 x.
Proof. exact (EQ_MP (@lem8053289 _142951 _142952 _142953 f g _106206 _106205 x) (@lem8053224 _142951 _142952 _142953 _106206 _106205 s t f g x y h1)). Qed.
Lemma lem8053310 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term337 _142951 _142953 g t y) : term335 _142951 _142953 t y.
Proof. exact (proj2 (@lem8053006 _142951 _142953 g t y h1)). Qed.
Lemma lem8053333 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) (y : cart _142951 _142953) : (term367 _142951 _142952 _142953 f _106207 g _106208 y) = (term369 _142951 _142952 _142953 f _106207 g _106208 y).
Proof. exact (@lem8051519 (term324 _142951 _142952 f _106207) (term324 _142951 _142953 g _106208) (@I ((cart _142951 _142953) -> Prop) _106208 y)). Qed.
Lemma lem8053334 {_142951 _142952 _142953 : Type'} (_106207 : type24 _142951 _142952) (_106208 : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term369 _142951 _142952 _142953 f _106207 g _106208 y.
Proof. exact (EQ_MP (@lem8053333 _142951 _142952 _142953 f _106207 g _106208 y) (@lem8053225 _142951 _142952 _142953 _106207 _106208 s t f g x y h1)). Qed.
Lemma lem8053336 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : @I (((cart _142951 _142952) -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem8052996 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053337 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term370 _142951 _142952 f s.
Proof. exact (fun h0 : term324 _142951 _142952 f s => @lem8053336 _142951 _142952 _142953 f g s x t y h1). Qed.
Lemma lem8053339 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053340 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (term370 _142951 _142952 f s) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f s).
Proof. exact (@lem8053339 (@I (((cart _142951 _142952) -> Prop) -> Prop) f s)). Qed.
Lemma lem8053341 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : @I (((cart _142951 _142952) -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem8053340 _142951 _142952 f s) (@lem8053337 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053347 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8053348 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) : (term348 _142951 _142952 f _106201 x) = (term372 _142951 _142952 x f _106201).
Proof. exact (@lem8053347 (@I ((cart _142951 _142952) -> Prop) _106201 x) (term324 _142951 _142952 f _106201)). Qed.
Lemma lem8053354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8053355 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) : (term373 _142951 _142952 f _106201 x) = (term374 _142951 _142952 x f _106201).
Proof. exact (MK_COMB (@lem8053354) (@lem8053348 _142951 _142952 x f _106201)). Qed.
Lemma lem8053361 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) : (term372 _142951 _142952 x f _106201) = (term372 _142951 _142952 x f _106201).
Proof. exact (eq_refl (term372 _142951 _142952 x f _106201)). Qed.
Lemma lem8053362 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) : ((term348 _142951 _142952 f _106201 x) = (term372 _142951 _142952 x f _106201)) = ((term372 _142951 _142952 x f _106201) = (term372 _142951 _142952 x f _106201)).
Proof. exact (MK_COMB (@lem8053355 _142951 _142952 x f _106201) (@lem8053361 _142951 _142952 x f _106201)). Qed.
Lemma lem8053364 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8053365 (x : Prop) : (x = x) = True.
Proof. exact (@lem8053364 Prop x). Qed.
Lemma lem8053366 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) : ((term372 _142951 _142952 x f _106201) = (term372 _142951 _142952 x f _106201)) = True.
Proof. exact (@lem8053365 (term372 _142951 _142952 x f _106201)). Qed.
Lemma lem8053367 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) : ((term348 _142951 _142952 f _106201 x) = (term372 _142951 _142952 x f _106201)) = True.
Proof. exact (TRANS (@lem8053362 _142951 _142952 x f _106201) (@lem8053366 _142951 _142952 x f _106201)). Qed.
Lemma lem8053368 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) : True = ((term348 _142951 _142952 f _106201 x) = (term372 _142951 _142952 x f _106201)).
Proof. exact (SYM (@lem8053367 _142951 _142952 x f _106201)). Qed.
Lemma lem8053369 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) : (term348 _142951 _142952 f _106201 x) = (term372 _142951 _142952 x f _106201).
Proof. exact (EQ_MP (@lem8053368 _142951 _142952 x f _106201) (@lem0)). Qed.
Lemma lem8053370 {_142951 _142952 _142953 : Type'} (_106201 : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term372 _142951 _142952 x f _106201.
Proof. exact (EQ_MP (@lem8053369 _142951 _142952 x f _106201) (@lem8053240 _142951 _142952 _142953 _106201 f g s x t y h1)). Qed.
Lemma lem8053372 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8053373 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) (x : cart _142951 _142952) : (term372 _142951 _142952 x f _106201) = (term376 _142951 _142952 f _106201 x).
Proof. exact (@lem8053372 (term324 _142951 _142952 f _106201) (@I ((cart _142951 _142952) -> Prop) _106201 x)). Qed.
Lemma lem8053375 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8053376 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) : (term377 _142951 _142952 f _106201) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f _106201).
Proof. exact (@lem8053375 (@I (((cart _142951 _142952) -> Prop) -> Prop) f _106201)). Qed.
Lemma lem8053377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8053378 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) : (term378 _142951 _142952 f _106201) = (term379 _142951 _142952 f _106201).
Proof. exact (MK_COMB (@lem8053377) (@lem8053376 _142951 _142952 f _106201)). Qed.
Lemma lem8053379 {_142951 _142952 : Type'} (_106201 : type24 _142951 _142952) (x : cart _142951 _142952) : (@I ((cart _142951 _142952) -> Prop) _106201 x) = (@I ((cart _142951 _142952) -> Prop) _106201 x).
Proof. exact (eq_refl (@I ((cart _142951 _142952) -> Prop) _106201 x)). Qed.
Lemma lem8053380 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) (x : cart _142951 _142952) : (term376 _142951 _142952 f _106201 x) = (term380 _142951 _142952 f _106201 x).
Proof. exact (MK_COMB (@lem8053378 _142951 _142952 f _106201) (@lem8053379 _142951 _142952 _106201 x)). Qed.
Lemma lem8053381 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106201 : type24 _142951 _142952) (x : cart _142951 _142952) : (term372 _142951 _142952 x f _106201) = (term380 _142951 _142952 f _106201 x).
Proof. exact (TRANS (@lem8053373 _142951 _142952 f _106201 x) (@lem8053380 _142951 _142952 f _106201 x)). Qed.
Lemma lem8053384 {_142951 _142952 _142953 : Type'} (_106201 : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term380 _142951 _142952 f _106201 x.
Proof. exact (EQ_MP (@lem8053381 _142951 _142952 f _106201 x) (@lem8053370 _142951 _142952 _142953 _106201 f g s x t y h1)). Qed.
Lemma lem8053385 {_142951 _142952 _142953 : Type'} (_106201 : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term380 _142951 _142952 f _106201 x.
Proof. exact (@lem8053384 _142951 _142952 _142953 _106201 f g s x t y h1). Qed.
Lemma lem8053386 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term380 _142951 _142952 f s x.
Proof. exact (@lem8053385 _142951 _142952 _142953 s f g s x t y h1). Qed.
Lemma lem8053389 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : @I ((cart _142951 _142952) -> Prop) s x.
Proof. exact (@lem8053386 _142951 _142952 _142953 f g s x t y h1 (@lem8053341 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053390 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term381 _142951 _142952 s x.
Proof. exact (fun h0 : term335 _142951 _142952 s x => @lem8053389 _142951 _142952 _142953 f g s x t y h1). Qed.
Lemma lem8053392 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053393 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term381 _142951 _142952 s x) = (@I ((cart _142951 _142952) -> Prop) s x).
Proof. exact (@lem8053392 (@I ((cart _142951 _142952) -> Prop) s x)). Qed.
Lemma lem8053394 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : @I ((cart _142951 _142952) -> Prop) s x.
Proof. exact (EQ_MP (@lem8053393 _142951 _142952 s x) (@lem8053390 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053397 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8053399 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term335 _142951 _142952 s x) = (term382 _142951 _142952 s x).
Proof. exact (@lem8053397 (@I ((cart _142951 _142952) -> Prop) s x)). Qed.
Lemma lem8053402 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) (h1 : term335 _142951 _142952 s x) : term382 _142951 _142952 s x.
Proof. exact (EQ_MP (@lem8053399 _142951 _142952 s x) (@lem8053248 _142951 _142952 s x h1)). Qed.
Lemma lem8053405 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142952 s x) (h2 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (@lem8053402 _142951 _142952 s x h1 (@lem8053394 _142951 _142952 _142953 f g s x t y h2)). Qed.
Lemma lem8053406 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142952 s x) (h2 : term354 _142951 _142952 _142953 f g s x t y) : term383.
Proof. exact (fun h0 : ~ False => @lem8053405 _142951 _142952 _142953 f g s x t y h1 h2). Qed.
Lemma lem8053408 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053409 : term383 = False.
Proof. exact (@lem8053408 False). Qed.
Lemma lem8053410 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142952 s x) (h2 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (EQ_MP (@lem8053409) (@lem8053406 _142951 _142952 _142953 f g s x t y h1 h2)). Qed.
Lemma lem8053412 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : @I (((cart _142951 _142953) -> Prop) -> Prop) g t.
Proof. exact (proj2 (@lem8052996 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053413 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term370 _142951 _142953 g t.
Proof. exact (fun h0 : term324 _142951 _142953 g t => @lem8053412 _142951 _142952 _142953 f g s x t y h1). Qed.
Lemma lem8053415 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053416 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term370 _142951 _142953 g t) = (@I (((cart _142951 _142953) -> Prop) -> Prop) g t).
Proof. exact (@lem8053415 (@I (((cart _142951 _142953) -> Prop) -> Prop) g t)). Qed.
Lemma lem8053417 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : @I (((cart _142951 _142953) -> Prop) -> Prop) g t.
Proof. exact (EQ_MP (@lem8053416 _142951 _142953 g t) (@lem8053413 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053423 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8053424 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) : (term348 _142951 _142953 g _106204 y) = (term372 _142951 _142953 y g _106204).
Proof. exact (@lem8053423 (@I ((cart _142951 _142953) -> Prop) _106204 y) (term324 _142951 _142953 g _106204)). Qed.
Lemma lem8053430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8053431 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) : (term373 _142951 _142953 g _106204 y) = (term374 _142951 _142953 y g _106204).
Proof. exact (MK_COMB (@lem8053430) (@lem8053424 _142951 _142953 y g _106204)). Qed.
Lemma lem8053437 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) : (term372 _142951 _142953 y g _106204) = (term372 _142951 _142953 y g _106204).
Proof. exact (eq_refl (term372 _142951 _142953 y g _106204)). Qed.
Lemma lem8053438 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) : ((term348 _142951 _142953 g _106204 y) = (term372 _142951 _142953 y g _106204)) = ((term372 _142951 _142953 y g _106204) = (term372 _142951 _142953 y g _106204)).
Proof. exact (MK_COMB (@lem8053431 _142951 _142953 y g _106204) (@lem8053437 _142951 _142953 y g _106204)). Qed.
Lemma lem8053440 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8053441 (x : Prop) : (x = x) = True.
Proof. exact (@lem8053440 Prop x). Qed.
Lemma lem8053442 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) : ((term372 _142951 _142953 y g _106204) = (term372 _142951 _142953 y g _106204)) = True.
Proof. exact (@lem8053441 (term372 _142951 _142953 y g _106204)). Qed.
Lemma lem8053443 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) : ((term348 _142951 _142953 g _106204 y) = (term372 _142951 _142953 y g _106204)) = True.
Proof. exact (TRANS (@lem8053438 _142951 _142953 y g _106204) (@lem8053442 _142951 _142953 y g _106204)). Qed.
Lemma lem8053444 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) : True = ((term348 _142951 _142953 g _106204 y) = (term372 _142951 _142953 y g _106204)).
Proof. exact (SYM (@lem8053443 _142951 _142953 y g _106204)). Qed.
Lemma lem8053445 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) : (term348 _142951 _142953 g _106204 y) = (term372 _142951 _142953 y g _106204).
Proof. exact (EQ_MP (@lem8053444 _142951 _142953 y g _106204) (@lem0)). Qed.
Lemma lem8053446 {_142951 _142952 _142953 : Type'} (_106204 : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term372 _142951 _142953 y g _106204.
Proof. exact (EQ_MP (@lem8053445 _142951 _142953 y g _106204) (@lem8053268 _142951 _142952 _142953 _106204 f g s x t y h1)). Qed.
Lemma lem8053448 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8053449 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) (y : cart _142951 _142953) : (term372 _142951 _142953 y g _106204) = (term376 _142951 _142953 g _106204 y).
Proof. exact (@lem8053448 (term324 _142951 _142953 g _106204) (@I ((cart _142951 _142953) -> Prop) _106204 y)). Qed.
Lemma lem8053451 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8053452 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) : (term377 _142951 _142953 g _106204) = (@I (((cart _142951 _142953) -> Prop) -> Prop) g _106204).
Proof. exact (@lem8053451 (@I (((cart _142951 _142953) -> Prop) -> Prop) g _106204)). Qed.
Lemma lem8053453 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8053454 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) : (term378 _142951 _142953 g _106204) = (term379 _142951 _142953 g _106204).
Proof. exact (MK_COMB (@lem8053453) (@lem8053452 _142951 _142953 g _106204)). Qed.
Lemma lem8053455 {_142951 _142953 : Type'} (_106204 : type24 _142951 _142953) (y : cart _142951 _142953) : (@I ((cart _142951 _142953) -> Prop) _106204 y) = (@I ((cart _142951 _142953) -> Prop) _106204 y).
Proof. exact (eq_refl (@I ((cart _142951 _142953) -> Prop) _106204 y)). Qed.
Lemma lem8053456 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) (y : cart _142951 _142953) : (term376 _142951 _142953 g _106204 y) = (term380 _142951 _142953 g _106204 y).
Proof. exact (MK_COMB (@lem8053454 _142951 _142953 g _106204) (@lem8053455 _142951 _142953 _106204 y)). Qed.
Lemma lem8053457 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (_106204 : type24 _142951 _142953) (y : cart _142951 _142953) : (term372 _142951 _142953 y g _106204) = (term380 _142951 _142953 g _106204 y).
Proof. exact (TRANS (@lem8053449 _142951 _142953 g _106204 y) (@lem8053456 _142951 _142953 g _106204 y)). Qed.
Lemma lem8053460 {_142951 _142952 _142953 : Type'} (_106204 : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term380 _142951 _142953 g _106204 y.
Proof. exact (EQ_MP (@lem8053457 _142951 _142953 g _106204 y) (@lem8053446 _142951 _142952 _142953 _106204 f g s x t y h1)). Qed.
Lemma lem8053461 {_142951 _142952 _142953 : Type'} (_106204 : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term380 _142951 _142953 g _106204 y.
Proof. exact (@lem8053460 _142951 _142952 _142953 _106204 f g s x t y h1). Qed.
Lemma lem8053462 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term380 _142951 _142953 g t y.
Proof. exact (@lem8053461 _142951 _142952 _142953 t f g s x t y h1). Qed.
Lemma lem8053465 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : @I ((cart _142951 _142953) -> Prop) t y.
Proof. exact (@lem8053462 _142951 _142952 _142953 f g s x t y h1 (@lem8053417 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053466 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : term381 _142951 _142953 t y.
Proof. exact (fun h0 : term335 _142951 _142953 t y => @lem8053465 _142951 _142952 _142953 f g s x t y h1). Qed.
Lemma lem8053468 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053469 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term381 _142951 _142953 t y) = (@I ((cart _142951 _142953) -> Prop) t y).
Proof. exact (@lem8053468 (@I ((cart _142951 _142953) -> Prop) t y)). Qed.
Lemma lem8053470 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : @I ((cart _142951 _142953) -> Prop) t y.
Proof. exact (EQ_MP (@lem8053469 _142951 _142953 t y) (@lem8053466 _142951 _142952 _142953 f g s x t y h1)). Qed.
Lemma lem8053473 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8053475 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term335 _142951 _142953 t y) = (term382 _142951 _142953 t y).
Proof. exact (@lem8053473 (@I ((cart _142951 _142953) -> Prop) t y)). Qed.
Lemma lem8053478 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) : term382 _142951 _142953 t y.
Proof. exact (EQ_MP (@lem8053475 _142951 _142953 t y) (@lem8053270 _142951 _142953 t y h1)). Qed.
Lemma lem8053481 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) (h2 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (@lem8053478 _142951 _142953 t y h1 (@lem8053470 _142951 _142952 _142953 f g s x t y h2)). Qed.
Lemma lem8053482 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) (h2 : term354 _142951 _142952 _142953 f g s x t y) : term383.
Proof. exact (fun h0 : ~ False => @lem8053481 _142951 _142952 _142953 f g s x t y h1 h2). Qed.
Lemma lem8053484 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053485 : term383 = False.
Proof. exact (@lem8053484 False). Qed.
Lemma lem8053486 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) (h2 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (EQ_MP (@lem8053485) (@lem8053482 _142951 _142952 _142953 f g s x t y h1 h2)). Qed.
Lemma lem8053488 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) (h1 : term337 _142951 _142952 f s x) : @I (((cart _142951 _142952) -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem8053005 _142951 _142952 f s x h1)). Qed.
Lemma lem8053489 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) (h1 : term337 _142951 _142952 f s x) : term370 _142951 _142952 f s.
Proof. exact (fun h0 : term324 _142951 _142952 f s => @lem8053488 _142951 _142952 f s x h1). Qed.
Lemma lem8053491 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053492 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (term370 _142951 _142952 f s) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f s).
Proof. exact (@lem8053491 (@I (((cart _142951 _142952) -> Prop) -> Prop) f s)). Qed.
Lemma lem8053493 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) (h1 : term337 _142951 _142952 f s x) : @I (((cart _142951 _142952) -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem8053492 _142951 _142952 f s) (@lem8053489 _142951 _142952 f s x h1)). Qed.
Lemma lem8053495 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) (h1 : term321 _142951 _142952 _142953 g x' f x'') : @I (((cart _142951 _142953) -> Prop) -> Prop) g x'.
Proof. exact (proj1 (@lem8052988 _142951 _142952 _142953 g x' f x'' h1)). Qed.
Lemma lem8053496 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) (h1 : term321 _142951 _142952 _142953 g x' f x'') : term370 _142951 _142953 g x'.
Proof. exact (fun h0 : term324 _142951 _142953 g x' => @lem8053495 _142951 _142952 _142953 g x' f x'' h1). Qed.
Lemma lem8053498 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053499 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) : (term370 _142951 _142953 g x') = (@I (((cart _142951 _142953) -> Prop) -> Prop) g x').
Proof. exact (@lem8053498 (@I (((cart _142951 _142953) -> Prop) -> Prop) g x')). Qed.
Lemma lem8053500 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) (h1 : term321 _142951 _142952 _142953 g x' f x'') : @I (((cart _142951 _142953) -> Prop) -> Prop) g x'.
Proof. exact (EQ_MP (@lem8053499 _142951 _142953 g x') (@lem8053496 _142951 _142952 _142953 g x' f x'' h1)). Qed.
Lemma lem8053516 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8053517 {_142951 _142952 _142953 : Type'} (_106205 : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term384 _142951 _142952 _142953 g _106206 _106205 x) = (term385 _142951 _142952 _142953 _106205 x g _106206).
Proof. exact (@lem8053516 (@I ((cart _142951 _142952) -> Prop) _106205 x) (term324 _142951 _142953 g _106206)). Qed.
Lemma lem8053523 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) : (term326 _142951 _142952 f _106205) = (term326 _142951 _142952 f _106205).
Proof. exact (eq_refl (term326 _142951 _142952 f _106205)). Qed.
Lemma lem8053524 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term368 _142951 _142952 _142953 f g _106206 _106205 x) = (term386 _142951 _142952 _142953 f _106205 x g _106206).
Proof. exact (MK_COMB (@lem8053523 _142951 _142952 f _106205) (@lem8053517 _142951 _142952 _142953 _106205 x g _106206)). Qed.
Lemma lem8053528 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8053529 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term386 _142951 _142952 _142953 f _106205 x g _106206) = (term387 _142951 _142952 _142953 x f _106205 g _106206).
Proof. exact (@lem8053528 (@I ((cart _142951 _142952) -> Prop) _106205 x) (term324 _142951 _142952 f _106205) (term324 _142951 _142953 g _106206)). Qed.
Lemma lem8053545 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term368 _142951 _142952 _142953 f g _106206 _106205 x) = (term387 _142951 _142952 _142953 x f _106205 g _106206).
Proof. exact (TRANS (@lem8053524 _142951 _142952 _142953 f _106205 x g _106206) (@lem8053529 _142951 _142952 _142953 x f _106205 g _106206)). Qed.
Lemma lem8053546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8053547 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term388 _142951 _142952 _142953 f g _106206 _106205 x) = (term389 _142951 _142952 _142953 x f _106205 g _106206).
Proof. exact (MK_COMB (@lem8053546) (@lem8053545 _142951 _142952 _142953 x f _106205 g _106206)). Qed.
Lemma lem8053563 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term387 _142951 _142952 _142953 x f _106205 g _106206) = (term387 _142951 _142952 _142953 x f _106205 g _106206).
Proof. exact (eq_refl (term387 _142951 _142952 _142953 x f _106205 g _106206)). Qed.
Lemma lem8053564 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : ((term368 _142951 _142952 _142953 f g _106206 _106205 x) = (term387 _142951 _142952 _142953 x f _106205 g _106206)) = ((term387 _142951 _142952 _142953 x f _106205 g _106206) = (term387 _142951 _142952 _142953 x f _106205 g _106206)).
Proof. exact (MK_COMB (@lem8053547 _142951 _142952 _142953 x f _106205 g _106206) (@lem8053563 _142951 _142952 _142953 x f _106205 g _106206)). Qed.
Lemma lem8053566 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8053567 (x : Prop) : (x = x) = True.
Proof. exact (@lem8053566 Prop x). Qed.
Lemma lem8053568 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : ((term387 _142951 _142952 _142953 x f _106205 g _106206) = (term387 _142951 _142952 _142953 x f _106205 g _106206)) = True.
Proof. exact (@lem8053567 (term387 _142951 _142952 _142953 x f _106205 g _106206)). Qed.
Lemma lem8053569 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : ((term368 _142951 _142952 _142953 f g _106206 _106205 x) = (term387 _142951 _142952 _142953 x f _106205 g _106206)) = True.
Proof. exact (TRANS (@lem8053564 _142951 _142952 _142953 x f _106205 g _106206) (@lem8053568 _142951 _142952 _142953 x f _106205 g _106206)). Qed.
Lemma lem8053570 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : True = ((term368 _142951 _142952 _142953 f g _106206 _106205 x) = (term387 _142951 _142952 _142953 x f _106205 g _106206)).
Proof. exact (SYM (@lem8053569 _142951 _142952 _142953 x f _106205 g _106206)). Qed.
Lemma lem8053571 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term368 _142951 _142952 _142953 f g _106206 _106205 x) = (term387 _142951 _142952 _142953 x f _106205 g _106206).
Proof. exact (EQ_MP (@lem8053570 _142951 _142952 _142953 x f _106205 g _106206) (@lem0)). Qed.
Lemma lem8053572 {_142951 _142952 _142953 : Type'} (_106205 : type24 _142951 _142952) (_106206 : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term387 _142951 _142952 _142953 x f _106205 g _106206.
Proof. exact (EQ_MP (@lem8053571 _142951 _142952 _142953 x f _106205 g _106206) (@lem8053290 _142951 _142952 _142953 _106206 _106205 s t f g x y h1)). Qed.
Lemma lem8053574 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8053575 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) (_106205 : type24 _142951 _142952) (x : cart _142951 _142952) : (term387 _142951 _142952 _142953 x f _106205 g _106206) = (term390 _142951 _142952 _142953 f g _106206 _106205 x).
Proof. exact (@lem8053574 (term327 _142951 _142952 _142953 f _106205 g _106206) (@I ((cart _142951 _142952) -> Prop) _106205 x)). Qed.
Lemma lem8053577 (a : Prop) (b : Prop) : (term391 a b) = (term392 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8053578 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term393 _142951 _142952 _142953 f _106205 g _106206) = (term394 _142951 _142952 _142953 f _106205 g _106206).
Proof. exact (@lem8053577 (term324 _142951 _142952 f _106205) (term324 _142951 _142953 g _106206)). Qed.
Lemma lem8053580 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8053581 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) : (term377 _142951 _142952 f _106205) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f _106205).
Proof. exact (@lem8053580 (@I (((cart _142951 _142952) -> Prop) -> Prop) f _106205)). Qed.
Lemma lem8053582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8053583 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) : (term395 _142951 _142952 f _106205) = (term336 _142951 _142952 f _106205).
Proof. exact (MK_COMB (@lem8053582) (@lem8053581 _142951 _142952 f _106205)). Qed.
Lemma lem8053585 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8053586 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term377 _142951 _142953 g _106206) = (@I (((cart _142951 _142953) -> Prop) -> Prop) g _106206).
Proof. exact (@lem8053585 (@I (((cart _142951 _142953) -> Prop) -> Prop) g _106206)). Qed.
Lemma lem8053587 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term394 _142951 _142952 _142953 f _106205 g _106206) = (term345 _142951 _142952 _142953 f _106205 g _106206).
Proof. exact (MK_COMB (@lem8053583 _142951 _142952 f _106205) (@lem8053586 _142951 _142953 g _106206)). Qed.
Lemma lem8053588 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term393 _142951 _142952 _142953 f _106205 g _106206) = (term345 _142951 _142952 _142953 f _106205 g _106206).
Proof. exact (TRANS (@lem8053578 _142951 _142952 _142953 f _106205 g _106206) (@lem8053587 _142951 _142952 _142953 f _106205 g _106206)). Qed.
Lemma lem8053589 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8053590 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106205 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) : (term396 _142951 _142952 _142953 f _106205 g _106206) = (term397 _142951 _142952 _142953 f _106205 g _106206).
Proof. exact (MK_COMB (@lem8053589) (@lem8053588 _142951 _142952 _142953 f _106205 g _106206)). Qed.
Lemma lem8053591 {_142951 _142952 : Type'} (_106205 : type24 _142951 _142952) (x : cart _142951 _142952) : (@I ((cart _142951 _142952) -> Prop) _106205 x) = (@I ((cart _142951 _142952) -> Prop) _106205 x).
Proof. exact (eq_refl (@I ((cart _142951 _142952) -> Prop) _106205 x)). Qed.
Lemma lem8053592 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) (_106205 : type24 _142951 _142952) (x : cart _142951 _142952) : (term390 _142951 _142952 _142953 f g _106206 _106205 x) = (term398 _142951 _142952 _142953 f g _106206 _106205 x).
Proof. exact (MK_COMB (@lem8053590 _142951 _142952 _142953 f _106205 g _106206) (@lem8053591 _142951 _142952 _106205 x)). Qed.
Lemma lem8053593 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (_106206 : type24 _142951 _142953) (_106205 : type24 _142951 _142952) (x : cart _142951 _142952) : (term387 _142951 _142952 _142953 x f _106205 g _106206) = (term398 _142951 _142952 _142953 f g _106206 _106205 x).
Proof. exact (TRANS (@lem8053575 _142951 _142952 _142953 f g _106206 _106205 x) (@lem8053592 _142951 _142952 _142953 f g _106206 _106205 x)). Qed.
Lemma lem8053595 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142952 f s x) : term345 _142951 _142952 _142953 f s g x'.
Proof. exact (conj (@lem8053493 _142951 _142952 f s x h2) (@lem8053500 _142951 _142952 _142953 g x' f x'' h1)). Qed.
Lemma lem8053597 {_142951 _142952 _142953 : Type'} (_106206 : type24 _142951 _142953) (_106205 : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term398 _142951 _142952 _142953 f g _106206 _106205 x.
Proof. exact (EQ_MP (@lem8053593 _142951 _142952 _142953 f g _106206 _106205 x) (@lem8053572 _142951 _142952 _142953 _106205 _106206 s t f g x y h1)). Qed.
Lemma lem8053598 {_142951 _142952 _142953 : Type'} (_106206 : type24 _142951 _142953) (_106205 : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term398 _142951 _142952 _142953 f g _106206 _106205 x.
Proof. exact (@lem8053597 _142951 _142952 _142953 _106206 _106205 s t f g x y h1). Qed.
Lemma lem8053599 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term398 _142951 _142952 _142953 f g x' s x.
Proof. exact (@lem8053598 _142951 _142952 _142953 x' s s t f g x y h1). Qed.
Lemma lem8053602 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142952 f s x) (h3 : term341 _142951 _142952 _142953 s t f g x y) : @I ((cart _142951 _142952) -> Prop) s x.
Proof. exact (@lem8053599 _142951 _142952 _142953 x' s t f g x y h3 (@lem8053595 _142951 _142952 _142953 g x' x'' f s x h1 h2)). Qed.
Lemma lem8053603 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142952 f s x) (h3 : term341 _142951 _142952 _142953 s t f g x y) : term381 _142951 _142952 s x.
Proof. exact (fun h0 : term335 _142951 _142952 s x => @lem8053602 _142951 _142952 _142953 x' x'' s t f g x y h1 h2 h3). Qed.
Lemma lem8053605 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053606 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term381 _142951 _142952 s x) = (@I ((cart _142951 _142952) -> Prop) s x).
Proof. exact (@lem8053605 (@I ((cart _142951 _142952) -> Prop) s x)). Qed.
Lemma lem8053607 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142952 f s x) (h3 : term341 _142951 _142952 _142953 s t f g x y) : @I ((cart _142951 _142952) -> Prop) s x.
Proof. exact (EQ_MP (@lem8053606 _142951 _142952 s x) (@lem8053603 _142951 _142952 _142953 x' x'' s t f g x y h1 h2 h3)). Qed.
Lemma lem8053610 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8053612 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term335 _142951 _142952 s x) = (term382 _142951 _142952 s x).
Proof. exact (@lem8053610 (@I ((cart _142951 _142952) -> Prop) s x)). Qed.
Lemma lem8053615 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) (h1 : term337 _142951 _142952 f s x) : term382 _142951 _142952 s x.
Proof. exact (EQ_MP (@lem8053612 _142951 _142952 s x) (@lem8053278 _142951 _142952 f s x h1)). Qed.
Lemma lem8053618 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142952 f s x) (h3 : term341 _142951 _142952 _142953 s t f g x y) : False.
Proof. exact (@lem8053615 _142951 _142952 f s x h2 (@lem8053607 _142951 _142952 _142953 x' x'' s t f g x y h1 h2 h3)). Qed.
Lemma lem8053619 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142952 f s x) (h3 : term341 _142951 _142952 _142953 s t f g x y) : term383.
Proof. exact (fun h0 : ~ False => @lem8053618 _142951 _142952 _142953 x' x'' s t f g x y h1 h2 h3). Qed.
Lemma lem8053621 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053622 : term383 = False.
Proof. exact (@lem8053621 False). Qed.
Lemma lem8053623 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142952 f s x) (h3 : term341 _142951 _142952 _142953 s t f g x y) : False.
Proof. exact (EQ_MP (@lem8053622) (@lem8053619 _142951 _142952 _142953 x' x'' s t f g x y h1 h2 h3)). Qed.
Lemma lem8053625 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) (h1 : term321 _142951 _142952 _142953 g x' f x'') : @I (((cart _142951 _142952) -> Prop) -> Prop) f x''.
Proof. exact (proj2 (@lem8052988 _142951 _142952 _142953 g x' f x'' h1)). Qed.
Lemma lem8053626 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) (h1 : term321 _142951 _142952 _142953 g x' f x'') : term370 _142951 _142952 f x''.
Proof. exact (fun h0 : term324 _142951 _142952 f x'' => @lem8053625 _142951 _142952 _142953 g x' f x'' h1). Qed.
Lemma lem8053628 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053629 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) : (term370 _142951 _142952 f x'') = (@I (((cart _142951 _142952) -> Prop) -> Prop) f x'').
Proof. exact (@lem8053628 (@I (((cart _142951 _142952) -> Prop) -> Prop) f x'')). Qed.
Lemma lem8053630 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) (h1 : term321 _142951 _142952 _142953 g x' f x'') : @I (((cart _142951 _142952) -> Prop) -> Prop) f x''.
Proof. exact (EQ_MP (@lem8053629 _142951 _142952 f x'') (@lem8053626 _142951 _142952 _142953 g x' f x'' h1)). Qed.
Lemma lem8053632 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term337 _142951 _142953 g t y) : @I (((cart _142951 _142953) -> Prop) -> Prop) g t.
Proof. exact (proj1 (@lem8053006 _142951 _142953 g t y h1)). Qed.
Lemma lem8053633 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term337 _142951 _142953 g t y) : term370 _142951 _142953 g t.
Proof. exact (fun h0 : term324 _142951 _142953 g t => @lem8053632 _142951 _142953 g t y h1). Qed.
Lemma lem8053635 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053636 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term370 _142951 _142953 g t) = (@I (((cart _142951 _142953) -> Prop) -> Prop) g t).
Proof. exact (@lem8053635 (@I (((cart _142951 _142953) -> Prop) -> Prop) g t)). Qed.
Lemma lem8053637 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term337 _142951 _142953 g t y) : @I (((cart _142951 _142953) -> Prop) -> Prop) g t.
Proof. exact (EQ_MP (@lem8053636 _142951 _142953 g t) (@lem8053633 _142951 _142953 g t y h1)). Qed.
Lemma lem8053653 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8053654 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term348 _142951 _142953 g _106208 y) = (term372 _142951 _142953 y g _106208).
Proof. exact (@lem8053653 (@I ((cart _142951 _142953) -> Prop) _106208 y) (term324 _142951 _142953 g _106208)). Qed.
Lemma lem8053660 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) : (term326 _142951 _142952 f _106207) = (term326 _142951 _142952 f _106207).
Proof. exact (eq_refl (term326 _142951 _142952 f _106207)). Qed.
Lemma lem8053661 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term369 _142951 _142952 _142953 f _106207 g _106208 y) = (term399 _142951 _142952 _142953 f _106207 y g _106208).
Proof. exact (MK_COMB (@lem8053660 _142951 _142952 f _106207) (@lem8053654 _142951 _142953 y g _106208)). Qed.
Lemma lem8053665 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8053666 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term399 _142951 _142952 _142953 f _106207 y g _106208) = (term400 _142951 _142952 _142953 y f _106207 g _106208).
Proof. exact (@lem8053665 (@I ((cart _142951 _142953) -> Prop) _106208 y) (term324 _142951 _142952 f _106207) (term324 _142951 _142953 g _106208)). Qed.
Lemma lem8053682 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term369 _142951 _142952 _142953 f _106207 g _106208 y) = (term400 _142951 _142952 _142953 y f _106207 g _106208).
Proof. exact (TRANS (@lem8053661 _142951 _142952 _142953 f _106207 y g _106208) (@lem8053666 _142951 _142952 _142953 y f _106207 g _106208)). Qed.
Lemma lem8053683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8053684 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term401 _142951 _142952 _142953 f _106207 g _106208 y) = (term402 _142951 _142952 _142953 y f _106207 g _106208).
Proof. exact (MK_COMB (@lem8053683) (@lem8053682 _142951 _142952 _142953 y f _106207 g _106208)). Qed.
Lemma lem8053700 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term400 _142951 _142952 _142953 y f _106207 g _106208) = (term400 _142951 _142952 _142953 y f _106207 g _106208).
Proof. exact (eq_refl (term400 _142951 _142952 _142953 y f _106207 g _106208)). Qed.
Lemma lem8053701 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : ((term369 _142951 _142952 _142953 f _106207 g _106208 y) = (term400 _142951 _142952 _142953 y f _106207 g _106208)) = ((term400 _142951 _142952 _142953 y f _106207 g _106208) = (term400 _142951 _142952 _142953 y f _106207 g _106208)).
Proof. exact (MK_COMB (@lem8053684 _142951 _142952 _142953 y f _106207 g _106208) (@lem8053700 _142951 _142952 _142953 y f _106207 g _106208)). Qed.
Lemma lem8053703 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8053704 (x : Prop) : (x = x) = True.
Proof. exact (@lem8053703 Prop x). Qed.
Lemma lem8053705 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : ((term400 _142951 _142952 _142953 y f _106207 g _106208) = (term400 _142951 _142952 _142953 y f _106207 g _106208)) = True.
Proof. exact (@lem8053704 (term400 _142951 _142952 _142953 y f _106207 g _106208)). Qed.
Lemma lem8053706 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : ((term369 _142951 _142952 _142953 f _106207 g _106208 y) = (term400 _142951 _142952 _142953 y f _106207 g _106208)) = True.
Proof. exact (TRANS (@lem8053701 _142951 _142952 _142953 y f _106207 g _106208) (@lem8053705 _142951 _142952 _142953 y f _106207 g _106208)). Qed.
Lemma lem8053707 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : True = ((term369 _142951 _142952 _142953 f _106207 g _106208 y) = (term400 _142951 _142952 _142953 y f _106207 g _106208)).
Proof. exact (SYM (@lem8053706 _142951 _142952 _142953 y f _106207 g _106208)). Qed.
Lemma lem8053708 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term369 _142951 _142952 _142953 f _106207 g _106208 y) = (term400 _142951 _142952 _142953 y f _106207 g _106208).
Proof. exact (EQ_MP (@lem8053707 _142951 _142952 _142953 y f _106207 g _106208) (@lem0)). Qed.
Lemma lem8053709 {_142951 _142952 _142953 : Type'} (_106207 : type24 _142951 _142952) (_106208 : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term400 _142951 _142952 _142953 y f _106207 g _106208.
Proof. exact (EQ_MP (@lem8053708 _142951 _142952 _142953 y f _106207 g _106208) (@lem8053334 _142951 _142952 _142953 _106207 _106208 s t f g x y h1)). Qed.
Lemma lem8053711 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8053712 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) (y : cart _142951 _142953) : (term400 _142951 _142952 _142953 y f _106207 g _106208) = (term403 _142951 _142952 _142953 f _106207 g _106208 y).
Proof. exact (@lem8053711 (term327 _142951 _142952 _142953 f _106207 g _106208) (@I ((cart _142951 _142953) -> Prop) _106208 y)). Qed.
Lemma lem8053714 (a : Prop) (b : Prop) : (term391 a b) = (term392 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8053715 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term393 _142951 _142952 _142953 f _106207 g _106208) = (term394 _142951 _142952 _142953 f _106207 g _106208).
Proof. exact (@lem8053714 (term324 _142951 _142952 f _106207) (term324 _142951 _142953 g _106208)). Qed.
Lemma lem8053717 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8053718 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) : (term377 _142951 _142952 f _106207) = (@I (((cart _142951 _142952) -> Prop) -> Prop) f _106207).
Proof. exact (@lem8053717 (@I (((cart _142951 _142952) -> Prop) -> Prop) f _106207)). Qed.
Lemma lem8053719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8053720 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) : (term395 _142951 _142952 f _106207) = (term336 _142951 _142952 f _106207).
Proof. exact (MK_COMB (@lem8053719) (@lem8053718 _142951 _142952 f _106207)). Qed.
Lemma lem8053722 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8053723 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term377 _142951 _142953 g _106208) = (@I (((cart _142951 _142953) -> Prop) -> Prop) g _106208).
Proof. exact (@lem8053722 (@I (((cart _142951 _142953) -> Prop) -> Prop) g _106208)). Qed.
Lemma lem8053724 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term394 _142951 _142952 _142953 f _106207 g _106208) = (term345 _142951 _142952 _142953 f _106207 g _106208).
Proof. exact (MK_COMB (@lem8053720 _142951 _142952 f _106207) (@lem8053723 _142951 _142953 g _106208)). Qed.
Lemma lem8053725 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term393 _142951 _142952 _142953 f _106207 g _106208) = (term345 _142951 _142952 _142953 f _106207 g _106208).
Proof. exact (TRANS (@lem8053715 _142951 _142952 _142953 f _106207 g _106208) (@lem8053724 _142951 _142952 _142953 f _106207 g _106208)). Qed.
Lemma lem8053726 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8053727 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) : (term396 _142951 _142952 _142953 f _106207 g _106208) = (term397 _142951 _142952 _142953 f _106207 g _106208).
Proof. exact (MK_COMB (@lem8053726) (@lem8053725 _142951 _142952 _142953 f _106207 g _106208)). Qed.
Lemma lem8053728 {_142951 _142953 : Type'} (_106208 : type24 _142951 _142953) (y : cart _142951 _142953) : (@I ((cart _142951 _142953) -> Prop) _106208 y) = (@I ((cart _142951 _142953) -> Prop) _106208 y).
Proof. exact (eq_refl (@I ((cart _142951 _142953) -> Prop) _106208 y)). Qed.
Lemma lem8053729 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) (y : cart _142951 _142953) : (term403 _142951 _142952 _142953 f _106207 g _106208 y) = (term404 _142951 _142952 _142953 f _106207 g _106208 y).
Proof. exact (MK_COMB (@lem8053727 _142951 _142952 _142953 f _106207 g _106208) (@lem8053728 _142951 _142953 _106208 y)). Qed.
Lemma lem8053730 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (_106207 : type24 _142951 _142952) (g : type56 _142951 _142953) (_106208 : type24 _142951 _142953) (y : cart _142951 _142953) : (term400 _142951 _142952 _142953 y f _106207 g _106208) = (term404 _142951 _142952 _142953 f _106207 g _106208 y).
Proof. exact (TRANS (@lem8053712 _142951 _142952 _142953 f _106207 g _106208 y) (@lem8053729 _142951 _142952 _142953 f _106207 g _106208 y)). Qed.
Lemma lem8053732 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (f : type56 _142951 _142952) (x'' : type24 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142953 g t y) : term345 _142951 _142952 _142953 f x'' g t.
Proof. exact (conj (@lem8053630 _142951 _142952 _142953 g x' f x'' h1) (@lem8053637 _142951 _142953 g t y h2)). Qed.
Lemma lem8053734 {_142951 _142952 _142953 : Type'} (_106207 : type24 _142951 _142952) (_106208 : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term404 _142951 _142952 _142953 f _106207 g _106208 y.
Proof. exact (EQ_MP (@lem8053730 _142951 _142952 _142953 f _106207 g _106208 y) (@lem8053709 _142951 _142952 _142953 _106207 _106208 s t f g x y h1)). Qed.
Lemma lem8053735 {_142951 _142952 _142953 : Type'} (_106207 : type24 _142951 _142952) (_106208 : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term404 _142951 _142952 _142953 f _106207 g _106208 y.
Proof. exact (@lem8053734 _142951 _142952 _142953 _106207 _106208 s t f g x y h1). Qed.
Lemma lem8053736 {_142951 _142952 _142953 : Type'} (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term341 _142951 _142952 _142953 s t f g x y) : term404 _142951 _142952 _142953 f x'' g t y.
Proof. exact (@lem8053735 _142951 _142952 _142953 x'' t s t f g x y h1). Qed.
Lemma lem8053739 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142953 g t y) (h3 : term341 _142951 _142952 _142953 s t f g x y) : @I ((cart _142951 _142953) -> Prop) t y.
Proof. exact (@lem8053736 _142951 _142952 _142953 x'' s t f g x y h3 (@lem8053732 _142951 _142952 _142953 x' f x'' g t y h1 h2)). Qed.
Lemma lem8053740 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142953 g t y) (h3 : term341 _142951 _142952 _142953 s t f g x y) : term381 _142951 _142953 t y.
Proof. exact (fun h0 : term335 _142951 _142953 t y => @lem8053739 _142951 _142952 _142953 x' x'' s t f g x y h1 h2 h3). Qed.
Lemma lem8053742 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053743 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term381 _142951 _142953 t y) = (@I ((cart _142951 _142953) -> Prop) t y).
Proof. exact (@lem8053742 (@I ((cart _142951 _142953) -> Prop) t y)). Qed.
Lemma lem8053744 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142953 g t y) (h3 : term341 _142951 _142952 _142953 s t f g x y) : @I ((cart _142951 _142953) -> Prop) t y.
Proof. exact (EQ_MP (@lem8053743 _142951 _142953 t y) (@lem8053740 _142951 _142952 _142953 x' x'' s t f g x y h1 h2 h3)). Qed.
Lemma lem8053747 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8053749 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term335 _142951 _142953 t y) = (term382 _142951 _142953 t y).
Proof. exact (@lem8053747 (@I ((cart _142951 _142953) -> Prop) t y)). Qed.
Lemma lem8053752 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term337 _142951 _142953 g t y) : term382 _142951 _142953 t y.
Proof. exact (EQ_MP (@lem8053749 _142951 _142953 t y) (@lem8053310 _142951 _142953 g t y h1)). Qed.
Lemma lem8053755 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142953 g t y) (h3 : term341 _142951 _142952 _142953 s t f g x y) : False.
Proof. exact (@lem8053752 _142951 _142953 g t y h2 (@lem8053744 _142951 _142952 _142953 x' x'' s t f g x y h1 h2 h3)). Qed.
Lemma lem8053756 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142953 g t y) (h3 : term341 _142951 _142952 _142953 s t f g x y) : term383.
Proof. exact (fun h0 : ~ False => @lem8053755 _142951 _142952 _142953 x' x'' s t f g x y h1 h2 h3). Qed.
Lemma lem8053758 (p : Prop) : (term371 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8053759 : term383 = False.
Proof. exact (@lem8053758 False). Qed.
Lemma lem8053760 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term337 _142951 _142953 g t y) (h3 : term341 _142951 _142952 _142953 s t f g x y) : False.
Proof. exact (EQ_MP (@lem8053759) (@lem8053756 _142951 _142952 _142953 x' x'' s t f g x y h1 h2 h3)). Qed.
Lemma lem8053761 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) (h2 : term354 _142951 _142952 _142953 f g s x t y) : (term335 _142951 _142953 t y) = False.
Proof. exact (prop_ext (fun h3 : term335 _142951 _142953 t y => @lem8053486 _142951 _142952 _142953 f g s x t y h1 h2) (fun h3 : False => @lem8053270 _142951 _142953 t y h1)). Qed.
Lemma lem8053762 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) (h2 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (EQ_MP (@lem8053761 _142951 _142952 _142953 f g s x t y h1 h2) (@lem8053270 _142951 _142953 t y h1)). Qed.
Lemma lem8053763 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142952 s x) (h2 : term354 _142951 _142952 _142953 f g s x t y) : (term335 _142951 _142952 s x) = False.
Proof. exact (prop_ext (fun h3 : term335 _142951 _142952 s x => @lem8053410 _142951 _142952 _142953 f g s x t y h1 h2) (fun h3 : False => @lem8053248 _142951 _142952 s x h1)). Qed.
Lemma lem8053764 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142952 s x) (h2 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (EQ_MP (@lem8053763 _142951 _142952 _142953 f g s x t y h1 h2) (@lem8053248 _142951 _142952 s x h1)). Qed.
Lemma lem8053765 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) (h2 : term354 _142951 _142952 _142953 f g s x t y) : (term335 _142951 _142953 t y) = False.
Proof. exact (prop_ext (fun h3 : term335 _142951 _142953 t y => @lem8053762 _142951 _142952 _142953 f g s x t y h1 h2) (fun h3 : False => @lem8053102 _142951 _142953 t y h1)). Qed.
Lemma lem8053766 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) (h2 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (EQ_MP (@lem8053765 _142951 _142952 _142953 f g s x t y h1 h2) (@lem8053102 _142951 _142953 t y h1)). Qed.
Lemma lem8053767 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142952 s x) (h2 : term354 _142951 _142952 _142953 f g s x t y) : (term335 _142951 _142952 s x) = False.
Proof. exact (prop_ext (fun h3 : term335 _142951 _142952 s x => @lem8053764 _142951 _142952 _142953 f g s x t y h1 h2) (fun h3 : False => @lem8053056 _142951 _142952 s x h1)). Qed.
Lemma lem8053768 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142952 s x) (h2 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (EQ_MP (@lem8053767 _142951 _142952 _142953 f g s x t y h1 h2) (@lem8053056 _142951 _142952 s x h1)). Qed.
Lemma lem8053769 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) (h2 : term354 _142951 _142952 _142953 f g s x t y) : (term335 _142951 _142953 t y) = False.
Proof. exact (prop_ext (fun h3 : term335 _142951 _142953 t y => @lem8053766 _142951 _142952 _142953 f g s x t y h1 h2) (fun h3 : False => @lem8053102 _142951 _142953 t y h1)). Qed.
Lemma lem8053770 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142953 t y) (h2 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (EQ_MP (@lem8053769 _142951 _142952 _142953 f g s x t y h1 h2) (@lem8053102 _142951 _142953 t y h1)). Qed.
Lemma lem8053771 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142952 s x) (h2 : term354 _142951 _142952 _142953 f g s x t y) : (term335 _142951 _142952 s x) = False.
Proof. exact (prop_ext (fun h3 : term335 _142951 _142952 s x => @lem8053768 _142951 _142952 _142953 f g s x t y h1 h2) (fun h3 : False => @lem8053056 _142951 _142952 s x h1)). Qed.
Lemma lem8053772 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term335 _142951 _142952 s x) (h2 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (EQ_MP (@lem8053771 _142951 _142952 _142953 f g s x t y h1 h2) (@lem8053056 _142951 _142952 s x h1)). Qed.
Lemma lem8053773 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term341 _142951 _142952 _142953 s t f g x y) : False.
Proof. exact (or_elim (@lem8053004 _142951 _142952 _142953 s t f g x y h2) (fun h0 : term337 _142951 _142952 f s x => @lem8053623 _142951 _142952 _142953 x' x'' s t f g x y h1 h0 h2) (fun h0 : term337 _142951 _142953 g t y => @lem8053760 _142951 _142952 _142953 x' x'' s t f g x y h1 h0 h2)). Qed.
Lemma lem8053774 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) (h1 : term354 _142951 _142952 _142953 f g s x t y) : False.
Proof. exact (or_elim (@lem8052995 _142951 _142952 _142953 f g s x t y h1) (fun h0 : term335 _142951 _142952 s x => @lem8053772 _142951 _142952 _142953 f g s x t y h0 h1) (fun h0 : term335 _142951 _142953 t y => @lem8053770 _142951 _142952 _142953 f g s x t y h0 h1)). Qed.
Lemma lem8053775 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (x'' : type24 _142951 _142952) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term321 _142951 _142952 _142953 g x' f x'') (h2 : term315 _142951 _142952 _142953 s t f g x y) : False.
Proof. exact (or_elim (@lem8052968 _142951 _142952 _142953 s t f g x y h2) (fun h0 : term354 _142951 _142952 _142953 f g s x t y => @lem8053774 _142951 _142952 _142953 f g s x t y h0) (fun h0 : term341 _142951 _142952 _142953 s t f g x y => @lem8053773 _142951 _142952 _142953 x' x'' s t f g x y h1 h0)). Qed.
Lemma lem8053776 {_142951 _142952 _142953 : Type'} (x' : type24 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term115 _142951 _142952 _142953 g x' f) (h2 : term315 _142951 _142952 _142953 s t f g x y) : False.
Proof. exact (ex_elim (@lem8052765 _142951 _142952 _142953 g x' f h1) (fun x'' : type24 _142951 _142952 => fun h0 : term405 _142951 _142952 _142953 g x' f x'' => @lem8053775 _142951 _142952 _142953 x' x'' s t f g x y h0 h2)). Qed.
Lemma lem8053777 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (h1 : term29 _142951 _142952 _142953 g f) (h2 : term315 _142951 _142952 _142953 s t f g x y) : False.
Proof. exact (ex_elim (@lem8052142 _142951 _142952 _142953 g f h1) (fun x' : type24 _142951 _142953 => fun h0 : term117 _142951 _142952 _142953 g f x' => @lem8053776 _142951 _142952 _142953 x' s t f g x y h0 h2)). Qed.
Lemma lem8053778 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term318 _142951 _142952 _142953 s f g x y) (h2 : term29 _142951 _142952 _142953 g f) : False.
Proof. exact (ex_elim (@lem8052763 _142951 _142952 _142953 s f g x y h1) (fun t : type24 _142951 _142953 => fun h0 : term317 _142951 _142952 _142953 s f g x y t => @lem8053777 _142951 _142952 _142953 s t f g x y h2 h0)). Qed.
Lemma lem8053779 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term93 _142951 _142952 _142953 f g x y) (h2 : term29 _142951 _142952 _142953 g f) : False.
Proof. exact (ex_elim (@lem8052762 _142951 _142952 _142953 f g x y h1) (fun s : type24 _142951 _142952 => fun h0 : term319 _142951 _142952 _142953 f g x y s => @lem8053778 _142951 _142952 _142953 s x y g f h0 h2)). Qed.
Lemma lem8053780 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term93 _142951 _142952 _142953 f g x y) (h2 : term29 _142951 _142952 _142953 g f) : (term93 _142951 _142952 _142953 f g x y) = False.
Proof. exact (prop_ext (fun h3 : term93 _142951 _142952 _142953 f g x y => @lem8053779 _142951 _142952 _142953 x y g f h1 h2) (fun h3 : False => @lem8052089 _142951 _142952 _142953 f g x y h1)). Qed.
Lemma lem8053781 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term93 _142951 _142952 _142953 f g x y) (h2 : term29 _142951 _142952 _142953 g f) : False.
Proof. exact (EQ_MP (@lem8053780 _142951 _142952 _142953 x y g f h1 h2) (@lem8052089 _142951 _142952 _142953 f g x y h1)). Qed.
Lemma lem8053782 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term29 _142951 _142952 _142953 g f) : term92 _142951 _142952 _142953 f g x y.
Proof. exact (fun h0 : term93 _142951 _142952 _142953 f g x y => @lem8053781 _142951 _142952 _142953 x y g f h0 h1). Qed.
Lemma lem8053783 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term29 _142951 _142952 _142953 g f) : (term45 _142951 _142952 _142953 f x g y) = (term67 _142951 _142952 _142953 f g x y).
Proof. exact (EQ_MP (@lem8052088 _142951 _142952 _142953 f g x y) (@lem8053782 _142951 _142952 _142953 x y g f h1)). Qed.
Lemma lem8053788 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term29 _142951 _142952 _142953 g f) : term71 _142951 _142952 _142953 f g x.
Proof. exact (fun y : cart _142951 _142953 => @lem8053783 _142951 _142952 _142953 x y g f h1). Qed.
Lemma lem8053793 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : term29 _142951 _142952 _142953 g f) : term74 _142951 _142952 _142953 f g.
Proof. exact (fun x : cart _142951 _142952 => @lem8053788 _142951 _142952 _142953 x g f h1). Qed.
Lemma lem8053794 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term75 _142951 _142952 _142953 f g.
Proof. exact (fun h0 : term29 _142951 _142952 _142953 g f => @lem8053793 _142951 _142952 _142953 g f h0). Qed.
Lemma lem8053799 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : term87 _142951 _142952 _142953 g.
Proof. exact (fun f : type56 _142951 _142952 => @lem8053794 _142951 _142952 _142953 f g). Qed.
Lemma lem8053804 {_142951 _142952 _142953 : Type'} : term91 _142951 _142952 _142953.
Proof. exact (fun g : type56 _142951 _142953 => @lem8053799 _142951 _142952 _142953 g). Qed.
Lemma lem8053805 {_142951 _142952 _142953 : Type'} : term90 _142951 _142952 _142953.
Proof. exact (EQ_MP (@lem8052083 _142951 _142952 _142953) (@lem8053804 _142951 _142952 _142953)). Qed.
Lemma lem8053806 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : term406 _142951 _142952 _142953 g.
Proof. exact (@lem8053805 _142951 _142952 _142953 g). Qed.
Lemma lem8053807 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term406 _142951 _142952 _142953 g) = (term86 _142951 _142952 _142953 g).
Proof. exact (eq_refl (term406 _142951 _142952 _142953 g)). Qed.
Lemma lem8053808 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : term86 _142951 _142952 _142953 g.
Proof. exact (EQ_MP (@lem8053807 _142951 _142952 _142953 g) (@lem8053806 _142951 _142952 _142953 g)). Qed.
Lemma lem8053809 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : term407 _142951 _142952 _142953 g f.
Proof. exact (@lem8053808 _142951 _142952 _142953 g f). Qed.
Lemma lem8053810 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term407 _142951 _142952 _142953 g f) = (term77 _142951 _142952 _142953 f g).
Proof. exact (eq_refl (term407 _142951 _142952 _142953 g f)). Qed.
Lemma lem8053811 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term77 _142951 _142952 _142953 f g.
Proof. exact (EQ_MP (@lem8053810 _142951 _142952 _142953 f g) (@lem8053809 _142951 _142952 _142953 g f)). Qed.
Lemma lem8053813 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term77 _142951 _142952 _142953 f g.
Proof. exact (@lem8051847 _142951 _142952 _142953 f g (@lem8053811 _142951 _142952 _142953 f g)). Qed.
Lemma lem8053814 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term78 _142951 _142952 _142953 f g) : False.
Proof. exact (@lem8053813 _142951 _142952 _142953 f g (@lem8051831 _142951 _142952 _142953 f g h1)). Qed.
Lemma lem8053815 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term78 _142951 _142952 _142953 f g) : (term78 _142951 _142952 _142953 f g) = False.
Proof. exact (prop_ext (fun h2 : term78 _142951 _142952 _142953 f g => @lem8053814 _142951 _142952 _142953 f g h1) (fun h2 : False => @lem8051831 _142951 _142952 _142953 f g h1)). Qed.
Lemma lem8053816 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term78 _142951 _142952 _142953 f g) : False.
Proof. exact (EQ_MP (@lem8053815 _142951 _142952 _142953 f g h1) (@lem8051831 _142951 _142952 _142953 f g h1)). Qed.
Lemma lem8053817 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term77 _142951 _142952 _142953 f g.
Proof. exact (fun h0 : term78 _142951 _142952 _142953 f g => @lem8053816 _142951 _142952 _142953 f g h0). Qed.
Lemma lem8053818 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term75 _142951 _142952 _142953 f g.
Proof. exact (EQ_MP (@lem8051830 _142951 _142952 _142953 f g) (@lem8053817 _142951 _142952 _142953 f g)). Qed.
Lemma lem8053819 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term20 _142951 _142952 _142953 f g.
Proof. exact (EQ_MP (@lem8051826 _142951 _142952 _142953 f g) (@lem8053818 _142951 _142952 _142953 f g)). Qed.
Lemma lem8053820 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term19 _142951 _142952 _142953 f g.
Proof. exact (EQ_MP (@lem8051596 _142951 _142952 _142953 f g) (@lem8053819 _142951 _142952 _142953 f g)). Qed.
Lemma lem8053821 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term7 _142951 _142952 f) (h2 : term7 _142951 _142953 g) : term18 _142951 _142952 _142953 f g.
Proof. exact (@lem8053820 _142951 _142952 _142953 f g (@lem8051520 _142951 _142952 _142953 f g h1 h2)). Qed.
