Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm309905_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Lemma lem307613 {A : Type'} (lt2 : type1402 A) (h1 : term0 A lt2) : term0 A lt2.
Proof. exact (h1). Qed.
Lemma lem307614 {A : Type'} (lt2 : type1402 A) (h1 : term1 A lt2) : term1 A lt2.
Proof. exact (h1). Qed.
Lemma lem307615 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term0 A lt2) : term2 A lt2 P.
Proof. exact (@lem307613 A lt2 h1 (term3 A P)). Qed.
Lemma lem307616 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term2 A lt2 P) = (term4 A lt2 P).
Proof. exact (eq_refl (term2 A lt2 P)). Qed.
Lemma lem307617 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term0 A lt2) : term4 A lt2 P.
Proof. exact (EQ_MP (@lem307616 A lt2 P) (@lem307615 A P lt2 h1)). Qed.
Lemma lem307618 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term1 A lt2) : term5 A lt2 P.
Proof. exact (@lem307614 A lt2 h1 (term3 A P)). Qed.
Lemma lem307619 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term5 A lt2 P) = (term6 A lt2 P).
Proof. exact (eq_refl (term5 A lt2 P)). Qed.
Lemma lem307620 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term1 A lt2) : term6 A lt2 P.
Proof. exact (EQ_MP (@lem307619 A lt2 P) (@lem307618 A P lt2 h1)). Qed.
Lemma lem307630 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem307631 {A : Type'} (f : A -> Prop) (y : A) : (term8 A f y) = (f y).
Proof. exact (@lem307630 A Prop f y). Qed.
Lemma lem307632 {A : Type'} (P : A -> Prop) (x : A) : (term9 A P x) = (term10 A P x).
Proof. exact (@lem307631 A (term3 A P) x). Qed.
Lemma lem307633 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem307634 {A : Type'} (P : A -> Prop) : (term12 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem307633 A P x)). Qed.
Lemma lem307635 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem307636 {A : Type'} (P : A -> Prop) (x : A) : (term9 A P x) = (term10 A P x).
Proof. exact (MK_COMB (@lem307634 A P) (@lem307635 A x)). Qed.
Lemma lem307637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307638 {A : Type'} (P : A -> Prop) (x : A) : (term13 A P x) = (term14 A P x).
Proof. exact (MK_COMB (@lem307637) (@lem307636 A P x)). Qed.
Lemma lem307639 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem307640 {A : Type'} (P : A -> Prop) (x : A) : ((term9 A P x) = (term10 A P x)) = ((term10 A P x) = (term11 A P x)).
Proof. exact (MK_COMB (@lem307638 A P x) (@lem307639 A P x)). Qed.
Lemma lem307641 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (EQ_MP (@lem307640 A P x) (@lem307632 A P x)). Qed.
Lemma lem307642 {A : Type'} (P : A -> Prop) : (term12 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem307641 A P x)). Qed.
Lemma lem307643 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem307644 {A : Type'} (P : A -> Prop) : (term15 A P) = (term16 A P).
Proof. exact (MK_COMB (@lem307643 A) (@lem307642 A P)). Qed.
Lemma lem307649 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307650 {A : Type'} (P : A -> Prop) : (term17 A P) = (term18 A P).
Proof. exact (MK_COMB (@lem307649) (@lem307644 A P)). Qed.
Lemma lem307658 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem307659 {A : Type'} (f : A -> Prop) (y : A) : (term8 A f y) = (f y).
Proof. exact (@lem307658 A Prop f y). Qed.
Lemma lem307660 {A : Type'} (P : A -> Prop) (x : A) : (term9 A P x) = (term10 A P x).
Proof. exact (@lem307659 A (term3 A P) x). Qed.
Lemma lem307661 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem307662 {A : Type'} (P : A -> Prop) : (term12 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem307661 A P x)). Qed.
Lemma lem307663 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem307664 {A : Type'} (P : A -> Prop) (x : A) : (term9 A P x) = (term10 A P x).
Proof. exact (MK_COMB (@lem307662 A P) (@lem307663 A x)). Qed.
Lemma lem307665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307666 {A : Type'} (P : A -> Prop) (x : A) : (term13 A P x) = (term14 A P x).
Proof. exact (MK_COMB (@lem307665) (@lem307664 A P x)). Qed.
Lemma lem307667 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem307668 {A : Type'} (P : A -> Prop) (x : A) : ((term9 A P x) = (term10 A P x)) = ((term10 A P x) = (term11 A P x)).
Proof. exact (MK_COMB (@lem307666 A P x) (@lem307667 A P x)). Qed.
Lemma lem307669 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (EQ_MP (@lem307668 A P x) (@lem307660 A P x)). Qed.
Lemma lem307670 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem307671 {A : Type'} (P : A -> Prop) (x : A) : (term19 A P x) = (term20 A P x).
Proof. exact (MK_COMB (@lem307670) (@lem307669 A P x)). Qed.
Lemma lem307679 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem307680 {A : Type'} (f : A -> Prop) (y : A) : (term8 A f y) = (f y).
Proof. exact (@lem307679 A Prop f y). Qed.
Lemma lem307681 {A : Type'} (P : A -> Prop) (y : A) : (term9 A P y) = (term10 A P y).
Proof. exact (@lem307680 A (term3 A P) y). Qed.
Lemma lem307682 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem307683 {A : Type'} (P : A -> Prop) : (term12 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem307682 A P x)). Qed.
Lemma lem307684 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem307685 {A : Type'} (P : A -> Prop) (y : A) : (term9 A P y) = (term10 A P y).
Proof. exact (MK_COMB (@lem307683 A P) (@lem307684 A y)). Qed.
Lemma lem307686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307687 {A : Type'} (P : A -> Prop) (y : A) : (term13 A P y) = (term14 A P y).
Proof. exact (MK_COMB (@lem307686) (@lem307685 A P y)). Qed.
Lemma lem307688 {A : Type'} (P : A -> Prop) (y : A) : (term10 A P y) = (term11 A P y).
Proof. exact (eq_refl (term10 A P y)). Qed.
Lemma lem307689 {A : Type'} (P : A -> Prop) (y : A) : ((term9 A P y) = (term10 A P y)) = ((term10 A P y) = (term11 A P y)).
Proof. exact (MK_COMB (@lem307687 A P y) (@lem307688 A P y)). Qed.
Lemma lem307690 {A : Type'} (P : A -> Prop) (y : A) : (term10 A P y) = (term11 A P y).
Proof. exact (EQ_MP (@lem307689 A P y) (@lem307681 A P y)). Qed.
Lemma lem307691 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem307692 {A : Type'} (P : A -> Prop) (y : A) : (term21 A P y) = (term22 A P y).
Proof. exact (MK_COMB (@lem307691) (@lem307690 A P y)). Qed.
Lemma lem307694 (t : Prop) : (term23 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem307695 {A : Type'} (P : A -> Prop) (y : A) : (term22 A P y) = (P y).
Proof. exact (@lem307694 (P y)). Qed.
Lemma lem307696 {A : Type'} (P : A -> Prop) (y : A) : (term21 A P y) = (P y).
Proof. exact (TRANS (@lem307692 A P y) (@lem307695 A P y)). Qed.
Lemma lem307697 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term24 A lt2 y x) = (term24 A lt2 y x).
Proof. exact (eq_refl (term24 A lt2 y x)). Qed.
Lemma lem307698 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term25 A lt2 x P y) = (term26 A lt2 x P y).
Proof. exact (MK_COMB (@lem307697 A lt2 y x) (@lem307696 A P y)). Qed.
Lemma lem307701 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term27 A lt2 x P) = (term28 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem307698 A lt2 x P y)). Qed.
Lemma lem307702 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem307703 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term29 A lt2 x P) = (term30 A lt2 x P).
Proof. exact (MK_COMB (@lem307702 A) (@lem307701 A lt2 x P)). Qed.
Lemma lem307708 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term31 A lt2 x P) = (term32 A lt2 x P).
Proof. exact (MK_COMB (@lem307671 A P x) (@lem307703 A lt2 x P)). Qed.
Lemma lem307711 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term33 A lt2 P) = (term34 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem307708 A lt2 x P)). Qed.
Lemma lem307712 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem307713 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term35 A lt2 P) = (term36 A lt2 P).
Proof. exact (MK_COMB (@lem307712 A) (@lem307711 A lt2 P)). Qed.
Lemma lem307718 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term4 A lt2 P) = (term37 A lt2 P).
Proof. exact (MK_COMB (@lem307650 A P) (@lem307713 A lt2 P)). Qed.
Lemma lem307721 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307722 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term38 A lt2 P) = (term39 A lt2 P).
Proof. exact (MK_COMB (@lem307721) (@lem307718 A lt2 P)). Qed.
Lemma lem307741 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term40 A lt2 P) = (term40 A lt2 P).
Proof. exact (eq_refl (term40 A lt2 P)). Qed.
Lemma lem307742 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term41 A lt2 P) = (term42 A lt2 P).
Proof. exact (MK_COMB (@lem307722 A lt2 P) (@lem307741 A lt2 P)). Qed.
Lemma lem307745 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term42 A lt2 P) = (term41 A lt2 P).
Proof. exact (SYM (@lem307742 A lt2 P)). Qed.
Lemma lem307763 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem307764 {A : Type'} (f : A -> Prop) (y : A) : (term8 A f y) = (f y).
Proof. exact (@lem307763 A Prop f y). Qed.
Lemma lem307765 {A : Type'} (P : A -> Prop) (y : A) : (term9 A P y) = (term10 A P y).
Proof. exact (@lem307764 A (term3 A P) y). Qed.
Lemma lem307766 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem307767 {A : Type'} (P : A -> Prop) : (term12 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem307766 A P x)). Qed.
Lemma lem307768 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem307769 {A : Type'} (P : A -> Prop) (y : A) : (term9 A P y) = (term10 A P y).
Proof. exact (MK_COMB (@lem307767 A P) (@lem307768 A y)). Qed.
Lemma lem307770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307771 {A : Type'} (P : A -> Prop) (y : A) : (term13 A P y) = (term14 A P y).
Proof. exact (MK_COMB (@lem307770) (@lem307769 A P y)). Qed.
Lemma lem307772 {A : Type'} (P : A -> Prop) (y : A) : (term10 A P y) = (term11 A P y).
Proof. exact (eq_refl (term10 A P y)). Qed.
Lemma lem307773 {A : Type'} (P : A -> Prop) (y : A) : ((term9 A P y) = (term10 A P y)) = ((term10 A P y) = (term11 A P y)).
Proof. exact (MK_COMB (@lem307771 A P y) (@lem307772 A P y)). Qed.
Lemma lem307774 {A : Type'} (P : A -> Prop) (y : A) : (term10 A P y) = (term11 A P y).
Proof. exact (EQ_MP (@lem307773 A P y) (@lem307765 A P y)). Qed.
Lemma lem307775 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term24 A lt2 y x) = (term24 A lt2 y x).
Proof. exact (eq_refl (term24 A lt2 y x)). Qed.
Lemma lem307776 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term43 A lt2 x P y) = (term44 A lt2 x P y).
Proof. exact (MK_COMB (@lem307775 A lt2 y x) (@lem307774 A P y)). Qed.
Lemma lem307779 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term45 A lt2 x P) = (term46 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem307776 A lt2 x P y)). Qed.
Lemma lem307780 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem307781 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term47 A lt2 x P) = (term48 A lt2 x P).
Proof. exact (MK_COMB (@lem307780 A) (@lem307779 A lt2 x P)). Qed.
Lemma lem307786 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307787 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term49 A lt2 x P) = (term50 A lt2 x P).
Proof. exact (MK_COMB (@lem307786) (@lem307781 A lt2 x P)). Qed.
Lemma lem307789 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem307790 {A : Type'} (f : A -> Prop) (y : A) : (term8 A f y) = (f y).
Proof. exact (@lem307789 A Prop f y). Qed.
Lemma lem307791 {A : Type'} (P : A -> Prop) (x : A) : (term9 A P x) = (term10 A P x).
Proof. exact (@lem307790 A (term3 A P) x). Qed.
Lemma lem307792 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem307793 {A : Type'} (P : A -> Prop) : (term12 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem307792 A P x)). Qed.
Lemma lem307794 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem307795 {A : Type'} (P : A -> Prop) (x : A) : (term9 A P x) = (term10 A P x).
Proof. exact (MK_COMB (@lem307793 A P) (@lem307794 A x)). Qed.
Lemma lem307796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307797 {A : Type'} (P : A -> Prop) (x : A) : (term13 A P x) = (term14 A P x).
Proof. exact (MK_COMB (@lem307796) (@lem307795 A P x)). Qed.
Lemma lem307798 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem307799 {A : Type'} (P : A -> Prop) (x : A) : ((term9 A P x) = (term10 A P x)) = ((term10 A P x) = (term11 A P x)).
Proof. exact (MK_COMB (@lem307797 A P x) (@lem307798 A P x)). Qed.
Lemma lem307800 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (EQ_MP (@lem307799 A P x) (@lem307791 A P x)). Qed.
Lemma lem307801 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term51 A lt2 P x) = (term52 A lt2 P x).
Proof. exact (MK_COMB (@lem307787 A lt2 x P) (@lem307800 A P x)). Qed.
Lemma lem307804 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term53 A lt2 P) = (term54 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem307801 A lt2 P x)). Qed.
Lemma lem307805 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem307806 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term55 A lt2 P) = (term56 A lt2 P).
Proof. exact (MK_COMB (@lem307805 A) (@lem307804 A lt2 P)). Qed.
Lemma lem307811 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307812 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term57 A lt2 P) = (term58 A lt2 P).
Proof. exact (MK_COMB (@lem307811) (@lem307806 A lt2 P)). Qed.
Lemma lem307818 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem307819 {A : Type'} (f : A -> Prop) (y : A) : (term8 A f y) = (f y).
Proof. exact (@lem307818 A Prop f y). Qed.
Lemma lem307820 {A : Type'} (P : A -> Prop) (x : A) : (term9 A P x) = (term10 A P x).
Proof. exact (@lem307819 A (term3 A P) x). Qed.
Lemma lem307821 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem307822 {A : Type'} (P : A -> Prop) : (term12 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem307821 A P x)). Qed.
Lemma lem307823 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem307824 {A : Type'} (P : A -> Prop) (x : A) : (term9 A P x) = (term10 A P x).
Proof. exact (MK_COMB (@lem307822 A P) (@lem307823 A x)). Qed.
Lemma lem307825 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307826 {A : Type'} (P : A -> Prop) (x : A) : (term13 A P x) = (term14 A P x).
Proof. exact (MK_COMB (@lem307825) (@lem307824 A P x)). Qed.
Lemma lem307827 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem307828 {A : Type'} (P : A -> Prop) (x : A) : ((term9 A P x) = (term10 A P x)) = ((term10 A P x) = (term11 A P x)).
Proof. exact (MK_COMB (@lem307826 A P x) (@lem307827 A P x)). Qed.
Lemma lem307829 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (EQ_MP (@lem307828 A P x) (@lem307820 A P x)). Qed.
Lemma lem307830 {A : Type'} (P : A -> Prop) : (term12 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem307829 A P x)). Qed.
Lemma lem307831 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem307832 {A : Type'} (P : A -> Prop) : (term59 A P) = (term60 A P).
Proof. exact (MK_COMB (@lem307831 A) (@lem307830 A P)). Qed.
Lemma lem307837 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term6 A lt2 P) = (term61 A lt2 P).
Proof. exact (MK_COMB (@lem307812 A lt2 P) (@lem307832 A P)). Qed.
Lemma lem307840 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem307841 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term62 A lt2 P) = (term63 A lt2 P).
Proof. exact (MK_COMB (@lem307840) (@lem307837 A lt2 P)). Qed.
Lemma lem307860 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term64 A lt2 P) = (term64 A lt2 P).
Proof. exact (eq_refl (term64 A lt2 P)). Qed.
Lemma lem307861 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term65 A lt2 P) = (term66 A lt2 P).
Proof. exact (MK_COMB (@lem307841 A lt2 P) (@lem307860 A lt2 P)). Qed.
Lemma lem307864 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term66 A lt2 P) = (term65 A lt2 P).
Proof. exact (SYM (@lem307861 A lt2 P)). Qed.
Lemma lem307866 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem307867 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term42 A lt2 P) = (term68 A lt2 P).
Proof. exact (@lem307866 (term42 A lt2 P)). Qed.
Lemma lem307868 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term68 A lt2 P) = (term42 A lt2 P).
Proof. exact (SYM (@lem307867 A lt2 P)). Qed.
Lemma lem307869 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term69 A lt2 P) : term69 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem307872 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term68 A lt2 P) : term68 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem307873 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term70 A lt2 P.
Proof. exact (fun h0 : term68 A lt2 P => @lem307872 A lt2 P h0). Qed.
Lemma lem307874 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term70 A lt2 P) : term70 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem307875 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term68 A lt2 P) : term68 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem307876 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term68 A lt2 P) (h2 : term70 A lt2 P) : term68 A lt2 P.
Proof. exact (@lem307874 A lt2 P h2 (@lem307875 A lt2 P h1)). Qed.
Lemma lem307877 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term68 A lt2 P) : term71 A lt2 P.
Proof. exact (fun h0 : term70 A lt2 P => @lem307876 A lt2 P h1 h0). Qed.
Lemma lem307878 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term70 A lt2 P) : term70 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem307879 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term68 A lt2 P) (h2 : term70 A lt2 P) : term68 A lt2 P.
Proof. exact (@lem307877 A lt2 P h1 (@lem307878 A lt2 P h2)). Qed.
Lemma lem307880 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term70 A lt2 P) : term70 A lt2 P.
Proof. exact (fun h0 : term68 A lt2 P => @lem307879 A lt2 P h0 h1). Qed.
Lemma lem307881 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term72 A lt2 P.
Proof. exact (fun h0 : term70 A lt2 P => @lem307880 A lt2 P h0). Qed.
Lemma lem307884 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term70 A lt2 P.
Proof. exact (@lem307881 A lt2 P (@lem307873 A lt2 P)). Qed.
Lemma lem307885 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term70 A lt2 P.
Proof. exact (@lem307884 A lt2 P). Qed.
Lemma lem307895 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem307896 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term68 A lt2 P) = (term73 A lt2 P).
Proof. exact (@lem307895 (term69 A lt2 P)). Qed.
Lemma lem307898 (t : Prop) : (term23 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem307899 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term73 A lt2 P) = (term42 A lt2 P).
Proof. exact (@lem307898 (term42 A lt2 P)). Qed.
Lemma lem307902 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term68 A lt2 P) = (term42 A lt2 P).
Proof. exact (TRANS (@lem307896 A lt2 P) (@lem307899 A lt2 P)). Qed.
Lemma lem307983 {A : Type'} (P : A -> Prop) : (term74 A P) = (term75 A P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem307902 A lt2 P)). Qed.
Lemma lem307984 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem307985 {A : Type'} (P : A -> Prop) : (term76 A P) = (term77 A P).
Proof. exact (MK_COMB (@lem307984 A) (@lem307983 A P)). Qed.
Lemma lem307990 {A : Type'} : (term78 A) = (term79 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem307985 A P)). Qed.
Lemma lem307991 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem308000 {A : Type'} : (term80 A) = (term81 A).
Proof. exact (MK_COMB (@lem307991 A) (@lem307990 A)). Qed.
Lemma lem308001 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem308002 {A : Type'} (P : A -> Prop) : (term82 A P) = (term82 A P).
Proof. exact (fun_ext (fun x : A => @lem308001 A P x)). Qed.
Lemma lem308003 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308004 {A : Type'} (P : A -> Prop) : (term83 A P) = (term83 A P).
Proof. exact (MK_COMB (@lem308003 A) (@lem308002 A P)). Qed.
Lemma lem308005 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem308010 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term26 A lt2 x P y) = (term26 A lt2 x P y).
Proof. exact (eq_refl (term26 A lt2 x P y)). Qed.
Lemma lem308011 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term28 A lt2 x P) = (term28 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem308010 A lt2 x P y)). Qed.
Lemma lem308012 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308013 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term30 A lt2 x P) = (term30 A lt2 x P).
Proof. exact (MK_COMB (@lem308012 A) (@lem308011 A lt2 x P)). Qed.
Lemma lem308014 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem308015 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term84 A lt2 x P) = (term84 A lt2 x P).
Proof. exact (MK_COMB (@lem308014) (@lem308013 A lt2 x P)). Qed.
Lemma lem308016 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term85 A lt2 P x) = (term85 A lt2 P x).
Proof. exact (MK_COMB (@lem308015 A lt2 x P) (@lem308005 A P x)). Qed.
Lemma lem308017 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term86 A lt2 P) = (term86 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem308016 A lt2 P x)). Qed.
Lemma lem308018 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308019 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term87 A lt2 P) = (term87 A lt2 P).
Proof. exact (MK_COMB (@lem308018 A) (@lem308017 A lt2 P)). Qed.
Lemma lem308020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem308021 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term88 A lt2 P) = (term88 A lt2 P).
Proof. exact (MK_COMB (@lem308020) (@lem308019 A lt2 P)). Qed.
Lemma lem308022 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term40 A lt2 P) = (term40 A lt2 P).
Proof. exact (MK_COMB (@lem308021 A lt2 P) (@lem308004 A P)). Qed.
Lemma lem308027 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term26 A lt2 x P y) = (term26 A lt2 x P y).
Proof. exact (eq_refl (term26 A lt2 x P y)). Qed.
Lemma lem308028 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term28 A lt2 x P) = (term28 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem308027 A lt2 x P y)). Qed.
Lemma lem308029 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308030 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term30 A lt2 x P) = (term30 A lt2 x P).
Proof. exact (MK_COMB (@lem308029 A) (@lem308028 A lt2 x P)). Qed.
Lemma lem308035 {A : Type'} (P : A -> Prop) (x : A) : (term20 A P x) = (term20 A P x).
Proof. exact (eq_refl (term20 A P x)). Qed.
Lemma lem308036 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term32 A lt2 x P) = (term32 A lt2 x P).
Proof. exact (MK_COMB (@lem308035 A P x) (@lem308030 A lt2 x P)). Qed.
Lemma lem308037 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term34 A lt2 P) = (term34 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem308036 A lt2 x P)). Qed.
Lemma lem308038 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem308039 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term36 A lt2 P) = (term36 A lt2 P).
Proof. exact (MK_COMB (@lem308038 A) (@lem308037 A lt2 P)). Qed.
Lemma lem308042 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term11 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem308043 {A : Type'} (P : A -> Prop) : (term3 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem308042 A P x)). Qed.
Lemma lem308044 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem308045 {A : Type'} (P : A -> Prop) : (term16 A P) = (term16 A P).
Proof. exact (MK_COMB (@lem308044 A) (@lem308043 A P)). Qed.
Lemma lem308046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem308047 {A : Type'} (P : A -> Prop) : (term18 A P) = (term18 A P).
Proof. exact (MK_COMB (@lem308046) (@lem308045 A P)). Qed.
Lemma lem308048 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term37 A lt2 P) = (term37 A lt2 P).
Proof. exact (MK_COMB (@lem308047 A P) (@lem308039 A lt2 P)). Qed.
Lemma lem308049 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem308050 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term39 A lt2 P) = (term39 A lt2 P).
Proof. exact (MK_COMB (@lem308049) (@lem308048 A lt2 P)). Qed.
Lemma lem308051 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term42 A lt2 P) = (term42 A lt2 P).
Proof. exact (MK_COMB (@lem308050 A lt2 P) (@lem308022 A lt2 P)). Qed.
Lemma lem308052 {A : Type'} (P : A -> Prop) : (term75 A P) = (term75 A P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem308051 A lt2 P)). Qed.
Lemma lem308053 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem308054 {A : Type'} (P : A -> Prop) : (term77 A P) = (term77 A P).
Proof. exact (MK_COMB (@lem308053 A) (@lem308052 A P)). Qed.
Lemma lem308055 {A : Type'} : (term79 A) = (term79 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem308054 A P)). Qed.
Lemma lem308056 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem308057 {A : Type'} : (term81 A) = (term81 A).
Proof. exact (MK_COMB (@lem308056 A) (@lem308055 A)). Qed.
Lemma lem308122 {A : Type'} : (term80 A) = (term81 A).
Proof. exact (TRANS (@lem308000 A) (@lem308057 A)). Qed.
Lemma lem308123 {A : Type'} : (term81 A) = (term80 A).
Proof. exact (SYM (@lem308122 A)). Qed.
Lemma lem308124 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term37 A lt2 P) : term37 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem308125 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term87 A lt2 P) : term87 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem308127 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem308128 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (term89 A P x).
Proof. exact (@lem308127 (P x)). Qed.
Lemma lem308129 {A : Type'} (P : A -> Prop) (x : A) : (term89 A P x) = (P x).
Proof. exact (SYM (@lem308128 A P x)). Qed.
Lemma lem308130 {A : Type'} (P : A -> Prop) (x : A) (h1 : term11 A P x) : term11 A P x.
Proof. exact (h1). Qed.
Lemma lem308133 {A : Type'} (P : A -> Prop) (x : A) : (term22 A P x) = (P x).
Proof. exact (@lem16933 (P x)). Qed.
Lemma lem308134 {A : Type'} (P : A -> Prop) : (term90 A P) = (term60 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem308135 {A : Type'} (P : A -> Prop) : (term91 A P) = (term92 A P).
Proof. exact (@lem308134 A (term3 A P)). Qed.
Lemma lem308136 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem308137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem308138 {A : Type'} (P : A -> Prop) (x : A) : (term21 A P x) = (term22 A P x).
Proof. exact (MK_COMB (@lem308137) (@lem308136 A P x)). Qed.
Lemma lem308139 {A : Type'} (P : A -> Prop) (x : A) : (term21 A P x) = (P x).
Proof. exact (TRANS (@lem308138 A P x) (@lem308133 A P x)). Qed.
Lemma lem308140 {A : Type'} (P : A -> Prop) : (term93 A P) = (term82 A P).
Proof. exact (fun_ext (fun x : A => @lem308139 A P x)). Qed.
Lemma lem308141 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308142 {A : Type'} (P : A -> Prop) : (term92 A P) = (term83 A P).
Proof. exact (MK_COMB (@lem308141 A) (@lem308140 A P)). Qed.
Lemma lem308143 {A : Type'} (P : A -> Prop) : (term91 A P) = (term83 A P).
Proof. exact (TRANS (@lem308135 A P) (@lem308142 A P)). Qed.
Lemma lem308151 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term26 A lt2 x P y) = (term94 A lt2 x P y).
Proof. exact (@lem17265 (lt2 y x) (P y)). Qed.
Lemma lem308152 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term28 A lt2 x P) = (term95 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem308151 A lt2 x P y)). Qed.
Lemma lem308153 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308154 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term30 A lt2 x P) = (term96 A lt2 x P).
Proof. exact (MK_COMB (@lem308153 A) (@lem308152 A lt2 x P)). Qed.
Lemma lem308156 {A : Type'} (P : A -> Prop) (x : A) : (term20 A P x) = (term20 A P x).
Proof. exact (eq_refl (term20 A P x)). Qed.
Lemma lem308157 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term32 A lt2 x P) = (term97 A lt2 x P).
Proof. exact (MK_COMB (@lem308156 A P x) (@lem308154 A lt2 x P)). Qed.
Lemma lem308158 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term34 A lt2 P) = (term98 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem308157 A lt2 x P)). Qed.
Lemma lem308159 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem308160 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term36 A lt2 P) = (term99 A lt2 P).
Proof. exact (MK_COMB (@lem308159 A) (@lem308158 A lt2 P)). Qed.
Lemma lem308161 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem308162 {A : Type'} (P : A -> Prop) : (term100 A P) = (term101 A P).
Proof. exact (MK_COMB (@lem308161) (@lem308143 A P)). Qed.
Lemma lem308163 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term102 A lt2 P) = (term103 A lt2 P).
Proof. exact (MK_COMB (@lem308162 A P) (@lem308160 A lt2 P)). Qed.
Lemma lem308164 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term37 A lt2 P) = (term102 A lt2 P).
Proof. exact (@lem17265 (term16 A P) (term36 A lt2 P)). Qed.
Lemma lem308165 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term37 A lt2 P) = (term103 A lt2 P).
Proof. exact (TRANS (@lem308164 A lt2 P) (@lem308163 A lt2 P)). Qed.
Lemma lem308252 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem308253 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (@lem308252 A P Q). Qed.
Lemma lem308254 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term106 A lt2 P) = (term107 A lt2 P).
Proof. exact (@lem308253 A (term83 A P) (term98 A lt2 P)). Qed.
Lemma lem308255 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term108 A lt2 P x) = (term97 A lt2 x P).
Proof. exact (eq_refl (term108 A lt2 P x)). Qed.
Lemma lem308256 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term109 A lt2 P) = (term98 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem308255 A lt2 x P)). Qed.
Lemma lem308257 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem308258 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term110 A lt2 P) = (term99 A lt2 P).
Proof. exact (MK_COMB (@lem308257 A) (@lem308256 A lt2 P)). Qed.
Lemma lem308259 {A : Type'} (P : A -> Prop) : (term101 A P) = (term101 A P).
Proof. exact (eq_refl (term101 A P)). Qed.
Lemma lem308260 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term106 A lt2 P) = (term103 A lt2 P).
Proof. exact (MK_COMB (@lem308259 A P) (@lem308258 A lt2 P)). Qed.
Lemma lem308261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem308262 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term111 A lt2 P) = (term112 A lt2 P).
Proof. exact (MK_COMB (@lem308261) (@lem308260 A lt2 P)). Qed.
Lemma lem308263 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term108 A lt2 P x) = (term97 A lt2 x P).
Proof. exact (eq_refl (term108 A lt2 P x)). Qed.
Lemma lem308264 {A : Type'} (P : A -> Prop) : (term101 A P) = (term101 A P).
Proof. exact (eq_refl (term101 A P)). Qed.
Lemma lem308265 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term113 A lt2 P x) = (term114 A lt2 x P).
Proof. exact (MK_COMB (@lem308264 A P) (@lem308263 A lt2 x P)). Qed.
Lemma lem308266 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term115 A lt2 P) = (term116 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem308265 A lt2 x P)). Qed.
Lemma lem308267 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem308268 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term107 A lt2 P) = (term117 A lt2 P).
Proof. exact (MK_COMB (@lem308267 A) (@lem308266 A lt2 P)). Qed.
Lemma lem308269 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term106 A lt2 P) = (term107 A lt2 P)) = ((term103 A lt2 P) = (term117 A lt2 P)).
Proof. exact (MK_COMB (@lem308262 A lt2 P) (@lem308268 A lt2 P)). Qed.
Lemma lem308271 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term103 A lt2 P) = (term117 A lt2 P).
Proof. exact (EQ_MP (@lem308269 A lt2 P) (@lem308254 A lt2 P)). Qed.
Lemma lem308272 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term37 A lt2 P) = (term117 A lt2 P).
Proof. exact (TRANS (@lem308165 A lt2 P) (@lem308271 A lt2 P)). Qed.
Lemma lem308273 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term37 A lt2 P) : term117 A lt2 P.
Proof. exact (EQ_MP (@lem308272 A lt2 P) (@lem308124 A lt2 P h1)). Qed.
Lemma lem308280 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term118 A lt2 x P y) = (term119 A lt2 x P y).
Proof. exact (@lem17362 (lt2 y x) (P y)). Qed.
Lemma lem308281 {A : Type'} (P : A -> Prop) : (term120 A P) = (term16 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem308282 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term121 A lt2 x P) = (term122 A lt2 x P).
Proof. exact (@lem308281 A (term28 A lt2 x P)). Qed.
Lemma lem308283 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term123 A lt2 x P y) = (term26 A lt2 x P y).
Proof. exact (eq_refl (term123 A lt2 x P y)). Qed.
Lemma lem308284 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem308285 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term124 A lt2 x P y) = (term118 A lt2 x P y).
Proof. exact (MK_COMB (@lem308284) (@lem308283 A lt2 x P y)). Qed.
Lemma lem308286 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term124 A lt2 x P y) = (term119 A lt2 x P y).
Proof. exact (TRANS (@lem308285 A lt2 x P y) (@lem308280 A lt2 x P y)). Qed.
Lemma lem308287 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term125 A lt2 x P) = (term126 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem308286 A lt2 x P y)). Qed.
Lemma lem308288 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem308289 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term122 A lt2 x P) = (term127 A lt2 x P).
Proof. exact (MK_COMB (@lem308288 A) (@lem308287 A lt2 x P)). Qed.
Lemma lem308290 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term121 A lt2 x P) = (term127 A lt2 x P).
Proof. exact (TRANS (@lem308282 A lt2 x P) (@lem308289 A lt2 x P)). Qed.
Lemma lem308291 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem308292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem308293 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term128 A lt2 x P) = (term129 A lt2 x P).
Proof. exact (MK_COMB (@lem308292) (@lem308290 A lt2 x P)). Qed.
Lemma lem308294 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term130 A lt2 P x) = (term131 A lt2 P x).
Proof. exact (MK_COMB (@lem308293 A lt2 x P) (@lem308291 A P x)). Qed.
Lemma lem308295 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term85 A lt2 P x) = (term130 A lt2 P x).
Proof. exact (@lem17265 (term30 A lt2 x P) (P x)). Qed.
Lemma lem308296 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term85 A lt2 P x) = (term131 A lt2 P x).
Proof. exact (TRANS (@lem308295 A lt2 P x) (@lem308294 A lt2 P x)). Qed.
Lemma lem308297 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term86 A lt2 P) = (term132 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem308296 A lt2 P x)). Qed.
Lemma lem308298 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308299 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term87 A lt2 P) = (term133 A lt2 P).
Proof. exact (MK_COMB (@lem308298 A) (@lem308297 A lt2 P)). Qed.
Lemma lem308382 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem308383 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (@lem308382 A P Q). Qed.
Lemma lem308384 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term136 A lt2 P x) = (term137 A lt2 P x).
Proof. exact (@lem308383 A (term126 A lt2 x P) (P x)). Qed.
Lemma lem308385 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term138 A lt2 x P y) = (term119 A lt2 x P y).
Proof. exact (eq_refl (term138 A lt2 x P y)). Qed.
Lemma lem308386 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term139 A lt2 x P) = (term126 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem308385 A lt2 x P y)). Qed.
Lemma lem308387 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem308388 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term140 A lt2 x P) = (term127 A lt2 x P).
Proof. exact (MK_COMB (@lem308387 A) (@lem308386 A lt2 x P)). Qed.
Lemma lem308389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem308390 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term141 A lt2 x P) = (term129 A lt2 x P).
Proof. exact (MK_COMB (@lem308389) (@lem308388 A lt2 x P)). Qed.
Lemma lem308391 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem308392 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term136 A lt2 P x) = (term131 A lt2 P x).
Proof. exact (MK_COMB (@lem308390 A lt2 x P) (@lem308391 A P x)). Qed.
Lemma lem308393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem308394 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term142 A lt2 P x) = (term143 A lt2 P x).
Proof. exact (MK_COMB (@lem308393) (@lem308392 A lt2 P x)). Qed.
Lemma lem308395 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term138 A lt2 x P y) = (term119 A lt2 x P y).
Proof. exact (eq_refl (term138 A lt2 x P y)). Qed.
Lemma lem308396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem308397 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term144 A lt2 x P y) = (term145 A lt2 x P y).
Proof. exact (MK_COMB (@lem308396) (@lem308395 A lt2 x P y)). Qed.
Lemma lem308398 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem308399 {A : Type'} (lt2 : type1402 A) (y : A) (P : A -> Prop) (x : A) : (term146 A lt2 y P x) = (term147 A lt2 y P x).
Proof. exact (MK_COMB (@lem308397 A lt2 x P y) (@lem308398 A P x)). Qed.
Lemma lem308400 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term148 A lt2 P x) = (term149 A lt2 P x).
Proof. exact (fun_ext (fun y : A => @lem308399 A lt2 y P x)). Qed.
Lemma lem308401 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem308402 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term137 A lt2 P x) = (term150 A lt2 P x).
Proof. exact (MK_COMB (@lem308401 A) (@lem308400 A lt2 P x)). Qed.
Lemma lem308403 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : ((term136 A lt2 P x) = (term137 A lt2 P x)) = ((term131 A lt2 P x) = (term150 A lt2 P x)).
Proof. exact (MK_COMB (@lem308394 A lt2 P x) (@lem308402 A lt2 P x)). Qed.
Lemma lem308404 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term131 A lt2 P x) = (term150 A lt2 P x).
Proof. exact (EQ_MP (@lem308403 A lt2 P x) (@lem308384 A lt2 P x)). Qed.
Lemma lem308405 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term132 A lt2 P) = (term151 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem308404 A lt2 P x)). Qed.
Lemma lem308406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308407 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term133 A lt2 P) = (term152 A lt2 P).
Proof. exact (MK_COMB (@lem308406 A) (@lem308405 A lt2 P)). Qed.
Lemma lem308409 {A B : Type'} (P : type1413 A B) : (term153 A B P) = (term154 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem308410 {A : Type'} (P : type1402 A) : (term155 A P) = (term156 A P).
Proof. exact (@lem308409 A A P). Qed.
Lemma lem308411 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term157 A lt2 P) = (term158 A lt2 P).
Proof. exact (@lem308410 A (term159 A lt2 P)). Qed.
Lemma lem308412 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term160 A lt2 P x) = (term149 A lt2 P x).
Proof. exact (eq_refl (term160 A lt2 P x)). Qed.
Lemma lem308413 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem308414 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) (y : A) : (term161 A lt2 P x y) = (term162 A lt2 P x y).
Proof. exact (MK_COMB (@lem308412 A lt2 P x) (@lem308413 A y)). Qed.
Lemma lem308415 {A : Type'} (lt2 : type1402 A) (y : A) (P : A -> Prop) (x : A) : (term162 A lt2 P x y) = (term147 A lt2 y P x).
Proof. exact (eq_refl (term162 A lt2 P x y)). Qed.
Lemma lem308416 {A : Type'} (lt2 : type1402 A) (y : A) (P : A -> Prop) (x : A) : (term161 A lt2 P x y) = (term147 A lt2 y P x).
Proof. exact (TRANS (@lem308414 A lt2 P x y) (@lem308415 A lt2 y P x)). Qed.
Lemma lem308417 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term163 A lt2 P x) = (term149 A lt2 P x).
Proof. exact (fun_ext (fun y : A => @lem308416 A lt2 y P x)). Qed.
Lemma lem308418 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem308419 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term164 A lt2 P x) = (term150 A lt2 P x).
Proof. exact (MK_COMB (@lem308418 A) (@lem308417 A lt2 P x)). Qed.
Lemma lem308420 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term165 A lt2 P) = (term151 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem308419 A lt2 P x)). Qed.
Lemma lem308421 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308422 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term157 A lt2 P) = (term152 A lt2 P).
Proof. exact (MK_COMB (@lem308421 A) (@lem308420 A lt2 P)). Qed.
Lemma lem308423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem308424 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term166 A lt2 P) = (term167 A lt2 P).
Proof. exact (MK_COMB (@lem308423) (@lem308422 A lt2 P)). Qed.
Lemma lem308425 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term160 A lt2 P x) = (term149 A lt2 P x).
Proof. exact (eq_refl (term160 A lt2 P x)). Qed.
Lemma lem308426 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem308427 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term168 A lt2 P y x) = (term169 A lt2 P y x).
Proof. exact (MK_COMB (@lem308425 A lt2 P x) (@lem308426 A y x)). Qed.
Lemma lem308428 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x : A) : (term169 A lt2 P y x) = (term170 A lt2 y P x).
Proof. exact (eq_refl (term169 A lt2 P y x)). Qed.
Lemma lem308429 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x : A) : (term168 A lt2 P y x) = (term170 A lt2 y P x).
Proof. exact (TRANS (@lem308427 A lt2 P y x) (@lem308428 A lt2 y P x)). Qed.
Lemma lem308430 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term171 A lt2 P y) = (term172 A lt2 y P).
Proof. exact (fun_ext (fun x : A => @lem308429 A lt2 y P x)). Qed.
Lemma lem308431 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308432 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term173 A lt2 P y) = (term174 A lt2 y P).
Proof. exact (MK_COMB (@lem308431 A) (@lem308430 A lt2 y P)). Qed.
Lemma lem308433 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term175 A lt2 P) = (term176 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem308432 A lt2 y P)). Qed.
Lemma lem308434 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem308435 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term158 A lt2 P) = (term177 A lt2 P).
Proof. exact (MK_COMB (@lem308434 A) (@lem308433 A lt2 P)). Qed.
Lemma lem308436 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term157 A lt2 P) = (term158 A lt2 P)) = ((term152 A lt2 P) = (term177 A lt2 P)).
Proof. exact (MK_COMB (@lem308424 A lt2 P) (@lem308435 A lt2 P)). Qed.
Lemma lem308437 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term152 A lt2 P) = (term177 A lt2 P).
Proof. exact (EQ_MP (@lem308436 A lt2 P) (@lem308411 A lt2 P)). Qed.
Lemma lem308439 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term133 A lt2 P) = (term177 A lt2 P).
Proof. exact (TRANS (@lem308407 A lt2 P) (@lem308437 A lt2 P)). Qed.
Lemma lem308440 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term87 A lt2 P) = (term177 A lt2 P).
Proof. exact (TRANS (@lem308299 A lt2 P) (@lem308439 A lt2 P)). Qed.
Lemma lem308441 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term87 A lt2 P) : term177 A lt2 P.
Proof. exact (EQ_MP (@lem308440 A lt2 P) (@lem308125 A lt2 P h1)). Qed.
Lemma lem308447 {A : Type'} (P : A -> Prop) (x : A) (h1 : term11 A P x) : term11 A P x.
Proof. exact (h1). Qed.
Lemma lem308448 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term174 A lt2 y P.
Proof. exact (h1). Qed.
Lemma lem308449 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term114 A lt2 x' P) : term114 A lt2 x' P.
Proof. exact (h1). Qed.
Lemma lem308455 {A : Type'} (P : A -> Prop) (x : A) (h1 : term11 A P x) : term11 A P x.
Proof. exact (h1). Qed.
Lemma lem308478 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x : A) : (term170 A lt2 y P x) = (term170 A lt2 y P x).
Proof. exact (eq_refl (term170 A lt2 y P x)). Qed.
Lemma lem308479 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term172 A lt2 y P) = (term172 A lt2 y P).
Proof. exact (fun_ext (fun x : A => @lem308478 A lt2 y P x)). Qed.
Lemma lem308480 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308481 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term174 A lt2 y P) = (term174 A lt2 y P).
Proof. exact (MK_COMB (@lem308480 A) (@lem308479 A lt2 y P)). Qed.
Lemma lem308482 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term174 A lt2 y P.
Proof. exact (EQ_MP (@lem308481 A lt2 y P) (@lem308448 A lt2 y P h1)). Qed.
Lemma lem308495 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (y : A) : (term94 A lt2 x' P y) = (term94 A lt2 x' P y).
Proof. exact (eq_refl (term94 A lt2 x' P y)). Qed.
Lemma lem308496 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term95 A lt2 x' P) = (term95 A lt2 x' P).
Proof. exact (fun_ext (fun y : A => @lem308495 A lt2 x' P y)). Qed.
Lemma lem308497 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308498 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term96 A lt2 x' P) = (term96 A lt2 x' P).
Proof. exact (MK_COMB (@lem308497 A) (@lem308496 A lt2 x' P)). Qed.
Lemma lem308505 {A : Type'} (P : A -> Prop) (x' : A) : (term20 A P x') = (term20 A P x').
Proof. exact (eq_refl (term20 A P x')). Qed.
Lemma lem308506 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term97 A lt2 x' P) = (term97 A lt2 x' P).
Proof. exact (MK_COMB (@lem308505 A P x') (@lem308498 A lt2 x' P)). Qed.
Lemma lem308509 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem308510 {A : Type'} (P : A -> Prop) : (term82 A P) = (term82 A P).
Proof. exact (fun_ext (fun x : A => @lem308509 A P x)). Qed.
Lemma lem308511 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308512 {A : Type'} (P : A -> Prop) : (term83 A P) = (term83 A P).
Proof. exact (MK_COMB (@lem308511 A) (@lem308510 A P)). Qed.
Lemma lem308513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem308514 {A : Type'} (P : A -> Prop) : (term101 A P) = (term101 A P).
Proof. exact (MK_COMB (@lem308513) (@lem308512 A P)). Qed.
Lemma lem308515 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term114 A lt2 x' P) = (term114 A lt2 x' P).
Proof. exact (MK_COMB (@lem308514 A P) (@lem308506 A lt2 x' P)). Qed.
Lemma lem308516 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term114 A lt2 x' P) : term114 A lt2 x' P.
Proof. exact (EQ_MP (@lem308515 A lt2 x' P) (@lem308449 A lt2 x' P h1)). Qed.
Lemma lem308517 {A : Type'} (P : A -> Prop) (h1 : term83 A P) : term83 A P.
Proof. exact (h1). Qed.
Lemma lem308518 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term97 A lt2 x' P.
Proof. exact (h1). Qed.
Lemma lem308519 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term96 A lt2 x' P.
Proof. exact (proj2 (@lem308518 A lt2 x' P h1)). Qed.
Lemma lem308524 {A : Type'} (P : A -> Prop) (x : A) (h1 : term11 A P x) : term11 A P x.
Proof. exact (h1). Qed.
Lemma lem308549 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem308550 {A : Type'} (P : A -> Prop) : (term82 A P) = (term82 A P).
Proof. exact (fun_ext (fun x : A => @lem308549 A P x)). Qed.
Lemma lem308551 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308553 {A : Type'} (P : A -> Prop) : (term83 A P) = (term83 A P).
Proof. exact (MK_COMB (@lem308551 A) (@lem308550 A P)). Qed.
Lemma lem308554 {A : Type'} (P : A -> Prop) (h1 : term83 A P) : term83 A P.
Proof. exact (EQ_MP (@lem308553 A P) (@lem308517 A P h1)). Qed.
Lemma lem308576 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x : A) : (term170 A lt2 y P x) = (term178 A lt2 y P x).
Proof. exact (@lem19699 (term179 A lt2 y x) (term180 A P y x) (P x)). Qed.
Lemma lem308577 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term172 A lt2 y P) = (term181 A lt2 y P).
Proof. exact (fun_ext (fun x : A => @lem308576 A lt2 y P x)). Qed.
Lemma lem308578 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308580 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) : (term174 A lt2 y P) = (term182 A lt2 y P).
Proof. exact (MK_COMB (@lem308578 A) (@lem308577 A lt2 y P)). Qed.
Lemma lem308581 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term182 A lt2 y P.
Proof. exact (EQ_MP (@lem308580 A lt2 y P) (@lem308482 A lt2 y P h1)). Qed.
Lemma lem308593 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (y : A) : (term94 A lt2 x' P y) = (term94 A lt2 x' P y).
Proof. exact (eq_refl (term94 A lt2 x' P y)). Qed.
Lemma lem308594 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term95 A lt2 x' P) = (term95 A lt2 x' P).
Proof. exact (fun_ext (fun y : A => @lem308593 A lt2 x' P y)). Qed.
Lemma lem308595 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem308597 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term96 A lt2 x' P) = (term96 A lt2 x' P).
Proof. exact (MK_COMB (@lem308595 A) (@lem308594 A lt2 x' P)). Qed.
Lemma lem308598 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term96 A lt2 x' P.
Proof. exact (EQ_MP (@lem308597 A lt2 x' P) (@lem308519 A lt2 x' P h1)). Qed.
Lemma lem308602 {A : Type'} (_6790 : A) (P : A -> Prop) (h1 : term83 A P) : term8 A P _6790.
Proof. exact (@lem308554 A P h1 _6790). Qed.
Lemma lem308603 {A : Type'} (P : A -> Prop) (_6790 : A) : (term8 A P _6790) = (P _6790).
Proof. exact (eq_refl (term8 A P _6790)). Qed.
Lemma lem308605 {A : Type'} (_6791 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term183 A lt2 y P _6791.
Proof. exact (@lem308581 A lt2 y P h1 _6791). Qed.
Lemma lem308606 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6791 : A) : (term183 A lt2 y P _6791) = (term178 A lt2 y P _6791).
Proof. exact (eq_refl (term183 A lt2 y P _6791)). Qed.
Lemma lem308607 {A : Type'} (_6791 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term178 A lt2 y P _6791.
Proof. exact (EQ_MP (@lem308606 A lt2 y P _6791) (@lem308605 A _6791 lt2 y P h1)). Qed.
Lemma lem308608 {A : Type'} (_6792 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term184 A lt2 x' P _6792.
Proof. exact (@lem308598 A lt2 x' P h1 _6792). Qed.
Lemma lem308609 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6792 : A) : (term184 A lt2 x' P _6792) = (term94 A lt2 x' P _6792).
Proof. exact (eq_refl (term184 A lt2 x' P _6792)). Qed.
Lemma lem308616 {A : Type'} (P : A -> Prop) (x : A) (h1 : term11 A P x) : term11 A P x.
Proof. exact (h1). Qed.
Lemma lem308634 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term11 A P x'.
Proof. exact (proj1 (@lem308518 A lt2 x' P h1)). Qed.
Lemma lem308640 {A : Type'} (_6792 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term94 A lt2 x' P _6792.
Proof. exact (EQ_MP (@lem308609 A lt2 x' P _6792) (@lem308608 A _6792 lt2 x' P h1)). Qed.
Lemma lem308646 {A : Type'} (_6791 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term185 A lt2 y P _6791.
Proof. exact (proj1 (@lem308607 A _6791 lt2 y P h1)). Qed.
Lemma lem308652 {A : Type'} (_6791 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term186 A y P _6791.
Proof. exact (proj2 (@lem308607 A _6791 lt2 y P h1)). Qed.
Lemma lem308654 {A : Type'} (_6790 : A) (P : A -> Prop) (h1 : term83 A P) : P _6790.
Proof. exact (EQ_MP (@lem308603 A P _6790) (@lem308602 A _6790 P h1)). Qed.
Lemma lem308655 {A : Type'} (_6790 : A) (P : A -> Prop) (h1 : term83 A P) : P _6790.
Proof. exact (@lem308654 A _6790 P h1). Qed.
Lemma lem308656 {A : Type'} (x : A) (P : A -> Prop) (h1 : term83 A P) : P x.
Proof. exact (@lem308655 A x P h1). Qed.
Lemma lem308657 {A : Type'} (x : A) (P : A -> Prop) (h1 : term83 A P) : term187 A P x.
Proof. exact (fun h0 : term11 A P x => @lem308656 A x P h1). Qed.
Lemma lem308659 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem308660 {A : Type'} (P : A -> Prop) (x : A) : (term187 A P x) = (P x).
Proof. exact (@lem308659 (P x)). Qed.
Lemma lem308661 {A : Type'} (x : A) (P : A -> Prop) (h1 : term83 A P) : P x.
Proof. exact (EQ_MP (@lem308660 A P x) (@lem308657 A x P h1)). Qed.
Lemma lem308664 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem308666 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term189 A P x).
Proof. exact (@lem308664 (P x)). Qed.
Lemma lem308669 {A : Type'} (P : A -> Prop) (x : A) (h1 : term11 A P x) : term189 A P x.
Proof. exact (EQ_MP (@lem308666 A P x) (@lem308616 A P x h1)). Qed.
Lemma lem308672 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : False.
Proof. exact (@lem308669 A P x h2 (@lem308661 A x P h1)). Qed.
Lemma lem308673 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : term190.
Proof. exact (fun h0 : ~ False => @lem308672 A P x h1 h2). Qed.
Lemma lem308675 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem308676 : term190 = False.
Proof. exact (@lem308675 False). Qed.
Lemma lem308677 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : False.
Proof. exact (EQ_MP (@lem308676) (@lem308673 A P x h1 h2)). Qed.
Lemma lem308680 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term11 A P x') : term11 A P x'.
Proof. exact (h1). Qed.
Lemma lem308681 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term11 A P x') : term191 A P x'.
Proof. exact (fun h0 : P x' => @lem308680 A P x' h1). Qed.
Lemma lem308683 (p : Prop) : (term192 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem308684 {A : Type'} (P : A -> Prop) (x' : A) : (term191 A P x') = (term11 A P x').
Proof. exact (@lem308683 (P x')). Qed.
Lemma lem308685 {A : Type'} (P : A -> Prop) (x' : A) (h1 : term11 A P x') : term11 A P x'.
Proof. exact (EQ_MP (@lem308684 A P x') (@lem308681 A P x' h1)). Qed.
Lemma lem308687 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem308690 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6791 : A) : (term185 A lt2 y P _6791) = (term194 A P lt2 y _6791).
Proof. exact (@lem308687 (P _6791) (term179 A lt2 y _6791)). Qed.
Lemma lem308693 {A : Type'} (_6791 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term194 A P lt2 y _6791.
Proof. exact (EQ_MP (@lem308690 A P lt2 y _6791) (@lem308646 A _6791 lt2 y P h1)). Qed.
Lemma lem308694 {A : Type'} (_6791 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term194 A P lt2 y _6791.
Proof. exact (@lem308693 A _6791 lt2 y P h1). Qed.
Lemma lem308695 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term194 A P lt2 y x'.
Proof. exact (@lem308694 A x' lt2 y P h1). Qed.
Lemma lem308698 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term174 A lt2 y P) (h2 : term11 A P x') : term179 A lt2 y x'.
Proof. exact (@lem308695 A x' lt2 y P h1 (@lem308685 A P x' h2)). Qed.
Lemma lem308699 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term174 A lt2 y P) (h2 : term11 A P x') : term195 A lt2 y x'.
Proof. exact (fun h0 : term196 A lt2 y x' => @lem308698 A lt2 y P x' h1 h2). Qed.
Lemma lem308701 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem308702 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x' : A) : (term195 A lt2 y x') = (term179 A lt2 y x').
Proof. exact (@lem308701 (term179 A lt2 y x')). Qed.
Lemma lem308703 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (x' : A) (h1 : term174 A lt2 y P) (h2 : term11 A P x') : term179 A lt2 y x'.
Proof. exact (EQ_MP (@lem308702 A lt2 y x') (@lem308699 A lt2 y P x' h1 h2)). Qed.
Lemma lem308709 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem308710 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6792 : A) (x' : A) : (term94 A lt2 x' P _6792) = (term197 A P lt2 _6792 x').
Proof. exact (@lem308709 (P _6792) (term198 A lt2 _6792 x')). Qed.
Lemma lem308716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem308717 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6792 : A) (x' : A) : (term199 A lt2 x' P _6792) = (term200 A P lt2 _6792 x').
Proof. exact (MK_COMB (@lem308716) (@lem308710 A P lt2 _6792 x')). Qed.
Lemma lem308723 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6792 : A) (x' : A) : (term197 A P lt2 _6792 x') = (term197 A P lt2 _6792 x').
Proof. exact (eq_refl (term197 A P lt2 _6792 x')). Qed.
Lemma lem308724 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6792 : A) (x' : A) : ((term94 A lt2 x' P _6792) = (term197 A P lt2 _6792 x')) = ((term197 A P lt2 _6792 x') = (term197 A P lt2 _6792 x')).
Proof. exact (MK_COMB (@lem308717 A P lt2 _6792 x') (@lem308723 A P lt2 _6792 x')). Qed.
Lemma lem308726 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem308727 (x : Prop) : (x = x) = True.
Proof. exact (@lem308726 Prop x). Qed.
Lemma lem308728 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6792 : A) (x' : A) : ((term197 A P lt2 _6792 x') = (term197 A P lt2 _6792 x')) = True.
Proof. exact (@lem308727 (term197 A P lt2 _6792 x')). Qed.
Lemma lem308729 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6792 : A) (x' : A) : ((term94 A lt2 x' P _6792) = (term197 A P lt2 _6792 x')) = True.
Proof. exact (TRANS (@lem308724 A P lt2 _6792 x') (@lem308728 A P lt2 _6792 x')). Qed.
Lemma lem308730 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6792 : A) (x' : A) : True = ((term94 A lt2 x' P _6792) = (term197 A P lt2 _6792 x')).
Proof. exact (SYM (@lem308729 A P lt2 _6792 x')). Qed.
Lemma lem308731 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6792 : A) (x' : A) : (term94 A lt2 x' P _6792) = (term197 A P lt2 _6792 x').
Proof. exact (EQ_MP (@lem308730 A P lt2 _6792 x') (@lem0)). Qed.
Lemma lem308732 {A : Type'} (_6792 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term197 A P lt2 _6792 x'.
Proof. exact (EQ_MP (@lem308731 A P lt2 _6792 x') (@lem308640 A _6792 lt2 x' P h1)). Qed.
Lemma lem308734 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem308735 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6792 : A) : (term197 A P lt2 _6792 x') = (term201 A lt2 x' P _6792).
Proof. exact (@lem308734 (term198 A lt2 _6792 x') (P _6792)). Qed.
Lemma lem308737 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem308738 {A : Type'} (lt2 : type1402 A) (_6792 : A) (x' : A) : (term202 A lt2 _6792 x') = (lt2 _6792 x').
Proof. exact (@lem308737 (lt2 _6792 x')). Qed.
Lemma lem308739 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem308740 {A : Type'} (lt2 : type1402 A) (_6792 : A) (x' : A) : (term203 A lt2 _6792 x') = (term24 A lt2 _6792 x').
Proof. exact (MK_COMB (@lem308739) (@lem308738 A lt2 _6792 x')). Qed.
Lemma lem308741 {A : Type'} (P : A -> Prop) (_6792 : A) : (P _6792) = (P _6792).
Proof. exact (eq_refl (P _6792)). Qed.
Lemma lem308742 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6792 : A) : (term201 A lt2 x' P _6792) = (term26 A lt2 x' P _6792).
Proof. exact (MK_COMB (@lem308740 A lt2 _6792 x') (@lem308741 A P _6792)). Qed.
Lemma lem308743 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6792 : A) : (term197 A P lt2 _6792 x') = (term26 A lt2 x' P _6792).
Proof. exact (TRANS (@lem308735 A lt2 x' P _6792) (@lem308742 A lt2 x' P _6792)). Qed.
Lemma lem308746 {A : Type'} (_6792 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term26 A lt2 x' P _6792.
Proof. exact (EQ_MP (@lem308743 A lt2 x' P _6792) (@lem308732 A _6792 lt2 x' P h1)). Qed.
Lemma lem308747 {A : Type'} (_6792 : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term26 A lt2 x' P _6792.
Proof. exact (@lem308746 A _6792 lt2 x' P h1). Qed.
Lemma lem308748 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term204 A lt2 P y x'.
Proof. exact (@lem308747 A (y x') lt2 x' P h1). Qed.
Lemma lem308751 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x') (h3 : term97 A lt2 x' P) : term205 A P y x'.
Proof. exact (@lem308748 A y lt2 x' P h3 (@lem308703 A lt2 y P x' h1 h2)). Qed.
Lemma lem308752 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x') (h3 : term97 A lt2 x' P) : term206 A P y x'.
Proof. exact (fun h0 : term180 A P y x' => @lem308751 A y lt2 x' P h1 h2 h3). Qed.
Lemma lem308754 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem308755 {A : Type'} (P : A -> Prop) (y : A -> A) (x' : A) : (term206 A P y x') = (term205 A P y x').
Proof. exact (@lem308754 (term205 A P y x')). Qed.
Lemma lem308756 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x') (h3 : term97 A lt2 x' P) : term205 A P y x'.
Proof. exact (EQ_MP (@lem308755 A P y x') (@lem308752 A y lt2 x' P h1 h2 h3)). Qed.
Lemma lem308762 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem308763 {A : Type'} (P : A -> Prop) (y : A -> A) (_6791 : A) : (term186 A y P _6791) = (term207 A P y _6791).
Proof. exact (@lem308762 (P _6791) (term180 A P y _6791)). Qed.
Lemma lem308769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem308770 {A : Type'} (P : A -> Prop) (y : A -> A) (_6791 : A) : (term208 A y P _6791) = (term209 A P y _6791).
Proof. exact (MK_COMB (@lem308769) (@lem308763 A P y _6791)). Qed.
Lemma lem308776 {A : Type'} (P : A -> Prop) (y : A -> A) (_6791 : A) : (term207 A P y _6791) = (term207 A P y _6791).
Proof. exact (eq_refl (term207 A P y _6791)). Qed.
Lemma lem308777 {A : Type'} (P : A -> Prop) (y : A -> A) (_6791 : A) : ((term186 A y P _6791) = (term207 A P y _6791)) = ((term207 A P y _6791) = (term207 A P y _6791)).
Proof. exact (MK_COMB (@lem308770 A P y _6791) (@lem308776 A P y _6791)). Qed.
Lemma lem308779 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem308780 (x : Prop) : (x = x) = True.
Proof. exact (@lem308779 Prop x). Qed.
Lemma lem308781 {A : Type'} (P : A -> Prop) (y : A -> A) (_6791 : A) : ((term207 A P y _6791) = (term207 A P y _6791)) = True.
Proof. exact (@lem308780 (term207 A P y _6791)). Qed.
Lemma lem308782 {A : Type'} (P : A -> Prop) (y : A -> A) (_6791 : A) : ((term186 A y P _6791) = (term207 A P y _6791)) = True.
Proof. exact (TRANS (@lem308777 A P y _6791) (@lem308781 A P y _6791)). Qed.
Lemma lem308783 {A : Type'} (P : A -> Prop) (y : A -> A) (_6791 : A) : True = ((term186 A y P _6791) = (term207 A P y _6791)).
Proof. exact (SYM (@lem308782 A P y _6791)). Qed.
Lemma lem308784 {A : Type'} (P : A -> Prop) (y : A -> A) (_6791 : A) : (term186 A y P _6791) = (term207 A P y _6791).
Proof. exact (EQ_MP (@lem308783 A P y _6791) (@lem0)). Qed.
Lemma lem308785 {A : Type'} (_6791 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term207 A P y _6791.
Proof. exact (EQ_MP (@lem308784 A P y _6791) (@lem308652 A _6791 lt2 y P h1)). Qed.
Lemma lem308787 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem308788 {A : Type'} (y : A -> A) (P : A -> Prop) (_6791 : A) : (term207 A P y _6791) = (term210 A y P _6791).
Proof. exact (@lem308787 (term180 A P y _6791) (P _6791)). Qed.
Lemma lem308790 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem308791 {A : Type'} (P : A -> Prop) (y : A -> A) (_6791 : A) : (term211 A P y _6791) = (term205 A P y _6791).
Proof. exact (@lem308790 (term205 A P y _6791)). Qed.
Lemma lem308792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem308793 {A : Type'} (P : A -> Prop) (y : A -> A) (_6791 : A) : (term212 A P y _6791) = (term213 A P y _6791).
Proof. exact (MK_COMB (@lem308792) (@lem308791 A P y _6791)). Qed.
Lemma lem308794 {A : Type'} (P : A -> Prop) (_6791 : A) : (P _6791) = (P _6791).
Proof. exact (eq_refl (P _6791)). Qed.
Lemma lem308795 {A : Type'} (y : A -> A) (P : A -> Prop) (_6791 : A) : (term210 A y P _6791) = (term214 A y P _6791).
Proof. exact (MK_COMB (@lem308793 A P y _6791) (@lem308794 A P _6791)). Qed.
Lemma lem308796 {A : Type'} (y : A -> A) (P : A -> Prop) (_6791 : A) : (term207 A P y _6791) = (term214 A y P _6791).
Proof. exact (TRANS (@lem308788 A y P _6791) (@lem308795 A y P _6791)). Qed.
Lemma lem308799 {A : Type'} (_6791 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term214 A y P _6791.
Proof. exact (EQ_MP (@lem308796 A y P _6791) (@lem308785 A _6791 lt2 y P h1)). Qed.
Lemma lem308800 {A : Type'} (_6791 : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term214 A y P _6791.
Proof. exact (@lem308799 A _6791 lt2 y P h1). Qed.
Lemma lem308801 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (h1 : term174 A lt2 y P) : term214 A y P x'.
Proof. exact (@lem308800 A x' lt2 y P h1). Qed.
Lemma lem308804 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x') (h3 : term97 A lt2 x' P) : P x'.
Proof. exact (@lem308801 A x' lt2 y P h1 (@lem308756 A y lt2 x' P h1 h2 h3)). Qed.
Lemma lem308805 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term97 A lt2 x' P) : term187 A P x'.
Proof. exact (fun h0 : term11 A P x' => @lem308804 A y lt2 x' P h1 h0 h2). Qed.
Lemma lem308807 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem308808 {A : Type'} (P : A -> Prop) (x' : A) : (term187 A P x') = (P x').
Proof. exact (@lem308807 (P x')). Qed.
Lemma lem308809 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term97 A lt2 x' P) : P x'.
Proof. exact (EQ_MP (@lem308808 A P x') (@lem308805 A y lt2 x' P h1 h2)). Qed.
Lemma lem308812 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem308814 {A : Type'} (P : A -> Prop) (x' : A) : (term11 A P x') = (term189 A P x').
Proof. exact (@lem308812 (P x')). Qed.
Lemma lem308817 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term97 A lt2 x' P) : term189 A P x'.
Proof. exact (EQ_MP (@lem308814 A P x') (@lem308634 A lt2 x' P h1)). Qed.
Lemma lem308820 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term97 A lt2 x' P) : False.
Proof. exact (@lem308817 A lt2 x' P h2 (@lem308809 A y lt2 x' P h1 h2)). Qed.
Lemma lem308821 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term97 A lt2 x' P) : term190.
Proof. exact (fun h0 : ~ False => @lem308820 A y lt2 x' P h1 h2). Qed.
Lemma lem308823 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem308824 : term190 = False.
Proof. exact (@lem308823 False). Qed.
Lemma lem308825 {A : Type'} (y : A -> A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term97 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem308824) (@lem308821 A y lt2 x' P h1 h2)). Qed.
Lemma lem308826 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : (term11 A P x) = False.
Proof. exact (prop_ext (fun h3 : term11 A P x => @lem308677 A P x h1 h2) (fun h3 : False => @lem308616 A P x h2)). Qed.
Lemma lem308827 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : False.
Proof. exact (EQ_MP (@lem308826 A P x h1 h2) (@lem308616 A P x h2)). Qed.
Lemma lem308828 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : (term11 A P x) = False.
Proof. exact (prop_ext (fun h3 : term11 A P x => @lem308827 A P x h1 h2) (fun h3 : False => @lem308524 A P x h2)). Qed.
Lemma lem308829 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : False.
Proof. exact (EQ_MP (@lem308828 A P x h1 h2) (@lem308524 A P x h2)). Qed.
Lemma lem308830 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : (term83 A P) = False.
Proof. exact (prop_ext (fun h3 : term83 A P => @lem308829 A P x h1 h2) (fun h3 : False => @lem308554 A P h1)). Qed.
Lemma lem308831 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : False.
Proof. exact (EQ_MP (@lem308830 A P x h1 h2) (@lem308554 A P h1)). Qed.
Lemma lem308832 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : (term11 A P x) = False.
Proof. exact (prop_ext (fun h3 : term11 A P x => @lem308831 A P x h1 h2) (fun h3 : False => @lem308524 A P x h2)). Qed.
Lemma lem308833 {A : Type'} (P : A -> Prop) (x : A) (h1 : term83 A P) (h2 : term11 A P x) : False.
Proof. exact (EQ_MP (@lem308832 A P x h1 h2) (@lem308524 A P x h2)). Qed.
Lemma lem308834 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x) (h3 : term114 A lt2 x' P) : False.
Proof. exact (or_elim (@lem308516 A lt2 x' P h3) (fun h0 : term83 A P => @lem308833 A P x h0 h2) (fun h0 : term97 A lt2 x' P => @lem308825 A y lt2 x' P h1 h0)). Qed.
Lemma lem308835 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x) (h3 : term114 A lt2 x' P) : (term114 A lt2 x' P) = False.
Proof. exact (prop_ext (fun h4 : term114 A lt2 x' P => @lem308834 A y x lt2 x' P h1 h2 h3) (fun h4 : False => @lem308516 A lt2 x' P h3)). Qed.
Lemma lem308836 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x) (h3 : term114 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem308835 A y x lt2 x' P h1 h2 h3) (@lem308516 A lt2 x' P h3)). Qed.
Lemma lem308837 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x) (h3 : term114 A lt2 x' P) : (term174 A lt2 y P) = False.
Proof. exact (prop_ext (fun h4 : term174 A lt2 y P => @lem308836 A y x lt2 x' P h1 h2 h3) (fun h4 : False => @lem308482 A lt2 y P h1)). Qed.
Lemma lem308838 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x) (h3 : term114 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem308837 A y x lt2 x' P h1 h2 h3) (@lem308482 A lt2 y P h1)). Qed.
Lemma lem308839 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x) (h3 : term114 A lt2 x' P) : (term11 A P x) = False.
Proof. exact (prop_ext (fun h4 : term11 A P x => @lem308838 A y x lt2 x' P h1 h2 h3) (fun h4 : False => @lem308455 A P x h2)). Qed.
Lemma lem308840 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x) (h3 : term114 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem308839 A y x lt2 x' P h1 h2 h3) (@lem308455 A P x h2)). Qed.
Lemma lem308841 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term174 A lt2 y P) (h2 : term11 A P x) (h3 : term37 A lt2 P) : False.
Proof. exact (ex_elim (@lem308273 A lt2 P h3) (fun x' : A => fun h0 : term116 A lt2 P x' => @lem308840 A y x lt2 x' P h1 h2 h0)). Qed.
Lemma lem308842 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term87 A lt2 P) (h2 : term11 A P x) (h3 : term37 A lt2 P) : False.
Proof. exact (ex_elim (@lem308441 A lt2 P h1) (fun y : A -> A => fun h0 : term176 A lt2 P y => @lem308841 A y x lt2 P h0 h2 h3)). Qed.
Lemma lem308843 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term87 A lt2 P) (h2 : term11 A P x) (h3 : term37 A lt2 P) : (term11 A P x) = False.
Proof. exact (prop_ext (fun h4 : term11 A P x => @lem308842 A x lt2 P h1 h2 h3) (fun h4 : False => @lem308447 A P x h2)). Qed.
Lemma lem308844 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term87 A lt2 P) (h2 : term11 A P x) (h3 : term37 A lt2 P) : False.
Proof. exact (EQ_MP (@lem308843 A x lt2 P h1 h2 h3) (@lem308447 A P x h2)). Qed.
Lemma lem308845 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term87 A lt2 P) (h2 : term11 A P x) (h3 : term37 A lt2 P) : (term11 A P x) = False.
Proof. exact (prop_ext (fun h4 : term11 A P x => @lem308844 A x lt2 P h1 h2 h3) (fun h4 : False => @lem308130 A P x h2)). Qed.
Lemma lem308846 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term87 A lt2 P) (h2 : term11 A P x) (h3 : term37 A lt2 P) : False.
Proof. exact (EQ_MP (@lem308845 A x lt2 P h1 h2 h3) (@lem308130 A P x h2)). Qed.
Lemma lem308847 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term87 A lt2 P) (h2 : term37 A lt2 P) : term89 A P x.
Proof. exact (fun h0 : term11 A P x => @lem308846 A x lt2 P h1 h0 h2). Qed.
Lemma lem308848 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term87 A lt2 P) (h2 : term37 A lt2 P) : P x.
Proof. exact (EQ_MP (@lem308129 A P x) (@lem308847 A x lt2 P h1 h2)). Qed.
Lemma lem308853 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term87 A lt2 P) (h2 : term37 A lt2 P) : term83 A P.
Proof. exact (fun x : A => @lem308848 A x lt2 P h1 h2). Qed.
Lemma lem308854 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term37 A lt2 P) : term40 A lt2 P.
Proof. exact (fun h0 : term87 A lt2 P => @lem308853 A lt2 P h0 h1). Qed.
Lemma lem308855 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term42 A lt2 P.
Proof. exact (fun h0 : term37 A lt2 P => @lem308854 A lt2 P h0). Qed.
Lemma lem308860 {A : Type'} (P : A -> Prop) : term77 A P.
Proof. exact (fun lt2 : type1402 A => @lem308855 A lt2 P). Qed.
Lemma lem308865 {A : Type'} : term81 A.
Proof. exact (fun P : A -> Prop => @lem308860 A P). Qed.
Lemma lem308866 {A : Type'} : term80 A.
Proof. exact (EQ_MP (@lem308123 A) (@lem308865 A)). Qed.
Lemma lem308867 {A : Type'} (P : A -> Prop) : term215 A P.
Proof. exact (@lem308866 A P). Qed.
Lemma lem308868 {A : Type'} (P : A -> Prop) : (term215 A P) = (term76 A P).
Proof. exact (eq_refl (term215 A P)). Qed.
Lemma lem308869 {A : Type'} (P : A -> Prop) : term76 A P.
Proof. exact (EQ_MP (@lem308868 A P) (@lem308867 A P)). Qed.
Lemma lem308870 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term216 A P lt2.
Proof. exact (@lem308869 A P lt2). Qed.
Lemma lem308871 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term216 A P lt2) = (term68 A lt2 P).
Proof. exact (eq_refl (term216 A P lt2)). Qed.
Lemma lem308872 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term68 A lt2 P.
Proof. exact (EQ_MP (@lem308871 A lt2 P) (@lem308870 A P lt2)). Qed.
Lemma lem308874 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term68 A lt2 P.
Proof. exact (@lem307885 A lt2 P (@lem308872 A lt2 P)). Qed.
Lemma lem308875 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term69 A lt2 P) : False.
Proof. exact (@lem308874 A lt2 P (@lem307869 A lt2 P h1)). Qed.
Lemma lem308876 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term69 A lt2 P) : (term69 A lt2 P) = False.
Proof. exact (prop_ext (fun h2 : term69 A lt2 P => @lem308875 A lt2 P h1) (fun h2 : False => @lem307869 A lt2 P h1)). Qed.
Lemma lem308877 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term69 A lt2 P) : False.
Proof. exact (EQ_MP (@lem308876 A lt2 P h1) (@lem307869 A lt2 P h1)). Qed.
Lemma lem308878 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term68 A lt2 P.
Proof. exact (fun h0 : term69 A lt2 P => @lem308877 A lt2 P h0). Qed.
Lemma lem308879 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term42 A lt2 P.
Proof. exact (EQ_MP (@lem307868 A lt2 P) (@lem308878 A lt2 P)). Qed.
Lemma lem308881 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem308882 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term66 A lt2 P) = (term217 A lt2 P).
Proof. exact (@lem308881 (term66 A lt2 P)). Qed.
Lemma lem308883 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term217 A lt2 P) = (term66 A lt2 P).
Proof. exact (SYM (@lem308882 A lt2 P)). Qed.
Lemma lem308884 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term218 A lt2 P) : term218 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem308887 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term217 A lt2 P) : term217 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem308888 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term219 A lt2 P.
Proof. exact (fun h0 : term217 A lt2 P => @lem308887 A lt2 P h0). Qed.
Lemma lem308889 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term219 A lt2 P) : term219 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem308890 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term217 A lt2 P) : term217 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem308891 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term217 A lt2 P) (h2 : term219 A lt2 P) : term217 A lt2 P.
Proof. exact (@lem308889 A lt2 P h2 (@lem308890 A lt2 P h1)). Qed.
Lemma lem308892 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term217 A lt2 P) : term220 A lt2 P.
Proof. exact (fun h0 : term219 A lt2 P => @lem308891 A lt2 P h1 h0). Qed.
Lemma lem308893 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term219 A lt2 P) : term219 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem308894 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term217 A lt2 P) (h2 : term219 A lt2 P) : term217 A lt2 P.
Proof. exact (@lem308892 A lt2 P h1 (@lem308893 A lt2 P h2)). Qed.
Lemma lem308895 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term219 A lt2 P) : term219 A lt2 P.
Proof. exact (fun h0 : term217 A lt2 P => @lem308894 A lt2 P h0 h1). Qed.
Lemma lem308896 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term221 A lt2 P.
Proof. exact (fun h0 : term219 A lt2 P => @lem308895 A lt2 P h0). Qed.
Lemma lem308899 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term219 A lt2 P.
Proof. exact (@lem308896 A lt2 P (@lem308888 A lt2 P)). Qed.
Lemma lem308900 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term219 A lt2 P.
Proof. exact (@lem308899 A lt2 P). Qed.
Lemma lem308910 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem308911 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term217 A lt2 P) = (term222 A lt2 P).
Proof. exact (@lem308910 (term218 A lt2 P)). Qed.
Lemma lem308913 (t : Prop) : (term23 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem308914 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term222 A lt2 P) = (term66 A lt2 P).
Proof. exact (@lem308913 (term66 A lt2 P)). Qed.
Lemma lem308917 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term217 A lt2 P) = (term66 A lt2 P).
Proof. exact (TRANS (@lem308911 A lt2 P) (@lem308914 A lt2 P)). Qed.
Lemma lem308978 {A : Type'} (P : A -> Prop) : (term223 A P) = (term224 A P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem308917 A lt2 P)). Qed.
Lemma lem308979 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem308980 {A : Type'} (P : A -> Prop) : (term225 A P) = (term226 A P).
Proof. exact (MK_COMB (@lem308979 A) (@lem308978 A P)). Qed.
Lemma lem308985 {A : Type'} : (term227 A) = (term228 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem308980 A P)). Qed.
Lemma lem308986 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem308995 {A : Type'} : (term229 A) = (term230 A).
Proof. exact (MK_COMB (@lem308986 A) (@lem308985 A)). Qed.
Lemma lem309002 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term44 A lt2 x P y) = (term44 A lt2 x P y).
Proof. exact (eq_refl (term44 A lt2 x P y)). Qed.
Lemma lem309003 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term46 A lt2 x P) = (term46 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem309002 A lt2 x P y)). Qed.
Lemma lem309004 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309005 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term48 A lt2 x P) = (term48 A lt2 x P).
Proof. exact (MK_COMB (@lem309004 A) (@lem309003 A lt2 x P)). Qed.
Lemma lem309008 {A : Type'} (P : A -> Prop) (x : A) : (term231 A P x) = (term231 A P x).
Proof. exact (eq_refl (term231 A P x)). Qed.
Lemma lem309009 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term232 A lt2 x P) = (term232 A lt2 x P).
Proof. exact (MK_COMB (@lem309008 A P x) (@lem309005 A lt2 x P)). Qed.
Lemma lem309010 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term233 A lt2 P) = (term233 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem309009 A lt2 x P)). Qed.
Lemma lem309011 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem309012 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term234 A lt2 P) = (term234 A lt2 P).
Proof. exact (MK_COMB (@lem309011 A) (@lem309010 A lt2 P)). Qed.
Lemma lem309013 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem309014 {A : Type'} (P : A -> Prop) : (term82 A P) = (term82 A P).
Proof. exact (fun_ext (fun x : A => @lem309013 A P x)). Qed.
Lemma lem309015 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem309016 {A : Type'} (P : A -> Prop) : (term235 A P) = (term235 A P).
Proof. exact (MK_COMB (@lem309015 A) (@lem309014 A P)). Qed.
Lemma lem309017 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem309018 {A : Type'} (P : A -> Prop) : (term236 A P) = (term236 A P).
Proof. exact (MK_COMB (@lem309017) (@lem309016 A P)). Qed.
Lemma lem309019 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term64 A lt2 P) = (term64 A lt2 P).
Proof. exact (MK_COMB (@lem309018 A P) (@lem309012 A lt2 P)). Qed.
Lemma lem309022 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term11 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem309023 {A : Type'} (P : A -> Prop) : (term3 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem309022 A P x)). Qed.
Lemma lem309024 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309025 {A : Type'} (P : A -> Prop) : (term60 A P) = (term60 A P).
Proof. exact (MK_COMB (@lem309024 A) (@lem309023 A P)). Qed.
Lemma lem309028 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term11 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem309035 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term44 A lt2 x P y) = (term44 A lt2 x P y).
Proof. exact (eq_refl (term44 A lt2 x P y)). Qed.
Lemma lem309036 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term46 A lt2 x P) = (term46 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem309035 A lt2 x P y)). Qed.
Lemma lem309037 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309038 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term48 A lt2 x P) = (term48 A lt2 x P).
Proof. exact (MK_COMB (@lem309037 A) (@lem309036 A lt2 x P)). Qed.
Lemma lem309039 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem309040 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term50 A lt2 x P) = (term50 A lt2 x P).
Proof. exact (MK_COMB (@lem309039) (@lem309038 A lt2 x P)). Qed.
Lemma lem309041 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term52 A lt2 P x) = (term52 A lt2 P x).
Proof. exact (MK_COMB (@lem309040 A lt2 x P) (@lem309028 A P x)). Qed.
Lemma lem309042 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term54 A lt2 P) = (term54 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem309041 A lt2 P x)). Qed.
Lemma lem309043 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309044 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term56 A lt2 P) = (term56 A lt2 P).
Proof. exact (MK_COMB (@lem309043 A) (@lem309042 A lt2 P)). Qed.
Lemma lem309045 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem309046 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term58 A lt2 P) = (term58 A lt2 P).
Proof. exact (MK_COMB (@lem309045) (@lem309044 A lt2 P)). Qed.
Lemma lem309047 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term61 A lt2 P) = (term61 A lt2 P).
Proof. exact (MK_COMB (@lem309046 A lt2 P) (@lem309025 A P)). Qed.
Lemma lem309048 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem309049 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term63 A lt2 P) = (term63 A lt2 P).
Proof. exact (MK_COMB (@lem309048) (@lem309047 A lt2 P)). Qed.
Lemma lem309050 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term66 A lt2 P) = (term66 A lt2 P).
Proof. exact (MK_COMB (@lem309049 A lt2 P) (@lem309019 A lt2 P)). Qed.
Lemma lem309051 {A : Type'} (P : A -> Prop) : (term224 A P) = (term224 A P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem309050 A lt2 P)). Qed.
Lemma lem309052 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem309053 {A : Type'} (P : A -> Prop) : (term226 A P) = (term226 A P).
Proof. exact (MK_COMB (@lem309052 A) (@lem309051 A P)). Qed.
Lemma lem309054 {A : Type'} : (term228 A) = (term228 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem309053 A P)). Qed.
Lemma lem309055 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem309056 {A : Type'} : (term230 A) = (term230 A).
Proof. exact (MK_COMB (@lem309055 A) (@lem309054 A)). Qed.
Lemma lem309121 {A : Type'} : (term229 A) = (term230 A).
Proof. exact (TRANS (@lem308995 A) (@lem309056 A)). Qed.
Lemma lem309122 {A : Type'} : (term230 A) = (term229 A).
Proof. exact (SYM (@lem309121 A)). Qed.
Lemma lem309123 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term61 A lt2 P) : term61 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem309124 {A : Type'} (P : A -> Prop) (h1 : term235 A P) : term235 A P.
Proof. exact (h1). Qed.
Lemma lem309126 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem309127 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term234 A lt2 P) = (term237 A lt2 P).
Proof. exact (@lem309126 (term234 A lt2 P)). Qed.
Lemma lem309128 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term237 A lt2 P) = (term234 A lt2 P).
Proof. exact (SYM (@lem309127 A lt2 P)). Qed.
Lemma lem309129 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term238 A lt2 P) : term238 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem309136 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term44 A lt2 x P y) = (term239 A lt2 x P y).
Proof. exact (@lem17265 (lt2 y x) (term11 A P y)). Qed.
Lemma lem309137 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term46 A lt2 x P) = (term240 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem309136 A lt2 x P y)). Qed.
Lemma lem309138 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309139 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term48 A lt2 x P) = (term241 A lt2 x P).
Proof. exact (MK_COMB (@lem309138 A) (@lem309137 A lt2 x P)). Qed.
Lemma lem309142 {A : Type'} (P : A -> Prop) (x : A) : (term22 A P x) = (P x).
Proof. exact (@lem16933 (P x)). Qed.
Lemma lem309143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem309144 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term242 A lt2 x P) = (term243 A lt2 x P).
Proof. exact (MK_COMB (@lem309143) (@lem309139 A lt2 x P)). Qed.
Lemma lem309145 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term244 A lt2 P x) = (term245 A lt2 P x).
Proof. exact (MK_COMB (@lem309144 A lt2 x P) (@lem309142 A P x)). Qed.
Lemma lem309146 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term246 A lt2 P x) = (term244 A lt2 P x).
Proof. exact (@lem17362 (term48 A lt2 x P) (term11 A P x)). Qed.
Lemma lem309147 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term246 A lt2 P x) = (term245 A lt2 P x).
Proof. exact (TRANS (@lem309146 A lt2 P x) (@lem309145 A lt2 P x)). Qed.
Lemma lem309148 {A : Type'} (P : A -> Prop) : (term120 A P) = (term16 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem309149 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term247 A lt2 P) = (term248 A lt2 P).
Proof. exact (@lem309148 A (term54 A lt2 P)). Qed.
Lemma lem309150 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term249 A lt2 P x) = (term52 A lt2 P x).
Proof. exact (eq_refl (term249 A lt2 P x)). Qed.
Lemma lem309151 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem309152 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term250 A lt2 P x) = (term246 A lt2 P x).
Proof. exact (MK_COMB (@lem309151) (@lem309150 A lt2 P x)). Qed.
Lemma lem309153 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term250 A lt2 P x) = (term245 A lt2 P x).
Proof. exact (TRANS (@lem309152 A lt2 P x) (@lem309147 A lt2 P x)). Qed.
Lemma lem309154 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term251 A lt2 P) = (term252 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem309153 A lt2 P x)). Qed.
Lemma lem309155 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem309156 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term248 A lt2 P) = (term253 A lt2 P).
Proof. exact (MK_COMB (@lem309155 A) (@lem309154 A lt2 P)). Qed.
Lemma lem309157 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term247 A lt2 P) = (term253 A lt2 P).
Proof. exact (TRANS (@lem309149 A lt2 P) (@lem309156 A lt2 P)). Qed.
Lemma lem309158 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term11 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem309159 {A : Type'} (P : A -> Prop) : (term3 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem309158 A P x)). Qed.
Lemma lem309160 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309161 {A : Type'} (P : A -> Prop) : (term60 A P) = (term60 A P).
Proof. exact (MK_COMB (@lem309160 A) (@lem309159 A P)). Qed.
Lemma lem309162 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem309163 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term254 A lt2 P) = (term255 A lt2 P).
Proof. exact (MK_COMB (@lem309162) (@lem309157 A lt2 P)). Qed.
Lemma lem309164 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term256 A lt2 P) = (term257 A lt2 P).
Proof. exact (MK_COMB (@lem309163 A lt2 P) (@lem309161 A P)). Qed.
Lemma lem309165 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term61 A lt2 P) = (term256 A lt2 P).
Proof. exact (@lem17265 (term56 A lt2 P) (term60 A P)). Qed.
Lemma lem309166 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term61 A lt2 P) = (term257 A lt2 P).
Proof. exact (TRANS (@lem309165 A lt2 P) (@lem309164 A lt2 P)). Qed.
Lemma lem309253 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem309254 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (@lem309253 A P Q). Qed.
Lemma lem309255 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term258 A lt2 P) = (term259 A lt2 P).
Proof. exact (@lem309254 A (term252 A lt2 P) (term60 A P)). Qed.
Lemma lem309256 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term260 A lt2 P x) = (term245 A lt2 P x).
Proof. exact (eq_refl (term260 A lt2 P x)). Qed.
Lemma lem309257 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term261 A lt2 P) = (term252 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem309256 A lt2 P x)). Qed.
Lemma lem309258 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem309259 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term262 A lt2 P) = (term253 A lt2 P).
Proof. exact (MK_COMB (@lem309258 A) (@lem309257 A lt2 P)). Qed.
Lemma lem309260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem309261 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term263 A lt2 P) = (term255 A lt2 P).
Proof. exact (MK_COMB (@lem309260) (@lem309259 A lt2 P)). Qed.
Lemma lem309262 {A : Type'} (P : A -> Prop) : (term60 A P) = (term60 A P).
Proof. exact (eq_refl (term60 A P)). Qed.
Lemma lem309263 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term258 A lt2 P) = (term257 A lt2 P).
Proof. exact (MK_COMB (@lem309261 A lt2 P) (@lem309262 A P)). Qed.
Lemma lem309264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem309265 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term264 A lt2 P) = (term265 A lt2 P).
Proof. exact (MK_COMB (@lem309264) (@lem309263 A lt2 P)). Qed.
Lemma lem309266 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term260 A lt2 P x) = (term245 A lt2 P x).
Proof. exact (eq_refl (term260 A lt2 P x)). Qed.
Lemma lem309267 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem309268 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x : A) : (term266 A lt2 P x) = (term267 A lt2 P x).
Proof. exact (MK_COMB (@lem309267) (@lem309266 A lt2 P x)). Qed.
Lemma lem309269 {A : Type'} (P : A -> Prop) : (term60 A P) = (term60 A P).
Proof. exact (eq_refl (term60 A P)). Qed.
Lemma lem309270 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term268 A lt2 x P) = (term269 A lt2 x P).
Proof. exact (MK_COMB (@lem309268 A lt2 P x) (@lem309269 A P)). Qed.
Lemma lem309271 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term270 A lt2 P) = (term271 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem309270 A lt2 x P)). Qed.
Lemma lem309272 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem309273 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term259 A lt2 P) = (term272 A lt2 P).
Proof. exact (MK_COMB (@lem309272 A) (@lem309271 A lt2 P)). Qed.
Lemma lem309274 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term258 A lt2 P) = (term259 A lt2 P)) = ((term257 A lt2 P) = (term272 A lt2 P)).
Proof. exact (MK_COMB (@lem309265 A lt2 P) (@lem309273 A lt2 P)). Qed.
Lemma lem309276 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term257 A lt2 P) = (term272 A lt2 P).
Proof. exact (EQ_MP (@lem309274 A lt2 P) (@lem309255 A lt2 P)). Qed.
Lemma lem309277 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term61 A lt2 P) = (term272 A lt2 P).
Proof. exact (TRANS (@lem309166 A lt2 P) (@lem309276 A lt2 P)). Qed.
Lemma lem309278 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term61 A lt2 P) : term272 A lt2 P.
Proof. exact (EQ_MP (@lem309277 A lt2 P) (@lem309123 A lt2 P h1)). Qed.
Lemma lem309279 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem309280 {A : Type'} (P : A -> Prop) : (term82 A P) = (term82 A P).
Proof. exact (fun_ext (fun x : A => @lem309279 A P x)). Qed.
Lemma lem309281 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem309290 {A : Type'} (P : A -> Prop) : (term235 A P) = (term235 A P).
Proof. exact (MK_COMB (@lem309281 A) (@lem309280 A P)). Qed.
Lemma lem309291 {A : Type'} (P : A -> Prop) (h1 : term235 A P) : term235 A P.
Proof. exact (EQ_MP (@lem309290 A P) (@lem309124 A P h1)). Qed.
Lemma lem309296 {A : Type'} (P : A -> Prop) (y : A) : (term22 A P y) = (P y).
Proof. exact (@lem16933 (P y)). Qed.
Lemma lem309298 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term273 A lt2 y x) = (term273 A lt2 y x).
Proof. exact (eq_refl (term273 A lt2 y x)). Qed.
Lemma lem309299 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term274 A lt2 x P y) = (term275 A lt2 x P y).
Proof. exact (MK_COMB (@lem309298 A lt2 y x) (@lem309296 A P y)). Qed.
Lemma lem309300 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term276 A lt2 x P y) = (term274 A lt2 x P y).
Proof. exact (@lem17362 (lt2 y x) (term11 A P y)). Qed.
Lemma lem309301 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term276 A lt2 x P y) = (term275 A lt2 x P y).
Proof. exact (TRANS (@lem309300 A lt2 x P y) (@lem309299 A lt2 x P y)). Qed.
Lemma lem309302 {A : Type'} (P : A -> Prop) : (term120 A P) = (term16 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem309303 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term277 A lt2 x P) = (term278 A lt2 x P).
Proof. exact (@lem309302 A (term46 A lt2 x P)). Qed.
Lemma lem309304 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term279 A lt2 x P y) = (term44 A lt2 x P y).
Proof. exact (eq_refl (term279 A lt2 x P y)). Qed.
Lemma lem309305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem309306 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term280 A lt2 x P y) = (term276 A lt2 x P y).
Proof. exact (MK_COMB (@lem309305) (@lem309304 A lt2 x P y)). Qed.
Lemma lem309307 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term280 A lt2 x P y) = (term275 A lt2 x P y).
Proof. exact (TRANS (@lem309306 A lt2 x P y) (@lem309301 A lt2 x P y)). Qed.
Lemma lem309308 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term281 A lt2 x P) = (term282 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem309307 A lt2 x P y)). Qed.
Lemma lem309309 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem309310 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term278 A lt2 x P) = (term283 A lt2 x P).
Proof. exact (MK_COMB (@lem309309 A) (@lem309308 A lt2 x P)). Qed.
Lemma lem309311 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term277 A lt2 x P) = (term283 A lt2 x P).
Proof. exact (TRANS (@lem309303 A lt2 x P) (@lem309310 A lt2 x P)). Qed.
Lemma lem309313 {A : Type'} (P : A -> Prop) (x : A) : (term284 A P x) = (term284 A P x).
Proof. exact (eq_refl (term284 A P x)). Qed.
Lemma lem309314 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term285 A lt2 x P) = (term286 A lt2 x P).
Proof. exact (MK_COMB (@lem309313 A P x) (@lem309311 A lt2 x P)). Qed.
Lemma lem309315 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term287 A lt2 x P) = (term285 A lt2 x P).
Proof. exact (@lem17045 (P x) (term48 A lt2 x P)). Qed.
Lemma lem309316 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term287 A lt2 x P) = (term286 A lt2 x P).
Proof. exact (TRANS (@lem309315 A lt2 x P) (@lem309314 A lt2 x P)). Qed.
Lemma lem309317 {A : Type'} (P : A -> Prop) : (term90 A P) = (term60 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem309318 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term238 A lt2 P) = (term288 A lt2 P).
Proof. exact (@lem309317 A (term233 A lt2 P)). Qed.
Lemma lem309319 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term289 A lt2 P x) = (term232 A lt2 x P).
Proof. exact (eq_refl (term289 A lt2 P x)). Qed.
Lemma lem309320 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem309321 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term290 A lt2 P x) = (term287 A lt2 x P).
Proof. exact (MK_COMB (@lem309320) (@lem309319 A lt2 x P)). Qed.
Lemma lem309322 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term290 A lt2 P x) = (term286 A lt2 x P).
Proof. exact (TRANS (@lem309321 A lt2 x P) (@lem309316 A lt2 x P)). Qed.
Lemma lem309323 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term291 A lt2 P) = (term292 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem309322 A lt2 x P)). Qed.
Lemma lem309324 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309325 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term288 A lt2 P) = (term293 A lt2 P).
Proof. exact (MK_COMB (@lem309324 A) (@lem309323 A lt2 P)). Qed.
Lemma lem309326 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term238 A lt2 P) = (term293 A lt2 P).
Proof. exact (TRANS (@lem309318 A lt2 P) (@lem309325 A lt2 P)). Qed.
Lemma lem309409 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem309410 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (@lem309409 A P Q). Qed.
Lemma lem309411 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term294 A lt2 x P) = (term295 A lt2 x P).
Proof. exact (@lem309410 A (term11 A P x) (term282 A lt2 x P)). Qed.
Lemma lem309412 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term296 A lt2 x P y) = (term275 A lt2 x P y).
Proof. exact (eq_refl (term296 A lt2 x P y)). Qed.
Lemma lem309413 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term297 A lt2 x P) = (term282 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem309412 A lt2 x P y)). Qed.
Lemma lem309414 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem309415 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term298 A lt2 x P) = (term283 A lt2 x P).
Proof. exact (MK_COMB (@lem309414 A) (@lem309413 A lt2 x P)). Qed.
Lemma lem309416 {A : Type'} (P : A -> Prop) (x : A) : (term284 A P x) = (term284 A P x).
Proof. exact (eq_refl (term284 A P x)). Qed.
Lemma lem309417 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term294 A lt2 x P) = (term286 A lt2 x P).
Proof. exact (MK_COMB (@lem309416 A P x) (@lem309415 A lt2 x P)). Qed.
Lemma lem309418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem309419 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term299 A lt2 x P) = (term300 A lt2 x P).
Proof. exact (MK_COMB (@lem309418) (@lem309417 A lt2 x P)). Qed.
Lemma lem309420 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term296 A lt2 x P y) = (term275 A lt2 x P y).
Proof. exact (eq_refl (term296 A lt2 x P y)). Qed.
Lemma lem309421 {A : Type'} (P : A -> Prop) (x : A) : (term284 A P x) = (term284 A P x).
Proof. exact (eq_refl (term284 A P x)). Qed.
Lemma lem309422 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term301 A lt2 x P y) = (term302 A lt2 x P y).
Proof. exact (MK_COMB (@lem309421 A P x) (@lem309420 A lt2 x P y)). Qed.
Lemma lem309423 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term303 A lt2 x P) = (term304 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem309422 A lt2 x P y)). Qed.
Lemma lem309424 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem309425 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term295 A lt2 x P) = (term305 A lt2 x P).
Proof. exact (MK_COMB (@lem309424 A) (@lem309423 A lt2 x P)). Qed.
Lemma lem309426 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term294 A lt2 x P) = (term295 A lt2 x P)) = ((term286 A lt2 x P) = (term305 A lt2 x P)).
Proof. exact (MK_COMB (@lem309419 A lt2 x P) (@lem309425 A lt2 x P)). Qed.
Lemma lem309427 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term286 A lt2 x P) = (term305 A lt2 x P).
Proof. exact (EQ_MP (@lem309426 A lt2 x P) (@lem309411 A lt2 x P)). Qed.
Lemma lem309428 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term292 A lt2 P) = (term306 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem309427 A lt2 x P)). Qed.
Lemma lem309429 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309430 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term293 A lt2 P) = (term307 A lt2 P).
Proof. exact (MK_COMB (@lem309429 A) (@lem309428 A lt2 P)). Qed.
Lemma lem309432 {A B : Type'} (P : type1413 A B) : (term153 A B P) = (term154 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem309433 {A : Type'} (P : type1402 A) : (term155 A P) = (term156 A P).
Proof. exact (@lem309432 A A P). Qed.
Lemma lem309434 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term308 A lt2 P) = (term309 A lt2 P).
Proof. exact (@lem309433 A (term310 A lt2 P)). Qed.
Lemma lem309435 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term311 A lt2 P x) = (term304 A lt2 x P).
Proof. exact (eq_refl (term311 A lt2 P x)). Qed.
Lemma lem309436 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem309437 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term312 A lt2 P x y) = (term313 A lt2 x P y).
Proof. exact (MK_COMB (@lem309435 A lt2 x P) (@lem309436 A y)). Qed.
Lemma lem309438 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term313 A lt2 x P y) = (term302 A lt2 x P y).
Proof. exact (eq_refl (term313 A lt2 x P y)). Qed.
Lemma lem309439 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term312 A lt2 P x y) = (term302 A lt2 x P y).
Proof. exact (TRANS (@lem309437 A lt2 x P y) (@lem309438 A lt2 x P y)). Qed.
Lemma lem309440 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term314 A lt2 P x) = (term304 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem309439 A lt2 x P y)). Qed.
Lemma lem309441 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem309442 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term315 A lt2 P x) = (term305 A lt2 x P).
Proof. exact (MK_COMB (@lem309441 A) (@lem309440 A lt2 x P)). Qed.
Lemma lem309443 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term316 A lt2 P) = (term306 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem309442 A lt2 x P)). Qed.
Lemma lem309444 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309445 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term308 A lt2 P) = (term307 A lt2 P).
Proof. exact (MK_COMB (@lem309444 A) (@lem309443 A lt2 P)). Qed.
Lemma lem309446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem309447 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term317 A lt2 P) = (term318 A lt2 P).
Proof. exact (MK_COMB (@lem309446) (@lem309445 A lt2 P)). Qed.
Lemma lem309448 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term311 A lt2 P x) = (term304 A lt2 x P).
Proof. exact (eq_refl (term311 A lt2 P x)). Qed.
Lemma lem309449 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem309450 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term319 A lt2 P y x) = (term320 A lt2 P y x).
Proof. exact (MK_COMB (@lem309448 A lt2 x P) (@lem309449 A y x)). Qed.
Lemma lem309451 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term320 A lt2 P y x) = (term321 A lt2 P y x).
Proof. exact (eq_refl (term320 A lt2 P y x)). Qed.
Lemma lem309452 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term319 A lt2 P y x) = (term321 A lt2 P y x).
Proof. exact (TRANS (@lem309450 A lt2 P y x) (@lem309451 A lt2 P y x)). Qed.
Lemma lem309453 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term322 A lt2 P y) = (term323 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem309452 A lt2 P y x)). Qed.
Lemma lem309454 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309455 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term324 A lt2 P y) = (term325 A lt2 P y).
Proof. exact (MK_COMB (@lem309454 A) (@lem309453 A lt2 P y)). Qed.
Lemma lem309456 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term326 A lt2 P) = (term327 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem309455 A lt2 P y)). Qed.
Lemma lem309457 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem309458 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term309 A lt2 P) = (term328 A lt2 P).
Proof. exact (MK_COMB (@lem309457 A) (@lem309456 A lt2 P)). Qed.
Lemma lem309459 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term308 A lt2 P) = (term309 A lt2 P)) = ((term307 A lt2 P) = (term328 A lt2 P)).
Proof. exact (MK_COMB (@lem309447 A lt2 P) (@lem309458 A lt2 P)). Qed.
Lemma lem309460 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term307 A lt2 P) = (term328 A lt2 P).
Proof. exact (EQ_MP (@lem309459 A lt2 P) (@lem309434 A lt2 P)). Qed.
Lemma lem309462 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term293 A lt2 P) = (term328 A lt2 P).
Proof. exact (TRANS (@lem309430 A lt2 P) (@lem309460 A lt2 P)). Qed.
Lemma lem309463 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term238 A lt2 P) = (term328 A lt2 P).
Proof. exact (TRANS (@lem309326 A lt2 P) (@lem309462 A lt2 P)). Qed.
Lemma lem309464 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term238 A lt2 P) : term328 A lt2 P.
Proof. exact (EQ_MP (@lem309463 A lt2 P) (@lem309129 A lt2 P h1)). Qed.
Lemma lem309465 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term325 A lt2 P y.
Proof. exact (h1). Qed.
Lemma lem309467 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term269 A lt2 x' P) : term269 A lt2 x' P.
Proof. exact (h1). Qed.
Lemma lem309490 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term321 A lt2 P y x) = (term321 A lt2 P y x).
Proof. exact (eq_refl (term321 A lt2 P y x)). Qed.
Lemma lem309491 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term323 A lt2 P y) = (term323 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem309490 A lt2 P y x)). Qed.
Lemma lem309492 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309493 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term325 A lt2 P y) = (term325 A lt2 P y).
Proof. exact (MK_COMB (@lem309492 A) (@lem309491 A lt2 P y)). Qed.
Lemma lem309494 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term325 A lt2 P y.
Proof. exact (EQ_MP (@lem309493 A lt2 P y) (@lem309465 A lt2 P y h1)). Qed.
Lemma lem309498 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem309503 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term11 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem309504 {A : Type'} (P : A -> Prop) : (term3 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem309503 A P x)). Qed.
Lemma lem309505 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309506 {A : Type'} (P : A -> Prop) : (term60 A P) = (term60 A P).
Proof. exact (MK_COMB (@lem309505 A) (@lem309504 A P)). Qed.
Lemma lem309509 {A : Type'} (P : A -> Prop) (x' : A) : (P x') = (P x').
Proof. exact (eq_refl (P x')). Qed.
Lemma lem309524 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (y : A) : (term239 A lt2 x' P y) = (term239 A lt2 x' P y).
Proof. exact (eq_refl (term239 A lt2 x' P y)). Qed.
Lemma lem309525 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term240 A lt2 x' P) = (term240 A lt2 x' P).
Proof. exact (fun_ext (fun y : A => @lem309524 A lt2 x' P y)). Qed.
Lemma lem309526 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309527 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term241 A lt2 x' P) = (term241 A lt2 x' P).
Proof. exact (MK_COMB (@lem309526 A) (@lem309525 A lt2 x' P)). Qed.
Lemma lem309528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem309529 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term243 A lt2 x' P) = (term243 A lt2 x' P).
Proof. exact (MK_COMB (@lem309528) (@lem309527 A lt2 x' P)). Qed.
Lemma lem309530 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) : (term245 A lt2 P x') = (term245 A lt2 P x').
Proof. exact (MK_COMB (@lem309529 A lt2 x' P) (@lem309509 A P x')). Qed.
Lemma lem309531 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem309532 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) : (term267 A lt2 P x') = (term267 A lt2 P x').
Proof. exact (MK_COMB (@lem309531) (@lem309530 A lt2 P x')). Qed.
Lemma lem309533 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term269 A lt2 x' P) = (term269 A lt2 x' P).
Proof. exact (MK_COMB (@lem309532 A lt2 P x') (@lem309506 A P)). Qed.
Lemma lem309534 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term269 A lt2 x' P) : term269 A lt2 x' P.
Proof. exact (EQ_MP (@lem309533 A lt2 x' P) (@lem309467 A lt2 x' P h1)). Qed.
Lemma lem309535 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : term245 A lt2 P x'.
Proof. exact (h1). Qed.
Lemma lem309536 {A : Type'} (P : A -> Prop) (h1 : term60 A P) : term60 A P.
Proof. exact (h1). Qed.
Lemma lem309538 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : term241 A lt2 x' P.
Proof. exact (proj1 (@lem309535 A lt2 P x' h1)). Qed.
Lemma lem309556 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term321 A lt2 P y x) = (term329 A lt2 P y x).
Proof. exact (@lem19490 (term179 A lt2 y x) (term11 A P x) (term205 A P y x)). Qed.
Lemma lem309557 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term323 A lt2 P y) = (term330 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem309556 A lt2 P y x)). Qed.
Lemma lem309558 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309560 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term325 A lt2 P y) = (term331 A lt2 P y).
Proof. exact (MK_COMB (@lem309558 A) (@lem309557 A lt2 P y)). Qed.
Lemma lem309561 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term331 A lt2 P y.
Proof. exact (EQ_MP (@lem309560 A lt2 P y) (@lem309494 A lt2 P y h1)). Qed.
Lemma lem309573 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (y : A) : (term239 A lt2 x' P y) = (term239 A lt2 x' P y).
Proof. exact (eq_refl (term239 A lt2 x' P y)). Qed.
Lemma lem309574 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term240 A lt2 x' P) = (term240 A lt2 x' P).
Proof. exact (fun_ext (fun y : A => @lem309573 A lt2 x' P y)). Qed.
Lemma lem309575 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309577 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) : (term241 A lt2 x' P) = (term241 A lt2 x' P).
Proof. exact (MK_COMB (@lem309575 A) (@lem309574 A lt2 x' P)). Qed.
Lemma lem309578 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : term241 A lt2 x' P.
Proof. exact (EQ_MP (@lem309577 A lt2 x' P) (@lem309538 A lt2 P x' h1)). Qed.
Lemma lem309609 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem309611 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term11 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem309612 {A : Type'} (P : A -> Prop) : (term3 A P) = (term3 A P).
Proof. exact (fun_ext (fun x : A => @lem309611 A P x)). Qed.
Lemma lem309613 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem309615 {A : Type'} (P : A -> Prop) : (term60 A P) = (term60 A P).
Proof. exact (MK_COMB (@lem309613 A) (@lem309612 A P)). Qed.
Lemma lem309616 {A : Type'} (P : A -> Prop) (h1 : term60 A P) : term60 A P.
Proof. exact (EQ_MP (@lem309615 A P) (@lem309536 A P h1)). Qed.
Lemma lem309617 {A : Type'} (_6793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term332 A lt2 P y _6793.
Proof. exact (@lem309561 A lt2 P y h1 _6793). Qed.
Lemma lem309618 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (_6793 : A) : (term332 A lt2 P y _6793) = (term329 A lt2 P y _6793).
Proof. exact (eq_refl (term332 A lt2 P y _6793)). Qed.
Lemma lem309619 {A : Type'} (_6793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term329 A lt2 P y _6793.
Proof. exact (EQ_MP (@lem309618 A lt2 P y _6793) (@lem309617 A _6793 lt2 P y h1)). Qed.
Lemma lem309620 {A : Type'} (_6794 : A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : term333 A lt2 x' P _6794.
Proof. exact (@lem309578 A lt2 P x' h1 _6794). Qed.
Lemma lem309621 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6794 : A) : (term333 A lt2 x' P _6794) = (term239 A lt2 x' P _6794).
Proof. exact (eq_refl (term333 A lt2 x' P _6794)). Qed.
Lemma lem309626 {A : Type'} (_6796 : A) (P : A -> Prop) (h1 : term60 A P) : term10 A P _6796.
Proof. exact (@lem309616 A P h1 _6796). Qed.
Lemma lem309627 {A : Type'} (P : A -> Prop) (_6796 : A) : (term10 A P _6796) = (term11 A P _6796).
Proof. exact (eq_refl (term10 A P _6796)). Qed.
Lemma lem309640 {A : Type'} (_6794 : A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : term239 A lt2 x' P _6794.
Proof. exact (EQ_MP (@lem309621 A lt2 x' P _6794) (@lem309620 A _6794 lt2 P x' h1)). Qed.
Lemma lem309648 {A : Type'} (_6793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term334 A P lt2 y _6793.
Proof. exact (proj1 (@lem309619 A _6793 lt2 P y h1)). Qed.
Lemma lem309654 {A : Type'} (_6793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term335 A P y _6793.
Proof. exact (proj2 (@lem309619 A _6793 lt2 P y h1)). Qed.
Lemma lem309656 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem309658 {A : Type'} (_6796 : A) (P : A -> Prop) (h1 : term60 A P) : term11 A P _6796.
Proof. exact (EQ_MP (@lem309627 A P _6796) (@lem309626 A _6796 P h1)). Qed.
Lemma lem309672 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : P x'.
Proof. exact (proj2 (@lem309535 A lt2 P x' h1)). Qed.
Lemma lem309673 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : term187 A P x'.
Proof. exact (fun h0 : term11 A P x' => @lem309672 A lt2 P x' h1). Qed.
Lemma lem309675 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem309676 {A : Type'} (P : A -> Prop) (x' : A) : (term187 A P x') = (P x').
Proof. exact (@lem309675 (P x')). Qed.
Lemma lem309677 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : P x'.
Proof. exact (EQ_MP (@lem309676 A P x') (@lem309673 A lt2 P x' h1)). Qed.
Lemma lem309683 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem309684 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6793 : A) : (term334 A P lt2 y _6793) = (term336 A lt2 y P _6793).
Proof. exact (@lem309683 (term179 A lt2 y _6793) (term11 A P _6793)). Qed.
Lemma lem309690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem309691 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6793 : A) : (term337 A P lt2 y _6793) = (term338 A lt2 y P _6793).
Proof. exact (MK_COMB (@lem309690) (@lem309684 A lt2 y P _6793)). Qed.
Lemma lem309697 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6793 : A) : (term336 A lt2 y P _6793) = (term336 A lt2 y P _6793).
Proof. exact (eq_refl (term336 A lt2 y P _6793)). Qed.
Lemma lem309698 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6793 : A) : ((term334 A P lt2 y _6793) = (term336 A lt2 y P _6793)) = ((term336 A lt2 y P _6793) = (term336 A lt2 y P _6793)).
Proof. exact (MK_COMB (@lem309691 A lt2 y P _6793) (@lem309697 A lt2 y P _6793)). Qed.
Lemma lem309700 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem309701 (x : Prop) : (x = x) = True.
Proof. exact (@lem309700 Prop x). Qed.
Lemma lem309702 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6793 : A) : ((term336 A lt2 y P _6793) = (term336 A lt2 y P _6793)) = True.
Proof. exact (@lem309701 (term336 A lt2 y P _6793)). Qed.
Lemma lem309703 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6793 : A) : ((term334 A P lt2 y _6793) = (term336 A lt2 y P _6793)) = True.
Proof. exact (TRANS (@lem309698 A lt2 y P _6793) (@lem309702 A lt2 y P _6793)). Qed.
Lemma lem309704 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6793 : A) : True = ((term334 A P lt2 y _6793) = (term336 A lt2 y P _6793)).
Proof. exact (SYM (@lem309703 A lt2 y P _6793)). Qed.
Lemma lem309705 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6793 : A) : (term334 A P lt2 y _6793) = (term336 A lt2 y P _6793).
Proof. exact (EQ_MP (@lem309704 A lt2 y P _6793) (@lem0)). Qed.
Lemma lem309706 {A : Type'} (_6793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term336 A lt2 y P _6793.
Proof. exact (EQ_MP (@lem309705 A lt2 y P _6793) (@lem309648 A _6793 lt2 P y h1)). Qed.
Lemma lem309708 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem309709 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6793 : A) : (term336 A lt2 y P _6793) = (term339 A P lt2 y _6793).
Proof. exact (@lem309708 (term11 A P _6793) (term179 A lt2 y _6793)). Qed.
Lemma lem309711 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem309712 {A : Type'} (P : A -> Prop) (_6793 : A) : (term22 A P _6793) = (P _6793).
Proof. exact (@lem309711 (P _6793)). Qed.
Lemma lem309713 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem309714 {A : Type'} (P : A -> Prop) (_6793 : A) : (term340 A P _6793) = (term341 A P _6793).
Proof. exact (MK_COMB (@lem309713) (@lem309712 A P _6793)). Qed.
Lemma lem309715 {A : Type'} (lt2 : type1402 A) (y : A -> A) (_6793 : A) : (term179 A lt2 y _6793) = (term179 A lt2 y _6793).
Proof. exact (eq_refl (term179 A lt2 y _6793)). Qed.
Lemma lem309716 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6793 : A) : (term339 A P lt2 y _6793) = (term342 A P lt2 y _6793).
Proof. exact (MK_COMB (@lem309714 A P _6793) (@lem309715 A lt2 y _6793)). Qed.
Lemma lem309717 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6793 : A) : (term336 A lt2 y P _6793) = (term342 A P lt2 y _6793).
Proof. exact (TRANS (@lem309709 A P lt2 y _6793) (@lem309716 A P lt2 y _6793)). Qed.
Lemma lem309720 {A : Type'} (_6793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term342 A P lt2 y _6793.
Proof. exact (EQ_MP (@lem309717 A P lt2 y _6793) (@lem309706 A _6793 lt2 P y h1)). Qed.
Lemma lem309721 {A : Type'} (_6793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term342 A P lt2 y _6793.
Proof. exact (@lem309720 A _6793 lt2 P y h1). Qed.
Lemma lem309722 {A : Type'} (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term342 A P lt2 y x'.
Proof. exact (@lem309721 A x' lt2 P y h1). Qed.
Lemma lem309725 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term325 A lt2 P y) (h2 : term245 A lt2 P x') : term179 A lt2 y x'.
Proof. exact (@lem309722 A x' lt2 P y h1 (@lem309677 A lt2 P x' h2)). Qed.
Lemma lem309726 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term325 A lt2 P y) (h2 : term245 A lt2 P x') : term195 A lt2 y x'.
Proof. exact (fun h0 : term196 A lt2 y x' => @lem309725 A y lt2 P x' h1 h2). Qed.
Lemma lem309728 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem309729 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x' : A) : (term195 A lt2 y x') = (term179 A lt2 y x').
Proof. exact (@lem309728 (term179 A lt2 y x')). Qed.
Lemma lem309730 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term325 A lt2 P y) (h2 : term245 A lt2 P x') : term179 A lt2 y x'.
Proof. exact (EQ_MP (@lem309729 A lt2 y x') (@lem309726 A y lt2 P x' h1 h2)). Qed.
Lemma lem309732 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : P x'.
Proof. exact (proj2 (@lem309535 A lt2 P x' h1)). Qed.
Lemma lem309733 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : term187 A P x'.
Proof. exact (fun h0 : term11 A P x' => @lem309732 A lt2 P x' h1). Qed.
Lemma lem309735 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem309736 {A : Type'} (P : A -> Prop) (x' : A) : (term187 A P x') = (P x').
Proof. exact (@lem309735 (P x')). Qed.
Lemma lem309737 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : P x'.
Proof. exact (EQ_MP (@lem309736 A P x') (@lem309733 A lt2 P x' h1)). Qed.
Lemma lem309743 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem309744 {A : Type'} (y : A -> A) (P : A -> Prop) (_6793 : A) : (term335 A P y _6793) = (term343 A y P _6793).
Proof. exact (@lem309743 (term205 A P y _6793) (term11 A P _6793)). Qed.
Lemma lem309750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem309751 {A : Type'} (y : A -> A) (P : A -> Prop) (_6793 : A) : (term344 A P y _6793) = (term345 A y P _6793).
Proof. exact (MK_COMB (@lem309750) (@lem309744 A y P _6793)). Qed.
Lemma lem309757 {A : Type'} (y : A -> A) (P : A -> Prop) (_6793 : A) : (term343 A y P _6793) = (term343 A y P _6793).
Proof. exact (eq_refl (term343 A y P _6793)). Qed.
Lemma lem309758 {A : Type'} (y : A -> A) (P : A -> Prop) (_6793 : A) : ((term335 A P y _6793) = (term343 A y P _6793)) = ((term343 A y P _6793) = (term343 A y P _6793)).
Proof. exact (MK_COMB (@lem309751 A y P _6793) (@lem309757 A y P _6793)). Qed.
Lemma lem309760 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem309761 (x : Prop) : (x = x) = True.
Proof. exact (@lem309760 Prop x). Qed.
Lemma lem309762 {A : Type'} (y : A -> A) (P : A -> Prop) (_6793 : A) : ((term343 A y P _6793) = (term343 A y P _6793)) = True.
Proof. exact (@lem309761 (term343 A y P _6793)). Qed.
Lemma lem309763 {A : Type'} (y : A -> A) (P : A -> Prop) (_6793 : A) : ((term335 A P y _6793) = (term343 A y P _6793)) = True.
Proof. exact (TRANS (@lem309758 A y P _6793) (@lem309762 A y P _6793)). Qed.
Lemma lem309764 {A : Type'} (y : A -> A) (P : A -> Prop) (_6793 : A) : True = ((term335 A P y _6793) = (term343 A y P _6793)).
Proof. exact (SYM (@lem309763 A y P _6793)). Qed.
Lemma lem309765 {A : Type'} (y : A -> A) (P : A -> Prop) (_6793 : A) : (term335 A P y _6793) = (term343 A y P _6793).
Proof. exact (EQ_MP (@lem309764 A y P _6793) (@lem0)). Qed.
Lemma lem309766 {A : Type'} (_6793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term343 A y P _6793.
Proof. exact (EQ_MP (@lem309765 A y P _6793) (@lem309654 A _6793 lt2 P y h1)). Qed.
Lemma lem309768 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem309769 {A : Type'} (P : A -> Prop) (y : A -> A) (_6793 : A) : (term343 A y P _6793) = (term346 A P y _6793).
Proof. exact (@lem309768 (term11 A P _6793) (term205 A P y _6793)). Qed.
Lemma lem309771 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem309772 {A : Type'} (P : A -> Prop) (_6793 : A) : (term22 A P _6793) = (P _6793).
Proof. exact (@lem309771 (P _6793)). Qed.
Lemma lem309773 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem309774 {A : Type'} (P : A -> Prop) (_6793 : A) : (term340 A P _6793) = (term341 A P _6793).
Proof. exact (MK_COMB (@lem309773) (@lem309772 A P _6793)). Qed.
Lemma lem309775 {A : Type'} (P : A -> Prop) (y : A -> A) (_6793 : A) : (term205 A P y _6793) = (term205 A P y _6793).
Proof. exact (eq_refl (term205 A P y _6793)). Qed.
Lemma lem309776 {A : Type'} (P : A -> Prop) (y : A -> A) (_6793 : A) : (term346 A P y _6793) = (term347 A P y _6793).
Proof. exact (MK_COMB (@lem309774 A P _6793) (@lem309775 A P y _6793)). Qed.
Lemma lem309777 {A : Type'} (P : A -> Prop) (y : A -> A) (_6793 : A) : (term343 A y P _6793) = (term347 A P y _6793).
Proof. exact (TRANS (@lem309769 A P y _6793) (@lem309776 A P y _6793)). Qed.
Lemma lem309780 {A : Type'} (_6793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term347 A P y _6793.
Proof. exact (EQ_MP (@lem309777 A P y _6793) (@lem309766 A _6793 lt2 P y h1)). Qed.
Lemma lem309781 {A : Type'} (_6793 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term347 A P y _6793.
Proof. exact (@lem309780 A _6793 lt2 P y h1). Qed.
Lemma lem309782 {A : Type'} (x' : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term325 A lt2 P y) : term347 A P y x'.
Proof. exact (@lem309781 A x' lt2 P y h1). Qed.
Lemma lem309785 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term325 A lt2 P y) (h2 : term245 A lt2 P x') : term205 A P y x'.
Proof. exact (@lem309782 A x' lt2 P y h1 (@lem309737 A lt2 P x' h2)). Qed.
Lemma lem309786 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term325 A lt2 P y) (h2 : term245 A lt2 P x') : term206 A P y x'.
Proof. exact (fun h0 : term180 A P y x' => @lem309785 A y lt2 P x' h1 h2). Qed.
Lemma lem309788 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem309789 {A : Type'} (P : A -> Prop) (y : A -> A) (x' : A) : (term206 A P y x') = (term205 A P y x').
Proof. exact (@lem309788 (term205 A P y x')). Qed.
Lemma lem309790 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term325 A lt2 P y) (h2 : term245 A lt2 P x') : term205 A P y x'.
Proof. exact (EQ_MP (@lem309789 A P y x') (@lem309786 A y lt2 P x' h1 h2)). Qed.
Lemma lem309792 (a : Prop) (b : Prop) : (term348 a b) = (term349 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem309793 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6794 : A) : (term239 A lt2 x' P _6794) = (term350 A lt2 x' P _6794).
Proof. exact (@lem309792 (lt2 _6794 x') (P _6794)). Qed.
Lemma lem309795 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem309796 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6794 : A) : (term350 A lt2 x' P _6794) = (term351 A lt2 x' P _6794).
Proof. exact (@lem309795 (term275 A lt2 x' P _6794)). Qed.
Lemma lem309797 {A : Type'} (lt2 : type1402 A) (x' : A) (P : A -> Prop) (_6794 : A) : (term239 A lt2 x' P _6794) = (term351 A lt2 x' P _6794).
Proof. exact (TRANS (@lem309793 A lt2 x' P _6794) (@lem309796 A lt2 x' P _6794)). Qed.
Lemma lem309799 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term325 A lt2 P y) (h2 : term245 A lt2 P x') : term352 A lt2 P y x'.
Proof. exact (conj (@lem309730 A y lt2 P x' h1 h2) (@lem309790 A y lt2 P x' h1 h2)). Qed.
Lemma lem309801 {A : Type'} (_6794 : A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : term351 A lt2 x' P _6794.
Proof. exact (EQ_MP (@lem309797 A lt2 x' P _6794) (@lem309640 A _6794 lt2 P x' h1)). Qed.
Lemma lem309802 {A : Type'} (_6794 : A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : term351 A lt2 x' P _6794.
Proof. exact (@lem309801 A _6794 lt2 P x' h1). Qed.
Lemma lem309803 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term245 A lt2 P x') : term353 A lt2 P y x'.
Proof. exact (@lem309802 A (y x') lt2 P x' h1). Qed.
Lemma lem309806 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term325 A lt2 P y) (h2 : term245 A lt2 P x') : False.
Proof. exact (@lem309803 A y lt2 P x' h2 (@lem309799 A y lt2 P x' h1 h2)). Qed.
Lemma lem309807 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term325 A lt2 P y) (h2 : term245 A lt2 P x') : term190.
Proof. exact (fun h0 : ~ False => @lem309806 A y lt2 P x' h1 h2). Qed.
Lemma lem309809 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem309810 : term190 = False.
Proof. exact (@lem309809 False). Qed.
Lemma lem309811 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (x' : A) (h1 : term325 A lt2 P y) (h2 : term245 A lt2 P x') : False.
Proof. exact (EQ_MP (@lem309810) (@lem309807 A y lt2 P x' h1 h2)). Qed.
Lemma lem309813 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem309814 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term187 A P x.
Proof. exact (fun h0 : term11 A P x => @lem309813 A P x h1). Qed.
Lemma lem309816 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem309817 {A : Type'} (P : A -> Prop) (x : A) : (term187 A P x) = (P x).
Proof. exact (@lem309816 (P x)). Qed.
Lemma lem309818 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem309817 A P x) (@lem309814 A P x h1)). Qed.
Lemma lem309821 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem309823 {A : Type'} (P : A -> Prop) (_6796 : A) : (term11 A P _6796) = (term189 A P _6796).
Proof. exact (@lem309821 (P _6796)). Qed.
Lemma lem309826 {A : Type'} (_6796 : A) (P : A -> Prop) (h1 : term60 A P) : term189 A P _6796.
Proof. exact (EQ_MP (@lem309823 A P _6796) (@lem309658 A _6796 P h1)). Qed.
Lemma lem309827 {A : Type'} (_6796 : A) (P : A -> Prop) (h1 : term60 A P) : term189 A P _6796.
Proof. exact (@lem309826 A _6796 P h1). Qed.
Lemma lem309828 {A : Type'} (x : A) (P : A -> Prop) (h1 : term60 A P) : term189 A P x.
Proof. exact (@lem309827 A x P h1). Qed.
Lemma lem309831 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : False.
Proof. exact (@lem309828 A x P h1 (@lem309818 A P x h2)). Qed.
Lemma lem309832 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : term190.
Proof. exact (fun h0 : ~ False => @lem309831 A P x h1 h2). Qed.
Lemma lem309834 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem309835 : term190 = False.
Proof. exact (@lem309834 False). Qed.
Lemma lem309836 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem309835) (@lem309832 A P x h1 h2)). Qed.
Lemma lem309837 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem309836 A P x h1 h2) (fun h3 : False => @lem309656 A P x h2)). Qed.
Lemma lem309838 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem309837 A P x h1 h2) (@lem309656 A P x h2)). Qed.
Lemma lem309839 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem309838 A P x h1 h2) (fun h3 : False => @lem309609 A P x h2)). Qed.
Lemma lem309840 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem309839 A P x h1 h2) (@lem309609 A P x h2)). Qed.
Lemma lem309841 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : (term60 A P) = False.
Proof. exact (prop_ext (fun h3 : term60 A P => @lem309840 A P x h1 h2) (fun h3 : False => @lem309616 A P h1)). Qed.
Lemma lem309842 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem309841 A P x h1 h2) (@lem309616 A P h1)). Qed.
Lemma lem309843 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : (P x) = False.
Proof. exact (prop_ext (fun h3 : P x => @lem309842 A P x h1 h2) (fun h3 : False => @lem309609 A P x h2)). Qed.
Lemma lem309844 {A : Type'} (P : A -> Prop) (x : A) (h1 : term60 A P) (h2 : P x) : False.
Proof. exact (EQ_MP (@lem309843 A P x h1 h2) (@lem309609 A P x h2)). Qed.
Lemma lem309845 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term325 A lt2 P y) (h2 : P x) (h3 : term269 A lt2 x' P) : False.
Proof. exact (or_elim (@lem309534 A lt2 x' P h3) (fun h0 : term245 A lt2 P x' => @lem309811 A y lt2 P x' h1 h0) (fun h0 : term60 A P => @lem309844 A P x h0 h2)). Qed.
Lemma lem309846 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term325 A lt2 P y) (h2 : P x) (h3 : term269 A lt2 x' P) : (term269 A lt2 x' P) = False.
Proof. exact (prop_ext (fun h4 : term269 A lt2 x' P => @lem309845 A y x lt2 x' P h1 h2 h3) (fun h4 : False => @lem309534 A lt2 x' P h3)). Qed.
Lemma lem309847 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term325 A lt2 P y) (h2 : P x) (h3 : term269 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem309846 A y x lt2 x' P h1 h2 h3) (@lem309534 A lt2 x' P h3)). Qed.
Lemma lem309848 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term325 A lt2 P y) (h2 : P x) (h3 : term269 A lt2 x' P) : (P x) = False.
Proof. exact (prop_ext (fun h4 : P x => @lem309847 A y x lt2 x' P h1 h2 h3) (fun h4 : False => @lem309498 A P x h2)). Qed.
Lemma lem309849 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term325 A lt2 P y) (h2 : P x) (h3 : term269 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem309848 A y x lt2 x' P h1 h2 h3) (@lem309498 A P x h2)). Qed.
Lemma lem309850 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term325 A lt2 P y) (h2 : P x) (h3 : term269 A lt2 x' P) : (term325 A lt2 P y) = False.
Proof. exact (prop_ext (fun h4 : term325 A lt2 P y => @lem309849 A y x lt2 x' P h1 h2 h3) (fun h4 : False => @lem309494 A lt2 P y h1)). Qed.
Lemma lem309851 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (x' : A) (P : A -> Prop) (h1 : term325 A lt2 P y) (h2 : P x) (h3 : term269 A lt2 x' P) : False.
Proof. exact (EQ_MP (@lem309850 A y x lt2 x' P h1 h2 h3) (@lem309494 A lt2 P y h1)). Qed.
Lemma lem309852 {A : Type'} (y : A -> A) (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term325 A lt2 P y) (h2 : P x) (h3 : term61 A lt2 P) : False.
Proof. exact (ex_elim (@lem309278 A lt2 P h3) (fun x' : A => fun h0 : term271 A lt2 P x' => @lem309851 A y x lt2 x' P h1 h2 h0)). Qed.
Lemma lem309853 {A : Type'} (y : A -> A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term325 A lt2 P y) (h2 : term235 A P) (h3 : term61 A lt2 P) : False.
Proof. exact (ex_elim (@lem309291 A P h2) (fun x : A => fun h0 : term82 A P x => @lem309852 A y x lt2 P h1 h0 h3)). Qed.
Lemma lem309854 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term235 A P) (h2 : term238 A lt2 P) (h3 : term61 A lt2 P) : False.
Proof. exact (ex_elim (@lem309464 A lt2 P h2) (fun y : A -> A => fun h0 : term327 A lt2 P y => @lem309853 A y lt2 P h0 h1 h3)). Qed.
Lemma lem309855 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term235 A P) (h2 : term238 A lt2 P) (h3 : term61 A lt2 P) : (term235 A P) = False.
Proof. exact (prop_ext (fun h4 : term235 A P => @lem309854 A lt2 P h1 h2 h3) (fun h4 : False => @lem309291 A P h1)). Qed.
Lemma lem309856 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term235 A P) (h2 : term238 A lt2 P) (h3 : term61 A lt2 P) : False.
Proof. exact (EQ_MP (@lem309855 A lt2 P h1 h2 h3) (@lem309291 A P h1)). Qed.
Lemma lem309857 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term235 A P) (h2 : term238 A lt2 P) (h3 : term61 A lt2 P) : (term238 A lt2 P) = False.
Proof. exact (prop_ext (fun h4 : term238 A lt2 P => @lem309856 A lt2 P h1 h2 h3) (fun h4 : False => @lem309129 A lt2 P h2)). Qed.
Lemma lem309858 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term235 A P) (h2 : term238 A lt2 P) (h3 : term61 A lt2 P) : False.
Proof. exact (EQ_MP (@lem309857 A lt2 P h1 h2 h3) (@lem309129 A lt2 P h2)). Qed.
Lemma lem309859 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term235 A P) (h2 : term61 A lt2 P) : term237 A lt2 P.
Proof. exact (fun h0 : term238 A lt2 P => @lem309858 A lt2 P h1 h0 h2). Qed.
Lemma lem309860 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term235 A P) (h2 : term61 A lt2 P) : term234 A lt2 P.
Proof. exact (EQ_MP (@lem309128 A lt2 P) (@lem309859 A lt2 P h1 h2)). Qed.
Lemma lem309861 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term61 A lt2 P) : term64 A lt2 P.
Proof. exact (fun h0 : term235 A P => @lem309860 A lt2 P h0 h1). Qed.
Lemma lem309862 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term66 A lt2 P.
Proof. exact (fun h0 : term61 A lt2 P => @lem309861 A lt2 P h0). Qed.
Lemma lem309867 {A : Type'} (P : A -> Prop) : term226 A P.
Proof. exact (fun lt2 : type1402 A => @lem309862 A lt2 P). Qed.
Lemma lem309872 {A : Type'} : term230 A.
Proof. exact (fun P : A -> Prop => @lem309867 A P). Qed.
Lemma lem309873 {A : Type'} : term229 A.
Proof. exact (EQ_MP (@lem309122 A) (@lem309872 A)). Qed.
Lemma lem309874 {A : Type'} (P : A -> Prop) : term354 A P.
Proof. exact (@lem309873 A P). Qed.
Lemma lem309875 {A : Type'} (P : A -> Prop) : (term354 A P) = (term225 A P).
Proof. exact (eq_refl (term354 A P)). Qed.
Lemma lem309876 {A : Type'} (P : A -> Prop) : term225 A P.
Proof. exact (EQ_MP (@lem309875 A P) (@lem309874 A P)). Qed.
Lemma lem309877 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term355 A P lt2.
Proof. exact (@lem309876 A P lt2). Qed.
Lemma lem309878 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term355 A P lt2) = (term217 A lt2 P).
Proof. exact (eq_refl (term355 A P lt2)). Qed.
Lemma lem309879 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term217 A lt2 P.
Proof. exact (EQ_MP (@lem309878 A lt2 P) (@lem309877 A P lt2)). Qed.
Lemma lem309881 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term217 A lt2 P.
Proof. exact (@lem308900 A lt2 P (@lem309879 A lt2 P)). Qed.
Lemma lem309882 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term218 A lt2 P) : False.
Proof. exact (@lem309881 A lt2 P (@lem308884 A lt2 P h1)). Qed.
Lemma lem309883 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term218 A lt2 P) : (term218 A lt2 P) = False.
Proof. exact (prop_ext (fun h2 : term218 A lt2 P => @lem309882 A lt2 P h1) (fun h2 : False => @lem308884 A lt2 P h1)). Qed.
Lemma lem309884 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term218 A lt2 P) : False.
Proof. exact (EQ_MP (@lem309883 A lt2 P h1) (@lem308884 A lt2 P h1)). Qed.
Lemma lem309885 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term217 A lt2 P.
Proof. exact (fun h0 : term218 A lt2 P => @lem309884 A lt2 P h0). Qed.
Lemma lem309886 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term66 A lt2 P.
Proof. exact (EQ_MP (@lem308883 A lt2 P) (@lem309885 A lt2 P)). Qed.
Lemma lem309887 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term65 A lt2 P.
Proof. exact (EQ_MP (@lem307864 A lt2 P) (@lem309886 A lt2 P)). Qed.
Lemma lem309888 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term41 A lt2 P.
Proof. exact (EQ_MP (@lem307745 A lt2 P) (@lem308879 A lt2 P)). Qed.
Lemma lem309889 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term1 A lt2) : term64 A lt2 P.
Proof. exact (@lem309887 A lt2 P (@lem307620 A P lt2 h1)). Qed.
Lemma lem309890 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term0 A lt2) : term40 A lt2 P.
Proof. exact (@lem309888 A lt2 P (@lem307617 A P lt2 h1)). Qed.
Lemma lem309895 {A : Type'} (lt2 : type1402 A) (h1 : term1 A lt2) : term0 A lt2.
Proof. exact (fun P : A -> Prop => @lem309889 A P lt2 h1). Qed.
Lemma lem309900 {A : Type'} (lt2 : type1402 A) (h1 : term0 A lt2) : term1 A lt2.
Proof. exact (fun P : A -> Prop => @lem309890 A P lt2 h1). Qed.
Lemma lem309901 {A : Type'} (lt2 : type1402 A) : term356 A lt2.
Proof. exact (fun h0 : term1 A lt2 => @lem309895 A lt2 h0). Qed.
Lemma lem309902 {A : Type'} (lt2 : type1402 A) : term357 A lt2.
Proof. exact (fun h0 : term0 A lt2 => @lem309900 A lt2 h0). Qed.
Lemma lem309903 {A : Type'} (lt2 : type1402 A) : term358 A lt2.
Proof. exact (conj (@lem309902 A lt2) (@lem309901 A lt2)). Qed.
Lemma lem309904 {A : Type'} (lt2 : type1402 A) : (term358 A lt2) = ((term0 A lt2) = (term1 A lt2)).
Proof. exact (@lem32 (term0 A lt2) (term1 A lt2)). Qed.
Lemma lem309905 {A : Type'} (lt2 : type1402 A) : (term0 A lt2) = (term1 A lt2).
Proof. exact (EQ_MP (@lem309904 A lt2) (@lem309903 A lt2)). Qed.
