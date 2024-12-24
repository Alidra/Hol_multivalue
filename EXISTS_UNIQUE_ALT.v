Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_UNIQUE_ALT_term_abbrevs.
Require Import EXISTS_REFL_spec.
Require Import EXISTS_UNIQUE_THM_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem7664 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem7665 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem7664 A x a h1)). Qed.
Lemma lem7666 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem7667 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem7666 A a x h1)). Qed.
Lemma lem7668 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem7665 A x a h1) (fun h1 : a = x => @lem7667 A a x h1)). Qed.
Lemma lem7669 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem7668 A a x)). Qed.
Lemma lem7670 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7671 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem7670 A) (@lem7669 A a)). Qed.
Lemma lem7672 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem7671 A a)). Qed.
Lemma lem7673 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7674 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem7673 A) (@lem7672 A)). Qed.
Lemma lem7675 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem7674 A) (@lem4363 A)). Qed.
Lemma lem7676 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (@lem4356 A P). Qed.
Lemma lem7677 {A : Type'} (P : A -> Prop) : (term8 A P) = ((term9 A P) = (term10 A P)).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem7682 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (EQ_MP (@lem7677 A P) (@lem7676 A P)). Qed.
Lemma lem7683 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (@lem7682 A P). Qed.
Lemma lem7704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7705 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem7704) (@lem7683 A P)). Qed.
Lemma lem7718 {A : Type'} (P : A -> Prop) : (term13 A P) = (term13 A P).
Proof. exact (eq_refl (term13 A P)). Qed.
Lemma lem7719 {A : Type'} (P : A -> Prop) : ((term9 A P) = (term13 A P)) = ((term10 A P) = (term13 A P)).
Proof. exact (MK_COMB (@lem7705 A P) (@lem7718 A P)). Qed.
Lemma lem7722 {A : Type'} (P : A -> Prop) : ((term10 A P) = (term13 A P)) = ((term9 A P) = (term13 A P)).
Proof. exact (SYM (@lem7719 A P)). Qed.
Lemma lem7723 {A : Type'} (P : A -> Prop) (h1 : term10 A P) : term10 A P.
Proof. exact (h1). Qed.
Lemma lem7724 {A : Type'} (P : A -> Prop) (h1 : term14 A P) : term14 A P.
Proof. exact (h1). Qed.
Lemma lem7725 {A : Type'} (P : A -> Prop) (h1 : term15 A P) : term15 A P.
Proof. exact (h1). Qed.
Lemma lem7726 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem7727 {A : Type'} (P : A -> Prop) (y : A) (h1 : P y) : P y.
Proof. exact (h1). Qed.
Lemma lem7728 {A : Type'} (P : A -> Prop) (h1 : term14 A P) : term14 A P.
Proof. exact (h1). Qed.
Lemma lem7729 {A : Type'} (x : A) (P : A -> Prop) (h1 : term14 A P) : term16 A P x.
Proof. exact (@lem7728 A P h1 x). Qed.
Lemma lem7730 {A : Type'} (P : A -> Prop) (x : A) : (term16 A P x) = (term17 A P x).
Proof. exact (eq_refl (term16 A P x)). Qed.
Lemma lem7731 {A : Type'} (x : A) (P : A -> Prop) (h1 : term14 A P) : term17 A P x.
Proof. exact (EQ_MP (@lem7730 A P x) (@lem7729 A x P h1)). Qed.
Lemma lem7732 {A : Type'} (x : A) (x' : A) (P : A -> Prop) (h1 : term14 A P) : term18 A P x x'.
Proof. exact (@lem7731 A x P h1 x'). Qed.
Lemma lem7733 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term18 A P x x') = (term19 A P x x').
Proof. exact (eq_refl (term18 A P x x')). Qed.
Lemma lem7734 {A : Type'} (x : A) (x' : A) (P : A -> Prop) (h1 : term14 A P) : term19 A P x x'.
Proof. exact (EQ_MP (@lem7733 A P x x') (@lem7732 A x x' P h1)). Qed.
Lemma lem7735 {A : Type'} (x : A) (P : A -> Prop) (x' : A) (h1 : term20 A x P x') : term20 A x P x'.
Proof. exact (h1). Qed.
Lemma lem7736 {A : Type'} (x : A) (P : A -> Prop) (x' : A) (h1 : term14 A P) (h2 : term20 A x P x') : x = x'.
Proof. exact (@lem7734 A x x' P h1 (@lem7735 A x P x' h2)). Qed.
Lemma lem7737 {A : Type'} (x : A) (P : A -> Prop) (x' : A) (h1 : term20 A x P x') : term21 A P x x'.
Proof. exact (fun h0 : term14 A P => @lem7736 A x P x' h0 h1). Qed.
Lemma lem7738 {A : Type'} (P : A -> Prop) (h1 : term14 A P) : term14 A P.
Proof. exact (h1). Qed.
Lemma lem7739 {A : Type'} (x : A) (P : A -> Prop) (x' : A) (h1 : term14 A P) (h2 : term20 A x P x') : x = x'.
Proof. exact (@lem7737 A x P x' h2 (@lem7738 A P h1)). Qed.
Lemma lem7740 {A : Type'} (x : A) (x' : A) (P : A -> Prop) (h1 : term14 A P) : term19 A P x x'.
Proof. exact (fun h0 : term20 A x P x' => @lem7739 A x P x' h1 h0). Qed.
Lemma lem7741 {A : Type'} (x : A) (P : A -> Prop) (h1 : term14 A P) : term17 A P x.
Proof. exact (fun x' : A => @lem7740 A x x' P h1). Qed.
Lemma lem7742 {A : Type'} (P : A -> Prop) (h1 : term14 A P) : term14 A P.
Proof. exact (fun x : A => @lem7741 A x P h1). Qed.
Lemma lem7743 {A : Type'} (P : A -> Prop) : term22 A P.
Proof. exact (fun h0 : term14 A P => @lem7742 A P h0). Qed.
Lemma lem7744 {A : Type'} (P : A -> Prop) (h1 : term14 A P) : term14 A P.
Proof. exact (@lem7743 A P (@lem7724 A P h1)). Qed.
Lemma lem7745 {A : Type'} (x : A) (P : A -> Prop) (h1 : term14 A P) : term16 A P x.
Proof. exact (@lem7744 A P h1 x). Qed.
Lemma lem7746 {A : Type'} (P : A -> Prop) (x : A) : (term16 A P x) = (term17 A P x).
Proof. exact (eq_refl (term16 A P x)). Qed.
Lemma lem7747 {A : Type'} (x : A) (P : A -> Prop) (h1 : term14 A P) : term17 A P x.
Proof. exact (EQ_MP (@lem7746 A P x) (@lem7745 A x P h1)). Qed.
Lemma lem7748 {A : Type'} (x : A) (x' : A) (P : A -> Prop) (h1 : term14 A P) : term18 A P x x'.
Proof. exact (@lem7747 A x P h1 x'). Qed.
Lemma lem7749 {A : Type'} (P : A -> Prop) (x : A) (x' : A) : (term18 A P x x') = (term19 A P x x').
Proof. exact (eq_refl (term18 A P x x')). Qed.
Lemma lem7752 {A : Type'} (x : A) (x' : A) (P : A -> Prop) (h1 : term14 A P) : term19 A P x x'.
Proof. exact (EQ_MP (@lem7749 A P x x') (@lem7748 A x x' P h1)). Qed.
Lemma lem7753 {A : Type'} (x : A) (x' : A) (P : A -> Prop) (h1 : term14 A P) : term19 A P x x'.
Proof. exact (@lem7752 A x x' P h1). Qed.
Lemma lem7754 {A : Type'} (x : A) (y : A) (P : A -> Prop) (h1 : term14 A P) : term19 A P x y.
Proof. exact (@lem7753 A x y P h1). Qed.
Lemma lem7755 {A : Type'} (P : A -> Prop) (x : A) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem7765 {A : Type'} (P : A -> Prop) (y : A) : (P y) = ((P y) = True).
Proof. exact (@lem7 (P y)). Qed.
Lemma lem7770 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem7755 A P x) (@lem7726 A P x h1)). Qed.
Lemma lem7771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7772 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : (term23 A P x) = (and True).
Proof. exact (MK_COMB (@lem7771) (@lem7770 A P x h1)). Qed.
Lemma lem7774 {A : Type'} (P : A -> Prop) (y : A) (h1 : P y) : (P y) = True.
Proof. exact (EQ_MP (@lem7765 A P y) (@lem7727 A P y h1)). Qed.
Lemma lem7775 {A : Type'} (x : A) (P : A -> Prop) (y : A) (h1 : P x) (h2 : P y) : (term20 A x P y) = (True /\ True).
Proof. exact (MK_COMB (@lem7772 A P x h1) (@lem7774 A P y h2)). Qed.
Lemma lem7777 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7778 : (True /\ True) = True.
Proof. exact (@lem7777 True). Qed.
Lemma lem7779 {A : Type'} (x : A) (P : A -> Prop) (y : A) (h1 : P x) (h2 : P y) : (term20 A x P y) = True.
Proof. exact (TRANS (@lem7775 A x P y h1 h2) (@lem7778)). Qed.
Lemma lem7780 {A : Type'} (x : A) (P : A -> Prop) (y : A) (h1 : P x) (h2 : P y) : True = (term20 A x P y).
Proof. exact (SYM (@lem7779 A x P y h1 h2)). Qed.
Lemma lem7781 {A : Type'} (x : A) (P : A -> Prop) (y : A) (h1 : P x) (h2 : P y) : term20 A x P y.
Proof. exact (EQ_MP (@lem7780 A x P y h1 h2) (@lem0)). Qed.
Lemma lem7782 {A : Type'} (x : A) (P : A -> Prop) (y : A) (h1 : term14 A P) (h2 : P x) (h3 : P y) : x = y.
Proof. exact (@lem7754 A x y P h1 (@lem7781 A x P y h2 h3)). Qed.
Lemma lem7783 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term14 A P) (h2 : P x) : term24 A P x y.
Proof. exact (fun h0 : P y => @lem7782 A x P y h1 h2 h0). Qed.
Lemma lem7784 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem7785 {A : Type'} (x : A) (y : A) (h1 : x = y) : y = x.
Proof. exact (SYM (@lem7784 A x y h1)). Qed.
Lemma lem7786 {A : Type'} (P : A -> Prop) : (term25 A P) = (term25 A P).
Proof. exact (eq_refl (term25 A P)). Qed.
Lemma lem7787 {A : Type'} (P : A -> Prop) (x : A) (y : A) (h1 : x = y) : (term26 A P y) = (term26 A P x).
Proof. exact (MK_COMB (@lem7786 A P) (@lem7785 A x y h1)). Qed.
Lemma lem7788 {A : Type'} (P : A -> Prop) (x : A) : (term26 A P x) = (P x).
Proof. exact (eq_refl (term26 A P x)). Qed.
Lemma lem7789 {A : Type'} (P : A -> Prop) (y : A) : (term27 A P y) = (term27 A P y).
Proof. exact (eq_refl (term27 A P y)). Qed.
Lemma lem7790 {A : Type'} (y : A) (P : A -> Prop) (x : A) : ((term26 A P y) = (term26 A P x)) = ((term26 A P y) = (P x)).
Proof. exact (MK_COMB (@lem7789 A P y) (@lem7788 A P x)). Qed.
Lemma lem7791 {A : Type'} (P : A -> Prop) (y : A) : (term26 A P y) = (P y).
Proof. exact (eq_refl (term26 A P y)). Qed.
Lemma lem7792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7793 {A : Type'} (P : A -> Prop) (y : A) : (term27 A P y) = (term28 A P y).
Proof. exact (MK_COMB (@lem7792) (@lem7791 A P y)). Qed.
Lemma lem7794 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem7795 {A : Type'} (y : A) (P : A -> Prop) (x : A) : ((term26 A P y) = (P x)) = ((P y) = (P x)).
Proof. exact (MK_COMB (@lem7793 A P y) (@lem7794 A P x)). Qed.
Lemma lem7796 {A : Type'} (y : A) (P : A -> Prop) (x : A) : ((term26 A P y) = (term26 A P x)) = ((P y) = (P x)).
Proof. exact (TRANS (@lem7790 A y P x) (@lem7795 A y P x)). Qed.
Lemma lem7797 {A : Type'} (P : A -> Prop) (x : A) (y : A) (h1 : x = y) : (P y) = (P x).
Proof. exact (EQ_MP (@lem7796 A y P x) (@lem7787 A P x y h1)). Qed.
Lemma lem7798 {A : Type'} (P : A -> Prop) (x : A) (y : A) (h1 : x = y) : (P x) = (P y).
Proof. exact (SYM (@lem7797 A P x y h1)). Qed.
Lemma lem7808 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem7809 {A : Type'} (P : A -> Prop) (x : A) (y : A) (h1 : P x) (h2 : x = y) : P y.
Proof. exact (EQ_MP (@lem7798 A P x y h2) (@lem7808 A P x h1)). Qed.
Lemma lem7810 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : P x) : term29 A x P y.
Proof. exact (fun h0 : x = y => @lem7809 A P x y h1 h0). Qed.
Lemma lem7811 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term14 A P) (h2 : P x) : term30 A x P y.
Proof. exact (conj (@lem7783 A y P x h1 h2) (@lem7810 A y P x h2)). Qed.
Lemma lem7812 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term30 A x P y) = ((P y) = (x = y)).
Proof. exact (@lem32 (P y) (x = y)). Qed.
Lemma lem7813 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term14 A P) (h2 : P x) : (P y) = (x = y).
Proof. exact (EQ_MP (@lem7812 A P x y) (@lem7811 A y P x h1 h2)). Qed.
Lemma lem7818 {A : Type'} (P : A -> Prop) (x : A) (h1 : term14 A P) (h2 : P x) : term31 A P x.
Proof. exact (fun y : A => @lem7813 A y P x h1 h2). Qed.
Lemma lem7819 {A : Type'} (P : A -> Prop) (x : A) (h1 : term14 A P) (h2 : P x) : term13 A P.
Proof. exact (ex_intro (term32 A P) x (@lem7818 A P x h1 h2)). Qed.
Lemma lem7820 {A : Type'} (P : A -> Prop) (h1 : term10 A P) : term14 A P.
Proof. exact (proj2 (@lem7723 A P h1)). Qed.
Lemma lem7821 {A : Type'} (P : A -> Prop) (h1 : term10 A P) : term15 A P.
Proof. exact (proj1 (@lem7723 A P h1)). Qed.
Lemma lem7822 {A : Type'} (P : A -> Prop) (x : A) (h1 : term14 A P) (h2 : P x) : (term14 A P) = (term13 A P).
Proof. exact (prop_ext (fun h3 : term14 A P => @lem7819 A P x h1 h2) (fun h3 : term13 A P => @lem7724 A P h1)). Qed.
Lemma lem7823 {A : Type'} (P : A -> Prop) (x : A) (h1 : term14 A P) (h2 : P x) : term13 A P.
Proof. exact (EQ_MP (@lem7822 A P x h1 h2) (@lem7724 A P h1)). Qed.
Lemma lem7824 {A : Type'} (P : A -> Prop) (h1 : term14 A P) (h2 : term15 A P) : term13 A P.
Proof. exact (ex_elim (@lem7725 A P h2) (fun x : A => fun h0 : term25 A P x => @lem7823 A P x h1 h0)). Qed.
Lemma lem7825 {A : Type'} (P : A -> Prop) (h1 : term15 A P) (h2 : term10 A P) : (term14 A P) = (term13 A P).
Proof. exact (prop_ext (fun h3 : term14 A P => @lem7824 A P h3 h1) (fun h3 : term13 A P => @lem7820 A P h2)). Qed.
Lemma lem7826 {A : Type'} (P : A -> Prop) (h1 : term15 A P) (h2 : term10 A P) : term13 A P.
Proof. exact (EQ_MP (@lem7825 A P h1 h2) (@lem7820 A P h2)). Qed.
Lemma lem7827 {A : Type'} (P : A -> Prop) (h1 : term10 A P) : (term15 A P) = (term13 A P).
Proof. exact (prop_ext (fun h2 : term15 A P => @lem7826 A P h2 h1) (fun h2 : term13 A P => @lem7821 A P h1)). Qed.
Lemma lem7828 {A : Type'} (P : A -> Prop) (h1 : term10 A P) : term13 A P.
Proof. exact (EQ_MP (@lem7827 A P h1) (@lem7821 A P h1)). Qed.
Lemma lem7829 {A : Type'} (P : A -> Prop) : term33 A P.
Proof. exact (fun h0 : term10 A P => @lem7828 A P h0). Qed.
Lemma lem7830 {A : Type'} (P : A -> Prop) (h1 : term13 A P) : term13 A P.
Proof. exact (h1). Qed.
Lemma lem7831 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : term31 A P x.
Proof. exact (h1). Qed.
Lemma lem7832 {A : Type'} (a : A) : term34 A a.
Proof. exact (@lem7675 A a). Qed.
Lemma lem7833 {A : Type'} (a : A) : (term34 A a) = (term3 A a).
Proof. exact (eq_refl (term34 A a)). Qed.
Lemma lem7834 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem7833 A a) (@lem7832 A a)). Qed.
Lemma lem7835 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem7837 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : term35 A P x y.
Proof. exact (@lem7831 A P x h1 y). Qed.
Lemma lem7838 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term35 A P x y) = ((P y) = (x = y)).
Proof. exact (eq_refl (term35 A P x y)). Qed.
Lemma lem7855 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (P y) = (x = y).
Proof. exact (EQ_MP (@lem7838 A P x y) (@lem7837 A y P x h1)). Qed.
Lemma lem7856 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (P y) = (x = y).
Proof. exact (@lem7855 A y P x h1). Qed.
Lemma lem7857 {A : Type'} (_377 : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (P _377) = (x = _377).
Proof. exact (@lem7856 A _377 P x h1). Qed.
Lemma lem7862 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term25 A P) = (term1 A x).
Proof. exact (fun_ext (fun _377 : A => @lem7857 A _377 P x h1)). Qed.
Lemma lem7863 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7864 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term15 A P) = (term3 A x).
Proof. exact (MK_COMB (@lem7863 A) (@lem7862 A P x h1)). Qed.
Lemma lem7866 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem7835 A a) (@lem7834 A a)). Qed.
Lemma lem7867 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (@lem7866 A a). Qed.
Lemma lem7868 {A : Type'} (x : A) : (term3 A x) = True.
Proof. exact (@lem7867 A x). Qed.
Lemma lem7869 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term15 A P) = True.
Proof. exact (TRANS (@lem7864 A P x h1) (@lem7868 A x)). Qed.
Lemma lem7870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7871 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term36 A P) = (and True).
Proof. exact (MK_COMB (@lem7870) (@lem7869 A P x h1)). Qed.
Lemma lem7936 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (P y) = (x = y).
Proof. exact (EQ_MP (@lem7838 A P x y) (@lem7837 A y P x h1)). Qed.
Lemma lem7937 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (P y) = (x = y).
Proof. exact (@lem7936 A y P x h1). Qed.
Lemma lem7938 {A : Type'} (_378 : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (P _378) = (x = _378).
Proof. exact (@lem7937 A _378 P x h1). Qed.
Lemma lem7941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7942 {A : Type'} (_378 : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term23 A P _378) = (term37 A x _378).
Proof. exact (MK_COMB (@lem7941) (@lem7938 A _378 P x h1)). Qed.
Lemma lem7944 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (P y) = (x = y).
Proof. exact (EQ_MP (@lem7838 A P x y) (@lem7837 A y P x h1)). Qed.
Lemma lem7945 {A : Type'} (y : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (P y) = (x = y).
Proof. exact (@lem7944 A y P x h1). Qed.
Lemma lem7946 {A : Type'} (x' : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (P x') = (x = x').
Proof. exact (@lem7945 A x' P x h1). Qed.
Lemma lem7949 {A : Type'} (_378 : A) (x' : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term20 A _378 P x') = (term38 A _378 x x').
Proof. exact (MK_COMB (@lem7942 A _378 P x h1) (@lem7946 A x' P x h1)). Qed.
Lemma lem7952 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7953 {A : Type'} (_378 : A) (x' : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term39 A _378 P x') = (term40 A _378 x x').
Proof. exact (MK_COMB (@lem7952) (@lem7949 A _378 x' P x h1)). Qed.
Lemma lem7956 {A : Type'} (_378 : A) (x' : A) : (_378 = x') = (_378 = x').
Proof. exact (eq_refl (_378 = x')). Qed.
Lemma lem7957 {A : Type'} (_378 : A) (x' : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term19 A P _378 x') = (term41 A x _378 x').
Proof. exact (MK_COMB (@lem7953 A _378 x' P x h1) (@lem7956 A _378 x')). Qed.
Lemma lem7960 {A : Type'} (_378 : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term42 A P _378) = (term43 A x _378).
Proof. exact (fun_ext (fun x' : A => @lem7957 A _378 x' P x h1)). Qed.
Lemma lem7961 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7962 {A : Type'} (_378 : A) (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term17 A P _378) = (term44 A x _378).
Proof. exact (MK_COMB (@lem7961 A) (@lem7960 A _378 P x h1)). Qed.
Lemma lem7969 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term45 A P) = (term46 A x).
Proof. exact (fun_ext (fun _378 : A => @lem7962 A _378 P x h1)). Qed.
Lemma lem7970 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7971 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term14 A P) = (term47 A x).
Proof. exact (MK_COMB (@lem7970 A) (@lem7969 A P x h1)). Qed.
Lemma lem7976 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term10 A P) = (term48 A x).
Proof. exact (MK_COMB (@lem7871 A P x h1) (@lem7971 A P x h1)). Qed.
Lemma lem7978 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7979 {A : Type'} (x : A) : (term48 A x) = (term47 A x).
Proof. exact (@lem7978 (term47 A x)). Qed.
Lemma lem7998 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term10 A P) = (term47 A x).
Proof. exact (TRANS (@lem7976 A P x h1) (@lem7979 A x)). Qed.
Lemma lem7999 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : (term47 A x) = (term10 A P).
Proof. exact (SYM (@lem7998 A P x h1)). Qed.
Lemma lem8000 {A : Type'} (x' : A) (x : A) (x'' : A) (h1 : term38 A x' x x'') : term38 A x' x x''.
Proof. exact (h1). Qed.
Lemma lem8001 {A : Type'} (x : A) (x'' : A) (h1 : x = x'') : x = x''.
Proof. exact (h1). Qed.
Lemma lem8002 {A : Type'} (x : A) (x'' : A) (h1 : x = x'') : x'' = x.
Proof. exact (SYM (@lem8001 A x x'' h1)). Qed.
Lemma lem8003 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x = x'.
Proof. exact (h1). Qed.
Lemma lem8004 {A : Type'} (x : A) (x' : A) (h1 : x = x') : x' = x.
Proof. exact (SYM (@lem8003 A x x' h1)). Qed.
Lemma lem8005 {A : Type'} (x'' : A) : (term0 A x'') = (term0 A x'').
Proof. exact (eq_refl (term0 A x'')). Qed.
Lemma lem8006 {A : Type'} (x'' : A) (x : A) (x' : A) (h1 : x = x') : (term49 A x'' x') = (term49 A x'' x).
Proof. exact (MK_COMB (@lem8005 A x'') (@lem8004 A x x' h1)). Qed.
Lemma lem8007 {A : Type'} (x : A) (x'' : A) : (term49 A x'' x) = (x = x'').
Proof. exact (eq_refl (term49 A x'' x)). Qed.
Lemma lem8008 {A : Type'} (x'' : A) (x' : A) : (term50 A x'' x') = (term50 A x'' x').
Proof. exact (eq_refl (term50 A x'' x')). Qed.
Lemma lem8009 {A : Type'} (x' : A) (x : A) (x'' : A) : ((term49 A x'' x') = (term49 A x'' x)) = ((term49 A x'' x') = (x = x'')).
Proof. exact (MK_COMB (@lem8008 A x'' x') (@lem8007 A x x'')). Qed.
Lemma lem8010 {A : Type'} (x' : A) (x'' : A) : (term49 A x'' x') = (x' = x'').
Proof. exact (eq_refl (term49 A x'' x')). Qed.
Lemma lem8011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8012 {A : Type'} (x' : A) (x'' : A) : (term50 A x'' x') = (term51 A x' x'').
Proof. exact (MK_COMB (@lem8011) (@lem8010 A x' x'')). Qed.
Lemma lem8013 {A : Type'} (x : A) (x'' : A) : (x = x'') = (x = x'').
Proof. exact (eq_refl (x = x'')). Qed.
Lemma lem8014 {A : Type'} (x' : A) (x : A) (x'' : A) : ((term49 A x'' x') = (x = x'')) = ((x' = x'') = (x = x'')).
Proof. exact (MK_COMB (@lem8012 A x' x'') (@lem8013 A x x'')). Qed.
Lemma lem8015 {A : Type'} (x' : A) (x : A) (x'' : A) : ((term49 A x'' x') = (term49 A x'' x)) = ((x' = x'') = (x = x'')).
Proof. exact (TRANS (@lem8009 A x' x x'') (@lem8014 A x' x x'')). Qed.
Lemma lem8016 {A : Type'} (x'' : A) (x : A) (x' : A) (h1 : x = x') : (x' = x'') = (x = x'').
Proof. exact (EQ_MP (@lem8015 A x' x x'') (@lem8006 A x'' x x' h1)). Qed.
Lemma lem8017 {A : Type'} (x'' : A) (x : A) (x' : A) (h1 : x = x') : (x = x'') = (x' = x'').
Proof. exact (SYM (@lem8016 A x'' x x' h1)). Qed.
Lemma lem8018 {A : Type'} (x : A) : (term1 A x) = (term1 A x).
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem8019 {A : Type'} (x : A) (x'' : A) (h1 : x = x'') : (term52 A x x'') = (term53 A x).
Proof. exact (MK_COMB (@lem8018 A x) (@lem8002 A x x'' h1)). Qed.
Lemma lem8020 {A : Type'} (x : A) : (term53 A x) = (x = x).
Proof. exact (eq_refl (term53 A x)). Qed.
Lemma lem8021 {A : Type'} (x : A) (x'' : A) : (term54 A x x'') = (term54 A x x'').
Proof. exact (eq_refl (term54 A x x'')). Qed.
Lemma lem8022 {A : Type'} (x'' : A) (x : A) : ((term52 A x x'') = (term53 A x)) = ((term52 A x x'') = (x = x)).
Proof. exact (MK_COMB (@lem8021 A x x'') (@lem8020 A x)). Qed.
Lemma lem8023 {A : Type'} (x : A) (x'' : A) : (term52 A x x'') = (x = x'').
Proof. exact (eq_refl (term52 A x x'')). Qed.
Lemma lem8024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8025 {A : Type'} (x : A) (x'' : A) : (term54 A x x'') = (term51 A x x'').
Proof. exact (MK_COMB (@lem8024) (@lem8023 A x x'')). Qed.
Lemma lem8026 {A : Type'} (x : A) : (x = x) = (x = x).
Proof. exact (eq_refl (x = x)). Qed.
Lemma lem8027 {A : Type'} (x'' : A) (x : A) : ((term52 A x x'') = (x = x)) = ((x = x'') = (x = x)).
Proof. exact (MK_COMB (@lem8025 A x x'') (@lem8026 A x)). Qed.
Lemma lem8028 {A : Type'} (x'' : A) (x : A) : ((term52 A x x'') = (term53 A x)) = ((x = x'') = (x = x)).
Proof. exact (TRANS (@lem8022 A x'' x) (@lem8027 A x'' x)). Qed.
Lemma lem8029 {A : Type'} (x : A) (x'' : A) (h1 : x = x'') : (x = x'') = (x = x).
Proof. exact (EQ_MP (@lem8028 A x'' x) (@lem8019 A x x'' h1)). Qed.
Lemma lem8030 {A : Type'} (x : A) (x'' : A) (h1 : x = x'') : (x = x) = (x = x'').
Proof. exact (SYM (@lem8029 A x x'' h1)). Qed.
Lemma lem8031 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8032 {A : Type'} (x' : A) (x : A) (x'' : A) (h1 : term38 A x' x x'') : x = x''.
Proof. exact (proj2 (@lem8000 A x' x x'' h1)). Qed.
Lemma lem8033 {A : Type'} (x' : A) (x : A) (x'' : A) (h1 : term38 A x' x x'') : x = x'.
Proof. exact (proj1 (@lem8000 A x' x x'' h1)). Qed.
Lemma lem8034 {A : Type'} (x : A) (x'' : A) (h1 : x = x'') : x = x''.
Proof. exact (EQ_MP (@lem8030 A x x'' h1) (@lem8031 A x)). Qed.
Lemma lem8035 {A : Type'} (x' : A) (x : A) (x'' : A) (h1 : x = x') (h2 : x = x'') : x' = x''.
Proof. exact (EQ_MP (@lem8017 A x'' x x' h1) (@lem8034 A x x'' h2)). Qed.
Lemma lem8036 {A : Type'} (x'' : A) (x : A) (x' : A) (h1 : term38 A x' x x'') (h2 : x = x') : (x = x'') = (x' = x'').
Proof. exact (prop_ext (fun h3 : x = x'' => @lem8035 A x' x x'' h2 h3) (fun h3 : x' = x'' => @lem8032 A x' x x'' h1)). Qed.
Lemma lem8037 {A : Type'} (x'' : A) (x : A) (x' : A) (h1 : term38 A x' x x'') (h2 : x = x') : x' = x''.
Proof. exact (EQ_MP (@lem8036 A x'' x x' h1 h2) (@lem8032 A x' x x'' h1)). Qed.
Lemma lem8038 {A : Type'} (x' : A) (x : A) (x'' : A) (h1 : term38 A x' x x'') : (x = x') = (x' = x'').
Proof. exact (prop_ext (fun h2 : x = x' => @lem8037 A x'' x x' h1 h2) (fun h2 : x' = x'' => @lem8033 A x' x x'' h1)). Qed.
Lemma lem8039 {A : Type'} (x' : A) (x : A) (x'' : A) (h1 : term38 A x' x x'') : x' = x''.
Proof. exact (EQ_MP (@lem8038 A x' x x'' h1) (@lem8033 A x' x x'' h1)). Qed.
Lemma lem8040 {A : Type'} (x : A) (x' : A) (x'' : A) : term41 A x x' x''.
Proof. exact (fun h0 : term38 A x' x x'' => @lem8039 A x' x x'' h0). Qed.
Lemma lem8045 {A : Type'} (x : A) (x' : A) : term44 A x x'.
Proof. exact (fun x'' : A => @lem8040 A x x' x''). Qed.
Lemma lem8050 {A : Type'} (x : A) : term47 A x.
Proof. exact (fun x' : A => @lem8045 A x x'). Qed.
Lemma lem8051 {A : Type'} (P : A -> Prop) (x : A) (h1 : term31 A P x) : term10 A P.
Proof. exact (EQ_MP (@lem7999 A P x h1) (@lem8050 A x)). Qed.
Lemma lem8052 {A : Type'} (P : A -> Prop) (h1 : term13 A P) : term10 A P.
Proof. exact (ex_elim (@lem7830 A P h1) (fun x : A => fun h0 : term32 A P x => @lem8051 A P x h0)). Qed.
Lemma lem8053 {A : Type'} (P : A -> Prop) : term55 A P.
Proof. exact (fun h0 : term13 A P => @lem8052 A P h0). Qed.
Lemma lem8054 {A : Type'} (P : A -> Prop) : term56 A P.
Proof. exact (conj (@lem7829 A P) (@lem8053 A P)). Qed.
Lemma lem8055 {A : Type'} (P : A -> Prop) : (term56 A P) = ((term10 A P) = (term13 A P)).
Proof. exact (@lem32 (term10 A P) (term13 A P)). Qed.
Lemma lem8056 {A : Type'} (P : A -> Prop) : (term10 A P) = (term13 A P).
Proof. exact (EQ_MP (@lem8055 A P) (@lem8054 A P)). Qed.
Lemma lem8057 {A : Type'} (P : A -> Prop) : (term9 A P) = (term13 A P).
Proof. exact (EQ_MP (@lem7722 A P) (@lem8056 A P)). Qed.
Lemma lem8062 {A : Type'} : term57 A.
Proof. exact (fun P : A -> Prop => @lem8057 A P). Qed.
