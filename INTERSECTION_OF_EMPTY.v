Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERSECTION_OF_EMPTY_term_abbrevs.
Require Import INTERSECTION_OF_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3354637_spec.
Require Import thm3354697_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4851739 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4842239 A P). Qed.
Lemma lem4851740 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4851741 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4851740 A P) (@lem4851739 A P)). Qed.
Lemma lem4851742 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4851741 A P Q). Qed.
Lemma lem4851743 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@INTERSECTION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4851745 {A : Type'} (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : P (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4851747 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4851743 A P Q) (@lem4851742 A P Q)). Qed.
Lemma lem4851748 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4851747 A P Q). Qed.
Lemma lem4851765 {A : Type'} : (@UNIV A) = (@UNIV A).
Proof. exact (eq_refl (@UNIV A)). Qed.
Lemma lem4851766 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q (@UNIV A)) = (term4 A P Q).
Proof. exact (MK_COMB (@lem4851748 A P Q) (@lem4851765 A)). Qed.
Lemma lem4851768 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4851769 {A : Type'} (f : type686 A) (y : A -> Prop) : (term6 A f y) = (f y).
Proof. exact (@lem4851768 (A -> Prop) Prop f y). Qed.
Lemma lem4851770 {A : Type'} (P : type180 A) (Q : type686 A) : (term7 A P Q) = (term4 A P Q).
Proof. exact (@lem4851769 A (term3 A P Q) (@UNIV A)). Qed.
Lemma lem4851771 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term8 A P Q s) = (term9 A P Q s).
Proof. exact (eq_refl (term8 A P Q s)). Qed.
Lemma lem4851772 {A : Type'} (P : type180 A) (Q : type686 A) : (term10 A P Q) = (term3 A P Q).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4851771 A P Q s)). Qed.
Lemma lem4851773 {A : Type'} : (@UNIV A) = (@UNIV A).
Proof. exact (eq_refl (@UNIV A)). Qed.
Lemma lem4851774 {A : Type'} (P : type180 A) (Q : type686 A) : (term7 A P Q) = (term4 A P Q).
Proof. exact (MK_COMB (@lem4851772 A P Q) (@lem4851773 A)). Qed.
Lemma lem4851775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4851776 {A : Type'} (P : type180 A) (Q : type686 A) : (term11 A P Q) = (term12 A P Q).
Proof. exact (MK_COMB (@lem4851775) (@lem4851774 A P Q)). Qed.
Lemma lem4851777 {A : Type'} (P : type180 A) (Q : type686 A) : (term4 A P Q) = (term13 A P Q).
Proof. exact (eq_refl (term4 A P Q)). Qed.
Lemma lem4851778 {A : Type'} (P : type180 A) (Q : type686 A) : ((term7 A P Q) = (term4 A P Q)) = ((term4 A P Q) = (term13 A P Q)).
Proof. exact (MK_COMB (@lem4851776 A P Q) (@lem4851777 A P Q)). Qed.
Lemma lem4851779 {A : Type'} (P : type180 A) (Q : type686 A) : (term4 A P Q) = (term13 A P Q).
Proof. exact (EQ_MP (@lem4851778 A P Q) (@lem4851770 A P Q)). Qed.
Lemma lem4851796 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q (@UNIV A)) = (term13 A P Q).
Proof. exact (TRANS (@lem4851766 A P Q) (@lem4851779 A P Q)). Qed.
Lemma lem4851797 {A : Type'} (P : type180 A) (Q : type686 A) : (term13 A P Q) = (@INTERSECTION_OF A P Q (@UNIV A)).
Proof. exact (SYM (@lem4851796 A P Q)). Qed.
Lemma lem4851798 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4851799 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem4851800 {A : Type'} (x : A) : term15 A x.
Proof. exact (EQ_MP (@lem4851799 A x) (@lem4851798 A x)). Qed.
Lemma lem4851801 {A : Type'} (x : A) : term16 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4851803 {A : Type'} (P : type180 A) : (P (@EMPTY (A -> Prop))) = ((P (@EMPTY (A -> Prop))) = True).
Proof. exact (@lem7 (P (@EMPTY (A -> Prop)))). Qed.
Lemma lem4851808 {A : Type'} (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (P (@EMPTY (A -> Prop))) = True.
Proof. exact (EQ_MP (@lem4851803 A P) (@lem4851745 A P h1)). Qed.
Lemma lem4851809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4851810 {A : Type'} (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (term17 A P) = (and True).
Proof. exact (MK_COMB (@lem4851809) (@lem4851808 A P h1)). Qed.
Lemma lem4851820 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4851801 A x (@lem4851800 A x)). Qed.
Lemma lem4851821 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem4851820 (A -> Prop) x). Qed.
Lemma lem4851822 {A : Type'} (c : A -> Prop) : (@IN (A -> Prop) c (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem4851821 A c). Qed.
Lemma lem4851823 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4851824 {A : Type'} (c : A -> Prop) : (term18 A c) = (imp False).
Proof. exact (MK_COMB (@lem4851823) (@lem4851822 A c)). Qed.
Lemma lem4851825 {A : Type'} (Q : type686 A) (c : A -> Prop) : (Q c) = (Q c).
Proof. exact (eq_refl (Q c)). Qed.
Lemma lem4851826 {A : Type'} (Q : type686 A) (c : A -> Prop) : (term19 A Q c) = (term20 A Q c).
Proof. exact (MK_COMB (@lem4851824 A c) (@lem4851825 A Q c)). Qed.
Lemma lem4851828 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4851829 {A : Type'} (Q : type686 A) (c : A -> Prop) : (term20 A Q c) = True.
Proof. exact (@lem4851828 (Q c)). Qed.
Lemma lem4851830 {A : Type'} (Q : type686 A) (c : A -> Prop) : (term19 A Q c) = True.
Proof. exact (TRANS (@lem4851826 A Q c) (@lem4851829 A Q c)). Qed.
Lemma lem4851831 {A : Type'} (Q : type686 A) : (term21 A Q) = (term22 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4851830 A Q c)). Qed.
Lemma lem4851832 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4851833 {A : Type'} (Q : type686 A) : (term23 A Q) = (term24 A).
Proof. exact (MK_COMB (@lem4851832 A) (@lem4851831 A Q)). Qed.
Lemma lem4851835 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4851836 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (@lem4851835 (A -> Prop) t). Qed.
Lemma lem4851837 {A : Type'} : (term24 A) = True.
Proof. exact (@lem4851836 A True). Qed.
Lemma lem4851838 {A : Type'} (Q : type686 A) : (term23 A Q) = True.
Proof. exact (TRANS (@lem4851833 A Q) (@lem4851837 A)). Qed.
Lemma lem4851839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4851840 {A : Type'} (Q : type686 A) : (term27 A Q) = (and True).
Proof. exact (MK_COMB (@lem4851839) (@lem4851838 A Q)). Qed.
Lemma lem4851844 {A : Type'} : (@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A).
Proof. exact (EQ_MP (@lem3354637 A) (@lem3354697 A)). Qed.
Lemma lem4851845 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4851846 {A : Type'} : (term28 A) = (@eq (A -> Prop) (@UNIV A)).
Proof. exact (MK_COMB (@lem4851845 A) (@lem4851844 A)). Qed.
Lemma lem4851847 {A : Type'} : (@UNIV A) = (@UNIV A).
Proof. exact (eq_refl (@UNIV A)). Qed.
Lemma lem4851848 {A : Type'} : ((@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A)) = ((@UNIV A) = (@UNIV A)).
Proof. exact (MK_COMB (@lem4851846 A) (@lem4851847 A)). Qed.
Lemma lem4851850 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4851851 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4851850 (A -> Prop) x). Qed.
Lemma lem4851852 {A : Type'} : ((@UNIV A) = (@UNIV A)) = True.
Proof. exact (@lem4851851 A (@UNIV A)). Qed.
Lemma lem4851853 {A : Type'} : ((@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A)) = True.
Proof. exact (TRANS (@lem4851848 A) (@lem4851852 A)). Qed.
Lemma lem4851854 {A : Type'} (Q : type686 A) : (term29 A Q) = (True /\ True).
Proof. exact (MK_COMB (@lem4851840 A Q) (@lem4851853 A)). Qed.
Lemma lem4851856 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4851857 : (True /\ True) = True.
Proof. exact (@lem4851856 True). Qed.
Lemma lem4851858 {A : Type'} (Q : type686 A) : (term29 A Q) = True.
Proof. exact (TRANS (@lem4851854 A Q) (@lem4851857)). Qed.
Lemma lem4851859 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (term30 A P Q) = (True /\ True).
Proof. exact (MK_COMB (@lem4851810 A P h1) (@lem4851858 A Q)). Qed.
Lemma lem4851861 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4851862 : (True /\ True) = True.
Proof. exact (@lem4851861 True). Qed.
Lemma lem4851863 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (term30 A P Q) = True.
Proof. exact (TRANS (@lem4851859 A Q P h1) (@lem4851862)). Qed.
Lemma lem4851864 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : True = (term30 A P Q).
Proof. exact (SYM (@lem4851863 A Q P h1)). Qed.
Lemma lem4851865 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : term30 A P Q.
Proof. exact (EQ_MP (@lem4851864 A Q P h1) (@lem0)). Qed.
Lemma lem4851866 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : term13 A P Q.
Proof. exact (ex_intro (term31 A P Q) (@EMPTY (A -> Prop)) (@lem4851865 A Q P h1)). Qed.
Lemma lem4851867 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : @INTERSECTION_OF A P Q (@UNIV A).
Proof. exact (EQ_MP (@lem4851797 A P Q) (@lem4851866 A Q P h1)). Qed.
Lemma lem4851868 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (P (@EMPTY (A -> Prop))) = (@INTERSECTION_OF A P Q (@UNIV A)).
Proof. exact (prop_ext (fun h2 : P (@EMPTY (A -> Prop)) => @lem4851867 A Q P h1) (fun h2 : @INTERSECTION_OF A P Q (@UNIV A) => @lem4851745 A P h1)). Qed.
Lemma lem4851869 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : @INTERSECTION_OF A P Q (@UNIV A).
Proof. exact (EQ_MP (@lem4851868 A Q P h1) (@lem4851745 A P h1)). Qed.
Lemma lem4851870 {A : Type'} (P : type180 A) (Q : type686 A) : term32 A P Q.
Proof. exact (fun h0 : P (@EMPTY (A -> Prop)) => @lem4851869 A Q P h0). Qed.
Lemma lem4851875 {A : Type'} (P : type180 A) : term33 A P.
Proof. exact (fun Q : type686 A => @lem4851870 A P Q). Qed.
Lemma lem4851880 {A : Type'} : term34 A.
Proof. exact (fun P : type180 A => @lem4851875 A P). Qed.
