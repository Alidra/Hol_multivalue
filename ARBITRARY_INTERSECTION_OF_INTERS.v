Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_INTERS_term_abbrevs.
Require Import ARBITRARY_spec.
Require Import ARBITRARY_INTERSECTION_OF_IDEMPOT_spec.
Require Import INTERSECTION_OF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem4868730 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4842239 A P). Qed.
Lemma lem4868731 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4868732 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4868731 A P) (@lem4868730 A P)). Qed.
Lemma lem4868733 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4868732 A P Q). Qed.
Lemma lem4868734 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@INTERSECTION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4868737 {A : Type'} (P : type686 A) (h1 : (term4 A P) = (@INTERSECTION_OF A (@ARBITRARY A) P)) : (term4 A P) = (@INTERSECTION_OF A (@ARBITRARY A) P).
Proof. exact (h1). Qed.
Lemma lem4868738 {A : Type'} (P : type686 A) (h1 : (term4 A P) = (@INTERSECTION_OF A (@ARBITRARY A) P)) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term4 A P).
Proof. exact (SYM (@lem4868737 A P h1)). Qed.
Lemma lem4868739 {A : Type'} (P : type686 A) (h1 : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term4 A P)) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term4 A P).
Proof. exact (h1). Qed.
Lemma lem4868740 {A : Type'} (P : type686 A) (h1 : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term4 A P)) : (term4 A P) = (@INTERSECTION_OF A (@ARBITRARY A) P).
Proof. exact (SYM (@lem4868739 A P h1)). Qed.
Lemma lem4868741 {A : Type'} (P : type686 A) : ((term4 A P) = (@INTERSECTION_OF A (@ARBITRARY A) P)) = ((@INTERSECTION_OF A (@ARBITRARY A) P) = (term4 A P)).
Proof. exact (prop_ext (fun h1 : (term4 A P) = (@INTERSECTION_OF A (@ARBITRARY A) P) => @lem4868738 A P h1) (fun h1 : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term4 A P) => @lem4868740 A P h1)). Qed.
Lemma lem4868742 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4868741 A P)). Qed.
Lemma lem4868743 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4868744 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem4868743 A) (@lem4868742 A)). Qed.
Lemma lem4868745 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem4868744 A) (@lem4868382 A)). Qed.
Lemma lem4868746 {A : Type'} (P : type686 A) : term9 A P.
Proof. exact (@lem4868745 A P). Qed.
Lemma lem4868747 {A : Type'} (P : type686 A) : (term9 A P) = ((@INTERSECTION_OF A (@ARBITRARY A) P) = (term4 A P)).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem4868749 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term10 A u P.
Proof. exact (h1). Qed.
Lemma lem4868751 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term4 A P).
Proof. exact (EQ_MP (@lem4868747 A P) (@lem4868746 A P)). Qed.
Lemma lem4868752 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term4 A P).
Proof. exact (@lem4868751 A P). Qed.
Lemma lem4868753 {A : Type'} (u : type686 A) : (@INTERS A u) = (@INTERS A u).
Proof. exact (eq_refl (@INTERS A u)). Qed.
Lemma lem4868754 {A : Type'} (P : type686 A) (u : type686 A) : (term11 A P u) = (term12 A P u).
Proof. exact (MK_COMB (@lem4868752 A P) (@lem4868753 A u)). Qed.
Lemma lem4868755 {A : Type'} (P : type686 A) (u : type686 A) : (term12 A P u) = (term11 A P u).
Proof. exact (SYM (@lem4868754 A P u)). Qed.
Lemma lem4868757 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4868734 A P Q) (@lem4868733 A P Q)). Qed.
Lemma lem4868758 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4868757 A P Q). Qed.
Lemma lem4868759 {A : Type'} (P : type686 A) : (term4 A P) = (term13 A P).
Proof. exact (@lem4868758 A (@ARBITRARY A) (@INTERSECTION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4868760 {A : Type'} (u : type686 A) : (@INTERS A u) = (@INTERS A u).
Proof. exact (eq_refl (@INTERS A u)). Qed.
Lemma lem4868761 {A : Type'} (P : type686 A) (u : type686 A) : (term12 A P u) = (term14 A P u).
Proof. exact (MK_COMB (@lem4868759 A P) (@lem4868760 A u)). Qed.
Lemma lem4868762 {A : Type'} (P : type686 A) (u : type686 A) : (term14 A P u) = (term12 A P u).
Proof. exact (SYM (@lem4868761 A P u)). Qed.
Lemma lem4868764 {A B : Type'} (f : A -> B) (y : A) : (term15 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4868765 {A : Type'} (f : type686 A) (y : A -> Prop) : (term16 A f y) = (f y).
Proof. exact (@lem4868764 (A -> Prop) Prop f y). Qed.
Lemma lem4868766 {A : Type'} (P : type686 A) (u : type686 A) : (term17 A P u) = (term14 A P u).
Proof. exact (@lem4868765 A (term13 A P) (@INTERS A u)). Qed.
Lemma lem4868767 {A : Type'} (P : type686 A) (s : A -> Prop) : (term18 A P s) = (term19 A P s).
Proof. exact (eq_refl (term18 A P s)). Qed.
Lemma lem4868768 {A : Type'} (P : type686 A) : (term20 A P) = (term13 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4868767 A P s)). Qed.
Lemma lem4868769 {A : Type'} (u : type686 A) : (@INTERS A u) = (@INTERS A u).
Proof. exact (eq_refl (@INTERS A u)). Qed.
Lemma lem4868770 {A : Type'} (P : type686 A) (u : type686 A) : (term17 A P u) = (term14 A P u).
Proof. exact (MK_COMB (@lem4868768 A P) (@lem4868769 A u)). Qed.
Lemma lem4868771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4868772 {A : Type'} (P : type686 A) (u : type686 A) : (term21 A P u) = (term22 A P u).
Proof. exact (MK_COMB (@lem4868771) (@lem4868770 A P u)). Qed.
Lemma lem4868773 {A : Type'} (P : type686 A) (u : type686 A) : (term14 A P u) = (term23 A P u).
Proof. exact (eq_refl (term14 A P u)). Qed.
Lemma lem4868774 {A : Type'} (P : type686 A) (u : type686 A) : ((term17 A P u) = (term14 A P u)) = ((term14 A P u) = (term23 A P u)).
Proof. exact (MK_COMB (@lem4868772 A P u) (@lem4868773 A P u)). Qed.
Lemma lem4868775 {A : Type'} (P : type686 A) (u : type686 A) : (term14 A P u) = (term23 A P u).
Proof. exact (EQ_MP (@lem4868774 A P u) (@lem4868766 A P u)). Qed.
Lemma lem4868792 {A : Type'} (P : type686 A) (u : type686 A) : (term23 A P u) = (term14 A P u).
Proof. exact (SYM (@lem4868775 A P u)). Qed.
Lemma lem4868793 {A : Type'} (s : type686 A) : term24 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4868794 {A : Type'} (s : type686 A) : (term24 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem4868796 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term25 A u P s.
Proof. exact (@lem4868749 A u P h1 s). Qed.
Lemma lem4868797 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term25 A u P s) = (term26 A u P s).
Proof. exact (eq_refl (term25 A u P s)). Qed.
Lemma lem4868798 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term26 A u P s.
Proof. exact (EQ_MP (@lem4868797 A u P s) (@lem4868796 A s u P h1)). Qed.
Lemma lem4868799 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term26 A u P s) = ((term26 A u P s) = True).
Proof. exact (@lem7 (term26 A u P s)). Qed.
Lemma lem4868804 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4868794 A s) (@lem4868793 A s)). Qed.
Lemma lem4868805 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4868804 A s). Qed.
Lemma lem4868806 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = True.
Proof. exact (@lem4868805 A u). Qed.
Lemma lem4868807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868808 {A : Type'} (u : type686 A) : (term27 A u) = (and True).
Proof. exact (MK_COMB (@lem4868807) (@lem4868806 A u)). Qed.
Lemma lem4868816 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term26 A u P s) = True.
Proof. exact (EQ_MP (@lem4868799 A u P s) (@lem4868798 A s u P h1)). Qed.
Lemma lem4868817 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term26 A u P s) = True.
Proof. exact (@lem4868816 A s u P h1). Qed.
Lemma lem4868818 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term26 A u P c) = True.
Proof. exact (@lem4868817 A c u P h1). Qed.
Lemma lem4868819 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term28 A u P) = (term29 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4868818 A c u P h1)). Qed.
Lemma lem4868820 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4868821 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term10 A u P) = (term30 A).
Proof. exact (MK_COMB (@lem4868820 A) (@lem4868819 A u P h1)). Qed.
Lemma lem4868823 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4868824 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem4868823 (A -> Prop) t). Qed.
Lemma lem4868825 {A : Type'} : (term30 A) = True.
Proof. exact (@lem4868824 A True). Qed.
Lemma lem4868826 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term10 A u P) = True.
Proof. exact (TRANS (@lem4868821 A u P h1) (@lem4868825 A)). Qed.
Lemma lem4868827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868828 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term33 A u P) = (and True).
Proof. exact (MK_COMB (@lem4868827) (@lem4868826 A u P h1)). Qed.
Lemma lem4868830 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4868831 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4868830 (A -> Prop) x). Qed.
Lemma lem4868832 {A : Type'} (u : type686 A) : ((@INTERS A u) = (@INTERS A u)) = True.
Proof. exact (@lem4868831 A (@INTERS A u)). Qed.
Lemma lem4868833 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term34 A P u) = (True /\ True).
Proof. exact (MK_COMB (@lem4868828 A u P h1) (@lem4868832 A u)). Qed.
Lemma lem4868835 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4868836 : (True /\ True) = True.
Proof. exact (@lem4868835 True). Qed.
Lemma lem4868837 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term34 A P u) = True.
Proof. exact (TRANS (@lem4868833 A u P h1) (@lem4868836)). Qed.
Lemma lem4868838 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term35 A P u) = (True /\ True).
Proof. exact (MK_COMB (@lem4868808 A u) (@lem4868837 A u P h1)). Qed.
Lemma lem4868840 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4868841 : (True /\ True) = True.
Proof. exact (@lem4868840 True). Qed.
Lemma lem4868842 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term35 A P u) = True.
Proof. exact (TRANS (@lem4868838 A u P h1) (@lem4868841)). Qed.
Lemma lem4868843 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : True = (term35 A P u).
Proof. exact (SYM (@lem4868842 A u P h1)). Qed.
Lemma lem4868844 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term35 A P u.
Proof. exact (EQ_MP (@lem4868843 A u P h1) (@lem0)). Qed.
Lemma lem4868845 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term23 A P u.
Proof. exact (ex_intro (term36 A P u) u (@lem4868844 A u P h1)). Qed.
Lemma lem4868846 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term14 A P u.
Proof. exact (EQ_MP (@lem4868792 A P u) (@lem4868845 A u P h1)). Qed.
Lemma lem4868847 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term12 A P u.
Proof. exact (EQ_MP (@lem4868762 A P u) (@lem4868846 A u P h1)). Qed.
Lemma lem4868848 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term11 A P u.
Proof. exact (EQ_MP (@lem4868755 A P u) (@lem4868847 A u P h1)). Qed.
Lemma lem4868849 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term10 A u P) = (term11 A P u).
Proof. exact (prop_ext (fun h2 : term10 A u P => @lem4868848 A u P h1) (fun h2 : term11 A P u => @lem4868749 A u P h1)). Qed.
Lemma lem4868850 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term11 A P u.
Proof. exact (EQ_MP (@lem4868849 A u P h1) (@lem4868749 A u P h1)). Qed.
Lemma lem4868851 {A : Type'} (P : type686 A) (u : type686 A) : term37 A P u.
Proof. exact (fun h0 : term10 A u P => @lem4868850 A u P h0). Qed.
Lemma lem4868856 {A : Type'} (P : type686 A) : term38 A P.
Proof. exact (fun u : type686 A => @lem4868851 A P u). Qed.
Lemma lem4868861 {A : Type'} : term39 A.
Proof. exact (fun P : type686 A => @lem4868856 A P). Qed.
