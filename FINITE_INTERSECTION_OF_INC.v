Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INTERSECTION_OF_INC_term_abbrevs.
Require Import FINITE_SING_spec.
Require Import INTERSECTION_OF_INC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4876799 {_92373 : Type'} (a : _92373) : term0 _92373 a.
Proof. exact (@lem3608356 _92373 a). Qed.
Lemma lem4876800 {_92373 : Type'} (a : _92373) : (term0 _92373 a) = (term1 _92373 a).
Proof. exact (eq_refl (term0 _92373 a)). Qed.
Lemma lem4876801 {_92373 : Type'} (a : _92373) : term1 _92373 a.
Proof. exact (EQ_MP (@lem4876800 _92373 a) (@lem4876799 _92373 a)). Qed.
Lemma lem4876802 {_92373 : Type'} (a : _92373) : (term1 _92373 a) = ((term1 _92373 a) = True).
Proof. exact (@lem7 (term1 _92373 a)). Qed.
Lemma lem4876804 {A : Type'} (P : type180 A) : term2 A P.
Proof. exact (@lem4842609 A P). Qed.
Lemma lem4876805 {A : Type'} (P : type180 A) : (term2 A P) = (term3 A P).
Proof. exact (eq_refl (term2 A P)). Qed.
Lemma lem4876806 {A : Type'} (P : type180 A) : term3 A P.
Proof. exact (EQ_MP (@lem4876805 A P) (@lem4876804 A P)). Qed.
Lemma lem4876807 {A : Type'} (P : type180 A) (Q : type686 A) : term4 A P Q.
Proof. exact (@lem4876806 A P Q). Qed.
Lemma lem4876808 {A : Type'} (P : type180 A) (Q : type686 A) : (term4 A P Q) = (term5 A P Q).
Proof. exact (eq_refl (term4 A P Q)). Qed.
Lemma lem4876809 {A : Type'} (P : type180 A) (Q : type686 A) : term5 A P Q.
Proof. exact (EQ_MP (@lem4876808 A P Q) (@lem4876807 A P Q)). Qed.
Lemma lem4876810 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term6 A P Q s.
Proof. exact (@lem4876809 A P Q s). Qed.
Lemma lem4876811 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term6 A P Q s) = (term7 A P Q s).
Proof. exact (eq_refl (term6 A P Q s)). Qed.
Lemma lem4876812 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term7 A P Q s.
Proof. exact (EQ_MP (@lem4876811 A P Q s) (@lem4876810 A P Q s)). Qed.
Lemma lem4876813 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term8 A P Q s) : term8 A P Q s.
Proof. exact (h1). Qed.
Lemma lem4876814 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term8 A P Q s) : @INTERSECTION_OF A P Q s.
Proof. exact (@lem4876812 A P Q s (@lem4876813 A P Q s h1)). Qed.
Lemma lem4876815 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A P Q s) = ((@INTERSECTION_OF A P Q s) = True).
Proof. exact (@lem7 (@INTERSECTION_OF A P Q s)). Qed.
Lemma lem4876816 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term8 A P Q s) : (@INTERSECTION_OF A P Q s) = True.
Proof. exact (EQ_MP (@lem4876815 A P Q s) (@lem4876814 A P Q s h1)). Qed.
Lemma lem4876833 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term9 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4876834 (p : Prop) (q : Prop) (p' : Prop) : term10 p q p'.
Proof. exact (fun q' : Prop => @lem4876833 p q p' q'). Qed.
Lemma lem4876835 (p : Prop) (q : Prop) : term11 p q.
Proof. exact (fun p' : Prop => @lem4876834 p q p'). Qed.
Lemma lem4876836 {A : Type'} (P : type686 A) (s : A -> Prop) : term12 A P s.
Proof. exact (@lem4876835 (P s) (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s)). Qed.
Lemma lem4876837 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : term13 A P s p'.
Proof. exact (@lem4876836 A P s p'). Qed.
Lemma lem4876838 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : (term13 A P s p') = (term14 A P s p').
Proof. exact (eq_refl (term13 A P s p')). Qed.
Lemma lem4876839 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : term14 A P s p'.
Proof. exact (EQ_MP (@lem4876838 A P s p') (@lem4876837 A P s p')). Qed.
Lemma lem4876840 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term15 A P s p' q'.
Proof. exact (@lem4876839 A P s p' q'). Qed.
Lemma lem4876841 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term15 A P s p' q') = (term16 A P s p' q').
Proof. exact (eq_refl (term15 A P s p' q')). Qed.
Lemma lem4876842 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term16 A P s p' q'.
Proof. exact (EQ_MP (@lem4876841 A P s p' q') (@lem4876840 A P s p' q')). Qed.
Lemma lem4876843 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4876844 {A : Type'} (P : type686 A) (s : A -> Prop) (q' : Prop) : term17 A P s q'.
Proof. exact (@lem4876842 A P s (P s) q'). Qed.
Lemma lem4876845 {A : Type'} (P : type686 A) (s : A -> Prop) (q' : Prop) : term18 A P s q'.
Proof. exact (@lem4876844 A P s q' (@lem4876843 A P s)). Qed.
Lemma lem4876846 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem4876847 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = ((P s) = True).
Proof. exact (@lem7 (P s)). Qed.
Lemma lem4876850 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term19 A P Q s.
Proof. exact (fun h0 : term8 A P Q s => @lem4876816 A P Q s h0). Qed.
Lemma lem4876851 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term19 A P Q s.
Proof. exact (@lem4876850 A P Q s). Qed.
Lemma lem4876852 {A : Type'} (P : type686 A) (s : A -> Prop) : term20 A P s.
Proof. exact (@lem4876851 A (@FINITE (A -> Prop)) P s). Qed.
Lemma lem4876856 {_92373 : Type'} (a : _92373) : (term1 _92373 a) = True.
Proof. exact (EQ_MP (@lem4876802 _92373 a) (@lem4876801 _92373 a)). Qed.
Lemma lem4876857 {A : Type'} (a : A -> Prop) : (term21 A a) = True.
Proof. exact (@lem4876856 (A -> Prop) a). Qed.
Lemma lem4876858 {A : Type'} (s : A -> Prop) : (term21 A s) = True.
Proof. exact (@lem4876857 A s). Qed.
Lemma lem4876859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4876860 {A : Type'} (s : A -> Prop) : (term22 A s) = (and True).
Proof. exact (MK_COMB (@lem4876859) (@lem4876858 A s)). Qed.
Lemma lem4876862 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (P s) = True.
Proof. exact (EQ_MP (@lem4876847 A P s) (@lem4876846 A P s h1)). Qed.
Lemma lem4876863 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (term23 A P s) = (True /\ True).
Proof. exact (MK_COMB (@lem4876860 A s) (@lem4876862 A P s h1)). Qed.
Lemma lem4876865 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4876866 : (True /\ True) = True.
Proof. exact (@lem4876865 True). Qed.
Lemma lem4876867 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (term23 A P s) = True.
Proof. exact (TRANS (@lem4876863 A P s h1) (@lem4876866)). Qed.
Lemma lem4876868 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : True = (term23 A P s).
Proof. exact (SYM (@lem4876867 A P s h1)). Qed.
Lemma lem4876869 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : term23 A P s.
Proof. exact (EQ_MP (@lem4876868 A P s h1) (@lem0)). Qed.
Lemma lem4876870 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = True.
Proof. exact (@lem4876852 A P s (@lem4876869 A P s h1)). Qed.
Lemma lem4876871 {A : Type'} (P : type686 A) (s : A -> Prop) : term24 A P s.
Proof. exact (fun h0 : P s => @lem4876870 A P s h0). Qed.
Lemma lem4876872 {A : Type'} (P : type686 A) (s : A -> Prop) : term25 A P s.
Proof. exact (@lem4876845 A P s True). Qed.
Lemma lem4876873 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = (term27 A P s).
Proof. exact (@lem4876872 A P s (@lem4876871 A P s)). Qed.
Lemma lem4876875 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4876876 {A : Type'} (P : type686 A) (s : A -> Prop) : (term27 A P s) = True.
Proof. exact (@lem4876875 (P s)). Qed.
Lemma lem4876877 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = True.
Proof. exact (TRANS (@lem4876873 A P s) (@lem4876876 A P s)). Qed.
Lemma lem4876878 {A : Type'} (P : type686 A) : (term28 A P) = (term29 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4876877 A P s)). Qed.
Lemma lem4876879 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4876880 {A : Type'} (P : type686 A) : (term30 A P) = (term31 A).
Proof. exact (MK_COMB (@lem4876879 A) (@lem4876878 A P)). Qed.
Lemma lem4876882 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4876883 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (@lem4876882 (A -> Prop) t). Qed.
Lemma lem4876884 {A : Type'} : (term31 A) = True.
Proof. exact (@lem4876883 A True). Qed.
Lemma lem4876885 {A : Type'} (P : type686 A) : (term30 A P) = True.
Proof. exact (TRANS (@lem4876880 A P) (@lem4876884 A)). Qed.
Lemma lem4876886 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4876885 A P)). Qed.
Lemma lem4876887 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4876888 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem4876887 A) (@lem4876886 A)). Qed.
Lemma lem4876890 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4876891 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (@lem4876890 (type686 A) t). Qed.
Lemma lem4876892 {A : Type'} : (term37 A) = True.
Proof. exact (@lem4876891 A True). Qed.
Lemma lem4876893 {A : Type'} : (term36 A) = True.
Proof. exact (TRANS (@lem4876888 A) (@lem4876892 A)). Qed.
Lemma lem4876894 {A : Type'} : True = (term36 A).
Proof. exact (SYM (@lem4876893 A)). Qed.
Lemma lem4876895 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem4876894 A) (@lem0)). Qed.
