Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm48920_term_abbrevs.
Require Import ETA_AX_spec.
Require Import GABS_DEF_spec.
Require Import SELECT_AX_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm297_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem48814 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem48815 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem48816 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem48815 A B t) (@lem48814 A B t)). Qed.
Lemma lem48817 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (@lem9221 A P). Qed.
Lemma lem48818 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (eq_refl (term2 A P)). Qed.
Lemma lem48819 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (EQ_MP (@lem48818 A P) (@lem48817 A P)). Qed.
Lemma lem48820 {A : Type'} (P : A -> Prop) (x : A) : term4 A P x.
Proof. exact (@lem48819 A P x). Qed.
Lemma lem48821 {A : Type'} (x : A) (P : A -> Prop) : (term4 A P x) = (term5 A x P).
Proof. exact (eq_refl (term4 A P x)). Qed.
Lemma lem48822 {A : Type'} (x : A) (P : A -> Prop) : term5 A x P.
Proof. exact (EQ_MP (@lem48821 A x P) (@lem48820 A P x)). Qed.
Lemma lem48823 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem48824 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term6 A P.
Proof. exact (@lem48822 A x P (@lem48823 A P x h1)). Qed.
Lemma lem48825 {A : Type'} (P : A -> Prop) : (term6 A P) = ((term6 A P) = True).
Proof. exact (@lem7 (term6 A P)). Qed.
Lemma lem48826 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : (term6 A P) = True.
Proof. exact (EQ_MP (@lem48825 A P) (@lem48824 A P x h1)). Qed.
Lemma lem48831 {A : Type'} (x : A) (P : A -> Prop) : term7 A x P.
Proof. exact (fun h0 : P x => @lem48826 A P x h0). Qed.
Lemma lem48832 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (fun x : A => @lem48831 A x P). Qed.
Lemma lem48834 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) : (term9 _216 P Q) = (term10 _216 P Q).
Proof. exact (@lem297 _216 P Q). Qed.
Lemma lem48835 {A : Type'} (P : A -> Prop) (Q : Prop) : (term9 A P Q) = (term10 A P Q).
Proof. exact (@lem48834 A P Q). Qed.
Lemma lem48836 {A : Type'} (P : A -> Prop) : (term8 A P) = (term11 A P).
Proof. exact (@lem48835 A P ((term6 A P) = True)). Qed.
Lemma lem48838 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (@lem44145 A P). Qed.
Lemma lem48839 {A : Type'} (P : A -> Prop) : (term12 A P) = ((@GABS A P) = (@ε A P)).
Proof. exact (eq_refl (term12 A P)). Qed.
Lemma lem48846 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term13 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem48847 (p : Prop) (q : Prop) (p' : Prop) : term14 p q p'.
Proof. exact (fun q' : Prop => @lem48846 p q p' q'). Qed.
Lemma lem48848 (p : Prop) (q : Prop) : term15 p q.
Proof. exact (fun p' : Prop => @lem48847 p q p'). Qed.
Lemma lem48849 {_5076 : Type'} (P : _5076 -> Prop) : term16 _5076 P.
Proof. exact (@lem48848 (ex P) (term17 _5076 P)). Qed.
Lemma lem48850 {_5076 : Type'} (P : _5076 -> Prop) (p' : Prop) : term18 _5076 P p'.
Proof. exact (@lem48849 _5076 P p'). Qed.
Lemma lem48851 {_5076 : Type'} (P : _5076 -> Prop) (p' : Prop) : (term18 _5076 P p') = (term19 _5076 P p').
Proof. exact (eq_refl (term18 _5076 P p')). Qed.
Lemma lem48852 {_5076 : Type'} (P : _5076 -> Prop) (p' : Prop) : term19 _5076 P p'.
Proof. exact (EQ_MP (@lem48851 _5076 P p') (@lem48850 _5076 P p')). Qed.
Lemma lem48853 {_5076 : Type'} (P : _5076 -> Prop) (p' : Prop) (q' : Prop) : term20 _5076 P p' q'.
Proof. exact (@lem48852 _5076 P p' q'). Qed.
Lemma lem48854 {_5076 : Type'} (P : _5076 -> Prop) (p' : Prop) (q' : Prop) : (term20 _5076 P p' q') = (term21 _5076 P p' q').
Proof. exact (eq_refl (term20 _5076 P p' q')). Qed.
Lemma lem48855 {_5076 : Type'} (P : _5076 -> Prop) (p' : Prop) (q' : Prop) : term21 _5076 P p' q'.
Proof. exact (EQ_MP (@lem48854 _5076 P p' q') (@lem48853 _5076 P p' q')). Qed.
Lemma lem48862 {_5076 : Type'} (P : _5076 -> Prop) : (ex P) = (ex P).
Proof. exact (eq_refl (ex P)). Qed.
Lemma lem48863 {_5076 : Type'} (P : _5076 -> Prop) (q' : Prop) : term22 _5076 P q'.
Proof. exact (@lem48855 _5076 P (ex P) q'). Qed.
Lemma lem48864 {_5076 : Type'} (P : _5076 -> Prop) (q' : Prop) : term23 _5076 P q'.
Proof. exact (@lem48863 _5076 P q' (@lem48862 _5076 P)). Qed.
Lemma lem48865 {_5076 : Type'} (P : _5076 -> Prop) (h1 : ex P) : ex P.
Proof. exact (h1). Qed.
Lemma lem48866 {_5076 : Type'} (P : _5076 -> Prop) : (ex P) = ((ex P) = True).
Proof. exact (@lem7 (ex P)). Qed.
Lemma lem48873 {A : Type'} (P : A -> Prop) : (@GABS A P) = (@ε A P).
Proof. exact (EQ_MP (@lem48839 A P) (@lem48838 A P)). Qed.
Lemma lem48874 {_5076 : Type'} (P : _5076 -> Prop) : (@GABS _5076 P) = (@ε _5076 P).
Proof. exact (@lem48873 _5076 P). Qed.
Lemma lem48881 {_5076 : Type'} (P : _5076 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem48882 {_5076 : Type'} (P : _5076 -> Prop) : (term17 _5076 P) = (term6 _5076 P).
Proof. exact (MK_COMB (@lem48881 _5076 P) (@lem48874 _5076 P)). Qed.
Lemma lem48884 {A : Type'} (P : A -> Prop) : term11 A P.
Proof. exact (EQ_MP (@lem48836 A P) (@lem48832 A P)). Qed.
Lemma lem48885 {_5076 : Type'} (P : _5076 -> Prop) : term11 _5076 P.
Proof. exact (@lem48884 _5076 P). Qed.
Lemma lem48894 {_5076 : Type'} (t : _5076 -> Prop) : (term24 _5076 t) = t.
Proof. exact (@lem48816 _5076 Prop t). Qed.
Lemma lem48895 {_5076 : Type'} (P : _5076 -> Prop) : (term24 _5076 P) = P.
Proof. exact (@lem48894 _5076 P). Qed.
Lemma lem48898 {_5076 : Type'} : (@ex _5076) = (@ex _5076).
Proof. exact (eq_refl (@ex _5076)). Qed.
Lemma lem48899 {_5076 : Type'} (P : _5076 -> Prop) : (term25 _5076 P) = (ex P).
Proof. exact (MK_COMB (@lem48898 _5076) (@lem48895 _5076 P)). Qed.
Lemma lem48901 {_5076 : Type'} (P : _5076 -> Prop) (h1 : ex P) : (ex P) = True.
Proof. exact (EQ_MP (@lem48866 _5076 P) (@lem48865 _5076 P h1)). Qed.
Lemma lem48904 {_5076 : Type'} (P : _5076 -> Prop) (h1 : ex P) : (term25 _5076 P) = True.
Proof. exact (TRANS (@lem48899 _5076 P) (@lem48901 _5076 P h1)). Qed.
Lemma lem48905 {_5076 : Type'} (P : _5076 -> Prop) (h1 : ex P) : True = (term25 _5076 P).
Proof. exact (SYM (@lem48904 _5076 P h1)). Qed.
Lemma lem48906 {_5076 : Type'} (P : _5076 -> Prop) (h1 : ex P) : term25 _5076 P.
Proof. exact (EQ_MP (@lem48905 _5076 P h1) (@lem0)). Qed.
Lemma lem48907 {_5076 : Type'} (P : _5076 -> Prop) (h1 : ex P) : (term6 _5076 P) = True.
Proof. exact (@lem48885 _5076 P (@lem48906 _5076 P h1)). Qed.
Lemma lem48910 {_5076 : Type'} (P : _5076 -> Prop) (h1 : ex P) : (term17 _5076 P) = True.
Proof. exact (TRANS (@lem48882 _5076 P) (@lem48907 _5076 P h1)). Qed.
Lemma lem48911 {_5076 : Type'} (P : _5076 -> Prop) : term26 _5076 P.
Proof. exact (fun h0 : ex P => @lem48910 _5076 P h0). Qed.
Lemma lem48912 {_5076 : Type'} (P : _5076 -> Prop) : term27 _5076 P.
Proof. exact (@lem48864 _5076 P True). Qed.
Lemma lem48913 {_5076 : Type'} (P : _5076 -> Prop) : (term28 _5076 P) = (term29 _5076 P).
Proof. exact (@lem48912 _5076 P (@lem48911 _5076 P)). Qed.
Lemma lem48915 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem48916 {_5076 : Type'} (P : _5076 -> Prop) : (term29 _5076 P) = True.
Proof. exact (@lem48915 (ex P)). Qed.
Lemma lem48919 {_5076 : Type'} (P : _5076 -> Prop) : (term28 _5076 P) = True.
Proof. exact (TRANS (@lem48913 _5076 P) (@lem48916 _5076 P)). Qed.
Lemma lem48920 {_5076 : Type'} (P : _5076 -> Prop) : True = (term28 _5076 P).
Proof. exact (SYM (@lem48919 _5076 P)). Qed.
