Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CASES_term_abbrevs.
Require Import ITERATE_CASES_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7188777 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7188779 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7188780 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7188779 A B h1 op). Qed.
Lemma lem7188781 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7188782 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7188781 A B op) (@lem7188780 A B op h1)). Qed.
Lemma lem7188783 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7188784 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7188782 A B op h1 (@lem7188783 B op h2)). Qed.
Lemma lem7188785 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7188784 A B op h0 h1). Qed.
Lemma lem7188786 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7188787 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7188785 A B op h2 (@lem7188786 A B h1)). Qed.
Lemma lem7188788 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7188787 A B op h1 h0). Qed.
Lemma lem7188789 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7188788 A B op h1). Qed.
Lemma lem7188790 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7188789 A B h0). Qed.
Lemma lem7188791 {A B : Type'} : term0 A B.
Proof. exact (@lem7188790 A B (@lem6160738 A B)). Qed.
Lemma lem7188792 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7188791 A B op). Qed.
Lemma lem7188793 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7188822 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7188823 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7188822 A). Qed.
Lemma lem7188824 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7188825 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7188823 A) (@lem7188824 A s)). Qed.
Lemma lem7188826 {A : Type'} (P : A -> Prop) (f : A -> real) (g : A -> real) : (term6 A P f g) = (term6 A P f g).
Proof. exact (eq_refl (term6 A P f g)). Qed.
Lemma lem7188827 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> real) (g : A -> real) : (term7 A s P f g) = (term8 A s P f g).
Proof. exact (MK_COMB (@lem7188825 A s) (@lem7188826 A P f g)). Qed.
Lemma lem7188828 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7188829 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> real) (g : A -> real) : (term9 A s P f g) = (term10 A s P f g).
Proof. exact (MK_COMB (@lem7188828) (@lem7188827 A s P f g)). Qed.
Lemma lem7188831 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7188832 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7188831 A). Qed.
Lemma lem7188839 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term11 A s P) = (term11 A s P).
Proof. exact (eq_refl (term11 A s P)). Qed.
Lemma lem7188840 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term12 A s P) = (term13 A s P).
Proof. exact (MK_COMB (@lem7188832 A) (@lem7188839 A s P)). Qed.
Lemma lem7188841 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7188842 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> real) : (term14 A s P f) = (term15 A s P f).
Proof. exact (MK_COMB (@lem7188840 A s P) (@lem7188841 A f)). Qed.
Lemma lem7188843 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7188844 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> real) : (term16 A s P f) = (term17 A s P f).
Proof. exact (MK_COMB (@lem7188843) (@lem7188842 A s P f)). Qed.
Lemma lem7188846 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7188847 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7188846 A). Qed.
Lemma lem7188854 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term18 A s P) = (term18 A s P).
Proof. exact (eq_refl (term18 A s P)). Qed.
Lemma lem7188855 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term19 A s P) = (term20 A s P).
Proof. exact (MK_COMB (@lem7188847 A) (@lem7188854 A s P)). Qed.
Lemma lem7188856 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7188857 {A : Type'} (s : A -> Prop) (P : A -> Prop) (g : A -> real) : (term21 A s P g) = (term22 A s P g).
Proof. exact (MK_COMB (@lem7188855 A s P) (@lem7188856 A g)). Qed.
Lemma lem7188858 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) (g : A -> real) : (term23 A f s P g) = (term24 A f s P g).
Proof. exact (MK_COMB (@lem7188844 A s P f) (@lem7188857 A s P g)). Qed.
Lemma lem7188859 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) (g : A -> real) : ((term7 A s P f g) = (term23 A f s P g)) = ((term8 A s P f g) = (term24 A f s P g)).
Proof. exact (MK_COMB (@lem7188829 A s P f g) (@lem7188858 A f s P g)). Qed.
Lemma lem7188862 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (eq_refl (term25 A s)). Qed.
Lemma lem7188863 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) (g : A -> real) : (term26 A f s P g) = (term27 A f s P g).
Proof. exact (MK_COMB (@lem7188862 A s) (@lem7188859 A f s P g)). Qed.
Lemma lem7188866 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) : (term28 A f s P) = (term29 A f s P).
Proof. exact (fun_ext (fun g : A -> real => @lem7188863 A f s P g)). Qed.
Lemma lem7188867 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7188868 {A : Type'} (f : A -> real) (s : A -> Prop) (P : A -> Prop) : (term30 A f s P) = (term31 A f s P).
Proof. exact (MK_COMB (@lem7188867 A) (@lem7188866 A f s P)). Qed.
Lemma lem7188873 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term32 A s P) = (term33 A s P).
Proof. exact (fun_ext (fun f : A -> real => @lem7188868 A f s P)). Qed.
Lemma lem7188874 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7188875 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term34 A s P) = (term35 A s P).
Proof. exact (MK_COMB (@lem7188874 A) (@lem7188873 A s P)). Qed.
Lemma lem7188880 {A : Type'} (s : A -> Prop) : (term36 A s) = (term37 A s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem7188875 A s P)). Qed.
Lemma lem7188881 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7188882 {A : Type'} (s : A -> Prop) : (term38 A s) = (term39 A s).
Proof. exact (MK_COMB (@lem7188881 A) (@lem7188880 A s)). Qed.
Lemma lem7188887 {A : Type'} : (term40 A) = (term41 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7188882 A s)). Qed.
Lemma lem7188888 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7188889 {A : Type'} : (term42 A) = (term43 A).
Proof. exact (MK_COMB (@lem7188888 A) (@lem7188887 A)). Qed.
Lemma lem7188894 {A : Type'} : (term43 A) = (term42 A).
Proof. exact (SYM (@lem7188889 A)). Qed.
Lemma lem7188896 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7188793 A B op) (@lem7188792 A B op)). Qed.
Lemma lem7188897 {A : Type'} (op : type1627) : term44 A op.
Proof. exact (@lem7188896 A real op). Qed.
Lemma lem7188898 {A : Type'} : term45 A.
Proof. exact (@lem7188897 A real_add). Qed.
Lemma lem7188900 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7188777) (@lem7067132)). Qed.
Lemma lem7188901 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7188900)). Qed.
Lemma lem7188902 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7188901) (@lem0)). Qed.
Lemma lem7188903 {A : Type'} : term43 A.
Proof. exact (@lem7188898 A (@lem7188902)). Qed.
Lemma lem7188904 {A : Type'} : term42 A.
Proof. exact (EQ_MP (@lem7188894 A) (@lem7188903 A)). Qed.
