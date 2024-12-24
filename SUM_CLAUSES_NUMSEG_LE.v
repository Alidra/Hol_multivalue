Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CLAUSES_NUMSEG_LE_term_abbrevs.
Require Import ITERATE_CLAUSES_NUMSEG_LE_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7221863 {_123593 : Type'} (f : nat -> _123593) (op : type1400 _123593) : term0 _123593 f op.
Proof. exact (@lem6198343 _123593 f op). Qed.
Lemma lem7221864 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : (term0 _123593 f op) = (term1 _123593 op f).
Proof. exact (eq_refl (term0 _123593 f op)). Qed.
Lemma lem7221867 {_123593 : Type'} (op : type1400 _123593) (f : nat -> _123593) : term1 _123593 op f.
Proof. exact (EQ_MP (@lem7221864 _123593 op f) (@lem7221863 _123593 f op)). Qed.
Lemma lem7221868 (op : type1627) (f : nat -> real) : term2 op f.
Proof. exact (@lem7221867 real op f). Qed.
Lemma lem7221869 (f : nat -> real) : term3 f.
Proof. exact (@lem7221868 real_add f). Qed.
Lemma lem7221870 (f : nat -> real) : term4 f.
Proof. exact (@lem7221869 f (@lem7067132)). Qed.
Lemma lem7221900 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7221901 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7221900 nat). Qed.
Lemma lem7221906 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem7221907 : term6 = term7.
Proof. exact (MK_COMB (@lem7221901) (@lem7221906)). Qed.
Lemma lem7221908 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221909 (f : nat -> real) : (term8 f) = (term9 f).
Proof. exact (MK_COMB (@lem7221907) (@lem7221908 f)). Qed.
Lemma lem7221910 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7221911 (f : nat -> real) : (term10 f) = (term11 f).
Proof. exact (MK_COMB (@lem7221910) (@lem7221909 f)). Qed.
Lemma lem7221912 (f : nat -> real) : (term12 f) = (term12 f).
Proof. exact (eq_refl (term12 f)). Qed.
Lemma lem7221913 (f : nat -> real) : ((term8 f) = (term12 f)) = ((term9 f) = (term12 f)).
Proof. exact (MK_COMB (@lem7221911 f) (@lem7221912 f)). Qed.
Lemma lem7221916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7221917 (f : nat -> real) : (term13 f) = (term14 f).
Proof. exact (MK_COMB (@lem7221916) (@lem7221913 f)). Qed.
Lemma lem7221925 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7221926 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7221925 nat). Qed.
Lemma lem7221931 (k : nat) : (term15 k) = (term15 k).
Proof. exact (eq_refl (term15 k)). Qed.
Lemma lem7221932 (k : nat) : (term16 k) = (term17 k).
Proof. exact (MK_COMB (@lem7221926) (@lem7221931 k)). Qed.
Lemma lem7221933 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221934 (k : nat) (f : nat -> real) : (term18 k f) = (term19 k f).
Proof. exact (MK_COMB (@lem7221932 k) (@lem7221933 f)). Qed.
Lemma lem7221935 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7221936 (k : nat) (f : nat -> real) : (term20 k f) = (term21 k f).
Proof. exact (MK_COMB (@lem7221935) (@lem7221934 k f)). Qed.
Lemma lem7221938 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7221939 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7221938 nat). Qed.
Lemma lem7221944 (k : nat) : (term22 k) = (term22 k).
Proof. exact (eq_refl (term22 k)). Qed.
Lemma lem7221945 (k : nat) : (term23 k) = (term24 k).
Proof. exact (MK_COMB (@lem7221939) (@lem7221944 k)). Qed.
Lemma lem7221946 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221947 (k : nat) (f : nat -> real) : (term25 k f) = (term26 k f).
Proof. exact (MK_COMB (@lem7221945 k) (@lem7221946 f)). Qed.
Lemma lem7221948 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7221949 (k : nat) (f : nat -> real) : (term27 k f) = (term28 k f).
Proof. exact (MK_COMB (@lem7221948) (@lem7221947 k f)). Qed.
Lemma lem7221950 (f : nat -> real) (k : nat) : (term29 f k) = (term29 f k).
Proof. exact (eq_refl (term29 f k)). Qed.
Lemma lem7221951 (f : nat -> real) (k : nat) : (term30 f k) = (term31 f k).
Proof. exact (MK_COMB (@lem7221949 k f) (@lem7221950 f k)). Qed.
Lemma lem7221952 (f : nat -> real) (k : nat) : ((term18 k f) = (term30 f k)) = ((term19 k f) = (term31 f k)).
Proof. exact (MK_COMB (@lem7221936 k f) (@lem7221951 f k)). Qed.
Lemma lem7221955 (f : nat -> real) : (term32 f) = (term33 f).
Proof. exact (fun_ext (fun k : nat => @lem7221952 f k)). Qed.
Lemma lem7221956 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7221957 (f : nat -> real) : (term34 f) = (term35 f).
Proof. exact (MK_COMB (@lem7221956) (@lem7221955 f)). Qed.
Lemma lem7221962 (f : nat -> real) : (term36 f) = (term4 f).
Proof. exact (MK_COMB (@lem7221917 f) (@lem7221957 f)). Qed.
Lemma lem7221965 (f : nat -> real) : (term37 f) = (term37 f).
Proof. exact (eq_refl (term37 f)). Qed.
Lemma lem7221966 (f : nat -> real) : (term38 f) = (term39 f).
Proof. exact (MK_COMB (@lem7221965 f) (@lem7221962 f)). Qed.
Lemma lem7221968 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7221969 (f : nat -> real) : (term39 f) = True.
Proof. exact (@lem7221968 (term4 f)). Qed.
Lemma lem7221972 (f : nat -> real) : (term40 f) = (term40 f).
Proof. exact (eq_refl (term40 f)). Qed.
Lemma lem7221973 (f : nat -> real) : (term40 f) = ((term39 f) = True).
Proof. exact (eq_refl (term40 f)). Qed.
Lemma lem7221974 (f : nat -> real) : (term41 f) = (term41 f).
Proof. exact (eq_refl (term41 f)). Qed.
Lemma lem7221975 (f : nat -> real) : ((term40 f) = (term40 f)) = ((term40 f) = ((term39 f) = True)).
Proof. exact (MK_COMB (@lem7221974 f) (@lem7221973 f)). Qed.
Lemma lem7221976 (f : nat -> real) : (term40 f) = ((term39 f) = True).
Proof. exact (eq_refl (term40 f)). Qed.
Lemma lem7221977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7221978 (f : nat -> real) : (term41 f) = (term42 f).
Proof. exact (MK_COMB (@lem7221977) (@lem7221976 f)). Qed.
Lemma lem7221979 (f : nat -> real) : ((term39 f) = True) = ((term39 f) = True).
Proof. exact (eq_refl ((term39 f) = True)). Qed.
Lemma lem7221980 (f : nat -> real) : ((term40 f) = ((term39 f) = True)) = (((term39 f) = True) = ((term39 f) = True)).
Proof. exact (MK_COMB (@lem7221978 f) (@lem7221979 f)). Qed.
Lemma lem7221981 (f : nat -> real) : ((term40 f) = (term40 f)) = (((term39 f) = True) = ((term39 f) = True)).
Proof. exact (TRANS (@lem7221975 f) (@lem7221980 f)). Qed.
Lemma lem7221982 (f : nat -> real) : ((term39 f) = True) = ((term39 f) = True).
Proof. exact (EQ_MP (@lem7221981 f) (@lem7221972 f)). Qed.
Lemma lem7221983 (f : nat -> real) : (term39 f) = True.
Proof. exact (EQ_MP (@lem7221982 f) (@lem7221969 f)). Qed.
Lemma lem7221984 (f : nat -> real) : (term38 f) = True.
Proof. exact (TRANS (@lem7221966 f) (@lem7221983 f)). Qed.
Lemma lem7221985 (f : nat -> real) : True = (term38 f).
Proof. exact (SYM (@lem7221984 f)). Qed.
Lemma lem7221986 (f : nat -> real) : term38 f.
Proof. exact (EQ_MP (@lem7221985 f) (@lem0)). Qed.
Lemma lem7221987 (f : nat -> real) : term36 f.
Proof. exact (@lem7221986 f (@lem7221870 f)). Qed.
