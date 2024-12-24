Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_EXP_term_abbrevs.
Require Import EXP_MULT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem88951 (m : nat) : term0 m.
Proof. exact (@lem88950 m). Qed.
Lemma lem88952 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem88953 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem88952 m) (@lem88951 m)). Qed.
Lemma lem88954 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem88953 m n). Qed.
Lemma lem88955 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem88956 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem88955 m n) (@lem88954 m n)). Qed.
Lemma lem88957 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem88956 m n p). Qed.
Lemma lem88958 (m : nat) (n : nat) (p : nat) : (term4 m n p) = ((term5 m n p) = (term6 m n p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem88975 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (EQ_MP (@lem88958 m n p) (@lem88957 m n p)). Qed.
Lemma lem88976 (x : nat) (m : nat) (n : nat) : (term5 x m n) = (term6 x m n).
Proof. exact (@lem88975 x m n). Qed.
Lemma lem88977 (x : nat) (m : nat) (n : nat) : (term7 x m n) = (term7 x m n).
Proof. exact (eq_refl (term7 x m n)). Qed.
Lemma lem88978 (x : nat) (m : nat) (n : nat) : ((term6 x m n) = (term5 x m n)) = ((term6 x m n) = (term6 x m n)).
Proof. exact (MK_COMB (@lem88977 x m n) (@lem88976 x m n)). Qed.
Lemma lem88980 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem88981 (x : nat) : (x = x) = True.
Proof. exact (@lem88980 nat x). Qed.
Lemma lem88982 (x : nat) (m : nat) (n : nat) : ((term6 x m n) = (term6 x m n)) = True.
Proof. exact (@lem88981 (term6 x m n)). Qed.
Lemma lem88983 (x : nat) (m : nat) (n : nat) : ((term6 x m n) = (term5 x m n)) = True.
Proof. exact (TRANS (@lem88978 x m n) (@lem88982 x m n)). Qed.
Lemma lem88984 (x : nat) (m : nat) : (term8 x m) = term9.
Proof. exact (fun_ext (fun n : nat => @lem88983 x m n)). Qed.
Lemma lem88985 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88986 (x : nat) (m : nat) : (term10 x m) = term11.
Proof. exact (MK_COMB (@lem88985) (@lem88984 x m)). Qed.
Lemma lem88988 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem88989 (t : Prop) : (term13 t) = t.
Proof. exact (@lem88988 nat t). Qed.
Lemma lem88990 : term11 = True.
Proof. exact (@lem88989 True). Qed.
Lemma lem88991 (x : nat) (m : nat) : (term10 x m) = True.
Proof. exact (TRANS (@lem88986 x m) (@lem88990)). Qed.
Lemma lem88992 (x : nat) : (term14 x) = term9.
Proof. exact (fun_ext (fun m : nat => @lem88991 x m)). Qed.
Lemma lem88993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88994 (x : nat) : (term15 x) = term11.
Proof. exact (MK_COMB (@lem88993) (@lem88992 x)). Qed.
Lemma lem88996 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem88997 (t : Prop) : (term13 t) = t.
Proof. exact (@lem88996 nat t). Qed.
Lemma lem88998 : term11 = True.
Proof. exact (@lem88997 True). Qed.
Lemma lem88999 (x : nat) : (term15 x) = True.
Proof. exact (TRANS (@lem88994 x) (@lem88998)). Qed.
Lemma lem89000 : term16 = term9.
Proof. exact (fun_ext (fun x : nat => @lem88999 x)). Qed.
Lemma lem89001 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89002 : term17 = term11.
Proof. exact (MK_COMB (@lem89001) (@lem89000)). Qed.
Lemma lem89004 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem89005 (t : Prop) : (term13 t) = t.
Proof. exact (@lem89004 nat t). Qed.
Lemma lem89006 : term11 = True.
Proof. exact (@lem89005 True). Qed.
Lemma lem89007 : term17 = True.
Proof. exact (TRANS (@lem89002) (@lem89006)). Qed.
Lemma lem89008 : True = term17.
Proof. exact (SYM (@lem89007)). Qed.
Lemma lem89009 : term17.
Proof. exact (EQ_MP (@lem89008) (@lem0)). Qed.
