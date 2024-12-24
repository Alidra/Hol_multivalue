Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ZCONSTR_term_abbrevs.
Lemma lem1057845 {A : Type'} : (@ZCONSTR A) = (term0 A).
Proof. exact (@ZCONSTR_def A). Qed.
Lemma lem1057846 (_17403 : nat) : _17403 = _17403.
Proof. exact (eq_refl _17403). Qed.
Lemma lem1057847 {A : Type'} (_17403 : nat) : (@ZCONSTR A _17403) = (term1 A _17403).
Proof. exact (MK_COMB (@lem1057845 A) (@lem1057846 _17403)). Qed.
Lemma lem1057848 {A : Type'} (_17403 : nat) : (term1 A _17403) = (term2 A _17403).
Proof. exact (eq_refl (term1 A _17403)). Qed.
Lemma lem1057849 {A : Type'} (_17403 : nat) : (@ZCONSTR A _17403) = (term2 A _17403).
Proof. exact (TRANS (@lem1057847 A _17403) (@lem1057848 A _17403)). Qed.
Lemma lem1057850 {A : Type'} (_17404 : A) : _17404 = _17404.
Proof. exact (eq_refl _17404). Qed.
Lemma lem1057851 {A : Type'} (_17403 : nat) (_17404 : A) : (@ZCONSTR A _17403 _17404) = (term3 A _17403 _17404).
Proof. exact (MK_COMB (@lem1057849 A _17403) (@lem1057850 A _17404)). Qed.
Lemma lem1057852 {A : Type'} (_17403 : nat) (_17404 : A) : (term3 A _17403 _17404) = (term4 A _17403 _17404).
Proof. exact (eq_refl (term3 A _17403 _17404)). Qed.
Lemma lem1057853 {A : Type'} (_17403 : nat) (_17404 : A) : (@ZCONSTR A _17403 _17404) = (term4 A _17403 _17404).
Proof. exact (TRANS (@lem1057851 A _17403 _17404) (@lem1057852 A _17403 _17404)). Qed.
Lemma lem1057854 {A : Type'} (_17405 : type1600 A) : _17405 = _17405.
Proof. exact (eq_refl _17405). Qed.
Lemma lem1057855 {A : Type'} (_17403 : nat) (_17404 : A) (_17405 : type1600 A) : (@ZCONSTR A _17403 _17404 _17405) = (term5 A _17403 _17404 _17405).
Proof. exact (MK_COMB (@lem1057853 A _17403 _17404) (@lem1057854 A _17405)). Qed.
Lemma lem1057856 {A : Type'} (_17403 : nat) (_17404 : A) (_17405 : type1600 A) : (term5 A _17403 _17404 _17405) = (term6 A _17403 _17404 _17405).
Proof. exact (eq_refl (term5 A _17403 _17404 _17405)). Qed.
Lemma lem1057857 {A : Type'} (_17403 : nat) (_17404 : A) (_17405 : type1600 A) : (@ZCONSTR A _17403 _17404 _17405) = (term6 A _17403 _17404 _17405).
Proof. exact (TRANS (@lem1057855 A _17403 _17404 _17405) (@lem1057856 A _17403 _17404 _17405)). Qed.
Lemma lem1057858 {A : Type'} (_17403 : nat) (_17404 : A) : term7 A _17403 _17404.
Proof. exact (fun _17405 : type1600 A => @lem1057857 A _17403 _17404 _17405). Qed.
Lemma lem1057859 {A : Type'} (_17403 : nat) : term8 A _17403.
Proof. exact (fun _17404 : A => @lem1057858 A _17403 _17404). Qed.
Lemma lem1057860 {A : Type'} : term9 A.
Proof. exact (fun _17403 : nat => @lem1057859 A _17403). Qed.
Lemma lem1057861 {A : Type'} (_17403 : nat) : term10 A _17403.
Proof. exact (@lem1057860 A _17403). Qed.
Lemma lem1057862 {A : Type'} (_17403 : nat) : (term10 A _17403) = (term8 A _17403).
Proof. exact (eq_refl (term10 A _17403)). Qed.
Lemma lem1057863 {A : Type'} (_17403 : nat) : term8 A _17403.
Proof. exact (EQ_MP (@lem1057862 A _17403) (@lem1057861 A _17403)). Qed.
Lemma lem1057864 {A : Type'} (_17403 : nat) (_17404 : A) : term11 A _17403 _17404.
Proof. exact (@lem1057863 A _17403 _17404). Qed.
Lemma lem1057865 {A : Type'} (_17403 : nat) (_17404 : A) : (term11 A _17403 _17404) = (term7 A _17403 _17404).
Proof. exact (eq_refl (term11 A _17403 _17404)). Qed.
Lemma lem1057866 {A : Type'} (_17403 : nat) (_17404 : A) : term7 A _17403 _17404.
Proof. exact (EQ_MP (@lem1057865 A _17403 _17404) (@lem1057864 A _17403 _17404)). Qed.
Lemma lem1057867 {A : Type'} (_17403 : nat) (_17404 : A) (_17405 : type1600 A) : term12 A _17403 _17404 _17405.
Proof. exact (@lem1057866 A _17403 _17404 _17405). Qed.
Lemma lem1057868 {A : Type'} (_17403 : nat) (_17404 : A) (_17405 : type1600 A) : (term12 A _17403 _17404 _17405) = ((@ZCONSTR A _17403 _17404 _17405) = (term6 A _17403 _17404 _17405)).
Proof. exact (eq_refl (term12 A _17403 _17404 _17405)). Qed.
Lemma lem1057869 {A : Type'} (_17403 : nat) (_17404 : A) (_17405 : type1600 A) : (@ZCONSTR A _17403 _17404 _17405) = (term6 A _17403 _17404 _17405).
Proof. exact (EQ_MP (@lem1057868 A _17403 _17404 _17405) (@lem1057867 A _17403 _17404 _17405)). Qed.
Lemma lem1057925 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (@ZCONSTR A c i r) = (term6 A c i r).
Proof. exact (@lem1057869 A c i r). Qed.
Lemma lem1057926 {A : Type'} (c : nat) (i : A) : term7 A c i.
Proof. exact (fun r : type1600 A => @lem1057925 A c i r). Qed.
Lemma lem1057927 {A : Type'} (c : nat) : term8 A c.
Proof. exact (fun i : A => @lem1057926 A c i). Qed.
Lemma lem1057928 {A : Type'} : term9 A.
Proof. exact (fun c : nat => @lem1057927 A c). Qed.
