Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LTE_CASES_term_abbrevs.
Require Import DISJ_SYM_spec.
Require Import LET_CASES_spec.
Lemma lem96918 (t1 : Prop) : term0 t1.
Proof. exact (@lem720 t1). Qed.
Lemma lem96919 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem96920 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem96919 t1) (@lem96918 t1)). Qed.
Lemma lem96921 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem96920 t1 t2). Qed.
Lemma lem96922 (t2 : Prop) (t1 : Prop) : (term2 t1 t2) = ((t1 \/ t2) = (t2 \/ t1)).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem96935 (t2 : Prop) (t1 : Prop) : (t1 \/ t2) = (t2 \/ t1).
Proof. exact (EQ_MP (@lem96922 t2 t1) (@lem96921 t1 t2)). Qed.
Lemma lem96936 (m : nat) (n : nat) : (term3 n m) = (term4 m n).
Proof. exact (@lem96935 (Peano.le n m) (Peano.lt m n)). Qed.
Lemma lem96937 (m : nat) : (term5 m) = (term6 m).
Proof. exact (fun_ext (fun n : nat => @lem96936 m n)). Qed.
Lemma lem96938 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96939 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem96938) (@lem96937 m)). Qed.
Lemma lem96940 : term9 = term10.
Proof. exact (fun_ext (fun m : nat => @lem96939 m)). Qed.
Lemma lem96941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96942 : term11 = term12.
Proof. exact (MK_COMB (@lem96941) (@lem96940)). Qed.
Lemma lem96943 : term12 = term11.
Proof. exact (SYM (@lem96942)). Qed.
Lemma lem96944 (m : nat) : term13 m.
Proof. exact (@lem96917 m). Qed.
Lemma lem96945 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem96946 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem96945 m) (@lem96944 m)). Qed.
Lemma lem96947 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem96946 m n). Qed.
Lemma lem96948 (n : nat) (m : nat) : (term15 m n) = (term4 n m).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem96951 (n : nat) (m : nat) : term4 n m.
Proof. exact (EQ_MP (@lem96948 n m) (@lem96947 m n)). Qed.
Lemma lem96952 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem96951 m n). Qed.
Lemma lem96957 (m : nat) : term8 m.
Proof. exact (fun n : nat => @lem96952 m n). Qed.
Lemma lem96962 : term12.
Proof. exact (fun m : nat => @lem96957 m). Qed.
Lemma lem96963 : term11.
Proof. exact (EQ_MP (@lem96943) (@lem96962)). Qed.
