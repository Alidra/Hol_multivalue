Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TRIV_EXISTS_IMP_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem6936 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem6937 {A : Type'} (P : Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem6938 (P : Prop) (Q : Prop) (h1 : P -> Q) : P -> Q.
Proof. exact (h1). Qed.
Lemma lem6962 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6963 (P : Prop) (Q : Prop) (h1 : P) (h2 : P -> Q) : Q.
Proof. exact (@lem6938 P Q h2 (@lem6962 P h1)). Qed.
Lemma lem6964 {A : Type'} (_369 : A) (P : Prop) (h1 : term1 A P) : term2 A P _369.
Proof. exact (@lem6937 A P h1 _369). Qed.
Lemma lem6965 {A : Type'} (_369 : A) (P : Prop) : (term2 A P _369) = P.
Proof. exact (eq_refl (term2 A P _369)). Qed.
Lemma lem6966 {A : Type'} (P : Prop) (h1 : term1 A P) : P.
Proof. exact (EQ_MP (@lem6965 A (@el A) P) (@lem6964 A (@el A) P h1)). Qed.
Lemma lem6970 {A : Type'} (P : Prop) (h1 : term1 A P) : (term1 A P) = P.
Proof. exact (prop_ext (fun h2 : term1 A P => @lem6966 A P h1) (fun h2 : P => @lem6937 A P h1)). Qed.
Lemma lem6971 {A : Type'} (P : Prop) (h1 : term1 A P) : P.
Proof. exact (EQ_MP (@lem6970 A P h1) (@lem6937 A P h1)). Qed.
Lemma lem6980 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : P -> Q) : term3 A Q.
Proof. exact (ex_intro (term4 A Q) (@el A) (@lem6963 P Q h1 h2)). Qed.
Lemma lem6981 {A : Type'} (P : Prop) (Q : Prop) (h1 : term1 A P) (h2 : P -> Q) : P = (term3 A Q).
Proof. exact (prop_ext (fun h3 : P => @lem6980 A P Q h3 h2) (fun h3 : term3 A Q => @lem6971 A P h1)). Qed.
Lemma lem6982 {A : Type'} (P : Prop) (Q : Prop) (h1 : term1 A P) (h2 : P -> Q) : term3 A Q.
Proof. exact (EQ_MP (@lem6981 A P Q h1 h2) (@lem6971 A P h1)). Qed.
Lemma lem6983 {A : Type'} (P : Prop) (Q : Prop) (h1 : term1 A P) (h2 : term0 A P Q) : term3 A Q.
Proof. exact (ex_elim (@lem6936 A P Q h2) (fun x : A => fun h0 : term5 A P Q x => @lem6982 A P Q h1 h0)). Qed.
Lemma lem6984 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term6 A P Q.
Proof. exact (fun h0 : term1 A P => @lem6983 A P Q h0 h1). Qed.
Lemma lem6985 {A : Type'} (P : Prop) (Q : Prop) : term7 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem6984 A P Q h0). Qed.
Lemma lem6986 {A : Type'} (P : Prop) (Q : Prop) (h1 : term6 A P Q) : term6 A P Q.
Proof. exact (h1). Qed.
Lemma lem6987 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6988 {A : Type'} (P : Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem6989 {A : Type'} (P : Prop) (Q : Prop) (h1 : term1 A P) (h2 : term6 A P Q) : term3 A Q.
Proof. exact (@lem6986 A P Q h2 (@lem6988 A P h1)). Qed.
Lemma lem6994 {A : Type'} (P : Prop) (h1 : P) : term1 A P.
Proof. exact (fun x : A => @lem6987 P h1). Qed.
Lemma lem6995 (Q : Prop) (h1 : Q) : Q.
Proof. exact (h1). Qed.
Lemma lem6996 {A : Type'} (P : Prop) (Q : Prop) (h1 : term1 A P) (h2 : term6 A P Q) : Q.
Proof. exact (ex_elim (@lem6989 A P Q h1 h2) (fun x : A => fun h0 : term4 A Q x => @lem6995 Q h0)). Qed.
Lemma lem6997 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : term6 A P Q) : (term1 A P) = Q.
Proof. exact (prop_ext (fun h3 : term1 A P => @lem6996 A P Q h3 h2) (fun h3 : Q => @lem6994 A P h1)). Qed.
Lemma lem6998 {A : Type'} (P : Prop) (Q : Prop) (h1 : P) (h2 : term6 A P Q) : Q.
Proof. exact (EQ_MP (@lem6997 A P Q h1 h2) (@lem6994 A P h1)). Qed.
Lemma lem6999 {A : Type'} (P : Prop) (Q : Prop) (h1 : term6 A P Q) : P -> Q.
Proof. exact (fun h0 : P => @lem6998 A P Q h0 h1). Qed.
Lemma lem7000 {A : Type'} (P : Prop) (Q : Prop) (h1 : term6 A P Q) : term0 A P Q.
Proof. exact (ex_intro (term5 A P Q) (@el A) (@lem6999 A P Q h1)). Qed.
Lemma lem7001 {A : Type'} (P : Prop) (Q : Prop) : term8 A P Q.
Proof. exact (fun h0 : term6 A P Q => @lem7000 A P Q h0). Qed.
Lemma lem7002 {A : Type'} (P : Prop) (Q : Prop) : term9 A P Q.
Proof. exact (conj (@lem6985 A P Q) (@lem7001 A P Q)). Qed.
Lemma lem7003 {A : Type'} (P : Prop) (Q : Prop) : (term9 A P Q) = ((term0 A P Q) = (term6 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term6 A P Q)). Qed.
Lemma lem7004 {A : Type'} (P : Prop) (Q : Prop) : (term0 A P Q) = (term6 A P Q).
Proof. exact (EQ_MP (@lem7003 A P Q) (@lem7002 A P Q)). Qed.
Lemma lem7009 {A : Type'} (P : Prop) : term10 A P.
Proof. exact (fun Q : Prop => @lem7004 A P Q). Qed.
Lemma lem7014 {A : Type'} : term11 A.
Proof. exact (fun P : Prop => @lem7009 A P). Qed.
