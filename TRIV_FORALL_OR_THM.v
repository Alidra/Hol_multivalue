Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TRIV_FORALL_OR_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem6073 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem6074 {A : Type'} (_254 : A) (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term1 A P Q _254.
Proof. exact (@lem6073 A P Q h1 _254). Qed.
Lemma lem6075 {A : Type'} (_254 : A) (P : Prop) (Q : Prop) : (term1 A P Q _254) = (P \/ Q).
Proof. exact (eq_refl (term1 A P Q _254)). Qed.
Lemma lem6076 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : P \/ Q.
Proof. exact (EQ_MP (@lem6075 A (@el A) P Q) (@lem6074 A (@el A) P Q h1)). Qed.
Lemma lem6077 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6078 (Q : Prop) (h1 : Q) : Q.
Proof. exact (h1). Qed.
Lemma lem6086 {A : Type'} (P : Prop) (h1 : P) : term2 A P.
Proof. exact (fun x : A => @lem6077 P h1). Qed.
Lemma lem6087 {A : Type'} (Q : Prop) (P : Prop) (h1 : P) : term3 A P Q.
Proof. exact (or_intro1 (@lem6086 A P h1) (term2 A Q)). Qed.
Lemma lem6098 {A : Type'} (Q : Prop) (h1 : Q) : term2 A Q.
Proof. exact (fun x : A => @lem6078 Q h1). Qed.
Lemma lem6099 {A : Type'} (P : Prop) (Q : Prop) (h1 : Q) : term3 A P Q.
Proof. exact (or_intro2 (term2 A P) (@lem6098 A Q h1)). Qed.
Lemma lem6100 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term3 A P Q.
Proof. exact (or_elim (@lem6076 A P Q h1) (fun h0 : P => @lem6087 A Q P h0) (fun h0 : Q => @lem6099 A P Q h0)). Qed.
Lemma lem6104 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : (term0 A P Q) = (term3 A P Q).
Proof. exact (prop_ext (fun h2 : term0 A P Q => @lem6100 A P Q h1) (fun h2 : term3 A P Q => @lem6073 A P Q h1)). Qed.
Lemma lem6105 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term3 A P Q.
Proof. exact (EQ_MP (@lem6104 A P Q h1) (@lem6073 A P Q h1)). Qed.
Lemma lem6106 {A : Type'} (P : Prop) (Q : Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem6105 A P Q h0). Qed.
Lemma lem6107 {A : Type'} (P : Prop) (Q : Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (h1). Qed.
Lemma lem6108 {A : Type'} (P : Prop) (h1 : term2 A P) : term2 A P.
Proof. exact (h1). Qed.
Lemma lem6109 {A : Type'} (Q : Prop) (h1 : term2 A Q) : term2 A Q.
Proof. exact (h1). Qed.
Lemma lem6110 {A : Type'} (_258 : A) (P : Prop) (h1 : term2 A P) : term5 A P _258.
Proof. exact (@lem6108 A P h1 _258). Qed.
Lemma lem6111 {A : Type'} (_258 : A) (P : Prop) : (term5 A P _258) = P.
Proof. exact (eq_refl (term5 A P _258)). Qed.
Lemma lem6112 {A : Type'} (P : Prop) (h1 : term2 A P) : P.
Proof. exact (EQ_MP (@lem6111 A (@el A) P) (@lem6110 A (@el A) P h1)). Qed.
Lemma lem6116 {A : Type'} (Q : Prop) (P : Prop) (h1 : term2 A P) : P \/ Q.
Proof. exact (or_intro1 (@lem6112 A P h1) Q). Qed.
Lemma lem6120 {A : Type'} (Q : Prop) (P : Prop) (h1 : term2 A P) : (term2 A P) = (P \/ Q).
Proof. exact (prop_ext (fun h2 : term2 A P => @lem6116 A Q P h1) (fun h2 : P \/ Q => @lem6108 A P h1)). Qed.
Lemma lem6121 {A : Type'} (Q : Prop) (P : Prop) (h1 : term2 A P) : P \/ Q.
Proof. exact (EQ_MP (@lem6120 A Q P h1) (@lem6108 A P h1)). Qed.
Lemma lem6122 {A : Type'} (_260 : A) (Q : Prop) (h1 : term2 A Q) : term5 A Q _260.
Proof. exact (@lem6109 A Q h1 _260). Qed.
Lemma lem6123 {A : Type'} (_260 : A) (Q : Prop) : (term5 A Q _260) = Q.
Proof. exact (eq_refl (term5 A Q _260)). Qed.
Lemma lem6124 {A : Type'} (Q : Prop) (h1 : term2 A Q) : Q.
Proof. exact (EQ_MP (@lem6123 A (@el A) Q) (@lem6122 A (@el A) Q h1)). Qed.
Lemma lem6131 {A : Type'} (P : Prop) (Q : Prop) (h1 : term2 A Q) : P \/ Q.
Proof. exact (or_intro2 P (@lem6124 A Q h1)). Qed.
Lemma lem6135 {A : Type'} (P : Prop) (Q : Prop) (h1 : term2 A Q) : (term2 A Q) = (P \/ Q).
Proof. exact (prop_ext (fun h2 : term2 A Q => @lem6131 A P Q h1) (fun h2 : P \/ Q => @lem6109 A Q h1)). Qed.
Lemma lem6136 {A : Type'} (P : Prop) (Q : Prop) (h1 : term2 A Q) : P \/ Q.
Proof. exact (EQ_MP (@lem6135 A P Q h1) (@lem6109 A Q h1)). Qed.
Lemma lem6137 {A : Type'} (P : Prop) (Q : Prop) (h1 : term3 A P Q) : P \/ Q.
Proof. exact (or_elim (@lem6107 A P Q h1) (fun h0 : term2 A P => @lem6121 A Q P h0) (fun h0 : term2 A Q => @lem6136 A P Q h0)). Qed.
Lemma lem6142 {A : Type'} (P : Prop) (Q : Prop) (h1 : term3 A P Q) : term0 A P Q.
Proof. exact (fun x : A => @lem6137 A P Q h1). Qed.
Lemma lem6143 {A : Type'} (P : Prop) (Q : Prop) : term6 A P Q.
Proof. exact (fun h0 : term3 A P Q => @lem6142 A P Q h0). Qed.
Lemma lem6144 {A : Type'} (P : Prop) (Q : Prop) : term7 A P Q.
Proof. exact (conj (@lem6106 A P Q) (@lem6143 A P Q)). Qed.
Lemma lem6145 {A : Type'} (P : Prop) (Q : Prop) : (term7 A P Q) = ((term0 A P Q) = (term3 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term3 A P Q)). Qed.
Lemma lem6146 {A : Type'} (P : Prop) (Q : Prop) : (term0 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem6145 A P Q) (@lem6144 A P Q)). Qed.
Lemma lem6151 {A : Type'} (P : Prop) : term8 A P.
Proof. exact (fun Q : Prop => @lem6146 A P Q). Qed.
Lemma lem6156 {A : Type'} : term9 A.
Proof. exact (fun P : Prop => @lem6151 A P). Qed.
