Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_REC_num_term_abbrevs.
Require Import WF_num_spec.
Require Import thm339314_spec.
Lemma lem365142 {A B : Type'} (lt2 : type1402 A) : term0 A B lt2.
Proof. exact (fun h0 : @WF A lt2 => @lem339314 A B lt2 h0). Qed.
Lemma lem365143 {B : Type'} (lt2 : type1605) : term1 B lt2.
Proof. exact (@lem365142 nat B lt2). Qed.
Lemma lem365144 {B : Type'} : term2 B.
Proof. exact (@lem365143 B Peano.lt). Qed.
Lemma lem365145 {B : Type'} : term3 B.
Proof. exact (@lem365144 B (@lem365140)). Qed.
Lemma lem365146 {B : Type'} (H : type972 B) : term4 B H.
Proof. exact (@lem365145 B H). Qed.
Lemma lem365147 {B : Type'} (H : type972 B) : (term4 B H) = (term5 B H).
Proof. exact (eq_refl (term4 B H)). Qed.
Lemma lem365150 {B : Type'} (H : type972 B) : term5 B H.
Proof. exact (EQ_MP (@lem365147 B H) (@lem365146 B H)). Qed.
Lemma lem365151 {A : Type'} (H : type972 A) : term5 A H.
Proof. exact (@lem365150 A H). Qed.
Lemma lem365156 {A : Type'} : term3 A.
Proof. exact (fun H : type972 A => @lem365151 A H). Qed.
