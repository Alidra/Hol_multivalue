Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TRIV_OR_FORALL_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem6219 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem6220 {A : Type'} (P : Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem6221 {A : Type'} (Q : Prop) (h1 : term1 A Q) : term1 A Q.
Proof. exact (h1). Qed.
Lemma lem6222 {A : Type'} (_281 : A) (P : Prop) (h1 : term1 A P) : term2 A P _281.
Proof. exact (@lem6220 A P h1 _281). Qed.
Lemma lem6223 {A : Type'} (_281 : A) (P : Prop) : (term2 A P _281) = P.
Proof. exact (eq_refl (term2 A P _281)). Qed.
Lemma lem6224 {A : Type'} (P : Prop) (h1 : term1 A P) : P.
Proof. exact (EQ_MP (@lem6223 A (@el A) P) (@lem6222 A (@el A) P h1)). Qed.
Lemma lem6228 {A : Type'} (Q : Prop) (P : Prop) (h1 : term1 A P) : P \/ Q.
Proof. exact (or_intro1 (@lem6224 A P h1) Q). Qed.
Lemma lem6232 {A : Type'} (Q : Prop) (P : Prop) (h1 : term1 A P) : (term1 A P) = (P \/ Q).
Proof. exact (prop_ext (fun h2 : term1 A P => @lem6228 A Q P h1) (fun h2 : P \/ Q => @lem6220 A P h1)). Qed.
Lemma lem6233 {A : Type'} (Q : Prop) (P : Prop) (h1 : term1 A P) : P \/ Q.
Proof. exact (EQ_MP (@lem6232 A Q P h1) (@lem6220 A P h1)). Qed.
Lemma lem6234 {A : Type'} (_283 : A) (Q : Prop) (h1 : term1 A Q) : term2 A Q _283.
Proof. exact (@lem6221 A Q h1 _283). Qed.
Lemma lem6235 {A : Type'} (_283 : A) (Q : Prop) : (term2 A Q _283) = Q.
Proof. exact (eq_refl (term2 A Q _283)). Qed.
Lemma lem6236 {A : Type'} (Q : Prop) (h1 : term1 A Q) : Q.
Proof. exact (EQ_MP (@lem6235 A (@el A) Q) (@lem6234 A (@el A) Q h1)). Qed.
Lemma lem6243 {A : Type'} (P : Prop) (Q : Prop) (h1 : term1 A Q) : P \/ Q.
Proof. exact (or_intro2 P (@lem6236 A Q h1)). Qed.
Lemma lem6247 {A : Type'} (P : Prop) (Q : Prop) (h1 : term1 A Q) : (term1 A Q) = (P \/ Q).
Proof. exact (prop_ext (fun h2 : term1 A Q => @lem6243 A P Q h1) (fun h2 : P \/ Q => @lem6221 A Q h1)). Qed.
Lemma lem6248 {A : Type'} (P : Prop) (Q : Prop) (h1 : term1 A Q) : P \/ Q.
Proof. exact (EQ_MP (@lem6247 A P Q h1) (@lem6221 A Q h1)). Qed.
Lemma lem6249 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : P \/ Q.
Proof. exact (or_elim (@lem6219 A P Q h1) (fun h0 : term1 A P => @lem6233 A Q P h0) (fun h0 : term1 A Q => @lem6248 A P Q h0)). Qed.
Lemma lem6254 {A : Type'} (P : Prop) (Q : Prop) (h1 : term0 A P Q) : term3 A P Q.
Proof. exact (fun x : A => @lem6249 A P Q h1). Qed.
Lemma lem6255 {A : Type'} (P : Prop) (Q : Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem6254 A P Q h0). Qed.
Lemma lem6256 {A : Type'} (P : Prop) (Q : Prop) (h1 : term3 A P Q) : term3 A P Q.
Proof. exact (h1). Qed.
Lemma lem6257 {A : Type'} (_286 : A) (P : Prop) (Q : Prop) (h1 : term3 A P Q) : term5 A P Q _286.
Proof. exact (@lem6256 A P Q h1 _286). Qed.
Lemma lem6258 {A : Type'} (_286 : A) (P : Prop) (Q : Prop) : (term5 A P Q _286) = (P \/ Q).
Proof. exact (eq_refl (term5 A P Q _286)). Qed.
Lemma lem6259 {A : Type'} (P : Prop) (Q : Prop) (h1 : term3 A P Q) : P \/ Q.
Proof. exact (EQ_MP (@lem6258 A (@el A) P Q) (@lem6257 A (@el A) P Q h1)). Qed.
Lemma lem6260 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem6261 (Q : Prop) (h1 : Q) : Q.
Proof. exact (h1). Qed.
Lemma lem6269 {A : Type'} (P : Prop) (h1 : P) : term1 A P.
Proof. exact (fun x : A => @lem6260 P h1). Qed.
Lemma lem6270 {A : Type'} (Q : Prop) (P : Prop) (h1 : P) : term0 A P Q.
Proof. exact (or_intro1 (@lem6269 A P h1) (term1 A Q)). Qed.
Lemma lem6281 {A : Type'} (Q : Prop) (h1 : Q) : term1 A Q.
Proof. exact (fun x : A => @lem6261 Q h1). Qed.
Lemma lem6282 {A : Type'} (P : Prop) (Q : Prop) (h1 : Q) : term0 A P Q.
Proof. exact (or_intro2 (term1 A P) (@lem6281 A Q h1)). Qed.
Lemma lem6283 {A : Type'} (P : Prop) (Q : Prop) (h1 : term3 A P Q) : term0 A P Q.
Proof. exact (or_elim (@lem6259 A P Q h1) (fun h0 : P => @lem6270 A Q P h0) (fun h0 : Q => @lem6282 A P Q h0)). Qed.
Lemma lem6287 {A : Type'} (P : Prop) (Q : Prop) (h1 : term3 A P Q) : (term3 A P Q) = (term0 A P Q).
Proof. exact (prop_ext (fun h2 : term3 A P Q => @lem6283 A P Q h1) (fun h2 : term0 A P Q => @lem6256 A P Q h1)). Qed.
Lemma lem6288 {A : Type'} (P : Prop) (Q : Prop) (h1 : term3 A P Q) : term0 A P Q.
Proof. exact (EQ_MP (@lem6287 A P Q h1) (@lem6256 A P Q h1)). Qed.
Lemma lem6289 {A : Type'} (P : Prop) (Q : Prop) : term6 A P Q.
Proof. exact (fun h0 : term3 A P Q => @lem6288 A P Q h0). Qed.
Lemma lem6290 {A : Type'} (P : Prop) (Q : Prop) : term7 A P Q.
Proof. exact (conj (@lem6255 A P Q) (@lem6289 A P Q)). Qed.
Lemma lem6291 {A : Type'} (P : Prop) (Q : Prop) : (term7 A P Q) = ((term0 A P Q) = (term3 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term3 A P Q)). Qed.
Lemma lem6292 {A : Type'} (P : Prop) (Q : Prop) : (term0 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem6291 A P Q) (@lem6290 A P Q)). Qed.
Lemma lem6297 {A : Type'} (P : Prop) : term8 A P.
Proof. exact (fun Q : Prop => @lem6292 A P Q). Qed.
Lemma lem6302 {A : Type'} : term9 A.
Proof. exact (fun P : Prop => @lem6297 A P). Qed.
