Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_AND_FORALL_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5177 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5179 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term1 A P.
Proof. exact (proj1 (@lem5177 A P Q h1)). Qed.
Lemma lem5180 {A : Type'} (_127 : A) (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term2 A P _127.
Proof. exact (@lem5179 A P Q h1 _127). Qed.
Lemma lem5181 {A : Type'} (P : A -> Prop) (_127 : A) : (term2 A P _127) = (P _127).
Proof. exact (eq_refl (term2 A P _127)). Qed.
Lemma lem5182 {A : Type'} (_127 : A) (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : P _127.
Proof. exact (EQ_MP (@lem5181 A P _127) (@lem5180 A _127 P Q h1)). Qed.
Lemma lem5183 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : P x.
Proof. exact (@lem5182 A x P Q h1). Qed.
Lemma lem5190 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem5177 A P Q h1). Qed.
Lemma lem5191 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : Q.
Proof. exact (proj2 (@lem5190 A P Q h1)). Qed.
Lemma lem5193 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term3 A P x Q.
Proof. exact (conj (@lem5183 A x P Q h1) (@lem5191 A P Q h1)). Qed.
Lemma lem5198 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term0 A P Q) : term4 A P Q.
Proof. exact (fun x : A => @lem5193 A x P Q h1). Qed.
Lemma lem5199 {A : Type'} (P : A -> Prop) (Q : Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5198 A P Q h0). Qed.
Lemma lem5200 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (h1). Qed.
Lemma lem5201 {A : Type'} (_128 : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term6 A P Q _128.
Proof. exact (@lem5200 A P Q h1 _128). Qed.
Lemma lem5202 {A : Type'} (P : A -> Prop) (_128 : A) (Q : Prop) : (term6 A P Q _128) = (term3 A P _128 Q).
Proof. exact (eq_refl (term6 A P Q _128)). Qed.
Lemma lem5203 {A : Type'} (_128 : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term3 A P _128 Q.
Proof. exact (EQ_MP (@lem5202 A P _128 Q) (@lem5201 A _128 P Q h1)). Qed.
Lemma lem5205 {A : Type'} (_128 : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : P _128.
Proof. exact (proj1 (@lem5203 A _128 P Q h1)). Qed.
Lemma lem5206 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : P x.
Proof. exact (@lem5205 A x P Q h1). Qed.
Lemma lem5212 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (@lem5200 A P Q h1). Qed.
Lemma lem5213 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : (term4 A P Q) = (P x).
Proof. exact (prop_ext (fun h2 : term4 A P Q => @lem5206 A x P Q h1) (fun h2 : P x => @lem5212 A P Q h1)). Qed.
Lemma lem5214 {A : Type'} (x : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : P x.
Proof. exact (EQ_MP (@lem5213 A x P Q h1) (@lem5212 A P Q h1)). Qed.
Lemma lem5219 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term1 A P.
Proof. exact (fun x : A => @lem5214 A x P Q h1). Qed.
Lemma lem5220 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (@lem5200 A P Q h1). Qed.
Lemma lem5221 {A : Type'} (_129 : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term6 A P Q _129.
Proof. exact (@lem5220 A P Q h1 _129). Qed.
Lemma lem5222 {A : Type'} (P : A -> Prop) (_129 : A) (Q : Prop) : (term6 A P Q _129) = (term3 A P _129 Q).
Proof. exact (eq_refl (term6 A P Q _129)). Qed.
Lemma lem5223 {A : Type'} (_129 : A) (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term3 A P _129 Q.
Proof. exact (EQ_MP (@lem5222 A P _129 Q) (@lem5221 A _129 P Q h1)). Qed.
Lemma lem5224 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : Q.
Proof. exact (proj2 (@lem5223 A (@el A) P Q h1)). Qed.
Lemma lem5229 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : (term4 A P Q) = Q.
Proof. exact (prop_ext (fun h2 : term4 A P Q => @lem5224 A P Q h1) (fun h2 : Q => @lem5220 A P Q h1)). Qed.
Lemma lem5230 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : Q.
Proof. exact (EQ_MP (@lem5229 A P Q h1) (@lem5220 A P Q h1)). Qed.
Lemma lem5231 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : term4 A P Q) : term0 A P Q.
Proof. exact (conj (@lem5219 A P Q h1) (@lem5230 A P Q h1)). Qed.
Lemma lem5232 {A : Type'} (P : A -> Prop) (Q : Prop) : term7 A P Q.
Proof. exact (fun h0 : term4 A P Q => @lem5231 A P Q h0). Qed.
Lemma lem5233 {A : Type'} (P : A -> Prop) (Q : Prop) : term5 A P Q.
Proof. exact (@lem5199 A P Q). Qed.
Lemma lem5234 {A : Type'} (P : A -> Prop) (Q : Prop) : term8 A P Q.
Proof. exact (conj (@lem5233 A P Q) (@lem5232 A P Q)). Qed.
Lemma lem5235 {A : Type'} (P : A -> Prop) (Q : Prop) : (term8 A P Q) = ((term0 A P Q) = (term4 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term4 A P Q)). Qed.
Lemma lem5236 {A : Type'} (P : A -> Prop) (Q : Prop) : (term0 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem5235 A P Q) (@lem5234 A P Q)). Qed.
Lemma lem5241 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (fun Q : Prop => @lem5236 A P Q). Qed.
Lemma lem5246 {A : Type'} : term10 A.
Proof. exact (fun P : A -> Prop => @lem5241 A P). Qed.
Lemma lem5247 {A : Type'} : term10 A.
Proof. exact (@lem5246 A). Qed.
