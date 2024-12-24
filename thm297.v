Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm297_term_abbrevs.
Require Import thm32_spec.
Lemma lem240 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) (h1 : term0 _216 P Q) : term0 _216 P Q.
Proof. exact (h1). Qed.
Lemma lem241 {_216 : Type'} (P : _216 -> Prop) (h1 : term1 _216 P) : term1 _216 P.
Proof. exact (h1). Qed.
Lemma lem242 {_216 : Type'} (P : _216 -> Prop) (x : _216) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem243 {_216 : Type'} (_8 : _216) (P : _216 -> Prop) (Q : Prop) (h1 : term0 _216 P Q) : term2 _216 P Q _8.
Proof. exact (@lem240 _216 P Q h1 _8). Qed.
Lemma lem244 {_216 : Type'} (P : _216 -> Prop) (_8 : _216) (Q : Prop) : (term2 _216 P Q _8) = (term3 _216 P _8 Q).
Proof. exact (eq_refl (term2 _216 P Q _8)). Qed.
Lemma lem245 {_216 : Type'} (_8 : _216) (P : _216 -> Prop) (Q : Prop) (h1 : term0 _216 P Q) : term3 _216 P _8 Q.
Proof. exact (EQ_MP (@lem244 _216 P _8 Q) (@lem243 _216 _8 P Q h1)). Qed.
Lemma lem249 {_216 : Type'} (P : _216 -> Prop) (_8 : _216) (h1 : P _8) : P _8.
Proof. exact (h1). Qed.
Lemma lem250 {_216 : Type'} (Q : Prop) (P : _216 -> Prop) (_8 : _216) (h1 : term0 _216 P Q) (h2 : P _8) : Q.
Proof. exact (@lem245 _216 _8 P Q h1 (@lem249 _216 P _8 h2)). Qed.
Lemma lem251 {_216 : Type'} (P : _216 -> Prop) (x : _216) (h1 : P x) : P x.
Proof. exact (@lem242 _216 P x h1). Qed.
Lemma lem252 {_216 : Type'} (_8 : _216) (P : _216 -> Prop) (Q : Prop) (h1 : term0 _216 P Q) : term3 _216 P _8 Q.
Proof. exact (fun h0 : P _8 => @lem250 _216 Q P _8 h1 h0). Qed.
Lemma lem253 {_216 : Type'} (x : _216) (P : _216 -> Prop) (Q : Prop) (h1 : term0 _216 P Q) : term3 _216 P x Q.
Proof. exact (@lem252 _216 x P Q h1). Qed.
Lemma lem254 {_216 : Type'} (P : _216 -> Prop) (x : _216) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem255 {_216 : Type'} (Q : Prop) (P : _216 -> Prop) (x : _216) (h1 : term0 _216 P Q) (h2 : P x) : Q.
Proof. exact (@lem253 _216 x P Q h1 (@lem254 _216 P x h2)). Qed.
Lemma lem263 {_216 : Type'} (Q : Prop) (P : _216 -> Prop) (x : _216) (h1 : term0 _216 P Q) (h2 : P x) : (P x) = Q.
Proof. exact (prop_ext (fun h3 : P x => @lem255 _216 Q P x h1 h2) (fun h3 : Q => @lem251 _216 P x h2)). Qed.
Lemma lem264 {_216 : Type'} (Q : Prop) (P : _216 -> Prop) (x : _216) (h1 : term0 _216 P Q) (h2 : P x) : Q.
Proof. exact (EQ_MP (@lem263 _216 Q P x h1 h2) (@lem251 _216 P x h2)). Qed.
Lemma lem268 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) (h1 : term0 _216 P Q) : term0 _216 P Q.
Proof. exact (@lem240 _216 P Q h1). Qed.
Lemma lem269 {_216 : Type'} (Q : Prop) (P : _216 -> Prop) (x : _216) (h1 : term0 _216 P Q) (h2 : P x) : (term0 _216 P Q) = Q.
Proof. exact (prop_ext (fun h3 : term0 _216 P Q => @lem264 _216 Q P x h1 h2) (fun h3 : Q => @lem268 _216 P Q h1)). Qed.
Lemma lem270 {_216 : Type'} (Q : Prop) (P : _216 -> Prop) (x : _216) (h1 : term0 _216 P Q) (h2 : P x) : Q.
Proof. exact (EQ_MP (@lem269 _216 Q P x h1 h2) (@lem268 _216 P Q h1)). Qed.
Lemma lem271 {_216 : Type'} (P : _216 -> Prop) (h1 : term1 _216 P) : term1 _216 P.
Proof. exact (@lem241 _216 P h1). Qed.
Lemma lem272 {_216 : Type'} (Q : Prop) (P : _216 -> Prop) (h1 : term0 _216 P Q) (h2 : term1 _216 P) : Q.
Proof. exact (ex_elim (@lem271 _216 P h2) (fun x : _216 => fun h0 : term4 _216 P x => @lem270 _216 Q P x h1 h0)). Qed.
Lemma lem273 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) (h1 : term0 _216 P Q) : term5 _216 P Q.
Proof. exact (fun h0 : term1 _216 P => @lem272 _216 Q P h1 h0). Qed.
Lemma lem274 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) : term6 _216 P Q.
Proof. exact (fun h0 : term0 _216 P Q => @lem273 _216 P Q h0). Qed.
Lemma lem275 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) (h1 : term5 _216 P Q) : term5 _216 P Q.
Proof. exact (h1). Qed.
Lemma lem276 {_216 : Type'} (P : _216 -> Prop) (x : _216) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem277 {_216 : Type'} (P : _216 -> Prop) (h1 : term1 _216 P) : term1 _216 P.
Proof. exact (h1). Qed.
Lemma lem278 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) (h1 : term1 _216 P) (h2 : term5 _216 P Q) : Q.
Proof. exact (@lem275 _216 P Q h2 (@lem277 _216 P h1)). Qed.
Lemma lem279 {_216 : Type'} (P : _216 -> Prop) (x : _216) (h1 : P x) : P x.
Proof. exact (@lem276 _216 P x h1). Qed.
Lemma lem280 {_216 : Type'} (P : _216 -> Prop) (x : _216) (h1 : P x) : term1 _216 P.
Proof. exact (ex_intro (term4 _216 P) x (@lem279 _216 P x h1)). Qed.
Lemma lem281 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) (h1 : term1 _216 P) (h2 : term5 _216 P Q) : Q.
Proof. exact (@lem278 _216 P Q h1 h2). Qed.
Lemma lem285 {_216 : Type'} (x : _216) (P : _216 -> Prop) (Q : Prop) (h1 : P x) (h2 : term5 _216 P Q) : (term1 _216 P) = Q.
Proof. exact (prop_ext (fun h3 : term1 _216 P => @lem281 _216 P Q h3 h2) (fun h3 : Q => @lem280 _216 P x h1)). Qed.
Lemma lem286 {_216 : Type'} (x : _216) (P : _216 -> Prop) (Q : Prop) (h1 : P x) (h2 : term5 _216 P Q) : Q.
Proof. exact (EQ_MP (@lem285 _216 x P Q h1 h2) (@lem280 _216 P x h1)). Qed.
Lemma lem287 {_216 : Type'} (x : _216) (P : _216 -> Prop) (Q : Prop) (h1 : term5 _216 P Q) : term3 _216 P x Q.
Proof. exact (fun h0 : P x => @lem286 _216 x P Q h0 h1). Qed.
Lemma lem292 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) (h1 : term5 _216 P Q) : term0 _216 P Q.
Proof. exact (fun x : _216 => @lem287 _216 x P Q h1). Qed.
Lemma lem293 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) : term7 _216 P Q.
Proof. exact (fun h0 : term5 _216 P Q => @lem292 _216 P Q h0). Qed.
Lemma lem294 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) : term6 _216 P Q.
Proof. exact (@lem274 _216 P Q). Qed.
Lemma lem295 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) : term8 _216 P Q.
Proof. exact (conj (@lem294 _216 P Q) (@lem293 _216 P Q)). Qed.
Lemma lem296 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) : (term8 _216 P Q) = ((term0 _216 P Q) = (term5 _216 P Q)).
Proof. exact (@lem32 (term0 _216 P Q) (term5 _216 P Q)). Qed.
Lemma lem297 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) : (term0 _216 P Q) = (term5 _216 P Q).
Proof. exact (EQ_MP (@lem296 _216 P Q) (@lem295 _216 P Q)). Qed.
