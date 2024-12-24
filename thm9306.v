Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm9306_term_abbrevs.
Require Import SELECT_AX_spec.
Require Import thm32_spec.
Require Import thm9232_spec.
Require Import thm9233_spec.
Lemma lem9262 {A : Type'} (x : A -> Prop) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem9263 {A : Type'} (x : A -> Prop) : (term2 A x) = (term2 A x).
Proof. exact (eq_refl (term2 A x)). Qed.
Lemma lem9264 {A : Type'} (x : A -> Prop) : ((ex x) = (term0 A x)) = ((ex x) = (term1 A x)).
Proof. exact (MK_COMB (@lem9263 A x) (@lem9262 A x)). Qed.
Lemma lem9265 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem9264 A x)). Qed.
Lemma lem9266 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem9267 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (MK_COMB (@lem9266 A) (@lem9265 A)). Qed.
Lemma lem9268 {A : Type'} : (term6 A) = (term5 A).
Proof. exact (SYM (@lem9267 A)). Qed.
Lemma lem9270 {A B : Type'} (t : A -> B) : t = (term7 A B t).
Proof. exact (EQ_MP (@lem9233 A B t) (@lem9232 A B t)). Qed.
Lemma lem9271 {A : Type'} (t : A -> Prop) : t = (term8 A t).
Proof. exact (@lem9270 A Prop t). Qed.
Lemma lem9272 {A : Type'} (P : A -> Prop) : P = (term8 A P).
Proof. exact (@lem9271 A P). Qed.
Lemma lem9273 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem9274 {A : Type'} (P : A -> Prop) : (ex P) = (term9 A P).
Proof. exact (MK_COMB (@lem9273 A) (@lem9272 A P)). Qed.
Lemma lem9275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9276 {A : Type'} (P : A -> Prop) : (term2 A P) = (term10 A P).
Proof. exact (MK_COMB (@lem9275) (@lem9274 A P)). Qed.
Lemma lem9277 {A : Type'} (P : A -> Prop) : (term1 A P) = (term1 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem9278 {A : Type'} (P : A -> Prop) : ((ex P) = (term1 A P)) = ((term9 A P) = (term1 A P)).
Proof. exact (MK_COMB (@lem9276 A P) (@lem9277 A P)). Qed.
Lemma lem9279 {A : Type'} (P : A -> Prop) : ((term9 A P) = (term1 A P)) = ((ex P) = (term1 A P)).
Proof. exact (SYM (@lem9278 A P)). Qed.
Lemma lem9280 {A : Type'} (P : A -> Prop) (h1 : term9 A P) : term9 A P.
Proof. exact (h1). Qed.
Lemma lem9281 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem9282 {A : Type'} (P : A -> Prop) : term11 A P.
Proof. exact (@lem9221 A P). Qed.
Lemma lem9283 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (eq_refl (term11 A P)). Qed.
Lemma lem9284 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (EQ_MP (@lem9283 A P) (@lem9282 A P)). Qed.
Lemma lem9285 {A : Type'} (P : A -> Prop) (x : A) : term13 A P x.
Proof. exact (@lem9284 A P x). Qed.
Lemma lem9286 {A : Type'} (x : A) (P : A -> Prop) : (term13 A P x) = (term14 A x P).
Proof. exact (eq_refl (term13 A P x)). Qed.
Lemma lem9289 {A : Type'} (x : A) (P : A -> Prop) : term14 A x P.
Proof. exact (EQ_MP (@lem9286 A x P) (@lem9285 A P x)). Qed.
Lemma lem9290 {A : Type'} (x : A) (P : A -> Prop) : term14 A x P.
Proof. exact (@lem9289 A x P). Qed.
Lemma lem9291 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term1 A P.
Proof. exact (@lem9290 A x P (@lem9281 A P x h1)). Qed.
Lemma lem9292 {A : Type'} (P : A -> Prop) (h1 : term9 A P) : term1 A P.
Proof. exact (ex_elim (@lem9280 A P h1) (fun x : A => fun h0 : term8 A P x => @lem9291 A P x h0)). Qed.
Lemma lem9293 {A : Type'} (P : A -> Prop) : term15 A P.
Proof. exact (fun h0 : term9 A P => @lem9292 A P h0). Qed.
Lemma lem9294 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem9295 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term9 A P.
Proof. exact (ex_intro (term8 A P) (@ε A P) (@lem9294 A P h1)). Qed.
Lemma lem9296 {A : Type'} (P : A -> Prop) : term16 A P.
Proof. exact (fun h0 : term1 A P => @lem9295 A P h0). Qed.
Lemma lem9297 {A : Type'} (P : A -> Prop) : term17 A P.
Proof. exact (conj (@lem9293 A P) (@lem9296 A P)). Qed.
Lemma lem9298 {A : Type'} (P : A -> Prop) : (term17 A P) = ((term9 A P) = (term1 A P)).
Proof. exact (@lem32 (term9 A P) (term1 A P)). Qed.
Lemma lem9299 {A : Type'} (P : A -> Prop) : (term9 A P) = (term1 A P).
Proof. exact (EQ_MP (@lem9298 A P) (@lem9297 A P)). Qed.
Lemma lem9300 {A : Type'} (P : A -> Prop) : (ex P) = (term1 A P).
Proof. exact (EQ_MP (@lem9279 A P) (@lem9299 A P)). Qed.
Lemma lem9305 {A : Type'} : term6 A.
Proof. exact (fun P : A -> Prop => @lem9300 A P). Qed.
Lemma lem9306 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem9268 A) (@lem9305 A)). Qed.
