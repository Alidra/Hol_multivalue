Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import bool_INDUCT_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem15251 (x : Prop) : term0 x.
Proof. exact (@lem9851 x). Qed.
Lemma lem15252 (x : Prop) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem15253 (x : Prop) : term1 x.
Proof. exact (EQ_MP (@lem15252 x) (@lem15251 x)). Qed.
Lemma lem15256 (P : Prop -> Prop) (h1 : term2 P) : term2 P.
Proof. exact (h1). Qed.
Lemma lem15257 (P : Prop -> Prop) (h1 : P True) : P True.
Proof. exact (h1). Qed.
Lemma lem15258 (P : Prop -> Prop) (h1 : P False) : P False.
Proof. exact (h1). Qed.
Lemma lem15261 (P : Prop -> Prop) : (P True) = ((P True) = True).
Proof. exact (@lem7 (P True)). Qed.
Lemma lem15264 (x : Prop) (h1 : x = True) : x = True.
Proof. exact (h1). Qed.
Lemma lem15265 (P : Prop -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem15266 (P : Prop -> Prop) (x : Prop) (h1 : x = True) : (P x) = (P True).
Proof. exact (MK_COMB (@lem15265 P) (@lem15264 x h1)). Qed.
Lemma lem15268 (P : Prop -> Prop) (h1 : P True) : (P True) = True.
Proof. exact (EQ_MP (@lem15261 P) (@lem15257 P h1)). Qed.
Lemma lem15269 (P : Prop -> Prop) (x : Prop) (h1 : P True) (h2 : x = True) : (P x) = True.
Proof. exact (TRANS (@lem15266 P x h2) (@lem15268 P h1)). Qed.
Lemma lem15270 (P : Prop -> Prop) (x : Prop) (h1 : P True) (h2 : x = True) : True = (P x).
Proof. exact (SYM (@lem15269 P x h1 h2)). Qed.
Lemma lem15271 (P : Prop -> Prop) (x : Prop) (h1 : P True) (h2 : x = True) : P x.
Proof. exact (EQ_MP (@lem15270 P x h1 h2) (@lem0)). Qed.
Lemma lem15272 (P : Prop -> Prop) : (P False) = ((P False) = True).
Proof. exact (@lem7 (P False)). Qed.
Lemma lem15277 (x : Prop) (h1 : x = False) : x = False.
Proof. exact (h1). Qed.
Lemma lem15278 (P : Prop -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem15279 (P : Prop -> Prop) (x : Prop) (h1 : x = False) : (P x) = (P False).
Proof. exact (MK_COMB (@lem15278 P) (@lem15277 x h1)). Qed.
Lemma lem15281 (P : Prop -> Prop) (h1 : P False) : (P False) = True.
Proof. exact (EQ_MP (@lem15272 P) (@lem15258 P h1)). Qed.
Lemma lem15282 (P : Prop -> Prop) (x : Prop) (h1 : P False) (h2 : x = False) : (P x) = True.
Proof. exact (TRANS (@lem15279 P x h2) (@lem15281 P h1)). Qed.
Lemma lem15283 (P : Prop -> Prop) (x : Prop) (h1 : P False) (h2 : x = False) : True = (P x).
Proof. exact (SYM (@lem15282 P x h1 h2)). Qed.
Lemma lem15284 (P : Prop -> Prop) (x : Prop) (h1 : P False) (h2 : x = False) : P x.
Proof. exact (EQ_MP (@lem15283 P x h1 h2) (@lem0)). Qed.
Lemma lem15285 (x : Prop) (P : Prop -> Prop) (h1 : P False) (h2 : P True) : P x.
Proof. exact (or_elim (@lem15253 x) (fun h0 : x = True => @lem15271 P x h2 h0) (fun h0 : x = False => @lem15284 P x h1 h0)). Qed.
Lemma lem15290 (P : Prop -> Prop) (h1 : P False) (h2 : P True) : term3 P.
Proof. exact (fun x : Prop => @lem15285 x P h1 h2). Qed.
Lemma lem15291 (P : Prop -> Prop) (h1 : term2 P) : P True.
Proof. exact (proj2 (@lem15256 P h1)). Qed.
Lemma lem15292 (P : Prop -> Prop) (h1 : term2 P) : P False.
Proof. exact (proj1 (@lem15256 P h1)). Qed.
Lemma lem15293 (P : Prop -> Prop) (h1 : P False) (h2 : P True) : (P True) = (term3 P).
Proof. exact (prop_ext (fun h3 : P True => @lem15290 P h1 h2) (fun h3 : term3 P => @lem15257 P h2)). Qed.
Lemma lem15294 (P : Prop -> Prop) (h1 : P False) (h2 : P True) : term3 P.
Proof. exact (EQ_MP (@lem15293 P h1 h2) (@lem15257 P h2)). Qed.
Lemma lem15295 (P : Prop -> Prop) (h1 : P False) (h2 : P True) : (P False) = (term3 P).
Proof. exact (prop_ext (fun h3 : P False => @lem15294 P h1 h2) (fun h3 : term3 P => @lem15258 P h1)). Qed.
Lemma lem15296 (P : Prop -> Prop) (h1 : P False) (h2 : P True) : term3 P.
Proof. exact (EQ_MP (@lem15295 P h1 h2) (@lem15258 P h1)). Qed.
Lemma lem15297 (P : Prop -> Prop) (h1 : P False) (h2 : term2 P) : (P True) = (term3 P).
Proof. exact (prop_ext (fun h3 : P True => @lem15296 P h1 h3) (fun h3 : term3 P => @lem15291 P h2)). Qed.
Lemma lem15298 (P : Prop -> Prop) (h1 : P False) (h2 : term2 P) : term3 P.
Proof. exact (EQ_MP (@lem15297 P h1 h2) (@lem15291 P h2)). Qed.
Lemma lem15299 (P : Prop -> Prop) (h1 : term2 P) : (P False) = (term3 P).
Proof. exact (prop_ext (fun h2 : P False => @lem15298 P h2 h1) (fun h2 : term3 P => @lem15292 P h1)). Qed.
Lemma lem15300 (P : Prop -> Prop) (h1 : term2 P) : term3 P.
Proof. exact (EQ_MP (@lem15299 P h1) (@lem15292 P h1)). Qed.
Lemma lem15301 (P : Prop -> Prop) : term4 P.
Proof. exact (fun h0 : term2 P => @lem15300 P h0). Qed.
Lemma lem15306 : term5.
Proof. exact (fun P : Prop -> Prop => @lem15301 P). Qed.
