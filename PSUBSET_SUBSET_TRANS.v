Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PSUBSET_SUBSET_TRANS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3224179 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3224180 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (@lem3224179 A s t). Qed.
Lemma lem3224184 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3224185 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (@lem3224184 A s t). Qed.
Lemma lem3224192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224193 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (MK_COMB (@lem3224192) (@lem3224185 A s t)). Qed.
Lemma lem3224197 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3224198 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (@lem3224197 A s t). Qed.
Lemma lem3224207 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3224208 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = (term6 A s t).
Proof. exact (MK_COMB (@lem3224207) (@lem3224198 A s t)). Qed.
Lemma lem3224209 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term7 A s t).
Proof. exact (MK_COMB (@lem3224193 A s t) (@lem3224208 A s t)). Qed.
Lemma lem3224212 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term7 A s t).
Proof. exact (TRANS (@lem3224180 A s t) (@lem3224209 A s t)). Qed.
Lemma lem3224213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224214 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term8 A s t) = (term9 A s t).
Proof. exact (MK_COMB (@lem3224213) (@lem3224212 A s t)). Qed.
Lemma lem3224216 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3224217 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (@lem3224216 A s t). Qed.
Lemma lem3224218 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@SUBSET A t u) = (term1 A t u).
Proof. exact (@lem3224217 A t u). Qed.
Lemma lem3224225 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term10 A s t u) = (term11 A s t u).
Proof. exact (MK_COMB (@lem3224214 A s t) (@lem3224218 A t u)). Qed.
Lemma lem3224228 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3224229 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term12 A s t u) = (term13 A s t u).
Proof. exact (MK_COMB (@lem3224228) (@lem3224225 A s t u)). Qed.
Lemma lem3224231 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3224232 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (@lem3224231 A s t). Qed.
Lemma lem3224233 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@PSUBSET A s u) = (term0 A s u).
Proof. exact (@lem3224232 A s u). Qed.
Lemma lem3224237 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3224238 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (@lem3224237 A s t). Qed.
Lemma lem3224239 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@SUBSET A s u) = (term1 A s u).
Proof. exact (@lem3224238 A s u). Qed.
Lemma lem3224246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224247 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term2 A s u) = (term3 A s u).
Proof. exact (MK_COMB (@lem3224246) (@lem3224239 A s u)). Qed.
Lemma lem3224251 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3224252 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (@lem3224251 A s t). Qed.
Lemma lem3224253 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (s = u) = (term4 A s u).
Proof. exact (@lem3224252 A s u). Qed.
Lemma lem3224262 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3224263 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term5 A s u) = (term6 A s u).
Proof. exact (MK_COMB (@lem3224262) (@lem3224253 A s u)). Qed.
Lemma lem3224264 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term0 A s u) = (term7 A s u).
Proof. exact (MK_COMB (@lem3224247 A s u) (@lem3224263 A s u)). Qed.
Lemma lem3224267 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@PSUBSET A s u) = (term7 A s u).
Proof. exact (TRANS (@lem3224233 A s u) (@lem3224264 A s u)). Qed.
Lemma lem3224268 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term14 A t s u) = (term15 A t s u).
Proof. exact (MK_COMB (@lem3224229 A s t u) (@lem3224267 A s u)). Qed.
Lemma lem3224271 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term16 A t s) = (term17 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3224268 A t s u)). Qed.
Lemma lem3224272 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3224273 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term18 A t s) = (term19 A t s).
Proof. exact (MK_COMB (@lem3224272 A) (@lem3224271 A t s)). Qed.
Lemma lem3224278 {A : Type'} (s : A -> Prop) : (term20 A s) = (term21 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3224273 A t s)). Qed.
Lemma lem3224279 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3224280 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (MK_COMB (@lem3224279 A) (@lem3224278 A s)). Qed.
Lemma lem3224285 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3224280 A s)). Qed.
Lemma lem3224286 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3224287 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (MK_COMB (@lem3224286 A) (@lem3224285 A)). Qed.
Lemma lem3224292 {A : Type'} : (term27 A) = (term26 A).
Proof. exact (SYM (@lem3224287 A)). Qed.
Lemma lem3224318 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3224319 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3224318 A P x). Qed.
Lemma lem3224320 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3224319 A s x). Qed.
Lemma lem3224321 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3224322 {A : Type'} (s : A -> Prop) (x : A) : (term28 A x s) = (term29 A s x).
Proof. exact (MK_COMB (@lem3224321) (@lem3224320 A s x)). Qed.
Lemma lem3224324 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3224325 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3224324 A P x). Qed.
Lemma lem3224326 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3224325 A t x). Qed.
Lemma lem3224327 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term30 A s x t) = (term31 A s t x).
Proof. exact (MK_COMB (@lem3224322 A s x) (@lem3224326 A t x)). Qed.
Lemma lem3224330 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term33 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224327 A s t x)). Qed.
Lemma lem3224331 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224332 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term34 A s t).
Proof. exact (MK_COMB (@lem3224331 A) (@lem3224330 A s t)). Qed.
Lemma lem3224337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224338 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3224337) (@lem3224332 A s t)). Qed.
Lemma lem3224346 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3224347 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3224346 A P x). Qed.
Lemma lem3224348 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3224347 A s x). Qed.
Lemma lem3224349 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3224350 {A : Type'} (s : A -> Prop) (x : A) : (term36 A x s) = (term37 A s x).
Proof. exact (MK_COMB (@lem3224349) (@lem3224348 A s x)). Qed.
Lemma lem3224352 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3224353 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3224352 A P x). Qed.
Lemma lem3224354 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3224353 A t x). Qed.
Lemma lem3224355 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x t)) = ((s x) = (t x)).
Proof. exact (MK_COMB (@lem3224350 A s x) (@lem3224354 A t x)). Qed.
Lemma lem3224358 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term38 A s t) = (term39 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224355 A s t x)). Qed.
Lemma lem3224359 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term40 A s t).
Proof. exact (MK_COMB (@lem3224359 A) (@lem3224358 A s t)). Qed.
Lemma lem3224365 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3224366 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term6 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3224365) (@lem3224360 A s t)). Qed.
Lemma lem3224367 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term42 A s t).
Proof. exact (MK_COMB (@lem3224338 A s t) (@lem3224366 A s t)). Qed.
Lemma lem3224370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224371 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term43 A s t).
Proof. exact (MK_COMB (@lem3224370) (@lem3224367 A s t)). Qed.
Lemma lem3224379 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3224380 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3224379 A P x). Qed.
Lemma lem3224381 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3224380 A t x). Qed.
Lemma lem3224382 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3224383 {A : Type'} (t : A -> Prop) (x : A) : (term28 A x t) = (term29 A t x).
Proof. exact (MK_COMB (@lem3224382) (@lem3224381 A t x)). Qed.
Lemma lem3224385 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3224386 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3224385 A P x). Qed.
Lemma lem3224387 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3224386 A u x). Qed.
Lemma lem3224388 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term30 A t x u) = (term31 A t u x).
Proof. exact (MK_COMB (@lem3224383 A t x) (@lem3224387 A u x)). Qed.
Lemma lem3224391 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term32 A t u) = (term33 A t u).
Proof. exact (fun_ext (fun x : A => @lem3224388 A t u x)). Qed.
Lemma lem3224392 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224393 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term1 A t u) = (term34 A t u).
Proof. exact (MK_COMB (@lem3224392 A) (@lem3224391 A t u)). Qed.
Lemma lem3224398 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term11 A s t u) = (term44 A s t u).
Proof. exact (MK_COMB (@lem3224371 A s t) (@lem3224393 A t u)). Qed.
Lemma lem3224401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3224402 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term13 A s t u) = (term45 A s t u).
Proof. exact (MK_COMB (@lem3224401) (@lem3224398 A s t u)). Qed.
Lemma lem3224412 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3224413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3224412 A P x). Qed.
Lemma lem3224414 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3224413 A s x). Qed.
Lemma lem3224415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3224416 {A : Type'} (s : A -> Prop) (x : A) : (term28 A x s) = (term29 A s x).
Proof. exact (MK_COMB (@lem3224415) (@lem3224414 A s x)). Qed.
Lemma lem3224418 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3224419 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3224418 A P x). Qed.
Lemma lem3224420 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3224419 A u x). Qed.
Lemma lem3224421 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term30 A s x u) = (term31 A s u x).
Proof. exact (MK_COMB (@lem3224416 A s x) (@lem3224420 A u x)). Qed.
Lemma lem3224424 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term32 A s u) = (term33 A s u).
Proof. exact (fun_ext (fun x : A => @lem3224421 A s u x)). Qed.
Lemma lem3224425 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224426 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term1 A s u) = (term34 A s u).
Proof. exact (MK_COMB (@lem3224425 A) (@lem3224424 A s u)). Qed.
Lemma lem3224431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224432 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term3 A s u) = (term35 A s u).
Proof. exact (MK_COMB (@lem3224431) (@lem3224426 A s u)). Qed.
Lemma lem3224440 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3224441 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3224440 A P x). Qed.
Lemma lem3224442 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3224441 A s x). Qed.
Lemma lem3224443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3224444 {A : Type'} (s : A -> Prop) (x : A) : (term36 A x s) = (term37 A s x).
Proof. exact (MK_COMB (@lem3224443) (@lem3224442 A s x)). Qed.
Lemma lem3224446 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3224447 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3224446 A P x). Qed.
Lemma lem3224448 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3224447 A u x). Qed.
Lemma lem3224449 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x u)) = ((s x) = (u x)).
Proof. exact (MK_COMB (@lem3224444 A s x) (@lem3224448 A u x)). Qed.
Lemma lem3224452 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term38 A s u) = (term39 A s u).
Proof. exact (fun_ext (fun x : A => @lem3224449 A s u x)). Qed.
Lemma lem3224453 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224454 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term4 A s u) = (term40 A s u).
Proof. exact (MK_COMB (@lem3224453 A) (@lem3224452 A s u)). Qed.
Lemma lem3224459 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3224460 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term6 A s u) = (term41 A s u).
Proof. exact (MK_COMB (@lem3224459) (@lem3224454 A s u)). Qed.
Lemma lem3224461 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term7 A s u) = (term42 A s u).
Proof. exact (MK_COMB (@lem3224432 A s u) (@lem3224460 A s u)). Qed.
Lemma lem3224464 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term15 A t s u) = (term46 A t s u).
Proof. exact (MK_COMB (@lem3224402 A s t u) (@lem3224461 A s u)). Qed.
Lemma lem3224467 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term17 A t s) = (term47 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3224464 A t s u)). Qed.
Lemma lem3224468 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3224469 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term19 A t s) = (term48 A t s).
Proof. exact (MK_COMB (@lem3224468 A) (@lem3224467 A t s)). Qed.
Lemma lem3224474 {A : Type'} (s : A -> Prop) : (term21 A s) = (term49 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3224469 A t s)). Qed.
Lemma lem3224475 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3224476 {A : Type'} (s : A -> Prop) : (term23 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem3224475 A) (@lem3224474 A s)). Qed.
Lemma lem3224481 {A : Type'} : (term25 A) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3224476 A s)). Qed.
Lemma lem3224482 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3224483 {A : Type'} : (term27 A) = (term52 A).
Proof. exact (MK_COMB (@lem3224482 A) (@lem3224481 A)). Qed.
Lemma lem3224488 {A : Type'} : (term52 A) = (term27 A).
Proof. exact (SYM (@lem3224483 A)). Qed.
Lemma lem3224490 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3224491 {A : Type'} : (term52 A) = (term54 A).
Proof. exact (@lem3224490 (term52 A)). Qed.
Lemma lem3224492 {A : Type'} : (term54 A) = (term52 A).
Proof. exact (SYM (@lem3224491 A)). Qed.
Lemma lem3224493 {A : Type'} (h1 : term55 A) : term55 A.
Proof. exact (h1). Qed.
Lemma lem3224496 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3224497 {A : Type'} : term56 A.
Proof. exact (fun h0 : term54 A => @lem3224496 A h0). Qed.
Lemma lem3224498 {A : Type'} (h1 : term56 A) : term56 A.
Proof. exact (h1). Qed.
Lemma lem3224499 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3224500 {A : Type'} (h1 : term54 A) (h2 : term56 A) : term54 A.
Proof. exact (@lem3224498 A h2 (@lem3224499 A h1)). Qed.
Lemma lem3224501 {A : Type'} (h1 : term54 A) : term57 A.
Proof. exact (fun h0 : term56 A => @lem3224500 A h1 h0). Qed.
Lemma lem3224502 {A : Type'} (h1 : term56 A) : term56 A.
Proof. exact (h1). Qed.
Lemma lem3224503 {A : Type'} (h1 : term54 A) (h2 : term56 A) : term54 A.
Proof. exact (@lem3224501 A h1 (@lem3224502 A h2)). Qed.
Lemma lem3224504 {A : Type'} (h1 : term56 A) : term56 A.
Proof. exact (fun h0 : term54 A => @lem3224503 A h0 h1). Qed.
Lemma lem3224505 {A : Type'} : term58 A.
Proof. exact (fun h0 : term56 A => @lem3224504 A h0). Qed.
Lemma lem3224508 {A : Type'} : term56 A.
Proof. exact (@lem3224505 A (@lem3224497 A)). Qed.
Lemma lem3224509 {A : Type'} : term56 A.
Proof. exact (@lem3224508 A). Qed.
Lemma lem3224511 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3224512 {A : Type'} : (term54 A) = (term59 A).
Proof. exact (@lem3224511 (term55 A)). Qed.
Lemma lem3224514 (t : Prop) : (term60 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3224515 {A : Type'} : (term59 A) = (term52 A).
Proof. exact (@lem3224514 (term52 A)). Qed.
Lemma lem3224566 {A : Type'} : (term54 A) = (term52 A).
Proof. exact (TRANS (@lem3224512 A) (@lem3224515 A)). Qed.
Lemma lem3224571 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((s x) = (u x)) = ((s x) = (u x)).
Proof. exact (eq_refl ((s x) = (u x))). Qed.
Lemma lem3224572 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term39 A s u) = (term39 A s u).
Proof. exact (fun_ext (fun x : A => @lem3224571 A s u x)). Qed.
Lemma lem3224573 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224574 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term40 A s u) = (term40 A s u).
Proof. exact (MK_COMB (@lem3224573 A) (@lem3224572 A s u)). Qed.
Lemma lem3224575 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3224576 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term41 A s u) = (term41 A s u).
Proof. exact (MK_COMB (@lem3224575) (@lem3224574 A s u)). Qed.
Lemma lem3224581 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term31 A s u x) = (term31 A s u x).
Proof. exact (eq_refl (term31 A s u x)). Qed.
Lemma lem3224582 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term33 A s u) = (term33 A s u).
Proof. exact (fun_ext (fun x : A => @lem3224581 A s u x)). Qed.
Lemma lem3224583 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224584 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term34 A s u) = (term34 A s u).
Proof. exact (MK_COMB (@lem3224583 A) (@lem3224582 A s u)). Qed.
Lemma lem3224585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224586 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term35 A s u) = (term35 A s u).
Proof. exact (MK_COMB (@lem3224585) (@lem3224584 A s u)). Qed.
Lemma lem3224587 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term42 A s u) = (term42 A s u).
Proof. exact (MK_COMB (@lem3224586 A s u) (@lem3224576 A s u)). Qed.
Lemma lem3224592 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term31 A t u x) = (term31 A t u x).
Proof. exact (eq_refl (term31 A t u x)). Qed.
Lemma lem3224593 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term33 A t u) = (term33 A t u).
Proof. exact (fun_ext (fun x : A => @lem3224592 A t u x)). Qed.
Lemma lem3224594 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224595 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term34 A t u) = (term34 A t u).
Proof. exact (MK_COMB (@lem3224594 A) (@lem3224593 A t u)). Qed.
Lemma lem3224600 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = ((s x) = (t x)).
Proof. exact (eq_refl ((s x) = (t x))). Qed.
Lemma lem3224601 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term39 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224600 A s t x)). Qed.
Lemma lem3224602 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224603 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term40 A s t) = (term40 A s t).
Proof. exact (MK_COMB (@lem3224602 A) (@lem3224601 A s t)). Qed.
Lemma lem3224604 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3224605 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3224604) (@lem3224603 A s t)). Qed.
Lemma lem3224610 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term31 A s t x) = (term31 A s t x).
Proof. exact (eq_refl (term31 A s t x)). Qed.
Lemma lem3224611 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term33 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224610 A s t x)). Qed.
Lemma lem3224612 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224613 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term34 A s t).
Proof. exact (MK_COMB (@lem3224612 A) (@lem3224611 A s t)). Qed.
Lemma lem3224614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224615 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3224614) (@lem3224613 A s t)). Qed.
Lemma lem3224616 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = (term42 A s t).
Proof. exact (MK_COMB (@lem3224615 A s t) (@lem3224605 A s t)). Qed.
Lemma lem3224617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224618 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term43 A s t).
Proof. exact (MK_COMB (@lem3224617) (@lem3224616 A s t)). Qed.
Lemma lem3224619 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term44 A s t u) = (term44 A s t u).
Proof. exact (MK_COMB (@lem3224618 A s t) (@lem3224595 A t u)). Qed.
Lemma lem3224620 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3224621 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term45 A s t u) = (term45 A s t u).
Proof. exact (MK_COMB (@lem3224620) (@lem3224619 A s t u)). Qed.
Lemma lem3224622 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term46 A t s u) = (term46 A t s u).
Proof. exact (MK_COMB (@lem3224621 A s t u) (@lem3224587 A s u)). Qed.
Lemma lem3224623 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term47 A t s) = (term47 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3224622 A t s u)). Qed.
Lemma lem3224624 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3224625 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term48 A t s) = (term48 A t s).
Proof. exact (MK_COMB (@lem3224624 A) (@lem3224623 A t s)). Qed.
Lemma lem3224626 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3224625 A t s)). Qed.
Lemma lem3224627 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3224628 {A : Type'} (s : A -> Prop) : (term50 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem3224627 A) (@lem3224626 A s)). Qed.
Lemma lem3224629 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3224628 A s)). Qed.
Lemma lem3224630 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3224631 {A : Type'} : (term52 A) = (term52 A).
Proof. exact (MK_COMB (@lem3224630 A) (@lem3224629 A)). Qed.
Lemma lem3224696 {A : Type'} : (term54 A) = (term52 A).
Proof. exact (TRANS (@lem3224566 A) (@lem3224631 A)). Qed.
Lemma lem3224697 {A : Type'} : (term52 A) = (term54 A).
Proof. exact (SYM (@lem3224696 A)). Qed.
Lemma lem3224698 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term44 A s t u) : term44 A s t u.
Proof. exact (h1). Qed.
Lemma lem3224700 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3224701 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term42 A s u) = (term61 A s u).
Proof. exact (@lem3224700 (term42 A s u)). Qed.
Lemma lem3224702 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term61 A s u) = (term42 A s u).
Proof. exact (SYM (@lem3224701 A s u)). Qed.
Lemma lem3224703 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term62 A s u) : term62 A s u.
Proof. exact (h1). Qed.
Lemma lem3224710 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term31 A s t x) = (term63 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3224711 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224710 A s t x)). Qed.
Lemma lem3224712 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224713 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3224712 A) (@lem3224711 A s t)). Qed.
Lemma lem3224728 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term66 A s t x) = (term67 A s t x).
Proof. exact (@lem17646 (s x) (t x)). Qed.
Lemma lem3224729 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3224730 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term70 A s t).
Proof. exact (@lem3224729 A (term39 A s t)). Qed.
Lemma lem3224731 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term71 A s t x) = ((s x) = (t x)).
Proof. exact (eq_refl (term71 A s t x)). Qed.
Lemma lem3224732 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3224733 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term72 A s t x) = (term66 A s t x).
Proof. exact (MK_COMB (@lem3224732) (@lem3224731 A s t x)). Qed.
Lemma lem3224734 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term72 A s t x) = (term67 A s t x).
Proof. exact (TRANS (@lem3224733 A s t x) (@lem3224728 A s t x)). Qed.
Lemma lem3224735 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term74 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224734 A s t x)). Qed.
Lemma lem3224736 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224737 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term70 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3224736 A) (@lem3224735 A s t)). Qed.
Lemma lem3224738 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term75 A s t).
Proof. exact (TRANS (@lem3224730 A s t) (@lem3224737 A s t)). Qed.
Lemma lem3224739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224740 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term76 A s t).
Proof. exact (MK_COMB (@lem3224739) (@lem3224713 A s t)). Qed.
Lemma lem3224741 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = (term77 A s t).
Proof. exact (MK_COMB (@lem3224740 A s t) (@lem3224738 A s t)). Qed.
Lemma lem3224748 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term31 A t u x) = (term63 A t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem3224749 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term33 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3224748 A t u x)). Qed.
Lemma lem3224750 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3224751 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term34 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3224750 A) (@lem3224749 A t u)). Qed.
Lemma lem3224752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224753 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term78 A s t).
Proof. exact (MK_COMB (@lem3224752) (@lem3224741 A s t)). Qed.
Lemma lem3224754 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term44 A s t u) = (term79 A s t u).
Proof. exact (MK_COMB (@lem3224753 A s t) (@lem3224751 A t u)). Qed.
Lemma lem3224788 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3224789 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (@lem3224788 A P Q). Qed.
Lemma lem3224790 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term83 A s t).
Proof. exact (@lem3224789 A (term84 A s t) (term85 A s t)). Qed.
Lemma lem3224791 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term87 A s t x).
Proof. exact (eq_refl (term86 A s t x)). Qed.
Lemma lem3224792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3224793 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term88 A s t x) = (term89 A s t x).
Proof. exact (MK_COMB (@lem3224792) (@lem3224791 A s t x)). Qed.
Lemma lem3224794 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term90 A s t x) = (term91 A s t x).
Proof. exact (eq_refl (term90 A s t x)). Qed.
Lemma lem3224795 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term92 A s t x) = (term67 A s t x).
Proof. exact (MK_COMB (@lem3224793 A s t x) (@lem3224794 A s t x)). Qed.
Lemma lem3224796 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term74 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224795 A s t x)). Qed.
Lemma lem3224797 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224798 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3224797 A) (@lem3224796 A s t)). Qed.
Lemma lem3224799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3224800 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term94 A s t) = (term95 A s t).
Proof. exact (MK_COMB (@lem3224799) (@lem3224798 A s t)). Qed.
Lemma lem3224801 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term87 A s t x).
Proof. exact (eq_refl (term86 A s t x)). Qed.
Lemma lem3224802 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term84 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224801 A s t x)). Qed.
Lemma lem3224803 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224804 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3224803 A) (@lem3224802 A s t)). Qed.
Lemma lem3224805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3224806 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term99 A s t) = (term100 A s t).
Proof. exact (MK_COMB (@lem3224805) (@lem3224804 A s t)). Qed.
Lemma lem3224807 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term90 A s t x) = (term91 A s t x).
Proof. exact (eq_refl (term90 A s t x)). Qed.
Lemma lem3224808 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term101 A s t) = (term85 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224807 A s t x)). Qed.
Lemma lem3224809 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224810 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term103 A s t).
Proof. exact (MK_COMB (@lem3224809 A) (@lem3224808 A s t)). Qed.
Lemma lem3224811 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term104 A s t).
Proof. exact (MK_COMB (@lem3224806 A s t) (@lem3224810 A s t)). Qed.
Lemma lem3224812 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term82 A s t) = (term83 A s t)) = ((term75 A s t) = (term104 A s t)).
Proof. exact (MK_COMB (@lem3224800 A s t) (@lem3224811 A s t)). Qed.
Lemma lem3224813 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term75 A s t) = (term104 A s t).
Proof. exact (EQ_MP (@lem3224812 A s t) (@lem3224790 A s t)). Qed.
Lemma lem3224874 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term76 A s t).
Proof. exact (eq_refl (term76 A s t)). Qed.
Lemma lem3224875 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term105 A s t).
Proof. exact (MK_COMB (@lem3224874 A s t) (@lem3224813 A s t)). Qed.
Lemma lem3224876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224877 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term106 A s t).
Proof. exact (MK_COMB (@lem3224876) (@lem3224875 A s t)). Qed.
Lemma lem3224910 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (eq_refl (term65 A t u)). Qed.
Lemma lem3224911 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term79 A s t u) = (term107 A s t u).
Proof. exact (MK_COMB (@lem3224877 A s t) (@lem3224910 A t u)). Qed.
Lemma lem3224913 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3224914 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (@lem3224913 A P Q). Qed.
Lemma lem3224915 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term82 A s t).
Proof. exact (@lem3224914 A (term84 A s t) (term85 A s t)). Qed.
Lemma lem3224916 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term87 A s t x).
Proof. exact (eq_refl (term86 A s t x)). Qed.
Lemma lem3224917 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term84 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224916 A s t x)). Qed.
Lemma lem3224918 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224919 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3224918 A) (@lem3224917 A s t)). Qed.
Lemma lem3224920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3224921 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term99 A s t) = (term100 A s t).
Proof. exact (MK_COMB (@lem3224920) (@lem3224919 A s t)). Qed.
Lemma lem3224922 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term90 A s t x) = (term91 A s t x).
Proof. exact (eq_refl (term90 A s t x)). Qed.
Lemma lem3224923 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term101 A s t) = (term85 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224922 A s t x)). Qed.
Lemma lem3224924 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224925 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term103 A s t).
Proof. exact (MK_COMB (@lem3224924 A) (@lem3224923 A s t)). Qed.
Lemma lem3224926 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term104 A s t).
Proof. exact (MK_COMB (@lem3224921 A s t) (@lem3224925 A s t)). Qed.
Lemma lem3224927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3224928 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term108 A s t) = (term109 A s t).
Proof. exact (MK_COMB (@lem3224927) (@lem3224926 A s t)). Qed.
Lemma lem3224929 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term87 A s t x).
Proof. exact (eq_refl (term86 A s t x)). Qed.
Lemma lem3224930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3224931 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term88 A s t x) = (term89 A s t x).
Proof. exact (MK_COMB (@lem3224930) (@lem3224929 A s t x)). Qed.
Lemma lem3224932 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term90 A s t x) = (term91 A s t x).
Proof. exact (eq_refl (term90 A s t x)). Qed.
Lemma lem3224933 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term92 A s t x) = (term67 A s t x).
Proof. exact (MK_COMB (@lem3224931 A s t x) (@lem3224932 A s t x)). Qed.
Lemma lem3224934 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term74 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224933 A s t x)). Qed.
Lemma lem3224935 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224936 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3224935 A) (@lem3224934 A s t)). Qed.
Lemma lem3224937 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term83 A s t) = (term82 A s t)) = ((term104 A s t) = (term75 A s t)).
Proof. exact (MK_COMB (@lem3224928 A s t) (@lem3224936 A s t)). Qed.
Lemma lem3224938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term104 A s t) = (term75 A s t).
Proof. exact (EQ_MP (@lem3224937 A s t) (@lem3224915 A s t)). Qed.
Lemma lem3224939 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term76 A s t).
Proof. exact (eq_refl (term76 A s t)). Qed.
Lemma lem3224940 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term77 A s t).
Proof. exact (MK_COMB (@lem3224939 A s t) (@lem3224938 A s t)). Qed.
Lemma lem3224942 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3224943 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (@lem3224942 A P Q). Qed.
Lemma lem3224944 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term113 A s t).
Proof. exact (@lem3224943 A (term65 A s t) (term74 A s t)). Qed.
Lemma lem3224945 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term114 A s t x) = (term67 A s t x).
Proof. exact (eq_refl (term114 A s t x)). Qed.
Lemma lem3224946 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term115 A s t) = (term74 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224945 A s t x)). Qed.
Lemma lem3224947 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224948 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term116 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3224947 A) (@lem3224946 A s t)). Qed.
Lemma lem3224949 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term76 A s t).
Proof. exact (eq_refl (term76 A s t)). Qed.
Lemma lem3224950 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term77 A s t).
Proof. exact (MK_COMB (@lem3224949 A s t) (@lem3224948 A s t)). Qed.
Lemma lem3224951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3224952 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term117 A s t) = (term118 A s t).
Proof. exact (MK_COMB (@lem3224951) (@lem3224950 A s t)). Qed.
Lemma lem3224953 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term114 A s t x) = (term67 A s t x).
Proof. exact (eq_refl (term114 A s t x)). Qed.
Lemma lem3224954 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term76 A s t).
Proof. exact (eq_refl (term76 A s t)). Qed.
Lemma lem3224955 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term119 A s t x) = (term120 A s t x).
Proof. exact (MK_COMB (@lem3224954 A s t) (@lem3224953 A s t x)). Qed.
Lemma lem3224956 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term121 A s t) = (term122 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224955 A s t x)). Qed.
Lemma lem3224957 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224958 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term113 A s t) = (term123 A s t).
Proof. exact (MK_COMB (@lem3224957 A) (@lem3224956 A s t)). Qed.
Lemma lem3224959 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term112 A s t) = (term113 A s t)) = ((term77 A s t) = (term123 A s t)).
Proof. exact (MK_COMB (@lem3224952 A s t) (@lem3224958 A s t)). Qed.
Lemma lem3224960 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term123 A s t).
Proof. exact (EQ_MP (@lem3224959 A s t) (@lem3224944 A s t)). Qed.
Lemma lem3224961 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term123 A s t).
Proof. exact (TRANS (@lem3224940 A s t) (@lem3224960 A s t)). Qed.
Lemma lem3224962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224963 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term124 A s t).
Proof. exact (MK_COMB (@lem3224962) (@lem3224961 A s t)). Qed.
Lemma lem3224964 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (eq_refl (term65 A t u)). Qed.
Lemma lem3224965 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term107 A s t u) = (term125 A s t u).
Proof. exact (MK_COMB (@lem3224963 A s t) (@lem3224964 A t u)). Qed.
Lemma lem3224967 {A : Type'} (P : A -> Prop) (Q : Prop) : (term126 A P Q) = (term127 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3224968 {A : Type'} (P : A -> Prop) (Q : Prop) : (term126 A P Q) = (term127 A P Q).
Proof. exact (@lem3224967 A P Q). Qed.
Lemma lem3224969 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term128 A s t u) = (term129 A s t u).
Proof. exact (@lem3224968 A (term122 A s t) (term65 A t u)). Qed.
Lemma lem3224970 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term130 A s t x) = (term120 A s t x).
Proof. exact (eq_refl (term130 A s t x)). Qed.
Lemma lem3224971 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term131 A s t) = (term122 A s t).
Proof. exact (fun_ext (fun x : A => @lem3224970 A s t x)). Qed.
Lemma lem3224972 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224973 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term132 A s t) = (term123 A s t).
Proof. exact (MK_COMB (@lem3224972 A) (@lem3224971 A s t)). Qed.
Lemma lem3224974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224975 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term133 A s t) = (term124 A s t).
Proof. exact (MK_COMB (@lem3224974) (@lem3224973 A s t)). Qed.
Lemma lem3224976 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (eq_refl (term65 A t u)). Qed.
Lemma lem3224977 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term128 A s t u) = (term125 A s t u).
Proof. exact (MK_COMB (@lem3224975 A s t) (@lem3224976 A t u)). Qed.
Lemma lem3224978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3224979 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term134 A s t u) = (term135 A s t u).
Proof. exact (MK_COMB (@lem3224978) (@lem3224977 A s t u)). Qed.
Lemma lem3224980 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term130 A s t x) = (term120 A s t x).
Proof. exact (eq_refl (term130 A s t x)). Qed.
Lemma lem3224981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3224982 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term136 A s t x) = (term137 A s t x).
Proof. exact (MK_COMB (@lem3224981) (@lem3224980 A s t x)). Qed.
Lemma lem3224983 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (eq_refl (term65 A t u)). Qed.
Lemma lem3224984 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term138 A s x t u) = (term139 A s x t u).
Proof. exact (MK_COMB (@lem3224982 A s t x) (@lem3224983 A t u)). Qed.
Lemma lem3224985 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term140 A s t u) = (term141 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3224984 A s x t u)). Qed.
Lemma lem3224986 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3224987 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term129 A s t u) = (term142 A s t u).
Proof. exact (MK_COMB (@lem3224986 A) (@lem3224985 A s t u)). Qed.
Lemma lem3224988 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term128 A s t u) = (term129 A s t u)) = ((term125 A s t u) = (term142 A s t u)).
Proof. exact (MK_COMB (@lem3224979 A s t u) (@lem3224987 A s t u)). Qed.
Lemma lem3224989 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term125 A s t u) = (term142 A s t u).
Proof. exact (EQ_MP (@lem3224988 A s t u) (@lem3224969 A s t u)). Qed.
Lemma lem3224990 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term107 A s t u) = (term142 A s t u).
Proof. exact (TRANS (@lem3224965 A s t u) (@lem3224989 A s t u)). Qed.
Lemma lem3224991 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term79 A s t u) = (term142 A s t u).
Proof. exact (TRANS (@lem3224911 A s t u) (@lem3224990 A s t u)). Qed.
Lemma lem3224992 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term44 A s t u) = (term142 A s t u).
Proof. exact (TRANS (@lem3224754 A s t u) (@lem3224991 A s t u)). Qed.
Lemma lem3224993 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term44 A s t u) : term142 A s t u.
Proof. exact (EQ_MP (@lem3224992 A s t u) (@lem3224698 A s t u h1)). Qed.
Lemma lem3225000 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term143 A s u x) = (term87 A s u x).
Proof. exact (@lem17362 (s x) (u x)). Qed.
Lemma lem3225001 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3225002 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term145 A s u).
Proof. exact (@lem3225001 A (term33 A s u)). Qed.
Lemma lem3225003 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term146 A s u x) = (term31 A s u x).
Proof. exact (eq_refl (term146 A s u x)). Qed.
Lemma lem3225004 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3225005 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term147 A s u x) = (term143 A s u x).
Proof. exact (MK_COMB (@lem3225004) (@lem3225003 A s u x)). Qed.
Lemma lem3225006 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term147 A s u x) = (term87 A s u x).
Proof. exact (TRANS (@lem3225005 A s u x) (@lem3225000 A s u x)). Qed.
Lemma lem3225007 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term148 A s u) = (term84 A s u).
Proof. exact (fun_ext (fun x : A => @lem3225006 A s u x)). Qed.
Lemma lem3225008 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3225009 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term145 A s u) = (term98 A s u).
Proof. exact (MK_COMB (@lem3225008 A) (@lem3225007 A s u)). Qed.
Lemma lem3225010 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term98 A s u).
Proof. exact (TRANS (@lem3225002 A s u) (@lem3225009 A s u)). Qed.
Lemma lem3225025 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((s x) = (u x)) = (term149 A s u x).
Proof. exact (@lem17784 (s x) (u x)). Qed.
Lemma lem3225026 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term39 A s u) = (term150 A s u).
Proof. exact (fun_ext (fun x : A => @lem3225025 A s u x)). Qed.
Lemma lem3225027 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225028 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term40 A s u) = (term151 A s u).
Proof. exact (MK_COMB (@lem3225027 A) (@lem3225026 A s u)). Qed.
Lemma lem3225029 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term152 A s u) = (term40 A s u).
Proof. exact (@lem16933 (term40 A s u)). Qed.
Lemma lem3225030 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term152 A s u) = (term151 A s u).
Proof. exact (TRANS (@lem3225029 A s u) (@lem3225028 A s u)). Qed.
Lemma lem3225031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3225032 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term153 A s u) = (term100 A s u).
Proof. exact (MK_COMB (@lem3225031) (@lem3225010 A s u)). Qed.
Lemma lem3225033 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term154 A s u) = (term155 A s u).
Proof. exact (MK_COMB (@lem3225032 A s u) (@lem3225030 A s u)). Qed.
Lemma lem3225034 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term62 A s u) = (term154 A s u).
Proof. exact (@lem17045 (term34 A s u) (term41 A s u)). Qed.
Lemma lem3225035 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term62 A s u) = (term155 A s u).
Proof. exact (TRANS (@lem3225034 A s u) (@lem3225033 A s u)). Qed.
Lemma lem3225065 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3225066 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (@lem3225065 A P Q). Qed.
Lemma lem3225067 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term158 A s u) = (term159 A s u).
Proof. exact (@lem3225066 A (term160 A s u) (term64 A s u)). Qed.
Lemma lem3225068 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term161 A s u x) = (term162 A s u x).
Proof. exact (eq_refl (term161 A s u x)). Qed.
Lemma lem3225069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3225070 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term163 A s u x) = (term164 A s u x).
Proof. exact (MK_COMB (@lem3225069) (@lem3225068 A s u x)). Qed.
Lemma lem3225071 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term165 A s u x) = (term63 A s u x).
Proof. exact (eq_refl (term165 A s u x)). Qed.
Lemma lem3225072 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term166 A s u x) = (term149 A s u x).
Proof. exact (MK_COMB (@lem3225070 A s u x) (@lem3225071 A s u x)). Qed.
Lemma lem3225073 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term167 A s u) = (term150 A s u).
Proof. exact (fun_ext (fun x : A => @lem3225072 A s u x)). Qed.
Lemma lem3225074 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225075 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term158 A s u) = (term151 A s u).
Proof. exact (MK_COMB (@lem3225074 A) (@lem3225073 A s u)). Qed.
Lemma lem3225076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3225077 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term168 A s u) = (term169 A s u).
Proof. exact (MK_COMB (@lem3225076) (@lem3225075 A s u)). Qed.
Lemma lem3225078 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term161 A s u x) = (term162 A s u x).
Proof. exact (eq_refl (term161 A s u x)). Qed.
Lemma lem3225079 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term170 A s u) = (term160 A s u).
Proof. exact (fun_ext (fun x : A => @lem3225078 A s u x)). Qed.
Lemma lem3225080 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225081 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term171 A s u) = (term172 A s u).
Proof. exact (MK_COMB (@lem3225080 A) (@lem3225079 A s u)). Qed.
Lemma lem3225082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3225083 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term173 A s u) = (term174 A s u).
Proof. exact (MK_COMB (@lem3225082) (@lem3225081 A s u)). Qed.
Lemma lem3225084 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term165 A s u x) = (term63 A s u x).
Proof. exact (eq_refl (term165 A s u x)). Qed.
Lemma lem3225085 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term175 A s u) = (term64 A s u).
Proof. exact (fun_ext (fun x : A => @lem3225084 A s u x)). Qed.
Lemma lem3225086 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225087 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term176 A s u) = (term65 A s u).
Proof. exact (MK_COMB (@lem3225086 A) (@lem3225085 A s u)). Qed.
Lemma lem3225088 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term159 A s u) = (term177 A s u).
Proof. exact (MK_COMB (@lem3225083 A s u) (@lem3225087 A s u)). Qed.
Lemma lem3225089 {A : Type'} (s : A -> Prop) (u : A -> Prop) : ((term158 A s u) = (term159 A s u)) = ((term151 A s u) = (term177 A s u)).
Proof. exact (MK_COMB (@lem3225077 A s u) (@lem3225088 A s u)). Qed.
Lemma lem3225090 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term151 A s u) = (term177 A s u).
Proof. exact (EQ_MP (@lem3225089 A s u) (@lem3225067 A s u)). Qed.
Lemma lem3225151 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term100 A s u) = (term100 A s u).
Proof. exact (eq_refl (term100 A s u)). Qed.
Lemma lem3225152 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term155 A s u) = (term178 A s u).
Proof. exact (MK_COMB (@lem3225151 A s u) (@lem3225090 A s u)). Qed.
Lemma lem3225154 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3225155 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (@lem3225154 A P Q). Qed.
Lemma lem3225156 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term181 A s u) = (term182 A s u).
Proof. exact (@lem3225155 A (term84 A s u) (term177 A s u)). Qed.
Lemma lem3225157 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term86 A s u x) = (term87 A s u x).
Proof. exact (eq_refl (term86 A s u x)). Qed.
Lemma lem3225158 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term96 A s u) = (term84 A s u).
Proof. exact (fun_ext (fun x : A => @lem3225157 A s u x)). Qed.
Lemma lem3225159 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3225160 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term97 A s u) = (term98 A s u).
Proof. exact (MK_COMB (@lem3225159 A) (@lem3225158 A s u)). Qed.
Lemma lem3225161 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3225162 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term99 A s u) = (term100 A s u).
Proof. exact (MK_COMB (@lem3225161) (@lem3225160 A s u)). Qed.
Lemma lem3225163 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term177 A s u) = (term177 A s u).
Proof. exact (eq_refl (term177 A s u)). Qed.
Lemma lem3225164 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term181 A s u) = (term178 A s u).
Proof. exact (MK_COMB (@lem3225162 A s u) (@lem3225163 A s u)). Qed.
Lemma lem3225165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3225166 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term183 A s u) = (term184 A s u).
Proof. exact (MK_COMB (@lem3225165) (@lem3225164 A s u)). Qed.
Lemma lem3225167 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term86 A s u x) = (term87 A s u x).
Proof. exact (eq_refl (term86 A s u x)). Qed.
Lemma lem3225168 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3225169 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term88 A s u x) = (term89 A s u x).
Proof. exact (MK_COMB (@lem3225168) (@lem3225167 A s u x)). Qed.
Lemma lem3225170 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term177 A s u) = (term177 A s u).
Proof. exact (eq_refl (term177 A s u)). Qed.
Lemma lem3225171 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) : (term185 A x s u) = (term186 A x s u).
Proof. exact (MK_COMB (@lem3225169 A s u x) (@lem3225170 A s u)). Qed.
Lemma lem3225172 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term187 A s u) = (term188 A s u).
Proof. exact (fun_ext (fun x : A => @lem3225171 A x s u)). Qed.
Lemma lem3225173 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3225174 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term182 A s u) = (term189 A s u).
Proof. exact (MK_COMB (@lem3225173 A) (@lem3225172 A s u)). Qed.
Lemma lem3225175 {A : Type'} (s : A -> Prop) (u : A -> Prop) : ((term181 A s u) = (term182 A s u)) = ((term178 A s u) = (term189 A s u)).
Proof. exact (MK_COMB (@lem3225166 A s u) (@lem3225174 A s u)). Qed.
Lemma lem3225176 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term178 A s u) = (term189 A s u).
Proof. exact (EQ_MP (@lem3225175 A s u) (@lem3225156 A s u)). Qed.
Lemma lem3225177 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term155 A s u) = (term189 A s u).
Proof. exact (TRANS (@lem3225152 A s u) (@lem3225176 A s u)). Qed.
Lemma lem3225178 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term62 A s u) = (term189 A s u).
Proof. exact (TRANS (@lem3225035 A s u) (@lem3225177 A s u)). Qed.
Lemma lem3225179 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term62 A s u) : term189 A s u.
Proof. exact (EQ_MP (@lem3225178 A s u) (@lem3224703 A s u h1)). Qed.
Lemma lem3225180 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term186 A x s u) : term186 A x s u.
Proof. exact (h1). Qed.
Lemma lem3225181 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term139 A s x' t u.
Proof. exact (h1). Qed.
Lemma lem3225192 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term63 A s u x) = (term63 A s u x).
Proof. exact (eq_refl (term63 A s u x)). Qed.
Lemma lem3225193 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term64 A s u) = (term64 A s u).
Proof. exact (fun_ext (fun x : A => @lem3225192 A s u x)). Qed.
Lemma lem3225194 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225195 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term65 A s u) = (term65 A s u).
Proof. exact (MK_COMB (@lem3225194 A) (@lem3225193 A s u)). Qed.
Lemma lem3225206 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term162 A s u x) = (term162 A s u x).
Proof. exact (eq_refl (term162 A s u x)). Qed.
Lemma lem3225207 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term160 A s u) = (term160 A s u).
Proof. exact (fun_ext (fun x : A => @lem3225206 A s u x)). Qed.
Lemma lem3225208 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225209 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term172 A s u) = (term172 A s u).
Proof. exact (MK_COMB (@lem3225208 A) (@lem3225207 A s u)). Qed.
Lemma lem3225210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3225211 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term174 A s u) = (term174 A s u).
Proof. exact (MK_COMB (@lem3225210) (@lem3225209 A s u)). Qed.
Lemma lem3225212 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term177 A s u) = (term177 A s u).
Proof. exact (MK_COMB (@lem3225211 A s u) (@lem3225195 A s u)). Qed.
Lemma lem3225225 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term89 A s u x) = (term89 A s u x).
Proof. exact (eq_refl (term89 A s u x)). Qed.
Lemma lem3225226 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) : (term186 A x s u) = (term186 A x s u).
Proof. exact (MK_COMB (@lem3225225 A s u x) (@lem3225212 A s u)). Qed.
Lemma lem3225227 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term186 A x s u) : term186 A x s u.
Proof. exact (EQ_MP (@lem3225226 A x s u) (@lem3225180 A x s u h1)). Qed.
Lemma lem3225238 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term63 A t u x) = (term63 A t u x).
Proof. exact (eq_refl (term63 A t u x)). Qed.
Lemma lem3225239 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term64 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3225238 A t u x)). Qed.
Lemma lem3225240 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225241 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3225240 A) (@lem3225239 A t u)). Qed.
Lemma lem3225266 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term67 A s t x') = (term67 A s t x').
Proof. exact (eq_refl (term67 A s t x')). Qed.
Lemma lem3225277 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term63 A s t x).
Proof. exact (eq_refl (term63 A s t x)). Qed.
Lemma lem3225278 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3225277 A s t x)). Qed.
Lemma lem3225279 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225280 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3225279 A) (@lem3225278 A s t)). Qed.
Lemma lem3225281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3225282 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term76 A s t).
Proof. exact (MK_COMB (@lem3225281) (@lem3225280 A s t)). Qed.
Lemma lem3225283 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term120 A s t x') = (term120 A s t x').
Proof. exact (MK_COMB (@lem3225282 A s t) (@lem3225266 A s t x')). Qed.
Lemma lem3225284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3225285 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term137 A s t x') = (term137 A s t x').
Proof. exact (MK_COMB (@lem3225284) (@lem3225283 A s t x')). Qed.
Lemma lem3225286 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) : (term139 A s x' t u) = (term139 A s x' t u).
Proof. exact (MK_COMB (@lem3225285 A s t x') (@lem3225241 A t u)). Qed.
Lemma lem3225287 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term139 A s x' t u.
Proof. exact (EQ_MP (@lem3225286 A s x' t u) (@lem3225181 A s x' t u h1)). Qed.
Lemma lem3225288 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term65 A t u.
Proof. exact (proj2 (@lem3225287 A s x' t u h1)). Qed.
Lemma lem3225289 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term120 A s t x'.
Proof. exact (proj1 (@lem3225287 A s x' t u h1)). Qed.
Lemma lem3225290 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term67 A s t x'.
Proof. exact (proj2 (@lem3225289 A s x' t u h1)). Qed.
Lemma lem3225291 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term65 A s t.
Proof. exact (proj1 (@lem3225289 A s x' t u h1)). Qed.
Lemma lem3225292 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term87 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3225293 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term91 A s t x') : term91 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3225304 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : term87 A s u x.
Proof. exact (h1). Qed.
Lemma lem3225305 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) : term177 A s u.
Proof. exact (h1). Qed.
Lemma lem3225309 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) : term172 A s u.
Proof. exact (proj1 (@lem3225305 A s u h1)). Qed.
Lemma lem3225330 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term63 A s t x).
Proof. exact (eq_refl (term63 A s t x)). Qed.
Lemma lem3225331 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3225330 A s t x)). Qed.
Lemma lem3225332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225334 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3225332 A) (@lem3225331 A s t)). Qed.
Lemma lem3225335 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term65 A s t.
Proof. exact (EQ_MP (@lem3225334 A s t) (@lem3225291 A s x' t u h1)). Qed.
Lemma lem3225372 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term63 A s t x).
Proof. exact (eq_refl (term63 A s t x)). Qed.
Lemma lem3225373 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3225372 A s t x)). Qed.
Lemma lem3225374 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225376 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3225374 A) (@lem3225373 A s t)). Qed.
Lemma lem3225377 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term65 A s t.
Proof. exact (EQ_MP (@lem3225376 A s t) (@lem3225291 A s x' t u h1)). Qed.
Lemma lem3225419 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term63 A t u x) = (term63 A t u x).
Proof. exact (eq_refl (term63 A t u x)). Qed.
Lemma lem3225420 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term64 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3225419 A t u x)). Qed.
Lemma lem3225421 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225423 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3225421 A) (@lem3225420 A t u)). Qed.
Lemma lem3225424 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term65 A t u.
Proof. exact (EQ_MP (@lem3225423 A t u) (@lem3225288 A s x' t u h1)). Qed.
Lemma lem3225432 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term63 A s t x).
Proof. exact (eq_refl (term63 A s t x)). Qed.
Lemma lem3225433 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3225432 A s t x)). Qed.
Lemma lem3225434 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225436 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3225434 A) (@lem3225433 A s t)). Qed.
Lemma lem3225437 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term65 A s t.
Proof. exact (EQ_MP (@lem3225436 A s t) (@lem3225291 A s x' t u h1)). Qed.
Lemma lem3225461 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term63 A t u x) = (term63 A t u x).
Proof. exact (eq_refl (term63 A t u x)). Qed.
Lemma lem3225462 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term64 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3225461 A t u x)). Qed.
Lemma lem3225463 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225465 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3225463 A) (@lem3225462 A t u)). Qed.
Lemma lem3225466 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term65 A t u.
Proof. exact (EQ_MP (@lem3225465 A t u) (@lem3225288 A s x' t u h1)). Qed.
Lemma lem3225495 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term162 A s u x) = (term162 A s u x).
Proof. exact (eq_refl (term162 A s u x)). Qed.
Lemma lem3225496 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term160 A s u) = (term160 A s u).
Proof. exact (fun_ext (fun x : A => @lem3225495 A s u x)). Qed.
Lemma lem3225497 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3225499 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term172 A s u) = (term172 A s u).
Proof. exact (MK_COMB (@lem3225497 A) (@lem3225496 A s u)). Qed.
Lemma lem3225500 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) : term172 A s u.
Proof. exact (EQ_MP (@lem3225499 A s u) (@lem3225309 A s u h1)). Qed.
Lemma lem3225517 {A : Type'} (_33152 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term165 A s t _33152.
Proof. exact (@lem3225335 A s x' t u h1 _33152). Qed.
Lemma lem3225518 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33152 : A) : (term165 A s t _33152) = (term63 A s t _33152).
Proof. exact (eq_refl (term165 A s t _33152)). Qed.
Lemma lem3225523 {A : Type'} (_33154 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term165 A s t _33154.
Proof. exact (@lem3225377 A s x' t u h1 _33154). Qed.
Lemma lem3225524 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33154 : A) : (term165 A s t _33154) = (term63 A s t _33154).
Proof. exact (eq_refl (term165 A s t _33154)). Qed.
Lemma lem3225532 {A : Type'} (_33157 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term165 A t u _33157.
Proof. exact (@lem3225424 A s x' t u h1 _33157). Qed.
Lemma lem3225533 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33157 : A) : (term165 A t u _33157) = (term63 A t u _33157).
Proof. exact (eq_refl (term165 A t u _33157)). Qed.
Lemma lem3225535 {A : Type'} (_33158 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term165 A s t _33158.
Proof. exact (@lem3225437 A s x' t u h1 _33158). Qed.
Lemma lem3225536 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33158 : A) : (term165 A s t _33158) = (term63 A s t _33158).
Proof. exact (eq_refl (term165 A s t _33158)). Qed.
Lemma lem3225538 {A : Type'} (_33159 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term165 A t u _33159.
Proof. exact (@lem3225466 A s x' t u h1 _33159). Qed.
Lemma lem3225539 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33159 : A) : (term165 A t u _33159) = (term63 A t u _33159).
Proof. exact (eq_refl (term165 A t u _33159)). Qed.
Lemma lem3225544 {A : Type'} (_33161 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) : term161 A s u _33161.
Proof. exact (@lem3225500 A s u h1 _33161). Qed.
Lemma lem3225545 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33161 : A) : (term161 A s u _33161) = (term162 A s u _33161).
Proof. exact (eq_refl (term161 A s u _33161)). Qed.
Lemma lem3225561 {A : Type'} (_33152 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term63 A s t _33152.
Proof. exact (EQ_MP (@lem3225518 A s t _33152) (@lem3225517 A _33152 s x' t u h1)). Qed.
Lemma lem3225565 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term190 A t x'.
Proof. exact (proj2 (@lem3225292 A s t x' h1)). Qed.
Lemma lem3225581 {A : Type'} (_33154 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term63 A s t _33154.
Proof. exact (EQ_MP (@lem3225524 A s t _33154) (@lem3225523 A _33154 s x' t u h1)). Qed.
Lemma lem3225585 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term190 A t x'.
Proof. exact (proj2 (@lem3225292 A s t x' h1)). Qed.
Lemma lem3225603 {A : Type'} (_33157 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term63 A t u _33157.
Proof. exact (EQ_MP (@lem3225533 A t u _33157) (@lem3225532 A _33157 s x' t u h1)). Qed.
Lemma lem3225609 {A : Type'} (_33158 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term63 A s t _33158.
Proof. exact (EQ_MP (@lem3225536 A s t _33158) (@lem3225535 A _33158 s x' t u h1)). Qed.
Lemma lem3225617 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : term190 A u x.
Proof. exact (proj2 (@lem3225304 A s u x h1)). Qed.
Lemma lem3225623 {A : Type'} (_33159 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term63 A t u _33159.
Proof. exact (EQ_MP (@lem3225539 A t u _33159) (@lem3225538 A _33159 s x' t u h1)). Qed.
Lemma lem3225631 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term91 A s t x') : term190 A s x'.
Proof. exact (proj1 (@lem3225293 A s t x' h1)). Qed.
Lemma lem3225639 {A : Type'} (_33161 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) : term162 A s u _33161.
Proof. exact (EQ_MP (@lem3225545 A s u _33161) (@lem3225544 A _33161 s u h1)). Qed.
Lemma lem3225647 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : s x'.
Proof. exact (proj1 (@lem3225292 A s t x' h1)). Qed.
Lemma lem3225648 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term191 A s x'.
Proof. exact (fun h0 : term190 A s x' => @lem3225647 A s t x' h1). Qed.
Lemma lem3225650 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225651 {A : Type'} (s : A -> Prop) (x' : A) : (term191 A s x') = (s x').
Proof. exact (@lem3225650 (s x')). Qed.
Lemma lem3225652 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3225651 A s x') (@lem3225648 A s t x' h1)). Qed.
Lemma lem3225658 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3225659 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33152 : A) : (term63 A s t _33152) = (term162 A t s _33152).
Proof. exact (@lem3225658 (t _33152) (term190 A s _33152)). Qed.
Lemma lem3225665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3225666 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33152 : A) : (term193 A s t _33152) = (term194 A t s _33152).
Proof. exact (MK_COMB (@lem3225665) (@lem3225659 A t s _33152)). Qed.
Lemma lem3225672 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33152 : A) : (term162 A t s _33152) = (term162 A t s _33152).
Proof. exact (eq_refl (term162 A t s _33152)). Qed.
Lemma lem3225673 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33152 : A) : ((term63 A s t _33152) = (term162 A t s _33152)) = ((term162 A t s _33152) = (term162 A t s _33152)).
Proof. exact (MK_COMB (@lem3225666 A t s _33152) (@lem3225672 A t s _33152)). Qed.
Lemma lem3225675 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3225676 (x : Prop) : (x = x) = True.
Proof. exact (@lem3225675 Prop x). Qed.
Lemma lem3225677 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33152 : A) : ((term162 A t s _33152) = (term162 A t s _33152)) = True.
Proof. exact (@lem3225676 (term162 A t s _33152)). Qed.
Lemma lem3225678 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33152 : A) : ((term63 A s t _33152) = (term162 A t s _33152)) = True.
Proof. exact (TRANS (@lem3225673 A t s _33152) (@lem3225677 A t s _33152)). Qed.
Lemma lem3225679 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33152 : A) : True = ((term63 A s t _33152) = (term162 A t s _33152)).
Proof. exact (SYM (@lem3225678 A t s _33152)). Qed.
Lemma lem3225680 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33152 : A) : (term63 A s t _33152) = (term162 A t s _33152).
Proof. exact (EQ_MP (@lem3225679 A t s _33152) (@lem0)). Qed.
Lemma lem3225681 {A : Type'} (_33152 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term162 A t s _33152.
Proof. exact (EQ_MP (@lem3225680 A t s _33152) (@lem3225561 A _33152 s x' t u h1)). Qed.
Lemma lem3225683 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3225684 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33152 : A) : (term162 A t s _33152) = (term196 A s t _33152).
Proof. exact (@lem3225683 (term190 A s _33152) (t _33152)). Qed.
Lemma lem3225686 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3225687 {A : Type'} (s : A -> Prop) (_33152 : A) : (term197 A s _33152) = (s _33152).
Proof. exact (@lem3225686 (s _33152)). Qed.
Lemma lem3225688 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3225689 {A : Type'} (s : A -> Prop) (_33152 : A) : (term198 A s _33152) = (term29 A s _33152).
Proof. exact (MK_COMB (@lem3225688) (@lem3225687 A s _33152)). Qed.
Lemma lem3225690 {A : Type'} (t : A -> Prop) (_33152 : A) : (t _33152) = (t _33152).
Proof. exact (eq_refl (t _33152)). Qed.
Lemma lem3225691 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33152 : A) : (term196 A s t _33152) = (term31 A s t _33152).
Proof. exact (MK_COMB (@lem3225689 A s _33152) (@lem3225690 A t _33152)). Qed.
Lemma lem3225692 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33152 : A) : (term162 A t s _33152) = (term31 A s t _33152).
Proof. exact (TRANS (@lem3225684 A s t _33152) (@lem3225691 A s t _33152)). Qed.
Lemma lem3225695 {A : Type'} (_33152 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A s t _33152.
Proof. exact (EQ_MP (@lem3225692 A s t _33152) (@lem3225681 A _33152 s x' t u h1)). Qed.
Lemma lem3225696 {A : Type'} (_33152 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A s t _33152.
Proof. exact (@lem3225695 A _33152 s x' t u h1). Qed.
Lemma lem3225697 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A s t x'.
Proof. exact (@lem3225696 A x' s x' t u h1). Qed.
Lemma lem3225700 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : t x'.
Proof. exact (@lem3225697 A s x' t u h2 (@lem3225652 A s t x' h1)). Qed.
Lemma lem3225701 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : term191 A t x'.
Proof. exact (fun h0 : term190 A t x' => @lem3225700 A s x' t u h1 h2). Qed.
Lemma lem3225703 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225704 {A : Type'} (t : A -> Prop) (x' : A) : (term191 A t x') = (t x').
Proof. exact (@lem3225703 (t x')). Qed.
Lemma lem3225705 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : t x'.
Proof. exact (EQ_MP (@lem3225704 A t x') (@lem3225701 A s x' t u h1 h2)). Qed.
Lemma lem3225708 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3225710 {A : Type'} (t : A -> Prop) (x' : A) : (term190 A t x') = (term199 A t x').
Proof. exact (@lem3225708 (t x')). Qed.
Lemma lem3225713 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term199 A t x'.
Proof. exact (EQ_MP (@lem3225710 A t x') (@lem3225565 A s t x' h1)). Qed.
Lemma lem3225716 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : False.
Proof. exact (@lem3225713 A s t x' h1 (@lem3225705 A s x' t u h1 h2)). Qed.
Lemma lem3225717 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : term200.
Proof. exact (fun h0 : ~ False => @lem3225716 A s x' t u h1 h2). Qed.
Lemma lem3225719 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225720 : term200 = False.
Proof. exact (@lem3225719 False). Qed.
Lemma lem3225721 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : False.
Proof. exact (EQ_MP (@lem3225720) (@lem3225717 A s x' t u h1 h2)). Qed.
Lemma lem3225723 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : s x'.
Proof. exact (proj1 (@lem3225292 A s t x' h1)). Qed.
Lemma lem3225724 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term191 A s x'.
Proof. exact (fun h0 : term190 A s x' => @lem3225723 A s t x' h1). Qed.
Lemma lem3225726 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225727 {A : Type'} (s : A -> Prop) (x' : A) : (term191 A s x') = (s x').
Proof. exact (@lem3225726 (s x')). Qed.
Lemma lem3225728 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3225727 A s x') (@lem3225724 A s t x' h1)). Qed.
Lemma lem3225734 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3225735 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33154 : A) : (term63 A s t _33154) = (term162 A t s _33154).
Proof. exact (@lem3225734 (t _33154) (term190 A s _33154)). Qed.
Lemma lem3225741 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3225742 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33154 : A) : (term193 A s t _33154) = (term194 A t s _33154).
Proof. exact (MK_COMB (@lem3225741) (@lem3225735 A t s _33154)). Qed.
Lemma lem3225748 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33154 : A) : (term162 A t s _33154) = (term162 A t s _33154).
Proof. exact (eq_refl (term162 A t s _33154)). Qed.
Lemma lem3225749 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33154 : A) : ((term63 A s t _33154) = (term162 A t s _33154)) = ((term162 A t s _33154) = (term162 A t s _33154)).
Proof. exact (MK_COMB (@lem3225742 A t s _33154) (@lem3225748 A t s _33154)). Qed.
Lemma lem3225751 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3225752 (x : Prop) : (x = x) = True.
Proof. exact (@lem3225751 Prop x). Qed.
Lemma lem3225753 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33154 : A) : ((term162 A t s _33154) = (term162 A t s _33154)) = True.
Proof. exact (@lem3225752 (term162 A t s _33154)). Qed.
Lemma lem3225754 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33154 : A) : ((term63 A s t _33154) = (term162 A t s _33154)) = True.
Proof. exact (TRANS (@lem3225749 A t s _33154) (@lem3225753 A t s _33154)). Qed.
Lemma lem3225755 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33154 : A) : True = ((term63 A s t _33154) = (term162 A t s _33154)).
Proof. exact (SYM (@lem3225754 A t s _33154)). Qed.
Lemma lem3225756 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33154 : A) : (term63 A s t _33154) = (term162 A t s _33154).
Proof. exact (EQ_MP (@lem3225755 A t s _33154) (@lem0)). Qed.
Lemma lem3225757 {A : Type'} (_33154 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term162 A t s _33154.
Proof. exact (EQ_MP (@lem3225756 A t s _33154) (@lem3225581 A _33154 s x' t u h1)). Qed.
Lemma lem3225759 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3225760 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33154 : A) : (term162 A t s _33154) = (term196 A s t _33154).
Proof. exact (@lem3225759 (term190 A s _33154) (t _33154)). Qed.
Lemma lem3225762 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3225763 {A : Type'} (s : A -> Prop) (_33154 : A) : (term197 A s _33154) = (s _33154).
Proof. exact (@lem3225762 (s _33154)). Qed.
Lemma lem3225764 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3225765 {A : Type'} (s : A -> Prop) (_33154 : A) : (term198 A s _33154) = (term29 A s _33154).
Proof. exact (MK_COMB (@lem3225764) (@lem3225763 A s _33154)). Qed.
Lemma lem3225766 {A : Type'} (t : A -> Prop) (_33154 : A) : (t _33154) = (t _33154).
Proof. exact (eq_refl (t _33154)). Qed.
Lemma lem3225767 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33154 : A) : (term196 A s t _33154) = (term31 A s t _33154).
Proof. exact (MK_COMB (@lem3225765 A s _33154) (@lem3225766 A t _33154)). Qed.
Lemma lem3225768 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33154 : A) : (term162 A t s _33154) = (term31 A s t _33154).
Proof. exact (TRANS (@lem3225760 A s t _33154) (@lem3225767 A s t _33154)). Qed.
Lemma lem3225771 {A : Type'} (_33154 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A s t _33154.
Proof. exact (EQ_MP (@lem3225768 A s t _33154) (@lem3225757 A _33154 s x' t u h1)). Qed.
Lemma lem3225772 {A : Type'} (_33154 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A s t _33154.
Proof. exact (@lem3225771 A _33154 s x' t u h1). Qed.
Lemma lem3225773 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A s t x'.
Proof. exact (@lem3225772 A x' s x' t u h1). Qed.
Lemma lem3225776 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : t x'.
Proof. exact (@lem3225773 A s x' t u h2 (@lem3225728 A s t x' h1)). Qed.
Lemma lem3225777 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : term191 A t x'.
Proof. exact (fun h0 : term190 A t x' => @lem3225776 A s x' t u h1 h2). Qed.
Lemma lem3225779 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225780 {A : Type'} (t : A -> Prop) (x' : A) : (term191 A t x') = (t x').
Proof. exact (@lem3225779 (t x')). Qed.
Lemma lem3225781 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : t x'.
Proof. exact (EQ_MP (@lem3225780 A t x') (@lem3225777 A s x' t u h1 h2)). Qed.
Lemma lem3225784 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3225786 {A : Type'} (t : A -> Prop) (x' : A) : (term190 A t x') = (term199 A t x').
Proof. exact (@lem3225784 (t x')). Qed.
Lemma lem3225789 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term199 A t x'.
Proof. exact (EQ_MP (@lem3225786 A t x') (@lem3225585 A s t x' h1)). Qed.
Lemma lem3225792 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : False.
Proof. exact (@lem3225789 A s t x' h1 (@lem3225781 A s x' t u h1 h2)). Qed.
Lemma lem3225793 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : term200.
Proof. exact (fun h0 : ~ False => @lem3225792 A s x' t u h1 h2). Qed.
Lemma lem3225795 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225796 : term200 = False.
Proof. exact (@lem3225795 False). Qed.
Lemma lem3225797 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) : False.
Proof. exact (EQ_MP (@lem3225796) (@lem3225793 A s x' t u h1 h2)). Qed.
Lemma lem3225799 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : s x.
Proof. exact (proj1 (@lem3225304 A s u x h1)). Qed.
Lemma lem3225800 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : term191 A s x.
Proof. exact (fun h0 : term190 A s x => @lem3225799 A s u x h1). Qed.
Lemma lem3225802 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225803 {A : Type'} (s : A -> Prop) (x : A) : (term191 A s x) = (s x).
Proof. exact (@lem3225802 (s x)). Qed.
Lemma lem3225804 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : s x.
Proof. exact (EQ_MP (@lem3225803 A s x) (@lem3225800 A s u x h1)). Qed.
Lemma lem3225810 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3225811 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33158 : A) : (term63 A s t _33158) = (term162 A t s _33158).
Proof. exact (@lem3225810 (t _33158) (term190 A s _33158)). Qed.
Lemma lem3225817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3225818 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33158 : A) : (term193 A s t _33158) = (term194 A t s _33158).
Proof. exact (MK_COMB (@lem3225817) (@lem3225811 A t s _33158)). Qed.
Lemma lem3225824 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33158 : A) : (term162 A t s _33158) = (term162 A t s _33158).
Proof. exact (eq_refl (term162 A t s _33158)). Qed.
Lemma lem3225825 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33158 : A) : ((term63 A s t _33158) = (term162 A t s _33158)) = ((term162 A t s _33158) = (term162 A t s _33158)).
Proof. exact (MK_COMB (@lem3225818 A t s _33158) (@lem3225824 A t s _33158)). Qed.
Lemma lem3225827 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3225828 (x : Prop) : (x = x) = True.
Proof. exact (@lem3225827 Prop x). Qed.
Lemma lem3225829 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33158 : A) : ((term162 A t s _33158) = (term162 A t s _33158)) = True.
Proof. exact (@lem3225828 (term162 A t s _33158)). Qed.
Lemma lem3225830 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33158 : A) : ((term63 A s t _33158) = (term162 A t s _33158)) = True.
Proof. exact (TRANS (@lem3225825 A t s _33158) (@lem3225829 A t s _33158)). Qed.
Lemma lem3225831 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33158 : A) : True = ((term63 A s t _33158) = (term162 A t s _33158)).
Proof. exact (SYM (@lem3225830 A t s _33158)). Qed.
Lemma lem3225832 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33158 : A) : (term63 A s t _33158) = (term162 A t s _33158).
Proof. exact (EQ_MP (@lem3225831 A t s _33158) (@lem0)). Qed.
Lemma lem3225833 {A : Type'} (_33158 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term162 A t s _33158.
Proof. exact (EQ_MP (@lem3225832 A t s _33158) (@lem3225609 A _33158 s x' t u h1)). Qed.
Lemma lem3225835 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3225836 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33158 : A) : (term162 A t s _33158) = (term196 A s t _33158).
Proof. exact (@lem3225835 (term190 A s _33158) (t _33158)). Qed.
Lemma lem3225838 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3225839 {A : Type'} (s : A -> Prop) (_33158 : A) : (term197 A s _33158) = (s _33158).
Proof. exact (@lem3225838 (s _33158)). Qed.
Lemma lem3225840 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3225841 {A : Type'} (s : A -> Prop) (_33158 : A) : (term198 A s _33158) = (term29 A s _33158).
Proof. exact (MK_COMB (@lem3225840) (@lem3225839 A s _33158)). Qed.
Lemma lem3225842 {A : Type'} (t : A -> Prop) (_33158 : A) : (t _33158) = (t _33158).
Proof. exact (eq_refl (t _33158)). Qed.
Lemma lem3225843 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33158 : A) : (term196 A s t _33158) = (term31 A s t _33158).
Proof. exact (MK_COMB (@lem3225841 A s _33158) (@lem3225842 A t _33158)). Qed.
Lemma lem3225844 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33158 : A) : (term162 A t s _33158) = (term31 A s t _33158).
Proof. exact (TRANS (@lem3225836 A s t _33158) (@lem3225843 A s t _33158)). Qed.
Lemma lem3225847 {A : Type'} (_33158 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A s t _33158.
Proof. exact (EQ_MP (@lem3225844 A s t _33158) (@lem3225833 A _33158 s x' t u h1)). Qed.
Lemma lem3225848 {A : Type'} (_33158 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A s t _33158.
Proof. exact (@lem3225847 A _33158 s x' t u h1). Qed.
Lemma lem3225849 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A s t x.
Proof. exact (@lem3225848 A x s x' t u h1). Qed.
Lemma lem3225852 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s u x) (h2 : term139 A s x' t u) : t x.
Proof. exact (@lem3225849 A x s x' t u h2 (@lem3225804 A s u x h1)). Qed.
Lemma lem3225853 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s u x) (h2 : term139 A s x' t u) : term191 A t x.
Proof. exact (fun h0 : term190 A t x => @lem3225852 A x s x' t u h1 h2). Qed.
Lemma lem3225855 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225856 {A : Type'} (t : A -> Prop) (x : A) : (term191 A t x) = (t x).
Proof. exact (@lem3225855 (t x)). Qed.
Lemma lem3225857 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s u x) (h2 : term139 A s x' t u) : t x.
Proof. exact (EQ_MP (@lem3225856 A t x) (@lem3225853 A x s x' t u h1 h2)). Qed.
Lemma lem3225863 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3225864 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33157 : A) : (term63 A t u _33157) = (term162 A u t _33157).
Proof. exact (@lem3225863 (u _33157) (term190 A t _33157)). Qed.
Lemma lem3225870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3225871 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33157 : A) : (term193 A t u _33157) = (term194 A u t _33157).
Proof. exact (MK_COMB (@lem3225870) (@lem3225864 A u t _33157)). Qed.
Lemma lem3225877 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33157 : A) : (term162 A u t _33157) = (term162 A u t _33157).
Proof. exact (eq_refl (term162 A u t _33157)). Qed.
Lemma lem3225878 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33157 : A) : ((term63 A t u _33157) = (term162 A u t _33157)) = ((term162 A u t _33157) = (term162 A u t _33157)).
Proof. exact (MK_COMB (@lem3225871 A u t _33157) (@lem3225877 A u t _33157)). Qed.
Lemma lem3225880 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3225881 (x : Prop) : (x = x) = True.
Proof. exact (@lem3225880 Prop x). Qed.
Lemma lem3225882 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33157 : A) : ((term162 A u t _33157) = (term162 A u t _33157)) = True.
Proof. exact (@lem3225881 (term162 A u t _33157)). Qed.
Lemma lem3225883 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33157 : A) : ((term63 A t u _33157) = (term162 A u t _33157)) = True.
Proof. exact (TRANS (@lem3225878 A u t _33157) (@lem3225882 A u t _33157)). Qed.
Lemma lem3225884 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33157 : A) : True = ((term63 A t u _33157) = (term162 A u t _33157)).
Proof. exact (SYM (@lem3225883 A u t _33157)). Qed.
Lemma lem3225885 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33157 : A) : (term63 A t u _33157) = (term162 A u t _33157).
Proof. exact (EQ_MP (@lem3225884 A u t _33157) (@lem0)). Qed.
Lemma lem3225886 {A : Type'} (_33157 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term162 A u t _33157.
Proof. exact (EQ_MP (@lem3225885 A u t _33157) (@lem3225603 A _33157 s x' t u h1)). Qed.
Lemma lem3225888 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3225889 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33157 : A) : (term162 A u t _33157) = (term196 A t u _33157).
Proof. exact (@lem3225888 (term190 A t _33157) (u _33157)). Qed.
Lemma lem3225891 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3225892 {A : Type'} (t : A -> Prop) (_33157 : A) : (term197 A t _33157) = (t _33157).
Proof. exact (@lem3225891 (t _33157)). Qed.
Lemma lem3225893 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3225894 {A : Type'} (t : A -> Prop) (_33157 : A) : (term198 A t _33157) = (term29 A t _33157).
Proof. exact (MK_COMB (@lem3225893) (@lem3225892 A t _33157)). Qed.
Lemma lem3225895 {A : Type'} (u : A -> Prop) (_33157 : A) : (u _33157) = (u _33157).
Proof. exact (eq_refl (u _33157)). Qed.
Lemma lem3225896 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33157 : A) : (term196 A t u _33157) = (term31 A t u _33157).
Proof. exact (MK_COMB (@lem3225894 A t _33157) (@lem3225895 A u _33157)). Qed.
Lemma lem3225897 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33157 : A) : (term162 A u t _33157) = (term31 A t u _33157).
Proof. exact (TRANS (@lem3225889 A t u _33157) (@lem3225896 A t u _33157)). Qed.
Lemma lem3225900 {A : Type'} (_33157 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A t u _33157.
Proof. exact (EQ_MP (@lem3225897 A t u _33157) (@lem3225886 A _33157 s x' t u h1)). Qed.
Lemma lem3225901 {A : Type'} (_33157 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A t u _33157.
Proof. exact (@lem3225900 A _33157 s x' t u h1). Qed.
Lemma lem3225902 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A t u x.
Proof. exact (@lem3225901 A x s x' t u h1). Qed.
Lemma lem3225905 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s u x) (h2 : term139 A s x' t u) : u x.
Proof. exact (@lem3225902 A x s x' t u h2 (@lem3225857 A x s x' t u h1 h2)). Qed.
Lemma lem3225906 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s u x) (h2 : term139 A s x' t u) : term191 A u x.
Proof. exact (fun h0 : term190 A u x => @lem3225905 A x s x' t u h1 h2). Qed.
Lemma lem3225908 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225909 {A : Type'} (u : A -> Prop) (x : A) : (term191 A u x) = (u x).
Proof. exact (@lem3225908 (u x)). Qed.
Lemma lem3225910 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s u x) (h2 : term139 A s x' t u) : u x.
Proof. exact (EQ_MP (@lem3225909 A u x) (@lem3225906 A x s x' t u h1 h2)). Qed.
Lemma lem3225913 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3225915 {A : Type'} (u : A -> Prop) (x : A) : (term190 A u x) = (term199 A u x).
Proof. exact (@lem3225913 (u x)). Qed.
Lemma lem3225918 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : term199 A u x.
Proof. exact (EQ_MP (@lem3225915 A u x) (@lem3225617 A s u x h1)). Qed.
Lemma lem3225921 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s u x) (h2 : term139 A s x' t u) : False.
Proof. exact (@lem3225918 A s u x h1 (@lem3225910 A x s x' t u h1 h2)). Qed.
Lemma lem3225922 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s u x) (h2 : term139 A s x' t u) : term200.
Proof. exact (fun h0 : ~ False => @lem3225921 A x s x' t u h1 h2). Qed.
Lemma lem3225924 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225925 : term200 = False.
Proof. exact (@lem3225924 False). Qed.
Lemma lem3225926 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term87 A s u x) (h2 : term139 A s x' t u) : False.
Proof. exact (EQ_MP (@lem3225925) (@lem3225922 A x s x' t u h1 h2)). Qed.
Lemma lem3225928 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term91 A s t x') : t x'.
Proof. exact (proj2 (@lem3225293 A s t x' h1)). Qed.
Lemma lem3225929 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term91 A s t x') : term191 A t x'.
Proof. exact (fun h0 : term190 A t x' => @lem3225928 A s t x' h1). Qed.
Lemma lem3225931 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225932 {A : Type'} (t : A -> Prop) (x' : A) : (term191 A t x') = (t x').
Proof. exact (@lem3225931 (t x')). Qed.
Lemma lem3225933 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term91 A s t x') : t x'.
Proof. exact (EQ_MP (@lem3225932 A t x') (@lem3225929 A s t x' h1)). Qed.
Lemma lem3225939 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3225940 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33159 : A) : (term63 A t u _33159) = (term162 A u t _33159).
Proof. exact (@lem3225939 (u _33159) (term190 A t _33159)). Qed.
Lemma lem3225946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3225947 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33159 : A) : (term193 A t u _33159) = (term194 A u t _33159).
Proof. exact (MK_COMB (@lem3225946) (@lem3225940 A u t _33159)). Qed.
Lemma lem3225953 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33159 : A) : (term162 A u t _33159) = (term162 A u t _33159).
Proof. exact (eq_refl (term162 A u t _33159)). Qed.
Lemma lem3225954 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33159 : A) : ((term63 A t u _33159) = (term162 A u t _33159)) = ((term162 A u t _33159) = (term162 A u t _33159)).
Proof. exact (MK_COMB (@lem3225947 A u t _33159) (@lem3225953 A u t _33159)). Qed.
Lemma lem3225956 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3225957 (x : Prop) : (x = x) = True.
Proof. exact (@lem3225956 Prop x). Qed.
Lemma lem3225958 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33159 : A) : ((term162 A u t _33159) = (term162 A u t _33159)) = True.
Proof. exact (@lem3225957 (term162 A u t _33159)). Qed.
Lemma lem3225959 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33159 : A) : ((term63 A t u _33159) = (term162 A u t _33159)) = True.
Proof. exact (TRANS (@lem3225954 A u t _33159) (@lem3225958 A u t _33159)). Qed.
Lemma lem3225960 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33159 : A) : True = ((term63 A t u _33159) = (term162 A u t _33159)).
Proof. exact (SYM (@lem3225959 A u t _33159)). Qed.
Lemma lem3225961 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33159 : A) : (term63 A t u _33159) = (term162 A u t _33159).
Proof. exact (EQ_MP (@lem3225960 A u t _33159) (@lem0)). Qed.
Lemma lem3225962 {A : Type'} (_33159 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term162 A u t _33159.
Proof. exact (EQ_MP (@lem3225961 A u t _33159) (@lem3225623 A _33159 s x' t u h1)). Qed.
Lemma lem3225964 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3225965 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33159 : A) : (term162 A u t _33159) = (term196 A t u _33159).
Proof. exact (@lem3225964 (term190 A t _33159) (u _33159)). Qed.
Lemma lem3225967 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3225968 {A : Type'} (t : A -> Prop) (_33159 : A) : (term197 A t _33159) = (t _33159).
Proof. exact (@lem3225967 (t _33159)). Qed.
Lemma lem3225969 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3225970 {A : Type'} (t : A -> Prop) (_33159 : A) : (term198 A t _33159) = (term29 A t _33159).
Proof. exact (MK_COMB (@lem3225969) (@lem3225968 A t _33159)). Qed.
Lemma lem3225971 {A : Type'} (u : A -> Prop) (_33159 : A) : (u _33159) = (u _33159).
Proof. exact (eq_refl (u _33159)). Qed.
Lemma lem3225972 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33159 : A) : (term196 A t u _33159) = (term31 A t u _33159).
Proof. exact (MK_COMB (@lem3225970 A t _33159) (@lem3225971 A u _33159)). Qed.
Lemma lem3225973 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33159 : A) : (term162 A u t _33159) = (term31 A t u _33159).
Proof. exact (TRANS (@lem3225965 A t u _33159) (@lem3225972 A t u _33159)). Qed.
Lemma lem3225976 {A : Type'} (_33159 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A t u _33159.
Proof. exact (EQ_MP (@lem3225973 A t u _33159) (@lem3225962 A _33159 s x' t u h1)). Qed.
Lemma lem3225977 {A : Type'} (_33159 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A t u _33159.
Proof. exact (@lem3225976 A _33159 s x' t u h1). Qed.
Lemma lem3225978 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) : term31 A t u x'.
Proof. exact (@lem3225977 A x' s x' t u h1). Qed.
Lemma lem3225981 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term91 A s t x') (h2 : term139 A s x' t u) : u x'.
Proof. exact (@lem3225978 A s x' t u h2 (@lem3225933 A s t x' h1)). Qed.
Lemma lem3225982 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term91 A s t x') (h2 : term139 A s x' t u) : term191 A u x'.
Proof. exact (fun h0 : term190 A u x' => @lem3225981 A s x' t u h1 h2). Qed.
Lemma lem3225984 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3225985 {A : Type'} (u : A -> Prop) (x' : A) : (term191 A u x') = (u x').
Proof. exact (@lem3225984 (u x')). Qed.
Lemma lem3225986 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term91 A s t x') (h2 : term139 A s x' t u) : u x'.
Proof. exact (EQ_MP (@lem3225985 A u x') (@lem3225982 A s x' t u h1 h2)). Qed.
Lemma lem3225988 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3225989 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33161 : A) : (term162 A s u _33161) = (term196 A u s _33161).
Proof. exact (@lem3225988 (term190 A u _33161) (s _33161)). Qed.
Lemma lem3225991 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3225992 {A : Type'} (u : A -> Prop) (_33161 : A) : (term197 A u _33161) = (u _33161).
Proof. exact (@lem3225991 (u _33161)). Qed.
Lemma lem3225993 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3225994 {A : Type'} (u : A -> Prop) (_33161 : A) : (term198 A u _33161) = (term29 A u _33161).
Proof. exact (MK_COMB (@lem3225993) (@lem3225992 A u _33161)). Qed.
Lemma lem3225995 {A : Type'} (s : A -> Prop) (_33161 : A) : (s _33161) = (s _33161).
Proof. exact (eq_refl (s _33161)). Qed.
Lemma lem3225996 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33161 : A) : (term196 A u s _33161) = (term31 A u s _33161).
Proof. exact (MK_COMB (@lem3225994 A u _33161) (@lem3225995 A s _33161)). Qed.
Lemma lem3225997 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33161 : A) : (term162 A s u _33161) = (term31 A u s _33161).
Proof. exact (TRANS (@lem3225989 A u s _33161) (@lem3225996 A u s _33161)). Qed.
Lemma lem3226000 {A : Type'} (_33161 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) : term31 A u s _33161.
Proof. exact (EQ_MP (@lem3225997 A u s _33161) (@lem3225639 A _33161 s u h1)). Qed.
Lemma lem3226001 {A : Type'} (_33161 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) : term31 A u s _33161.
Proof. exact (@lem3226000 A _33161 s u h1). Qed.
Lemma lem3226002 {A : Type'} (x' : A) (s : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) : term31 A u s x'.
Proof. exact (@lem3226001 A x' s u h1). Qed.
Lemma lem3226005 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) (h2 : term91 A s t x') (h3 : term139 A s x' t u) : s x'.
Proof. exact (@lem3226002 A x' s u h1 (@lem3225986 A s x' t u h2 h3)). Qed.
Lemma lem3226006 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) (h2 : term91 A s t x') (h3 : term139 A s x' t u) : term191 A s x'.
Proof. exact (fun h0 : term190 A s x' => @lem3226005 A s x' t u h1 h2 h3). Qed.
Lemma lem3226008 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3226009 {A : Type'} (s : A -> Prop) (x' : A) : (term191 A s x') = (s x').
Proof. exact (@lem3226008 (s x')). Qed.
Lemma lem3226010 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) (h2 : term91 A s t x') (h3 : term139 A s x' t u) : s x'.
Proof. exact (EQ_MP (@lem3226009 A s x') (@lem3226006 A s x' t u h1 h2 h3)). Qed.
Lemma lem3226013 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3226015 {A : Type'} (s : A -> Prop) (x' : A) : (term190 A s x') = (term199 A s x').
Proof. exact (@lem3226013 (s x')). Qed.
Lemma lem3226018 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term91 A s t x') : term199 A s x'.
Proof. exact (EQ_MP (@lem3226015 A s x') (@lem3225631 A s t x' h1)). Qed.
Lemma lem3226021 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) (h2 : term91 A s t x') (h3 : term139 A s x' t u) : False.
Proof. exact (@lem3226018 A s t x' h2 (@lem3226010 A s x' t u h1 h2 h3)). Qed.
Lemma lem3226022 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) (h2 : term91 A s t x') (h3 : term139 A s x' t u) : term200.
Proof. exact (fun h0 : ~ False => @lem3226021 A s x' t u h1 h2 h3). Qed.
Lemma lem3226024 (p : Prop) : (term192 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3226025 : term200 = False.
Proof. exact (@lem3226024 False). Qed.
Lemma lem3226026 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term177 A s u) (h2 : term91 A s t x') (h3 : term139 A s x' t u) : False.
Proof. exact (EQ_MP (@lem3226025) (@lem3226022 A s x' t u h1 h2 h3)). Qed.
Lemma lem3226027 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term91 A s t x') (h2 : term139 A s x' t u) (h3 : term186 A x s u) : False.
Proof. exact (or_elim (@lem3225227 A x s u h3) (fun h0 : term87 A s u x => @lem3225926 A x s x' t u h0 h2) (fun h0 : term177 A s u => @lem3226026 A s x' t u h0 h1 h2)). Qed.
Lemma lem3226028 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term139 A s x' t u) (h3 : term186 A x s u) : False.
Proof. exact (or_elim (@lem3225227 A x s u h3) (fun h0 : term87 A s u x => @lem3225721 A s x' t u h1 h2) (fun h0 : term177 A s u => @lem3225797 A s x' t u h1 h2)). Qed.
Lemma lem3226029 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) (h2 : term186 A x s u) : False.
Proof. exact (or_elim (@lem3225290 A s x' t u h1) (fun h0 : term87 A s t x' => @lem3226028 A x' t x s u h0 h1 h2) (fun h0 : term91 A s t x' => @lem3226027 A x' t x s u h0 h1 h2)). Qed.
Lemma lem3226030 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) (h2 : term186 A x s u) : (term139 A s x' t u) = False.
Proof. exact (prop_ext (fun h3 : term139 A s x' t u => @lem3226029 A x' t x s u h1 h2) (fun h3 : False => @lem3225287 A s x' t u h1)). Qed.
Lemma lem3226031 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) (h2 : term186 A x s u) : False.
Proof. exact (EQ_MP (@lem3226030 A x' t x s u h1 h2) (@lem3225287 A s x' t u h1)). Qed.
Lemma lem3226032 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) (h2 : term186 A x s u) : (term186 A x s u) = False.
Proof. exact (prop_ext (fun h3 : term186 A x s u => @lem3226031 A x' t x s u h1 h2) (fun h3 : False => @lem3225227 A x s u h2)). Qed.
Lemma lem3226033 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term139 A s x' t u) (h2 : term186 A x s u) : False.
Proof. exact (EQ_MP (@lem3226032 A x' t x s u h1 h2) (@lem3225227 A x s u h2)). Qed.
Lemma lem3226034 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term44 A s t u) (h2 : term186 A x s u) : False.
Proof. exact (ex_elim (@lem3224993 A s t u h1) (fun x' : A => fun h0 : term141 A s t u x' => @lem3226033 A x' t x s u h0 h2)). Qed.
Lemma lem3226035 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term62 A s u) (h2 : term44 A s t u) : False.
Proof. exact (ex_elim (@lem3225179 A s u h1) (fun x : A => fun h0 : term188 A s u x => @lem3226034 A t x s u h2 h0)). Qed.
Lemma lem3226036 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term62 A s u) (h2 : term44 A s t u) : (term62 A s u) = False.
Proof. exact (prop_ext (fun h3 : term62 A s u => @lem3226035 A s t u h1 h2) (fun h3 : False => @lem3224703 A s u h1)). Qed.
Lemma lem3226037 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term62 A s u) (h2 : term44 A s t u) : False.
Proof. exact (EQ_MP (@lem3226036 A s t u h1 h2) (@lem3224703 A s u h1)). Qed.
Lemma lem3226038 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term44 A s t u) : term61 A s u.
Proof. exact (fun h0 : term62 A s u => @lem3226037 A s t u h0 h1). Qed.
Lemma lem3226039 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term44 A s t u) : term42 A s u.
Proof. exact (EQ_MP (@lem3224702 A s u) (@lem3226038 A s t u h1)). Qed.
Lemma lem3226040 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term46 A t s u.
Proof. exact (fun h0 : term44 A s t u => @lem3226039 A s t u h0). Qed.
Lemma lem3226045 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term48 A t s.
Proof. exact (fun u : A -> Prop => @lem3226040 A t s u). Qed.
Lemma lem3226050 {A : Type'} (s : A -> Prop) : term50 A s.
Proof. exact (fun t : A -> Prop => @lem3226045 A t s). Qed.
Lemma lem3226055 {A : Type'} : term52 A.
Proof. exact (fun s : A -> Prop => @lem3226050 A s). Qed.
Lemma lem3226056 {A : Type'} : term54 A.
Proof. exact (EQ_MP (@lem3224697 A) (@lem3226055 A)). Qed.
Lemma lem3226058 {A : Type'} : term54 A.
Proof. exact (@lem3224509 A (@lem3226056 A)). Qed.
Lemma lem3226059 {A : Type'} (h1 : term55 A) : False.
Proof. exact (@lem3226058 A (@lem3224493 A h1)). Qed.
Lemma lem3226060 {A : Type'} (h1 : term55 A) : (term55 A) = False.
Proof. exact (prop_ext (fun h2 : term55 A => @lem3226059 A h1) (fun h2 : False => @lem3224493 A h1)). Qed.
Lemma lem3226061 {A : Type'} (h1 : term55 A) : False.
Proof. exact (EQ_MP (@lem3226060 A h1) (@lem3224493 A h1)). Qed.
Lemma lem3226062 {A : Type'} : term54 A.
Proof. exact (fun h0 : term55 A => @lem3226061 A h0). Qed.
Lemma lem3226063 {A : Type'} : term52 A.
Proof. exact (EQ_MP (@lem3224492 A) (@lem3226062 A)). Qed.
Lemma lem3226064 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem3224488 A) (@lem3226063 A)). Qed.
Lemma lem3226065 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem3224292 A) (@lem3226064 A)). Qed.
