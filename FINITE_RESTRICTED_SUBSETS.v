Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_RESTRICTED_SUBSETS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_POWERSET_spec.
Require Import FINITE_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm1842_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm7_spec.
Lemma lem4604277 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4604278 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term1 A s.
Proof. exact (@lem4604277 A h1 s). Qed.
Lemma lem4604279 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem4604280 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (EQ_MP (@lem4604279 A s) (@lem4604278 A s h1)). Qed.
Lemma lem4604281 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term3 A s t.
Proof. exact (@lem4604280 A s h1 t). Qed.
Lemma lem4604282 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A s t) = (term4 A t s).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem4604283 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term0 A) : term4 A t s.
Proof. exact (EQ_MP (@lem4604282 A t s) (@lem4604281 A s t h1)). Qed.
Lemma lem4604284 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term5 A s t.
Proof. exact (h1). Qed.
Lemma lem4604285 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : @FINITE A s.
Proof. exact (@lem4604283 A t s h1 (@lem4604284 A s t h2)). Qed.
Lemma lem4604286 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term6 A s.
Proof. exact (fun h0 : term0 A => @lem4604285 A s t h0 h1). Qed.
Lemma lem4604287 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term7 A s.
Proof. exact (h1). Qed.
Lemma lem4604288 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term6 A s.
Proof. exact (ex_elim (@lem4604287 A s h1) (fun t : A -> Prop => fun h0 : term8 A s t => @lem4604286 A s t h0)). Qed.
Lemma lem4604289 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4604290 {A : Type'} (s : A -> Prop) (h1 : term0 A) (h2 : term7 A s) : @FINITE A s.
Proof. exact (@lem4604288 A s h2 (@lem4604289 A h1)). Qed.
Lemma lem4604291 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term9 A s.
Proof. exact (fun h0 : term7 A s => @lem4604290 A s h1 h0). Qed.
Lemma lem4604292 {A : Type'} (h1 : term0 A) : term10 A.
Proof. exact (fun s : A -> Prop => @lem4604291 A s h1). Qed.
Lemma lem4604293 {A : Type'} : term11 A.
Proof. exact (fun h0 : term0 A => @lem4604292 A h0). Qed.
Lemma lem4604294 {A : Type'} : term10 A.
Proof. exact (@lem4604293 A (@lem3599924 A)). Qed.
Lemma lem4604295 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem4604294 A s). Qed.
Lemma lem4604296 {A : Type'} (s : A -> Prop) : (term12 A s) = (term9 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem4604298 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4604300 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem4604296 A s) (@lem4604295 A s)). Qed.
Lemma lem4604301 {A : Type'} (s : type686 A) : term13 A s.
Proof. exact (@lem4604300 (A -> Prop) s). Qed.
Lemma lem4604302 {A : Type'} (s : A -> Prop) (P : type686 A) : term14 A s P.
Proof. exact (@lem4604301 A (term15 A s P)). Qed.
Lemma lem4604303 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem4603107 A s). Qed.
Lemma lem4604304 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem4604305 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem4604304 A s) (@lem4604303 A s)). Qed.
Lemma lem4604306 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4604307 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term18 A s.
Proof. exact (@lem4604305 A s (@lem4604306 A s h1)). Qed.
Lemma lem4604308 {A : Type'} (s : A -> Prop) : (term18 A s) = ((term18 A s) = True).
Proof. exact (@lem7 (term18 A s)). Qed.
Lemma lem4604309 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term18 A s) = True.
Proof. exact (EQ_MP (@lem4604308 A s) (@lem4604307 A s h1)). Qed.
Lemma lem4604315 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4604320 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (fun h0 : @FINITE A s => @lem4604309 A s h0). Qed.
Lemma lem4604321 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (@lem4604320 A s). Qed.
Lemma lem4604323 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4604315 A s) (@lem4604298 A s h1)). Qed.
Lemma lem4604324 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4604323 A s h1)). Qed.
Lemma lem4604325 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4604324 A s h1) (@lem0)). Qed.
Lemma lem4604326 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term18 A s) = True.
Proof. exact (@lem4604321 A s (@lem4604325 A s h1)). Qed.
Lemma lem4604327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4604328 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term20 A s) = (and True).
Proof. exact (MK_COMB (@lem4604327) (@lem4604326 A s h1)). Qed.
Lemma lem4604339 {A : Type'} (P : type686 A) (s : A -> Prop) : (term21 A P s) = (term21 A P s).
Proof. exact (eq_refl (term21 A P s)). Qed.
Lemma lem4604340 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : (term22 A P s) = (term23 A P s).
Proof. exact (MK_COMB (@lem4604328 A s h1) (@lem4604339 A P s)). Qed.
Lemma lem4604342 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4604343 {A : Type'} (P : type686 A) (s : A -> Prop) : (term23 A P s) = (term21 A P s).
Proof. exact (@lem4604342 (term21 A P s)). Qed.
Lemma lem4604354 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : (term22 A P s) = (term21 A P s).
Proof. exact (TRANS (@lem4604340 A P s h1) (@lem4604343 A P s)). Qed.
Lemma lem4604355 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : (term21 A P s) = (term22 A P s).
Proof. exact (SYM (@lem4604354 A P s h1)). Qed.
Lemma lem4604357 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4604358 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term25 A s t).
Proof. exact (@lem4604357 (A -> Prop) s t). Qed.
Lemma lem4604359 {A : Type'} (P : type686 A) (s : A -> Prop) : (term21 A P s) = (term26 A P s).
Proof. exact (@lem4604358 A (term15 A s P) (term27 A s)). Qed.
Lemma lem4604373 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4604374 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term24 A s t).
Proof. exact (@lem4604373 A s t). Qed.
Lemma lem4604375 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term24 A t s).
Proof. exact (@lem4604374 A t s). Qed.
Lemma lem4604382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4604383 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term28 A t s) = (term29 A t s).
Proof. exact (MK_COMB (@lem4604382) (@lem4604375 A t s)). Qed.
Lemma lem4604384 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem4604385 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term30 A s P t) = (term31 A s P t).
Proof. exact (MK_COMB (@lem4604383 A t s) (@lem4604384 A P t)). Qed.
Lemma lem4604388 {A : Type'} (GEN_PVAR_158 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_158) = (@SETSPEC (A -> Prop) GEN_PVAR_158).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_158)). Qed.
Lemma lem4604389 {A : Type'} (GEN_PVAR_158 : A -> Prop) (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term32 A GEN_PVAR_158 s P t) = (term33 A GEN_PVAR_158 s P t).
Proof. exact (MK_COMB (@lem4604388 A GEN_PVAR_158) (@lem4604385 A s P t)). Qed.
Lemma lem4604390 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4604391 {A : Type'} (GEN_PVAR_158 : A -> Prop) (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term34 A GEN_PVAR_158 s P t) = (term35 A GEN_PVAR_158 s P t).
Proof. exact (MK_COMB (@lem4604389 A GEN_PVAR_158 s P t) (@lem4604390 A t)). Qed.
Lemma lem4604392 {A : Type'} (GEN_PVAR_158 : A -> Prop) (s : A -> Prop) (P : type686 A) : (term36 A GEN_PVAR_158 s P) = (term37 A GEN_PVAR_158 s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4604391 A GEN_PVAR_158 s P t)). Qed.
Lemma lem4604393 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4604394 {A : Type'} (GEN_PVAR_158 : A -> Prop) (s : A -> Prop) (P : type686 A) : (term38 A GEN_PVAR_158 s P) = (term39 A GEN_PVAR_158 s P).
Proof. exact (MK_COMB (@lem4604393 A) (@lem4604392 A GEN_PVAR_158 s P)). Qed.
Lemma lem4604399 {A : Type'} (s : A -> Prop) (P : type686 A) : (term40 A s P) = (term41 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_158 : A -> Prop => @lem4604394 A GEN_PVAR_158 s P)). Qed.
Lemma lem4604400 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4604401 {A : Type'} (s : A -> Prop) (P : type686 A) : (term15 A s P) = (term42 A s P).
Proof. exact (MK_COMB (@lem4604400 A) (@lem4604399 A s P)). Qed.
Lemma lem4604402 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4604403 {A : Type'} (x : A -> Prop) (s : A -> Prop) (P : type686 A) : (term43 A x s P) = (term44 A x s P).
Proof. exact (MK_COMB (@lem4604402 A x) (@lem4604401 A s P)). Qed.
Lemma lem4604404 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4604405 {A : Type'} (x : A -> Prop) (s : A -> Prop) (P : type686 A) : (term45 A x s P) = (term46 A x s P).
Proof. exact (MK_COMB (@lem4604404) (@lem4604403 A x s P)). Qed.
Lemma lem4604411 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4604412 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term24 A s t).
Proof. exact (@lem4604411 A s t). Qed.
Lemma lem4604413 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term24 A t s).
Proof. exact (@lem4604412 A t s). Qed.
Lemma lem4604420 {A : Type'} (GEN_PVAR_157 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_157) = (@SETSPEC (A -> Prop) GEN_PVAR_157).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_157)). Qed.
Lemma lem4604421 {A : Type'} (GEN_PVAR_157 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term47 A GEN_PVAR_157 t s) = (term48 A GEN_PVAR_157 t s).
Proof. exact (MK_COMB (@lem4604420 A GEN_PVAR_157) (@lem4604413 A t s)). Qed.
Lemma lem4604422 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4604423 {A : Type'} (GEN_PVAR_157 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term49 A GEN_PVAR_157 s t) = (term50 A GEN_PVAR_157 s t).
Proof. exact (MK_COMB (@lem4604421 A GEN_PVAR_157 t s) (@lem4604422 A t)). Qed.
Lemma lem4604424 {A : Type'} (GEN_PVAR_157 : A -> Prop) (s : A -> Prop) : (term51 A GEN_PVAR_157 s) = (term52 A GEN_PVAR_157 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4604423 A GEN_PVAR_157 s t)). Qed.
Lemma lem4604425 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4604426 {A : Type'} (GEN_PVAR_157 : A -> Prop) (s : A -> Prop) : (term53 A GEN_PVAR_157 s) = (term54 A GEN_PVAR_157 s).
Proof. exact (MK_COMB (@lem4604425 A) (@lem4604424 A GEN_PVAR_157 s)). Qed.
Lemma lem4604431 {A : Type'} (s : A -> Prop) : (term55 A s) = (term56 A s).
Proof. exact (fun_ext (fun GEN_PVAR_157 : A -> Prop => @lem4604426 A GEN_PVAR_157 s)). Qed.
Lemma lem4604432 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4604433 {A : Type'} (s : A -> Prop) : (term27 A s) = (term57 A s).
Proof. exact (MK_COMB (@lem4604432 A) (@lem4604431 A s)). Qed.
Lemma lem4604434 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4604435 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term58 A x s) = (term59 A x s).
Proof. exact (MK_COMB (@lem4604434 A x) (@lem4604433 A s)). Qed.
Lemma lem4604436 {A : Type'} (P : type686 A) (x : A -> Prop) (s : A -> Prop) : (term60 A P x s) = (term61 A P x s).
Proof. exact (MK_COMB (@lem4604405 A x s P) (@lem4604435 A x s)). Qed.
Lemma lem4604439 {A : Type'} (P : type686 A) (s : A -> Prop) : (term62 A P s) = (term63 A P s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4604436 A P x s)). Qed.
Lemma lem4604440 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4604441 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = (term64 A P s).
Proof. exact (MK_COMB (@lem4604440 A) (@lem4604439 A P s)). Qed.
Lemma lem4604446 {A : Type'} (P : type686 A) (s : A -> Prop) : (term21 A P s) = (term64 A P s).
Proof. exact (TRANS (@lem4604359 A P s) (@lem4604441 A P s)). Qed.
Lemma lem4604447 {A : Type'} (P : type686 A) (s : A -> Prop) : (term64 A P s) = (term21 A P s).
Proof. exact (SYM (@lem4604446 A P s)). Qed.
Lemma lem4604455 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term65 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4604456 {A : Type'} (p : type686 A) (x : A -> Prop) : (term66 A x p) = (p x).
Proof. exact (@lem4604455 (A -> Prop) p x). Qed.
Lemma lem4604457 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : (term67 A x s P) = (term68 A s P x).
Proof. exact (@lem4604456 A (term69 A s P) x). Qed.
Lemma lem4604458 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term68 A s P t) = (term31 A s P t).
Proof. exact (eq_refl (term68 A s P t)). Qed.
Lemma lem4604459 {A : Type'} (GEN_PVAR_158 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_158) = (@SETSPEC (A -> Prop) GEN_PVAR_158).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_158)). Qed.
Lemma lem4604460 {A : Type'} (GEN_PVAR_158 : A -> Prop) (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term70 A GEN_PVAR_158 s P t) = (term33 A GEN_PVAR_158 s P t).
Proof. exact (MK_COMB (@lem4604459 A GEN_PVAR_158) (@lem4604458 A s P t)). Qed.
Lemma lem4604461 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4604462 {A : Type'} (GEN_PVAR_158 : A -> Prop) (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term71 A GEN_PVAR_158 s P t) = (term35 A GEN_PVAR_158 s P t).
Proof. exact (MK_COMB (@lem4604460 A GEN_PVAR_158 s P t) (@lem4604461 A t)). Qed.
Lemma lem4604463 {A : Type'} (GEN_PVAR_158 : A -> Prop) (s : A -> Prop) (P : type686 A) : (term72 A GEN_PVAR_158 s P) = (term37 A GEN_PVAR_158 s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4604462 A GEN_PVAR_158 s P t)). Qed.
Lemma lem4604464 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4604465 {A : Type'} (GEN_PVAR_158 : A -> Prop) (s : A -> Prop) (P : type686 A) : (term73 A GEN_PVAR_158 s P) = (term39 A GEN_PVAR_158 s P).
Proof. exact (MK_COMB (@lem4604464 A) (@lem4604463 A GEN_PVAR_158 s P)). Qed.
Lemma lem4604466 {A : Type'} (s : A -> Prop) (P : type686 A) : (term74 A s P) = (term41 A s P).
Proof. exact (fun_ext (fun GEN_PVAR_158 : A -> Prop => @lem4604465 A GEN_PVAR_158 s P)). Qed.
Lemma lem4604467 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4604468 {A : Type'} (s : A -> Prop) (P : type686 A) : (term75 A s P) = (term42 A s P).
Proof. exact (MK_COMB (@lem4604467 A) (@lem4604466 A s P)). Qed.
Lemma lem4604469 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4604470 {A : Type'} (x : A -> Prop) (s : A -> Prop) (P : type686 A) : (term67 A x s P) = (term44 A x s P).
Proof. exact (MK_COMB (@lem4604469 A x) (@lem4604468 A s P)). Qed.
Lemma lem4604471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4604472 {A : Type'} (x : A -> Prop) (s : A -> Prop) (P : type686 A) : (term76 A x s P) = (term77 A x s P).
Proof. exact (MK_COMB (@lem4604471) (@lem4604470 A x s P)). Qed.
Lemma lem4604473 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : (term68 A s P x) = (term31 A s P x).
Proof. exact (eq_refl (term68 A s P x)). Qed.
Lemma lem4604474 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : ((term67 A x s P) = (term68 A s P x)) = ((term44 A x s P) = (term31 A s P x)).
Proof. exact (MK_COMB (@lem4604472 A x s P) (@lem4604473 A s P x)). Qed.
Lemma lem4604475 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : (term44 A x s P) = (term31 A s P x).
Proof. exact (EQ_MP (@lem4604474 A s P x) (@lem4604457 A s P x)). Qed.
Lemma lem4604485 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4604486 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4604485 A P x). Qed.
Lemma lem4604487 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem4604486 A x x'). Qed.
Lemma lem4604488 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4604489 {A : Type'} (x : A -> Prop) (x' : A) : (term78 A x' x) = (term79 A x x').
Proof. exact (MK_COMB (@lem4604488) (@lem4604487 A x x')). Qed.
Lemma lem4604491 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4604492 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4604491 A P x). Qed.
Lemma lem4604493 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4604492 A s x). Qed.
Lemma lem4604494 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term80 A x x' s) = (term81 A x s x').
Proof. exact (MK_COMB (@lem4604489 A x x') (@lem4604493 A s x')). Qed.
Lemma lem4604497 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term82 A x s) = (term83 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4604494 A x s x')). Qed.
Lemma lem4604498 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4604499 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term24 A x s) = (term84 A x s).
Proof. exact (MK_COMB (@lem4604498 A) (@lem4604497 A x s)). Qed.
Lemma lem4604504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4604505 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term29 A x s) = (term85 A x s).
Proof. exact (MK_COMB (@lem4604504) (@lem4604499 A x s)). Qed.
Lemma lem4604506 {A : Type'} (P : type686 A) (x : A -> Prop) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem4604507 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : (term31 A s P x) = (term86 A s P x).
Proof. exact (MK_COMB (@lem4604505 A x s) (@lem4604506 A P x)). Qed.
Lemma lem4604510 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : (term44 A x s P) = (term86 A s P x).
Proof. exact (TRANS (@lem4604475 A s P x) (@lem4604507 A s P x)). Qed.
Lemma lem4604511 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4604512 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : (term46 A x s P) = (term87 A s P x).
Proof. exact (MK_COMB (@lem4604511) (@lem4604510 A s P x)). Qed.
Lemma lem4604514 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term65 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4604515 {A : Type'} (p : type686 A) (x : A -> Prop) : (term66 A x p) = (p x).
Proof. exact (@lem4604514 (A -> Prop) p x). Qed.
Lemma lem4604516 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term88 A x s) = (term89 A s x).
Proof. exact (@lem4604515 A (term90 A s) x). Qed.
Lemma lem4604517 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term89 A s t) = (term24 A t s).
Proof. exact (eq_refl (term89 A s t)). Qed.
Lemma lem4604518 {A : Type'} (GEN_PVAR_157 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_157) = (@SETSPEC (A -> Prop) GEN_PVAR_157).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_157)). Qed.
Lemma lem4604519 {A : Type'} (GEN_PVAR_157 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term91 A GEN_PVAR_157 s t) = (term48 A GEN_PVAR_157 t s).
Proof. exact (MK_COMB (@lem4604518 A GEN_PVAR_157) (@lem4604517 A t s)). Qed.
Lemma lem4604520 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4604521 {A : Type'} (GEN_PVAR_157 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term92 A GEN_PVAR_157 s t) = (term50 A GEN_PVAR_157 s t).
Proof. exact (MK_COMB (@lem4604519 A GEN_PVAR_157 t s) (@lem4604520 A t)). Qed.
Lemma lem4604522 {A : Type'} (GEN_PVAR_157 : A -> Prop) (s : A -> Prop) : (term93 A GEN_PVAR_157 s) = (term52 A GEN_PVAR_157 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4604521 A GEN_PVAR_157 s t)). Qed.
Lemma lem4604523 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4604524 {A : Type'} (GEN_PVAR_157 : A -> Prop) (s : A -> Prop) : (term94 A GEN_PVAR_157 s) = (term54 A GEN_PVAR_157 s).
Proof. exact (MK_COMB (@lem4604523 A) (@lem4604522 A GEN_PVAR_157 s)). Qed.
Lemma lem4604525 {A : Type'} (s : A -> Prop) : (term95 A s) = (term56 A s).
Proof. exact (fun_ext (fun GEN_PVAR_157 : A -> Prop => @lem4604524 A GEN_PVAR_157 s)). Qed.
Lemma lem4604526 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4604527 {A : Type'} (s : A -> Prop) : (term96 A s) = (term57 A s).
Proof. exact (MK_COMB (@lem4604526 A) (@lem4604525 A s)). Qed.
Lemma lem4604528 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4604529 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term88 A x s) = (term59 A x s).
Proof. exact (MK_COMB (@lem4604528 A x) (@lem4604527 A s)). Qed.
Lemma lem4604530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4604531 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term97 A x s) = (term98 A x s).
Proof. exact (MK_COMB (@lem4604530) (@lem4604529 A x s)). Qed.
Lemma lem4604532 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term89 A s x) = (term24 A x s).
Proof. exact (eq_refl (term89 A s x)). Qed.
Lemma lem4604533 {A : Type'} (x : A -> Prop) (s : A -> Prop) : ((term88 A x s) = (term89 A s x)) = ((term59 A x s) = (term24 A x s)).
Proof. exact (MK_COMB (@lem4604531 A x s) (@lem4604532 A x s)). Qed.
Lemma lem4604534 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term59 A x s) = (term24 A x s).
Proof. exact (EQ_MP (@lem4604533 A x s) (@lem4604516 A s x)). Qed.
Lemma lem4604542 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4604543 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4604542 A P x). Qed.
Lemma lem4604544 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem4604543 A x x'). Qed.
Lemma lem4604545 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4604546 {A : Type'} (x : A -> Prop) (x' : A) : (term78 A x' x) = (term79 A x x').
Proof. exact (MK_COMB (@lem4604545) (@lem4604544 A x x')). Qed.
Lemma lem4604548 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4604549 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4604548 A P x). Qed.
Lemma lem4604550 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4604549 A s x). Qed.
Lemma lem4604551 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term80 A x x' s) = (term81 A x s x').
Proof. exact (MK_COMB (@lem4604546 A x x') (@lem4604550 A s x')). Qed.
Lemma lem4604554 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term82 A x s) = (term83 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4604551 A x s x')). Qed.
Lemma lem4604555 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4604556 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term24 A x s) = (term84 A x s).
Proof. exact (MK_COMB (@lem4604555 A) (@lem4604554 A x s)). Qed.
Lemma lem4604561 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term59 A x s) = (term84 A x s).
Proof. exact (TRANS (@lem4604534 A x s) (@lem4604556 A x s)). Qed.
Lemma lem4604562 {A : Type'} (P : type686 A) (x : A -> Prop) (s : A -> Prop) : (term61 A P x s) = (term99 A P x s).
Proof. exact (MK_COMB (@lem4604512 A s P x) (@lem4604561 A x s)). Qed.
Lemma lem4604565 {A : Type'} (P : type686 A) (s : A -> Prop) : (term63 A P s) = (term100 A P s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4604562 A P x s)). Qed.
Lemma lem4604566 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4604567 {A : Type'} (P : type686 A) (s : A -> Prop) : (term64 A P s) = (term101 A P s).
Proof. exact (MK_COMB (@lem4604566 A) (@lem4604565 A P s)). Qed.
Lemma lem4604572 {A : Type'} (P : type686 A) (s : A -> Prop) : (term101 A P s) = (term64 A P s).
Proof. exact (SYM (@lem4604567 A P s)). Qed.
Lemma lem4604574 (p : Prop) : p = (term102 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4604575 {A : Type'} (P : type686 A) (s : A -> Prop) : (term101 A P s) = (term103 A P s).
Proof. exact (@lem4604574 (term101 A P s)). Qed.
Lemma lem4604576 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term101 A P s).
Proof. exact (SYM (@lem4604575 A P s)). Qed.
Lemma lem4604577 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term104 A P s) : term104 A P s.
Proof. exact (h1). Qed.
Lemma lem4604580 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term103 A P s) : term103 A P s.
Proof. exact (h1). Qed.
Lemma lem4604581 {A : Type'} (P : type686 A) (s : A -> Prop) : term105 A P s.
Proof. exact (fun h0 : term103 A P s => @lem4604580 A P s h0). Qed.
Lemma lem4604582 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term105 A P s) : term105 A P s.
Proof. exact (h1). Qed.
Lemma lem4604583 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term103 A P s) : term103 A P s.
Proof. exact (h1). Qed.
Lemma lem4604584 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term103 A P s) (h2 : term105 A P s) : term103 A P s.
Proof. exact (@lem4604582 A P s h2 (@lem4604583 A P s h1)). Qed.
Lemma lem4604585 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term103 A P s) : term106 A P s.
Proof. exact (fun h0 : term105 A P s => @lem4604584 A P s h1 h0). Qed.
Lemma lem4604586 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term105 A P s) : term105 A P s.
Proof. exact (h1). Qed.
Lemma lem4604587 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term103 A P s) (h2 : term105 A P s) : term103 A P s.
Proof. exact (@lem4604585 A P s h1 (@lem4604586 A P s h2)). Qed.
Lemma lem4604588 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term105 A P s) : term105 A P s.
Proof. exact (fun h0 : term103 A P s => @lem4604587 A P s h0 h1). Qed.
Lemma lem4604589 {A : Type'} (P : type686 A) (s : A -> Prop) : term107 A P s.
Proof. exact (fun h0 : term105 A P s => @lem4604588 A P s h0). Qed.
Lemma lem4604592 {A : Type'} (P : type686 A) (s : A -> Prop) : term105 A P s.
Proof. exact (@lem4604589 A P s (@lem4604581 A P s)). Qed.
Lemma lem4604593 {A : Type'} (P : type686 A) (s : A -> Prop) : term105 A P s.
Proof. exact (@lem4604592 A P s). Qed.
Lemma lem4604603 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4604604 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term108 A P s).
Proof. exact (@lem4604603 (term104 A P s)). Qed.
Lemma lem4604606 (t : Prop) : (term109 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4604607 {A : Type'} (P : type686 A) (s : A -> Prop) : (term108 A P s) = (term101 A P s).
Proof. exact (@lem4604606 (term101 A P s)). Qed.
Lemma lem4604612 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term101 A P s).
Proof. exact (TRANS (@lem4604604 A P s) (@lem4604607 A P s)). Qed.
Lemma lem4604629 {A : Type'} (s : A -> Prop) : (term110 A s) = (term111 A s).
Proof. exact (fun_ext (fun P : type686 A => @lem4604612 A P s)). Qed.
Lemma lem4604630 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4604631 {A : Type'} (s : A -> Prop) : (term112 A s) = (term113 A s).
Proof. exact (MK_COMB (@lem4604630 A) (@lem4604629 A s)). Qed.
Lemma lem4604636 {A : Type'} : (term114 A) = (term115 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4604631 A s)). Qed.
Lemma lem4604637 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4604646 {A : Type'} : (term116 A) = (term117 A).
Proof. exact (MK_COMB (@lem4604637 A) (@lem4604636 A)). Qed.
Lemma lem4604651 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term81 A x s x') = (term81 A x s x').
Proof. exact (eq_refl (term81 A x s x')). Qed.
Lemma lem4604652 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term83 A x s) = (term83 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4604651 A x s x')). Qed.
Lemma lem4604653 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4604654 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term84 A x s) = (term84 A x s).
Proof. exact (MK_COMB (@lem4604653 A) (@lem4604652 A x s)). Qed.
Lemma lem4604655 {A : Type'} (P : type686 A) (x : A -> Prop) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem4604660 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term81 A x s x') = (term81 A x s x').
Proof. exact (eq_refl (term81 A x s x')). Qed.
Lemma lem4604661 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term83 A x s) = (term83 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4604660 A x s x')). Qed.
Lemma lem4604662 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4604663 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term84 A x s) = (term84 A x s).
Proof. exact (MK_COMB (@lem4604662 A) (@lem4604661 A x s)). Qed.
Lemma lem4604664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4604665 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term85 A x s) = (term85 A x s).
Proof. exact (MK_COMB (@lem4604664) (@lem4604663 A x s)). Qed.
Lemma lem4604666 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : (term86 A s P x) = (term86 A s P x).
Proof. exact (MK_COMB (@lem4604665 A x s) (@lem4604655 A P x)). Qed.
Lemma lem4604667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4604668 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : (term87 A s P x) = (term87 A s P x).
Proof. exact (MK_COMB (@lem4604667) (@lem4604666 A s P x)). Qed.
Lemma lem4604669 {A : Type'} (P : type686 A) (x : A -> Prop) (s : A -> Prop) : (term99 A P x s) = (term99 A P x s).
Proof. exact (MK_COMB (@lem4604668 A s P x) (@lem4604654 A x s)). Qed.
Lemma lem4604670 {A : Type'} (P : type686 A) (s : A -> Prop) : (term100 A P s) = (term100 A P s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4604669 A P x s)). Qed.
Lemma lem4604671 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4604672 {A : Type'} (P : type686 A) (s : A -> Prop) : (term101 A P s) = (term101 A P s).
Proof. exact (MK_COMB (@lem4604671 A) (@lem4604670 A P s)). Qed.
Lemma lem4604673 {A : Type'} (s : A -> Prop) : (term111 A s) = (term111 A s).
Proof. exact (fun_ext (fun P : type686 A => @lem4604672 A P s)). Qed.
Lemma lem4604674 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4604675 {A : Type'} (s : A -> Prop) : (term113 A s) = (term113 A s).
Proof. exact (MK_COMB (@lem4604674 A) (@lem4604673 A s)). Qed.
Lemma lem4604676 {A : Type'} : (term115 A) = (term115 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4604675 A s)). Qed.
Lemma lem4604677 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4604678 {A : Type'} : (term117 A) = (term117 A).
Proof. exact (MK_COMB (@lem4604677 A) (@lem4604676 A)). Qed.
Lemma lem4604719 {A : Type'} : (term116 A) = (term117 A).
Proof. exact (TRANS (@lem4604646 A) (@lem4604678 A)). Qed.
Lemma lem4604720 {A : Type'} : (term117 A) = (term116 A).
Proof. exact (SYM (@lem4604719 A)). Qed.
Lemma lem4604721 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term86 A s P x.
Proof. exact (h1). Qed.
Lemma lem4604724 (p : Prop) : p = (term102 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4604725 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (term118 A s x').
Proof. exact (@lem4604724 (s x')). Qed.
Lemma lem4604726 {A : Type'} (s : A -> Prop) (x' : A) : (term118 A s x') = (s x').
Proof. exact (SYM (@lem4604725 A s x')). Qed.
Lemma lem4604727 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term119 A s x') : term119 A s x'.
Proof. exact (h1). Qed.
Lemma lem4604734 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term81 A x s x') = (term120 A x s x').
Proof. exact (@lem17265 (x x') (s x')). Qed.
Lemma lem4604735 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term83 A x s) = (term121 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4604734 A x s x')). Qed.
Lemma lem4604736 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4604737 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term84 A x s) = (term122 A x s).
Proof. exact (MK_COMB (@lem4604736 A) (@lem4604735 A x s)). Qed.
Lemma lem4604738 {A : Type'} (P : type686 A) (x : A -> Prop) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem4604739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4604740 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term85 A x s) = (term123 A x s).
Proof. exact (MK_COMB (@lem4604739) (@lem4604737 A x s)). Qed.
Lemma lem4604777 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : (term86 A s P x) = (term124 A s P x).
Proof. exact (MK_COMB (@lem4604740 A x s) (@lem4604738 A P x)). Qed.
Lemma lem4604778 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term124 A s P x.
Proof. exact (EQ_MP (@lem4604777 A s P x) (@lem4604721 A s P x h1)). Qed.
Lemma lem4604784 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : x x'.
Proof. exact (h1). Qed.
Lemma lem4604790 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term119 A s x') : term119 A s x'.
Proof. exact (h1). Qed.
Lemma lem4604793 {A : Type'} (P : type686 A) (x : A -> Prop) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem4604796 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4604797 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4604802 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4604803 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4604802 A Prop f x). Qed.
Lemma lem4604805 {A : Type'} (x : A -> Prop) (x' : A) : (x x') = (@I (A -> Prop) x x').
Proof. exact (@lem4604803 A x x'). Qed.
Lemma lem4604806 {A : Type'} (x : A -> Prop) (x' : A) : (term119 A x x') = (term125 A x x').
Proof. exact (MK_COMB (@lem4604797) (@lem4604805 A x x')). Qed.
Lemma lem4604807 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4604808 {A : Type'} (x : A -> Prop) (x' : A) : (term126 A x x') = (term127 A x x').
Proof. exact (MK_COMB (@lem4604807) (@lem4604806 A x x')). Qed.
Lemma lem4604809 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term120 A x s x') = (term128 A x s x').
Proof. exact (MK_COMB (@lem4604808 A x x') (@lem4604796 A s x')). Qed.
Lemma lem4604810 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term121 A x s) = (term129 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4604809 A x s x')). Qed.
Lemma lem4604811 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4604812 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term122 A x s) = (term130 A x s).
Proof. exact (MK_COMB (@lem4604811 A) (@lem4604810 A x s)). Qed.
Lemma lem4604813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4604814 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term123 A x s) = (term131 A x s).
Proof. exact (MK_COMB (@lem4604813) (@lem4604812 A x s)). Qed.
Lemma lem4604815 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) : (term124 A s P x) = (term132 A s P x).
Proof. exact (MK_COMB (@lem4604814 A x s) (@lem4604793 A P x)). Qed.
Lemma lem4604816 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term132 A s P x.
Proof. exact (EQ_MP (@lem4604815 A s P x) (@lem4604778 A s P x h1)). Qed.
Lemma lem4604821 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4604822 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4604821 A Prop f x). Qed.
Lemma lem4604824 {A : Type'} (x : A -> Prop) (x' : A) : (x x') = (@I (A -> Prop) x x').
Proof. exact (@lem4604822 A x x'). Qed.
Lemma lem4604831 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term119 A s x') : term119 A s x'.
Proof. exact (h1). Qed.
Lemma lem4604833 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term130 A x s.
Proof. exact (proj1 (@lem4604816 A s P x h1)). Qed.
Lemma lem4604841 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term119 A s x') : term119 A s x'.
Proof. exact (h1). Qed.
Lemma lem4604849 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term128 A x s x') = (term128 A x s x').
Proof. exact (eq_refl (term128 A x s x')). Qed.
Lemma lem4604850 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term129 A x s) = (term129 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4604849 A x s x')). Qed.
Lemma lem4604851 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4604853 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term130 A x s) = (term130 A x s).
Proof. exact (MK_COMB (@lem4604851 A) (@lem4604850 A x s)). Qed.
Lemma lem4604854 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term130 A x s.
Proof. exact (EQ_MP (@lem4604853 A x s) (@lem4604833 A s P x h1)). Qed.
Lemma lem4604859 {A : Type'} (_55359 : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term133 A x s _55359.
Proof. exact (@lem4604854 A s P x h1 _55359). Qed.
Lemma lem4604860 {A : Type'} (x : A -> Prop) (s : A -> Prop) (_55359 : A) : (term133 A x s _55359) = (term128 A x s _55359).
Proof. exact (eq_refl (term133 A x s _55359)). Qed.
Lemma lem4604865 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term119 A s x') : term119 A s x'.
Proof. exact (h1). Qed.
Lemma lem4604871 {A : Type'} (_55359 : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term128 A x s _55359.
Proof. exact (EQ_MP (@lem4604860 A x s _55359) (@lem4604859 A _55359 s P x h1)). Qed.
Lemma lem4604875 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : @I (A -> Prop) x x'.
Proof. exact (EQ_MP (@lem4604824 A x x') (@lem4604784 A x x' h1)). Qed.
Lemma lem4604876 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : term134 A x x'.
Proof. exact (fun h0 : term125 A x x' => @lem4604875 A x x' h1). Qed.
Lemma lem4604878 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4604879 {A : Type'} (x : A -> Prop) (x' : A) : (term134 A x x') = (@I (A -> Prop) x x').
Proof. exact (@lem4604878 (@I (A -> Prop) x x')). Qed.
Lemma lem4604880 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : @I (A -> Prop) x x'.
Proof. exact (EQ_MP (@lem4604879 A x x') (@lem4604876 A x x' h1)). Qed.
Lemma lem4604886 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4604887 {A : Type'} (s : A -> Prop) (x : A -> Prop) (_55359 : A) : (term128 A x s _55359) = (term136 A s x _55359).
Proof. exact (@lem4604886 (s _55359) (term125 A x _55359)). Qed.
Lemma lem4604893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4604894 {A : Type'} (s : A -> Prop) (x : A -> Prop) (_55359 : A) : (term137 A x s _55359) = (term138 A s x _55359).
Proof. exact (MK_COMB (@lem4604893) (@lem4604887 A s x _55359)). Qed.
Lemma lem4604900 {A : Type'} (s : A -> Prop) (x : A -> Prop) (_55359 : A) : (term136 A s x _55359) = (term136 A s x _55359).
Proof. exact (eq_refl (term136 A s x _55359)). Qed.
Lemma lem4604901 {A : Type'} (s : A -> Prop) (x : A -> Prop) (_55359 : A) : ((term128 A x s _55359) = (term136 A s x _55359)) = ((term136 A s x _55359) = (term136 A s x _55359)).
Proof. exact (MK_COMB (@lem4604894 A s x _55359) (@lem4604900 A s x _55359)). Qed.
Lemma lem4604903 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4604904 (x : Prop) : (x = x) = True.
Proof. exact (@lem4604903 Prop x). Qed.
Lemma lem4604905 {A : Type'} (s : A -> Prop) (x : A -> Prop) (_55359 : A) : ((term136 A s x _55359) = (term136 A s x _55359)) = True.
Proof. exact (@lem4604904 (term136 A s x _55359)). Qed.
Lemma lem4604906 {A : Type'} (s : A -> Prop) (x : A -> Prop) (_55359 : A) : ((term128 A x s _55359) = (term136 A s x _55359)) = True.
Proof. exact (TRANS (@lem4604901 A s x _55359) (@lem4604905 A s x _55359)). Qed.
Lemma lem4604907 {A : Type'} (s : A -> Prop) (x : A -> Prop) (_55359 : A) : True = ((term128 A x s _55359) = (term136 A s x _55359)).
Proof. exact (SYM (@lem4604906 A s x _55359)). Qed.
Lemma lem4604908 {A : Type'} (s : A -> Prop) (x : A -> Prop) (_55359 : A) : (term128 A x s _55359) = (term136 A s x _55359).
Proof. exact (EQ_MP (@lem4604907 A s x _55359) (@lem0)). Qed.
Lemma lem4604909 {A : Type'} (_55359 : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term136 A s x _55359.
Proof. exact (EQ_MP (@lem4604908 A s x _55359) (@lem4604871 A _55359 s P x h1)). Qed.
Lemma lem4604911 (b : Prop) (a : Prop) : (a \/ b) = (term139 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4604912 {A : Type'} (x : A -> Prop) (s : A -> Prop) (_55359 : A) : (term136 A s x _55359) = (term140 A x s _55359).
Proof. exact (@lem4604911 (term125 A x _55359) (s _55359)). Qed.
Lemma lem4604914 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4604915 {A : Type'} (x : A -> Prop) (_55359 : A) : (term141 A x _55359) = (@I (A -> Prop) x _55359).
Proof. exact (@lem4604914 (@I (A -> Prop) x _55359)). Qed.
Lemma lem4604916 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4604917 {A : Type'} (x : A -> Prop) (_55359 : A) : (term142 A x _55359) = (term143 A x _55359).
Proof. exact (MK_COMB (@lem4604916) (@lem4604915 A x _55359)). Qed.
Lemma lem4604918 {A : Type'} (s : A -> Prop) (_55359 : A) : (s _55359) = (s _55359).
Proof. exact (eq_refl (s _55359)). Qed.
Lemma lem4604919 {A : Type'} (x : A -> Prop) (s : A -> Prop) (_55359 : A) : (term140 A x s _55359) = (term144 A x s _55359).
Proof. exact (MK_COMB (@lem4604917 A x _55359) (@lem4604918 A s _55359)). Qed.
Lemma lem4604920 {A : Type'} (x : A -> Prop) (s : A -> Prop) (_55359 : A) : (term136 A s x _55359) = (term144 A x s _55359).
Proof. exact (TRANS (@lem4604912 A x s _55359) (@lem4604919 A x s _55359)). Qed.
Lemma lem4604923 {A : Type'} (_55359 : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term144 A x s _55359.
Proof. exact (EQ_MP (@lem4604920 A x s _55359) (@lem4604909 A _55359 s P x h1)). Qed.
Lemma lem4604924 {A : Type'} (_55359 : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term144 A x s _55359.
Proof. exact (@lem4604923 A _55359 s P x h1). Qed.
Lemma lem4604925 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term144 A x s x'.
Proof. exact (@lem4604924 A x' s P x h1). Qed.
Lemma lem4604928 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : x x') (h2 : term86 A s P x) : s x'.
Proof. exact (@lem4604925 A x' s P x h2 (@lem4604880 A x x' h1)). Qed.
Lemma lem4604929 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : x x') (h2 : term86 A s P x) : term145 A s x'.
Proof. exact (fun h0 : term119 A s x' => @lem4604928 A x' s P x h1 h2). Qed.
Lemma lem4604931 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4604932 {A : Type'} (s : A -> Prop) (x' : A) : (term145 A s x') = (s x').
Proof. exact (@lem4604931 (s x')). Qed.
Lemma lem4604933 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : x x') (h2 : term86 A s P x) : s x'.
Proof. exact (EQ_MP (@lem4604932 A s x') (@lem4604929 A x' s P x h1 h2)). Qed.
Lemma lem4604936 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4604938 {A : Type'} (s : A -> Prop) (x' : A) : (term119 A s x') = (term146 A s x').
Proof. exact (@lem4604936 (s x')). Qed.
Lemma lem4604941 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term119 A s x') : term146 A s x'.
Proof. exact (EQ_MP (@lem4604938 A s x') (@lem4604865 A s x' h1)). Qed.
Lemma lem4604944 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : False.
Proof. exact (@lem4604941 A s x' h1 (@lem4604933 A x' s P x h2 h3)). Qed.
Lemma lem4604945 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : term147.
Proof. exact (fun h0 : ~ False => @lem4604944 A x' s P x h1 h2 h3). Qed.
Lemma lem4604947 (p : Prop) : (term135 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4604948 : term147 = False.
Proof. exact (@lem4604947 False). Qed.
Lemma lem4604949 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : False.
Proof. exact (EQ_MP (@lem4604948) (@lem4604945 A x' s P x h1 h2 h3)). Qed.
Lemma lem4604950 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : (term119 A s x') = False.
Proof. exact (prop_ext (fun h4 : term119 A s x' => @lem4604949 A x' s P x h1 h2 h3) (fun h4 : False => @lem4604865 A s x' h1)). Qed.
Lemma lem4604951 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : False.
Proof. exact (EQ_MP (@lem4604950 A x' s P x h1 h2 h3) (@lem4604865 A s x' h1)). Qed.
Lemma lem4604952 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : (term119 A s x') = False.
Proof. exact (prop_ext (fun h4 : term119 A s x' => @lem4604951 A x' s P x h1 h2 h3) (fun h4 : False => @lem4604841 A s x' h1)). Qed.
Lemma lem4604953 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : False.
Proof. exact (EQ_MP (@lem4604952 A x' s P x h1 h2 h3) (@lem4604841 A s x' h1)). Qed.
Lemma lem4604954 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : (term119 A s x') = False.
Proof. exact (prop_ext (fun h4 : term119 A s x' => @lem4604953 A x' s P x h1 h2 h3) (fun h4 : False => @lem4604841 A s x' h1)). Qed.
Lemma lem4604955 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : False.
Proof. exact (EQ_MP (@lem4604954 A x' s P x h1 h2 h3) (@lem4604841 A s x' h1)). Qed.
Lemma lem4604956 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : (term119 A s x') = False.
Proof. exact (prop_ext (fun h4 : term119 A s x' => @lem4604955 A x' s P x h1 h2 h3) (fun h4 : False => @lem4604831 A s x' h1)). Qed.
Lemma lem4604957 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : False.
Proof. exact (EQ_MP (@lem4604956 A x' s P x h1 h2 h3) (@lem4604831 A s x' h1)). Qed.
Lemma lem4604958 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : (term119 A s x') = False.
Proof. exact (prop_ext (fun h4 : term119 A s x' => @lem4604957 A x' s P x h1 h2 h3) (fun h4 : False => @lem4604790 A s x' h1)). Qed.
Lemma lem4604959 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : False.
Proof. exact (EQ_MP (@lem4604958 A x' s P x h1 h2 h3) (@lem4604790 A s x' h1)). Qed.
Lemma lem4604960 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : (x x') = False.
Proof. exact (prop_ext (fun h4 : x x' => @lem4604959 A x' s P x h1 h2 h3) (fun h4 : False => @lem4604784 A x x' h2)). Qed.
Lemma lem4604961 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : False.
Proof. exact (EQ_MP (@lem4604960 A x' s P x h1 h2 h3) (@lem4604784 A x x' h2)). Qed.
Lemma lem4604962 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : (term119 A s x') = False.
Proof. exact (prop_ext (fun h4 : term119 A s x' => @lem4604961 A x' s P x h1 h2 h3) (fun h4 : False => @lem4604727 A s x' h1)). Qed.
Lemma lem4604963 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term119 A s x') (h2 : x x') (h3 : term86 A s P x) : False.
Proof. exact (EQ_MP (@lem4604962 A x' s P x h1 h2 h3) (@lem4604727 A s x' h1)). Qed.
Lemma lem4604964 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : x x') (h2 : term86 A s P x) : term118 A s x'.
Proof. exact (fun h0 : term119 A s x' => @lem4604963 A x' s P x h0 h1 h2). Qed.
Lemma lem4604965 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : x x') (h2 : term86 A s P x) : s x'.
Proof. exact (EQ_MP (@lem4604726 A s x') (@lem4604964 A x' s P x h1 h2)). Qed.
Lemma lem4604966 {A : Type'} (x' : A) (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term81 A x s x'.
Proof. exact (fun h0 : x x' => @lem4604965 A x' s P x h0 h1). Qed.
Lemma lem4604971 {A : Type'} (s : A -> Prop) (P : type686 A) (x : A -> Prop) (h1 : term86 A s P x) : term84 A x s.
Proof. exact (fun x' : A => @lem4604966 A x' s P x h1). Qed.
Lemma lem4604972 {A : Type'} (P : type686 A) (x : A -> Prop) (s : A -> Prop) : term99 A P x s.
Proof. exact (fun h0 : term86 A s P x => @lem4604971 A s P x h0). Qed.
Lemma lem4604977 {A : Type'} (P : type686 A) (s : A -> Prop) : term101 A P s.
Proof. exact (fun x : A -> Prop => @lem4604972 A P x s). Qed.
Lemma lem4604982 {A : Type'} (s : A -> Prop) : term113 A s.
Proof. exact (fun P : type686 A => @lem4604977 A P s). Qed.
Lemma lem4604987 {A : Type'} : term117 A.
Proof. exact (fun s : A -> Prop => @lem4604982 A s). Qed.
Lemma lem4604988 {A : Type'} : term116 A.
Proof. exact (EQ_MP (@lem4604720 A) (@lem4604987 A)). Qed.
Lemma lem4604989 {A : Type'} (s : A -> Prop) : term148 A s.
Proof. exact (@lem4604988 A s). Qed.
Lemma lem4604990 {A : Type'} (s : A -> Prop) : (term148 A s) = (term112 A s).
Proof. exact (eq_refl (term148 A s)). Qed.
Lemma lem4604991 {A : Type'} (s : A -> Prop) : term112 A s.
Proof. exact (EQ_MP (@lem4604990 A s) (@lem4604989 A s)). Qed.
Lemma lem4604992 {A : Type'} (s : A -> Prop) (P : type686 A) : term149 A s P.
Proof. exact (@lem4604991 A s P). Qed.
Lemma lem4604993 {A : Type'} (P : type686 A) (s : A -> Prop) : (term149 A s P) = (term103 A P s).
Proof. exact (eq_refl (term149 A s P)). Qed.
Lemma lem4604994 {A : Type'} (P : type686 A) (s : A -> Prop) : term103 A P s.
Proof. exact (EQ_MP (@lem4604993 A P s) (@lem4604992 A s P)). Qed.
Lemma lem4604996 {A : Type'} (P : type686 A) (s : A -> Prop) : term103 A P s.
Proof. exact (@lem4604593 A P s (@lem4604994 A P s)). Qed.
Lemma lem4604997 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term104 A P s) : False.
Proof. exact (@lem4604996 A P s (@lem4604577 A P s h1)). Qed.
Lemma lem4604998 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term104 A P s) : (term104 A P s) = False.
Proof. exact (prop_ext (fun h2 : term104 A P s => @lem4604997 A P s h1) (fun h2 : False => @lem4604577 A P s h1)). Qed.
Lemma lem4604999 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term104 A P s) : False.
Proof. exact (EQ_MP (@lem4604998 A P s h1) (@lem4604577 A P s h1)). Qed.
Lemma lem4605000 {A : Type'} (P : type686 A) (s : A -> Prop) : term103 A P s.
Proof. exact (fun h0 : term104 A P s => @lem4604999 A P s h0). Qed.
Lemma lem4605001 {A : Type'} (P : type686 A) (s : A -> Prop) : term101 A P s.
Proof. exact (EQ_MP (@lem4604576 A P s) (@lem4605000 A P s)). Qed.
Lemma lem4605002 {A : Type'} (P : type686 A) (s : A -> Prop) : term64 A P s.
Proof. exact (EQ_MP (@lem4604572 A P s) (@lem4605001 A P s)). Qed.
Lemma lem4605003 {A : Type'} (P : type686 A) (s : A -> Prop) : term21 A P s.
Proof. exact (EQ_MP (@lem4604447 A P s) (@lem4605002 A P s)). Qed.
Lemma lem4605004 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : term22 A P s.
Proof. exact (EQ_MP (@lem4604355 A P s h1) (@lem4605003 A P s)). Qed.
Lemma lem4605005 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : term150 A s P.
Proof. exact (ex_intro (term151 A s P) (term27 A s) (@lem4605004 A P s h1)). Qed.
Lemma lem4605006 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : term152 A s P.
Proof. exact (@lem4604302 A s P (@lem4605005 A P s h1)). Qed.
Lemma lem4605007 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = (term152 A s P).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem4605006 A P s h1) (fun h2 : term152 A s P => @lem4604298 A s h1)). Qed.
Lemma lem4605008 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : term152 A s P.
Proof. exact (EQ_MP (@lem4605007 A P s h1) (@lem4604298 A s h1)). Qed.
Lemma lem4605009 {A : Type'} (s : A -> Prop) (P : type686 A) : term153 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem4605008 A P s h0). Qed.
Lemma lem4605014 {A : Type'} (P : type686 A) : term154 A P.
Proof. exact (fun s : A -> Prop => @lem4605009 A s P). Qed.
Lemma lem4605019 {A : Type'} : term155 A.
Proof. exact (fun P : type686 A => @lem4605014 A P). Qed.
