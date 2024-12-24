Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_EMPTY_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3258190 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3258191 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3258190 A s t). Qed.
Lemma lem3258192 {A : Type'} (s : A -> Prop) : ((@INTER A (@EMPTY A) s) = (@EMPTY A)) = (term1 A s).
Proof. exact (@lem3258191 A (@INTER A (@EMPTY A) s) (@EMPTY A)). Qed.
Lemma lem3258201 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3258192 A s)). Qed.
Lemma lem3258202 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3258203 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3258202 A) (@lem3258201 A)). Qed.
Lemma lem3258208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258209 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem3258208) (@lem3258203 A)). Qed.
Lemma lem3258217 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3258218 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3258217 A s t). Qed.
Lemma lem3258219 {A : Type'} (s : A -> Prop) : ((@INTER A s (@EMPTY A)) = (@EMPTY A)) = (term8 A s).
Proof. exact (@lem3258218 A (@INTER A s (@EMPTY A)) (@EMPTY A)). Qed.
Lemma lem3258228 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3258219 A s)). Qed.
Lemma lem3258229 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3258230 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem3258229 A) (@lem3258228 A)). Qed.
Lemma lem3258235 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem3258209 A) (@lem3258230 A)). Qed.
Lemma lem3258238 {A : Type'} : (term14 A) = (term13 A).
Proof. exact (SYM (@lem3258235 A)). Qed.
Lemma lem3258252 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3258253 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (@lem3258252 A s x t). Qed.
Lemma lem3258254 {A : Type'} (x : A) (s : A -> Prop) : (term17 A x s) = (term18 A x s).
Proof. exact (@lem3258253 A (@EMPTY A) x s). Qed.
Lemma lem3258258 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3258259 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3258258 A x). Qed.
Lemma lem3258260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258261 {A : Type'} (x : A) : (term19 A x) = (and False).
Proof. exact (MK_COMB (@lem3258260) (@lem3258259 A x)). Qed.
Lemma lem3258263 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258264 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3258263 A P x). Qed.
Lemma lem3258265 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3258264 A s x). Qed.
Lemma lem3258266 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (term20 A s x).
Proof. exact (MK_COMB (@lem3258261 A x) (@lem3258265 A s x)). Qed.
Lemma lem3258268 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3258269 {A : Type'} (s : A -> Prop) (x : A) : (term20 A s x) = False.
Proof. exact (@lem3258268 (s x)). Qed.
Lemma lem3258270 {A : Type'} (x : A) (s : A -> Prop) : (term18 A x s) = False.
Proof. exact (TRANS (@lem3258266 A s x) (@lem3258269 A s x)). Qed.
Lemma lem3258271 {A : Type'} (x : A) (s : A -> Prop) : (term17 A x s) = False.
Proof. exact (TRANS (@lem3258254 A x s) (@lem3258270 A x s)). Qed.
Lemma lem3258272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3258273 {A : Type'} (x : A) (s : A -> Prop) : (term21 A x s) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3258272) (@lem3258271 A x s)). Qed.
Lemma lem3258275 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3258276 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3258275 A x). Qed.
Lemma lem3258277 {A : Type'} (s : A -> Prop) (x : A) : ((term17 A x s) = (@IN A x (@EMPTY A))) = (False = False).
Proof. exact (MK_COMB (@lem3258273 A x s) (@lem3258276 A x)). Qed.
Lemma lem3258279 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3258280 : (False = False) = (~ False).
Proof. exact (@lem3258279 False). Qed.
Lemma lem3258282 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3258283 : (False = False) = True.
Proof. exact (TRANS (@lem3258280) (@lem3258282)). Qed.
Lemma lem3258284 {A : Type'} (s : A -> Prop) (x : A) : ((term17 A x s) = (@IN A x (@EMPTY A))) = True.
Proof. exact (TRANS (@lem3258277 A s x) (@lem3258283)). Qed.
Lemma lem3258285 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A).
Proof. exact (fun_ext (fun x : A => @lem3258284 A s x)). Qed.
Lemma lem3258286 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3258287 {A : Type'} (s : A -> Prop) : (term1 A s) = (term24 A).
Proof. exact (MK_COMB (@lem3258286 A) (@lem3258285 A s)). Qed.
Lemma lem3258289 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3258290 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (@lem3258289 A t). Qed.
Lemma lem3258291 {A : Type'} : (term24 A) = True.
Proof. exact (@lem3258290 A True). Qed.
Lemma lem3258292 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3258287 A s) (@lem3258291 A)). Qed.
Lemma lem3258293 {A : Type'} : (term3 A) = (term26 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3258292 A s)). Qed.
Lemma lem3258294 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3258295 {A : Type'} : (term5 A) = (term27 A).
Proof. exact (MK_COMB (@lem3258294 A) (@lem3258293 A)). Qed.
Lemma lem3258297 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3258298 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (@lem3258297 (A -> Prop) t). Qed.
Lemma lem3258299 {A : Type'} : (term27 A) = True.
Proof. exact (@lem3258298 A True). Qed.
Lemma lem3258300 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3258295 A) (@lem3258299 A)). Qed.
Lemma lem3258301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258302 {A : Type'} : (term7 A) = (and True).
Proof. exact (MK_COMB (@lem3258301) (@lem3258300 A)). Qed.
Lemma lem3258314 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3258315 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (@lem3258314 A s x t). Qed.
Lemma lem3258316 {A : Type'} (s : A -> Prop) (x : A) : (term29 A x s) = (term30 A s x).
Proof. exact (@lem3258315 A s x (@EMPTY A)). Qed.
Lemma lem3258320 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258321 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3258320 A P x). Qed.
Lemma lem3258322 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3258321 A s x). Qed.
Lemma lem3258323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258324 {A : Type'} (s : A -> Prop) (x : A) : (term31 A x s) = (term32 A s x).
Proof. exact (MK_COMB (@lem3258323) (@lem3258322 A s x)). Qed.
Lemma lem3258326 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3258327 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3258326 A x). Qed.
Lemma lem3258328 {A : Type'} (s : A -> Prop) (x : A) : (term30 A s x) = (term33 A s x).
Proof. exact (MK_COMB (@lem3258324 A s x) (@lem3258327 A x)). Qed.
Lemma lem3258330 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem3258331 {A : Type'} (s : A -> Prop) (x : A) : (term33 A s x) = False.
Proof. exact (@lem3258330 (s x)). Qed.
Lemma lem3258332 {A : Type'} (s : A -> Prop) (x : A) : (term30 A s x) = False.
Proof. exact (TRANS (@lem3258328 A s x) (@lem3258331 A s x)). Qed.
Lemma lem3258333 {A : Type'} (x : A) (s : A -> Prop) : (term29 A x s) = False.
Proof. exact (TRANS (@lem3258316 A s x) (@lem3258332 A s x)). Qed.
Lemma lem3258334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3258335 {A : Type'} (x : A) (s : A -> Prop) : (term34 A x s) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3258334) (@lem3258333 A x s)). Qed.
Lemma lem3258337 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3258338 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3258337 A x). Qed.
Lemma lem3258339 {A : Type'} (s : A -> Prop) (x : A) : ((term29 A x s) = (@IN A x (@EMPTY A))) = (False = False).
Proof. exact (MK_COMB (@lem3258335 A x s) (@lem3258338 A x)). Qed.
Lemma lem3258341 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3258342 : (False = False) = (~ False).
Proof. exact (@lem3258341 False). Qed.
Lemma lem3258344 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3258345 : (False = False) = True.
Proof. exact (TRANS (@lem3258342) (@lem3258344)). Qed.
Lemma lem3258346 {A : Type'} (s : A -> Prop) (x : A) : ((term29 A x s) = (@IN A x (@EMPTY A))) = True.
Proof. exact (TRANS (@lem3258339 A s x) (@lem3258345)). Qed.
Lemma lem3258347 {A : Type'} (s : A -> Prop) : (term35 A s) = (term23 A).
Proof. exact (fun_ext (fun x : A => @lem3258346 A s x)). Qed.
Lemma lem3258348 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3258349 {A : Type'} (s : A -> Prop) : (term8 A s) = (term24 A).
Proof. exact (MK_COMB (@lem3258348 A) (@lem3258347 A s)). Qed.
Lemma lem3258351 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3258352 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (@lem3258351 A t). Qed.
Lemma lem3258353 {A : Type'} : (term24 A) = True.
Proof. exact (@lem3258352 A True). Qed.
Lemma lem3258354 {A : Type'} (s : A -> Prop) : (term8 A s) = True.
Proof. exact (TRANS (@lem3258349 A s) (@lem3258353 A)). Qed.
Lemma lem3258355 {A : Type'} : (term10 A) = (term26 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3258354 A s)). Qed.
Lemma lem3258356 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3258357 {A : Type'} : (term12 A) = (term27 A).
Proof. exact (MK_COMB (@lem3258356 A) (@lem3258355 A)). Qed.
Lemma lem3258359 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3258360 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (@lem3258359 (A -> Prop) t). Qed.
Lemma lem3258361 {A : Type'} : (term27 A) = True.
Proof. exact (@lem3258360 A True). Qed.
Lemma lem3258362 {A : Type'} : (term12 A) = True.
Proof. exact (TRANS (@lem3258357 A) (@lem3258361 A)). Qed.
Lemma lem3258363 {A : Type'} : (term14 A) = (True /\ True).
Proof. exact (MK_COMB (@lem3258302 A) (@lem3258362 A)). Qed.
Lemma lem3258365 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3258366 : (True /\ True) = True.
Proof. exact (@lem3258365 True). Qed.
Lemma lem3258367 {A : Type'} : (term14 A) = True.
Proof. exact (TRANS (@lem3258363 A) (@lem3258366)). Qed.
Lemma lem3258368 {A : Type'} : True = (term14 A).
Proof. exact (SYM (@lem3258367 A)). Qed.
Lemma lem3258369 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3258368 A) (@lem0)). Qed.
Lemma lem3258370 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3258238 A) (@lem3258369 A)). Qed.
