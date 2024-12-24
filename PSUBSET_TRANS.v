Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PSUBSET_TRANS_term_abbrevs.
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
Lemma lem3221190 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3221191 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (@lem3221190 A s t). Qed.
Lemma lem3221195 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3221196 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (@lem3221195 A s t). Qed.
Lemma lem3221203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221204 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (MK_COMB (@lem3221203) (@lem3221196 A s t)). Qed.
Lemma lem3221208 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3221209 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (@lem3221208 A s t). Qed.
Lemma lem3221218 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221219 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = (term6 A s t).
Proof. exact (MK_COMB (@lem3221218) (@lem3221209 A s t)). Qed.
Lemma lem3221220 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term7 A s t).
Proof. exact (MK_COMB (@lem3221204 A s t) (@lem3221219 A s t)). Qed.
Lemma lem3221223 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term7 A s t).
Proof. exact (TRANS (@lem3221191 A s t) (@lem3221220 A s t)). Qed.
Lemma lem3221224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221225 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term8 A s t) = (term9 A s t).
Proof. exact (MK_COMB (@lem3221224) (@lem3221223 A s t)). Qed.
Lemma lem3221227 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3221228 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (@lem3221227 A s t). Qed.
Lemma lem3221229 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@PSUBSET A t u) = (term0 A t u).
Proof. exact (@lem3221228 A t u). Qed.
Lemma lem3221233 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3221234 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (@lem3221233 A s t). Qed.
Lemma lem3221235 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@SUBSET A t u) = (term1 A t u).
Proof. exact (@lem3221234 A t u). Qed.
Lemma lem3221242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221243 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term2 A t u) = (term3 A t u).
Proof. exact (MK_COMB (@lem3221242) (@lem3221235 A t u)). Qed.
Lemma lem3221247 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3221248 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (@lem3221247 A s t). Qed.
Lemma lem3221249 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (t = u) = (term4 A t u).
Proof. exact (@lem3221248 A t u). Qed.
Lemma lem3221258 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221259 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term5 A t u) = (term6 A t u).
Proof. exact (MK_COMB (@lem3221258) (@lem3221249 A t u)). Qed.
Lemma lem3221260 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term0 A t u) = (term7 A t u).
Proof. exact (MK_COMB (@lem3221243 A t u) (@lem3221259 A t u)). Qed.
Lemma lem3221263 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@PSUBSET A t u) = (term7 A t u).
Proof. exact (TRANS (@lem3221229 A t u) (@lem3221260 A t u)). Qed.
Lemma lem3221264 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term10 A s t u) = (term11 A s t u).
Proof. exact (MK_COMB (@lem3221225 A s t) (@lem3221263 A t u)). Qed.
Lemma lem3221267 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3221268 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term12 A s t u) = (term13 A s t u).
Proof. exact (MK_COMB (@lem3221267) (@lem3221264 A s t u)). Qed.
Lemma lem3221270 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3221271 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (@lem3221270 A s t). Qed.
Lemma lem3221272 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@PSUBSET A s u) = (term0 A s u).
Proof. exact (@lem3221271 A s u). Qed.
Lemma lem3221276 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3221277 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (@lem3221276 A s t). Qed.
Lemma lem3221278 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@SUBSET A s u) = (term1 A s u).
Proof. exact (@lem3221277 A s u). Qed.
Lemma lem3221285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221286 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term2 A s u) = (term3 A s u).
Proof. exact (MK_COMB (@lem3221285) (@lem3221278 A s u)). Qed.
Lemma lem3221290 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3221291 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (@lem3221290 A s t). Qed.
Lemma lem3221292 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (s = u) = (term4 A s u).
Proof. exact (@lem3221291 A s u). Qed.
Lemma lem3221301 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221302 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term5 A s u) = (term6 A s u).
Proof. exact (MK_COMB (@lem3221301) (@lem3221292 A s u)). Qed.
Lemma lem3221303 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term0 A s u) = (term7 A s u).
Proof. exact (MK_COMB (@lem3221286 A s u) (@lem3221302 A s u)). Qed.
Lemma lem3221306 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@PSUBSET A s u) = (term7 A s u).
Proof. exact (TRANS (@lem3221272 A s u) (@lem3221303 A s u)). Qed.
Lemma lem3221307 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term14 A t s u) = (term15 A t s u).
Proof. exact (MK_COMB (@lem3221268 A s t u) (@lem3221306 A s u)). Qed.
Lemma lem3221310 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term16 A t s) = (term17 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3221307 A t s u)). Qed.
Lemma lem3221311 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3221312 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term18 A t s) = (term19 A t s).
Proof. exact (MK_COMB (@lem3221311 A) (@lem3221310 A t s)). Qed.
Lemma lem3221317 {A : Type'} (s : A -> Prop) : (term20 A s) = (term21 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3221312 A t s)). Qed.
Lemma lem3221318 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3221319 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (MK_COMB (@lem3221318 A) (@lem3221317 A s)). Qed.
Lemma lem3221324 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3221319 A s)). Qed.
Lemma lem3221325 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3221326 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (MK_COMB (@lem3221325 A) (@lem3221324 A)). Qed.
Lemma lem3221331 {A : Type'} : (term27 A) = (term26 A).
Proof. exact (SYM (@lem3221326 A)). Qed.
Lemma lem3221357 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221358 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221357 A P x). Qed.
Lemma lem3221359 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3221358 A s x). Qed.
Lemma lem3221360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3221361 {A : Type'} (s : A -> Prop) (x : A) : (term28 A x s) = (term29 A s x).
Proof. exact (MK_COMB (@lem3221360) (@lem3221359 A s x)). Qed.
Lemma lem3221363 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221364 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221363 A P x). Qed.
Lemma lem3221365 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3221364 A t x). Qed.
Lemma lem3221366 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term30 A s x t) = (term31 A s t x).
Proof. exact (MK_COMB (@lem3221361 A s x) (@lem3221365 A t x)). Qed.
Lemma lem3221369 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term33 A s t).
Proof. exact (fun_ext (fun x : A => @lem3221366 A s t x)). Qed.
Lemma lem3221370 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221371 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term34 A s t).
Proof. exact (MK_COMB (@lem3221370 A) (@lem3221369 A s t)). Qed.
Lemma lem3221376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221377 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3221376) (@lem3221371 A s t)). Qed.
Lemma lem3221385 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221386 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221385 A P x). Qed.
Lemma lem3221387 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3221386 A s x). Qed.
Lemma lem3221388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3221389 {A : Type'} (s : A -> Prop) (x : A) : (term36 A x s) = (term37 A s x).
Proof. exact (MK_COMB (@lem3221388) (@lem3221387 A s x)). Qed.
Lemma lem3221391 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221392 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221391 A P x). Qed.
Lemma lem3221393 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3221392 A t x). Qed.
Lemma lem3221394 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x t)) = ((s x) = (t x)).
Proof. exact (MK_COMB (@lem3221389 A s x) (@lem3221393 A t x)). Qed.
Lemma lem3221397 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term38 A s t) = (term39 A s t).
Proof. exact (fun_ext (fun x : A => @lem3221394 A s t x)). Qed.
Lemma lem3221398 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221399 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term40 A s t).
Proof. exact (MK_COMB (@lem3221398 A) (@lem3221397 A s t)). Qed.
Lemma lem3221404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221405 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term6 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3221404) (@lem3221399 A s t)). Qed.
Lemma lem3221406 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term42 A s t).
Proof. exact (MK_COMB (@lem3221377 A s t) (@lem3221405 A s t)). Qed.
Lemma lem3221409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221410 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term43 A s t).
Proof. exact (MK_COMB (@lem3221409) (@lem3221406 A s t)). Qed.
Lemma lem3221420 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221421 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221420 A P x). Qed.
Lemma lem3221422 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3221421 A t x). Qed.
Lemma lem3221423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3221424 {A : Type'} (t : A -> Prop) (x : A) : (term28 A x t) = (term29 A t x).
Proof. exact (MK_COMB (@lem3221423) (@lem3221422 A t x)). Qed.
Lemma lem3221426 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221427 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221426 A P x). Qed.
Lemma lem3221428 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3221427 A u x). Qed.
Lemma lem3221429 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term30 A t x u) = (term31 A t u x).
Proof. exact (MK_COMB (@lem3221424 A t x) (@lem3221428 A u x)). Qed.
Lemma lem3221432 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term32 A t u) = (term33 A t u).
Proof. exact (fun_ext (fun x : A => @lem3221429 A t u x)). Qed.
Lemma lem3221433 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221434 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term1 A t u) = (term34 A t u).
Proof. exact (MK_COMB (@lem3221433 A) (@lem3221432 A t u)). Qed.
Lemma lem3221439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221440 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term3 A t u) = (term35 A t u).
Proof. exact (MK_COMB (@lem3221439) (@lem3221434 A t u)). Qed.
Lemma lem3221448 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221449 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221448 A P x). Qed.
Lemma lem3221450 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3221449 A t x). Qed.
Lemma lem3221451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3221452 {A : Type'} (t : A -> Prop) (x : A) : (term36 A x t) = (term37 A t x).
Proof. exact (MK_COMB (@lem3221451) (@lem3221450 A t x)). Qed.
Lemma lem3221454 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221455 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221454 A P x). Qed.
Lemma lem3221456 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3221455 A u x). Qed.
Lemma lem3221457 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : ((@IN A x t) = (@IN A x u)) = ((t x) = (u x)).
Proof. exact (MK_COMB (@lem3221452 A t x) (@lem3221456 A u x)). Qed.
Lemma lem3221460 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term38 A t u) = (term39 A t u).
Proof. exact (fun_ext (fun x : A => @lem3221457 A t u x)). Qed.
Lemma lem3221461 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221462 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term4 A t u) = (term40 A t u).
Proof. exact (MK_COMB (@lem3221461 A) (@lem3221460 A t u)). Qed.
Lemma lem3221467 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221468 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term6 A t u) = (term41 A t u).
Proof. exact (MK_COMB (@lem3221467) (@lem3221462 A t u)). Qed.
Lemma lem3221469 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term7 A t u) = (term42 A t u).
Proof. exact (MK_COMB (@lem3221440 A t u) (@lem3221468 A t u)). Qed.
Lemma lem3221472 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term11 A s t u) = (term44 A s t u).
Proof. exact (MK_COMB (@lem3221410 A s t) (@lem3221469 A t u)). Qed.
Lemma lem3221475 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3221476 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term13 A s t u) = (term45 A s t u).
Proof. exact (MK_COMB (@lem3221475) (@lem3221472 A s t u)). Qed.
Lemma lem3221486 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221487 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221486 A P x). Qed.
Lemma lem3221488 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3221487 A s x). Qed.
Lemma lem3221489 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3221490 {A : Type'} (s : A -> Prop) (x : A) : (term28 A x s) = (term29 A s x).
Proof. exact (MK_COMB (@lem3221489) (@lem3221488 A s x)). Qed.
Lemma lem3221492 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221493 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221492 A P x). Qed.
Lemma lem3221494 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3221493 A u x). Qed.
Lemma lem3221495 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term30 A s x u) = (term31 A s u x).
Proof. exact (MK_COMB (@lem3221490 A s x) (@lem3221494 A u x)). Qed.
Lemma lem3221498 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term32 A s u) = (term33 A s u).
Proof. exact (fun_ext (fun x : A => @lem3221495 A s u x)). Qed.
Lemma lem3221499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221500 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term1 A s u) = (term34 A s u).
Proof. exact (MK_COMB (@lem3221499 A) (@lem3221498 A s u)). Qed.
Lemma lem3221505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221506 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term3 A s u) = (term35 A s u).
Proof. exact (MK_COMB (@lem3221505) (@lem3221500 A s u)). Qed.
Lemma lem3221514 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221515 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221514 A P x). Qed.
Lemma lem3221516 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3221515 A s x). Qed.
Lemma lem3221517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3221518 {A : Type'} (s : A -> Prop) (x : A) : (term36 A x s) = (term37 A s x).
Proof. exact (MK_COMB (@lem3221517) (@lem3221516 A s x)). Qed.
Lemma lem3221520 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3221521 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3221520 A P x). Qed.
Lemma lem3221522 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3221521 A u x). Qed.
Lemma lem3221523 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x u)) = ((s x) = (u x)).
Proof. exact (MK_COMB (@lem3221518 A s x) (@lem3221522 A u x)). Qed.
Lemma lem3221526 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term38 A s u) = (term39 A s u).
Proof. exact (fun_ext (fun x : A => @lem3221523 A s u x)). Qed.
Lemma lem3221527 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221528 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term4 A s u) = (term40 A s u).
Proof. exact (MK_COMB (@lem3221527 A) (@lem3221526 A s u)). Qed.
Lemma lem3221533 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221534 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term6 A s u) = (term41 A s u).
Proof. exact (MK_COMB (@lem3221533) (@lem3221528 A s u)). Qed.
Lemma lem3221535 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term7 A s u) = (term42 A s u).
Proof. exact (MK_COMB (@lem3221506 A s u) (@lem3221534 A s u)). Qed.
Lemma lem3221538 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term15 A t s u) = (term46 A t s u).
Proof. exact (MK_COMB (@lem3221476 A s t u) (@lem3221535 A s u)). Qed.
Lemma lem3221541 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term17 A t s) = (term47 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3221538 A t s u)). Qed.
Lemma lem3221542 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3221543 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term19 A t s) = (term48 A t s).
Proof. exact (MK_COMB (@lem3221542 A) (@lem3221541 A t s)). Qed.
Lemma lem3221548 {A : Type'} (s : A -> Prop) : (term21 A s) = (term49 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3221543 A t s)). Qed.
Lemma lem3221549 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3221550 {A : Type'} (s : A -> Prop) : (term23 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem3221549 A) (@lem3221548 A s)). Qed.
Lemma lem3221555 {A : Type'} : (term25 A) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3221550 A s)). Qed.
Lemma lem3221556 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3221557 {A : Type'} : (term27 A) = (term52 A).
Proof. exact (MK_COMB (@lem3221556 A) (@lem3221555 A)). Qed.
Lemma lem3221562 {A : Type'} : (term52 A) = (term27 A).
Proof. exact (SYM (@lem3221557 A)). Qed.
Lemma lem3221564 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3221565 {A : Type'} : (term52 A) = (term54 A).
Proof. exact (@lem3221564 (term52 A)). Qed.
Lemma lem3221566 {A : Type'} : (term54 A) = (term52 A).
Proof. exact (SYM (@lem3221565 A)). Qed.
Lemma lem3221567 {A : Type'} (h1 : term55 A) : term55 A.
Proof. exact (h1). Qed.
Lemma lem3221570 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3221571 {A : Type'} : term56 A.
Proof. exact (fun h0 : term54 A => @lem3221570 A h0). Qed.
Lemma lem3221572 {A : Type'} (h1 : term56 A) : term56 A.
Proof. exact (h1). Qed.
Lemma lem3221573 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3221574 {A : Type'} (h1 : term54 A) (h2 : term56 A) : term54 A.
Proof. exact (@lem3221572 A h2 (@lem3221573 A h1)). Qed.
Lemma lem3221575 {A : Type'} (h1 : term54 A) : term57 A.
Proof. exact (fun h0 : term56 A => @lem3221574 A h1 h0). Qed.
Lemma lem3221576 {A : Type'} (h1 : term56 A) : term56 A.
Proof. exact (h1). Qed.
Lemma lem3221577 {A : Type'} (h1 : term54 A) (h2 : term56 A) : term54 A.
Proof. exact (@lem3221575 A h1 (@lem3221576 A h2)). Qed.
Lemma lem3221578 {A : Type'} (h1 : term56 A) : term56 A.
Proof. exact (fun h0 : term54 A => @lem3221577 A h0 h1). Qed.
Lemma lem3221579 {A : Type'} : term58 A.
Proof. exact (fun h0 : term56 A => @lem3221578 A h0). Qed.
Lemma lem3221582 {A : Type'} : term56 A.
Proof. exact (@lem3221579 A (@lem3221571 A)). Qed.
Lemma lem3221583 {A : Type'} : term56 A.
Proof. exact (@lem3221582 A). Qed.
Lemma lem3221585 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3221586 {A : Type'} : (term54 A) = (term59 A).
Proof. exact (@lem3221585 (term55 A)). Qed.
Lemma lem3221588 (t : Prop) : (term60 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3221589 {A : Type'} : (term59 A) = (term52 A).
Proof. exact (@lem3221588 (term52 A)). Qed.
Lemma lem3221646 {A : Type'} : (term54 A) = (term52 A).
Proof. exact (TRANS (@lem3221586 A) (@lem3221589 A)). Qed.
Lemma lem3221651 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((s x) = (u x)) = ((s x) = (u x)).
Proof. exact (eq_refl ((s x) = (u x))). Qed.
Lemma lem3221652 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term39 A s u) = (term39 A s u).
Proof. exact (fun_ext (fun x : A => @lem3221651 A s u x)). Qed.
Lemma lem3221653 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221654 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term40 A s u) = (term40 A s u).
Proof. exact (MK_COMB (@lem3221653 A) (@lem3221652 A s u)). Qed.
Lemma lem3221655 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221656 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term41 A s u) = (term41 A s u).
Proof. exact (MK_COMB (@lem3221655) (@lem3221654 A s u)). Qed.
Lemma lem3221661 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term31 A s u x) = (term31 A s u x).
Proof. exact (eq_refl (term31 A s u x)). Qed.
Lemma lem3221662 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term33 A s u) = (term33 A s u).
Proof. exact (fun_ext (fun x : A => @lem3221661 A s u x)). Qed.
Lemma lem3221663 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221664 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term34 A s u) = (term34 A s u).
Proof. exact (MK_COMB (@lem3221663 A) (@lem3221662 A s u)). Qed.
Lemma lem3221665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221666 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term35 A s u) = (term35 A s u).
Proof. exact (MK_COMB (@lem3221665) (@lem3221664 A s u)). Qed.
Lemma lem3221667 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term42 A s u) = (term42 A s u).
Proof. exact (MK_COMB (@lem3221666 A s u) (@lem3221656 A s u)). Qed.
Lemma lem3221672 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : ((t x) = (u x)) = ((t x) = (u x)).
Proof. exact (eq_refl ((t x) = (u x))). Qed.
Lemma lem3221673 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term39 A t u) = (term39 A t u).
Proof. exact (fun_ext (fun x : A => @lem3221672 A t u x)). Qed.
Lemma lem3221674 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221675 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term40 A t u) = (term40 A t u).
Proof. exact (MK_COMB (@lem3221674 A) (@lem3221673 A t u)). Qed.
Lemma lem3221676 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221677 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term41 A t u) = (term41 A t u).
Proof. exact (MK_COMB (@lem3221676) (@lem3221675 A t u)). Qed.
Lemma lem3221682 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term31 A t u x) = (term31 A t u x).
Proof. exact (eq_refl (term31 A t u x)). Qed.
Lemma lem3221683 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term33 A t u) = (term33 A t u).
Proof. exact (fun_ext (fun x : A => @lem3221682 A t u x)). Qed.
Lemma lem3221684 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221685 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term34 A t u) = (term34 A t u).
Proof. exact (MK_COMB (@lem3221684 A) (@lem3221683 A t u)). Qed.
Lemma lem3221686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221687 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term35 A t u) = (term35 A t u).
Proof. exact (MK_COMB (@lem3221686) (@lem3221685 A t u)). Qed.
Lemma lem3221688 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term42 A t u) = (term42 A t u).
Proof. exact (MK_COMB (@lem3221687 A t u) (@lem3221677 A t u)). Qed.
Lemma lem3221693 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = ((s x) = (t x)).
Proof. exact (eq_refl ((s x) = (t x))). Qed.
Lemma lem3221694 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term39 A s t).
Proof. exact (fun_ext (fun x : A => @lem3221693 A s t x)). Qed.
Lemma lem3221695 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221696 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term40 A s t) = (term40 A s t).
Proof. exact (MK_COMB (@lem3221695 A) (@lem3221694 A s t)). Qed.
Lemma lem3221697 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221698 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3221697) (@lem3221696 A s t)). Qed.
Lemma lem3221703 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term31 A s t x) = (term31 A s t x).
Proof. exact (eq_refl (term31 A s t x)). Qed.
Lemma lem3221704 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term33 A s t).
Proof. exact (fun_ext (fun x : A => @lem3221703 A s t x)). Qed.
Lemma lem3221705 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221706 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term34 A s t).
Proof. exact (MK_COMB (@lem3221705 A) (@lem3221704 A s t)). Qed.
Lemma lem3221707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221708 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3221707) (@lem3221706 A s t)). Qed.
Lemma lem3221709 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = (term42 A s t).
Proof. exact (MK_COMB (@lem3221708 A s t) (@lem3221698 A s t)). Qed.
Lemma lem3221710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221711 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term43 A s t).
Proof. exact (MK_COMB (@lem3221710) (@lem3221709 A s t)). Qed.
Lemma lem3221712 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term44 A s t u) = (term44 A s t u).
Proof. exact (MK_COMB (@lem3221711 A s t) (@lem3221688 A t u)). Qed.
Lemma lem3221713 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3221714 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term45 A s t u) = (term45 A s t u).
Proof. exact (MK_COMB (@lem3221713) (@lem3221712 A s t u)). Qed.
Lemma lem3221715 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term46 A t s u) = (term46 A t s u).
Proof. exact (MK_COMB (@lem3221714 A s t u) (@lem3221667 A s u)). Qed.
Lemma lem3221716 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term47 A t s) = (term47 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3221715 A t s u)). Qed.
Lemma lem3221717 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3221718 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term48 A t s) = (term48 A t s).
Proof. exact (MK_COMB (@lem3221717 A) (@lem3221716 A t s)). Qed.
Lemma lem3221719 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3221718 A t s)). Qed.
Lemma lem3221720 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3221721 {A : Type'} (s : A -> Prop) : (term50 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem3221720 A) (@lem3221719 A s)). Qed.
Lemma lem3221722 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3221721 A s)). Qed.
Lemma lem3221723 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3221724 {A : Type'} : (term52 A) = (term52 A).
Proof. exact (MK_COMB (@lem3221723 A) (@lem3221722 A)). Qed.
Lemma lem3221797 {A : Type'} : (term54 A) = (term52 A).
Proof. exact (TRANS (@lem3221646 A) (@lem3221724 A)). Qed.
Lemma lem3221798 {A : Type'} : (term52 A) = (term54 A).
Proof. exact (SYM (@lem3221797 A)). Qed.
Lemma lem3221799 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term44 A s t u) : term44 A s t u.
Proof. exact (h1). Qed.
Lemma lem3221801 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3221802 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term42 A s u) = (term61 A s u).
Proof. exact (@lem3221801 (term42 A s u)). Qed.
Lemma lem3221803 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term61 A s u) = (term42 A s u).
Proof. exact (SYM (@lem3221802 A s u)). Qed.
Lemma lem3221804 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term62 A s u) : term62 A s u.
Proof. exact (h1). Qed.
Lemma lem3221811 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term31 A s t x) = (term63 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3221812 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3221811 A s t x)). Qed.
Lemma lem3221813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221814 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3221813 A) (@lem3221812 A s t)). Qed.
Lemma lem3221829 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term66 A s t x) = (term67 A s t x).
Proof. exact (@lem17646 (s x) (t x)). Qed.
Lemma lem3221830 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3221831 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term70 A s t).
Proof. exact (@lem3221830 A (term39 A s t)). Qed.
Lemma lem3221832 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term71 A s t x) = ((s x) = (t x)).
Proof. exact (eq_refl (term71 A s t x)). Qed.
Lemma lem3221833 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221834 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term72 A s t x) = (term66 A s t x).
Proof. exact (MK_COMB (@lem3221833) (@lem3221832 A s t x)). Qed.
Lemma lem3221835 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term72 A s t x) = (term67 A s t x).
Proof. exact (TRANS (@lem3221834 A s t x) (@lem3221829 A s t x)). Qed.
Lemma lem3221836 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term74 A s t).
Proof. exact (fun_ext (fun x : A => @lem3221835 A s t x)). Qed.
Lemma lem3221837 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3221838 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term70 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3221837 A) (@lem3221836 A s t)). Qed.
Lemma lem3221839 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term75 A s t).
Proof. exact (TRANS (@lem3221831 A s t) (@lem3221838 A s t)). Qed.
Lemma lem3221840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221841 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term76 A s t).
Proof. exact (MK_COMB (@lem3221840) (@lem3221814 A s t)). Qed.
Lemma lem3221842 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = (term77 A s t).
Proof. exact (MK_COMB (@lem3221841 A s t) (@lem3221839 A s t)). Qed.
Lemma lem3221849 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term31 A t u x) = (term63 A t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem3221850 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term33 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3221849 A t u x)). Qed.
Lemma lem3221851 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3221852 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term34 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3221851 A) (@lem3221850 A t u)). Qed.
Lemma lem3221867 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term66 A t u x) = (term67 A t u x).
Proof. exact (@lem17646 (t x) (u x)). Qed.
Lemma lem3221868 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3221869 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term41 A t u) = (term70 A t u).
Proof. exact (@lem3221868 A (term39 A t u)). Qed.
Lemma lem3221870 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term71 A t u x) = ((t x) = (u x)).
Proof. exact (eq_refl (term71 A t u x)). Qed.
Lemma lem3221871 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3221872 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term72 A t u x) = (term66 A t u x).
Proof. exact (MK_COMB (@lem3221871) (@lem3221870 A t u x)). Qed.
Lemma lem3221873 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term72 A t u x) = (term67 A t u x).
Proof. exact (TRANS (@lem3221872 A t u x) (@lem3221867 A t u x)). Qed.
Lemma lem3221874 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term73 A t u) = (term74 A t u).
Proof. exact (fun_ext (fun x : A => @lem3221873 A t u x)). Qed.
Lemma lem3221875 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3221876 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term70 A t u) = (term75 A t u).
Proof. exact (MK_COMB (@lem3221875 A) (@lem3221874 A t u)). Qed.
Lemma lem3221877 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term41 A t u) = (term75 A t u).
Proof. exact (TRANS (@lem3221869 A t u) (@lem3221876 A t u)). Qed.
Lemma lem3221878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221879 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term35 A t u) = (term76 A t u).
Proof. exact (MK_COMB (@lem3221878) (@lem3221852 A t u)). Qed.
Lemma lem3221880 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term42 A t u) = (term77 A t u).
Proof. exact (MK_COMB (@lem3221879 A t u) (@lem3221877 A t u)). Qed.
Lemma lem3221881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3221882 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term78 A s t).
Proof. exact (MK_COMB (@lem3221881) (@lem3221842 A s t)). Qed.
Lemma lem3221883 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term44 A s t u) = (term79 A s t u).
Proof. exact (MK_COMB (@lem3221882 A s t) (@lem3221880 A t u)). Qed.
Lemma lem3221917 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3221918 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (@lem3221917 A P Q). Qed.
Lemma lem3221919 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term83 A s t).
Proof. exact (@lem3221918 A (term84 A s t) (term85 A s t)). Qed.
Lemma lem3221920 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term87 A s t x).
Proof. exact (eq_refl (term86 A s t x)). Qed.
Lemma lem3221921 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3221922 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term88 A s t x) = (term89 A s t x).
Proof. exact (MK_COMB (@lem3221921) (@lem3221920 A s t x)). Qed.
Lemma lem3221923 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term90 A s t x) = (term91 A s t x).
Proof. exact (eq_refl (term90 A s t x)). Qed.
Lemma lem3221924 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term92 A s t x) = (term67 A s t x).
Proof. exact (MK_COMB (@lem3221922 A s t x) (@lem3221923 A s t x)). Qed.
Lemma lem3221925 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term74 A s t).
Proof. exact (fun_ext (fun x : A => @lem3221924 A s t x)). Qed.
Lemma lem3221926 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3221927 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3221926 A) (@lem3221925 A s t)). Qed.
Lemma lem3221928 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3221929 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term94 A s t) = (term95 A s t).
Proof. exact (MK_COMB (@lem3221928) (@lem3221927 A s t)). Qed.
Lemma lem3221930 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term87 A s t x).
Proof. exact (eq_refl (term86 A s t x)). Qed.
Lemma lem3221931 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term84 A s t).
Proof. exact (fun_ext (fun x : A => @lem3221930 A s t x)). Qed.
Lemma lem3221932 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3221933 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3221932 A) (@lem3221931 A s t)). Qed.
Lemma lem3221934 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3221935 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term99 A s t) = (term100 A s t).
Proof. exact (MK_COMB (@lem3221934) (@lem3221933 A s t)). Qed.
Lemma lem3221936 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term90 A s t x) = (term91 A s t x).
Proof. exact (eq_refl (term90 A s t x)). Qed.
Lemma lem3221937 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term101 A s t) = (term85 A s t).
Proof. exact (fun_ext (fun x : A => @lem3221936 A s t x)). Qed.
Lemma lem3221938 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3221939 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term103 A s t).
Proof. exact (MK_COMB (@lem3221938 A) (@lem3221937 A s t)). Qed.
Lemma lem3221940 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term104 A s t).
Proof. exact (MK_COMB (@lem3221935 A s t) (@lem3221939 A s t)). Qed.
Lemma lem3221941 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term82 A s t) = (term83 A s t)) = ((term75 A s t) = (term104 A s t)).
Proof. exact (MK_COMB (@lem3221929 A s t) (@lem3221940 A s t)). Qed.
Lemma lem3221942 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term75 A s t) = (term104 A s t).
Proof. exact (EQ_MP (@lem3221941 A s t) (@lem3221919 A s t)). Qed.
Lemma lem3222003 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term76 A s t).
Proof. exact (eq_refl (term76 A s t)). Qed.
Lemma lem3222004 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term105 A s t).
Proof. exact (MK_COMB (@lem3222003 A s t) (@lem3221942 A s t)). Qed.
Lemma lem3222005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3222006 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term106 A s t).
Proof. exact (MK_COMB (@lem3222005) (@lem3222004 A s t)). Qed.
Lemma lem3222040 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3222041 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (@lem3222040 A P Q). Qed.
Lemma lem3222042 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term82 A t u) = (term83 A t u).
Proof. exact (@lem3222041 A (term84 A t u) (term85 A t u)). Qed.
Lemma lem3222043 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term86 A t u x) = (term87 A t u x).
Proof. exact (eq_refl (term86 A t u x)). Qed.
Lemma lem3222044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3222045 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term88 A t u x) = (term89 A t u x).
Proof. exact (MK_COMB (@lem3222044) (@lem3222043 A t u x)). Qed.
Lemma lem3222046 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term90 A t u x) = (term91 A t u x).
Proof. exact (eq_refl (term90 A t u x)). Qed.
Lemma lem3222047 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term92 A t u x) = (term67 A t u x).
Proof. exact (MK_COMB (@lem3222045 A t u x) (@lem3222046 A t u x)). Qed.
Lemma lem3222048 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term93 A t u) = (term74 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222047 A t u x)). Qed.
Lemma lem3222049 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222050 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term82 A t u) = (term75 A t u).
Proof. exact (MK_COMB (@lem3222049 A) (@lem3222048 A t u)). Qed.
Lemma lem3222051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3222052 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term94 A t u) = (term95 A t u).
Proof. exact (MK_COMB (@lem3222051) (@lem3222050 A t u)). Qed.
Lemma lem3222053 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term86 A t u x) = (term87 A t u x).
Proof. exact (eq_refl (term86 A t u x)). Qed.
Lemma lem3222054 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term96 A t u) = (term84 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222053 A t u x)). Qed.
Lemma lem3222055 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222056 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term97 A t u) = (term98 A t u).
Proof. exact (MK_COMB (@lem3222055 A) (@lem3222054 A t u)). Qed.
Lemma lem3222057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3222058 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term99 A t u) = (term100 A t u).
Proof. exact (MK_COMB (@lem3222057) (@lem3222056 A t u)). Qed.
Lemma lem3222059 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term90 A t u x) = (term91 A t u x).
Proof. exact (eq_refl (term90 A t u x)). Qed.
Lemma lem3222060 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term101 A t u) = (term85 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222059 A t u x)). Qed.
Lemma lem3222061 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222062 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term102 A t u) = (term103 A t u).
Proof. exact (MK_COMB (@lem3222061 A) (@lem3222060 A t u)). Qed.
Lemma lem3222063 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term83 A t u) = (term104 A t u).
Proof. exact (MK_COMB (@lem3222058 A t u) (@lem3222062 A t u)). Qed.
Lemma lem3222064 {A : Type'} (t : A -> Prop) (u : A -> Prop) : ((term82 A t u) = (term83 A t u)) = ((term75 A t u) = (term104 A t u)).
Proof. exact (MK_COMB (@lem3222052 A t u) (@lem3222063 A t u)). Qed.
Lemma lem3222065 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term75 A t u) = (term104 A t u).
Proof. exact (EQ_MP (@lem3222064 A t u) (@lem3222042 A t u)). Qed.
Lemma lem3222126 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term76 A t u) = (term76 A t u).
Proof. exact (eq_refl (term76 A t u)). Qed.
Lemma lem3222127 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term77 A t u) = (term105 A t u).
Proof. exact (MK_COMB (@lem3222126 A t u) (@lem3222065 A t u)). Qed.
Lemma lem3222128 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term79 A s t u) = (term107 A s t u).
Proof. exact (MK_COMB (@lem3222006 A s t) (@lem3222127 A t u)). Qed.
Lemma lem3222130 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3222131 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (@lem3222130 A P Q). Qed.
Lemma lem3222132 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term82 A s t).
Proof. exact (@lem3222131 A (term84 A s t) (term85 A s t)). Qed.
Lemma lem3222133 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term87 A s t x).
Proof. exact (eq_refl (term86 A s t x)). Qed.
Lemma lem3222134 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term84 A s t).
Proof. exact (fun_ext (fun x : A => @lem3222133 A s t x)). Qed.
Lemma lem3222135 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222136 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3222135 A) (@lem3222134 A s t)). Qed.
Lemma lem3222137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3222138 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term99 A s t) = (term100 A s t).
Proof. exact (MK_COMB (@lem3222137) (@lem3222136 A s t)). Qed.
Lemma lem3222139 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term90 A s t x) = (term91 A s t x).
Proof. exact (eq_refl (term90 A s t x)). Qed.
Lemma lem3222140 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term101 A s t) = (term85 A s t).
Proof. exact (fun_ext (fun x : A => @lem3222139 A s t x)). Qed.
Lemma lem3222141 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222142 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term103 A s t).
Proof. exact (MK_COMB (@lem3222141 A) (@lem3222140 A s t)). Qed.
Lemma lem3222143 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term104 A s t).
Proof. exact (MK_COMB (@lem3222138 A s t) (@lem3222142 A s t)). Qed.
Lemma lem3222144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3222145 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term108 A s t) = (term109 A s t).
Proof. exact (MK_COMB (@lem3222144) (@lem3222143 A s t)). Qed.
Lemma lem3222146 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term87 A s t x).
Proof. exact (eq_refl (term86 A s t x)). Qed.
Lemma lem3222147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3222148 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term88 A s t x) = (term89 A s t x).
Proof. exact (MK_COMB (@lem3222147) (@lem3222146 A s t x)). Qed.
Lemma lem3222149 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term90 A s t x) = (term91 A s t x).
Proof. exact (eq_refl (term90 A s t x)). Qed.
Lemma lem3222150 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term92 A s t x) = (term67 A s t x).
Proof. exact (MK_COMB (@lem3222148 A s t x) (@lem3222149 A s t x)). Qed.
Lemma lem3222151 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term74 A s t).
Proof. exact (fun_ext (fun x : A => @lem3222150 A s t x)). Qed.
Lemma lem3222152 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222153 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3222152 A) (@lem3222151 A s t)). Qed.
Lemma lem3222154 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term83 A s t) = (term82 A s t)) = ((term104 A s t) = (term75 A s t)).
Proof. exact (MK_COMB (@lem3222145 A s t) (@lem3222153 A s t)). Qed.
Lemma lem3222155 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term104 A s t) = (term75 A s t).
Proof. exact (EQ_MP (@lem3222154 A s t) (@lem3222132 A s t)). Qed.
Lemma lem3222156 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term76 A s t).
Proof. exact (eq_refl (term76 A s t)). Qed.
Lemma lem3222157 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term77 A s t).
Proof. exact (MK_COMB (@lem3222156 A s t) (@lem3222155 A s t)). Qed.
Lemma lem3222159 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3222160 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (@lem3222159 A P Q). Qed.
Lemma lem3222161 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term113 A s t).
Proof. exact (@lem3222160 A (term65 A s t) (term74 A s t)). Qed.
Lemma lem3222162 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term114 A s t x) = (term67 A s t x).
Proof. exact (eq_refl (term114 A s t x)). Qed.
Lemma lem3222163 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term115 A s t) = (term74 A s t).
Proof. exact (fun_ext (fun x : A => @lem3222162 A s t x)). Qed.
Lemma lem3222164 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222165 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term116 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3222164 A) (@lem3222163 A s t)). Qed.
Lemma lem3222166 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term76 A s t).
Proof. exact (eq_refl (term76 A s t)). Qed.
Lemma lem3222167 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term77 A s t).
Proof. exact (MK_COMB (@lem3222166 A s t) (@lem3222165 A s t)). Qed.
Lemma lem3222168 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3222169 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term117 A s t) = (term118 A s t).
Proof. exact (MK_COMB (@lem3222168) (@lem3222167 A s t)). Qed.
Lemma lem3222170 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term114 A s t x) = (term67 A s t x).
Proof. exact (eq_refl (term114 A s t x)). Qed.
Lemma lem3222171 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term76 A s t).
Proof. exact (eq_refl (term76 A s t)). Qed.
Lemma lem3222172 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term119 A s t x) = (term120 A s t x).
Proof. exact (MK_COMB (@lem3222171 A s t) (@lem3222170 A s t x)). Qed.
Lemma lem3222173 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term121 A s t) = (term122 A s t).
Proof. exact (fun_ext (fun x : A => @lem3222172 A s t x)). Qed.
Lemma lem3222174 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222175 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term113 A s t) = (term123 A s t).
Proof. exact (MK_COMB (@lem3222174 A) (@lem3222173 A s t)). Qed.
Lemma lem3222176 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term112 A s t) = (term113 A s t)) = ((term77 A s t) = (term123 A s t)).
Proof. exact (MK_COMB (@lem3222169 A s t) (@lem3222175 A s t)). Qed.
Lemma lem3222177 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term123 A s t).
Proof. exact (EQ_MP (@lem3222176 A s t) (@lem3222161 A s t)). Qed.
Lemma lem3222178 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term123 A s t).
Proof. exact (TRANS (@lem3222157 A s t) (@lem3222177 A s t)). Qed.
Lemma lem3222179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3222180 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term124 A s t).
Proof. exact (MK_COMB (@lem3222179) (@lem3222178 A s t)). Qed.
Lemma lem3222182 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3222183 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (@lem3222182 A P Q). Qed.
Lemma lem3222184 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term83 A t u) = (term82 A t u).
Proof. exact (@lem3222183 A (term84 A t u) (term85 A t u)). Qed.
Lemma lem3222185 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term86 A t u x) = (term87 A t u x).
Proof. exact (eq_refl (term86 A t u x)). Qed.
Lemma lem3222186 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term96 A t u) = (term84 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222185 A t u x)). Qed.
Lemma lem3222187 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222188 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term97 A t u) = (term98 A t u).
Proof. exact (MK_COMB (@lem3222187 A) (@lem3222186 A t u)). Qed.
Lemma lem3222189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3222190 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term99 A t u) = (term100 A t u).
Proof. exact (MK_COMB (@lem3222189) (@lem3222188 A t u)). Qed.
Lemma lem3222191 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term90 A t u x) = (term91 A t u x).
Proof. exact (eq_refl (term90 A t u x)). Qed.
Lemma lem3222192 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term101 A t u) = (term85 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222191 A t u x)). Qed.
Lemma lem3222193 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222194 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term102 A t u) = (term103 A t u).
Proof. exact (MK_COMB (@lem3222193 A) (@lem3222192 A t u)). Qed.
Lemma lem3222195 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term83 A t u) = (term104 A t u).
Proof. exact (MK_COMB (@lem3222190 A t u) (@lem3222194 A t u)). Qed.
Lemma lem3222196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3222197 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term108 A t u) = (term109 A t u).
Proof. exact (MK_COMB (@lem3222196) (@lem3222195 A t u)). Qed.
Lemma lem3222198 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term86 A t u x) = (term87 A t u x).
Proof. exact (eq_refl (term86 A t u x)). Qed.
Lemma lem3222199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3222200 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term88 A t u x) = (term89 A t u x).
Proof. exact (MK_COMB (@lem3222199) (@lem3222198 A t u x)). Qed.
Lemma lem3222201 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term90 A t u x) = (term91 A t u x).
Proof. exact (eq_refl (term90 A t u x)). Qed.
Lemma lem3222202 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term92 A t u x) = (term67 A t u x).
Proof. exact (MK_COMB (@lem3222200 A t u x) (@lem3222201 A t u x)). Qed.
Lemma lem3222203 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term93 A t u) = (term74 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222202 A t u x)). Qed.
Lemma lem3222204 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222205 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term82 A t u) = (term75 A t u).
Proof. exact (MK_COMB (@lem3222204 A) (@lem3222203 A t u)). Qed.
Lemma lem3222206 {A : Type'} (t : A -> Prop) (u : A -> Prop) : ((term83 A t u) = (term82 A t u)) = ((term104 A t u) = (term75 A t u)).
Proof. exact (MK_COMB (@lem3222197 A t u) (@lem3222205 A t u)). Qed.
Lemma lem3222207 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term104 A t u) = (term75 A t u).
Proof. exact (EQ_MP (@lem3222206 A t u) (@lem3222184 A t u)). Qed.
Lemma lem3222208 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term76 A t u) = (term76 A t u).
Proof. exact (eq_refl (term76 A t u)). Qed.
Lemma lem3222209 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term105 A t u) = (term77 A t u).
Proof. exact (MK_COMB (@lem3222208 A t u) (@lem3222207 A t u)). Qed.
Lemma lem3222211 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3222212 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (@lem3222211 A P Q). Qed.
Lemma lem3222213 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term112 A t u) = (term113 A t u).
Proof. exact (@lem3222212 A (term65 A t u) (term74 A t u)). Qed.
Lemma lem3222214 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term114 A t u x) = (term67 A t u x).
Proof. exact (eq_refl (term114 A t u x)). Qed.
Lemma lem3222215 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term115 A t u) = (term74 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222214 A t u x)). Qed.
Lemma lem3222216 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222217 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term116 A t u) = (term75 A t u).
Proof. exact (MK_COMB (@lem3222216 A) (@lem3222215 A t u)). Qed.
Lemma lem3222218 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term76 A t u) = (term76 A t u).
Proof. exact (eq_refl (term76 A t u)). Qed.
Lemma lem3222219 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term112 A t u) = (term77 A t u).
Proof. exact (MK_COMB (@lem3222218 A t u) (@lem3222217 A t u)). Qed.
Lemma lem3222220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3222221 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term117 A t u) = (term118 A t u).
Proof. exact (MK_COMB (@lem3222220) (@lem3222219 A t u)). Qed.
Lemma lem3222222 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term114 A t u x) = (term67 A t u x).
Proof. exact (eq_refl (term114 A t u x)). Qed.
Lemma lem3222223 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term76 A t u) = (term76 A t u).
Proof. exact (eq_refl (term76 A t u)). Qed.
Lemma lem3222224 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term119 A t u x) = (term120 A t u x).
Proof. exact (MK_COMB (@lem3222223 A t u) (@lem3222222 A t u x)). Qed.
Lemma lem3222225 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term121 A t u) = (term122 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222224 A t u x)). Qed.
Lemma lem3222226 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222227 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term113 A t u) = (term123 A t u).
Proof. exact (MK_COMB (@lem3222226 A) (@lem3222225 A t u)). Qed.
Lemma lem3222228 {A : Type'} (t : A -> Prop) (u : A -> Prop) : ((term112 A t u) = (term113 A t u)) = ((term77 A t u) = (term123 A t u)).
Proof. exact (MK_COMB (@lem3222221 A t u) (@lem3222227 A t u)). Qed.
Lemma lem3222229 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term77 A t u) = (term123 A t u).
Proof. exact (EQ_MP (@lem3222228 A t u) (@lem3222213 A t u)). Qed.
Lemma lem3222230 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term105 A t u) = (term123 A t u).
Proof. exact (TRANS (@lem3222209 A t u) (@lem3222229 A t u)). Qed.
Lemma lem3222231 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term107 A s t u) = (term125 A s t u).
Proof. exact (MK_COMB (@lem3222180 A s t) (@lem3222230 A t u)). Qed.
Lemma lem3222233 {A : Type'} (P : A -> Prop) (Q : Prop) : (term126 A P Q) = (term127 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3222234 {A : Type'} (P : A -> Prop) (Q : Prop) : (term126 A P Q) = (term127 A P Q).
Proof. exact (@lem3222233 A P Q). Qed.
Lemma lem3222235 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term128 A s t u) = (term129 A s t u).
Proof. exact (@lem3222234 A (term122 A s t) (term123 A t u)). Qed.
Lemma lem3222236 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term130 A s t x) = (term120 A s t x).
Proof. exact (eq_refl (term130 A s t x)). Qed.
Lemma lem3222237 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term131 A s t) = (term122 A s t).
Proof. exact (fun_ext (fun x : A => @lem3222236 A s t x)). Qed.
Lemma lem3222238 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222239 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term132 A s t) = (term123 A s t).
Proof. exact (MK_COMB (@lem3222238 A) (@lem3222237 A s t)). Qed.
Lemma lem3222240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3222241 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term133 A s t) = (term124 A s t).
Proof. exact (MK_COMB (@lem3222240) (@lem3222239 A s t)). Qed.
Lemma lem3222242 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term123 A t u) = (term123 A t u).
Proof. exact (eq_refl (term123 A t u)). Qed.
Lemma lem3222243 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term128 A s t u) = (term125 A s t u).
Proof. exact (MK_COMB (@lem3222241 A s t) (@lem3222242 A t u)). Qed.
Lemma lem3222244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3222245 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term134 A s t u) = (term135 A s t u).
Proof. exact (MK_COMB (@lem3222244) (@lem3222243 A s t u)). Qed.
Lemma lem3222246 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term130 A s t x) = (term120 A s t x).
Proof. exact (eq_refl (term130 A s t x)). Qed.
Lemma lem3222247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3222248 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term136 A s t x) = (term137 A s t x).
Proof. exact (MK_COMB (@lem3222247) (@lem3222246 A s t x)). Qed.
Lemma lem3222249 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term123 A t u) = (term123 A t u).
Proof. exact (eq_refl (term123 A t u)). Qed.
Lemma lem3222250 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term138 A s x t u) = (term139 A s x t u).
Proof. exact (MK_COMB (@lem3222248 A s t x) (@lem3222249 A t u)). Qed.
Lemma lem3222251 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term140 A s t u) = (term141 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3222250 A s x t u)). Qed.
Lemma lem3222252 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222253 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term129 A s t u) = (term142 A s t u).
Proof. exact (MK_COMB (@lem3222252 A) (@lem3222251 A s t u)). Qed.
Lemma lem3222254 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term128 A s t u) = (term129 A s t u)) = ((term125 A s t u) = (term142 A s t u)).
Proof. exact (MK_COMB (@lem3222245 A s t u) (@lem3222253 A s t u)). Qed.
Lemma lem3222255 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term125 A s t u) = (term142 A s t u).
Proof. exact (EQ_MP (@lem3222254 A s t u) (@lem3222235 A s t u)). Qed.
Lemma lem3222257 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3222258 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (@lem3222257 A P Q). Qed.
Lemma lem3222259 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term143 A s x t u) = (term144 A s x t u).
Proof. exact (@lem3222258 A (term120 A s t x) (term122 A t u)). Qed.
Lemma lem3222260 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term130 A t u x) = (term120 A t u x).
Proof. exact (eq_refl (term130 A t u x)). Qed.
Lemma lem3222261 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term131 A t u) = (term122 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222260 A t u x)). Qed.
Lemma lem3222262 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222263 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term132 A t u) = (term123 A t u).
Proof. exact (MK_COMB (@lem3222262 A) (@lem3222261 A t u)). Qed.
Lemma lem3222264 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term137 A s t x) = (term137 A s t x).
Proof. exact (eq_refl (term137 A s t x)). Qed.
Lemma lem3222265 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term143 A s x t u) = (term139 A s x t u).
Proof. exact (MK_COMB (@lem3222264 A s t x) (@lem3222263 A t u)). Qed.
Lemma lem3222266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3222267 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term145 A s x t u) = (term146 A s x t u).
Proof. exact (MK_COMB (@lem3222266) (@lem3222265 A s x t u)). Qed.
Lemma lem3222268 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) : (term130 A t u x') = (term120 A t u x').
Proof. exact (eq_refl (term130 A t u x')). Qed.
Lemma lem3222269 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term137 A s t x) = (term137 A s t x).
Proof. exact (eq_refl (term137 A s t x)). Qed.
Lemma lem3222270 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) (x' : A) : (term147 A s x t u x') = (term148 A s x t u x').
Proof. exact (MK_COMB (@lem3222269 A s t x) (@lem3222268 A t u x')). Qed.
Lemma lem3222271 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term149 A s x t u) = (term150 A s x t u).
Proof. exact (fun_ext (fun x' : A => @lem3222270 A s x t u x')). Qed.
Lemma lem3222272 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222273 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term144 A s x t u) = (term151 A s x t u).
Proof. exact (MK_COMB (@lem3222272 A) (@lem3222271 A s x t u)). Qed.
Lemma lem3222274 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : ((term143 A s x t u) = (term144 A s x t u)) = ((term139 A s x t u) = (term151 A s x t u)).
Proof. exact (MK_COMB (@lem3222267 A s x t u) (@lem3222273 A s x t u)). Qed.
Lemma lem3222275 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term139 A s x t u) = (term151 A s x t u).
Proof. exact (EQ_MP (@lem3222274 A s x t u) (@lem3222259 A s x t u)). Qed.
Lemma lem3222276 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term141 A s t u) = (term152 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3222275 A s x t u)). Qed.
Lemma lem3222277 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222278 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term142 A s t u) = (term153 A s t u).
Proof. exact (MK_COMB (@lem3222277 A) (@lem3222276 A s t u)). Qed.
Lemma lem3222279 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term125 A s t u) = (term153 A s t u).
Proof. exact (TRANS (@lem3222255 A s t u) (@lem3222278 A s t u)). Qed.
Lemma lem3222280 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term107 A s t u) = (term153 A s t u).
Proof. exact (TRANS (@lem3222231 A s t u) (@lem3222279 A s t u)). Qed.
Lemma lem3222281 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term79 A s t u) = (term153 A s t u).
Proof. exact (TRANS (@lem3222128 A s t u) (@lem3222280 A s t u)). Qed.
Lemma lem3222282 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term44 A s t u) = (term153 A s t u).
Proof. exact (TRANS (@lem3221883 A s t u) (@lem3222281 A s t u)). Qed.
Lemma lem3222283 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term44 A s t u) : term153 A s t u.
Proof. exact (EQ_MP (@lem3222282 A s t u) (@lem3221799 A s t u h1)). Qed.
Lemma lem3222290 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term154 A s u x) = (term87 A s u x).
Proof. exact (@lem17362 (s x) (u x)). Qed.
Lemma lem3222291 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3222292 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term155 A s u) = (term156 A s u).
Proof. exact (@lem3222291 A (term33 A s u)). Qed.
Lemma lem3222293 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term157 A s u x) = (term31 A s u x).
Proof. exact (eq_refl (term157 A s u x)). Qed.
Lemma lem3222294 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3222295 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term158 A s u x) = (term154 A s u x).
Proof. exact (MK_COMB (@lem3222294) (@lem3222293 A s u x)). Qed.
Lemma lem3222296 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term158 A s u x) = (term87 A s u x).
Proof. exact (TRANS (@lem3222295 A s u x) (@lem3222290 A s u x)). Qed.
Lemma lem3222297 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term159 A s u) = (term84 A s u).
Proof. exact (fun_ext (fun x : A => @lem3222296 A s u x)). Qed.
Lemma lem3222298 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222299 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term156 A s u) = (term98 A s u).
Proof. exact (MK_COMB (@lem3222298 A) (@lem3222297 A s u)). Qed.
Lemma lem3222300 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term155 A s u) = (term98 A s u).
Proof. exact (TRANS (@lem3222292 A s u) (@lem3222299 A s u)). Qed.
Lemma lem3222315 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((s x) = (u x)) = (term160 A s u x).
Proof. exact (@lem17784 (s x) (u x)). Qed.
Lemma lem3222316 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term39 A s u) = (term161 A s u).
Proof. exact (fun_ext (fun x : A => @lem3222315 A s u x)). Qed.
Lemma lem3222317 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222318 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term40 A s u) = (term162 A s u).
Proof. exact (MK_COMB (@lem3222317 A) (@lem3222316 A s u)). Qed.
Lemma lem3222319 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term163 A s u) = (term40 A s u).
Proof. exact (@lem16933 (term40 A s u)). Qed.
Lemma lem3222320 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term163 A s u) = (term162 A s u).
Proof. exact (TRANS (@lem3222319 A s u) (@lem3222318 A s u)). Qed.
Lemma lem3222321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3222322 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term164 A s u) = (term100 A s u).
Proof. exact (MK_COMB (@lem3222321) (@lem3222300 A s u)). Qed.
Lemma lem3222323 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term165 A s u) = (term166 A s u).
Proof. exact (MK_COMB (@lem3222322 A s u) (@lem3222320 A s u)). Qed.
Lemma lem3222324 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term62 A s u) = (term165 A s u).
Proof. exact (@lem17045 (term34 A s u) (term41 A s u)). Qed.
Lemma lem3222325 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term62 A s u) = (term166 A s u).
Proof. exact (TRANS (@lem3222324 A s u) (@lem3222323 A s u)). Qed.
Lemma lem3222355 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3222356 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem3222355 A P Q). Qed.
Lemma lem3222357 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term169 A s u) = (term170 A s u).
Proof. exact (@lem3222356 A (term171 A s u) (term64 A s u)). Qed.
Lemma lem3222358 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term172 A s u x) = (term173 A s u x).
Proof. exact (eq_refl (term172 A s u x)). Qed.
Lemma lem3222359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3222360 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term174 A s u x) = (term175 A s u x).
Proof. exact (MK_COMB (@lem3222359) (@lem3222358 A s u x)). Qed.
Lemma lem3222361 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term176 A s u x) = (term63 A s u x).
Proof. exact (eq_refl (term176 A s u x)). Qed.
Lemma lem3222362 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term177 A s u x) = (term160 A s u x).
Proof. exact (MK_COMB (@lem3222360 A s u x) (@lem3222361 A s u x)). Qed.
Lemma lem3222363 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term178 A s u) = (term161 A s u).
Proof. exact (fun_ext (fun x : A => @lem3222362 A s u x)). Qed.
Lemma lem3222364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222365 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term169 A s u) = (term162 A s u).
Proof. exact (MK_COMB (@lem3222364 A) (@lem3222363 A s u)). Qed.
Lemma lem3222366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3222367 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term179 A s u) = (term180 A s u).
Proof. exact (MK_COMB (@lem3222366) (@lem3222365 A s u)). Qed.
Lemma lem3222368 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term172 A s u x) = (term173 A s u x).
Proof. exact (eq_refl (term172 A s u x)). Qed.
Lemma lem3222369 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term181 A s u) = (term171 A s u).
Proof. exact (fun_ext (fun x : A => @lem3222368 A s u x)). Qed.
Lemma lem3222370 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222371 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term182 A s u) = (term183 A s u).
Proof. exact (MK_COMB (@lem3222370 A) (@lem3222369 A s u)). Qed.
Lemma lem3222372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3222373 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term184 A s u) = (term185 A s u).
Proof. exact (MK_COMB (@lem3222372) (@lem3222371 A s u)). Qed.
Lemma lem3222374 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term176 A s u x) = (term63 A s u x).
Proof. exact (eq_refl (term176 A s u x)). Qed.
Lemma lem3222375 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term186 A s u) = (term64 A s u).
Proof. exact (fun_ext (fun x : A => @lem3222374 A s u x)). Qed.
Lemma lem3222376 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222377 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term187 A s u) = (term65 A s u).
Proof. exact (MK_COMB (@lem3222376 A) (@lem3222375 A s u)). Qed.
Lemma lem3222378 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term170 A s u) = (term188 A s u).
Proof. exact (MK_COMB (@lem3222373 A s u) (@lem3222377 A s u)). Qed.
Lemma lem3222379 {A : Type'} (s : A -> Prop) (u : A -> Prop) : ((term169 A s u) = (term170 A s u)) = ((term162 A s u) = (term188 A s u)).
Proof. exact (MK_COMB (@lem3222367 A s u) (@lem3222378 A s u)). Qed.
Lemma lem3222380 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term162 A s u) = (term188 A s u).
Proof. exact (EQ_MP (@lem3222379 A s u) (@lem3222357 A s u)). Qed.
Lemma lem3222441 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term100 A s u) = (term100 A s u).
Proof. exact (eq_refl (term100 A s u)). Qed.
Lemma lem3222442 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term166 A s u) = (term189 A s u).
Proof. exact (MK_COMB (@lem3222441 A s u) (@lem3222380 A s u)). Qed.
Lemma lem3222444 {A : Type'} (P : A -> Prop) (Q : Prop) : (term190 A P Q) = (term191 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3222445 {A : Type'} (P : A -> Prop) (Q : Prop) : (term190 A P Q) = (term191 A P Q).
Proof. exact (@lem3222444 A P Q). Qed.
Lemma lem3222446 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term192 A s u) = (term193 A s u).
Proof. exact (@lem3222445 A (term84 A s u) (term188 A s u)). Qed.
Lemma lem3222447 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term86 A s u x) = (term87 A s u x).
Proof. exact (eq_refl (term86 A s u x)). Qed.
Lemma lem3222448 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term96 A s u) = (term84 A s u).
Proof. exact (fun_ext (fun x : A => @lem3222447 A s u x)). Qed.
Lemma lem3222449 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222450 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term97 A s u) = (term98 A s u).
Proof. exact (MK_COMB (@lem3222449 A) (@lem3222448 A s u)). Qed.
Lemma lem3222451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3222452 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term99 A s u) = (term100 A s u).
Proof. exact (MK_COMB (@lem3222451) (@lem3222450 A s u)). Qed.
Lemma lem3222453 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term188 A s u) = (term188 A s u).
Proof. exact (eq_refl (term188 A s u)). Qed.
Lemma lem3222454 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term192 A s u) = (term189 A s u).
Proof. exact (MK_COMB (@lem3222452 A s u) (@lem3222453 A s u)). Qed.
Lemma lem3222455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3222456 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term194 A s u) = (term195 A s u).
Proof. exact (MK_COMB (@lem3222455) (@lem3222454 A s u)). Qed.
Lemma lem3222457 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term86 A s u x) = (term87 A s u x).
Proof. exact (eq_refl (term86 A s u x)). Qed.
Lemma lem3222458 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3222459 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term88 A s u x) = (term89 A s u x).
Proof. exact (MK_COMB (@lem3222458) (@lem3222457 A s u x)). Qed.
Lemma lem3222460 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term188 A s u) = (term188 A s u).
Proof. exact (eq_refl (term188 A s u)). Qed.
Lemma lem3222461 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) : (term196 A x s u) = (term197 A x s u).
Proof. exact (MK_COMB (@lem3222459 A s u x) (@lem3222460 A s u)). Qed.
Lemma lem3222462 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term198 A s u) = (term199 A s u).
Proof. exact (fun_ext (fun x : A => @lem3222461 A x s u)). Qed.
Lemma lem3222463 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3222464 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term193 A s u) = (term200 A s u).
Proof. exact (MK_COMB (@lem3222463 A) (@lem3222462 A s u)). Qed.
Lemma lem3222465 {A : Type'} (s : A -> Prop) (u : A -> Prop) : ((term192 A s u) = (term193 A s u)) = ((term189 A s u) = (term200 A s u)).
Proof. exact (MK_COMB (@lem3222456 A s u) (@lem3222464 A s u)). Qed.
Lemma lem3222466 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term189 A s u) = (term200 A s u).
Proof. exact (EQ_MP (@lem3222465 A s u) (@lem3222446 A s u)). Qed.
Lemma lem3222467 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term166 A s u) = (term200 A s u).
Proof. exact (TRANS (@lem3222442 A s u) (@lem3222466 A s u)). Qed.
Lemma lem3222468 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term62 A s u) = (term200 A s u).
Proof. exact (TRANS (@lem3222325 A s u) (@lem3222467 A s u)). Qed.
Lemma lem3222469 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term62 A s u) : term200 A s u.
Proof. exact (EQ_MP (@lem3222468 A s u) (@lem3221804 A s u h1)). Qed.
Lemma lem3222470 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term197 A x s u) : term197 A x s u.
Proof. exact (h1). Qed.
Lemma lem3222471 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (h1 : term151 A s x' t u) : term151 A s x' t u.
Proof. exact (h1). Qed.
Lemma lem3222472 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term148 A s x' t u x''.
Proof. exact (h1). Qed.
Lemma lem3222483 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term63 A s u x) = (term63 A s u x).
Proof. exact (eq_refl (term63 A s u x)). Qed.
Lemma lem3222484 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term64 A s u) = (term64 A s u).
Proof. exact (fun_ext (fun x : A => @lem3222483 A s u x)). Qed.
Lemma lem3222485 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222486 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term65 A s u) = (term65 A s u).
Proof. exact (MK_COMB (@lem3222485 A) (@lem3222484 A s u)). Qed.
Lemma lem3222497 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term173 A s u x) = (term173 A s u x).
Proof. exact (eq_refl (term173 A s u x)). Qed.
Lemma lem3222498 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term171 A s u) = (term171 A s u).
Proof. exact (fun_ext (fun x : A => @lem3222497 A s u x)). Qed.
Lemma lem3222499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222500 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term183 A s u) = (term183 A s u).
Proof. exact (MK_COMB (@lem3222499 A) (@lem3222498 A s u)). Qed.
Lemma lem3222501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3222502 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term185 A s u) = (term185 A s u).
Proof. exact (MK_COMB (@lem3222501) (@lem3222500 A s u)). Qed.
Lemma lem3222503 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term188 A s u) = (term188 A s u).
Proof. exact (MK_COMB (@lem3222502 A s u) (@lem3222486 A s u)). Qed.
Lemma lem3222516 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term89 A s u x) = (term89 A s u x).
Proof. exact (eq_refl (term89 A s u x)). Qed.
Lemma lem3222517 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) : (term197 A x s u) = (term197 A x s u).
Proof. exact (MK_COMB (@lem3222516 A s u x) (@lem3222503 A s u)). Qed.
Lemma lem3222518 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term197 A x s u) : term197 A x s u.
Proof. exact (EQ_MP (@lem3222517 A x s u) (@lem3222470 A x s u h1)). Qed.
Lemma lem3222543 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) : (term67 A t u x'') = (term67 A t u x'').
Proof. exact (eq_refl (term67 A t u x'')). Qed.
Lemma lem3222554 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term63 A t u x) = (term63 A t u x).
Proof. exact (eq_refl (term63 A t u x)). Qed.
Lemma lem3222555 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term64 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222554 A t u x)). Qed.
Lemma lem3222556 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222557 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3222556 A) (@lem3222555 A t u)). Qed.
Lemma lem3222558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3222559 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term76 A t u) = (term76 A t u).
Proof. exact (MK_COMB (@lem3222558) (@lem3222557 A t u)). Qed.
Lemma lem3222560 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) : (term120 A t u x'') = (term120 A t u x'').
Proof. exact (MK_COMB (@lem3222559 A t u) (@lem3222543 A t u x'')). Qed.
Lemma lem3222585 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term67 A s t x') = (term67 A s t x').
Proof. exact (eq_refl (term67 A s t x')). Qed.
Lemma lem3222596 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term63 A s t x).
Proof. exact (eq_refl (term63 A s t x)). Qed.
Lemma lem3222597 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3222596 A s t x)). Qed.
Lemma lem3222598 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222599 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3222598 A) (@lem3222597 A s t)). Qed.
Lemma lem3222600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3222601 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term76 A s t).
Proof. exact (MK_COMB (@lem3222600) (@lem3222599 A s t)). Qed.
Lemma lem3222602 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term120 A s t x') = (term120 A s t x').
Proof. exact (MK_COMB (@lem3222601 A s t) (@lem3222585 A s t x')). Qed.
Lemma lem3222603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3222604 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term137 A s t x') = (term137 A s t x').
Proof. exact (MK_COMB (@lem3222603) (@lem3222602 A s t x')). Qed.
Lemma lem3222605 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) : (term148 A s x' t u x'') = (term148 A s x' t u x'').
Proof. exact (MK_COMB (@lem3222604 A s t x') (@lem3222560 A t u x'')). Qed.
Lemma lem3222606 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term148 A s x' t u x''.
Proof. exact (EQ_MP (@lem3222605 A s x' t u x'') (@lem3222472 A s x' t u x'' h1)). Qed.
Lemma lem3222607 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term120 A t u x''.
Proof. exact (proj2 (@lem3222606 A s x' t u x'' h1)). Qed.
Lemma lem3222608 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term120 A s t x'.
Proof. exact (proj1 (@lem3222606 A s x' t u x'' h1)). Qed.
Lemma lem3222609 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term67 A t u x''.
Proof. exact (proj2 (@lem3222607 A s x' t u x'' h1)). Qed.
Lemma lem3222610 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A t u.
Proof. exact (proj1 (@lem3222607 A s x' t u x'' h1)). Qed.
Lemma lem3222611 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term67 A s t x'.
Proof. exact (proj2 (@lem3222608 A s x' t u x'' h1)). Qed.
Lemma lem3222612 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A s t.
Proof. exact (proj1 (@lem3222608 A s x' t u x'' h1)). Qed.
Lemma lem3222613 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term87 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3222617 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term87 A t u x''.
Proof. exact (h1). Qed.
Lemma lem3222637 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term87 A t u x''.
Proof. exact (h1). Qed.
Lemma lem3222638 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term91 A t u x'') : term91 A t u x''.
Proof. exact (h1). Qed.
Lemma lem3222649 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : term87 A s u x.
Proof. exact (h1). Qed.
Lemma lem3222650 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term188 A s u) : term188 A s u.
Proof. exact (h1). Qed.
Lemma lem3222654 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term188 A s u) : term183 A s u.
Proof. exact (proj1 (@lem3222650 A s u h1)). Qed.
Lemma lem3222662 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term63 A t u x) = (term63 A t u x).
Proof. exact (eq_refl (term63 A t u x)). Qed.
Lemma lem3222663 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term64 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222662 A t u x)). Qed.
Lemma lem3222664 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222666 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3222664 A) (@lem3222663 A t u)). Qed.
Lemma lem3222667 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A t u.
Proof. exact (EQ_MP (@lem3222666 A t u) (@lem3222610 A s x' t u x'' h1)). Qed.
Lemma lem3222712 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term63 A t u x) = (term63 A t u x).
Proof. exact (eq_refl (term63 A t u x)). Qed.
Lemma lem3222713 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term64 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222712 A t u x)). Qed.
Lemma lem3222714 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222716 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3222714 A) (@lem3222713 A t u)). Qed.
Lemma lem3222717 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A t u.
Proof. exact (EQ_MP (@lem3222716 A t u) (@lem3222610 A s x' t u x'' h1)). Qed.
Lemma lem3222793 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term63 A s t x).
Proof. exact (eq_refl (term63 A s t x)). Qed.
Lemma lem3222794 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3222793 A s t x)). Qed.
Lemma lem3222795 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222797 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3222795 A) (@lem3222794 A s t)). Qed.
Lemma lem3222798 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A s t.
Proof. exact (EQ_MP (@lem3222797 A s t) (@lem3222612 A s x' t u x'' h1)). Qed.
Lemma lem3222843 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term63 A s t x).
Proof. exact (eq_refl (term63 A s t x)). Qed.
Lemma lem3222844 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3222843 A s t x)). Qed.
Lemma lem3222845 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222847 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3222845 A) (@lem3222844 A s t)). Qed.
Lemma lem3222848 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A s t.
Proof. exact (EQ_MP (@lem3222847 A s t) (@lem3222612 A s x' t u x'' h1)). Qed.
Lemma lem3222898 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term63 A t u x) = (term63 A t u x).
Proof. exact (eq_refl (term63 A t u x)). Qed.
Lemma lem3222899 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term64 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222898 A t u x)). Qed.
Lemma lem3222900 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222902 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3222900 A) (@lem3222899 A t u)). Qed.
Lemma lem3222903 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A t u.
Proof. exact (EQ_MP (@lem3222902 A t u) (@lem3222610 A s x' t u x'' h1)). Qed.
Lemma lem3222948 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term63 A t u x) = (term63 A t u x).
Proof. exact (eq_refl (term63 A t u x)). Qed.
Lemma lem3222949 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term64 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3222948 A t u x)). Qed.
Lemma lem3222950 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3222952 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3222950 A) (@lem3222949 A t u)). Qed.
Lemma lem3222953 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A t u.
Proof. exact (EQ_MP (@lem3222952 A t u) (@lem3222610 A s x' t u x'' h1)). Qed.
Lemma lem3223016 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term63 A t u x) = (term63 A t u x).
Proof. exact (eq_refl (term63 A t u x)). Qed.
Lemma lem3223017 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term64 A t u) = (term64 A t u).
Proof. exact (fun_ext (fun x : A => @lem3223016 A t u x)). Qed.
Lemma lem3223018 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3223020 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term65 A t u) = (term65 A t u).
Proof. exact (MK_COMB (@lem3223018 A) (@lem3223017 A t u)). Qed.
Lemma lem3223021 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A t u.
Proof. exact (EQ_MP (@lem3223020 A t u) (@lem3222610 A s x' t u x'' h1)). Qed.
Lemma lem3223029 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term63 A s t x).
Proof. exact (eq_refl (term63 A s t x)). Qed.
Lemma lem3223030 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3223029 A s t x)). Qed.
Lemma lem3223031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3223033 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3223031 A) (@lem3223030 A s t)). Qed.
Lemma lem3223034 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A s t.
Proof. exact (EQ_MP (@lem3223033 A s t) (@lem3222612 A s x' t u x'' h1)). Qed.
Lemma lem3223079 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term63 A s t x).
Proof. exact (eq_refl (term63 A s t x)). Qed.
Lemma lem3223080 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem3223079 A s t x)). Qed.
Lemma lem3223081 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3223083 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3223081 A) (@lem3223080 A s t)). Qed.
Lemma lem3223084 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term65 A s t.
Proof. exact (EQ_MP (@lem3223083 A s t) (@lem3222612 A s x' t u x'' h1)). Qed.
Lemma lem3223108 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term173 A s u x) = (term173 A s u x).
Proof. exact (eq_refl (term173 A s u x)). Qed.
Lemma lem3223109 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term171 A s u) = (term171 A s u).
Proof. exact (fun_ext (fun x : A => @lem3223108 A s u x)). Qed.
Lemma lem3223110 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3223112 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term183 A s u) = (term183 A s u).
Proof. exact (MK_COMB (@lem3223110 A) (@lem3223109 A s u)). Qed.
Lemma lem3223113 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term188 A s u) : term183 A s u.
Proof. exact (EQ_MP (@lem3223112 A s u) (@lem3222654 A s u h1)). Qed.
Lemma lem3223127 {A : Type'} (_33127 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term176 A t u _33127.
Proof. exact (@lem3222667 A s x' t u x'' h1 _33127). Qed.
Lemma lem3223128 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33127 : A) : (term176 A t u _33127) = (term63 A t u _33127).
Proof. exact (eq_refl (term176 A t u _33127)). Qed.
Lemma lem3223133 {A : Type'} (_33129 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term176 A t u _33129.
Proof. exact (@lem3222717 A s x' t u x'' h1 _33129). Qed.
Lemma lem3223134 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33129 : A) : (term176 A t u _33129) = (term63 A t u _33129).
Proof. exact (eq_refl (term176 A t u _33129)). Qed.
Lemma lem3223148 {A : Type'} (_33134 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term176 A s t _33134.
Proof. exact (@lem3222798 A s x' t u x'' h1 _33134). Qed.
Lemma lem3223149 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33134 : A) : (term176 A s t _33134) = (term63 A s t _33134).
Proof. exact (eq_refl (term176 A s t _33134)). Qed.
Lemma lem3223154 {A : Type'} (_33136 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term176 A s t _33136.
Proof. exact (@lem3222848 A s x' t u x'' h1 _33136). Qed.
Lemma lem3223155 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33136 : A) : (term176 A s t _33136) = (term63 A s t _33136).
Proof. exact (eq_refl (term176 A s t _33136)). Qed.
Lemma lem3223163 {A : Type'} (_33139 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term176 A t u _33139.
Proof. exact (@lem3222903 A s x' t u x'' h1 _33139). Qed.
Lemma lem3223164 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33139 : A) : (term176 A t u _33139) = (term63 A t u _33139).
Proof. exact (eq_refl (term176 A t u _33139)). Qed.
Lemma lem3223169 {A : Type'} (_33141 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term176 A t u _33141.
Proof. exact (@lem3222953 A s x' t u x'' h1 _33141). Qed.
Lemma lem3223170 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33141 : A) : (term176 A t u _33141) = (term63 A t u _33141).
Proof. exact (eq_refl (term176 A t u _33141)). Qed.
Lemma lem3223181 {A : Type'} (_33145 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term176 A t u _33145.
Proof. exact (@lem3223021 A s x' t u x'' h1 _33145). Qed.
Lemma lem3223182 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33145 : A) : (term176 A t u _33145) = (term63 A t u _33145).
Proof. exact (eq_refl (term176 A t u _33145)). Qed.
Lemma lem3223184 {A : Type'} (_33146 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term176 A s t _33146.
Proof. exact (@lem3223034 A s x' t u x'' h1 _33146). Qed.
Lemma lem3223185 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33146 : A) : (term176 A s t _33146) = (term63 A s t _33146).
Proof. exact (eq_refl (term176 A s t _33146)). Qed.
Lemma lem3223190 {A : Type'} (_33148 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term176 A s t _33148.
Proof. exact (@lem3223084 A s x' t u x'' h1 _33148). Qed.
Lemma lem3223191 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33148 : A) : (term176 A s t _33148) = (term63 A s t _33148).
Proof. exact (eq_refl (term176 A s t _33148)). Qed.
Lemma lem3223193 {A : Type'} (_33149 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term188 A s u) : term172 A s u _33149.
Proof. exact (@lem3223113 A s u h1 _33149). Qed.
Lemma lem3223194 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33149 : A) : (term172 A s u _33149) = (term173 A s u _33149).
Proof. exact (eq_refl (term172 A s u _33149)). Qed.
Lemma lem3223204 {A : Type'} (_33127 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term63 A t u _33127.
Proof. exact (EQ_MP (@lem3223128 A t u _33127) (@lem3223127 A _33127 s x' t u x'' h1)). Qed.
Lemma lem3223218 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term201 A u x''.
Proof. exact (proj2 (@lem3222617 A t u x'' h1)). Qed.
Lemma lem3223228 {A : Type'} (_33129 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term63 A t u _33129.
Proof. exact (EQ_MP (@lem3223134 A t u _33129) (@lem3223133 A _33129 s x' t u x'' h1)). Qed.
Lemma lem3223242 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term201 A u x''.
Proof. exact (proj2 (@lem3222617 A t u x'' h1)). Qed.
Lemma lem3223266 {A : Type'} (_33134 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term63 A s t _33134.
Proof. exact (EQ_MP (@lem3223149 A s t _33134) (@lem3223148 A _33134 s x' t u x'' h1)). Qed.
Lemma lem3223270 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term201 A t x'.
Proof. exact (proj2 (@lem3222613 A s t x' h1)). Qed.
Lemma lem3223290 {A : Type'} (_33136 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term63 A s t _33136.
Proof. exact (EQ_MP (@lem3223155 A s t _33136) (@lem3223154 A _33136 s x' t u x'' h1)). Qed.
Lemma lem3223294 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term201 A t x'.
Proof. exact (proj2 (@lem3222613 A s t x' h1)). Qed.
Lemma lem3223316 {A : Type'} (_33139 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term63 A t u _33139.
Proof. exact (EQ_MP (@lem3223164 A t u _33139) (@lem3223163 A _33139 s x' t u x'' h1)). Qed.
Lemma lem3223330 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term201 A u x''.
Proof. exact (proj2 (@lem3222637 A t u x'' h1)). Qed.
Lemma lem3223340 {A : Type'} (_33141 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term63 A t u _33141.
Proof. exact (EQ_MP (@lem3223170 A t u _33141) (@lem3223169 A _33141 s x' t u x'' h1)). Qed.
Lemma lem3223354 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term201 A u x''.
Proof. exact (proj2 (@lem3222637 A t u x'' h1)). Qed.
Lemma lem3223372 {A : Type'} (_33145 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term63 A t u _33145.
Proof. exact (EQ_MP (@lem3223182 A t u _33145) (@lem3223181 A _33145 s x' t u x'' h1)). Qed.
Lemma lem3223378 {A : Type'} (_33146 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term63 A s t _33146.
Proof. exact (EQ_MP (@lem3223185 A s t _33146) (@lem3223184 A _33146 s x' t u x'' h1)). Qed.
Lemma lem3223390 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : term201 A u x.
Proof. exact (proj2 (@lem3222649 A s u x h1)). Qed.
Lemma lem3223402 {A : Type'} (_33148 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term63 A s t _33148.
Proof. exact (EQ_MP (@lem3223191 A s t _33148) (@lem3223190 A _33148 s x' t u x'' h1)). Qed.
Lemma lem3223408 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term91 A t u x'') : term201 A t x''.
Proof. exact (proj1 (@lem3222638 A t u x'' h1)). Qed.
Lemma lem3223416 {A : Type'} (_33149 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term188 A s u) : term173 A s u _33149.
Proof. exact (EQ_MP (@lem3223194 A s u _33149) (@lem3223193 A _33149 s u h1)). Qed.
Lemma lem3223424 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : t x''.
Proof. exact (proj1 (@lem3222617 A t u x'' h1)). Qed.
Lemma lem3223425 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term202 A t x''.
Proof. exact (fun h0 : term201 A t x'' => @lem3223424 A t u x'' h1). Qed.
Lemma lem3223427 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223428 {A : Type'} (t : A -> Prop) (x'' : A) : (term202 A t x'') = (t x'').
Proof. exact (@lem3223427 (t x'')). Qed.
Lemma lem3223429 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : t x''.
Proof. exact (EQ_MP (@lem3223428 A t x'') (@lem3223425 A t u x'' h1)). Qed.
Lemma lem3223435 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3223436 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33127 : A) : (term63 A t u _33127) = (term173 A u t _33127).
Proof. exact (@lem3223435 (u _33127) (term201 A t _33127)). Qed.
Lemma lem3223442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3223443 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33127 : A) : (term204 A t u _33127) = (term205 A u t _33127).
Proof. exact (MK_COMB (@lem3223442) (@lem3223436 A u t _33127)). Qed.
Lemma lem3223449 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33127 : A) : (term173 A u t _33127) = (term173 A u t _33127).
Proof. exact (eq_refl (term173 A u t _33127)). Qed.
Lemma lem3223450 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33127 : A) : ((term63 A t u _33127) = (term173 A u t _33127)) = ((term173 A u t _33127) = (term173 A u t _33127)).
Proof. exact (MK_COMB (@lem3223443 A u t _33127) (@lem3223449 A u t _33127)). Qed.
Lemma lem3223452 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3223453 (x : Prop) : (x = x) = True.
Proof. exact (@lem3223452 Prop x). Qed.
Lemma lem3223454 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33127 : A) : ((term173 A u t _33127) = (term173 A u t _33127)) = True.
Proof. exact (@lem3223453 (term173 A u t _33127)). Qed.
Lemma lem3223455 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33127 : A) : ((term63 A t u _33127) = (term173 A u t _33127)) = True.
Proof. exact (TRANS (@lem3223450 A u t _33127) (@lem3223454 A u t _33127)). Qed.
Lemma lem3223456 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33127 : A) : True = ((term63 A t u _33127) = (term173 A u t _33127)).
Proof. exact (SYM (@lem3223455 A u t _33127)). Qed.
Lemma lem3223457 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33127 : A) : (term63 A t u _33127) = (term173 A u t _33127).
Proof. exact (EQ_MP (@lem3223456 A u t _33127) (@lem0)). Qed.
Lemma lem3223458 {A : Type'} (_33127 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term173 A u t _33127.
Proof. exact (EQ_MP (@lem3223457 A u t _33127) (@lem3223204 A _33127 s x' t u x'' h1)). Qed.
Lemma lem3223460 (b : Prop) (a : Prop) : (a \/ b) = (term206 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3223461 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33127 : A) : (term173 A u t _33127) = (term207 A t u _33127).
Proof. exact (@lem3223460 (term201 A t _33127) (u _33127)). Qed.
Lemma lem3223463 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3223464 {A : Type'} (t : A -> Prop) (_33127 : A) : (term208 A t _33127) = (t _33127).
Proof. exact (@lem3223463 (t _33127)). Qed.
Lemma lem3223465 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3223466 {A : Type'} (t : A -> Prop) (_33127 : A) : (term209 A t _33127) = (term29 A t _33127).
Proof. exact (MK_COMB (@lem3223465) (@lem3223464 A t _33127)). Qed.
Lemma lem3223467 {A : Type'} (u : A -> Prop) (_33127 : A) : (u _33127) = (u _33127).
Proof. exact (eq_refl (u _33127)). Qed.
Lemma lem3223468 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33127 : A) : (term207 A t u _33127) = (term31 A t u _33127).
Proof. exact (MK_COMB (@lem3223466 A t _33127) (@lem3223467 A u _33127)). Qed.
Lemma lem3223469 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33127 : A) : (term173 A u t _33127) = (term31 A t u _33127).
Proof. exact (TRANS (@lem3223461 A t u _33127) (@lem3223468 A t u _33127)). Qed.
Lemma lem3223472 {A : Type'} (_33127 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u _33127.
Proof. exact (EQ_MP (@lem3223469 A t u _33127) (@lem3223458 A _33127 s x' t u x'' h1)). Qed.
Lemma lem3223473 {A : Type'} (_33127 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u _33127.
Proof. exact (@lem3223472 A _33127 s x' t u x'' h1). Qed.
Lemma lem3223474 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u x''.
Proof. exact (@lem3223473 A x'' s x' t u x'' h1). Qed.
Lemma lem3223477 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : u x''.
Proof. exact (@lem3223474 A s x' t u x'' h2 (@lem3223429 A t u x'' h1)). Qed.
Lemma lem3223478 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : term202 A u x''.
Proof. exact (fun h0 : term201 A u x'' => @lem3223477 A s x' t u x'' h1 h2). Qed.
Lemma lem3223480 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223481 {A : Type'} (u : A -> Prop) (x'' : A) : (term202 A u x'') = (u x'').
Proof. exact (@lem3223480 (u x'')). Qed.
Lemma lem3223482 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : u x''.
Proof. exact (EQ_MP (@lem3223481 A u x'') (@lem3223478 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223485 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3223487 {A : Type'} (u : A -> Prop) (x'' : A) : (term201 A u x'') = (term210 A u x'').
Proof. exact (@lem3223485 (u x'')). Qed.
Lemma lem3223490 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term210 A u x''.
Proof. exact (EQ_MP (@lem3223487 A u x'') (@lem3223218 A t u x'' h1)). Qed.
Lemma lem3223493 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : False.
Proof. exact (@lem3223490 A t u x'' h1 (@lem3223482 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223494 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : term211.
Proof. exact (fun h0 : ~ False => @lem3223493 A s x' t u x'' h1 h2). Qed.
Lemma lem3223496 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223497 : term211 = False.
Proof. exact (@lem3223496 False). Qed.
Lemma lem3223498 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : False.
Proof. exact (EQ_MP (@lem3223497) (@lem3223494 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223500 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : t x''.
Proof. exact (proj1 (@lem3222617 A t u x'' h1)). Qed.
Lemma lem3223501 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term202 A t x''.
Proof. exact (fun h0 : term201 A t x'' => @lem3223500 A t u x'' h1). Qed.
Lemma lem3223503 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223504 {A : Type'} (t : A -> Prop) (x'' : A) : (term202 A t x'') = (t x'').
Proof. exact (@lem3223503 (t x'')). Qed.
Lemma lem3223505 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : t x''.
Proof. exact (EQ_MP (@lem3223504 A t x'') (@lem3223501 A t u x'' h1)). Qed.
Lemma lem3223511 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3223512 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33129 : A) : (term63 A t u _33129) = (term173 A u t _33129).
Proof. exact (@lem3223511 (u _33129) (term201 A t _33129)). Qed.
Lemma lem3223518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3223519 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33129 : A) : (term204 A t u _33129) = (term205 A u t _33129).
Proof. exact (MK_COMB (@lem3223518) (@lem3223512 A u t _33129)). Qed.
Lemma lem3223525 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33129 : A) : (term173 A u t _33129) = (term173 A u t _33129).
Proof. exact (eq_refl (term173 A u t _33129)). Qed.
Lemma lem3223526 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33129 : A) : ((term63 A t u _33129) = (term173 A u t _33129)) = ((term173 A u t _33129) = (term173 A u t _33129)).
Proof. exact (MK_COMB (@lem3223519 A u t _33129) (@lem3223525 A u t _33129)). Qed.
Lemma lem3223528 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3223529 (x : Prop) : (x = x) = True.
Proof. exact (@lem3223528 Prop x). Qed.
Lemma lem3223530 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33129 : A) : ((term173 A u t _33129) = (term173 A u t _33129)) = True.
Proof. exact (@lem3223529 (term173 A u t _33129)). Qed.
Lemma lem3223531 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33129 : A) : ((term63 A t u _33129) = (term173 A u t _33129)) = True.
Proof. exact (TRANS (@lem3223526 A u t _33129) (@lem3223530 A u t _33129)). Qed.
Lemma lem3223532 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33129 : A) : True = ((term63 A t u _33129) = (term173 A u t _33129)).
Proof. exact (SYM (@lem3223531 A u t _33129)). Qed.
Lemma lem3223533 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33129 : A) : (term63 A t u _33129) = (term173 A u t _33129).
Proof. exact (EQ_MP (@lem3223532 A u t _33129) (@lem0)). Qed.
Lemma lem3223534 {A : Type'} (_33129 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term173 A u t _33129.
Proof. exact (EQ_MP (@lem3223533 A u t _33129) (@lem3223228 A _33129 s x' t u x'' h1)). Qed.
Lemma lem3223536 (b : Prop) (a : Prop) : (a \/ b) = (term206 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3223537 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33129 : A) : (term173 A u t _33129) = (term207 A t u _33129).
Proof. exact (@lem3223536 (term201 A t _33129) (u _33129)). Qed.
Lemma lem3223539 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3223540 {A : Type'} (t : A -> Prop) (_33129 : A) : (term208 A t _33129) = (t _33129).
Proof. exact (@lem3223539 (t _33129)). Qed.
Lemma lem3223541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3223542 {A : Type'} (t : A -> Prop) (_33129 : A) : (term209 A t _33129) = (term29 A t _33129).
Proof. exact (MK_COMB (@lem3223541) (@lem3223540 A t _33129)). Qed.
Lemma lem3223543 {A : Type'} (u : A -> Prop) (_33129 : A) : (u _33129) = (u _33129).
Proof. exact (eq_refl (u _33129)). Qed.
Lemma lem3223544 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33129 : A) : (term207 A t u _33129) = (term31 A t u _33129).
Proof. exact (MK_COMB (@lem3223542 A t _33129) (@lem3223543 A u _33129)). Qed.
Lemma lem3223545 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33129 : A) : (term173 A u t _33129) = (term31 A t u _33129).
Proof. exact (TRANS (@lem3223537 A t u _33129) (@lem3223544 A t u _33129)). Qed.
Lemma lem3223548 {A : Type'} (_33129 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u _33129.
Proof. exact (EQ_MP (@lem3223545 A t u _33129) (@lem3223534 A _33129 s x' t u x'' h1)). Qed.
Lemma lem3223549 {A : Type'} (_33129 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u _33129.
Proof. exact (@lem3223548 A _33129 s x' t u x'' h1). Qed.
Lemma lem3223550 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u x''.
Proof. exact (@lem3223549 A x'' s x' t u x'' h1). Qed.
Lemma lem3223553 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : u x''.
Proof. exact (@lem3223550 A s x' t u x'' h2 (@lem3223505 A t u x'' h1)). Qed.
Lemma lem3223554 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : term202 A u x''.
Proof. exact (fun h0 : term201 A u x'' => @lem3223553 A s x' t u x'' h1 h2). Qed.
Lemma lem3223556 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223557 {A : Type'} (u : A -> Prop) (x'' : A) : (term202 A u x'') = (u x'').
Proof. exact (@lem3223556 (u x'')). Qed.
Lemma lem3223558 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : u x''.
Proof. exact (EQ_MP (@lem3223557 A u x'') (@lem3223554 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223561 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3223563 {A : Type'} (u : A -> Prop) (x'' : A) : (term201 A u x'') = (term210 A u x'').
Proof. exact (@lem3223561 (u x'')). Qed.
Lemma lem3223566 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term210 A u x''.
Proof. exact (EQ_MP (@lem3223563 A u x'') (@lem3223242 A t u x'' h1)). Qed.
Lemma lem3223569 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : False.
Proof. exact (@lem3223566 A t u x'' h1 (@lem3223558 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223570 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : term211.
Proof. exact (fun h0 : ~ False => @lem3223569 A s x' t u x'' h1 h2). Qed.
Lemma lem3223572 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223573 : term211 = False.
Proof. exact (@lem3223572 False). Qed.
Lemma lem3223574 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : False.
Proof. exact (EQ_MP (@lem3223573) (@lem3223570 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223576 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : s x'.
Proof. exact (proj1 (@lem3222613 A s t x' h1)). Qed.
Lemma lem3223577 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term202 A s x'.
Proof. exact (fun h0 : term201 A s x' => @lem3223576 A s t x' h1). Qed.
Lemma lem3223579 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223580 {A : Type'} (s : A -> Prop) (x' : A) : (term202 A s x') = (s x').
Proof. exact (@lem3223579 (s x')). Qed.
Lemma lem3223581 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3223580 A s x') (@lem3223577 A s t x' h1)). Qed.
Lemma lem3223587 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3223588 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33134 : A) : (term63 A s t _33134) = (term173 A t s _33134).
Proof. exact (@lem3223587 (t _33134) (term201 A s _33134)). Qed.
Lemma lem3223594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3223595 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33134 : A) : (term204 A s t _33134) = (term205 A t s _33134).
Proof. exact (MK_COMB (@lem3223594) (@lem3223588 A t s _33134)). Qed.
Lemma lem3223601 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33134 : A) : (term173 A t s _33134) = (term173 A t s _33134).
Proof. exact (eq_refl (term173 A t s _33134)). Qed.
Lemma lem3223602 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33134 : A) : ((term63 A s t _33134) = (term173 A t s _33134)) = ((term173 A t s _33134) = (term173 A t s _33134)).
Proof. exact (MK_COMB (@lem3223595 A t s _33134) (@lem3223601 A t s _33134)). Qed.
Lemma lem3223604 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3223605 (x : Prop) : (x = x) = True.
Proof. exact (@lem3223604 Prop x). Qed.
Lemma lem3223606 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33134 : A) : ((term173 A t s _33134) = (term173 A t s _33134)) = True.
Proof. exact (@lem3223605 (term173 A t s _33134)). Qed.
Lemma lem3223607 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33134 : A) : ((term63 A s t _33134) = (term173 A t s _33134)) = True.
Proof. exact (TRANS (@lem3223602 A t s _33134) (@lem3223606 A t s _33134)). Qed.
Lemma lem3223608 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33134 : A) : True = ((term63 A s t _33134) = (term173 A t s _33134)).
Proof. exact (SYM (@lem3223607 A t s _33134)). Qed.
Lemma lem3223609 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33134 : A) : (term63 A s t _33134) = (term173 A t s _33134).
Proof. exact (EQ_MP (@lem3223608 A t s _33134) (@lem0)). Qed.
Lemma lem3223610 {A : Type'} (_33134 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term173 A t s _33134.
Proof. exact (EQ_MP (@lem3223609 A t s _33134) (@lem3223266 A _33134 s x' t u x'' h1)). Qed.
Lemma lem3223612 (b : Prop) (a : Prop) : (a \/ b) = (term206 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3223613 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33134 : A) : (term173 A t s _33134) = (term207 A s t _33134).
Proof. exact (@lem3223612 (term201 A s _33134) (t _33134)). Qed.
Lemma lem3223615 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3223616 {A : Type'} (s : A -> Prop) (_33134 : A) : (term208 A s _33134) = (s _33134).
Proof. exact (@lem3223615 (s _33134)). Qed.
Lemma lem3223617 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3223618 {A : Type'} (s : A -> Prop) (_33134 : A) : (term209 A s _33134) = (term29 A s _33134).
Proof. exact (MK_COMB (@lem3223617) (@lem3223616 A s _33134)). Qed.
Lemma lem3223619 {A : Type'} (t : A -> Prop) (_33134 : A) : (t _33134) = (t _33134).
Proof. exact (eq_refl (t _33134)). Qed.
Lemma lem3223620 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33134 : A) : (term207 A s t _33134) = (term31 A s t _33134).
Proof. exact (MK_COMB (@lem3223618 A s _33134) (@lem3223619 A t _33134)). Qed.
Lemma lem3223621 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33134 : A) : (term173 A t s _33134) = (term31 A s t _33134).
Proof. exact (TRANS (@lem3223613 A s t _33134) (@lem3223620 A s t _33134)). Qed.
Lemma lem3223624 {A : Type'} (_33134 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t _33134.
Proof. exact (EQ_MP (@lem3223621 A s t _33134) (@lem3223610 A _33134 s x' t u x'' h1)). Qed.
Lemma lem3223625 {A : Type'} (_33134 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t _33134.
Proof. exact (@lem3223624 A _33134 s x' t u x'' h1). Qed.
Lemma lem3223626 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t x'.
Proof. exact (@lem3223625 A x' s x' t u x'' h1). Qed.
Lemma lem3223629 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : t x'.
Proof. exact (@lem3223626 A s x' t u x'' h2 (@lem3223581 A s t x' h1)). Qed.
Lemma lem3223630 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : term202 A t x'.
Proof. exact (fun h0 : term201 A t x' => @lem3223629 A s x' t u x'' h1 h2). Qed.
Lemma lem3223632 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223633 {A : Type'} (t : A -> Prop) (x' : A) : (term202 A t x') = (t x').
Proof. exact (@lem3223632 (t x')). Qed.
Lemma lem3223634 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : t x'.
Proof. exact (EQ_MP (@lem3223633 A t x') (@lem3223630 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223637 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3223639 {A : Type'} (t : A -> Prop) (x' : A) : (term201 A t x') = (term210 A t x').
Proof. exact (@lem3223637 (t x')). Qed.
Lemma lem3223642 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term210 A t x'.
Proof. exact (EQ_MP (@lem3223639 A t x') (@lem3223270 A s t x' h1)). Qed.
Lemma lem3223645 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : False.
Proof. exact (@lem3223642 A s t x' h1 (@lem3223634 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223646 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : term211.
Proof. exact (fun h0 : ~ False => @lem3223645 A s x' t u x'' h1 h2). Qed.
Lemma lem3223648 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223649 : term211 = False.
Proof. exact (@lem3223648 False). Qed.
Lemma lem3223650 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : False.
Proof. exact (EQ_MP (@lem3223649) (@lem3223646 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223652 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : s x'.
Proof. exact (proj1 (@lem3222613 A s t x' h1)). Qed.
Lemma lem3223653 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term202 A s x'.
Proof. exact (fun h0 : term201 A s x' => @lem3223652 A s t x' h1). Qed.
Lemma lem3223655 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223656 {A : Type'} (s : A -> Prop) (x' : A) : (term202 A s x') = (s x').
Proof. exact (@lem3223655 (s x')). Qed.
Lemma lem3223657 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3223656 A s x') (@lem3223653 A s t x' h1)). Qed.
Lemma lem3223663 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3223664 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33136 : A) : (term63 A s t _33136) = (term173 A t s _33136).
Proof. exact (@lem3223663 (t _33136) (term201 A s _33136)). Qed.
Lemma lem3223670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3223671 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33136 : A) : (term204 A s t _33136) = (term205 A t s _33136).
Proof. exact (MK_COMB (@lem3223670) (@lem3223664 A t s _33136)). Qed.
Lemma lem3223677 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33136 : A) : (term173 A t s _33136) = (term173 A t s _33136).
Proof. exact (eq_refl (term173 A t s _33136)). Qed.
Lemma lem3223678 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33136 : A) : ((term63 A s t _33136) = (term173 A t s _33136)) = ((term173 A t s _33136) = (term173 A t s _33136)).
Proof. exact (MK_COMB (@lem3223671 A t s _33136) (@lem3223677 A t s _33136)). Qed.
Lemma lem3223680 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3223681 (x : Prop) : (x = x) = True.
Proof. exact (@lem3223680 Prop x). Qed.
Lemma lem3223682 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33136 : A) : ((term173 A t s _33136) = (term173 A t s _33136)) = True.
Proof. exact (@lem3223681 (term173 A t s _33136)). Qed.
Lemma lem3223683 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33136 : A) : ((term63 A s t _33136) = (term173 A t s _33136)) = True.
Proof. exact (TRANS (@lem3223678 A t s _33136) (@lem3223682 A t s _33136)). Qed.
Lemma lem3223684 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33136 : A) : True = ((term63 A s t _33136) = (term173 A t s _33136)).
Proof. exact (SYM (@lem3223683 A t s _33136)). Qed.
Lemma lem3223685 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33136 : A) : (term63 A s t _33136) = (term173 A t s _33136).
Proof. exact (EQ_MP (@lem3223684 A t s _33136) (@lem0)). Qed.
Lemma lem3223686 {A : Type'} (_33136 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term173 A t s _33136.
Proof. exact (EQ_MP (@lem3223685 A t s _33136) (@lem3223290 A _33136 s x' t u x'' h1)). Qed.
Lemma lem3223688 (b : Prop) (a : Prop) : (a \/ b) = (term206 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3223689 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33136 : A) : (term173 A t s _33136) = (term207 A s t _33136).
Proof. exact (@lem3223688 (term201 A s _33136) (t _33136)). Qed.
Lemma lem3223691 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3223692 {A : Type'} (s : A -> Prop) (_33136 : A) : (term208 A s _33136) = (s _33136).
Proof. exact (@lem3223691 (s _33136)). Qed.
Lemma lem3223693 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3223694 {A : Type'} (s : A -> Prop) (_33136 : A) : (term209 A s _33136) = (term29 A s _33136).
Proof. exact (MK_COMB (@lem3223693) (@lem3223692 A s _33136)). Qed.
Lemma lem3223695 {A : Type'} (t : A -> Prop) (_33136 : A) : (t _33136) = (t _33136).
Proof. exact (eq_refl (t _33136)). Qed.
Lemma lem3223696 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33136 : A) : (term207 A s t _33136) = (term31 A s t _33136).
Proof. exact (MK_COMB (@lem3223694 A s _33136) (@lem3223695 A t _33136)). Qed.
Lemma lem3223697 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33136 : A) : (term173 A t s _33136) = (term31 A s t _33136).
Proof. exact (TRANS (@lem3223689 A s t _33136) (@lem3223696 A s t _33136)). Qed.
Lemma lem3223700 {A : Type'} (_33136 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t _33136.
Proof. exact (EQ_MP (@lem3223697 A s t _33136) (@lem3223686 A _33136 s x' t u x'' h1)). Qed.
Lemma lem3223701 {A : Type'} (_33136 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t _33136.
Proof. exact (@lem3223700 A _33136 s x' t u x'' h1). Qed.
Lemma lem3223702 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t x'.
Proof. exact (@lem3223701 A x' s x' t u x'' h1). Qed.
Lemma lem3223705 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : t x'.
Proof. exact (@lem3223702 A s x' t u x'' h2 (@lem3223657 A s t x' h1)). Qed.
Lemma lem3223706 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : term202 A t x'.
Proof. exact (fun h0 : term201 A t x' => @lem3223705 A s x' t u x'' h1 h2). Qed.
Lemma lem3223708 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223709 {A : Type'} (t : A -> Prop) (x' : A) : (term202 A t x') = (t x').
Proof. exact (@lem3223708 (t x')). Qed.
Lemma lem3223710 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : t x'.
Proof. exact (EQ_MP (@lem3223709 A t x') (@lem3223706 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223713 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3223715 {A : Type'} (t : A -> Prop) (x' : A) : (term201 A t x') = (term210 A t x').
Proof. exact (@lem3223713 (t x')). Qed.
Lemma lem3223718 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term87 A s t x') : term210 A t x'.
Proof. exact (EQ_MP (@lem3223715 A t x') (@lem3223294 A s t x' h1)). Qed.
Lemma lem3223721 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : False.
Proof. exact (@lem3223718 A s t x' h1 (@lem3223710 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223722 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : term211.
Proof. exact (fun h0 : ~ False => @lem3223721 A s x' t u x'' h1 h2). Qed.
Lemma lem3223724 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223725 : term211 = False.
Proof. exact (@lem3223724 False). Qed.
Lemma lem3223726 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') : False.
Proof. exact (EQ_MP (@lem3223725) (@lem3223722 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223728 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : t x''.
Proof. exact (proj1 (@lem3222637 A t u x'' h1)). Qed.
Lemma lem3223729 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term202 A t x''.
Proof. exact (fun h0 : term201 A t x'' => @lem3223728 A t u x'' h1). Qed.
Lemma lem3223731 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223732 {A : Type'} (t : A -> Prop) (x'' : A) : (term202 A t x'') = (t x'').
Proof. exact (@lem3223731 (t x'')). Qed.
Lemma lem3223733 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : t x''.
Proof. exact (EQ_MP (@lem3223732 A t x'') (@lem3223729 A t u x'' h1)). Qed.
Lemma lem3223739 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3223740 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33139 : A) : (term63 A t u _33139) = (term173 A u t _33139).
Proof. exact (@lem3223739 (u _33139) (term201 A t _33139)). Qed.
Lemma lem3223746 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3223747 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33139 : A) : (term204 A t u _33139) = (term205 A u t _33139).
Proof. exact (MK_COMB (@lem3223746) (@lem3223740 A u t _33139)). Qed.
Lemma lem3223753 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33139 : A) : (term173 A u t _33139) = (term173 A u t _33139).
Proof. exact (eq_refl (term173 A u t _33139)). Qed.
Lemma lem3223754 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33139 : A) : ((term63 A t u _33139) = (term173 A u t _33139)) = ((term173 A u t _33139) = (term173 A u t _33139)).
Proof. exact (MK_COMB (@lem3223747 A u t _33139) (@lem3223753 A u t _33139)). Qed.
Lemma lem3223756 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3223757 (x : Prop) : (x = x) = True.
Proof. exact (@lem3223756 Prop x). Qed.
Lemma lem3223758 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33139 : A) : ((term173 A u t _33139) = (term173 A u t _33139)) = True.
Proof. exact (@lem3223757 (term173 A u t _33139)). Qed.
Lemma lem3223759 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33139 : A) : ((term63 A t u _33139) = (term173 A u t _33139)) = True.
Proof. exact (TRANS (@lem3223754 A u t _33139) (@lem3223758 A u t _33139)). Qed.
Lemma lem3223760 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33139 : A) : True = ((term63 A t u _33139) = (term173 A u t _33139)).
Proof. exact (SYM (@lem3223759 A u t _33139)). Qed.
Lemma lem3223761 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33139 : A) : (term63 A t u _33139) = (term173 A u t _33139).
Proof. exact (EQ_MP (@lem3223760 A u t _33139) (@lem0)). Qed.
Lemma lem3223762 {A : Type'} (_33139 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term173 A u t _33139.
Proof. exact (EQ_MP (@lem3223761 A u t _33139) (@lem3223316 A _33139 s x' t u x'' h1)). Qed.
Lemma lem3223764 (b : Prop) (a : Prop) : (a \/ b) = (term206 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3223765 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33139 : A) : (term173 A u t _33139) = (term207 A t u _33139).
Proof. exact (@lem3223764 (term201 A t _33139) (u _33139)). Qed.
Lemma lem3223767 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3223768 {A : Type'} (t : A -> Prop) (_33139 : A) : (term208 A t _33139) = (t _33139).
Proof. exact (@lem3223767 (t _33139)). Qed.
Lemma lem3223769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3223770 {A : Type'} (t : A -> Prop) (_33139 : A) : (term209 A t _33139) = (term29 A t _33139).
Proof. exact (MK_COMB (@lem3223769) (@lem3223768 A t _33139)). Qed.
Lemma lem3223771 {A : Type'} (u : A -> Prop) (_33139 : A) : (u _33139) = (u _33139).
Proof. exact (eq_refl (u _33139)). Qed.
Lemma lem3223772 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33139 : A) : (term207 A t u _33139) = (term31 A t u _33139).
Proof. exact (MK_COMB (@lem3223770 A t _33139) (@lem3223771 A u _33139)). Qed.
Lemma lem3223773 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33139 : A) : (term173 A u t _33139) = (term31 A t u _33139).
Proof. exact (TRANS (@lem3223765 A t u _33139) (@lem3223772 A t u _33139)). Qed.
Lemma lem3223776 {A : Type'} (_33139 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u _33139.
Proof. exact (EQ_MP (@lem3223773 A t u _33139) (@lem3223762 A _33139 s x' t u x'' h1)). Qed.
Lemma lem3223777 {A : Type'} (_33139 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u _33139.
Proof. exact (@lem3223776 A _33139 s x' t u x'' h1). Qed.
Lemma lem3223778 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u x''.
Proof. exact (@lem3223777 A x'' s x' t u x'' h1). Qed.
Lemma lem3223781 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : u x''.
Proof. exact (@lem3223778 A s x' t u x'' h2 (@lem3223733 A t u x'' h1)). Qed.
Lemma lem3223782 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : term202 A u x''.
Proof. exact (fun h0 : term201 A u x'' => @lem3223781 A s x' t u x'' h1 h2). Qed.
Lemma lem3223784 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223785 {A : Type'} (u : A -> Prop) (x'' : A) : (term202 A u x'') = (u x'').
Proof. exact (@lem3223784 (u x'')). Qed.
Lemma lem3223786 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : u x''.
Proof. exact (EQ_MP (@lem3223785 A u x'') (@lem3223782 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223789 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3223791 {A : Type'} (u : A -> Prop) (x'' : A) : (term201 A u x'') = (term210 A u x'').
Proof. exact (@lem3223789 (u x'')). Qed.
Lemma lem3223794 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term210 A u x''.
Proof. exact (EQ_MP (@lem3223791 A u x'') (@lem3223330 A t u x'' h1)). Qed.
Lemma lem3223797 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : False.
Proof. exact (@lem3223794 A t u x'' h1 (@lem3223786 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223798 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : term211.
Proof. exact (fun h0 : ~ False => @lem3223797 A s x' t u x'' h1 h2). Qed.
Lemma lem3223800 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223801 : term211 = False.
Proof. exact (@lem3223800 False). Qed.
Lemma lem3223802 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : False.
Proof. exact (EQ_MP (@lem3223801) (@lem3223798 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223804 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : t x''.
Proof. exact (proj1 (@lem3222637 A t u x'' h1)). Qed.
Lemma lem3223805 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term202 A t x''.
Proof. exact (fun h0 : term201 A t x'' => @lem3223804 A t u x'' h1). Qed.
Lemma lem3223807 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223808 {A : Type'} (t : A -> Prop) (x'' : A) : (term202 A t x'') = (t x'').
Proof. exact (@lem3223807 (t x'')). Qed.
Lemma lem3223809 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : t x''.
Proof. exact (EQ_MP (@lem3223808 A t x'') (@lem3223805 A t u x'' h1)). Qed.
Lemma lem3223815 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3223816 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33141 : A) : (term63 A t u _33141) = (term173 A u t _33141).
Proof. exact (@lem3223815 (u _33141) (term201 A t _33141)). Qed.
Lemma lem3223822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3223823 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33141 : A) : (term204 A t u _33141) = (term205 A u t _33141).
Proof. exact (MK_COMB (@lem3223822) (@lem3223816 A u t _33141)). Qed.
Lemma lem3223829 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33141 : A) : (term173 A u t _33141) = (term173 A u t _33141).
Proof. exact (eq_refl (term173 A u t _33141)). Qed.
Lemma lem3223830 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33141 : A) : ((term63 A t u _33141) = (term173 A u t _33141)) = ((term173 A u t _33141) = (term173 A u t _33141)).
Proof. exact (MK_COMB (@lem3223823 A u t _33141) (@lem3223829 A u t _33141)). Qed.
Lemma lem3223832 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3223833 (x : Prop) : (x = x) = True.
Proof. exact (@lem3223832 Prop x). Qed.
Lemma lem3223834 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33141 : A) : ((term173 A u t _33141) = (term173 A u t _33141)) = True.
Proof. exact (@lem3223833 (term173 A u t _33141)). Qed.
Lemma lem3223835 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33141 : A) : ((term63 A t u _33141) = (term173 A u t _33141)) = True.
Proof. exact (TRANS (@lem3223830 A u t _33141) (@lem3223834 A u t _33141)). Qed.
Lemma lem3223836 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33141 : A) : True = ((term63 A t u _33141) = (term173 A u t _33141)).
Proof. exact (SYM (@lem3223835 A u t _33141)). Qed.
Lemma lem3223837 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33141 : A) : (term63 A t u _33141) = (term173 A u t _33141).
Proof. exact (EQ_MP (@lem3223836 A u t _33141) (@lem0)). Qed.
Lemma lem3223838 {A : Type'} (_33141 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term173 A u t _33141.
Proof. exact (EQ_MP (@lem3223837 A u t _33141) (@lem3223340 A _33141 s x' t u x'' h1)). Qed.
Lemma lem3223840 (b : Prop) (a : Prop) : (a \/ b) = (term206 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3223841 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33141 : A) : (term173 A u t _33141) = (term207 A t u _33141).
Proof. exact (@lem3223840 (term201 A t _33141) (u _33141)). Qed.
Lemma lem3223843 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3223844 {A : Type'} (t : A -> Prop) (_33141 : A) : (term208 A t _33141) = (t _33141).
Proof. exact (@lem3223843 (t _33141)). Qed.
Lemma lem3223845 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3223846 {A : Type'} (t : A -> Prop) (_33141 : A) : (term209 A t _33141) = (term29 A t _33141).
Proof. exact (MK_COMB (@lem3223845) (@lem3223844 A t _33141)). Qed.
Lemma lem3223847 {A : Type'} (u : A -> Prop) (_33141 : A) : (u _33141) = (u _33141).
Proof. exact (eq_refl (u _33141)). Qed.
Lemma lem3223848 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33141 : A) : (term207 A t u _33141) = (term31 A t u _33141).
Proof. exact (MK_COMB (@lem3223846 A t _33141) (@lem3223847 A u _33141)). Qed.
Lemma lem3223849 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33141 : A) : (term173 A u t _33141) = (term31 A t u _33141).
Proof. exact (TRANS (@lem3223841 A t u _33141) (@lem3223848 A t u _33141)). Qed.
Lemma lem3223852 {A : Type'} (_33141 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u _33141.
Proof. exact (EQ_MP (@lem3223849 A t u _33141) (@lem3223838 A _33141 s x' t u x'' h1)). Qed.
Lemma lem3223853 {A : Type'} (_33141 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u _33141.
Proof. exact (@lem3223852 A _33141 s x' t u x'' h1). Qed.
Lemma lem3223854 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u x''.
Proof. exact (@lem3223853 A x'' s x' t u x'' h1). Qed.
Lemma lem3223857 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : u x''.
Proof. exact (@lem3223854 A s x' t u x'' h2 (@lem3223809 A t u x'' h1)). Qed.
Lemma lem3223858 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : term202 A u x''.
Proof. exact (fun h0 : term201 A u x'' => @lem3223857 A s x' t u x'' h1 h2). Qed.
Lemma lem3223860 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223861 {A : Type'} (u : A -> Prop) (x'' : A) : (term202 A u x'') = (u x'').
Proof. exact (@lem3223860 (u x'')). Qed.
Lemma lem3223862 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : u x''.
Proof. exact (EQ_MP (@lem3223861 A u x'') (@lem3223858 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223865 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3223867 {A : Type'} (u : A -> Prop) (x'' : A) : (term201 A u x'') = (term210 A u x'').
Proof. exact (@lem3223865 (u x'')). Qed.
Lemma lem3223870 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') : term210 A u x''.
Proof. exact (EQ_MP (@lem3223867 A u x'') (@lem3223354 A t u x'' h1)). Qed.
Lemma lem3223873 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : False.
Proof. exact (@lem3223870 A t u x'' h1 (@lem3223862 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223874 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : term211.
Proof. exact (fun h0 : ~ False => @lem3223873 A s x' t u x'' h1 h2). Qed.
Lemma lem3223876 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223877 : term211 = False.
Proof. exact (@lem3223876 False). Qed.
Lemma lem3223878 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') : False.
Proof. exact (EQ_MP (@lem3223877) (@lem3223874 A s x' t u x'' h1 h2)). Qed.
Lemma lem3223880 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : s x.
Proof. exact (proj1 (@lem3222649 A s u x h1)). Qed.
Lemma lem3223881 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : term202 A s x.
Proof. exact (fun h0 : term201 A s x => @lem3223880 A s u x h1). Qed.
Lemma lem3223883 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223884 {A : Type'} (s : A -> Prop) (x : A) : (term202 A s x) = (s x).
Proof. exact (@lem3223883 (s x)). Qed.
Lemma lem3223885 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : s x.
Proof. exact (EQ_MP (@lem3223884 A s x) (@lem3223881 A s u x h1)). Qed.
Lemma lem3223891 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3223892 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33146 : A) : (term63 A s t _33146) = (term173 A t s _33146).
Proof. exact (@lem3223891 (t _33146) (term201 A s _33146)). Qed.
Lemma lem3223898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3223899 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33146 : A) : (term204 A s t _33146) = (term205 A t s _33146).
Proof. exact (MK_COMB (@lem3223898) (@lem3223892 A t s _33146)). Qed.
Lemma lem3223905 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33146 : A) : (term173 A t s _33146) = (term173 A t s _33146).
Proof. exact (eq_refl (term173 A t s _33146)). Qed.
Lemma lem3223906 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33146 : A) : ((term63 A s t _33146) = (term173 A t s _33146)) = ((term173 A t s _33146) = (term173 A t s _33146)).
Proof. exact (MK_COMB (@lem3223899 A t s _33146) (@lem3223905 A t s _33146)). Qed.
Lemma lem3223908 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3223909 (x : Prop) : (x = x) = True.
Proof. exact (@lem3223908 Prop x). Qed.
Lemma lem3223910 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33146 : A) : ((term173 A t s _33146) = (term173 A t s _33146)) = True.
Proof. exact (@lem3223909 (term173 A t s _33146)). Qed.
Lemma lem3223911 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33146 : A) : ((term63 A s t _33146) = (term173 A t s _33146)) = True.
Proof. exact (TRANS (@lem3223906 A t s _33146) (@lem3223910 A t s _33146)). Qed.
Lemma lem3223912 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33146 : A) : True = ((term63 A s t _33146) = (term173 A t s _33146)).
Proof. exact (SYM (@lem3223911 A t s _33146)). Qed.
Lemma lem3223913 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33146 : A) : (term63 A s t _33146) = (term173 A t s _33146).
Proof. exact (EQ_MP (@lem3223912 A t s _33146) (@lem0)). Qed.
Lemma lem3223914 {A : Type'} (_33146 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term173 A t s _33146.
Proof. exact (EQ_MP (@lem3223913 A t s _33146) (@lem3223378 A _33146 s x' t u x'' h1)). Qed.
Lemma lem3223916 (b : Prop) (a : Prop) : (a \/ b) = (term206 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3223917 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33146 : A) : (term173 A t s _33146) = (term207 A s t _33146).
Proof. exact (@lem3223916 (term201 A s _33146) (t _33146)). Qed.
Lemma lem3223919 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3223920 {A : Type'} (s : A -> Prop) (_33146 : A) : (term208 A s _33146) = (s _33146).
Proof. exact (@lem3223919 (s _33146)). Qed.
Lemma lem3223921 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3223922 {A : Type'} (s : A -> Prop) (_33146 : A) : (term209 A s _33146) = (term29 A s _33146).
Proof. exact (MK_COMB (@lem3223921) (@lem3223920 A s _33146)). Qed.
Lemma lem3223923 {A : Type'} (t : A -> Prop) (_33146 : A) : (t _33146) = (t _33146).
Proof. exact (eq_refl (t _33146)). Qed.
Lemma lem3223924 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33146 : A) : (term207 A s t _33146) = (term31 A s t _33146).
Proof. exact (MK_COMB (@lem3223922 A s _33146) (@lem3223923 A t _33146)). Qed.
Lemma lem3223925 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33146 : A) : (term173 A t s _33146) = (term31 A s t _33146).
Proof. exact (TRANS (@lem3223917 A s t _33146) (@lem3223924 A s t _33146)). Qed.
Lemma lem3223928 {A : Type'} (_33146 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t _33146.
Proof. exact (EQ_MP (@lem3223925 A s t _33146) (@lem3223914 A _33146 s x' t u x'' h1)). Qed.
Lemma lem3223929 {A : Type'} (_33146 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t _33146.
Proof. exact (@lem3223928 A _33146 s x' t u x'' h1). Qed.
Lemma lem3223930 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t x.
Proof. exact (@lem3223929 A x s x' t u x'' h1). Qed.
Lemma lem3223933 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s u x) (h2 : term148 A s x' t u x'') : t x.
Proof. exact (@lem3223930 A x s x' t u x'' h2 (@lem3223885 A s u x h1)). Qed.
Lemma lem3223934 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s u x) (h2 : term148 A s x' t u x'') : term202 A t x.
Proof. exact (fun h0 : term201 A t x => @lem3223933 A x s x' t u x'' h1 h2). Qed.
Lemma lem3223936 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223937 {A : Type'} (t : A -> Prop) (x : A) : (term202 A t x) = (t x).
Proof. exact (@lem3223936 (t x)). Qed.
Lemma lem3223938 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s u x) (h2 : term148 A s x' t u x'') : t x.
Proof. exact (EQ_MP (@lem3223937 A t x) (@lem3223934 A x s x' t u x'' h1 h2)). Qed.
Lemma lem3223944 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3223945 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33145 : A) : (term63 A t u _33145) = (term173 A u t _33145).
Proof. exact (@lem3223944 (u _33145) (term201 A t _33145)). Qed.
Lemma lem3223951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3223952 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33145 : A) : (term204 A t u _33145) = (term205 A u t _33145).
Proof. exact (MK_COMB (@lem3223951) (@lem3223945 A u t _33145)). Qed.
Lemma lem3223958 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33145 : A) : (term173 A u t _33145) = (term173 A u t _33145).
Proof. exact (eq_refl (term173 A u t _33145)). Qed.
Lemma lem3223959 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33145 : A) : ((term63 A t u _33145) = (term173 A u t _33145)) = ((term173 A u t _33145) = (term173 A u t _33145)).
Proof. exact (MK_COMB (@lem3223952 A u t _33145) (@lem3223958 A u t _33145)). Qed.
Lemma lem3223961 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3223962 (x : Prop) : (x = x) = True.
Proof. exact (@lem3223961 Prop x). Qed.
Lemma lem3223963 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33145 : A) : ((term173 A u t _33145) = (term173 A u t _33145)) = True.
Proof. exact (@lem3223962 (term173 A u t _33145)). Qed.
Lemma lem3223964 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33145 : A) : ((term63 A t u _33145) = (term173 A u t _33145)) = True.
Proof. exact (TRANS (@lem3223959 A u t _33145) (@lem3223963 A u t _33145)). Qed.
Lemma lem3223965 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33145 : A) : True = ((term63 A t u _33145) = (term173 A u t _33145)).
Proof. exact (SYM (@lem3223964 A u t _33145)). Qed.
Lemma lem3223966 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33145 : A) : (term63 A t u _33145) = (term173 A u t _33145).
Proof. exact (EQ_MP (@lem3223965 A u t _33145) (@lem0)). Qed.
Lemma lem3223967 {A : Type'} (_33145 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term173 A u t _33145.
Proof. exact (EQ_MP (@lem3223966 A u t _33145) (@lem3223372 A _33145 s x' t u x'' h1)). Qed.
Lemma lem3223969 (b : Prop) (a : Prop) : (a \/ b) = (term206 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3223970 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33145 : A) : (term173 A u t _33145) = (term207 A t u _33145).
Proof. exact (@lem3223969 (term201 A t _33145) (u _33145)). Qed.
Lemma lem3223972 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3223973 {A : Type'} (t : A -> Prop) (_33145 : A) : (term208 A t _33145) = (t _33145).
Proof. exact (@lem3223972 (t _33145)). Qed.
Lemma lem3223974 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3223975 {A : Type'} (t : A -> Prop) (_33145 : A) : (term209 A t _33145) = (term29 A t _33145).
Proof. exact (MK_COMB (@lem3223974) (@lem3223973 A t _33145)). Qed.
Lemma lem3223976 {A : Type'} (u : A -> Prop) (_33145 : A) : (u _33145) = (u _33145).
Proof. exact (eq_refl (u _33145)). Qed.
Lemma lem3223977 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33145 : A) : (term207 A t u _33145) = (term31 A t u _33145).
Proof. exact (MK_COMB (@lem3223975 A t _33145) (@lem3223976 A u _33145)). Qed.
Lemma lem3223978 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33145 : A) : (term173 A u t _33145) = (term31 A t u _33145).
Proof. exact (TRANS (@lem3223970 A t u _33145) (@lem3223977 A t u _33145)). Qed.
Lemma lem3223981 {A : Type'} (_33145 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u _33145.
Proof. exact (EQ_MP (@lem3223978 A t u _33145) (@lem3223967 A _33145 s x' t u x'' h1)). Qed.
Lemma lem3223982 {A : Type'} (_33145 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u _33145.
Proof. exact (@lem3223981 A _33145 s x' t u x'' h1). Qed.
Lemma lem3223983 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A t u x.
Proof. exact (@lem3223982 A x s x' t u x'' h1). Qed.
Lemma lem3223986 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s u x) (h2 : term148 A s x' t u x'') : u x.
Proof. exact (@lem3223983 A x s x' t u x'' h2 (@lem3223938 A x s x' t u x'' h1 h2)). Qed.
Lemma lem3223987 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s u x) (h2 : term148 A s x' t u x'') : term202 A u x.
Proof. exact (fun h0 : term201 A u x => @lem3223986 A x s x' t u x'' h1 h2). Qed.
Lemma lem3223989 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3223990 {A : Type'} (u : A -> Prop) (x : A) : (term202 A u x) = (u x).
Proof. exact (@lem3223989 (u x)). Qed.
Lemma lem3223991 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s u x) (h2 : term148 A s x' t u x'') : u x.
Proof. exact (EQ_MP (@lem3223990 A u x) (@lem3223987 A x s x' t u x'' h1 h2)). Qed.
Lemma lem3223994 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3223996 {A : Type'} (u : A -> Prop) (x : A) : (term201 A u x) = (term210 A u x).
Proof. exact (@lem3223994 (u x)). Qed.
Lemma lem3223999 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term87 A s u x) : term210 A u x.
Proof. exact (EQ_MP (@lem3223996 A u x) (@lem3223390 A s u x h1)). Qed.
Lemma lem3224002 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s u x) (h2 : term148 A s x' t u x'') : False.
Proof. exact (@lem3223999 A s u x h1 (@lem3223991 A x s x' t u x'' h1 h2)). Qed.
Lemma lem3224003 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s u x) (h2 : term148 A s x' t u x'') : term211.
Proof. exact (fun h0 : ~ False => @lem3224002 A x s x' t u x'' h1 h2). Qed.
Lemma lem3224005 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3224006 : term211 = False.
Proof. exact (@lem3224005 False). Qed.
Lemma lem3224007 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term87 A s u x) (h2 : term148 A s x' t u x'') : False.
Proof. exact (EQ_MP (@lem3224006) (@lem3224003 A x s x' t u x'' h1 h2)). Qed.
Lemma lem3224009 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term91 A t u x'') : u x''.
Proof. exact (proj2 (@lem3222638 A t u x'' h1)). Qed.
Lemma lem3224010 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term91 A t u x'') : term202 A u x''.
Proof. exact (fun h0 : term201 A u x'' => @lem3224009 A t u x'' h1). Qed.
Lemma lem3224012 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3224013 {A : Type'} (u : A -> Prop) (x'' : A) : (term202 A u x'') = (u x'').
Proof. exact (@lem3224012 (u x'')). Qed.
Lemma lem3224014 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term91 A t u x'') : u x''.
Proof. exact (EQ_MP (@lem3224013 A u x'') (@lem3224010 A t u x'' h1)). Qed.
Lemma lem3224016 (b : Prop) (a : Prop) : (a \/ b) = (term206 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3224017 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33149 : A) : (term173 A s u _33149) = (term207 A u s _33149).
Proof. exact (@lem3224016 (term201 A u _33149) (s _33149)). Qed.
Lemma lem3224019 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3224020 {A : Type'} (u : A -> Prop) (_33149 : A) : (term208 A u _33149) = (u _33149).
Proof. exact (@lem3224019 (u _33149)). Qed.
Lemma lem3224021 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3224022 {A : Type'} (u : A -> Prop) (_33149 : A) : (term209 A u _33149) = (term29 A u _33149).
Proof. exact (MK_COMB (@lem3224021) (@lem3224020 A u _33149)). Qed.
Lemma lem3224023 {A : Type'} (s : A -> Prop) (_33149 : A) : (s _33149) = (s _33149).
Proof. exact (eq_refl (s _33149)). Qed.
Lemma lem3224024 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33149 : A) : (term207 A u s _33149) = (term31 A u s _33149).
Proof. exact (MK_COMB (@lem3224022 A u _33149) (@lem3224023 A s _33149)). Qed.
Lemma lem3224025 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33149 : A) : (term173 A s u _33149) = (term31 A u s _33149).
Proof. exact (TRANS (@lem3224017 A u s _33149) (@lem3224024 A u s _33149)). Qed.
Lemma lem3224028 {A : Type'} (_33149 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term188 A s u) : term31 A u s _33149.
Proof. exact (EQ_MP (@lem3224025 A u s _33149) (@lem3223416 A _33149 s u h1)). Qed.
Lemma lem3224029 {A : Type'} (_33149 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term188 A s u) : term31 A u s _33149.
Proof. exact (@lem3224028 A _33149 s u h1). Qed.
Lemma lem3224030 {A : Type'} (x'' : A) (s : A -> Prop) (u : A -> Prop) (h1 : term188 A s u) : term31 A u s x''.
Proof. exact (@lem3224029 A x'' s u h1). Qed.
Lemma lem3224033 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term188 A s u) (h2 : term91 A t u x'') : s x''.
Proof. exact (@lem3224030 A x'' s u h1 (@lem3224014 A t u x'' h2)). Qed.
Lemma lem3224034 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term188 A s u) (h2 : term91 A t u x'') : term202 A s x''.
Proof. exact (fun h0 : term201 A s x'' => @lem3224033 A s t u x'' h1 h2). Qed.
Lemma lem3224036 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3224037 {A : Type'} (s : A -> Prop) (x'' : A) : (term202 A s x'') = (s x'').
Proof. exact (@lem3224036 (s x'')). Qed.
Lemma lem3224038 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term188 A s u) (h2 : term91 A t u x'') : s x''.
Proof. exact (EQ_MP (@lem3224037 A s x'') (@lem3224034 A s t u x'' h1 h2)). Qed.
Lemma lem3224044 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3224045 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33148 : A) : (term63 A s t _33148) = (term173 A t s _33148).
Proof. exact (@lem3224044 (t _33148) (term201 A s _33148)). Qed.
Lemma lem3224051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3224052 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33148 : A) : (term204 A s t _33148) = (term205 A t s _33148).
Proof. exact (MK_COMB (@lem3224051) (@lem3224045 A t s _33148)). Qed.
Lemma lem3224058 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33148 : A) : (term173 A t s _33148) = (term173 A t s _33148).
Proof. exact (eq_refl (term173 A t s _33148)). Qed.
Lemma lem3224059 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33148 : A) : ((term63 A s t _33148) = (term173 A t s _33148)) = ((term173 A t s _33148) = (term173 A t s _33148)).
Proof. exact (MK_COMB (@lem3224052 A t s _33148) (@lem3224058 A t s _33148)). Qed.
Lemma lem3224061 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3224062 (x : Prop) : (x = x) = True.
Proof. exact (@lem3224061 Prop x). Qed.
Lemma lem3224063 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33148 : A) : ((term173 A t s _33148) = (term173 A t s _33148)) = True.
Proof. exact (@lem3224062 (term173 A t s _33148)). Qed.
Lemma lem3224064 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33148 : A) : ((term63 A s t _33148) = (term173 A t s _33148)) = True.
Proof. exact (TRANS (@lem3224059 A t s _33148) (@lem3224063 A t s _33148)). Qed.
Lemma lem3224065 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33148 : A) : True = ((term63 A s t _33148) = (term173 A t s _33148)).
Proof. exact (SYM (@lem3224064 A t s _33148)). Qed.
Lemma lem3224066 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33148 : A) : (term63 A s t _33148) = (term173 A t s _33148).
Proof. exact (EQ_MP (@lem3224065 A t s _33148) (@lem0)). Qed.
Lemma lem3224067 {A : Type'} (_33148 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term173 A t s _33148.
Proof. exact (EQ_MP (@lem3224066 A t s _33148) (@lem3223402 A _33148 s x' t u x'' h1)). Qed.
Lemma lem3224069 (b : Prop) (a : Prop) : (a \/ b) = (term206 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3224070 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33148 : A) : (term173 A t s _33148) = (term207 A s t _33148).
Proof. exact (@lem3224069 (term201 A s _33148) (t _33148)). Qed.
Lemma lem3224072 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3224073 {A : Type'} (s : A -> Prop) (_33148 : A) : (term208 A s _33148) = (s _33148).
Proof. exact (@lem3224072 (s _33148)). Qed.
Lemma lem3224074 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3224075 {A : Type'} (s : A -> Prop) (_33148 : A) : (term209 A s _33148) = (term29 A s _33148).
Proof. exact (MK_COMB (@lem3224074) (@lem3224073 A s _33148)). Qed.
Lemma lem3224076 {A : Type'} (t : A -> Prop) (_33148 : A) : (t _33148) = (t _33148).
Proof. exact (eq_refl (t _33148)). Qed.
Lemma lem3224077 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33148 : A) : (term207 A s t _33148) = (term31 A s t _33148).
Proof. exact (MK_COMB (@lem3224075 A s _33148) (@lem3224076 A t _33148)). Qed.
Lemma lem3224078 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33148 : A) : (term173 A t s _33148) = (term31 A s t _33148).
Proof. exact (TRANS (@lem3224070 A s t _33148) (@lem3224077 A s t _33148)). Qed.
Lemma lem3224081 {A : Type'} (_33148 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t _33148.
Proof. exact (EQ_MP (@lem3224078 A s t _33148) (@lem3224067 A _33148 s x' t u x'' h1)). Qed.
Lemma lem3224082 {A : Type'} (_33148 : A) (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t _33148.
Proof. exact (@lem3224081 A _33148 s x' t u x'' h1). Qed.
Lemma lem3224083 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term148 A s x' t u x'') : term31 A s t x''.
Proof. exact (@lem3224082 A x'' s x' t u x'' h1). Qed.
Lemma lem3224086 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term188 A s u) (h2 : term91 A t u x'') (h3 : term148 A s x' t u x'') : t x''.
Proof. exact (@lem3224083 A s x' t u x'' h3 (@lem3224038 A s t u x'' h1 h2)). Qed.
Lemma lem3224087 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term188 A s u) (h2 : term91 A t u x'') (h3 : term148 A s x' t u x'') : term202 A t x''.
Proof. exact (fun h0 : term201 A t x'' => @lem3224086 A s x' t u x'' h1 h2 h3). Qed.
Lemma lem3224089 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3224090 {A : Type'} (t : A -> Prop) (x'' : A) : (term202 A t x'') = (t x'').
Proof. exact (@lem3224089 (t x'')). Qed.
Lemma lem3224091 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term188 A s u) (h2 : term91 A t u x'') (h3 : term148 A s x' t u x'') : t x''.
Proof. exact (EQ_MP (@lem3224090 A t x'') (@lem3224087 A s x' t u x'' h1 h2 h3)). Qed.
Lemma lem3224094 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3224096 {A : Type'} (t : A -> Prop) (x'' : A) : (term201 A t x'') = (term210 A t x'').
Proof. exact (@lem3224094 (t x'')). Qed.
Lemma lem3224099 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term91 A t u x'') : term210 A t x''.
Proof. exact (EQ_MP (@lem3224096 A t x'') (@lem3223408 A t u x'' h1)). Qed.
Lemma lem3224102 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term188 A s u) (h2 : term91 A t u x'') (h3 : term148 A s x' t u x'') : False.
Proof. exact (@lem3224099 A t u x'' h2 (@lem3224091 A s x' t u x'' h1 h2 h3)). Qed.
Lemma lem3224103 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term188 A s u) (h2 : term91 A t u x'') (h3 : term148 A s x' t u x'') : term211.
Proof. exact (fun h0 : ~ False => @lem3224102 A s x' t u x'' h1 h2 h3). Qed.
Lemma lem3224105 (p : Prop) : (term203 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3224106 : term211 = False.
Proof. exact (@lem3224105 False). Qed.
Lemma lem3224107 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (u : A -> Prop) (x'' : A) (h1 : term188 A s u) (h2 : term91 A t u x'') (h3 : term148 A s x' t u x'') : False.
Proof. exact (EQ_MP (@lem3224106) (@lem3224103 A s x' t u x'' h1 h2 h3)). Qed.
Lemma lem3224108 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term91 A t u x'') (h2 : term148 A s x' t u x'') (h3 : term197 A x s u) : False.
Proof. exact (or_elim (@lem3222518 A x s u h3) (fun h0 : term87 A s u x => @lem3224007 A x s x' t u x'' h0 h2) (fun h0 : term188 A s u => @lem3224107 A s x' t u x'' h0 h1 h2)). Qed.
Lemma lem3224109 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') (h3 : term197 A x s u) : False.
Proof. exact (or_elim (@lem3222518 A x s u h3) (fun h0 : term87 A s u x => @lem3223802 A s x' t u x'' h1 h2) (fun h0 : term188 A s u => @lem3223878 A s x' t u x'' h1 h2)). Qed.
Lemma lem3224110 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term148 A s x' t u x'') (h2 : term197 A x s u) : False.
Proof. exact (or_elim (@lem3222609 A s x' t u x'' h1) (fun h0 : term87 A t u x'' => @lem3224109 A x' t x'' x s u h0 h1 h2) (fun h0 : term91 A t u x'' => @lem3224108 A x' t x'' x s u h0 h1 h2)). Qed.
Lemma lem3224111 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') (h3 : term197 A x s u) : False.
Proof. exact (or_elim (@lem3222518 A x s u h3) (fun h0 : term87 A s u x => @lem3223650 A s x' t u x'' h1 h2) (fun h0 : term188 A s u => @lem3223726 A s x' t u x'' h1 h2)). Qed.
Lemma lem3224112 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term87 A t u x'') (h2 : term148 A s x' t u x'') (h3 : term197 A x s u) : False.
Proof. exact (or_elim (@lem3222518 A x s u h3) (fun h0 : term87 A s u x => @lem3223498 A s x' t u x'' h1 h2) (fun h0 : term188 A s u => @lem3223574 A s x' t u x'' h1 h2)). Qed.
Lemma lem3224113 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term87 A s t x') (h2 : term148 A s x' t u x'') (h3 : term197 A x s u) : False.
Proof. exact (or_elim (@lem3222609 A s x' t u x'' h2) (fun h0 : term87 A t u x'' => @lem3224112 A x' t x'' x s u h0 h2 h3) (fun h0 : term91 A t u x'' => @lem3224111 A x' t x'' x s u h1 h2 h3)). Qed.
Lemma lem3224114 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term148 A s x' t u x'') (h2 : term197 A x s u) : False.
Proof. exact (or_elim (@lem3222611 A s x' t u x'' h1) (fun h0 : term87 A s t x' => @lem3224113 A x' t x'' x s u h0 h1 h2) (fun h0 : term91 A s t x' => @lem3224110 A x' t x'' x s u h1 h2)). Qed.
Lemma lem3224115 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term148 A s x' t u x'') (h2 : term197 A x s u) : (term148 A s x' t u x'') = False.
Proof. exact (prop_ext (fun h3 : term148 A s x' t u x'' => @lem3224114 A x' t x'' x s u h1 h2) (fun h3 : False => @lem3222606 A s x' t u x'' h1)). Qed.
Lemma lem3224116 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term148 A s x' t u x'') (h2 : term197 A x s u) : False.
Proof. exact (EQ_MP (@lem3224115 A x' t x'' x s u h1 h2) (@lem3222606 A s x' t u x'' h1)). Qed.
Lemma lem3224117 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term148 A s x' t u x'') (h2 : term197 A x s u) : (term197 A x s u) = False.
Proof. exact (prop_ext (fun h3 : term197 A x s u => @lem3224116 A x' t x'' x s u h1 h2) (fun h3 : False => @lem3222518 A x s u h2)). Qed.
Lemma lem3224118 {A : Type'} (x' : A) (t : A -> Prop) (x'' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term148 A s x' t u x'') (h2 : term197 A x s u) : False.
Proof. exact (EQ_MP (@lem3224117 A x' t x'' x s u h1 h2) (@lem3222518 A x s u h2)). Qed.
Lemma lem3224119 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term151 A s x' t u) (h2 : term197 A x s u) : False.
Proof. exact (ex_elim (@lem3222471 A s x' t u h1) (fun x'' : A => fun h0 : term150 A s x' t u x'' => @lem3224118 A x' t x'' x s u h0 h2)). Qed.
Lemma lem3224120 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term44 A s t u) (h2 : term197 A x s u) : False.
Proof. exact (ex_elim (@lem3222283 A s t u h1) (fun x' : A => fun h0 : term152 A s t u x' => @lem3224119 A x' t x s u h0 h2)). Qed.
Lemma lem3224121 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term62 A s u) (h2 : term44 A s t u) : False.
Proof. exact (ex_elim (@lem3222469 A s u h1) (fun x : A => fun h0 : term199 A s u x => @lem3224120 A t x s u h2 h0)). Qed.
Lemma lem3224122 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term62 A s u) (h2 : term44 A s t u) : (term62 A s u) = False.
Proof. exact (prop_ext (fun h3 : term62 A s u => @lem3224121 A s t u h1 h2) (fun h3 : False => @lem3221804 A s u h1)). Qed.
Lemma lem3224123 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term62 A s u) (h2 : term44 A s t u) : False.
Proof. exact (EQ_MP (@lem3224122 A s t u h1 h2) (@lem3221804 A s u h1)). Qed.
Lemma lem3224124 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term44 A s t u) : term61 A s u.
Proof. exact (fun h0 : term62 A s u => @lem3224123 A s t u h0 h1). Qed.
Lemma lem3224125 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term44 A s t u) : term42 A s u.
Proof. exact (EQ_MP (@lem3221803 A s u) (@lem3224124 A s t u h1)). Qed.
Lemma lem3224126 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term46 A t s u.
Proof. exact (fun h0 : term44 A s t u => @lem3224125 A s t u h0). Qed.
Lemma lem3224131 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term48 A t s.
Proof. exact (fun u : A -> Prop => @lem3224126 A t s u). Qed.
Lemma lem3224136 {A : Type'} (s : A -> Prop) : term50 A s.
Proof. exact (fun t : A -> Prop => @lem3224131 A t s). Qed.
Lemma lem3224141 {A : Type'} : term52 A.
Proof. exact (fun s : A -> Prop => @lem3224136 A s). Qed.
Lemma lem3224142 {A : Type'} : term54 A.
Proof. exact (EQ_MP (@lem3221798 A) (@lem3224141 A)). Qed.
Lemma lem3224144 {A : Type'} : term54 A.
Proof. exact (@lem3221583 A (@lem3224142 A)). Qed.
Lemma lem3224145 {A : Type'} (h1 : term55 A) : False.
Proof. exact (@lem3224144 A (@lem3221567 A h1)). Qed.
Lemma lem3224146 {A : Type'} (h1 : term55 A) : (term55 A) = False.
Proof. exact (prop_ext (fun h2 : term55 A => @lem3224145 A h1) (fun h2 : False => @lem3221567 A h1)). Qed.
Lemma lem3224147 {A : Type'} (h1 : term55 A) : False.
Proof. exact (EQ_MP (@lem3224146 A h1) (@lem3221567 A h1)). Qed.
Lemma lem3224148 {A : Type'} : term54 A.
Proof. exact (fun h0 : term55 A => @lem3224147 A h0). Qed.
Lemma lem3224149 {A : Type'} : term52 A.
Proof. exact (EQ_MP (@lem3221566 A) (@lem3224148 A)). Qed.
Lemma lem3224150 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem3221562 A) (@lem3224149 A)). Qed.
Lemma lem3224151 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem3221331 A) (@lem3224150 A)). Qed.
