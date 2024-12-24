Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_DELETE_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_DELETE_IMP_spec.
Require Import FINITE_INSERT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1823_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Lemma lem3609228 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem3609229 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3609230 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3609229 A s) (@lem3609228 A s)). Qed.
Lemma lem3609231 {A : Type'} (s : A -> Prop) (x : A) : term2 A s x.
Proof. exact (@lem3609230 A s x). Qed.
Lemma lem3609232 {A : Type'} (x : A) (s : A -> Prop) : (term2 A s x) = ((term3 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term2 A s x)). Qed.
Lemma lem3609234 {A : Type'} (x : A) (s : A -> Prop) : term4 A x s.
Proof. exact (@lem9784 (@IN A x s)). Qed.
Lemma lem3609235 {A : Type'} (x : A) (s : A -> Prop) : (term4 A x s) = (term5 A x s).
Proof. exact (eq_refl (term4 A x s)). Qed.
Lemma lem3609236 {A : Type'} (x : A) (s : A -> Prop) : term5 A x s.
Proof. exact (EQ_MP (@lem3609235 A x s) (@lem3609234 A x s)). Qed.
Lemma lem3609237 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3609238 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : term6 A x s.
Proof. exact (h1). Qed.
Lemma lem3609239 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3609207 A s). Qed.
Lemma lem3609240 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem3609241 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem3609240 A s) (@lem3609239 A s)). Qed.
Lemma lem3609242 {A : Type'} (s : A -> Prop) (x : A) : term9 A s x.
Proof. exact (@lem3609241 A s x). Qed.
Lemma lem3609243 {A : Type'} (s : A -> Prop) (x : A) : (term9 A s x) = (term10 A s x).
Proof. exact (eq_refl (term9 A s x)). Qed.
Lemma lem3609244 {A : Type'} (s : A -> Prop) (x : A) : term10 A s x.
Proof. exact (EQ_MP (@lem3609243 A s x) (@lem3609242 A s x)). Qed.
Lemma lem3609245 {A : Type'} (s : A -> Prop) (x : A) : (term10 A s x) = ((term10 A s x) = True).
Proof. exact (@lem7 (term10 A s x)). Qed.
Lemma lem3609252 {A : Type'} (s : A -> Prop) (x : A) : (term10 A s x) = True.
Proof. exact (EQ_MP (@lem3609245 A s x) (@lem3609244 A s x)). Qed.
Lemma lem3609253 {A : Type'} (s : A -> Prop) (x : A) : (term10 A s x) = True.
Proof. exact (@lem3609252 A s x). Qed.
Lemma lem3609254 {A : Type'} (s : A -> Prop) (x : A) : True = (term10 A s x).
Proof. exact (SYM (@lem3609253 A s x)). Qed.
Lemma lem3609255 {A : Type'} (s : A -> Prop) (x : A) : term10 A s x.
Proof. exact (EQ_MP (@lem3609254 A s x) (@lem0)). Qed.
Lemma lem3609258 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term11 A s x)) : s = (term11 A s x).
Proof. exact (h1). Qed.
Lemma lem3609259 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3609260 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term11 A s x)) : (@FINITE A s) = (term12 A s x).
Proof. exact (MK_COMB (@lem3609259 A) (@lem3609258 A s x h1)). Qed.
Lemma lem3609261 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term13 A s x).
Proof. exact (eq_refl (term13 A s x)). Qed.
Lemma lem3609262 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term11 A s x)) : (term14 A x s) = (term15 A s x).
Proof. exact (MK_COMB (@lem3609261 A s x) (@lem3609260 A s x h1)). Qed.
Lemma lem3609263 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term11 A s x)) : (term15 A s x) = (term14 A x s).
Proof. exact (SYM (@lem3609262 A s x h1)). Qed.
Lemma lem3609271 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3609232 A x s) (@lem3609231 A s x)). Qed.
Lemma lem3609272 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (@FINITE A s).
Proof. exact (@lem3609271 A x s). Qed.
Lemma lem3609273 {A : Type'} (s : A -> Prop) (x : A) : (term12 A s x) = (term16 A s x).
Proof. exact (@lem3609272 A x (@DELETE A s x)). Qed.
Lemma lem3609274 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term13 A s x).
Proof. exact (eq_refl (term13 A s x)). Qed.
Lemma lem3609275 {A : Type'} (s : A -> Prop) (x : A) : (term15 A s x) = (term17 A s x).
Proof. exact (MK_COMB (@lem3609274 A s x) (@lem3609273 A s x)). Qed.
Lemma lem3609277 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3609278 {A : Type'} (s : A -> Prop) (x : A) : (term17 A s x) = True.
Proof. exact (@lem3609277 (term16 A s x)). Qed.
Lemma lem3609279 {A : Type'} (s : A -> Prop) (x : A) : (term15 A s x) = True.
Proof. exact (TRANS (@lem3609275 A s x) (@lem3609278 A s x)). Qed.
Lemma lem3609280 {A : Type'} (s : A -> Prop) (x : A) : True = (term15 A s x).
Proof. exact (SYM (@lem3609279 A s x)). Qed.
Lemma lem3609281 {A : Type'} (s : A -> Prop) (x : A) : term15 A s x.
Proof. exact (EQ_MP (@lem3609280 A s x) (@lem0)). Qed.
Lemma lem3609287 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3609288 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (@lem3609287 A s t). Qed.
Lemma lem3609289 {A : Type'} (s : A -> Prop) (x : A) : (s = (term11 A s x)) = (term19 A s x).
Proof. exact (@lem3609288 A s (term11 A s x)). Qed.
Lemma lem3609298 {A : Type'} (x : A) (s : A -> Prop) : (term20 A x s) = (term20 A x s).
Proof. exact (eq_refl (term20 A x s)). Qed.
Lemma lem3609299 {A : Type'} (s : A -> Prop) (x : A) : (term21 A s x) = (term22 A s x).
Proof. exact (MK_COMB (@lem3609298 A x s) (@lem3609289 A s x)). Qed.
Lemma lem3609302 {A : Type'} (s : A -> Prop) (x : A) : (term22 A s x) = (term21 A s x).
Proof. exact (SYM (@lem3609299 A s x)). Qed.
Lemma lem3609306 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3609307 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3609306 A P x). Qed.
Lemma lem3609308 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3609307 A s x). Qed.
Lemma lem3609309 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3609310 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term23 A s x).
Proof. exact (MK_COMB (@lem3609309) (@lem3609308 A s x)). Qed.
Lemma lem3609318 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3609319 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3609318 A P x). Qed.
Lemma lem3609320 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3609319 A s x'). Qed.
Lemma lem3609321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3609322 {A : Type'} (s : A -> Prop) (x' : A) : (term24 A x' s) = (term25 A s x').
Proof. exact (MK_COMB (@lem3609321) (@lem3609320 A s x')). Qed.
Lemma lem3609324 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term26 A x y s) = (term27 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3609325 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term26 A x y s) = (term27 A y x s).
Proof. exact (@lem3609324 A y x s). Qed.
Lemma lem3609326 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term28 A x' s x) = (term29 A x' s x).
Proof. exact (@lem3609325 A x x' (@DELETE A s x)). Qed.
Lemma lem3609332 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term30 A x s y) = (term31 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3609333 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term30 A x s y) = (term31 A s x y).
Proof. exact (@lem3609332 A s x y). Qed.
Lemma lem3609334 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term30 A x' s x) = (term31 A s x' x).
Proof. exact (@lem3609333 A s x' x). Qed.
Lemma lem3609338 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3609339 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3609338 A P x). Qed.
Lemma lem3609340 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3609339 A s x'). Qed.
Lemma lem3609341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3609342 {A : Type'} (s : A -> Prop) (x' : A) : (term32 A x' s) = (term33 A s x').
Proof. exact (MK_COMB (@lem3609341) (@lem3609340 A s x')). Qed.
Lemma lem3609345 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3609346 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term31 A s x' x) = (term35 A s x' x).
Proof. exact (MK_COMB (@lem3609342 A s x') (@lem3609345 A x' x)). Qed.
Lemma lem3609349 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term30 A x' s x) = (term35 A s x' x).
Proof. exact (TRANS (@lem3609334 A s x' x) (@lem3609346 A s x' x)). Qed.
Lemma lem3609350 {A : Type'} (x' : A) (x : A) : (term36 A x' x) = (term36 A x' x).
Proof. exact (eq_refl (term36 A x' x)). Qed.
Lemma lem3609351 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term29 A x' s x) = (term37 A s x' x).
Proof. exact (MK_COMB (@lem3609350 A x' x) (@lem3609349 A s x' x)). Qed.
Lemma lem3609354 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term28 A x' s x) = (term37 A s x' x).
Proof. exact (TRANS (@lem3609326 A x' s x) (@lem3609351 A s x' x)). Qed.
Lemma lem3609355 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((@IN A x' s) = (term28 A x' s x)) = ((s x') = (term37 A s x' x)).
Proof. exact (MK_COMB (@lem3609322 A s x') (@lem3609354 A s x' x)). Qed.
Lemma lem3609358 {A : Type'} (s : A -> Prop) (x : A) : (term38 A s x) = (term39 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3609355 A s x' x)). Qed.
Lemma lem3609359 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3609360 {A : Type'} (s : A -> Prop) (x : A) : (term19 A s x) = (term40 A s x).
Proof. exact (MK_COMB (@lem3609359 A) (@lem3609358 A s x)). Qed.
Lemma lem3609365 {A : Type'} (s : A -> Prop) (x : A) : (term22 A s x) = (term41 A s x).
Proof. exact (MK_COMB (@lem3609310 A s x) (@lem3609360 A s x)). Qed.
Lemma lem3609368 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (term22 A s x).
Proof. exact (SYM (@lem3609365 A s x)). Qed.
Lemma lem3609370 (p : Prop) : p = (term42 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3609371 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (term43 A s x).
Proof. exact (@lem3609370 (term41 A s x)). Qed.
Lemma lem3609372 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term41 A s x).
Proof. exact (SYM (@lem3609371 A s x)). Qed.
Lemma lem3609373 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : term44 A s x.
Proof. exact (h1). Qed.
Lemma lem3609376 {A : Type'} (s : A -> Prop) (x : A) (h1 : term43 A s x) : term43 A s x.
Proof. exact (h1). Qed.
Lemma lem3609377 {A : Type'} (s : A -> Prop) (x : A) : term45 A s x.
Proof. exact (fun h0 : term43 A s x => @lem3609376 A s x h0). Qed.
Lemma lem3609378 {A : Type'} (s : A -> Prop) (x : A) (h1 : term45 A s x) : term45 A s x.
Proof. exact (h1). Qed.
Lemma lem3609379 {A : Type'} (s : A -> Prop) (x : A) (h1 : term43 A s x) : term43 A s x.
Proof. exact (h1). Qed.
Lemma lem3609380 {A : Type'} (s : A -> Prop) (x : A) (h1 : term43 A s x) (h2 : term45 A s x) : term43 A s x.
Proof. exact (@lem3609378 A s x h2 (@lem3609379 A s x h1)). Qed.
Lemma lem3609381 {A : Type'} (s : A -> Prop) (x : A) (h1 : term43 A s x) : term46 A s x.
Proof. exact (fun h0 : term45 A s x => @lem3609380 A s x h1 h0). Qed.
Lemma lem3609382 {A : Type'} (s : A -> Prop) (x : A) (h1 : term45 A s x) : term45 A s x.
Proof. exact (h1). Qed.
Lemma lem3609383 {A : Type'} (s : A -> Prop) (x : A) (h1 : term43 A s x) (h2 : term45 A s x) : term43 A s x.
Proof. exact (@lem3609381 A s x h1 (@lem3609382 A s x h2)). Qed.
Lemma lem3609384 {A : Type'} (s : A -> Prop) (x : A) (h1 : term45 A s x) : term45 A s x.
Proof. exact (fun h0 : term43 A s x => @lem3609383 A s x h0 h1). Qed.
Lemma lem3609385 {A : Type'} (s : A -> Prop) (x : A) : term47 A s x.
Proof. exact (fun h0 : term45 A s x => @lem3609384 A s x h0). Qed.
Lemma lem3609388 {A : Type'} (s : A -> Prop) (x : A) : term45 A s x.
Proof. exact (@lem3609385 A s x (@lem3609377 A s x)). Qed.
Lemma lem3609389 {A : Type'} (s : A -> Prop) (x : A) : term45 A s x.
Proof. exact (@lem3609388 A s x). Qed.
Lemma lem3609399 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3609400 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term48 A s x).
Proof. exact (@lem3609399 (term44 A s x)). Qed.
Lemma lem3609402 (t : Prop) : (term49 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3609403 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (term41 A s x).
Proof. exact (@lem3609402 (term41 A s x)). Qed.
Lemma lem3609406 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term41 A s x).
Proof. exact (TRANS (@lem3609400 A s x) (@lem3609403 A s x)). Qed.
Lemma lem3609415 {A : Type'} (x : A) : (term50 A x) = (term51 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3609406 A s x)). Qed.
Lemma lem3609416 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3609417 {A : Type'} (x : A) : (term52 A x) = (term53 A x).
Proof. exact (MK_COMB (@lem3609416 A) (@lem3609415 A x)). Qed.
Lemma lem3609422 {A : Type'} : (term54 A) = (term55 A).
Proof. exact (fun_ext (fun x : A => @lem3609417 A x)). Qed.
Lemma lem3609423 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3609432 {A : Type'} : (term56 A) = (term57 A).
Proof. exact (MK_COMB (@lem3609423 A) (@lem3609422 A)). Qed.
Lemma lem3609447 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x') = (term37 A s x' x)) = ((s x') = (term37 A s x' x)).
Proof. exact (eq_refl ((s x') = (term37 A s x' x))). Qed.
Lemma lem3609448 {A : Type'} (s : A -> Prop) (x : A) : (term39 A s x) = (term39 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3609447 A s x' x)). Qed.
Lemma lem3609449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3609450 {A : Type'} (s : A -> Prop) (x : A) : (term40 A s x) = (term40 A s x).
Proof. exact (MK_COMB (@lem3609449 A) (@lem3609448 A s x)). Qed.
Lemma lem3609453 {A : Type'} (s : A -> Prop) (x : A) : (term23 A s x) = (term23 A s x).
Proof. exact (eq_refl (term23 A s x)). Qed.
Lemma lem3609454 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (term41 A s x).
Proof. exact (MK_COMB (@lem3609453 A s x) (@lem3609450 A s x)). Qed.
Lemma lem3609455 {A : Type'} (x : A) : (term51 A x) = (term51 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3609454 A s x)). Qed.
Lemma lem3609456 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3609457 {A : Type'} (x : A) : (term53 A x) = (term53 A x).
Proof. exact (MK_COMB (@lem3609456 A) (@lem3609455 A x)). Qed.
Lemma lem3609458 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (fun_ext (fun x : A => @lem3609457 A x)). Qed.
Lemma lem3609459 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3609460 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (MK_COMB (@lem3609459 A) (@lem3609458 A)). Qed.
Lemma lem3609487 {A : Type'} : (term56 A) = (term57 A).
Proof. exact (TRANS (@lem3609432 A) (@lem3609460 A)). Qed.
Lemma lem3609488 {A : Type'} : (term57 A) = (term56 A).
Proof. exact (SYM (@lem3609487 A)). Qed.
Lemma lem3609491 (p : Prop) : p = (term42 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3609492 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x') = (term37 A s x' x)) = (term58 A s x' x).
Proof. exact (@lem3609491 ((s x') = (term37 A s x' x))). Qed.
Lemma lem3609493 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term58 A s x' x) = ((s x') = (term37 A s x' x)).
Proof. exact (SYM (@lem3609492 A s x' x)). Qed.
Lemma lem3609494 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A s x' x) : term59 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3609500 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3609510 {A : Type'} (x' : A) (x : A) : (term60 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3609512 {A : Type'} (s : A -> Prop) (x' : A) : (term61 A s x') = (term61 A s x').
Proof. exact (eq_refl (term61 A s x')). Qed.
Lemma lem3609513 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term62 A s x' x) = (term63 A s x' x).
Proof. exact (MK_COMB (@lem3609512 A s x') (@lem3609510 A x' x)). Qed.
Lemma lem3609514 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term64 A s x' x) = (term62 A s x' x).
Proof. exact (@lem17045 (s x') (term34 A x' x)). Qed.
Lemma lem3609515 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term64 A s x' x) = (term63 A s x' x).
Proof. exact (TRANS (@lem3609514 A s x' x) (@lem3609513 A s x' x)). Qed.
Lemma lem3609520 {A : Type'} (x' : A) (x : A) : (term65 A x' x) = (term65 A x' x).
Proof. exact (eq_refl (term65 A x' x)). Qed.
Lemma lem3609521 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term66 A s x' x) = (term67 A s x' x).
Proof. exact (MK_COMB (@lem3609520 A x' x) (@lem3609515 A s x' x)). Qed.
Lemma lem3609522 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term68 A s x' x) = (term66 A s x' x).
Proof. exact (@lem17160 (x' = x) (term35 A s x' x)). Qed.
Lemma lem3609523 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term68 A s x' x) = (term67 A s x' x).
Proof. exact (TRANS (@lem3609522 A s x' x) (@lem3609521 A s x' x)). Qed.
Lemma lem3609529 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term69 A s x' x) = (term69 A s x' x).
Proof. exact (eq_refl (term69 A s x' x)). Qed.
Lemma lem3609531 {A : Type'} (s : A -> Prop) (x' : A) : (term33 A s x') = (term33 A s x').
Proof. exact (eq_refl (term33 A s x')). Qed.
Lemma lem3609532 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term70 A s x' x) = (term71 A s x' x).
Proof. exact (MK_COMB (@lem3609531 A s x') (@lem3609523 A s x' x)). Qed.
Lemma lem3609533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3609534 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term72 A s x' x) = (term73 A s x' x).
Proof. exact (MK_COMB (@lem3609533) (@lem3609532 A s x' x)). Qed.
Lemma lem3609535 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term74 A s x' x) = (term75 A s x' x).
Proof. exact (MK_COMB (@lem3609534 A s x' x) (@lem3609529 A s x' x)). Qed.
Lemma lem3609536 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term59 A s x' x) = (term74 A s x' x).
Proof. exact (@lem17646 (s x') (term37 A s x' x)). Qed.
Lemma lem3609541 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term59 A s x' x) = (term75 A s x' x).
Proof. exact (TRANS (@lem3609536 A s x' x) (@lem3609535 A s x' x)). Qed.
Lemma lem3609546 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3609608 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A s x' x) : term75 A s x' x.
Proof. exact (EQ_MP (@lem3609541 A s x' x) (@lem3609494 A s x' x h1)). Qed.
Lemma lem3609609 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) : term71 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3609610 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term69 A s x' x) : term69 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3609611 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) : term67 A s x' x.
Proof. exact (proj2 (@lem3609609 A s x' x h1)). Qed.
Lemma lem3609613 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) : term63 A s x' x.
Proof. exact (proj2 (@lem3609611 A s x' x h1)). Qed.
Lemma lem3609617 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term69 A s x' x) : term37 A s x' x.
Proof. exact (proj2 (@lem3609610 A s x' x h1)). Qed.
Lemma lem3609620 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term35 A s x' x) : term35 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3609638 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term76 A s x'.
Proof. exact (h1). Qed.
Lemma lem3609654 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3609658 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3609666 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3609690 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term76 A s x'.
Proof. exact (h1). Qed.
Lemma lem3609696 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) : term34 A x' x.
Proof. exact (proj1 (@lem3609611 A s x' x h1)). Qed.
Lemma lem3609698 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3609700 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3609702 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term69 A s x' x) : term76 A s x'.
Proof. exact (proj1 (@lem3609610 A s x' x h1)). Qed.
Lemma lem3609704 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3609708 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term69 A s x' x) : term76 A s x'.
Proof. exact (proj1 (@lem3609610 A s x' x h1)). Qed.
Lemma lem3609754 {A : Type'} (x : A) : (term77 A x) = (term77 A x).
Proof. exact (eq_refl (term77 A x)). Qed.
Lemma lem3609755 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term78 A x x') = (term79 A x).
Proof. exact (MK_COMB (@lem3609754 A x) (@lem3609698 A x' x h1)). Qed.
Lemma lem3609756 {A : Type'} (x : A) : (term79 A x) = (term80 A x).
Proof. exact (eq_refl (term79 A x)). Qed.
Lemma lem3609757 {A : Type'} (x : A) (x' : A) : (term81 A x x') = (term81 A x x').
Proof. exact (eq_refl (term81 A x x')). Qed.
Lemma lem3609758 {A : Type'} (x' : A) (x : A) : ((term78 A x x') = (term79 A x)) = ((term78 A x x') = (term80 A x)).
Proof. exact (MK_COMB (@lem3609757 A x x') (@lem3609756 A x)). Qed.
Lemma lem3609759 {A : Type'} (x' : A) (x : A) : (term78 A x x') = (term34 A x' x).
Proof. exact (eq_refl (term78 A x x')). Qed.
Lemma lem3609760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3609761 {A : Type'} (x' : A) (x : A) : (term81 A x x') = (term82 A x' x).
Proof. exact (MK_COMB (@lem3609760) (@lem3609759 A x' x)). Qed.
Lemma lem3609762 {A : Type'} (x : A) : (term80 A x) = (term80 A x).
Proof. exact (eq_refl (term80 A x)). Qed.
Lemma lem3609763 {A : Type'} (x' : A) (x : A) : ((term78 A x x') = (term80 A x)) = ((term34 A x' x) = (term80 A x)).
Proof. exact (MK_COMB (@lem3609761 A x' x) (@lem3609762 A x)). Qed.
Lemma lem3609764 {A : Type'} (x' : A) (x : A) : ((term78 A x x') = (term79 A x)) = ((term34 A x' x) = (term80 A x)).
Proof. exact (TRANS (@lem3609758 A x' x) (@lem3609763 A x' x)). Qed.
Lemma lem3609765 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term34 A x' x) = (term80 A x).
Proof. exact (EQ_MP (@lem3609764 A x' x) (@lem3609755 A x' x h1)). Qed.
Lemma lem3609766 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : term80 A x.
Proof. exact (EQ_MP (@lem3609765 A x' x h2) (@lem3609696 A s x' x h1)). Qed.
Lemma lem3609794 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3609795 {A : Type'} (s : A -> Prop) : (term83 A s) = (term83 A s).
Proof. exact (eq_refl (term83 A s)). Qed.
Lemma lem3609796 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term84 A s x') = (term84 A s x).
Proof. exact (MK_COMB (@lem3609795 A s) (@lem3609704 A x' x h1)). Qed.
Lemma lem3609797 {A : Type'} (s : A -> Prop) (x : A) : (term84 A s x) = (term76 A s x).
Proof. exact (eq_refl (term84 A s x)). Qed.
Lemma lem3609798 {A : Type'} (s : A -> Prop) (x' : A) : (term85 A s x') = (term85 A s x').
Proof. exact (eq_refl (term85 A s x')). Qed.
Lemma lem3609799 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term84 A s x') = (term84 A s x)) = ((term84 A s x') = (term76 A s x)).
Proof. exact (MK_COMB (@lem3609798 A s x') (@lem3609797 A s x)). Qed.
Lemma lem3609800 {A : Type'} (s : A -> Prop) (x' : A) : (term84 A s x') = (term76 A s x').
Proof. exact (eq_refl (term84 A s x')). Qed.
Lemma lem3609801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3609802 {A : Type'} (s : A -> Prop) (x' : A) : (term85 A s x') = (term86 A s x').
Proof. exact (MK_COMB (@lem3609801) (@lem3609800 A s x')). Qed.
Lemma lem3609803 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term76 A s x).
Proof. exact (eq_refl (term76 A s x)). Qed.
Lemma lem3609804 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term84 A s x') = (term76 A s x)) = ((term76 A s x') = (term76 A s x)).
Proof. exact (MK_COMB (@lem3609802 A s x') (@lem3609803 A s x)). Qed.
Lemma lem3609805 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term84 A s x') = (term84 A s x)) = ((term76 A s x') = (term76 A s x)).
Proof. exact (TRANS (@lem3609799 A x' s x) (@lem3609804 A x' s x)). Qed.
Lemma lem3609806 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term76 A s x') = (term76 A s x).
Proof. exact (EQ_MP (@lem3609805 A x' s x) (@lem3609796 A s x' x h1)). Qed.
Lemma lem3609807 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term69 A s x' x) (h2 : x' = x) : term76 A s x.
Proof. exact (EQ_MP (@lem3609806 A s x' x h2) (@lem3609702 A s x' x h1)). Qed.
Lemma lem3609823 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) : s x'.
Proof. exact (proj1 (@lem3609609 A s x' x h1)). Qed.
Lemma lem3609824 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) : term87 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3609823 A s x' x h1). Qed.
Lemma lem3609826 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609827 {A : Type'} (s : A -> Prop) (x' : A) : (term87 A s x') = (s x').
Proof. exact (@lem3609826 (s x')). Qed.
Lemma lem3609828 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3609827 A s x') (@lem3609824 A s x' x h1)). Qed.
Lemma lem3609831 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3609833 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term89 A s x').
Proof. exact (@lem3609831 (s x')). Qed.
Lemma lem3609836 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term89 A s x'.
Proof. exact (EQ_MP (@lem3609833 A s x') (@lem3609690 A s x' h1)). Qed.
Lemma lem3609839 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term71 A s x' x) : False.
Proof. exact (@lem3609836 A s x' h1 (@lem3609828 A s x' x h2)). Qed.
Lemma lem3609840 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term71 A s x' x) : term90.
Proof. exact (fun h0 : ~ False => @lem3609839 A s x' x h1 h2). Qed.
Lemma lem3609842 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609843 : term90 = False.
Proof. exact (@lem3609842 False). Qed.
Lemma lem3609844 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term71 A s x' x) : False.
Proof. exact (EQ_MP (@lem3609843) (@lem3609840 A s x' x h1 h2)). Qed.
Lemma lem3609860 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3609861 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3609860 A x). Qed.
Lemma lem3609862 {A : Type'} (x : A) : term91 A x.
Proof. exact (fun h0 : term80 A x => @lem3609861 A x). Qed.
Lemma lem3609864 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609865 {A : Type'} (x : A) : (term91 A x) = (x = x).
Proof. exact (@lem3609864 (x = x)). Qed.
Lemma lem3609866 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3609865 A x) (@lem3609862 A x)). Qed.
Lemma lem3609869 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3609871 {A : Type'} (x : A) : (term80 A x) = (term92 A x).
Proof. exact (@lem3609869 (x = x)). Qed.
Lemma lem3609874 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : term92 A x.
Proof. exact (EQ_MP (@lem3609871 A x) (@lem3609766 A s x' x h1 h2)). Qed.
Lemma lem3609877 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : False.
Proof. exact (@lem3609874 A s x' x h1 h2 (@lem3609866 A x)). Qed.
Lemma lem3609878 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : term90.
Proof. exact (fun h0 : ~ False => @lem3609877 A s x' x h1 h2). Qed.
Lemma lem3609880 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609881 : term90 = False.
Proof. exact (@lem3609880 False). Qed.
Lemma lem3609884 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3609885 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term87 A s x.
Proof. exact (fun h0 : term76 A s x => @lem3609884 A s x h1). Qed.
Lemma lem3609887 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609888 {A : Type'} (s : A -> Prop) (x : A) : (term87 A s x) = (s x).
Proof. exact (@lem3609887 (s x)). Qed.
Lemma lem3609889 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3609888 A s x) (@lem3609885 A s x h1)). Qed.
Lemma lem3609892 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3609894 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term89 A s x).
Proof. exact (@lem3609892 (s x)). Qed.
Lemma lem3609897 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term69 A s x' x) (h2 : x' = x) : term89 A s x.
Proof. exact (EQ_MP (@lem3609894 A s x) (@lem3609807 A s x' x h1 h2)). Qed.
Lemma lem3609900 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : False.
Proof. exact (@lem3609897 A s x' x h2 h3 (@lem3609889 A s x h1)). Qed.
Lemma lem3609901 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : term90.
Proof. exact (fun h0 : ~ False => @lem3609900 A s x' x h1 h2 h3). Qed.
Lemma lem3609903 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609904 : term90 = False.
Proof. exact (@lem3609903 False). Qed.
Lemma lem3609905 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609904) (@lem3609901 A s x' x h1 h2 h3)). Qed.
Lemma lem3609921 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term35 A s x' x) : s x'.
Proof. exact (proj1 (@lem3609620 A s x' x h1)). Qed.
Lemma lem3609922 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term35 A s x' x) : term87 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3609921 A s x' x h1). Qed.
Lemma lem3609924 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609925 {A : Type'} (s : A -> Prop) (x' : A) : (term87 A s x') = (s x').
Proof. exact (@lem3609924 (s x')). Qed.
Lemma lem3609926 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term35 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3609925 A s x') (@lem3609922 A s x' x h1)). Qed.
Lemma lem3609929 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3609931 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term89 A s x').
Proof. exact (@lem3609929 (s x')). Qed.
Lemma lem3609934 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term69 A s x' x) : term89 A s x'.
Proof. exact (EQ_MP (@lem3609931 A s x') (@lem3609708 A s x' x h1)). Qed.
Lemma lem3609937 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term69 A s x' x) (h2 : term35 A s x' x) : False.
Proof. exact (@lem3609934 A s x' x h1 (@lem3609926 A s x' x h2)). Qed.
Lemma lem3609938 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term69 A s x' x) (h2 : term35 A s x' x) : term90.
Proof. exact (fun h0 : ~ False => @lem3609937 A s x' x h1 h2). Qed.
Lemma lem3609940 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3609941 : term90 = False.
Proof. exact (@lem3609940 False). Qed.
Lemma lem3609942 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term69 A s x' x) (h2 : term35 A s x' x) : False.
Proof. exact (EQ_MP (@lem3609941) (@lem3609938 A s x' x h1 h2)). Qed.
Lemma lem3609943 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3609905 A s x' x h1 h2 h3) (fun h4 : False => @lem3609794 A s x h1)). Qed.
Lemma lem3609945 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609943 A s x' x h1 h2 h3) (@lem3609794 A s x h1)). Qed.
Lemma lem3609946 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609881) (@lem3609878 A s x' x h1 h2)). Qed.
Lemma lem3609947 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3609945 A s x' x h1 h2 h3) (fun h4 : False => @lem3609704 A x' x h3)). Qed.
Lemma lem3609948 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609947 A s x' x h1 h2 h3) (@lem3609704 A x' x h3)). Qed.
Lemma lem3609949 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3609948 A s x' x h1 h2 h3) (fun h4 : False => @lem3609700 A s x h1)). Qed.
Lemma lem3609950 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609949 A s x' x h1 h2 h3) (@lem3609700 A s x h1)). Qed.
Lemma lem3609951 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3609946 A s x' x h1 h2) (fun h3 : False => @lem3609698 A x' x h2)). Qed.
Lemma lem3609952 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609951 A s x' x h1 h2) (@lem3609698 A x' x h2)). Qed.
Lemma lem3609953 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term71 A s x' x) : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3609844 A s x' x h1 h2) (fun h3 : False => @lem3609690 A s x' h1)). Qed.
Lemma lem3609954 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term71 A s x' x) : False.
Proof. exact (EQ_MP (@lem3609953 A s x' x h1 h2) (@lem3609690 A s x' h1)). Qed.
Lemma lem3609955 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3609950 A s x' x h1 h2 h3) (fun h4 : False => @lem3609666 A x' x h3)). Qed.
Lemma lem3609956 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609955 A s x' x h1 h2 h3) (@lem3609666 A x' x h3)). Qed.
Lemma lem3609957 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3609956 A s x' x h1 h2 h3) (fun h4 : False => @lem3609658 A s x h1)). Qed.
Lemma lem3609958 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609957 A s x' x h1 h2 h3) (@lem3609658 A s x h1)). Qed.
Lemma lem3609959 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3609952 A s x' x h1 h2) (fun h3 : False => @lem3609654 A x' x h2)). Qed.
Lemma lem3609960 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609959 A s x' x h1 h2) (@lem3609654 A x' x h2)). Qed.
Lemma lem3609961 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term71 A s x' x) : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3609954 A s x' x h1 h2) (fun h3 : False => @lem3609638 A s x' h1)). Qed.
Lemma lem3609962 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term71 A s x' x) : False.
Proof. exact (EQ_MP (@lem3609961 A s x' x h1 h2) (@lem3609638 A s x' h1)). Qed.
Lemma lem3609963 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3609958 A s x' x h1 h2 h3) (fun h4 : False => @lem3609666 A x' x h3)). Qed.
Lemma lem3609964 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609963 A s x' x h1 h2 h3) (@lem3609666 A x' x h3)). Qed.
Lemma lem3609965 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3609964 A s x' x h1 h2 h3) (fun h4 : False => @lem3609658 A s x h1)). Qed.
Lemma lem3609966 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609965 A s x' x h1 h2 h3) (@lem3609658 A s x h1)). Qed.
Lemma lem3609967 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3609960 A s x' x h1 h2) (fun h3 : False => @lem3609654 A x' x h2)). Qed.
Lemma lem3609968 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3609967 A s x' x h1 h2) (@lem3609654 A x' x h2)). Qed.
Lemma lem3609969 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term71 A s x' x) : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3609962 A s x' x h1 h2) (fun h3 : False => @lem3609638 A s x' h1)). Qed.
Lemma lem3609970 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x') (h2 : term71 A s x' x) : False.
Proof. exact (EQ_MP (@lem3609969 A s x' x h1 h2) (@lem3609638 A s x' h1)). Qed.
Lemma lem3609971 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term69 A s x' x) : False.
Proof. exact (or_elim (@lem3609617 A s x' x h2) (fun h0 : x' = x => @lem3609966 A s x' x h1 h2 h0) (fun h0 : term35 A s x' x => @lem3609942 A s x' x h2 h0)). Qed.
Lemma lem3609972 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) : False.
Proof. exact (or_elim (@lem3609613 A s x' x h1) (fun h0 : term76 A s x' => @lem3609970 A s x' x h0 h1) (fun h0 : x' = x => @lem3609968 A s x' x h1 h0)). Qed.
Lemma lem3609973 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term59 A s x' x) (h2 : s x) : False.
Proof. exact (or_elim (@lem3609608 A s x' x h1) (fun h0 : term71 A s x' x => @lem3609972 A s x' x h0) (fun h0 : term69 A s x' x => @lem3609971 A s x' x h2 h0)). Qed.
Lemma lem3609974 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term59 A s x' x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3609973 A x' s x h1 h2) (fun h3 : False => @lem3609546 A s x h2)). Qed.
Lemma lem3609975 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term59 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3609974 A x' s x h1 h2) (@lem3609546 A s x h2)). Qed.
Lemma lem3609976 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term59 A s x' x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3609975 A x' s x h1 h2) (fun h3 : False => @lem3609500 A s x h2)). Qed.
Lemma lem3609977 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term59 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3609976 A x' s x h1 h2) (@lem3609500 A s x h2)). Qed.
Lemma lem3609978 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term59 A s x' x) (h2 : s x) : (term59 A s x' x) = False.
Proof. exact (prop_ext (fun h3 : term59 A s x' x => @lem3609977 A x' s x h1 h2) (fun h3 : False => @lem3609494 A s x' x h1)). Qed.
Lemma lem3609979 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term59 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3609978 A x' s x h1 h2) (@lem3609494 A s x' x h1)). Qed.
Lemma lem3609980 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : term58 A s x' x.
Proof. exact (fun h0 : term59 A s x' x => @lem3609979 A x' s x h0 h1). Qed.
Lemma lem3609981 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : (s x') = (term37 A s x' x).
Proof. exact (EQ_MP (@lem3609493 A s x' x) (@lem3609980 A x' s x h1)). Qed.
Lemma lem3609986 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term40 A s x.
Proof. exact (fun x' : A => @lem3609981 A x' s x h1). Qed.
Lemma lem3609987 {A : Type'} (s : A -> Prop) (x : A) : term41 A s x.
Proof. exact (fun h0 : s x => @lem3609986 A s x h0). Qed.
Lemma lem3609992 {A : Type'} (x : A) : term53 A x.
Proof. exact (fun s : A -> Prop => @lem3609987 A s x). Qed.
Lemma lem3609997 {A : Type'} : term57 A.
Proof. exact (fun x : A => @lem3609992 A x). Qed.
Lemma lem3609998 {A : Type'} : term56 A.
Proof. exact (EQ_MP (@lem3609488 A) (@lem3609997 A)). Qed.
Lemma lem3609999 {A : Type'} (x : A) : term93 A x.
Proof. exact (@lem3609998 A x). Qed.
Lemma lem3610000 {A : Type'} (x : A) : (term93 A x) = (term52 A x).
Proof. exact (eq_refl (term93 A x)). Qed.
Lemma lem3610001 {A : Type'} (x : A) : term52 A x.
Proof. exact (EQ_MP (@lem3610000 A x) (@lem3609999 A x)). Qed.
Lemma lem3610002 {A : Type'} (x : A) (s : A -> Prop) : term94 A x s.
Proof. exact (@lem3610001 A x s). Qed.
Lemma lem3610003 {A : Type'} (s : A -> Prop) (x : A) : (term94 A x s) = (term43 A s x).
Proof. exact (eq_refl (term94 A x s)). Qed.
Lemma lem3610004 {A : Type'} (s : A -> Prop) (x : A) : term43 A s x.
Proof. exact (EQ_MP (@lem3610003 A s x) (@lem3610002 A x s)). Qed.
Lemma lem3610006 {A : Type'} (s : A -> Prop) (x : A) : term43 A s x.
Proof. exact (@lem3609389 A s x (@lem3610004 A s x)). Qed.
Lemma lem3610007 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : False.
Proof. exact (@lem3610006 A s x (@lem3609373 A s x h1)). Qed.
Lemma lem3610008 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : (term44 A s x) = False.
Proof. exact (prop_ext (fun h2 : term44 A s x => @lem3610007 A s x h1) (fun h2 : False => @lem3609373 A s x h1)). Qed.
Lemma lem3610009 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : False.
Proof. exact (EQ_MP (@lem3610008 A s x h1) (@lem3609373 A s x h1)). Qed.
Lemma lem3610010 {A : Type'} (s : A -> Prop) (x : A) : term43 A s x.
Proof. exact (fun h0 : term44 A s x => @lem3610009 A s x h0). Qed.
Lemma lem3610011 {A : Type'} (s : A -> Prop) (x : A) : term41 A s x.
Proof. exact (EQ_MP (@lem3609372 A s x) (@lem3610010 A s x)). Qed.
Lemma lem3610012 {A : Type'} (s : A -> Prop) (x : A) : term22 A s x.
Proof. exact (EQ_MP (@lem3609368 A s x) (@lem3610011 A s x)). Qed.
Lemma lem3610013 {A : Type'} (s : A -> Prop) (x : A) : term21 A s x.
Proof. exact (EQ_MP (@lem3609302 A s x) (@lem3610012 A s x)). Qed.
Lemma lem3610015 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : s = (term11 A s x).
Proof. exact (@lem3610013 A s x (@lem3609237 A x s h1)). Qed.
Lemma lem3610016 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term11 A s x)) : term14 A x s.
Proof. exact (EQ_MP (@lem3609263 A s x h1) (@lem3609281 A s x)). Qed.
Lemma lem3610017 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (s = (term11 A s x)) = (term14 A x s).
Proof. exact (prop_ext (fun h2 : s = (term11 A s x) => @lem3610016 A s x h2) (fun h2 : term14 A x s => @lem3610015 A x s h1)). Qed.
Lemma lem3610018 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term14 A x s.
Proof. exact (EQ_MP (@lem3610017 A x s h1) (@lem3610015 A x s h1)). Qed.
Lemma lem3610023 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@DELETE A s x) = s) : (@DELETE A s x) = s.
Proof. exact (h1). Qed.
Lemma lem3610024 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3610025 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@DELETE A s x) = s) : (term16 A s x) = (@FINITE A s).
Proof. exact (MK_COMB (@lem3610024 A) (@lem3610023 A x s h1)). Qed.
Lemma lem3610026 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3610027 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@DELETE A s x) = s) : (term13 A s x) = (term95 A s).
Proof. exact (MK_COMB (@lem3610026) (@lem3610025 A x s h1)). Qed.
Lemma lem3610028 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3610029 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@DELETE A s x) = s) : (term14 A x s) = (term96 A s).
Proof. exact (MK_COMB (@lem3610027 A x s h1) (@lem3610028 A s)). Qed.
Lemma lem3610031 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3610032 {A : Type'} (s : A -> Prop) : (term96 A s) = True.
Proof. exact (@lem3610031 (@FINITE A s)). Qed.
Lemma lem3610033 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@DELETE A s x) = s) : (term14 A x s) = True.
Proof. exact (TRANS (@lem3610029 A x s h1) (@lem3610032 A s)). Qed.
Lemma lem3610034 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@DELETE A s x) = s) : True = (term14 A x s).
Proof. exact (SYM (@lem3610033 A x s h1)). Qed.
Lemma lem3610035 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@DELETE A s x) = s) : term14 A x s.
Proof. exact (EQ_MP (@lem3610034 A x s h1) (@lem0)). Qed.
Lemma lem3610041 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3610042 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (@lem3610041 A s t). Qed.
Lemma lem3610043 {A : Type'} (x : A) (s : A -> Prop) : ((@DELETE A s x) = s) = (term97 A x s).
Proof. exact (@lem3610042 A (@DELETE A s x) s). Qed.
Lemma lem3610052 {A : Type'} (x : A) (s : A -> Prop) : (term98 A x s) = (term98 A x s).
Proof. exact (eq_refl (term98 A x s)). Qed.
Lemma lem3610053 {A : Type'} (x : A) (s : A -> Prop) : (term99 A x s) = (term100 A x s).
Proof. exact (MK_COMB (@lem3610052 A x s) (@lem3610043 A x s)). Qed.
Lemma lem3610056 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (term99 A x s).
Proof. exact (SYM (@lem3610053 A x s)). Qed.
Lemma lem3610060 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3610061 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3610060 A P x). Qed.
Lemma lem3610062 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3610061 A s x). Qed.
Lemma lem3610063 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3610064 {A : Type'} (s : A -> Prop) (x : A) : (term6 A x s) = (term76 A s x).
Proof. exact (MK_COMB (@lem3610063) (@lem3610062 A s x)). Qed.
Lemma lem3610065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3610066 {A : Type'} (s : A -> Prop) (x : A) : (term98 A x s) = (term101 A s x).
Proof. exact (MK_COMB (@lem3610065) (@lem3610064 A s x)). Qed.
Lemma lem3610074 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term30 A x s y) = (term31 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3610075 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term30 A x s y) = (term31 A s x y).
Proof. exact (@lem3610074 A s x y). Qed.
Lemma lem3610076 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term30 A x' s x) = (term31 A s x' x).
Proof. exact (@lem3610075 A s x' x). Qed.
Lemma lem3610080 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3610081 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3610080 A P x). Qed.
Lemma lem3610082 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3610081 A s x'). Qed.
Lemma lem3610083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3610084 {A : Type'} (s : A -> Prop) (x' : A) : (term32 A x' s) = (term33 A s x').
Proof. exact (MK_COMB (@lem3610083) (@lem3610082 A s x')). Qed.
Lemma lem3610087 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3610088 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term31 A s x' x) = (term35 A s x' x).
Proof. exact (MK_COMB (@lem3610084 A s x') (@lem3610087 A x' x)). Qed.
Lemma lem3610091 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term30 A x' s x) = (term35 A s x' x).
Proof. exact (TRANS (@lem3610076 A s x' x) (@lem3610088 A s x' x)). Qed.
Lemma lem3610092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3610093 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term102 A x' s x) = (term103 A s x' x).
Proof. exact (MK_COMB (@lem3610092) (@lem3610091 A s x' x)). Qed.
Lemma lem3610095 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3610096 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3610095 A P x). Qed.
Lemma lem3610097 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3610096 A s x'). Qed.
Lemma lem3610098 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term30 A x' s x) = (@IN A x' s)) = ((term35 A s x' x) = (s x')).
Proof. exact (MK_COMB (@lem3610093 A s x' x) (@lem3610097 A s x')). Qed.
Lemma lem3610101 {A : Type'} (x : A) (s : A -> Prop) : (term104 A x s) = (term105 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3610098 A x s x')). Qed.
Lemma lem3610102 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3610103 {A : Type'} (x : A) (s : A -> Prop) : (term97 A x s) = (term106 A x s).
Proof. exact (MK_COMB (@lem3610102 A) (@lem3610101 A x s)). Qed.
Lemma lem3610108 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (term107 A x s).
Proof. exact (MK_COMB (@lem3610066 A s x) (@lem3610103 A x s)). Qed.
Lemma lem3610111 {A : Type'} (x : A) (s : A -> Prop) : (term107 A x s) = (term100 A x s).
Proof. exact (SYM (@lem3610108 A x s)). Qed.
Lemma lem3610113 (p : Prop) : p = (term42 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3610114 {A : Type'} (x : A) (s : A -> Prop) : (term107 A x s) = (term108 A x s).
Proof. exact (@lem3610113 (term107 A x s)). Qed.
Lemma lem3610115 {A : Type'} (x : A) (s : A -> Prop) : (term108 A x s) = (term107 A x s).
Proof. exact (SYM (@lem3610114 A x s)). Qed.
Lemma lem3610116 {A : Type'} (x : A) (s : A -> Prop) (h1 : term109 A x s) : term109 A x s.
Proof. exact (h1). Qed.
Lemma lem3610119 {A : Type'} (x : A) (s : A -> Prop) (h1 : term108 A x s) : term108 A x s.
Proof. exact (h1). Qed.
Lemma lem3610120 {A : Type'} (x : A) (s : A -> Prop) : term110 A x s.
Proof. exact (fun h0 : term108 A x s => @lem3610119 A x s h0). Qed.
Lemma lem3610121 {A : Type'} (x : A) (s : A -> Prop) (h1 : term110 A x s) : term110 A x s.
Proof. exact (h1). Qed.
Lemma lem3610122 {A : Type'} (x : A) (s : A -> Prop) (h1 : term108 A x s) : term108 A x s.
Proof. exact (h1). Qed.
Lemma lem3610123 {A : Type'} (x : A) (s : A -> Prop) (h1 : term108 A x s) (h2 : term110 A x s) : term108 A x s.
Proof. exact (@lem3610121 A x s h2 (@lem3610122 A x s h1)). Qed.
Lemma lem3610124 {A : Type'} (x : A) (s : A -> Prop) (h1 : term108 A x s) : term111 A x s.
Proof. exact (fun h0 : term110 A x s => @lem3610123 A x s h1 h0). Qed.
Lemma lem3610125 {A : Type'} (x : A) (s : A -> Prop) (h1 : term110 A x s) : term110 A x s.
Proof. exact (h1). Qed.
Lemma lem3610126 {A : Type'} (x : A) (s : A -> Prop) (h1 : term108 A x s) (h2 : term110 A x s) : term108 A x s.
Proof. exact (@lem3610124 A x s h1 (@lem3610125 A x s h2)). Qed.
Lemma lem3610127 {A : Type'} (x : A) (s : A -> Prop) (h1 : term110 A x s) : term110 A x s.
Proof. exact (fun h0 : term108 A x s => @lem3610126 A x s h0 h1). Qed.
Lemma lem3610128 {A : Type'} (x : A) (s : A -> Prop) : term112 A x s.
Proof. exact (fun h0 : term110 A x s => @lem3610127 A x s h0). Qed.
Lemma lem3610131 {A : Type'} (x : A) (s : A -> Prop) : term110 A x s.
Proof. exact (@lem3610128 A x s (@lem3610120 A x s)). Qed.
Lemma lem3610132 {A : Type'} (x : A) (s : A -> Prop) : term110 A x s.
Proof. exact (@lem3610131 A x s). Qed.
Lemma lem3610142 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3610143 {A : Type'} (x : A) (s : A -> Prop) : (term108 A x s) = (term113 A x s).
Proof. exact (@lem3610142 (term109 A x s)). Qed.
Lemma lem3610145 (t : Prop) : (term49 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3610146 {A : Type'} (x : A) (s : A -> Prop) : (term113 A x s) = (term107 A x s).
Proof. exact (@lem3610145 (term107 A x s)). Qed.
Lemma lem3610149 {A : Type'} (x : A) (s : A -> Prop) : (term108 A x s) = (term107 A x s).
Proof. exact (TRANS (@lem3610143 A x s) (@lem3610146 A x s)). Qed.
Lemma lem3610156 {A : Type'} (s : A -> Prop) : (term114 A s) = (term115 A s).
Proof. exact (fun_ext (fun x : A => @lem3610149 A x s)). Qed.
Lemma lem3610157 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3610158 {A : Type'} (s : A -> Prop) : (term116 A s) = (term117 A s).
Proof. exact (MK_COMB (@lem3610157 A) (@lem3610156 A s)). Qed.
Lemma lem3610163 {A : Type'} : (term118 A) = (term119 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3610158 A s)). Qed.
Lemma lem3610164 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3610173 {A : Type'} : (term120 A) = (term121 A).
Proof. exact (MK_COMB (@lem3610164 A) (@lem3610163 A)). Qed.
Lemma lem3610184 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term35 A s x' x) = (s x')) = ((term35 A s x' x) = (s x')).
Proof. exact (eq_refl ((term35 A s x' x) = (s x'))). Qed.
Lemma lem3610185 {A : Type'} (x : A) (s : A -> Prop) : (term105 A x s) = (term105 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3610184 A x s x')). Qed.
Lemma lem3610186 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3610187 {A : Type'} (x : A) (s : A -> Prop) : (term106 A x s) = (term106 A x s).
Proof. exact (MK_COMB (@lem3610186 A) (@lem3610185 A x s)). Qed.
Lemma lem3610192 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (term101 A s x).
Proof. exact (eq_refl (term101 A s x)). Qed.
Lemma lem3610193 {A : Type'} (x : A) (s : A -> Prop) : (term107 A x s) = (term107 A x s).
Proof. exact (MK_COMB (@lem3610192 A s x) (@lem3610187 A x s)). Qed.
Lemma lem3610194 {A : Type'} (s : A -> Prop) : (term115 A s) = (term115 A s).
Proof. exact (fun_ext (fun x : A => @lem3610193 A x s)). Qed.
Lemma lem3610195 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3610196 {A : Type'} (s : A -> Prop) : (term117 A s) = (term117 A s).
Proof. exact (MK_COMB (@lem3610195 A) (@lem3610194 A s)). Qed.
Lemma lem3610197 {A : Type'} : (term119 A) = (term119 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3610196 A s)). Qed.
Lemma lem3610198 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3610199 {A : Type'} : (term121 A) = (term121 A).
Proof. exact (MK_COMB (@lem3610198 A) (@lem3610197 A)). Qed.
Lemma lem3610224 {A : Type'} : (term120 A) = (term121 A).
Proof. exact (TRANS (@lem3610173 A) (@lem3610199 A)). Qed.
Lemma lem3610225 {A : Type'} : (term121 A) = (term120 A).
Proof. exact (SYM (@lem3610224 A)). Qed.
Lemma lem3610228 (p : Prop) : p = (term42 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3610229 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term35 A s x' x) = (s x')) = (term122 A x s x').
Proof. exact (@lem3610228 ((term35 A s x' x) = (s x'))). Qed.
Lemma lem3610230 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term122 A x s x') = ((term35 A s x' x) = (s x')).
Proof. exact (SYM (@lem3610229 A x s x')). Qed.
Lemma lem3610231 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term123 A x s x') : term123 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3610237 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term76 A s x.
Proof. exact (h1). Qed.
Lemma lem3610243 {A : Type'} (x' : A) (x : A) : (term60 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3610245 {A : Type'} (s : A -> Prop) (x' : A) : (term61 A s x') = (term61 A s x').
Proof. exact (eq_refl (term61 A s x')). Qed.
Lemma lem3610246 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term62 A s x' x) = (term63 A s x' x).
Proof. exact (MK_COMB (@lem3610245 A s x') (@lem3610243 A x' x)). Qed.
Lemma lem3610247 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term64 A s x' x) = (term62 A s x' x).
Proof. exact (@lem17045 (s x') (term34 A x' x)). Qed.
Lemma lem3610248 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term64 A s x' x) = (term63 A s x' x).
Proof. exact (TRANS (@lem3610247 A s x' x) (@lem3610246 A s x' x)). Qed.
Lemma lem3610253 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem3610254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3610255 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term124 A s x' x) = (term125 A s x' x).
Proof. exact (MK_COMB (@lem3610254) (@lem3610248 A s x' x)). Qed.
Lemma lem3610256 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term126 A x s x') = (term127 A x s x').
Proof. exact (MK_COMB (@lem3610255 A s x' x) (@lem3610253 A s x')). Qed.
Lemma lem3610261 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term128 A x s x') = (term128 A x s x').
Proof. exact (eq_refl (term128 A x s x')). Qed.
Lemma lem3610262 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term129 A x s x') = (term130 A x s x').
Proof. exact (MK_COMB (@lem3610261 A x s x') (@lem3610256 A x s x')). Qed.
Lemma lem3610263 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term123 A x s x') = (term129 A x s x').
Proof. exact (@lem17646 (term35 A s x' x) (s x')). Qed.
Lemma lem3610268 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term123 A x s x') = (term130 A x s x').
Proof. exact (TRANS (@lem3610263 A x s x') (@lem3610262 A x s x')). Qed.
Lemma lem3610275 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term76 A s x.
Proof. exact (h1). Qed.
Lemma lem3610319 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term123 A x s x') : term130 A x s x'.
Proof. exact (EQ_MP (@lem3610268 A x s x') (@lem3610231 A x s x' h1)). Qed.
Lemma lem3610320 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term131 A x s x') : term131 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3610321 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term127 A x s x') : term127 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3610323 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term131 A x s x') : term35 A s x' x.
Proof. exact (proj1 (@lem3610320 A x s x' h1)). Qed.
Lemma lem3610327 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term127 A x s x') : term63 A s x' x.
Proof. exact (proj1 (@lem3610321 A x s x' h1)). Qed.
Lemma lem3610357 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term76 A s x'.
Proof. exact (h1). Qed.
Lemma lem3610361 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term76 A s x.
Proof. exact (h1). Qed.
Lemma lem3610369 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3610373 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term131 A x s x') : term76 A s x'.
Proof. exact (proj2 (@lem3610320 A x s x' h1)). Qed.
Lemma lem3610383 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term76 A s x'.
Proof. exact (h1). Qed.
Lemma lem3610385 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term76 A s x.
Proof. exact (h1). Qed.
Lemma lem3610387 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term127 A x s x') : s x'.
Proof. exact (proj2 (@lem3610321 A x s x' h1)). Qed.
Lemma lem3610389 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3610417 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term76 A s x.
Proof. exact (h1). Qed.
Lemma lem3610418 {A : Type'} (s : A -> Prop) : (term132 A s) = (term132 A s).
Proof. exact (eq_refl (term132 A s)). Qed.
Lemma lem3610419 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term133 A s x') = (term133 A s x).
Proof. exact (MK_COMB (@lem3610418 A s) (@lem3610389 A x' x h1)). Qed.
Lemma lem3610420 {A : Type'} (s : A -> Prop) (x : A) : (term133 A s x) = (s x).
Proof. exact (eq_refl (term133 A s x)). Qed.
Lemma lem3610421 {A : Type'} (s : A -> Prop) (x' : A) : (term134 A s x') = (term134 A s x').
Proof. exact (eq_refl (term134 A s x')). Qed.
Lemma lem3610422 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term133 A s x') = (term133 A s x)) = ((term133 A s x') = (s x)).
Proof. exact (MK_COMB (@lem3610421 A s x') (@lem3610420 A s x)). Qed.
Lemma lem3610423 {A : Type'} (s : A -> Prop) (x' : A) : (term133 A s x') = (s x').
Proof. exact (eq_refl (term133 A s x')). Qed.
Lemma lem3610424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3610425 {A : Type'} (s : A -> Prop) (x' : A) : (term134 A s x') = (term25 A s x').
Proof. exact (MK_COMB (@lem3610424) (@lem3610423 A s x')). Qed.
Lemma lem3610426 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3610427 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term133 A s x') = (s x)) = ((s x') = (s x)).
Proof. exact (MK_COMB (@lem3610425 A s x') (@lem3610426 A s x)). Qed.
Lemma lem3610428 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term133 A s x') = (term133 A s x)) = ((s x') = (s x)).
Proof. exact (TRANS (@lem3610422 A x' s x) (@lem3610427 A x' s x)). Qed.
Lemma lem3610429 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (s x') = (s x).
Proof. exact (EQ_MP (@lem3610428 A x' s x) (@lem3610419 A s x' x h1)). Qed.
Lemma lem3610446 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term131 A x s x') : s x'.
Proof. exact (proj1 (@lem3610323 A x s x' h1)). Qed.
Lemma lem3610447 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term131 A x s x') : term87 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3610446 A x s x' h1). Qed.
Lemma lem3610449 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3610450 {A : Type'} (s : A -> Prop) (x' : A) : (term87 A s x') = (s x').
Proof. exact (@lem3610449 (s x')). Qed.
Lemma lem3610451 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term131 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3610450 A s x') (@lem3610447 A x s x' h1)). Qed.
Lemma lem3610454 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3610456 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term89 A s x').
Proof. exact (@lem3610454 (s x')). Qed.
Lemma lem3610459 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term131 A x s x') : term89 A s x'.
Proof. exact (EQ_MP (@lem3610456 A s x') (@lem3610373 A x s x' h1)). Qed.
Lemma lem3610462 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term131 A x s x') : False.
Proof. exact (@lem3610459 A x s x' h1 (@lem3610451 A x s x' h1)). Qed.
Lemma lem3610463 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term131 A x s x') : term90.
Proof. exact (fun h0 : ~ False => @lem3610462 A x s x' h1). Qed.
Lemma lem3610465 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3610466 : term90 = False.
Proof. exact (@lem3610465 False). Qed.
Lemma lem3610467 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term131 A x s x') : False.
Proof. exact (EQ_MP (@lem3610466) (@lem3610463 A x s x' h1)). Qed.
Lemma lem3610469 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term127 A x s x') : s x'.
Proof. exact (proj2 (@lem3610321 A x s x' h1)). Qed.
Lemma lem3610470 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term127 A x s x') : term87 A s x'.
Proof. exact (fun h0 : term76 A s x' => @lem3610469 A x s x' h1). Qed.
Lemma lem3610472 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3610473 {A : Type'} (s : A -> Prop) (x' : A) : (term87 A s x') = (s x').
Proof. exact (@lem3610472 (s x')). Qed.
Lemma lem3610474 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term127 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3610473 A s x') (@lem3610470 A x s x' h1)). Qed.
Lemma lem3610477 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3610479 {A : Type'} (s : A -> Prop) (x' : A) : (term76 A s x') = (term89 A s x').
Proof. exact (@lem3610477 (s x')). Qed.
Lemma lem3610482 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term76 A s x') : term89 A s x'.
Proof. exact (EQ_MP (@lem3610479 A s x') (@lem3610383 A s x' h1)). Qed.
Lemma lem3610485 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term127 A x s x') : False.
Proof. exact (@lem3610482 A s x' h1 (@lem3610474 A x s x' h2)). Qed.
Lemma lem3610486 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term127 A x s x') : term90.
Proof. exact (fun h0 : ~ False => @lem3610485 A x s x' h1 h2). Qed.
Lemma lem3610488 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3610489 : term90 = False.
Proof. exact (@lem3610488 False). Qed.
Lemma lem3610490 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term127 A x s x') : False.
Proof. exact (EQ_MP (@lem3610489) (@lem3610486 A x s x' h1 h2)). Qed.
Lemma lem3610492 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term127 A x s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3610429 A s x' x h2) (@lem3610387 A x s x' h1)). Qed.
Lemma lem3610493 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term127 A x s x') (h2 : x' = x) : term87 A s x.
Proof. exact (fun h0 : term76 A s x => @lem3610492 A s x' x h1 h2). Qed.
Lemma lem3610495 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3610496 {A : Type'} (s : A -> Prop) (x : A) : (term87 A s x) = (s x).
Proof. exact (@lem3610495 (s x)). Qed.
Lemma lem3610497 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term127 A x s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3610496 A s x) (@lem3610493 A s x' x h1 h2)). Qed.
Lemma lem3610500 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3610502 {A : Type'} (s : A -> Prop) (x : A) : (term76 A s x) = (term89 A s x).
Proof. exact (@lem3610500 (s x)). Qed.
Lemma lem3610505 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term89 A s x.
Proof. exact (EQ_MP (@lem3610502 A s x) (@lem3610417 A s x h1)). Qed.
Lemma lem3610508 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : False.
Proof. exact (@lem3610505 A s x h1 (@lem3610497 A s x' x h2 h3)). Qed.
Lemma lem3610509 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : term90.
Proof. exact (fun h0 : ~ False => @lem3610508 A s x' x h1 h2 h3). Qed.
Lemma lem3610511 (p : Prop) : (term88 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3610512 : term90 = False.
Proof. exact (@lem3610511 False). Qed.
Lemma lem3610513 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3610512) (@lem3610509 A s x' x h1 h2 h3)). Qed.
Lemma lem3610514 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : (term76 A s x) = False.
Proof. exact (prop_ext (fun h4 : term76 A s x => @lem3610513 A s x' x h1 h2 h3) (fun h4 : False => @lem3610417 A s x h1)). Qed.
Lemma lem3610516 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3610514 A s x' x h1 h2 h3) (@lem3610417 A s x h1)). Qed.
Lemma lem3610517 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3610516 A s x' x h1 h2 h3) (fun h4 : False => @lem3610389 A x' x h3)). Qed.
Lemma lem3610518 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3610517 A s x' x h1 h2 h3) (@lem3610389 A x' x h3)). Qed.
Lemma lem3610519 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : (term76 A s x) = False.
Proof. exact (prop_ext (fun h4 : term76 A s x => @lem3610518 A s x' x h1 h2 h3) (fun h4 : False => @lem3610385 A s x h1)). Qed.
Lemma lem3610520 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3610519 A s x' x h1 h2 h3) (@lem3610385 A s x h1)). Qed.
Lemma lem3610521 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term127 A x s x') : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3610490 A x s x' h1 h2) (fun h3 : False => @lem3610383 A s x' h1)). Qed.
Lemma lem3610522 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term127 A x s x') : False.
Proof. exact (EQ_MP (@lem3610521 A x s x' h1 h2) (@lem3610383 A s x' h1)). Qed.
Lemma lem3610523 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3610520 A s x' x h1 h2 h3) (fun h4 : False => @lem3610369 A x' x h3)). Qed.
Lemma lem3610524 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3610523 A s x' x h1 h2 h3) (@lem3610369 A x' x h3)). Qed.
Lemma lem3610525 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : (term76 A s x) = False.
Proof. exact (prop_ext (fun h4 : term76 A s x => @lem3610524 A s x' x h1 h2 h3) (fun h4 : False => @lem3610361 A s x h1)). Qed.
Lemma lem3610526 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3610525 A s x' x h1 h2 h3) (@lem3610361 A s x h1)). Qed.
Lemma lem3610527 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term127 A x s x') : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3610522 A x s x' h1 h2) (fun h3 : False => @lem3610357 A s x' h1)). Qed.
Lemma lem3610528 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term127 A x s x') : False.
Proof. exact (EQ_MP (@lem3610527 A x s x' h1 h2) (@lem3610357 A s x' h1)). Qed.
Lemma lem3610529 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3610526 A s x' x h1 h2 h3) (fun h4 : False => @lem3610369 A x' x h3)). Qed.
Lemma lem3610530 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3610529 A s x' x h1 h2 h3) (@lem3610369 A x' x h3)). Qed.
Lemma lem3610531 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : (term76 A s x) = False.
Proof. exact (prop_ext (fun h4 : term76 A s x => @lem3610530 A s x' x h1 h2 h3) (fun h4 : False => @lem3610361 A s x h1)). Qed.
Lemma lem3610532 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term76 A s x) (h2 : term127 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3610531 A s x' x h1 h2 h3) (@lem3610361 A s x h1)). Qed.
Lemma lem3610533 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term127 A x s x') : (term76 A s x') = False.
Proof. exact (prop_ext (fun h3 : term76 A s x' => @lem3610528 A x s x' h1 h2) (fun h3 : False => @lem3610357 A s x' h1)). Qed.
Lemma lem3610534 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x') (h2 : term127 A x s x') : False.
Proof. exact (EQ_MP (@lem3610533 A x s x' h1 h2) (@lem3610357 A s x' h1)). Qed.
Lemma lem3610535 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term127 A x s x') : False.
Proof. exact (or_elim (@lem3610327 A x s x' h2) (fun h0 : term76 A s x' => @lem3610534 A x s x' h0 h2) (fun h0 : x' = x => @lem3610532 A s x' x h1 h2 h0)). Qed.
Lemma lem3610536 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term123 A x s x') : False.
Proof. exact (or_elim (@lem3610319 A x s x' h2) (fun h0 : term131 A x s x' => @lem3610467 A x s x' h0) (fun h0 : term127 A x s x' => @lem3610535 A x s x' h1 h0)). Qed.
Lemma lem3610537 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term123 A x s x') : (term76 A s x) = False.
Proof. exact (prop_ext (fun h3 : term76 A s x => @lem3610536 A x s x' h1 h2) (fun h3 : False => @lem3610275 A s x h1)). Qed.
Lemma lem3610538 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term123 A x s x') : False.
Proof. exact (EQ_MP (@lem3610537 A x s x' h1 h2) (@lem3610275 A s x h1)). Qed.
Lemma lem3610539 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term123 A x s x') : (term76 A s x) = False.
Proof. exact (prop_ext (fun h3 : term76 A s x => @lem3610538 A x s x' h1 h2) (fun h3 : False => @lem3610237 A s x h1)). Qed.
Lemma lem3610540 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term123 A x s x') : False.
Proof. exact (EQ_MP (@lem3610539 A x s x' h1 h2) (@lem3610237 A s x h1)). Qed.
Lemma lem3610541 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term123 A x s x') : (term123 A x s x') = False.
Proof. exact (prop_ext (fun h3 : term123 A x s x' => @lem3610540 A x s x' h1 h2) (fun h3 : False => @lem3610231 A x s x' h2)). Qed.
Lemma lem3610542 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term76 A s x) (h2 : term123 A x s x') : False.
Proof. exact (EQ_MP (@lem3610541 A x s x' h1 h2) (@lem3610231 A x s x' h2)). Qed.
Lemma lem3610543 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term76 A s x) : term122 A x s x'.
Proof. exact (fun h0 : term123 A x s x' => @lem3610542 A x s x' h1 h0). Qed.
Lemma lem3610544 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term76 A s x) : (term35 A s x' x) = (s x').
Proof. exact (EQ_MP (@lem3610230 A x s x') (@lem3610543 A x' s x h1)). Qed.
Lemma lem3610549 {A : Type'} (s : A -> Prop) (x : A) (h1 : term76 A s x) : term106 A x s.
Proof. exact (fun x' : A => @lem3610544 A x' s x h1). Qed.
Lemma lem3610550 {A : Type'} (x : A) (s : A -> Prop) : term107 A x s.
Proof. exact (fun h0 : term76 A s x => @lem3610549 A s x h0). Qed.
Lemma lem3610555 {A : Type'} (s : A -> Prop) : term117 A s.
Proof. exact (fun x : A => @lem3610550 A x s). Qed.
Lemma lem3610560 {A : Type'} : term121 A.
Proof. exact (fun s : A -> Prop => @lem3610555 A s). Qed.
Lemma lem3610561 {A : Type'} : term120 A.
Proof. exact (EQ_MP (@lem3610225 A) (@lem3610560 A)). Qed.
Lemma lem3610562 {A : Type'} (s : A -> Prop) : term135 A s.
Proof. exact (@lem3610561 A s). Qed.
Lemma lem3610563 {A : Type'} (s : A -> Prop) : (term135 A s) = (term116 A s).
Proof. exact (eq_refl (term135 A s)). Qed.
Lemma lem3610564 {A : Type'} (s : A -> Prop) : term116 A s.
Proof. exact (EQ_MP (@lem3610563 A s) (@lem3610562 A s)). Qed.
Lemma lem3610565 {A : Type'} (s : A -> Prop) (x : A) : term136 A s x.
Proof. exact (@lem3610564 A s x). Qed.
Lemma lem3610566 {A : Type'} (x : A) (s : A -> Prop) : (term136 A s x) = (term108 A x s).
Proof. exact (eq_refl (term136 A s x)). Qed.
Lemma lem3610567 {A : Type'} (x : A) (s : A -> Prop) : term108 A x s.
Proof. exact (EQ_MP (@lem3610566 A x s) (@lem3610565 A s x)). Qed.
Lemma lem3610569 {A : Type'} (x : A) (s : A -> Prop) : term108 A x s.
Proof. exact (@lem3610132 A x s (@lem3610567 A x s)). Qed.
Lemma lem3610570 {A : Type'} (x : A) (s : A -> Prop) (h1 : term109 A x s) : False.
Proof. exact (@lem3610569 A x s (@lem3610116 A x s h1)). Qed.
Lemma lem3610571 {A : Type'} (x : A) (s : A -> Prop) (h1 : term109 A x s) : (term109 A x s) = False.
Proof. exact (prop_ext (fun h2 : term109 A x s => @lem3610570 A x s h1) (fun h2 : False => @lem3610116 A x s h1)). Qed.
Lemma lem3610572 {A : Type'} (x : A) (s : A -> Prop) (h1 : term109 A x s) : False.
Proof. exact (EQ_MP (@lem3610571 A x s h1) (@lem3610116 A x s h1)). Qed.
Lemma lem3610573 {A : Type'} (x : A) (s : A -> Prop) : term108 A x s.
Proof. exact (fun h0 : term109 A x s => @lem3610572 A x s h0). Qed.
Lemma lem3610574 {A : Type'} (x : A) (s : A -> Prop) : term107 A x s.
Proof. exact (EQ_MP (@lem3610115 A x s) (@lem3610573 A x s)). Qed.
Lemma lem3610575 {A : Type'} (x : A) (s : A -> Prop) : term100 A x s.
Proof. exact (EQ_MP (@lem3610111 A x s) (@lem3610574 A x s)). Qed.
Lemma lem3610576 {A : Type'} (x : A) (s : A -> Prop) : term99 A x s.
Proof. exact (EQ_MP (@lem3610056 A x s) (@lem3610575 A x s)). Qed.
Lemma lem3610577 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : (@DELETE A s x) = s.
Proof. exact (@lem3610576 A x s (@lem3609238 A x s h1)). Qed.
Lemma lem3610578 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : ((@DELETE A s x) = s) = (term14 A x s).
Proof. exact (prop_ext (fun h2 : (@DELETE A s x) = s => @lem3610035 A x s h2) (fun h2 : term14 A x s => @lem3610577 A x s h1)). Qed.
Lemma lem3610579 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : term14 A x s.
Proof. exact (EQ_MP (@lem3610578 A x s h1) (@lem3610577 A x s h1)). Qed.
Lemma lem3610581 {A : Type'} (x : A) (s : A -> Prop) : term14 A x s.
Proof. exact (or_elim (@lem3609236 A x s) (fun h0 : @IN A x s => @lem3610018 A x s h0) (fun h0 : term6 A x s => @lem3610579 A x s h0)). Qed.
Lemma lem3610582 {A : Type'} (s : A -> Prop) (x : A) : term137 A s x.
Proof. exact (conj (@lem3610581 A x s) (@lem3609255 A s x)). Qed.
Lemma lem3610583 {A : Type'} (x : A) (s : A -> Prop) : (term137 A s x) = ((term16 A s x) = (@FINITE A s)).
Proof. exact (@lem32 (term16 A s x) (@FINITE A s)). Qed.
Lemma lem3610584 {A : Type'} (x : A) (s : A -> Prop) : (term16 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3610583 A x s) (@lem3610582 A s x)). Qed.
Lemma lem3610589 {A : Type'} (s : A -> Prop) : term138 A s.
Proof. exact (fun x : A => @lem3610584 A x s). Qed.
Lemma lem3610594 {A : Type'} : term139 A.
Proof. exact (fun s : A -> Prop => @lem3610589 A s). Qed.
