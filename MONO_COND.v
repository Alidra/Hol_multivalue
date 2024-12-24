Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONO_COND_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm7_spec.
Lemma lem13263 (b : Prop) : term0 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem13264 (b : Prop) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem13265 (b : Prop) : term1 b.
Proof. exact (EQ_MP (@lem13264 b) (@lem13263 b)). Qed.
Lemma lem13266 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem13267 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem13268 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term2 A B C D) : term2 A B C D.
Proof. exact (h1). Qed.
Lemma lem13269 (C : Prop) (D : Prop) (h1 : C -> D) : C -> D.
Proof. exact (h1). Qed.
Lemma lem13270 (A : Prop) (B : Prop) (h1 : A -> B) : A -> B.
Proof. exact (h1). Qed.
Lemma lem13271 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : (term3 A C B D) = (term3 A C B D).
Proof. exact (eq_refl (term3 A C B D)). Qed.
Lemma lem13272 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (b : Prop) (h1 : b = True) : (term4 A C B D b) = (term5 A C B D).
Proof. exact (MK_COMB (@lem13271 A C B D) (@lem13266 b h1)). Qed.
Lemma lem13273 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : (term5 A C B D) = (term6 A C B D).
Proof. exact (eq_refl (term5 A C B D)). Qed.
Lemma lem13274 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (b : Prop) : (term7 A C B D b) = (term7 A C B D b).
Proof. exact (eq_refl (term7 A C B D b)). Qed.
Lemma lem13275 (b : Prop) (A : Prop) (C : Prop) (B : Prop) (D : Prop) : ((term4 A C B D b) = (term5 A C B D)) = ((term4 A C B D b) = (term6 A C B D)).
Proof. exact (MK_COMB (@lem13274 A C B D b) (@lem13273 A C B D)). Qed.
Lemma lem13276 (A : Prop) (C : Prop) (b : Prop) (B : Prop) (D : Prop) : (term4 A C B D b) = (term8 A C b B D).
Proof. exact (eq_refl (term4 A C B D b)). Qed.
Lemma lem13277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13278 (A : Prop) (C : Prop) (b : Prop) (B : Prop) (D : Prop) : (term7 A C B D b) = (term9 A C b B D).
Proof. exact (MK_COMB (@lem13277) (@lem13276 A C b B D)). Qed.
Lemma lem13279 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : (term6 A C B D) = (term6 A C B D).
Proof. exact (eq_refl (term6 A C B D)). Qed.
Lemma lem13280 (b : Prop) (A : Prop) (C : Prop) (B : Prop) (D : Prop) : ((term4 A C B D b) = (term6 A C B D)) = ((term8 A C b B D) = (term6 A C B D)).
Proof. exact (MK_COMB (@lem13278 A C b B D) (@lem13279 A C B D)). Qed.
Lemma lem13281 (b : Prop) (A : Prop) (C : Prop) (B : Prop) (D : Prop) : ((term4 A C B D b) = (term5 A C B D)) = ((term8 A C b B D) = (term6 A C B D)).
Proof. exact (TRANS (@lem13275 b A C B D) (@lem13280 b A C B D)). Qed.
Lemma lem13282 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (b : Prop) (h1 : b = True) : (term8 A C b B D) = (term6 A C B D).
Proof. exact (EQ_MP (@lem13281 b A C B D) (@lem13272 A C B D b h1)). Qed.
Lemma lem13283 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (b : Prop) (h1 : b = True) : (term6 A C B D) = (term8 A C b B D).
Proof. exact (SYM (@lem13282 A C B D b h1)). Qed.
Lemma lem13284 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : (term3 A C B D) = (term3 A C B D).
Proof. exact (eq_refl (term3 A C B D)). Qed.
Lemma lem13285 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (b : Prop) (h1 : b = False) : (term4 A C B D b) = (term10 A C B D).
Proof. exact (MK_COMB (@lem13284 A C B D) (@lem13267 b h1)). Qed.
Lemma lem13286 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : (term10 A C B D) = (term11 A C B D).
Proof. exact (eq_refl (term10 A C B D)). Qed.
Lemma lem13287 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (b : Prop) : (term7 A C B D b) = (term7 A C B D b).
Proof. exact (eq_refl (term7 A C B D b)). Qed.
Lemma lem13288 (b : Prop) (A : Prop) (C : Prop) (B : Prop) (D : Prop) : ((term4 A C B D b) = (term10 A C B D)) = ((term4 A C B D b) = (term11 A C B D)).
Proof. exact (MK_COMB (@lem13287 A C B D b) (@lem13286 A C B D)). Qed.
Lemma lem13289 (A : Prop) (C : Prop) (b : Prop) (B : Prop) (D : Prop) : (term4 A C B D b) = (term8 A C b B D).
Proof. exact (eq_refl (term4 A C B D b)). Qed.
Lemma lem13290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13291 (A : Prop) (C : Prop) (b : Prop) (B : Prop) (D : Prop) : (term7 A C B D b) = (term9 A C b B D).
Proof. exact (MK_COMB (@lem13290) (@lem13289 A C b B D)). Qed.
Lemma lem13292 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : (term11 A C B D) = (term11 A C B D).
Proof. exact (eq_refl (term11 A C B D)). Qed.
Lemma lem13293 (b : Prop) (A : Prop) (C : Prop) (B : Prop) (D : Prop) : ((term4 A C B D b) = (term11 A C B D)) = ((term8 A C b B D) = (term11 A C B D)).
Proof. exact (MK_COMB (@lem13291 A C b B D) (@lem13292 A C B D)). Qed.
Lemma lem13294 (b : Prop) (A : Prop) (C : Prop) (B : Prop) (D : Prop) : ((term4 A C B D b) = (term10 A C B D)) = ((term8 A C b B D) = (term11 A C B D)).
Proof. exact (TRANS (@lem13288 b A C B D) (@lem13293 b A C B D)). Qed.
Lemma lem13295 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (b : Prop) (h1 : b = False) : (term8 A C b B D) = (term11 A C B D).
Proof. exact (EQ_MP (@lem13294 b A C B D) (@lem13285 A C B D b h1)). Qed.
Lemma lem13296 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (b : Prop) (h1 : b = False) : (term11 A C B D) = (term8 A C b B D).
Proof. exact (SYM (@lem13295 A C B D b h1)). Qed.
Lemma lem13297 (A : Prop) (B : Prop) : (A -> B) = ((A -> B) = True).
Proof. exact (@lem7 (A -> B)). Qed.
Lemma lem13304 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem13305 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem13304 Prop t2 t1). Qed.
Lemma lem13306 (C : Prop) (A : Prop) : (@COND Prop True A C) = A.
Proof. exact (@lem13305 C A). Qed.
Lemma lem13307 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem13308 (C : Prop) (A : Prop) : (term12 A C) = (imp A).
Proof. exact (MK_COMB (@lem13307) (@lem13306 C A)). Qed.
Lemma lem13310 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem13311 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem13310 Prop t2 t1). Qed.
Lemma lem13312 (D : Prop) (B : Prop) : (@COND Prop True B D) = B.
Proof. exact (@lem13311 D B). Qed.
Lemma lem13313 (C : Prop) (D : Prop) (A : Prop) (B : Prop) : (term6 A C B D) = (A -> B).
Proof. exact (MK_COMB (@lem13308 C A) (@lem13312 D B)). Qed.
Lemma lem13315 (A : Prop) (B : Prop) (h1 : A -> B) : (A -> B) = True.
Proof. exact (EQ_MP (@lem13297 A B) (@lem13270 A B h1)). Qed.
Lemma lem13316 (C : Prop) (D : Prop) (A : Prop) (B : Prop) (h1 : A -> B) : (term6 A C B D) = True.
Proof. exact (TRANS (@lem13313 C D A B) (@lem13315 A B h1)). Qed.
Lemma lem13317 (C : Prop) (D : Prop) (A : Prop) (B : Prop) (h1 : A -> B) : True = (term6 A C B D).
Proof. exact (SYM (@lem13316 C D A B h1)). Qed.
Lemma lem13318 (C : Prop) (D : Prop) (A : Prop) (B : Prop) (h1 : A -> B) : term6 A C B D.
Proof. exact (EQ_MP (@lem13317 C D A B h1) (@lem0)). Qed.
Lemma lem13321 (C : Prop) (D : Prop) : (C -> D) = ((C -> D) = True).
Proof. exact (@lem7 (C -> D)). Qed.
Lemma lem13326 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem13327 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem13326 Prop t1 t2). Qed.
Lemma lem13328 (A : Prop) (C : Prop) : (@COND Prop False A C) = C.
Proof. exact (@lem13327 A C). Qed.
Lemma lem13329 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem13330 (A : Prop) (C : Prop) : (term13 A C) = (imp C).
Proof. exact (MK_COMB (@lem13329) (@lem13328 A C)). Qed.
Lemma lem13332 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem13333 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem13332 Prop t1 t2). Qed.
Lemma lem13334 (B : Prop) (D : Prop) : (@COND Prop False B D) = D.
Proof. exact (@lem13333 B D). Qed.
Lemma lem13335 (A : Prop) (B : Prop) (C : Prop) (D : Prop) : (term11 A C B D) = (C -> D).
Proof. exact (MK_COMB (@lem13330 A C) (@lem13334 B D)). Qed.
Lemma lem13337 (C : Prop) (D : Prop) (h1 : C -> D) : (C -> D) = True.
Proof. exact (EQ_MP (@lem13321 C D) (@lem13269 C D h1)). Qed.
Lemma lem13338 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : C -> D) : (term11 A C B D) = True.
Proof. exact (TRANS (@lem13335 A B C D) (@lem13337 C D h1)). Qed.
Lemma lem13339 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : C -> D) : True = (term11 A C B D).
Proof. exact (SYM (@lem13338 A B C D h1)). Qed.
Lemma lem13340 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : C -> D) : term11 A C B D.
Proof. exact (EQ_MP (@lem13339 A B C D h1) (@lem0)). Qed.
Lemma lem13341 (A : Prop) (B : Prop) (b : Prop) (C : Prop) (D : Prop) (h1 : b = False) (h2 : C -> D) : term8 A C b B D.
Proof. exact (EQ_MP (@lem13296 A C B D b h1) (@lem13340 A B C D h2)). Qed.
Lemma lem13342 (C : Prop) (D : Prop) (b : Prop) (A : Prop) (B : Prop) (h1 : b = True) (h2 : A -> B) : term8 A C b B D.
Proof. exact (EQ_MP (@lem13283 A C B D b h1) (@lem13318 C D A B h2)). Qed.
Lemma lem13343 (b : Prop) (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A -> B) (h2 : C -> D) : term8 A C b B D.
Proof. exact (or_elim (@lem13265 b) (fun h0 : b = True => @lem13342 C D b A B h0 h1) (fun h0 : b = False => @lem13341 A B b C D h0 h2)). Qed.
Lemma lem13344 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term2 A B C D) : C -> D.
Proof. exact (proj2 (@lem13268 A B C D h1)). Qed.
Lemma lem13345 (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term2 A B C D) : A -> B.
Proof. exact (proj1 (@lem13268 A B C D h1)). Qed.
Lemma lem13346 (b : Prop) (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A -> B) (h2 : C -> D) : (C -> D) = (term8 A C b B D).
Proof. exact (prop_ext (fun h3 : C -> D => @lem13343 b A B C D h1 h2) (fun h3 : term8 A C b B D => @lem13269 C D h2)). Qed.
Lemma lem13347 (b : Prop) (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A -> B) (h2 : C -> D) : term8 A C b B D.
Proof. exact (EQ_MP (@lem13346 b A B C D h1 h2) (@lem13269 C D h2)). Qed.
Lemma lem13348 (b : Prop) (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A -> B) (h2 : C -> D) : (A -> B) = (term8 A C b B D).
Proof. exact (prop_ext (fun h3 : A -> B => @lem13347 b A B C D h1 h2) (fun h3 : term8 A C b B D => @lem13270 A B h1)). Qed.
Lemma lem13349 (b : Prop) (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : A -> B) (h2 : C -> D) : term8 A C b B D.
Proof. exact (EQ_MP (@lem13348 b A B C D h1 h2) (@lem13270 A B h1)). Qed.
Lemma lem13350 (b : Prop) (C : Prop) (D : Prop) (A : Prop) (B : Prop) (h1 : term2 A B C D) (h2 : A -> B) : (C -> D) = (term8 A C b B D).
Proof. exact (prop_ext (fun h3 : C -> D => @lem13349 b A B C D h2 h3) (fun h3 : term8 A C b B D => @lem13344 A B C D h1)). Qed.
Lemma lem13351 (b : Prop) (C : Prop) (D : Prop) (A : Prop) (B : Prop) (h1 : term2 A B C D) (h2 : A -> B) : term8 A C b B D.
Proof. exact (EQ_MP (@lem13350 b C D A B h1 h2) (@lem13344 A B C D h1)). Qed.
Lemma lem13352 (b : Prop) (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term2 A B C D) : (A -> B) = (term8 A C b B D).
Proof. exact (prop_ext (fun h2 : A -> B => @lem13351 b C D A B h1 h2) (fun h2 : term8 A C b B D => @lem13345 A B C D h1)). Qed.
Lemma lem13353 (b : Prop) (A : Prop) (B : Prop) (C : Prop) (D : Prop) (h1 : term2 A B C D) : term8 A C b B D.
Proof. exact (EQ_MP (@lem13352 b A B C D h1) (@lem13345 A B C D h1)). Qed.
Lemma lem13354 (A : Prop) (C : Prop) (b : Prop) (B : Prop) (D : Prop) : term14 A C b B D.
Proof. exact (fun h0 : term2 A B C D => @lem13353 b A B C D h0). Qed.
