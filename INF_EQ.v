Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_EQ_term_abbrevs.
Require Import inf_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem5204234 (s : real -> Prop) : term0 s.
Proof. exact (@lem5204233 s). Qed.
Lemma lem5204235 (s : real -> Prop) : (term0 s) = ((inf s) = (term1 s)).
Proof. exact (eq_refl (term0 s)). Qed.
Lemma lem5204248 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term2 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5204249 (p : Prop) (q : Prop) (p' : Prop) : term3 p q p'.
Proof. exact (fun q' : Prop => @lem5204248 p q p' q'). Qed.
Lemma lem5204250 (p : Prop) (q : Prop) : term4 p q.
Proof. exact (fun p' : Prop => @lem5204249 p q p'). Qed.
Lemma lem5204251 (s : real -> Prop) (t : real -> Prop) : term5 s t.
Proof. exact (@lem5204250 (term6 s t) ((inf s) = (inf t))). Qed.
Lemma lem5204252 (s : real -> Prop) (t : real -> Prop) (p' : Prop) : term7 s t p'.
Proof. exact (@lem5204251 s t p'). Qed.
Lemma lem5204253 (s : real -> Prop) (t : real -> Prop) (p' : Prop) : (term7 s t p') = (term8 s t p').
Proof. exact (eq_refl (term7 s t p')). Qed.
Lemma lem5204254 (s : real -> Prop) (t : real -> Prop) (p' : Prop) : term8 s t p'.
Proof. exact (EQ_MP (@lem5204253 s t p') (@lem5204252 s t p')). Qed.
Lemma lem5204255 (s : real -> Prop) (t : real -> Prop) (p' : Prop) (q' : Prop) : term9 s t p' q'.
Proof. exact (@lem5204254 s t p' q'). Qed.
Lemma lem5204256 (s : real -> Prop) (t : real -> Prop) (p' : Prop) (q' : Prop) : (term9 s t p' q') = (term10 s t p' q').
Proof. exact (eq_refl (term9 s t p' q')). Qed.
Lemma lem5204257 (s : real -> Prop) (t : real -> Prop) (p' : Prop) (q' : Prop) : term10 s t p' q'.
Proof. exact (EQ_MP (@lem5204256 s t p' q') (@lem5204255 s t p' q')). Qed.
Lemma lem5204318 (s : real -> Prop) (t : real -> Prop) : (term6 s t) = (term6 s t).
Proof. exact (eq_refl (term6 s t)). Qed.
Lemma lem5204319 (s : real -> Prop) (t : real -> Prop) (q' : Prop) : term11 s t q'.
Proof. exact (@lem5204257 s t (term6 s t) q'). Qed.
Lemma lem5204320 (s : real -> Prop) (t : real -> Prop) (q' : Prop) : term12 s t q'.
Proof. exact (@lem5204319 s t q' (@lem5204318 s t)). Qed.
Lemma lem5204321 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : term6 s t.
Proof. exact (h1). Qed.
Lemma lem5204322 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : term13 s t a.
Proof. exact (@lem5204321 s t h1 a). Qed.
Lemma lem5204323 (s : real -> Prop) (t : real -> Prop) (a : real) : (term13 s t a) = ((term14 s a) = (term14 t a)).
Proof. exact (eq_refl (term13 s t a)). Qed.
Lemma lem5204328 (s : real -> Prop) : (inf s) = (term1 s).
Proof. exact (EQ_MP (@lem5204235 s) (@lem5204234 s)). Qed.
Lemma lem5204332 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term14 s a) = (term14 t a).
Proof. exact (EQ_MP (@lem5204323 s t a) (@lem5204322 a s t h1)). Qed.
Lemma lem5204360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5204361 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term15 s a) = (term15 t a).
Proof. exact (MK_COMB (@lem5204360) (@lem5204332 a s t h1)). Qed.
Lemma lem5204396 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term2 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5204397 (p : Prop) (q : Prop) (p' : Prop) : term3 p q p'.
Proof. exact (fun q' : Prop => @lem5204396 p q p' q'). Qed.
Lemma lem5204398 (p : Prop) (q : Prop) : term4 p q.
Proof. exact (fun p' : Prop => @lem5204397 p q p'). Qed.
Lemma lem5204399 (s : real -> Prop) (b : real) (a : real) : term16 s b a.
Proof. exact (@lem5204398 (term14 s b) (real_le b a)). Qed.
Lemma lem5204400 (s : real -> Prop) (b : real) (a : real) (p' : Prop) : term17 s b a p'.
Proof. exact (@lem5204399 s b a p'). Qed.
Lemma lem5204401 (s : real -> Prop) (b : real) (a : real) (p' : Prop) : (term17 s b a p') = (term18 s b a p').
Proof. exact (eq_refl (term17 s b a p')). Qed.
Lemma lem5204402 (s : real -> Prop) (b : real) (a : real) (p' : Prop) : term18 s b a p'.
Proof. exact (EQ_MP (@lem5204401 s b a p') (@lem5204400 s b a p')). Qed.
Lemma lem5204403 (s : real -> Prop) (b : real) (a : real) (p' : Prop) (q' : Prop) : term19 s b a p' q'.
Proof. exact (@lem5204402 s b a p' q'). Qed.
Lemma lem5204404 (s : real -> Prop) (b : real) (a : real) (p' : Prop) (q' : Prop) : (term19 s b a p' q') = (term20 s b a p' q').
Proof. exact (eq_refl (term19 s b a p' q')). Qed.
Lemma lem5204405 (s : real -> Prop) (b : real) (a : real) (p' : Prop) (q' : Prop) : term20 s b a p' q'.
Proof. exact (EQ_MP (@lem5204404 s b a p' q') (@lem5204403 s b a p' q')). Qed.
Lemma lem5204407 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term14 s a) = (term14 t a).
Proof. exact (EQ_MP (@lem5204323 s t a) (@lem5204322 a s t h1)). Qed.
Lemma lem5204408 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term14 s b) = (term14 t b).
Proof. exact (@lem5204407 b s t h1). Qed.
Lemma lem5204436 (s : real -> Prop) (a : real) (t : real -> Prop) (b : real) (q' : Prop) : term21 s a t b q'.
Proof. exact (@lem5204405 s b a (term14 t b) q'). Qed.
Lemma lem5204437 (a : real) (b : real) (q' : Prop) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : term22 s a t b q'.
Proof. exact (@lem5204436 s a t b q' (@lem5204408 b s t h1)). Qed.
Lemma lem5204456 (b : real) (a : real) : (real_le b a) = (real_le b a).
Proof. exact (eq_refl (real_le b a)). Qed.
Lemma lem5204457 (t : real -> Prop) (b : real) (a : real) : term23 t b a.
Proof. exact (fun h0 : term14 t b => @lem5204456 b a). Qed.
Lemma lem5204458 (b : real) (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : term24 s t b a.
Proof. exact (@lem5204437 a b (real_le b a) s t h1). Qed.
Lemma lem5204459 (b : real) (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term25 s b a) = (term25 t b a).
Proof. exact (@lem5204458 b a s t h1 (@lem5204457 t b a)). Qed.
Lemma lem5204552 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term26 s a) = (term26 t a).
Proof. exact (fun_ext (fun b : real => @lem5204459 b a s t h1)). Qed.
Lemma lem5204645 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5204646 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term27 s a) = (term27 t a).
Proof. exact (MK_COMB (@lem5204645) (@lem5204552 a s t h1)). Qed.
Lemma lem5204743 (a : real) (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term28 s a) = (term28 t a).
Proof. exact (MK_COMB (@lem5204361 a s t h1) (@lem5204646 a s t h1)). Qed.
Lemma lem5204869 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term29 s) = (term29 t).
Proof. exact (fun_ext (fun a : real => @lem5204743 a s t h1)). Qed.
Lemma lem5204995 : (@ε real) = (@ε real).
Proof. exact (eq_refl (@ε real)). Qed.
Lemma lem5204996 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term1 s) = (term1 t).
Proof. exact (MK_COMB (@lem5204995) (@lem5204869 s t h1)). Qed.
Lemma lem5205122 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (inf s) = (term1 t).
Proof. exact (TRANS (@lem5204328 s) (@lem5204996 s t h1)). Qed.
Lemma lem5205123 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5205124 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : (term30 s) = (term31 t).
Proof. exact (MK_COMB (@lem5205123) (@lem5205122 s t h1)). Qed.
Lemma lem5205251 (s : real -> Prop) : (inf s) = (term1 s).
Proof. exact (EQ_MP (@lem5204235 s) (@lem5204234 s)). Qed.
Lemma lem5205252 (t : real -> Prop) : (inf t) = (term1 t).
Proof. exact (@lem5205251 t). Qed.
Lemma lem5205378 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : ((inf s) = (inf t)) = ((term1 t) = (term1 t)).
Proof. exact (MK_COMB (@lem5205124 s t h1) (@lem5205252 t)). Qed.
Lemma lem5205380 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5205381 (x : real) : (x = x) = True.
Proof. exact (@lem5205380 real x). Qed.
Lemma lem5205382 (t : real -> Prop) : ((term1 t) = (term1 t)) = True.
Proof. exact (@lem5205381 (term1 t)). Qed.
Lemma lem5205383 (s : real -> Prop) (t : real -> Prop) (h1 : term6 s t) : ((inf s) = (inf t)) = True.
Proof. exact (TRANS (@lem5205378 s t h1) (@lem5205382 t)). Qed.
Lemma lem5205384 (s : real -> Prop) (t : real -> Prop) : term32 s t.
Proof. exact (fun h0 : term6 s t => @lem5205383 s t h0). Qed.
Lemma lem5205385 (s : real -> Prop) (t : real -> Prop) : term33 s t.
Proof. exact (@lem5204320 s t True). Qed.
Lemma lem5205386 (s : real -> Prop) (t : real -> Prop) : (term34 s t) = (term35 s t).
Proof. exact (@lem5205385 s t (@lem5205384 s t)). Qed.
Lemma lem5205388 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5205389 (s : real -> Prop) (t : real -> Prop) : (term35 s t) = True.
Proof. exact (@lem5205388 (term6 s t)). Qed.
Lemma lem5205390 (s : real -> Prop) (t : real -> Prop) : (term34 s t) = True.
Proof. exact (TRANS (@lem5205386 s t) (@lem5205389 s t)). Qed.
Lemma lem5205391 (s : real -> Prop) : (term36 s) = term37.
Proof. exact (fun_ext (fun t : real -> Prop => @lem5205390 s t)). Qed.
Lemma lem5205392 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5205393 (s : real -> Prop) : (term38 s) = term39.
Proof. exact (MK_COMB (@lem5205392) (@lem5205391 s)). Qed.
Lemma lem5205395 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5205396 (t : Prop) : (term41 t) = t.
Proof. exact (@lem5205395 (real -> Prop) t). Qed.
Lemma lem5205397 : term39 = True.
Proof. exact (@lem5205396 True). Qed.
Lemma lem5205398 (s : real -> Prop) : (term38 s) = True.
Proof. exact (TRANS (@lem5205393 s) (@lem5205397)). Qed.
Lemma lem5205399 : term42 = term37.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5205398 s)). Qed.
Lemma lem5205400 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5205401 : term43 = term39.
Proof. exact (MK_COMB (@lem5205400) (@lem5205399)). Qed.
Lemma lem5205403 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5205404 (t : Prop) : (term41 t) = t.
Proof. exact (@lem5205403 (real -> Prop) t). Qed.
Lemma lem5205405 : term39 = True.
Proof. exact (@lem5205404 True). Qed.
Lemma lem5205406 : term43 = True.
Proof. exact (TRANS (@lem5205401) (@lem5205405)). Qed.
Lemma lem5205407 : True = term43.
Proof. exact (SYM (@lem5205406)). Qed.
Lemma lem5205408 : term43.
Proof. exact (EQ_MP (@lem5205407) (@lem0)). Qed.
