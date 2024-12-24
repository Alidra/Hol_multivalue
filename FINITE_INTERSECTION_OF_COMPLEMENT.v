Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INTERSECTION_OF_COMPLEMENT_term_abbrevs.
Require Import COMPL_COMPL_spec.
Require Import ETA_AX_spec.
Require Import FINITE_UNION_OF_COMPLEMENT_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4879266 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4879267 {A : Type'} (s : A -> Prop) : (term0 A s) = ((term1 A s) = s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4879269 {A B : Type'} (t : A -> B) : term2 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem4879270 {A B : Type'} (t : A -> B) : (term2 A B t) = ((term3 A B t) = t).
Proof. exact (eq_refl (term2 A B t)). Qed.
Lemma lem4879271 {A B : Type'} (t : A -> B) : (term3 A B t) = t.
Proof. exact (EQ_MP (@lem4879270 A B t) (@lem4879269 A B t)). Qed.
Lemma lem4879272 {A : Type'} (P : type686 A) : term4 A P.
Proof. exact (@lem4879265 A P). Qed.
Lemma lem4879273 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem4879274 {A : Type'} (P : type686 A) : term5 A P.
Proof. exact (EQ_MP (@lem4879273 A P) (@lem4879272 A P)). Qed.
Lemma lem4879275 {A : Type'} (P : type686 A) (s : A -> Prop) : term6 A P s.
Proof. exact (@lem4879274 A P s). Qed.
Lemma lem4879276 {A : Type'} (P : type686 A) (s : A -> Prop) : (term6 A P s) = ((@UNION_OF A (@FINITE (A -> Prop)) P s) = (term7 A P s)).
Proof. exact (eq_refl (term6 A P s)). Qed.
Lemma lem4879289 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term7 A P s).
Proof. exact (EQ_MP (@lem4879276 A P s) (@lem4879275 A P s)). Qed.
Lemma lem4879290 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term7 A P s).
Proof. exact (@lem4879289 A P s). Qed.
Lemma lem4879291 {A : Type'} (P : type686 A) (s : A -> Prop) : (term8 A P s) = (term9 A P s).
Proof. exact (@lem4879290 A (term10 A P) (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4879293 {A B : Type'} (f : A -> B) (y : A) : (term11 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4879294 {A : Type'} (f : type686 A) (y : A -> Prop) : (term12 A f y) = (f y).
Proof. exact (@lem4879293 (A -> Prop) Prop f y). Qed.
Lemma lem4879295 {A : Type'} (P : type686 A) (s : A -> Prop) : (term13 A P s) = (term14 A P s).
Proof. exact (@lem4879294 A (term10 A P) (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4879296 {A : Type'} (P : type686 A) (s : A -> Prop) : (term15 A P s) = (term16 A P s).
Proof. exact (eq_refl (term15 A P s)). Qed.
Lemma lem4879297 {A : Type'} (P : type686 A) : (term17 A P) = (term10 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4879296 A P s)). Qed.
Lemma lem4879298 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4879299 {A : Type'} (P : type686 A) (s : A -> Prop) : (term13 A P s) = (term14 A P s).
Proof. exact (MK_COMB (@lem4879297 A P) (@lem4879298 A s)). Qed.
Lemma lem4879300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4879301 {A : Type'} (P : type686 A) (s : A -> Prop) : (term18 A P s) = (term19 A P s).
Proof. exact (MK_COMB (@lem4879300) (@lem4879299 A P s)). Qed.
Lemma lem4879302 {A : Type'} (P : type686 A) (s : A -> Prop) : (term14 A P s) = (term20 A P s).
Proof. exact (eq_refl (term14 A P s)). Qed.
Lemma lem4879303 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term13 A P s) = (term14 A P s)) = ((term14 A P s) = (term20 A P s)).
Proof. exact (MK_COMB (@lem4879301 A P s) (@lem4879302 A P s)). Qed.
Lemma lem4879304 {A : Type'} (P : type686 A) (s : A -> Prop) : (term14 A P s) = (term20 A P s).
Proof. exact (EQ_MP (@lem4879303 A P s) (@lem4879295 A P s)). Qed.
Lemma lem4879305 {A : Type'} (P : type686 A) : (term21 A P) = (term22 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4879304 A P s)). Qed.
Lemma lem4879306 {A : Type'} : (@INTERSECTION_OF A (@FINITE (A -> Prop))) = (@INTERSECTION_OF A (@FINITE (A -> Prop))).
Proof. exact (eq_refl (@INTERSECTION_OF A (@FINITE (A -> Prop)))). Qed.
Lemma lem4879307 {A : Type'} (P : type686 A) : (term23 A P) = (term24 A P).
Proof. exact (MK_COMB (@lem4879306 A) (@lem4879305 A P)). Qed.
Lemma lem4879308 {A : Type'} (s : A -> Prop) : (term1 A s) = (term1 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem4879309 {A : Type'} (P : type686 A) (s : A -> Prop) : (term9 A P s) = (term25 A P s).
Proof. exact (MK_COMB (@lem4879307 A P) (@lem4879308 A s)). Qed.
Lemma lem4879310 {A : Type'} (P : type686 A) (s : A -> Prop) : (term8 A P s) = (term25 A P s).
Proof. exact (TRANS (@lem4879291 A P s) (@lem4879309 A P s)). Qed.
Lemma lem4879311 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = (term26 A P s).
Proof. exact (eq_refl (term26 A P s)). Qed.
Lemma lem4879312 {A : Type'} (P : type686 A) (s : A -> Prop) : ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term8 A P s)) = ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term25 A P s)).
Proof. exact (MK_COMB (@lem4879311 A P s) (@lem4879310 A P s)). Qed.
Lemma lem4879315 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4879312 A P s)). Qed.
Lemma lem4879316 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4879317 {A : Type'} (P : type686 A) : (term29 A P) = (term30 A P).
Proof. exact (MK_COMB (@lem4879316 A) (@lem4879315 A P)). Qed.
Lemma lem4879322 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4879317 A P)). Qed.
Lemma lem4879323 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4879324 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (MK_COMB (@lem4879323 A) (@lem4879322 A)). Qed.
Lemma lem4879329 {A : Type'} : (term34 A) = (term33 A).
Proof. exact (SYM (@lem4879324 A)). Qed.
Lemma lem4879341 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (EQ_MP (@lem4879267 A s) (@lem4879266 A s)). Qed.
Lemma lem4879342 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (@lem4879341 A s). Qed.
Lemma lem4879343 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4879344 {A : Type'} (P : type686 A) (s : A -> Prop) : (term20 A P s) = (P s).
Proof. exact (MK_COMB (@lem4879343 A P) (@lem4879342 A s)). Qed.
Lemma lem4879345 {A : Type'} (P : type686 A) : (term22 A P) = (term35 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4879344 A P s)). Qed.
Lemma lem4879346 {A : Type'} (t : type686 A) : (term35 A t) = t.
Proof. exact (@lem4879271 (A -> Prop) Prop t). Qed.
Lemma lem4879347 {A : Type'} (P : type686 A) : (term35 A P) = P.
Proof. exact (@lem4879346 A P). Qed.
Lemma lem4879348 {A : Type'} (P : type686 A) : (term22 A P) = P.
Proof. exact (TRANS (@lem4879345 A P) (@lem4879347 A P)). Qed.
Lemma lem4879349 {A : Type'} : (@INTERSECTION_OF A (@FINITE (A -> Prop))) = (@INTERSECTION_OF A (@FINITE (A -> Prop))).
Proof. exact (eq_refl (@INTERSECTION_OF A (@FINITE (A -> Prop)))). Qed.
Lemma lem4879350 {A : Type'} (P : type686 A) : (term24 A P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (MK_COMB (@lem4879349 A) (@lem4879348 A P)). Qed.
Lemma lem4879352 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (EQ_MP (@lem4879267 A s) (@lem4879266 A s)). Qed.
Lemma lem4879353 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (@lem4879352 A s). Qed.
Lemma lem4879354 {A : Type'} (P : type686 A) (s : A -> Prop) : (term25 A P s) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s).
Proof. exact (MK_COMB (@lem4879350 A P) (@lem4879353 A s)). Qed.
Lemma lem4879355 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = (term26 A P s).
Proof. exact (eq_refl (term26 A P s)). Qed.
Lemma lem4879356 {A : Type'} (P : type686 A) (s : A -> Prop) : ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term25 A P s)) = ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s)).
Proof. exact (MK_COMB (@lem4879355 A P s) (@lem4879354 A P s)). Qed.
Lemma lem4879358 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4879359 (x : Prop) : (x = x) = True.
Proof. exact (@lem4879358 Prop x). Qed.
Lemma lem4879360 {A : Type'} (P : type686 A) (s : A -> Prop) : ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s)) = True.
Proof. exact (@lem4879359 (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s)). Qed.
Lemma lem4879361 {A : Type'} (P : type686 A) (s : A -> Prop) : ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (term25 A P s)) = True.
Proof. exact (TRANS (@lem4879356 A P s) (@lem4879360 A P s)). Qed.
Lemma lem4879362 {A : Type'} (P : type686 A) : (term28 A P) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4879361 A P s)). Qed.
Lemma lem4879363 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4879364 {A : Type'} (P : type686 A) : (term30 A P) = (term37 A).
Proof. exact (MK_COMB (@lem4879363 A) (@lem4879362 A P)). Qed.
Lemma lem4879366 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4879367 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem4879366 (A -> Prop) t). Qed.
Lemma lem4879368 {A : Type'} : (term37 A) = True.
Proof. exact (@lem4879367 A True). Qed.
Lemma lem4879369 {A : Type'} (P : type686 A) : (term30 A P) = True.
Proof. exact (TRANS (@lem4879364 A P) (@lem4879368 A)). Qed.
Lemma lem4879370 {A : Type'} : (term32 A) = (term40 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4879369 A P)). Qed.
Lemma lem4879371 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4879372 {A : Type'} : (term34 A) = (term41 A).
Proof. exact (MK_COMB (@lem4879371 A) (@lem4879370 A)). Qed.
Lemma lem4879374 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4879375 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (@lem4879374 (type686 A) t). Qed.
Lemma lem4879376 {A : Type'} : (term41 A) = True.
Proof. exact (@lem4879375 A True). Qed.
Lemma lem4879377 {A : Type'} : (term34 A) = True.
Proof. exact (TRANS (@lem4879372 A) (@lem4879376 A)). Qed.
Lemma lem4879378 {A : Type'} : True = (term34 A).
Proof. exact (SYM (@lem4879377 A)). Qed.
Lemma lem4879379 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem4879378 A) (@lem0)). Qed.
Lemma lem4879380 {A : Type'} : term33 A.
Proof. exact (EQ_MP (@lem4879329 A) (@lem4879379 A)). Qed.
