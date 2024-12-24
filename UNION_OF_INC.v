Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_OF_INC_term_abbrevs.
Require Import IN_SING_spec.
Require Import UNION_OF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3322190_spec.
Require Import thm3322871_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4842240 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4842241 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4842242 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4842241 A P) (@lem4842240 A P)). Qed.
Lemma lem4842243 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4842242 A P Q). Qed.
Lemma lem4842244 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@UNION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4842246 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term4 A P Q s) : term4 A P Q s.
Proof. exact (h1). Qed.
Lemma lem4842247 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : Q s.
Proof. exact (h1). Qed.
Lemma lem4842248 {A : Type'} (P : type180 A) (s : A -> Prop) (h1 : term5 A P s) : term5 A P s.
Proof. exact (h1). Qed.
Lemma lem4842250 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4842244 A P Q) (@lem4842243 A P Q)). Qed.
Lemma lem4842251 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4842250 A P Q). Qed.
Lemma lem4842268 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4842269 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@UNION_OF A P Q s) = (term6 A P Q s).
Proof. exact (MK_COMB (@lem4842251 A P Q) (@lem4842268 A s)). Qed.
Lemma lem4842271 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4842272 {A : Type'} (f : type686 A) (y : A -> Prop) : (term8 A f y) = (f y).
Proof. exact (@lem4842271 (A -> Prop) Prop f y). Qed.
Lemma lem4842273 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term9 A P Q s) = (term6 A P Q s).
Proof. exact (@lem4842272 A (term3 A P Q) s). Qed.
Lemma lem4842274 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term6 A P Q s) = (term10 A P Q s).
Proof. exact (eq_refl (term6 A P Q s)). Qed.
Lemma lem4842275 {A : Type'} (P : type180 A) (Q : type686 A) : (term11 A P Q) = (term3 A P Q).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4842274 A P Q s)). Qed.
Lemma lem4842276 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4842277 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term9 A P Q s) = (term6 A P Q s).
Proof. exact (MK_COMB (@lem4842275 A P Q) (@lem4842276 A s)). Qed.
Lemma lem4842278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4842279 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term12 A P Q s) = (term13 A P Q s).
Proof. exact (MK_COMB (@lem4842278) (@lem4842277 A P Q s)). Qed.
Lemma lem4842280 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term6 A P Q s) = (term10 A P Q s).
Proof. exact (eq_refl (term6 A P Q s)). Qed.
Lemma lem4842281 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : ((term9 A P Q s) = (term6 A P Q s)) = ((term6 A P Q s) = (term10 A P Q s)).
Proof. exact (MK_COMB (@lem4842279 A P Q s) (@lem4842280 A P Q s)). Qed.
Lemma lem4842282 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term6 A P Q s) = (term10 A P Q s).
Proof. exact (EQ_MP (@lem4842281 A P Q s) (@lem4842273 A P Q s)). Qed.
Lemma lem4842299 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@UNION_OF A P Q s) = (term10 A P Q s).
Proof. exact (TRANS (@lem4842269 A P Q s) (@lem4842282 A P Q s)). Qed.
Lemma lem4842300 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term10 A P Q s) = (@UNION_OF A P Q s).
Proof. exact (SYM (@lem4842299 A P Q s)). Qed.
Lemma lem4842301 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4842302 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem4842303 {A : Type'} (x : A) : term15 A x.
Proof. exact (EQ_MP (@lem4842302 A x) (@lem4842301 A x)). Qed.
Lemma lem4842304 {A : Type'} (x : A) (y : A) : term16 A x y.
Proof. exact (@lem4842303 A x y). Qed.
Lemma lem4842305 {A : Type'} (x : A) (y : A) : (term16 A x y) = ((term17 A x y) = (x = y)).
Proof. exact (eq_refl (term16 A x y)). Qed.
Lemma lem4842307 {A : Type'} (P : type180 A) (s : A -> Prop) : (term5 A P s) = ((term5 A P s) = True).
Proof. exact (@lem7 (term5 A P s)). Qed.
Lemma lem4842309 {A : Type'} (Q : type686 A) (s : A -> Prop) : (Q s) = ((Q s) = True).
Proof. exact (@lem7 (Q s)). Qed.
Lemma lem4842314 {A : Type'} (P : type180 A) (s : A -> Prop) (h1 : term5 A P s) : (term5 A P s) = True.
Proof. exact (EQ_MP (@lem4842307 A P s) (@lem4842248 A P s h1)). Qed.
Lemma lem4842315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4842316 {A : Type'} (P : type180 A) (s : A -> Prop) (h1 : term5 A P s) : (term18 A P s) = (and True).
Proof. exact (MK_COMB (@lem4842315) (@lem4842314 A P s h1)). Qed.
Lemma lem4842326 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term19 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4842327 (p : Prop) (q : Prop) (p' : Prop) : term20 p q p'.
Proof. exact (fun q' : Prop => @lem4842326 p q p' q'). Qed.
Lemma lem4842328 (p : Prop) (q : Prop) : term21 p q.
Proof. exact (fun p' : Prop => @lem4842327 p q p'). Qed.
Lemma lem4842329 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) : term22 A s Q c.
Proof. exact (@lem4842328 (term23 A c s) (Q c)). Qed.
Lemma lem4842330 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) : term24 A s Q c p'.
Proof. exact (@lem4842329 A s Q c p'). Qed.
Lemma lem4842331 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) : (term24 A s Q c p') = (term25 A s Q c p').
Proof. exact (eq_refl (term24 A s Q c p')). Qed.
Lemma lem4842332 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) : term25 A s Q c p'.
Proof. exact (EQ_MP (@lem4842331 A s Q c p') (@lem4842330 A s Q c p')). Qed.
Lemma lem4842333 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) (q' : Prop) : term26 A s Q c p' q'.
Proof. exact (@lem4842332 A s Q c p' q'). Qed.
Lemma lem4842334 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) (q' : Prop) : (term26 A s Q c p' q') = (term27 A s Q c p' q').
Proof. exact (eq_refl (term26 A s Q c p' q')). Qed.
Lemma lem4842335 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) (q' : Prop) : term27 A s Q c p' q'.
Proof. exact (EQ_MP (@lem4842334 A s Q c p' q') (@lem4842333 A s Q c p' q')). Qed.
Lemma lem4842337 {A : Type'} (x : A) (y : A) : (term17 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4842305 A x y) (@lem4842304 A x y)). Qed.
Lemma lem4842338 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term23 A x y) = (x = y).
Proof. exact (@lem4842337 (A -> Prop) x y). Qed.
Lemma lem4842339 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term23 A c s) = (c = s).
Proof. exact (@lem4842338 A c s). Qed.
Lemma lem4842342 {A : Type'} (Q : type686 A) (c : A -> Prop) (s : A -> Prop) (q' : Prop) : term28 A Q c s q'.
Proof. exact (@lem4842335 A s Q c (c = s) q'). Qed.
Lemma lem4842343 {A : Type'} (Q : type686 A) (c : A -> Prop) (s : A -> Prop) (q' : Prop) : term29 A Q c s q'.
Proof. exact (@lem4842342 A Q c s q' (@lem4842339 A c s)). Qed.
Lemma lem4842346 {A : Type'} (c : A -> Prop) (s : A -> Prop) (h1 : c = s) : c = s.
Proof. exact (h1). Qed.
Lemma lem4842347 {A : Type'} (Q : type686 A) : Q = Q.
Proof. exact (eq_refl Q). Qed.
Lemma lem4842348 {A : Type'} (Q : type686 A) (c : A -> Prop) (s : A -> Prop) (h1 : c = s) : (Q c) = (Q s).
Proof. exact (MK_COMB (@lem4842347 A Q) (@lem4842346 A c s h1)). Qed.
Lemma lem4842350 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (Q s) = True.
Proof. exact (EQ_MP (@lem4842309 A Q s) (@lem4842247 A Q s h1)). Qed.
Lemma lem4842351 {A : Type'} (Q : type686 A) (c : A -> Prop) (s : A -> Prop) (h1 : Q s) (h2 : c = s) : (Q c) = True.
Proof. exact (TRANS (@lem4842348 A Q c s h2) (@lem4842350 A Q s h1)). Qed.
Lemma lem4842352 {A : Type'} (c : A -> Prop) (Q : type686 A) (s : A -> Prop) (h1 : Q s) : term30 A s Q c.
Proof. exact (fun h0 : c = s => @lem4842351 A Q c s h1 h0). Qed.
Lemma lem4842353 {A : Type'} (Q : type686 A) (c : A -> Prop) (s : A -> Prop) : term31 A Q c s.
Proof. exact (@lem4842343 A Q c s True). Qed.
Lemma lem4842354 {A : Type'} (c : A -> Prop) (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term32 A s Q c) = (term33 A c s).
Proof. exact (@lem4842353 A Q c s (@lem4842352 A c Q s h1)). Qed.
Lemma lem4842358 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4842359 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term33 A c s) = True.
Proof. exact (@lem4842358 (c = s)). Qed.
Lemma lem4842360 {A : Type'} (c : A -> Prop) (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term32 A s Q c) = True.
Proof. exact (TRANS (@lem4842354 A c Q s h1) (@lem4842359 A c s)). Qed.
Lemma lem4842361 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term34 A s Q) = (term35 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4842360 A c Q s h1)). Qed.
Lemma lem4842362 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4842363 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term36 A s Q) = (term37 A).
Proof. exact (MK_COMB (@lem4842362 A) (@lem4842361 A Q s h1)). Qed.
Lemma lem4842365 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4842366 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem4842365 (A -> Prop) t). Qed.
Lemma lem4842367 {A : Type'} : (term37 A) = True.
Proof. exact (@lem4842366 A True). Qed.
Lemma lem4842368 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term36 A s Q) = True.
Proof. exact (TRANS (@lem4842363 A Q s h1) (@lem4842367 A)). Qed.
Lemma lem4842369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4842370 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term40 A s Q) = (and True).
Proof. exact (MK_COMB (@lem4842369) (@lem4842368 A Q s h1)). Qed.
Lemma lem4842374 {_86807 : Type'} (s : _86807 -> Prop) : (term41 _86807 s) = s.
Proof. exact (EQ_MP (@lem3322190 _86807 s) (@lem3322871 _86807 s)). Qed.
Lemma lem4842375 {A : Type'} (s : A -> Prop) : (term41 A s) = s.
Proof. exact (@lem4842374 A s). Qed.
Lemma lem4842376 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4842377 {A : Type'} (s : A -> Prop) : (term42 A s) = (@eq (A -> Prop) s).
Proof. exact (MK_COMB (@lem4842376 A) (@lem4842375 A s)). Qed.
Lemma lem4842378 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4842379 {A : Type'} (s : A -> Prop) : ((term41 A s) = s) = (s = s).
Proof. exact (MK_COMB (@lem4842377 A s) (@lem4842378 A s)). Qed.
Lemma lem4842381 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4842382 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4842381 (A -> Prop) x). Qed.
Lemma lem4842383 {A : Type'} (s : A -> Prop) : (s = s) = True.
Proof. exact (@lem4842382 A s). Qed.
Lemma lem4842384 {A : Type'} (s : A -> Prop) : ((term41 A s) = s) = True.
Proof. exact (TRANS (@lem4842379 A s) (@lem4842383 A s)). Qed.
Lemma lem4842385 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term43 A Q s) = (True /\ True).
Proof. exact (MK_COMB (@lem4842370 A Q s h1) (@lem4842384 A s)). Qed.
Lemma lem4842387 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4842388 : (True /\ True) = True.
Proof. exact (@lem4842387 True). Qed.
Lemma lem4842389 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term43 A Q s) = True.
Proof. exact (TRANS (@lem4842385 A Q s h1) (@lem4842388)). Qed.
Lemma lem4842390 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : (term44 A P Q s) = (True /\ True).
Proof. exact (MK_COMB (@lem4842316 A P s h1) (@lem4842389 A Q s h2)). Qed.
Lemma lem4842392 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4842393 : (True /\ True) = True.
Proof. exact (@lem4842392 True). Qed.
Lemma lem4842394 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : (term44 A P Q s) = True.
Proof. exact (TRANS (@lem4842390 A P Q s h1 h2) (@lem4842393)). Qed.
Lemma lem4842395 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : True = (term44 A P Q s).
Proof. exact (SYM (@lem4842394 A P Q s h1 h2)). Qed.
Lemma lem4842396 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : term44 A P Q s.
Proof. exact (EQ_MP (@lem4842395 A P Q s h1 h2) (@lem0)). Qed.
Lemma lem4842397 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : term10 A P Q s.
Proof. exact (ex_intro (term45 A P Q s) (@INSERT (A -> Prop) s (@EMPTY (A -> Prop))) (@lem4842396 A P Q s h1 h2)). Qed.
Lemma lem4842398 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : @UNION_OF A P Q s.
Proof. exact (EQ_MP (@lem4842300 A P Q s) (@lem4842397 A P Q s h1 h2)). Qed.
Lemma lem4842399 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term4 A P Q s) : Q s.
Proof. exact (proj2 (@lem4842246 A P Q s h1)). Qed.
Lemma lem4842400 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term4 A P Q s) : term5 A P s.
Proof. exact (proj1 (@lem4842246 A P Q s h1)). Qed.
Lemma lem4842401 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : (Q s) = (@UNION_OF A P Q s).
Proof. exact (prop_ext (fun h3 : Q s => @lem4842398 A P Q s h1 h2) (fun h3 : @UNION_OF A P Q s => @lem4842247 A Q s h2)). Qed.
Lemma lem4842402 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : @UNION_OF A P Q s.
Proof. exact (EQ_MP (@lem4842401 A P Q s h1 h2) (@lem4842247 A Q s h2)). Qed.
Lemma lem4842403 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : (term5 A P s) = (@UNION_OF A P Q s).
Proof. exact (prop_ext (fun h3 : term5 A P s => @lem4842402 A P Q s h1 h2) (fun h3 : @UNION_OF A P Q s => @lem4842248 A P s h1)). Qed.
Lemma lem4842404 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : @UNION_OF A P Q s.
Proof. exact (EQ_MP (@lem4842403 A P Q s h1 h2) (@lem4842248 A P s h1)). Qed.
Lemma lem4842405 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : term4 A P Q s) : (Q s) = (@UNION_OF A P Q s).
Proof. exact (prop_ext (fun h3 : Q s => @lem4842404 A P Q s h1 h3) (fun h3 : @UNION_OF A P Q s => @lem4842399 A P Q s h2)). Qed.
Lemma lem4842406 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : term4 A P Q s) : @UNION_OF A P Q s.
Proof. exact (EQ_MP (@lem4842405 A P Q s h1 h2) (@lem4842399 A P Q s h2)). Qed.
Lemma lem4842407 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term4 A P Q s) : (term5 A P s) = (@UNION_OF A P Q s).
Proof. exact (prop_ext (fun h2 : term5 A P s => @lem4842406 A P Q s h2 h1) (fun h2 : @UNION_OF A P Q s => @lem4842400 A P Q s h1)). Qed.
Lemma lem4842408 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term4 A P Q s) : @UNION_OF A P Q s.
Proof. exact (EQ_MP (@lem4842407 A P Q s h1) (@lem4842400 A P Q s h1)). Qed.
Lemma lem4842409 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term46 A P Q s.
Proof. exact (fun h0 : term4 A P Q s => @lem4842408 A P Q s h0). Qed.
Lemma lem4842414 {A : Type'} (P : type180 A) (Q : type686 A) : term47 A P Q.
Proof. exact (fun s : A -> Prop => @lem4842409 A P Q s). Qed.
Lemma lem4842419 {A : Type'} (P : type180 A) : term48 A P.
Proof. exact (fun Q : type686 A => @lem4842414 A P Q). Qed.
Lemma lem4842424 {A : Type'} : term49 A.
Proof. exact (fun P : type180 A => @lem4842419 A P). Qed.
