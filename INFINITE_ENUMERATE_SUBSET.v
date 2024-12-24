Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_ENUMERATE_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_NUMSEG_LT_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import INFINITE_DIFF_FINITE_spec.
Require Import INFINITE_IMAGE_INJ_spec.
Require Import INFINITE_NONEMPTY_spec.
Require Import INFINITE_SUPERSET_spec.
Require Import MONO_EXISTS_spec.
Require Import SUBSET_spec.
Require Import WF_num_spec.
Require Import WLOG_LT_spec.
Require Import num_INFINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1804_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm358361_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem4774273 {_97990 : Type'} (h1 : term0 _97990) : term0 _97990.
Proof. exact (h1). Qed.
Lemma lem4774274 {_97990 : Type'} (s : _97990 -> Prop) (h1 : term0 _97990) : term1 _97990 s.
Proof. exact (@lem4774273 _97990 h1 s). Qed.
Lemma lem4774275 {_97990 : Type'} (s : _97990 -> Prop) : (term1 _97990 s) = (term2 _97990 s).
Proof. exact (eq_refl (term1 _97990 s)). Qed.
Lemma lem4774276 {_97990 : Type'} (s : _97990 -> Prop) (h1 : term0 _97990) : term2 _97990 s.
Proof. exact (EQ_MP (@lem4774275 _97990 s) (@lem4774274 _97990 s h1)). Qed.
Lemma lem4774277 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term0 _97990) : term3 _97990 s t.
Proof. exact (@lem4774276 _97990 s h1 t). Qed.
Lemma lem4774278 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) : (term3 _97990 s t) = (term4 _97990 s t).
Proof. exact (eq_refl (term3 _97990 s t)). Qed.
Lemma lem4774279 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term0 _97990) : term4 _97990 s t.
Proof. exact (EQ_MP (@lem4774278 _97990 s t) (@lem4774277 _97990 s t h1)). Qed.
Lemma lem4774280 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term5 _97990 s t) : term5 _97990 s t.
Proof. exact (h1). Qed.
Lemma lem4774281 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term0 _97990) (h2 : term5 _97990 s t) : @INFINITE _97990 t.
Proof. exact (@lem4774279 _97990 s t h1 (@lem4774280 _97990 s t h2)). Qed.
Lemma lem4774282 {_97990 : Type'} (s : _97990 -> Prop) (t : _97990 -> Prop) (h1 : term5 _97990 s t) : term6 _97990 t.
Proof. exact (fun h0 : term0 _97990 => @lem4774281 _97990 s t h0 h1). Qed.
Lemma lem4774283 {_97990 : Type'} (t : _97990 -> Prop) (h1 : term7 _97990 t) : term7 _97990 t.
Proof. exact (h1). Qed.
Lemma lem4774284 {_97990 : Type'} (t : _97990 -> Prop) (h1 : term7 _97990 t) : term6 _97990 t.
Proof. exact (ex_elim (@lem4774283 _97990 t h1) (fun s : _97990 -> Prop => fun h0 : term8 _97990 t s => @lem4774282 _97990 s t h0)). Qed.
Lemma lem4774285 {_97990 : Type'} (h1 : term0 _97990) : term0 _97990.
Proof. exact (h1). Qed.
Lemma lem4774286 {_97990 : Type'} (t : _97990 -> Prop) (h1 : term0 _97990) (h2 : term7 _97990 t) : @INFINITE _97990 t.
Proof. exact (@lem4774284 _97990 t h2 (@lem4774285 _97990 h1)). Qed.
Lemma lem4774287 {_97990 : Type'} (t : _97990 -> Prop) (h1 : term0 _97990) : term9 _97990 t.
Proof. exact (fun h0 : term7 _97990 t => @lem4774286 _97990 t h1 h0). Qed.
Lemma lem4774288 {_97990 : Type'} (h1 : term0 _97990) : term10 _97990.
Proof. exact (fun t : _97990 -> Prop => @lem4774287 _97990 t h1). Qed.
Lemma lem4774289 {_97990 : Type'} : term11 _97990.
Proof. exact (fun h0 : term0 _97990 => @lem4774288 _97990 h0). Qed.
Lemma lem4774290 {_97990 : Type'} : term10 _97990.
Proof. exact (@lem4774289 _97990 (@lem3735653 _97990)). Qed.
Lemma lem4774291 {_97990 : Type'} (t : _97990 -> Prop) : term12 _97990 t.
Proof. exact (@lem4774290 _97990 t). Qed.
Lemma lem4774292 {_97990 : Type'} (t : _97990 -> Prop) : (term12 _97990 t) = (term9 _97990 t).
Proof. exact (eq_refl (term12 _97990 t)). Qed.
Lemma lem4774294 (P : type1605) (h1 : term13 P) : term13 P.
Proof. exact (h1). Qed.
Lemma lem4774295 (P : type1605) (h1 : term14 P) : term14 P.
Proof. exact (h1). Qed.
Lemma lem4774296 (P : type1605) (h1 : term14 P) (h2 : term13 P) : term15 P.
Proof. exact (@lem4774294 P h2 (@lem4774295 P h1)). Qed.
Lemma lem4774297 (P : type1605) (h1 : term14 P) : term16 P.
Proof. exact (fun h0 : term13 P => @lem4774296 P h1 h0). Qed.
Lemma lem4774298 (P : type1605) (h1 : term13 P) : term13 P.
Proof. exact (h1). Qed.
Lemma lem4774299 (P : type1605) (h1 : term14 P) (h2 : term13 P) : term15 P.
Proof. exact (@lem4774297 P h1 (@lem4774298 P h2)). Qed.
Lemma lem4774300 (P : type1605) (h1 : term13 P) : term13 P.
Proof. exact (fun h0 : term14 P => @lem4774299 P h0 h1). Qed.
Lemma lem4774301 (P : type1605) : term17 P.
Proof. exact (fun h0 : term13 P => @lem4774300 P h0). Qed.
Lemma lem4774303 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term18 A P Q) : term18 A P Q.
Proof. exact (h1). Qed.
Lemma lem4774304 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term19 A P Q) : term19 A P Q.
Proof. exact (h1). Qed.
Lemma lem4774305 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term19 A P Q) (h2 : term18 A P Q) : term20 A P Q.
Proof. exact (@lem4774303 A P Q h2 (@lem4774304 A P Q h1)). Qed.
Lemma lem4774306 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term19 A P Q) : term21 A P Q.
Proof. exact (fun h0 : term18 A P Q => @lem4774305 A P Q h1 h0). Qed.
Lemma lem4774307 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term18 A P Q) : term18 A P Q.
Proof. exact (h1). Qed.
Lemma lem4774308 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term19 A P Q) (h2 : term18 A P Q) : term20 A P Q.
Proof. exact (@lem4774306 A P Q h1 (@lem4774307 A P Q h2)). Qed.
Lemma lem4774309 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term18 A P Q) : term18 A P Q.
Proof. exact (fun h0 : term19 A P Q => @lem4774308 A P Q h0 h1). Qed.
Lemma lem4774310 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term22 A P Q.
Proof. exact (fun h0 : term18 A P Q => @lem4774309 A P Q h0). Qed.
Lemma lem4774322 {_93152 : Type'} (s : _93152 -> Prop) : term23 _93152 s.
Proof. exact (@lem3631342 _93152 s). Qed.
Lemma lem4774323 {_93152 : Type'} (s : _93152 -> Prop) : (term23 _93152 s) = (term24 _93152 s).
Proof. exact (eq_refl (term23 _93152 s)). Qed.
Lemma lem4774325 (n : nat) : term25 n.
Proof. exact (@lem4621509 n). Qed.
Lemma lem4774326 (n : nat) : (term25 n) = (term26 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem4774327 (n : nat) : term26 n.
Proof. exact (EQ_MP (@lem4774326 n) (@lem4774325 n)). Qed.
Lemma lem4774328 (n : nat) : (term26 n) = ((term26 n) = True).
Proof. exact (@lem7 (term26 n)). Qed.
Lemma lem4774330 {A B : Type'} (f : A -> B) : term27 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4774331 {A B : Type'} (f : A -> B) : (term27 A B f) = (term28 A B f).
Proof. exact (eq_refl (term27 A B f)). Qed.
Lemma lem4774332 {A B : Type'} (f : A -> B) : term28 A B f.
Proof. exact (EQ_MP (@lem4774331 A B f) (@lem4774330 A B f)). Qed.
Lemma lem4774333 {A B : Type'} (f : A -> B) (s : A -> Prop) : term29 A B f s.
Proof. exact (@lem4774332 A B f s). Qed.
Lemma lem4774334 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term29 A B f s) = (term30 A B f s).
Proof. exact (eq_refl (term29 A B f s)). Qed.
Lemma lem4774335 {A B : Type'} (f : A -> B) (s : A -> Prop) : term30 A B f s.
Proof. exact (EQ_MP (@lem4774334 A B f s) (@lem4774333 A B f s)). Qed.
Lemma lem4774336 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4774337 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term31 A B f s.
Proof. exact (@lem4774335 A B f s (@lem4774336 A s h1)). Qed.
Lemma lem4774338 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term31 A B f s) = ((term31 A B f s) = True).
Proof. exact (@lem7 (term31 A B f s)). Qed.
Lemma lem4774339 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term31 A B f s) = True.
Proof. exact (EQ_MP (@lem4774338 A B f s) (@lem4774337 A B f s h1)). Qed.
Lemma lem4774354 (p : Prop) (q : Prop) (r : Prop) : (term32 p q r) = (term33 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem4774355 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term35 A s t).
Proof. exact (@lem4774354 (@INFINITE A s) (@FINITE A t) (term36 A s t)). Qed.
Lemma lem4774360 {A : Type'} (s : A -> Prop) : (term37 A s) = (term38 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4774355 A s t)). Qed.
Lemma lem4774361 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4774362 {A : Type'} (s : A -> Prop) : (term39 A s) = (term40 A s).
Proof. exact (MK_COMB (@lem4774361 A) (@lem4774360 A s)). Qed.
Lemma lem4774367 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4774362 A s)). Qed.
Lemma lem4774368 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4774369 {A : Type'} : (term43 A) = (term44 A).
Proof. exact (MK_COMB (@lem4774368 A) (@lem4774367 A)). Qed.
Lemma lem4774374 {A : Type'} : term44 A.
Proof. exact (EQ_MP (@lem4774369 A) (@lem3632103 A)). Qed.
Lemma lem4774375 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem4774376 {A : Type'} (s : A -> Prop) (h1 : term44 A) : term45 A s.
Proof. exact (@lem4774375 A h1 s). Qed.
Lemma lem4774377 {A : Type'} (s : A -> Prop) : (term45 A s) = (term40 A s).
Proof. exact (eq_refl (term45 A s)). Qed.
Lemma lem4774378 {A : Type'} (s : A -> Prop) (h1 : term44 A) : term40 A s.
Proof. exact (EQ_MP (@lem4774377 A s) (@lem4774376 A s h1)). Qed.
Lemma lem4774379 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A) : term46 A s t.
Proof. exact (@lem4774378 A s h1 t). Qed.
Lemma lem4774380 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term46 A s t) = (term35 A s t).
Proof. exact (eq_refl (term46 A s t)). Qed.
Lemma lem4774381 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A) : term35 A s t.
Proof. exact (EQ_MP (@lem4774380 A s t) (@lem4774379 A s t h1)). Qed.
Lemma lem4774382 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : @INFINITE A s.
Proof. exact (h1). Qed.
Lemma lem4774383 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term44 A) (h2 : @INFINITE A s) : term47 A s t.
Proof. exact (@lem4774381 A s t h1 (@lem4774382 A s h2)). Qed.
Lemma lem4774384 {A : Type'} (s : A -> Prop) (h1 : term44 A) (h2 : @INFINITE A s) : term48 A s.
Proof. exact (fun t : A -> Prop => @lem4774383 A t s h1 h2). Qed.
Lemma lem4774385 {A : Type'} (s : A -> Prop) (h1 : term44 A) : term49 A s.
Proof. exact (fun h0 : @INFINITE A s => @lem4774384 A s h1 h0). Qed.
Lemma lem4774386 {A : Type'} (h1 : term44 A) : term50 A.
Proof. exact (fun s : A -> Prop => @lem4774385 A s h1). Qed.
Lemma lem4774387 {A : Type'} : term51 A.
Proof. exact (fun h0 : term44 A => @lem4774386 A h0). Qed.
Lemma lem4774388 {A : Type'} : term50 A.
Proof. exact (@lem4774387 A (@lem4774374 A)). Qed.
Lemma lem4774389 {A : Type'} (s : A -> Prop) : term52 A s.
Proof. exact (@lem4774388 A s). Qed.
Lemma lem4774390 {A : Type'} (s : A -> Prop) : (term52 A s) = (term49 A s).
Proof. exact (eq_refl (term52 A s)). Qed.
Lemma lem4774393 {A B : Type'} (lt2 : type1402 A) : term53 A B lt2.
Proof. exact (fun h0 : @WF A lt2 => @lem358361 A B lt2 h0). Qed.
Lemma lem4774394 {B : Type'} (lt2 : type1605) : term54 B lt2.
Proof. exact (@lem4774393 nat B lt2). Qed.
Lemma lem4774395 {B : Type'} : term55 B.
Proof. exact (@lem4774394 B Peano.lt). Qed.
Lemma lem4774396 {B : Type'} : term56 B.
Proof. exact (@lem4774395 B (@lem365140)). Qed.
Lemma lem4774397 {B : Type'} (h1 : term56 B) : term56 B.
Proof. exact (h1). Qed.
Lemma lem4774398 {B : Type'} (P : type970 B) (h1 : term56 B) : term57 B P.
Proof. exact (@lem4774397 B h1 P). Qed.
Lemma lem4774399 {B : Type'} (P : type970 B) : (term57 B P) = (term58 B P).
Proof. exact (eq_refl (term57 B P)). Qed.
Lemma lem4774400 {B : Type'} (P : type970 B) (h1 : term56 B) : term58 B P.
Proof. exact (EQ_MP (@lem4774399 B P) (@lem4774398 B P h1)). Qed.
Lemma lem4774401 {B : Type'} (P : type970 B) (h1 : term59 B P) : term59 B P.
Proof. exact (h1). Qed.
Lemma lem4774402 {B : Type'} (P : type970 B) (h1 : term56 B) (h2 : term59 B P) : term60 B P.
Proof. exact (@lem4774400 B P h1 (@lem4774401 B P h2)). Qed.
Lemma lem4774403 {B : Type'} (P : type970 B) (h1 : term59 B P) : term61 B P.
Proof. exact (fun h0 : term56 B => @lem4774402 B P h0 h1). Qed.
Lemma lem4774404 {B : Type'} (h1 : term56 B) : term56 B.
Proof. exact (h1). Qed.
Lemma lem4774405 {B : Type'} (P : type970 B) (h1 : term56 B) (h2 : term59 B P) : term60 B P.
Proof. exact (@lem4774403 B P h2 (@lem4774404 B h1)). Qed.
Lemma lem4774406 {B : Type'} (P : type970 B) (h1 : term56 B) : term58 B P.
Proof. exact (fun h0 : term59 B P => @lem4774405 B P h1 h0). Qed.
Lemma lem4774407 {B : Type'} (h1 : term56 B) : term56 B.
Proof. exact (fun P : type970 B => @lem4774406 B P h1). Qed.
Lemma lem4774408 {B : Type'} : term62 B.
Proof. exact (fun h0 : term56 B => @lem4774407 B h0). Qed.
Lemma lem4774409 {B : Type'} : term56 B.
Proof. exact (@lem4774408 B (@lem4774396 B)). Qed.
Lemma lem4774410 {B : Type'} (P : type970 B) : term57 B P.
Proof. exact (@lem4774409 B P). Qed.
Lemma lem4774411 {B : Type'} (P : type970 B) : (term57 B P) = (term58 B P).
Proof. exact (eq_refl (term57 B P)). Qed.
Lemma lem4774413 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : @INFINITE A s.
Proof. exact (h1). Qed.
Lemma lem4774414 {A : Type'} (s : A -> Prop) (h1 : term63 A s) : term63 A s.
Proof. exact (h1). Qed.
Lemma lem4774415 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term64 A s f) : term64 A s f.
Proof. exact (h1). Qed.
Lemma lem4774416 {A : Type'} (f : nat -> A) (h1 : term65 A f) : term65 A f.
Proof. exact (h1). Qed.
Lemma lem4774417 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : term66 A f s.
Proof. exact (h1). Qed.
Lemma lem4774418 {A : Type'} (s : A -> Prop) (h1 : term67 A s) : term67 A s.
Proof. exact (h1). Qed.
Lemma lem4774420 {B : Type'} (P : type970 B) : term58 B P.
Proof. exact (EQ_MP (@lem4774411 B P) (@lem4774410 B P)). Qed.
Lemma lem4774421 {A : Type'} (P : type970 A) : term58 A P.
Proof. exact (@lem4774420 A P). Qed.
Lemma lem4774422 {A : Type'} (s : A -> Prop) : term68 A s.
Proof. exact (@lem4774421 A (term69 A s)). Qed.
Lemma lem4774423 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term70 A s f) = (term71 A s f).
Proof. exact (eq_refl (term70 A s f)). Qed.
Lemma lem4774424 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4774425 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term72 A s f n) = (term73 A s f n).
Proof. exact (MK_COMB (@lem4774423 A s f) (@lem4774424 n)). Qed.
Lemma lem4774426 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term73 A s f n) = (term74 A s n f).
Proof. exact (eq_refl (term73 A s f n)). Qed.
Lemma lem4774427 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term72 A s f n) = (term74 A s n f).
Proof. exact (TRANS (@lem4774425 A s f n) (@lem4774426 A s n f)). Qed.
Lemma lem4774428 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4774429 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term75 A s f n y) = (term76 A s n f y).
Proof. exact (MK_COMB (@lem4774427 A s n f) (@lem4774428 A y)). Qed.
Lemma lem4774430 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term76 A s n f y) = (term77 A s n f y).
Proof. exact (eq_refl (term76 A s n f y)). Qed.
Lemma lem4774431 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term75 A s f n y) = (term77 A s n f y).
Proof. exact (TRANS (@lem4774429 A s n f y) (@lem4774430 A s n f y)). Qed.
Lemma lem4774432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4774433 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term78 A s f n y) = (term79 A s n f y).
Proof. exact (MK_COMB (@lem4774432) (@lem4774431 A s n f y)). Qed.
Lemma lem4774434 {A : Type'} (s : A -> Prop) (g : nat -> A) : (term70 A s g) = (term71 A s g).
Proof. exact (eq_refl (term70 A s g)). Qed.
Lemma lem4774435 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4774436 {A : Type'} (s : A -> Prop) (g : nat -> A) (n : nat) : (term72 A s g n) = (term73 A s g n).
Proof. exact (MK_COMB (@lem4774434 A s g) (@lem4774435 n)). Qed.
Lemma lem4774437 {A : Type'} (s : A -> Prop) (n : nat) (g : nat -> A) : (term73 A s g n) = (term74 A s n g).
Proof. exact (eq_refl (term73 A s g n)). Qed.
Lemma lem4774438 {A : Type'} (s : A -> Prop) (n : nat) (g : nat -> A) : (term72 A s g n) = (term74 A s n g).
Proof. exact (TRANS (@lem4774436 A s g n) (@lem4774437 A s n g)). Qed.
Lemma lem4774439 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4774440 {A : Type'} (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) : (term75 A s g n y) = (term76 A s n g y).
Proof. exact (MK_COMB (@lem4774438 A s n g) (@lem4774439 A y)). Qed.
Lemma lem4774441 {A : Type'} (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) : (term76 A s n g y) = (term77 A s n g y).
Proof. exact (eq_refl (term76 A s n g y)). Qed.
Lemma lem4774442 {A : Type'} (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) : (term75 A s g n y) = (term77 A s n g y).
Proof. exact (TRANS (@lem4774440 A s n g y) (@lem4774441 A s n g y)). Qed.
Lemma lem4774443 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) : ((term75 A s f n y) = (term75 A s g n y)) = ((term77 A s n f y) = (term77 A s n g y)).
Proof. exact (MK_COMB (@lem4774433 A s n f y) (@lem4774442 A s n g y)). Qed.
Lemma lem4774444 {A : Type'} (n : nat) (f : nat -> A) (g : nat -> A) : (term80 A n f g) = (term80 A n f g).
Proof. exact (eq_refl (term80 A n f g)). Qed.
Lemma lem4774445 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) : (term81 A f s g n y) = (term82 A f s n g y).
Proof. exact (MK_COMB (@lem4774444 A n f g) (@lem4774443 A f s n g y)). Qed.
Lemma lem4774446 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) : (term83 A f s g n) = (term84 A f s n g).
Proof. exact (fun_ext (fun y : A => @lem4774445 A f s n g y)). Qed.
Lemma lem4774447 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4774448 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) : (term85 A f s g n) = (term86 A f s n g).
Proof. exact (MK_COMB (@lem4774447 A) (@lem4774446 A f s n g)). Qed.
Lemma lem4774449 {A : Type'} (f : nat -> A) (s : A -> Prop) (g : nat -> A) : (term87 A f s g) = (term88 A f s g).
Proof. exact (fun_ext (fun n : nat => @lem4774448 A f s n g)). Qed.
Lemma lem4774450 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4774451 {A : Type'} (f : nat -> A) (s : A -> Prop) (g : nat -> A) : (term89 A f s g) = (term90 A f s g).
Proof. exact (MK_COMB (@lem4774450) (@lem4774449 A f s g)). Qed.
Lemma lem4774452 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term91 A f s) = (term92 A f s).
Proof. exact (fun_ext (fun g : nat -> A => @lem4774451 A f s g)). Qed.
Lemma lem4774453 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4774454 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term93 A f s) = (term94 A f s).
Proof. exact (MK_COMB (@lem4774453 A) (@lem4774452 A f s)). Qed.
Lemma lem4774455 {A : Type'} (s : A -> Prop) : (term95 A s) = (term96 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem4774454 A f s)). Qed.
Lemma lem4774456 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4774457 {A : Type'} (s : A -> Prop) : (term97 A s) = (term98 A s).
Proof. exact (MK_COMB (@lem4774456 A) (@lem4774455 A s)). Qed.
Lemma lem4774458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4774459 {A : Type'} (s : A -> Prop) : (term99 A s) = (term100 A s).
Proof. exact (MK_COMB (@lem4774458) (@lem4774457 A s)). Qed.
Lemma lem4774460 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term70 A s f) = (term71 A s f).
Proof. exact (eq_refl (term70 A s f)). Qed.
Lemma lem4774461 (z : nat) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem4774462 {A : Type'} (s : A -> Prop) (f : nat -> A) (z : nat) : (term72 A s f z) = (term73 A s f z).
Proof. exact (MK_COMB (@lem4774460 A s f) (@lem4774461 z)). Qed.
Lemma lem4774463 {A : Type'} (s : A -> Prop) (z : nat) (f : nat -> A) : (term73 A s f z) = (term74 A s z f).
Proof. exact (eq_refl (term73 A s f z)). Qed.
Lemma lem4774464 {A : Type'} (s : A -> Prop) (z : nat) (f : nat -> A) : (term72 A s f z) = (term74 A s z f).
Proof. exact (TRANS (@lem4774462 A s f z) (@lem4774463 A s z f)). Qed.
Lemma lem4774465 {A : Type'} (f : nat -> A) (z : nat) : (f z) = (f z).
Proof. exact (eq_refl (f z)). Qed.
Lemma lem4774466 {A : Type'} (s : A -> Prop) (f : nat -> A) (z : nat) : (term101 A s f z) = (term102 A s f z).
Proof. exact (MK_COMB (@lem4774464 A s z f) (@lem4774465 A f z)). Qed.
Lemma lem4774467 {A : Type'} (s : A -> Prop) (f : nat -> A) (z : nat) : (term102 A s f z) = (term103 A s f z).
Proof. exact (eq_refl (term102 A s f z)). Qed.
Lemma lem4774468 {A : Type'} (s : A -> Prop) (f : nat -> A) (z : nat) : (term101 A s f z) = (term103 A s f z).
Proof. exact (TRANS (@lem4774466 A s f z) (@lem4774467 A s f z)). Qed.
Lemma lem4774469 (z : nat) (n : nat) : (term104 z n) = (term104 z n).
Proof. exact (eq_refl (term104 z n)). Qed.
Lemma lem4774470 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) (z : nat) : (term105 A n s f z) = (term106 A n s f z).
Proof. exact (MK_COMB (@lem4774469 z n) (@lem4774468 A s f z)). Qed.
Lemma lem4774471 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) : (term107 A n s f) = (term108 A n s f).
Proof. exact (fun_ext (fun z : nat => @lem4774470 A n s f z)). Qed.
Lemma lem4774472 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4774473 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) : (term109 A n s f) = (term110 A n s f).
Proof. exact (MK_COMB (@lem4774472) (@lem4774471 A n s f)). Qed.
Lemma lem4774474 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4774475 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) : (term111 A n s f) = (term112 A n s f).
Proof. exact (MK_COMB (@lem4774474) (@lem4774473 A n s f)). Qed.
Lemma lem4774476 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term70 A s f) = (term71 A s f).
Proof. exact (eq_refl (term70 A s f)). Qed.
Lemma lem4774477 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4774478 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term72 A s f n) = (term73 A s f n).
Proof. exact (MK_COMB (@lem4774476 A s f) (@lem4774477 n)). Qed.
Lemma lem4774479 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term73 A s f n) = (term74 A s n f).
Proof. exact (eq_refl (term73 A s f n)). Qed.
Lemma lem4774480 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term72 A s f n) = (term74 A s n f).
Proof. exact (TRANS (@lem4774478 A s f n) (@lem4774479 A s n f)). Qed.
Lemma lem4774481 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4774482 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term75 A s f n y) = (term76 A s n f y).
Proof. exact (MK_COMB (@lem4774480 A s n f) (@lem4774481 A y)). Qed.
Lemma lem4774483 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term76 A s n f y) = (term77 A s n f y).
Proof. exact (eq_refl (term76 A s n f y)). Qed.
Lemma lem4774484 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term75 A s f n y) = (term77 A s n f y).
Proof. exact (TRANS (@lem4774482 A s n f y) (@lem4774483 A s n f y)). Qed.
Lemma lem4774485 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term113 A s f n) = (term74 A s n f).
Proof. exact (fun_ext (fun y : A => @lem4774484 A s n f y)). Qed.
Lemma lem4774486 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4774487 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term114 A s f n) = (term115 A s n f).
Proof. exact (MK_COMB (@lem4774486 A) (@lem4774485 A s n f)). Qed.
Lemma lem4774488 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term116 A s f n) = (term117 A s n f).
Proof. exact (MK_COMB (@lem4774475 A n s f) (@lem4774487 A s n f)). Qed.
Lemma lem4774489 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term118 A s f) = (term119 A s f).
Proof. exact (fun_ext (fun n : nat => @lem4774488 A s n f)). Qed.
Lemma lem4774490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4774491 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term120 A s f) = (term121 A s f).
Proof. exact (MK_COMB (@lem4774490) (@lem4774489 A s f)). Qed.
Lemma lem4774492 {A : Type'} (s : A -> Prop) : (term122 A s) = (term123 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem4774491 A s f)). Qed.
Lemma lem4774493 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4774494 {A : Type'} (s : A -> Prop) : (term124 A s) = (term125 A s).
Proof. exact (MK_COMB (@lem4774493 A) (@lem4774492 A s)). Qed.
Lemma lem4774495 {A : Type'} (s : A -> Prop) : (term126 A s) = (term127 A s).
Proof. exact (MK_COMB (@lem4774459 A s) (@lem4774494 A s)). Qed.
Lemma lem4774496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4774497 {A : Type'} (s : A -> Prop) : (term128 A s) = (term129 A s).
Proof. exact (MK_COMB (@lem4774496) (@lem4774495 A s)). Qed.
Lemma lem4774498 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term70 A s f) = (term71 A s f).
Proof. exact (eq_refl (term70 A s f)). Qed.
Lemma lem4774499 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4774500 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term72 A s f n) = (term73 A s f n).
Proof. exact (MK_COMB (@lem4774498 A s f) (@lem4774499 n)). Qed.
Lemma lem4774501 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term73 A s f n) = (term74 A s n f).
Proof. exact (eq_refl (term73 A s f n)). Qed.
Lemma lem4774502 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term72 A s f n) = (term74 A s n f).
Proof. exact (TRANS (@lem4774500 A s f n) (@lem4774501 A s n f)). Qed.
Lemma lem4774503 {A : Type'} (f : nat -> A) (n : nat) : (f n) = (f n).
Proof. exact (eq_refl (f n)). Qed.
Lemma lem4774504 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term101 A s f n) = (term102 A s f n).
Proof. exact (MK_COMB (@lem4774502 A s n f) (@lem4774503 A f n)). Qed.
Lemma lem4774505 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term102 A s f n) = (term103 A s f n).
Proof. exact (eq_refl (term102 A s f n)). Qed.
Lemma lem4774506 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term101 A s f n) = (term103 A s f n).
Proof. exact (TRANS (@lem4774504 A s f n) (@lem4774505 A s f n)). Qed.
Lemma lem4774507 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term130 A s f) = (term131 A s f).
Proof. exact (fun_ext (fun n : nat => @lem4774506 A s f n)). Qed.
Lemma lem4774508 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4774509 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term132 A s f) = (term133 A s f).
Proof. exact (MK_COMB (@lem4774508) (@lem4774507 A s f)). Qed.
Lemma lem4774510 {A : Type'} (s : A -> Prop) : (term134 A s) = (term135 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem4774509 A s f)). Qed.
Lemma lem4774511 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem4774512 {A : Type'} (s : A -> Prop) : (term136 A s) = (term67 A s).
Proof. exact (MK_COMB (@lem4774511 A) (@lem4774510 A s)). Qed.
Lemma lem4774513 {A : Type'} (s : A -> Prop) : (term68 A s) = (term137 A s).
Proof. exact (MK_COMB (@lem4774497 A s) (@lem4774512 A s)). Qed.
Lemma lem4774514 {A : Type'} (s : A -> Prop) : term137 A s.
Proof. exact (EQ_MP (@lem4774513 A s) (@lem4774422 A s)). Qed.
Lemma lem4774536 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term138 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4774537 (p : Prop) (q : Prop) (p' : Prop) : term139 p q p'.
Proof. exact (fun q' : Prop => @lem4774536 p q p' q'). Qed.
Lemma lem4774538 (p : Prop) (q : Prop) : term140 p q.
Proof. exact (fun p' : Prop => @lem4774537 p q p'). Qed.
Lemma lem4774539 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) : term141 A f s n g y.
Proof. exact (@lem4774538 (term142 A n f g) ((term77 A s n f y) = (term77 A s n g y))). Qed.
Lemma lem4774540 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) (p' : Prop) : term143 A f s n g y p'.
Proof. exact (@lem4774539 A f s n g y p'). Qed.
Lemma lem4774541 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) (p' : Prop) : (term143 A f s n g y p') = (term144 A f s n g y p').
Proof. exact (eq_refl (term143 A f s n g y p')). Qed.
Lemma lem4774542 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) (p' : Prop) : term144 A f s n g y p'.
Proof. exact (EQ_MP (@lem4774541 A f s n g y p') (@lem4774540 A f s n g y p')). Qed.
Lemma lem4774543 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) (p' : Prop) (q' : Prop) : term145 A f s n g y p' q'.
Proof. exact (@lem4774542 A f s n g y p' q'). Qed.
Lemma lem4774544 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) (p' : Prop) (q' : Prop) : (term145 A f s n g y p' q') = (term146 A f s n g y p' q').
Proof. exact (eq_refl (term145 A f s n g y p' q')). Qed.
Lemma lem4774545 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) (p' : Prop) (q' : Prop) : term146 A f s n g y p' q'.
Proof. exact (EQ_MP (@lem4774544 A f s n g y p' q') (@lem4774543 A f s n g y p' q')). Qed.
Lemma lem4774577 {A : Type'} (n : nat) (f : nat -> A) (g : nat -> A) : (term142 A n f g) = (term142 A n f g).
Proof. exact (eq_refl (term142 A n f g)). Qed.
Lemma lem4774578 {A : Type'} (s : A -> Prop) (y : A) (n : nat) (f : nat -> A) (g : nat -> A) (q' : Prop) : term147 A s y n f g q'.
Proof. exact (@lem4774545 A f s n g y (term142 A n f g) q'). Qed.
Lemma lem4774579 {A : Type'} (s : A -> Prop) (y : A) (n : nat) (f : nat -> A) (g : nat -> A) (q' : Prop) : term148 A s y n f g q'.
Proof. exact (@lem4774578 A s y n f g q' (@lem4774577 A n f g)). Qed.
Lemma lem4774580 {A : Type'} (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : term142 A n f g.
Proof. exact (h1). Qed.
Lemma lem4774581 {A : Type'} (z : nat) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : term149 A n f g z.
Proof. exact (@lem4774580 A n f g h1 z). Qed.
Lemma lem4774582 {A : Type'} (n : nat) (f : nat -> A) (g : nat -> A) (z : nat) : (term149 A n f g z) = (term150 A n f g z).
Proof. exact (eq_refl (term149 A n f g z)). Qed.
Lemma lem4774583 {A : Type'} (z : nat) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : term150 A n f g z.
Proof. exact (EQ_MP (@lem4774582 A n f g z) (@lem4774581 A z n f g h1)). Qed.
Lemma lem4774584 (z : nat) (n : nat) (h1 : Peano.lt z n) : Peano.lt z n.
Proof. exact (h1). Qed.
Lemma lem4774585 {A : Type'} (f : nat -> A) (g : nat -> A) (z : nat) (n : nat) (h1 : term142 A n f g) (h2 : Peano.lt z n) : (f z) = (g z).
Proof. exact (@lem4774583 A z n f g h1 (@lem4774584 z n h2)). Qed.
Lemma lem4774602 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term138 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4774603 (p : Prop) (q : Prop) (p' : Prop) : term139 p q p'.
Proof. exact (fun q' : Prop => @lem4774602 p q p' q'). Qed.
Lemma lem4774604 (p : Prop) (q : Prop) : term140 p q.
Proof. exact (fun p' : Prop => @lem4774603 p q p'). Qed.
Lemma lem4774605 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) : term151 A n f m y.
Proof. exact (@lem4774604 (Peano.lt m n) (term152 A f m y)). Qed.
Lemma lem4774606 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) (p' : Prop) : term153 A n f m y p'.
Proof. exact (@lem4774605 A n f m y p'). Qed.
Lemma lem4774607 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) (p' : Prop) : (term153 A n f m y p') = (term154 A n f m y p').
Proof. exact (eq_refl (term153 A n f m y p')). Qed.
Lemma lem4774608 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) (p' : Prop) : term154 A n f m y p'.
Proof. exact (EQ_MP (@lem4774607 A n f m y p') (@lem4774606 A n f m y p')). Qed.
Lemma lem4774609 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) (p' : Prop) (q' : Prop) : term155 A n f m y p' q'.
Proof. exact (@lem4774608 A n f m y p' q'). Qed.
Lemma lem4774610 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) (p' : Prop) (q' : Prop) : (term155 A n f m y p' q') = (term156 A n f m y p' q').
Proof. exact (eq_refl (term155 A n f m y p' q')). Qed.
Lemma lem4774611 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) (p' : Prop) (q' : Prop) : term156 A n f m y p' q'.
Proof. exact (EQ_MP (@lem4774610 A n f m y p' q') (@lem4774609 A n f m y p' q')). Qed.
Lemma lem4774612 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem4774613 {A : Type'} (f : nat -> A) (y : A) (m : nat) (n : nat) (q' : Prop) : term157 A f y m n q'.
Proof. exact (@lem4774611 A n f m y (Peano.lt m n) q'). Qed.
Lemma lem4774614 {A : Type'} (f : nat -> A) (y : A) (m : nat) (n : nat) (q' : Prop) : term158 A f y m n q'.
Proof. exact (@lem4774613 A f y m n q' (@lem4774612 m n)). Qed.
Lemma lem4774615 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem4774616 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem4774621 {A : Type'} (z : nat) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : term150 A n f g z.
Proof. exact (fun h0 : Peano.lt z n => @lem4774585 A f g z n h1 h0). Qed.
Lemma lem4774622 {A : Type'} (m : nat) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : term150 A n f g m.
Proof. exact (@lem4774621 A m n f g h1). Qed.
Lemma lem4774624 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem4774616 m n) (@lem4774615 m n h1)). Qed.
Lemma lem4774625 (m : nat) (n : nat) (h1 : Peano.lt m n) : True = (Peano.lt m n).
Proof. exact (SYM (@lem4774624 m n h1)). Qed.
Lemma lem4774626 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem4774625 m n h1) (@lem0)). Qed.
Lemma lem4774627 {A : Type'} (f : nat -> A) (g : nat -> A) (m : nat) (n : nat) (h1 : term142 A n f g) (h2 : Peano.lt m n) : (f m) = (g m).
Proof. exact (@lem4774622 A m n f g h1 (@lem4774626 m n h2)). Qed.
Lemma lem4774628 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4774629 {A : Type'} (f : nat -> A) (g : nat -> A) (m : nat) (n : nat) (h1 : term142 A n f g) (h2 : Peano.lt m n) : (term159 A f m) = (term159 A g m).
Proof. exact (MK_COMB (@lem4774628 A) (@lem4774627 A f g m n h1 h2)). Qed.
Lemma lem4774630 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4774631 {A : Type'} (y : A) (f : nat -> A) (g : nat -> A) (m : nat) (n : nat) (h1 : term142 A n f g) (h2 : Peano.lt m n) : ((f m) = y) = ((g m) = y).
Proof. exact (MK_COMB (@lem4774629 A f g m n h1 h2) (@lem4774630 A y)). Qed.
Lemma lem4774634 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4774635 {A : Type'} (y : A) (f : nat -> A) (g : nat -> A) (m : nat) (n : nat) (h1 : term142 A n f g) (h2 : Peano.lt m n) : (term152 A f m y) = (term152 A g m y).
Proof. exact (MK_COMB (@lem4774634) (@lem4774631 A y f g m n h1 h2)). Qed.
Lemma lem4774638 {A : Type'} (m : nat) (y : A) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : term160 A n f g m y.
Proof. exact (fun h0 : Peano.lt m n => @lem4774635 A y f g m n h1 h0). Qed.
Lemma lem4774639 {A : Type'} (f : nat -> A) (n : nat) (g : nat -> A) (m : nat) (y : A) : term161 A f n g m y.
Proof. exact (@lem4774614 A f y m n (term152 A g m y)). Qed.
Lemma lem4774640 {A : Type'} (m : nat) (y : A) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : (term162 A n f m y) = (term162 A n g m y).
Proof. exact (@lem4774639 A f n g m y (@lem4774638 A m y n f g h1)). Qed.
Lemma lem4774668 {A : Type'} (y : A) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : (term163 A n f y) = (term163 A n g y).
Proof. exact (fun_ext (fun m : nat => @lem4774640 A m y n f g h1)). Qed.
Lemma lem4774696 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4774697 {A : Type'} (y : A) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : (term164 A n f y) = (term164 A n g y).
Proof. exact (MK_COMB (@lem4774696) (@lem4774668 A y n f g h1)). Qed.
Lemma lem4774729 {A : Type'} (y : A) (s : A -> Prop) : (term165 A y s) = (term165 A y s).
Proof. exact (eq_refl (term165 A y s)). Qed.
Lemma lem4774730 {A : Type'} (s : A -> Prop) (y : A) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : (term77 A s n f y) = (term77 A s n g y).
Proof. exact (MK_COMB (@lem4774729 A y s) (@lem4774697 A y n f g h1)). Qed.
Lemma lem4774764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4774765 {A : Type'} (s : A -> Prop) (y : A) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : (term79 A s n f y) = (term79 A s n g y).
Proof. exact (MK_COMB (@lem4774764) (@lem4774730 A s y n f g h1)). Qed.
Lemma lem4774832 {A : Type'} (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) : (term77 A s n g y) = (term77 A s n g y).
Proof. exact (eq_refl (term77 A s n g y)). Qed.
Lemma lem4774833 {A : Type'} (s : A -> Prop) (y : A) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : ((term77 A s n f y) = (term77 A s n g y)) = ((term77 A s n g y) = (term77 A s n g y)).
Proof. exact (MK_COMB (@lem4774765 A s y n f g h1) (@lem4774832 A s n g y)). Qed.
Lemma lem4774835 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4774836 (x : Prop) : (x = x) = True.
Proof. exact (@lem4774835 Prop x). Qed.
Lemma lem4774837 {A : Type'} (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) : ((term77 A s n g y) = (term77 A s n g y)) = True.
Proof. exact (@lem4774836 (term77 A s n g y)). Qed.
Lemma lem4774838 {A : Type'} (s : A -> Prop) (y : A) (n : nat) (f : nat -> A) (g : nat -> A) (h1 : term142 A n f g) : ((term77 A s n f y) = (term77 A s n g y)) = True.
Proof. exact (TRANS (@lem4774833 A s y n f g h1) (@lem4774837 A s n g y)). Qed.
Lemma lem4774839 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) : term166 A f s n g y.
Proof. exact (fun h0 : term142 A n f g => @lem4774838 A s y n f g h0). Qed.
Lemma lem4774840 {A : Type'} (s : A -> Prop) (y : A) (n : nat) (f : nat -> A) (g : nat -> A) : term167 A s y n f g.
Proof. exact (@lem4774579 A s y n f g True). Qed.
Lemma lem4774841 {A : Type'} (s : A -> Prop) (y : A) (n : nat) (f : nat -> A) (g : nat -> A) : (term82 A f s n g y) = (term168 A n f g).
Proof. exact (@lem4774840 A s y n f g (@lem4774839 A f s n g y)). Qed.
Lemma lem4774843 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4774844 {A : Type'} (n : nat) (f : nat -> A) (g : nat -> A) : (term168 A n f g) = True.
Proof. exact (@lem4774843 (term142 A n f g)). Qed.
Lemma lem4774845 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) (y : A) : (term82 A f s n g y) = True.
Proof. exact (TRANS (@lem4774841 A s y n f g) (@lem4774844 A n f g)). Qed.
Lemma lem4774846 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) : (term84 A f s n g) = (term169 A).
Proof. exact (fun_ext (fun y : A => @lem4774845 A f s n g y)). Qed.
Lemma lem4774847 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4774848 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) : (term86 A f s n g) = (term170 A).
Proof. exact (MK_COMB (@lem4774847 A) (@lem4774846 A f s n g)). Qed.
Lemma lem4774850 {A : Type'} (t : Prop) : (term171 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4774851 {A : Type'} (t : Prop) : (term171 A t) = t.
Proof. exact (@lem4774850 A t). Qed.
Lemma lem4774852 {A : Type'} : (term170 A) = True.
Proof. exact (@lem4774851 A True). Qed.
Lemma lem4774853 {A : Type'} (f : nat -> A) (s : A -> Prop) (n : nat) (g : nat -> A) : (term86 A f s n g) = True.
Proof. exact (TRANS (@lem4774848 A f s n g) (@lem4774852 A)). Qed.
Lemma lem4774854 {A : Type'} (f : nat -> A) (s : A -> Prop) (g : nat -> A) : (term88 A f s g) = term172.
Proof. exact (fun_ext (fun n : nat => @lem4774853 A f s n g)). Qed.
Lemma lem4774855 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4774856 {A : Type'} (f : nat -> A) (s : A -> Prop) (g : nat -> A) : (term90 A f s g) = term173.
Proof. exact (MK_COMB (@lem4774855) (@lem4774854 A f s g)). Qed.
Lemma lem4774858 {A : Type'} (t : Prop) : (term171 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4774859 (t : Prop) : (term174 t) = t.
Proof. exact (@lem4774858 nat t). Qed.
Lemma lem4774860 : term173 = True.
Proof. exact (@lem4774859 True). Qed.
Lemma lem4774861 {A : Type'} (f : nat -> A) (s : A -> Prop) (g : nat -> A) : (term90 A f s g) = True.
Proof. exact (TRANS (@lem4774856 A f s g) (@lem4774860)). Qed.
Lemma lem4774862 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term92 A f s) = (term175 A).
Proof. exact (fun_ext (fun g : nat -> A => @lem4774861 A f s g)). Qed.
Lemma lem4774863 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4774864 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term94 A f s) = (term176 A).
Proof. exact (MK_COMB (@lem4774863 A) (@lem4774862 A f s)). Qed.
Lemma lem4774866 {A : Type'} (t : Prop) : (term171 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4774867 {A : Type'} (t : Prop) : (term177 A t) = t.
Proof. exact (@lem4774866 (nat -> A) t). Qed.
Lemma lem4774868 {A : Type'} : (term176 A) = True.
Proof. exact (@lem4774867 A True). Qed.
Lemma lem4774869 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term94 A f s) = True.
Proof. exact (TRANS (@lem4774864 A f s) (@lem4774868 A)). Qed.
Lemma lem4774870 {A : Type'} (s : A -> Prop) : (term96 A s) = (term175 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem4774869 A f s)). Qed.
Lemma lem4774871 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4774872 {A : Type'} (s : A -> Prop) : (term98 A s) = (term176 A).
Proof. exact (MK_COMB (@lem4774871 A) (@lem4774870 A s)). Qed.
Lemma lem4774874 {A : Type'} (t : Prop) : (term171 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4774875 {A : Type'} (t : Prop) : (term177 A t) = t.
Proof. exact (@lem4774874 (nat -> A) t). Qed.
Lemma lem4774876 {A : Type'} : (term176 A) = True.
Proof. exact (@lem4774875 A True). Qed.
Lemma lem4774877 {A : Type'} (s : A -> Prop) : (term98 A s) = True.
Proof. exact (TRANS (@lem4774872 A s) (@lem4774876 A)). Qed.
Lemma lem4774878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4774879 {A : Type'} (s : A -> Prop) : (term100 A s) = (and True).
Proof. exact (MK_COMB (@lem4774878) (@lem4774877 A s)). Qed.
Lemma lem4775221 {A : Type'} (s : A -> Prop) : (term125 A s) = (term125 A s).
Proof. exact (eq_refl (term125 A s)). Qed.
Lemma lem4775222 {A : Type'} (s : A -> Prop) : (term127 A s) = (term178 A s).
Proof. exact (MK_COMB (@lem4774879 A s) (@lem4775221 A s)). Qed.
Lemma lem4775224 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4775225 {A : Type'} (s : A -> Prop) : (term178 A s) = (term125 A s).
Proof. exact (@lem4775224 (term125 A s)). Qed.
Lemma lem4775567 {A : Type'} (s : A -> Prop) : (term127 A s) = (term125 A s).
Proof. exact (TRANS (@lem4775222 A s) (@lem4775225 A s)). Qed.
Lemma lem4775568 {A : Type'} (s : A -> Prop) : (term125 A s) = (term127 A s).
Proof. exact (SYM (@lem4775567 A s)). Qed.
Lemma lem4775573 {A : Type'} (s : A -> Prop) : term49 A s.
Proof. exact (EQ_MP (@lem4774390 A s) (@lem4774389 A s)). Qed.
Lemma lem4775574 {A : Type'} (s : A -> Prop) : term49 A s.
Proof. exact (@lem4775573 A s). Qed.
Lemma lem4775575 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : term48 A s.
Proof. exact (@lem4775574 A s (@lem4774413 A s h1)). Qed.
Lemma lem4775576 {A : Type'} (f : nat -> A) (n : nat) (s : A -> Prop) (h1 : @INFINITE A s) : term179 A s f n.
Proof. exact (@lem4775575 A s h1 (term180 A f n)). Qed.
Lemma lem4775577 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term179 A s f n) = (term181 A s f n).
Proof. exact (eq_refl (term179 A s f n)). Qed.
Lemma lem4775578 {A : Type'} (f : nat -> A) (n : nat) (s : A -> Prop) (h1 : @INFINITE A s) : term181 A s f n.
Proof. exact (EQ_MP (@lem4775577 A s f n) (@lem4775576 A f n s h1)). Qed.
Lemma lem4775582 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term138 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4775583 (p : Prop) (q : Prop) (p' : Prop) : term139 p q p'.
Proof. exact (fun q' : Prop => @lem4775582 p q p' q'). Qed.
Lemma lem4775584 (p : Prop) (q : Prop) : term140 p q.
Proof. exact (fun p' : Prop => @lem4775583 p q p'). Qed.
Lemma lem4775585 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term182 A s n f.
Proof. exact (@lem4775584 (term181 A s f n) (term115 A s n f)). Qed.
Lemma lem4775586 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (p' : Prop) : term183 A s n f p'.
Proof. exact (@lem4775585 A s n f p'). Qed.
Lemma lem4775587 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (p' : Prop) : (term183 A s n f p') = (term184 A s n f p').
Proof. exact (eq_refl (term183 A s n f p')). Qed.
Lemma lem4775588 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (p' : Prop) : term184 A s n f p'.
Proof. exact (EQ_MP (@lem4775587 A s n f p') (@lem4775586 A s n f p')). Qed.
Lemma lem4775589 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (p' : Prop) (q' : Prop) : term185 A s n f p' q'.
Proof. exact (@lem4775588 A s n f p' q'). Qed.
Lemma lem4775590 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (p' : Prop) (q' : Prop) : (term185 A s n f p' q') = (term186 A s n f p' q').
Proof. exact (eq_refl (term185 A s n f p' q')). Qed.
Lemma lem4775591 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (p' : Prop) (q' : Prop) : term186 A s n f p' q'.
Proof. exact (EQ_MP (@lem4775590 A s n f p' q') (@lem4775589 A s n f p' q')). Qed.
Lemma lem4775595 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term138 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4775596 (p : Prop) (q : Prop) (p' : Prop) : term139 p q p'.
Proof. exact (fun q' : Prop => @lem4775595 p q p' q'). Qed.
Lemma lem4775597 (p : Prop) (q : Prop) : term140 p q.
Proof. exact (fun p' : Prop => @lem4775596 p q p'). Qed.
Lemma lem4775598 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : term187 A s f n.
Proof. exact (@lem4775597 (term188 A f n) (term189 A s f n)). Qed.
Lemma lem4775599 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (p' : Prop) : term190 A s f n p'.
Proof. exact (@lem4775598 A s f n p'). Qed.
Lemma lem4775600 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (p' : Prop) : (term190 A s f n p') = (term191 A s f n p').
Proof. exact (eq_refl (term190 A s f n p')). Qed.
Lemma lem4775601 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (p' : Prop) : term191 A s f n p'.
Proof. exact (EQ_MP (@lem4775600 A s f n p') (@lem4775599 A s f n p')). Qed.
Lemma lem4775602 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (p' : Prop) (q' : Prop) : term192 A s f n p' q'.
Proof. exact (@lem4775601 A s f n p' q'). Qed.
Lemma lem4775603 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (p' : Prop) (q' : Prop) : (term192 A s f n p' q') = (term193 A s f n p' q').
Proof. exact (eq_refl (term192 A s f n p' q')). Qed.
Lemma lem4775604 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (p' : Prop) (q' : Prop) : term193 A s f n p' q'.
Proof. exact (EQ_MP (@lem4775603 A s f n p' q') (@lem4775602 A s f n p' q')). Qed.
Lemma lem4775606 {A B : Type'} (f : A -> B) (s : A -> Prop) : term194 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4774339 A B f s h0). Qed.
Lemma lem4775607 {A : Type'} (f : nat -> A) (s : nat -> Prop) : term195 A f s.
Proof. exact (@lem4775606 nat A f s). Qed.
Lemma lem4775608 {A : Type'} (f : nat -> A) (n : nat) : term196 A f n.
Proof. exact (@lem4775607 A f (term197 n)). Qed.
Lemma lem4775610 (n : nat) : (term26 n) = True.
Proof. exact (EQ_MP (@lem4774328 n) (@lem4774327 n)). Qed.
Lemma lem4775611 (n : nat) : True = (term26 n).
Proof. exact (SYM (@lem4775610 n)). Qed.
Lemma lem4775612 (n : nat) : term26 n.
Proof. exact (EQ_MP (@lem4775611 n) (@lem0)). Qed.
Lemma lem4775613 {A : Type'} (f : nat -> A) (n : nat) : (term188 A f n) = True.
Proof. exact (@lem4775608 A f n (@lem4775612 n)). Qed.
Lemma lem4775614 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (q' : Prop) : term198 A s f n q'.
Proof. exact (@lem4775604 A s f n True q'). Qed.
Lemma lem4775615 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (q' : Prop) : term199 A s f n q'.
Proof. exact (@lem4775614 A s f n q' (@lem4775613 A f n)). Qed.
Lemma lem4775625 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term189 A s f n) = (term189 A s f n).
Proof. exact (eq_refl (term189 A s f n)). Qed.
Lemma lem4775626 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : term200 A s f n.
Proof. exact (fun h0 : True => @lem4775625 A s f n). Qed.
Lemma lem4775627 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : term201 A s f n.
Proof. exact (@lem4775615 A s f n (term189 A s f n)). Qed.
Lemma lem4775628 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term181 A s f n) = (term202 A s f n).
Proof. exact (@lem4775627 A s f n (@lem4775626 A s f n)). Qed.
Lemma lem4775630 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4775631 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term202 A s f n) = (term189 A s f n).
Proof. exact (@lem4775630 (term189 A s f n)). Qed.
Lemma lem4775636 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term181 A s f n) = (term189 A s f n).
Proof. exact (TRANS (@lem4775628 A s f n) (@lem4775631 A s f n)). Qed.
Lemma lem4775637 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (q' : Prop) : term203 A s f n q'.
Proof. exact (@lem4775591 A s n f (term189 A s f n) q'). Qed.
Lemma lem4775638 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (q' : Prop) : term204 A s f n q'.
Proof. exact (@lem4775637 A s f n q' (@lem4775636 A s f n)). Qed.
Lemma lem4775679 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term115 A s n f) = (term115 A s n f).
Proof. exact (eq_refl (term115 A s n f)). Qed.
Lemma lem4775680 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term205 A s n f.
Proof. exact (fun h0 : term189 A s f n => @lem4775679 A s n f). Qed.
Lemma lem4775681 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term206 A s n f.
Proof. exact (@lem4775638 A s f n (term115 A s n f)). Qed.
Lemma lem4775682 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term207 A s n f) = (term208 A s n f).
Proof. exact (@lem4775681 A s n f (@lem4775680 A s n f)). Qed.
Lemma lem4775788 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term208 A s n f) = (term207 A s n f).
Proof. exact (SYM (@lem4775682 A s n f)). Qed.
Lemma lem4775789 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (h1 : term189 A s f n) : term189 A s f n.
Proof. exact (h1). Qed.
Lemma lem4775791 {_93152 : Type'} (s : _93152 -> Prop) : term24 _93152 s.
Proof. exact (EQ_MP (@lem4774323 _93152 s) (@lem4774322 _93152 s)). Qed.
Lemma lem4775792 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (@lem4775791 A s). Qed.
Lemma lem4775793 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : term209 A s f n.
Proof. exact (@lem4775792 A (term210 A s f n)). Qed.
Lemma lem4775794 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (h1 : term189 A s f n) : term211 A s f n.
Proof. exact (@lem4775793 A s f n (@lem4775789 A s f n h1)). Qed.
Lemma lem4775800 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term212 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4775801 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term212 A s t).
Proof. exact (@lem4775800 A s t). Qed.
Lemma lem4775802 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : ((term210 A s f n) = (@EMPTY A)) = (term213 A s f n).
Proof. exact (@lem4775801 A (term210 A s f n) (@EMPTY A)). Qed.
Lemma lem4775815 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4775816 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term211 A s f n) = (term214 A s f n).
Proof. exact (MK_COMB (@lem4775815) (@lem4775802 A s f n)). Qed.
Lemma lem4775817 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4775818 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term215 A s f n) = (term216 A s f n).
Proof. exact (MK_COMB (@lem4775817) (@lem4775816 A s f n)). Qed.
Lemma lem4775835 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term115 A s n f) = (term115 A s n f).
Proof. exact (eq_refl (term115 A s n f)). Qed.
Lemma lem4775836 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term217 A s n f) = (term218 A s n f).
Proof. exact (MK_COMB (@lem4775818 A s f n) (@lem4775835 A s n f)). Qed.
Lemma lem4775839 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term218 A s n f) = (term217 A s n f).
Proof. exact (SYM (@lem4775836 A s n f)). Qed.
Lemma lem4775849 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term219 A x s t) = (term220 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4775850 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term219 A x s t) = (term220 A s x t).
Proof. exact (@lem4775849 A s x t). Qed.
Lemma lem4775851 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term221 A x s f n) = (term222 A s x f n).
Proof. exact (@lem4775850 A s x (term180 A f n)). Qed.
Lemma lem4775855 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4775856 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4775855 A P x). Qed.
Lemma lem4775857 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4775856 A s x). Qed.
Lemma lem4775858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4775859 {A : Type'} (s : A -> Prop) (x : A) : (term165 A x s) = (term223 A s x).
Proof. exact (MK_COMB (@lem4775858) (@lem4775857 A s x)). Qed.
Lemma lem4775861 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term224 A B y f s) = (term225 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4775862 {A : Type'} (y : A) (f : nat -> A) (s : nat -> Prop) : (term226 A y f s) = (term227 A y f s).
Proof. exact (@lem4775861 nat A y f s). Qed.
Lemma lem4775863 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term228 A x f n) = (term229 A x f n).
Proof. exact (@lem4775862 A x f (term197 n)). Qed.
Lemma lem4775873 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term230 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4775874 (p : nat -> Prop) (x : nat) : (term231 x p) = (p x).
Proof. exact (@lem4775873 nat p x). Qed.
Lemma lem4775875 (n : nat) (x : nat) : (term232 x n) = (term233 n x).
Proof. exact (@lem4775874 (term234 n) x). Qed.
Lemma lem4775876 (m : nat) (n : nat) : (term233 n m) = (Peano.lt m n).
Proof. exact (eq_refl (term233 n m)). Qed.
Lemma lem4775877 (GEN_PVAR_209 : nat) : (@SETSPEC nat GEN_PVAR_209) = (@SETSPEC nat GEN_PVAR_209).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_209)). Qed.
Lemma lem4775878 (GEN_PVAR_209 : nat) (m : nat) (n : nat) : (term235 GEN_PVAR_209 n m) = (term236 GEN_PVAR_209 m n).
Proof. exact (MK_COMB (@lem4775877 GEN_PVAR_209) (@lem4775876 m n)). Qed.
Lemma lem4775879 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4775880 (GEN_PVAR_209 : nat) (n : nat) (m : nat) : (term237 GEN_PVAR_209 n m) = (term238 GEN_PVAR_209 n m).
Proof. exact (MK_COMB (@lem4775878 GEN_PVAR_209 m n) (@lem4775879 m)). Qed.
Lemma lem4775881 (GEN_PVAR_209 : nat) (n : nat) : (term239 GEN_PVAR_209 n) = (term240 GEN_PVAR_209 n).
Proof. exact (fun_ext (fun m : nat => @lem4775880 GEN_PVAR_209 n m)). Qed.
Lemma lem4775882 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4775883 (GEN_PVAR_209 : nat) (n : nat) : (term241 GEN_PVAR_209 n) = (term242 GEN_PVAR_209 n).
Proof. exact (MK_COMB (@lem4775882) (@lem4775881 GEN_PVAR_209 n)). Qed.
Lemma lem4775884 (n : nat) : (term243 n) = (term244 n).
Proof. exact (fun_ext (fun GEN_PVAR_209 : nat => @lem4775883 GEN_PVAR_209 n)). Qed.
Lemma lem4775885 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4775886 (n : nat) : (term245 n) = (term197 n).
Proof. exact (MK_COMB (@lem4775885) (@lem4775884 n)). Qed.
Lemma lem4775887 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem4775888 (x : nat) (n : nat) : (term232 x n) = (term246 x n).
Proof. exact (MK_COMB (@lem4775887 x) (@lem4775886 n)). Qed.
Lemma lem4775889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4775890 (x : nat) (n : nat) : (term247 x n) = (term248 x n).
Proof. exact (MK_COMB (@lem4775889) (@lem4775888 x n)). Qed.
Lemma lem4775891 (x : nat) (n : nat) : (term233 n x) = (Peano.lt x n).
Proof. exact (eq_refl (term233 n x)). Qed.
Lemma lem4775892 (x : nat) (n : nat) : ((term232 x n) = (term233 n x)) = ((term246 x n) = (Peano.lt x n)).
Proof. exact (MK_COMB (@lem4775890 x n) (@lem4775891 x n)). Qed.
Lemma lem4775893 (x : nat) (n : nat) : (term246 x n) = (Peano.lt x n).
Proof. exact (EQ_MP (@lem4775892 x n) (@lem4775875 n x)). Qed.
Lemma lem4775894 {A : Type'} (x : A) (f : nat -> A) (x' : nat) : (term249 A x f x') = (term249 A x f x').
Proof. exact (eq_refl (term249 A x f x')). Qed.
Lemma lem4775895 {A : Type'} (x : A) (f : nat -> A) (x' : nat) (n : nat) : (term250 A x f x' n) = (term251 A x f x' n).
Proof. exact (MK_COMB (@lem4775894 A x f x') (@lem4775893 x' n)). Qed.
Lemma lem4775898 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term252 A x f n) = (term253 A x f n).
Proof. exact (fun_ext (fun x' : nat => @lem4775895 A x f x' n)). Qed.
Lemma lem4775899 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4775900 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term229 A x f n) = (term254 A x f n).
Proof. exact (MK_COMB (@lem4775899) (@lem4775898 A x f n)). Qed.
Lemma lem4775905 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term228 A x f n) = (term254 A x f n).
Proof. exact (TRANS (@lem4775863 A x f n) (@lem4775900 A x f n)). Qed.
Lemma lem4775906 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4775907 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term255 A x f n) = (term256 A x f n).
Proof. exact (MK_COMB (@lem4775906) (@lem4775905 A x f n)). Qed.
Lemma lem4775908 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term222 A s x f n) = (term257 A s x f n).
Proof. exact (MK_COMB (@lem4775859 A s x) (@lem4775907 A x f n)). Qed.
Lemma lem4775911 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term221 A x s f n) = (term257 A s x f n).
Proof. exact (TRANS (@lem4775851 A s x f n) (@lem4775908 A s x f n)). Qed.
Lemma lem4775912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4775913 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term258 A x s f n) = (term259 A s x f n).
Proof. exact (MK_COMB (@lem4775912) (@lem4775911 A s x f n)). Qed.
Lemma lem4775915 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4775916 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4775915 A x). Qed.
Lemma lem4775917 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : ((term221 A x s f n) = (@IN A x (@EMPTY A))) = ((term257 A s x f n) = False).
Proof. exact (MK_COMB (@lem4775913 A s x f n) (@lem4775916 A x)). Qed.
Lemma lem4775919 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4775920 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : ((term257 A s x f n) = False) = (term260 A s x f n).
Proof. exact (@lem4775919 (term257 A s x f n)). Qed.
Lemma lem4775931 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : ((term221 A x s f n) = (@IN A x (@EMPTY A))) = (term260 A s x f n).
Proof. exact (TRANS (@lem4775917 A s x f n) (@lem4775920 A s x f n)). Qed.
Lemma lem4775932 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term261 A s f n) = (term262 A s f n).
Proof. exact (fun_ext (fun x : A => @lem4775931 A s x f n)). Qed.
Lemma lem4775933 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4775934 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term213 A s f n) = (term263 A s f n).
Proof. exact (MK_COMB (@lem4775933 A) (@lem4775932 A s f n)). Qed.
Lemma lem4775939 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4775940 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term214 A s f n) = (term264 A s f n).
Proof. exact (MK_COMB (@lem4775939) (@lem4775934 A s f n)). Qed.
Lemma lem4775941 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4775942 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term216 A s f n) = (term265 A s f n).
Proof. exact (MK_COMB (@lem4775941) (@lem4775940 A s f n)). Qed.
Lemma lem4775950 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4775951 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4775950 A P x). Qed.
Lemma lem4775952 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem4775951 A s y). Qed.
Lemma lem4775953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4775954 {A : Type'} (s : A -> Prop) (y : A) : (term165 A y s) = (term223 A s y).
Proof. exact (MK_COMB (@lem4775953) (@lem4775952 A s y)). Qed.
Lemma lem4775963 {A : Type'} (n : nat) (f : nat -> A) (y : A) : (term164 A n f y) = (term164 A n f y).
Proof. exact (eq_refl (term164 A n f y)). Qed.
Lemma lem4775964 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term77 A s n f y) = (term266 A s n f y).
Proof. exact (MK_COMB (@lem4775954 A s y) (@lem4775963 A n f y)). Qed.
Lemma lem4775967 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term74 A s n f) = (term267 A s n f).
Proof. exact (fun_ext (fun y : A => @lem4775964 A s n f y)). Qed.
Lemma lem4775968 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4775969 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term115 A s n f) = (term268 A s n f).
Proof. exact (MK_COMB (@lem4775968 A) (@lem4775967 A s n f)). Qed.
Lemma lem4775974 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term218 A s n f) = (term269 A s n f).
Proof. exact (MK_COMB (@lem4775942 A s f n) (@lem4775969 A s n f)). Qed.
Lemma lem4775977 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term269 A s n f) = (term218 A s n f).
Proof. exact (SYM (@lem4775974 A s n f)). Qed.
Lemma lem4775979 (p : Prop) : p = (term270 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4775980 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term269 A s n f) = (term271 A s n f).
Proof. exact (@lem4775979 (term269 A s n f)). Qed.
Lemma lem4775981 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term271 A s n f) = (term269 A s n f).
Proof. exact (SYM (@lem4775980 A s n f)). Qed.
Lemma lem4775982 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term272 A s n f) : term272 A s n f.
Proof. exact (h1). Qed.
Lemma lem4775985 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term271 A s n f) : term271 A s n f.
Proof. exact (h1). Qed.
Lemma lem4775986 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term273 A s n f.
Proof. exact (fun h0 : term271 A s n f => @lem4775985 A s n f h0). Qed.
Lemma lem4775987 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term273 A s n f) : term273 A s n f.
Proof. exact (h1). Qed.
Lemma lem4775988 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term271 A s n f) : term271 A s n f.
Proof. exact (h1). Qed.
Lemma lem4775989 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term271 A s n f) (h2 : term273 A s n f) : term271 A s n f.
Proof. exact (@lem4775987 A s n f h2 (@lem4775988 A s n f h1)). Qed.
Lemma lem4775990 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term271 A s n f) : term274 A s n f.
Proof. exact (fun h0 : term273 A s n f => @lem4775989 A s n f h1 h0). Qed.
Lemma lem4775991 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term273 A s n f) : term273 A s n f.
Proof. exact (h1). Qed.
Lemma lem4775992 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term271 A s n f) (h2 : term273 A s n f) : term271 A s n f.
Proof. exact (@lem4775990 A s n f h1 (@lem4775991 A s n f h2)). Qed.
Lemma lem4775993 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term273 A s n f) : term273 A s n f.
Proof. exact (fun h0 : term271 A s n f => @lem4775992 A s n f h0 h1). Qed.
Lemma lem4775994 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term275 A s n f.
Proof. exact (fun h0 : term273 A s n f => @lem4775993 A s n f h0). Qed.
Lemma lem4775997 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term273 A s n f.
Proof. exact (@lem4775994 A s n f (@lem4775986 A s n f)). Qed.
Lemma lem4775998 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term273 A s n f.
Proof. exact (@lem4775997 A s n f). Qed.
Lemma lem4776012 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4776013 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term271 A s n f) = (term276 A s n f).
Proof. exact (@lem4776012 (term272 A s n f)). Qed.
Lemma lem4776015 (t : Prop) : (term277 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4776016 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term276 A s n f) = (term269 A s n f).
Proof. exact (@lem4776015 (term269 A s n f)). Qed.
Lemma lem4776019 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term271 A s n f) = (term269 A s n f).
Proof. exact (TRANS (@lem4776013 A s n f) (@lem4776016 A s n f)). Qed.
Lemma lem4776112 {A : Type'} (n : nat) (f : nat -> A) : (term278 A n f) = (term279 A n f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4776019 A s n f)). Qed.
Lemma lem4776113 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4776114 {A : Type'} (n : nat) (f : nat -> A) : (term280 A n f) = (term281 A n f).
Proof. exact (MK_COMB (@lem4776113 A) (@lem4776112 A n f)). Qed.
Lemma lem4776119 {A : Type'} (f : nat -> A) : (term282 A f) = (term283 A f).
Proof. exact (fun_ext (fun n : nat => @lem4776114 A n f)). Qed.
Lemma lem4776120 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4776121 {A : Type'} (f : nat -> A) : (term284 A f) = (term285 A f).
Proof. exact (MK_COMB (@lem4776120) (@lem4776119 A f)). Qed.
Lemma lem4776126 {A : Type'} : (term286 A) = (term287 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem4776121 A f)). Qed.
Lemma lem4776127 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4776136 {A : Type'} : (term288 A) = (term289 A).
Proof. exact (MK_COMB (@lem4776127 A) (@lem4776126 A)). Qed.
Lemma lem4776143 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) : (term162 A n f m y) = (term162 A n f m y).
Proof. exact (eq_refl (term162 A n f m y)). Qed.
Lemma lem4776144 {A : Type'} (n : nat) (f : nat -> A) (y : A) : (term163 A n f y) = (term163 A n f y).
Proof. exact (fun_ext (fun m : nat => @lem4776143 A n f m y)). Qed.
Lemma lem4776145 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4776146 {A : Type'} (n : nat) (f : nat -> A) (y : A) : (term164 A n f y) = (term164 A n f y).
Proof. exact (MK_COMB (@lem4776145) (@lem4776144 A n f y)). Qed.
Lemma lem4776149 {A : Type'} (s : A -> Prop) (y : A) : (term223 A s y) = (term223 A s y).
Proof. exact (eq_refl (term223 A s y)). Qed.
Lemma lem4776150 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term266 A s n f y) = (term266 A s n f y).
Proof. exact (MK_COMB (@lem4776149 A s y) (@lem4776146 A n f y)). Qed.
Lemma lem4776151 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term267 A s n f) = (term267 A s n f).
Proof. exact (fun_ext (fun y : A => @lem4776150 A s n f y)). Qed.
Lemma lem4776152 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4776153 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term268 A s n f) = (term268 A s n f).
Proof. exact (MK_COMB (@lem4776152 A) (@lem4776151 A s n f)). Qed.
Lemma lem4776158 {A : Type'} (x : A) (f : nat -> A) (x' : nat) (n : nat) : (term251 A x f x' n) = (term251 A x f x' n).
Proof. exact (eq_refl (term251 A x f x' n)). Qed.
Lemma lem4776159 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term253 A x f n) = (term253 A x f n).
Proof. exact (fun_ext (fun x' : nat => @lem4776158 A x f x' n)). Qed.
Lemma lem4776160 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4776161 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term254 A x f n) = (term254 A x f n).
Proof. exact (MK_COMB (@lem4776160) (@lem4776159 A x f n)). Qed.
Lemma lem4776162 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4776163 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term256 A x f n) = (term256 A x f n).
Proof. exact (MK_COMB (@lem4776162) (@lem4776161 A x f n)). Qed.
Lemma lem4776166 {A : Type'} (s : A -> Prop) (x : A) : (term223 A s x) = (term223 A s x).
Proof. exact (eq_refl (term223 A s x)). Qed.
Lemma lem4776167 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term257 A s x f n) = (term257 A s x f n).
Proof. exact (MK_COMB (@lem4776166 A s x) (@lem4776163 A x f n)). Qed.
Lemma lem4776168 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4776169 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term260 A s x f n) = (term260 A s x f n).
Proof. exact (MK_COMB (@lem4776168) (@lem4776167 A s x f n)). Qed.
Lemma lem4776170 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term262 A s f n) = (term262 A s f n).
Proof. exact (fun_ext (fun x : A => @lem4776169 A s x f n)). Qed.
Lemma lem4776171 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4776172 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term263 A s f n) = (term263 A s f n).
Proof. exact (MK_COMB (@lem4776171 A) (@lem4776170 A s f n)). Qed.
Lemma lem4776173 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4776174 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term264 A s f n) = (term264 A s f n).
Proof. exact (MK_COMB (@lem4776173) (@lem4776172 A s f n)). Qed.
Lemma lem4776175 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4776176 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term265 A s f n) = (term265 A s f n).
Proof. exact (MK_COMB (@lem4776175) (@lem4776174 A s f n)). Qed.
Lemma lem4776177 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term269 A s n f) = (term269 A s n f).
Proof. exact (MK_COMB (@lem4776176 A s f n) (@lem4776153 A s n f)). Qed.
Lemma lem4776178 {A : Type'} (n : nat) (f : nat -> A) : (term279 A n f) = (term279 A n f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4776177 A s n f)). Qed.
Lemma lem4776179 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4776180 {A : Type'} (n : nat) (f : nat -> A) : (term281 A n f) = (term281 A n f).
Proof. exact (MK_COMB (@lem4776179 A) (@lem4776178 A n f)). Qed.
Lemma lem4776181 {A : Type'} (f : nat -> A) : (term283 A f) = (term283 A f).
Proof. exact (fun_ext (fun n : nat => @lem4776180 A n f)). Qed.
Lemma lem4776182 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4776183 {A : Type'} (f : nat -> A) : (term285 A f) = (term285 A f).
Proof. exact (MK_COMB (@lem4776182) (@lem4776181 A f)). Qed.
Lemma lem4776184 {A : Type'} : (term287 A) = (term287 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem4776183 A f)). Qed.
Lemma lem4776185 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4776186 {A : Type'} : (term289 A) = (term289 A).
Proof. exact (MK_COMB (@lem4776185 A) (@lem4776184 A)). Qed.
Lemma lem4776241 {A : Type'} : (term288 A) = (term289 A).
Proof. exact (TRANS (@lem4776136 A) (@lem4776186 A)). Qed.
Lemma lem4776242 {A : Type'} : (term289 A) = (term288 A).
Proof. exact (SYM (@lem4776241 A)). Qed.
Lemma lem4776243 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (h1 : term264 A s f n) : term264 A s f n.
Proof. exact (h1). Qed.
Lemma lem4776245 (p : Prop) : p = (term270 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4776246 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term268 A s n f) = (term290 A s n f).
Proof. exact (@lem4776245 (term268 A s n f)). Qed.
Lemma lem4776247 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term290 A s n f) = (term268 A s n f).
Proof. exact (SYM (@lem4776246 A s n f)). Qed.
Lemma lem4776248 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term291 A s n f) : term291 A s n f.
Proof. exact (h1). Qed.
Lemma lem4776256 {A : Type'} (x : A) (f : nat -> A) (x' : nat) (n : nat) : (term292 A x f x' n) = (term293 A x f x' n).
Proof. exact (@lem17045 (x = (f x')) (Peano.lt x' n)). Qed.
Lemma lem4776257 (P : nat -> Prop) : (term294 P) = (term295 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem4776258 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term256 A x f n) = (term296 A x f n).
Proof. exact (@lem4776257 (term253 A x f n)). Qed.
Lemma lem4776259 {A : Type'} (x : A) (f : nat -> A) (x' : nat) (n : nat) : (term297 A x f n x') = (term251 A x f x' n).
Proof. exact (eq_refl (term297 A x f n x')). Qed.
Lemma lem4776260 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4776261 {A : Type'} (x : A) (f : nat -> A) (x' : nat) (n : nat) : (term298 A x f n x') = (term292 A x f x' n).
Proof. exact (MK_COMB (@lem4776260) (@lem4776259 A x f x' n)). Qed.
Lemma lem4776262 {A : Type'} (x : A) (f : nat -> A) (x' : nat) (n : nat) : (term298 A x f n x') = (term293 A x f x' n).
Proof. exact (TRANS (@lem4776261 A x f x' n) (@lem4776256 A x f x' n)). Qed.
Lemma lem4776263 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term299 A x f n) = (term300 A x f n).
Proof. exact (fun_ext (fun x' : nat => @lem4776262 A x f x' n)). Qed.
Lemma lem4776264 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4776265 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term296 A x f n) = (term301 A x f n).
Proof. exact (MK_COMB (@lem4776264) (@lem4776263 A x f n)). Qed.
Lemma lem4776266 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term256 A x f n) = (term301 A x f n).
Proof. exact (TRANS (@lem4776258 A x f n) (@lem4776265 A x f n)). Qed.
Lemma lem4776268 {A : Type'} (s : A -> Prop) (x : A) : (term223 A s x) = (term223 A s x).
Proof. exact (eq_refl (term223 A s x)). Qed.
Lemma lem4776269 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term257 A s x f n) = (term302 A s x f n).
Proof. exact (MK_COMB (@lem4776268 A s x) (@lem4776266 A x f n)). Qed.
Lemma lem4776270 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term303 A s x f n) = (term257 A s x f n).
Proof. exact (@lem16933 (term257 A s x f n)). Qed.
Lemma lem4776271 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term303 A s x f n) = (term302 A s x f n).
Proof. exact (TRANS (@lem4776270 A s x f n) (@lem4776269 A s x f n)). Qed.
Lemma lem4776272 {A : Type'} (P : A -> Prop) : (term304 A P) = (term305 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4776273 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term264 A s f n) = (term306 A s f n).
Proof. exact (@lem4776272 A (term262 A s f n)). Qed.
Lemma lem4776274 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term307 A s f n x) = (term260 A s x f n).
Proof. exact (eq_refl (term307 A s f n x)). Qed.
Lemma lem4776275 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4776276 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term308 A s f n x) = (term303 A s x f n).
Proof. exact (MK_COMB (@lem4776275) (@lem4776274 A s x f n)). Qed.
Lemma lem4776277 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term308 A s f n x) = (term302 A s x f n).
Proof. exact (TRANS (@lem4776276 A s x f n) (@lem4776271 A s x f n)). Qed.
Lemma lem4776278 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term309 A s f n) = (term310 A s f n).
Proof. exact (fun_ext (fun x : A => @lem4776277 A s x f n)). Qed.
Lemma lem4776279 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4776280 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term306 A s f n) = (term311 A s f n).
Proof. exact (MK_COMB (@lem4776279 A) (@lem4776278 A s f n)). Qed.
Lemma lem4776361 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term264 A s f n) = (term311 A s f n).
Proof. exact (TRANS (@lem4776273 A s f n) (@lem4776280 A s f n)). Qed.
Lemma lem4776362 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (h1 : term264 A s f n) : term311 A s f n.
Proof. exact (EQ_MP (@lem4776361 A s f n) (@lem4776243 A s f n h1)). Qed.
Lemma lem4776367 {A : Type'} (f : nat -> A) (m : nat) (y : A) : (term312 A f m y) = ((f m) = y).
Proof. exact (@lem16933 ((f m) = y)). Qed.
Lemma lem4776369 (m : nat) (n : nat) : (term313 m n) = (term313 m n).
Proof. exact (eq_refl (term313 m n)). Qed.
Lemma lem4776370 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) : (term314 A n f m y) = (term315 A n f m y).
Proof. exact (MK_COMB (@lem4776369 m n) (@lem4776367 A f m y)). Qed.
Lemma lem4776371 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) : (term316 A n f m y) = (term314 A n f m y).
Proof. exact (@lem17362 (Peano.lt m n) (term152 A f m y)). Qed.
Lemma lem4776372 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) : (term316 A n f m y) = (term315 A n f m y).
Proof. exact (TRANS (@lem4776371 A n f m y) (@lem4776370 A n f m y)). Qed.
Lemma lem4776373 (P : nat -> Prop) : (term317 P) = (term318 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4776374 {A : Type'} (n : nat) (f : nat -> A) (y : A) : (term319 A n f y) = (term320 A n f y).
Proof. exact (@lem4776373 (term163 A n f y)). Qed.
Lemma lem4776375 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) : (term321 A n f y m) = (term162 A n f m y).
Proof. exact (eq_refl (term321 A n f y m)). Qed.
Lemma lem4776376 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4776377 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) : (term322 A n f y m) = (term316 A n f m y).
Proof. exact (MK_COMB (@lem4776376) (@lem4776375 A n f m y)). Qed.
Lemma lem4776378 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) : (term322 A n f y m) = (term315 A n f m y).
Proof. exact (TRANS (@lem4776377 A n f m y) (@lem4776372 A n f m y)). Qed.
Lemma lem4776379 {A : Type'} (n : nat) (f : nat -> A) (y : A) : (term323 A n f y) = (term324 A n f y).
Proof. exact (fun_ext (fun m : nat => @lem4776378 A n f m y)). Qed.
Lemma lem4776380 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4776381 {A : Type'} (n : nat) (f : nat -> A) (y : A) : (term320 A n f y) = (term325 A n f y).
Proof. exact (MK_COMB (@lem4776380) (@lem4776379 A n f y)). Qed.
Lemma lem4776382 {A : Type'} (n : nat) (f : nat -> A) (y : A) : (term319 A n f y) = (term325 A n f y).
Proof. exact (TRANS (@lem4776374 A n f y) (@lem4776381 A n f y)). Qed.
Lemma lem4776384 {A : Type'} (s : A -> Prop) (y : A) : (term326 A s y) = (term326 A s y).
Proof. exact (eq_refl (term326 A s y)). Qed.
Lemma lem4776385 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term327 A s n f y) = (term328 A s n f y).
Proof. exact (MK_COMB (@lem4776384 A s y) (@lem4776382 A n f y)). Qed.
Lemma lem4776386 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term329 A s n f y) = (term327 A s n f y).
Proof. exact (@lem17045 (s y) (term164 A n f y)). Qed.
Lemma lem4776387 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term329 A s n f y) = (term328 A s n f y).
Proof. exact (TRANS (@lem4776386 A s n f y) (@lem4776385 A s n f y)). Qed.
Lemma lem4776388 {A : Type'} (P : A -> Prop) : (term330 A P) = (term331 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4776389 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term291 A s n f) = (term332 A s n f).
Proof. exact (@lem4776388 A (term267 A s n f)). Qed.
Lemma lem4776390 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term333 A s n f y) = (term266 A s n f y).
Proof. exact (eq_refl (term333 A s n f y)). Qed.
Lemma lem4776391 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4776392 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term334 A s n f y) = (term329 A s n f y).
Proof. exact (MK_COMB (@lem4776391) (@lem4776390 A s n f y)). Qed.
Lemma lem4776393 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term334 A s n f y) = (term328 A s n f y).
Proof. exact (TRANS (@lem4776392 A s n f y) (@lem4776387 A s n f y)). Qed.
Lemma lem4776394 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term335 A s n f) = (term336 A s n f).
Proof. exact (fun_ext (fun y : A => @lem4776393 A s n f y)). Qed.
Lemma lem4776395 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4776396 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term332 A s n f) = (term337 A s n f).
Proof. exact (MK_COMB (@lem4776395 A) (@lem4776394 A s n f)). Qed.
Lemma lem4776397 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term291 A s n f) = (term337 A s n f).
Proof. exact (TRANS (@lem4776389 A s n f) (@lem4776396 A s n f)). Qed.
Lemma lem4776496 {A : Type'} (P : Prop) (Q : A -> Prop) : (term338 A P Q) = (term339 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4776497 (P : Prop) (Q : nat -> Prop) : (term340 P Q) = (term341 P Q).
Proof. exact (@lem4776496 nat P Q). Qed.
Lemma lem4776498 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term342 A s n f y) = (term343 A s n f y).
Proof. exact (@lem4776497 (term344 A s y) (term324 A n f y)). Qed.
Lemma lem4776499 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) : (term345 A n f y m) = (term315 A n f m y).
Proof. exact (eq_refl (term345 A n f y m)). Qed.
Lemma lem4776500 {A : Type'} (n : nat) (f : nat -> A) (y : A) : (term346 A n f y) = (term324 A n f y).
Proof. exact (fun_ext (fun m : nat => @lem4776499 A n f m y)). Qed.
Lemma lem4776501 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4776502 {A : Type'} (n : nat) (f : nat -> A) (y : A) : (term347 A n f y) = (term325 A n f y).
Proof. exact (MK_COMB (@lem4776501) (@lem4776500 A n f y)). Qed.
Lemma lem4776503 {A : Type'} (s : A -> Prop) (y : A) : (term326 A s y) = (term326 A s y).
Proof. exact (eq_refl (term326 A s y)). Qed.
Lemma lem4776504 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term342 A s n f y) = (term328 A s n f y).
Proof. exact (MK_COMB (@lem4776503 A s y) (@lem4776502 A n f y)). Qed.
Lemma lem4776505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4776506 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term348 A s n f y) = (term349 A s n f y).
Proof. exact (MK_COMB (@lem4776505) (@lem4776504 A s n f y)). Qed.
Lemma lem4776507 {A : Type'} (n : nat) (f : nat -> A) (m : nat) (y : A) : (term345 A n f y m) = (term315 A n f m y).
Proof. exact (eq_refl (term345 A n f y m)). Qed.
Lemma lem4776508 {A : Type'} (s : A -> Prop) (y : A) : (term326 A s y) = (term326 A s y).
Proof. exact (eq_refl (term326 A s y)). Qed.
Lemma lem4776509 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : nat) (y : A) : (term350 A s n f y m) = (term351 A s n f m y).
Proof. exact (MK_COMB (@lem4776508 A s y) (@lem4776507 A n f m y)). Qed.
Lemma lem4776510 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term352 A s n f y) = (term353 A s n f y).
Proof. exact (fun_ext (fun m : nat => @lem4776509 A s n f m y)). Qed.
Lemma lem4776511 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4776512 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term343 A s n f y) = (term354 A s n f y).
Proof. exact (MK_COMB (@lem4776511) (@lem4776510 A s n f y)). Qed.
Lemma lem4776513 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : ((term342 A s n f y) = (term343 A s n f y)) = ((term328 A s n f y) = (term354 A s n f y)).
Proof. exact (MK_COMB (@lem4776506 A s n f y) (@lem4776512 A s n f y)). Qed.
Lemma lem4776514 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term328 A s n f y) = (term354 A s n f y).
Proof. exact (EQ_MP (@lem4776513 A s n f y) (@lem4776498 A s n f y)). Qed.
Lemma lem4776515 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term336 A s n f) = (term355 A s n f).
Proof. exact (fun_ext (fun y : A => @lem4776514 A s n f y)). Qed.
Lemma lem4776516 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4776517 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term337 A s n f) = (term356 A s n f).
Proof. exact (MK_COMB (@lem4776516 A) (@lem4776515 A s n f)). Qed.
Lemma lem4776519 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4776520 {A : Type'} (P : type1424 A) : (term359 A P) = (term360 A P).
Proof. exact (@lem4776519 A nat P). Qed.
Lemma lem4776521 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term361 A s n f) = (term362 A s n f).
Proof. exact (@lem4776520 A (term363 A s n f)). Qed.
Lemma lem4776522 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term364 A s n f y) = (term353 A s n f y).
Proof. exact (eq_refl (term364 A s n f y)). Qed.
Lemma lem4776523 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4776524 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) (m : nat) : (term365 A s n f y m) = (term366 A s n f y m).
Proof. exact (MK_COMB (@lem4776522 A s n f y) (@lem4776523 m)). Qed.
Lemma lem4776525 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : nat) (y : A) : (term366 A s n f y m) = (term351 A s n f m y).
Proof. exact (eq_refl (term366 A s n f y m)). Qed.
Lemma lem4776526 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : nat) (y : A) : (term365 A s n f y m) = (term351 A s n f m y).
Proof. exact (TRANS (@lem4776524 A s n f y m) (@lem4776525 A s n f m y)). Qed.
Lemma lem4776527 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term367 A s n f y) = (term353 A s n f y).
Proof. exact (fun_ext (fun m : nat => @lem4776526 A s n f m y)). Qed.
Lemma lem4776528 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4776529 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term368 A s n f y) = (term354 A s n f y).
Proof. exact (MK_COMB (@lem4776528) (@lem4776527 A s n f y)). Qed.
Lemma lem4776530 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term369 A s n f) = (term355 A s n f).
Proof. exact (fun_ext (fun y : A => @lem4776529 A s n f y)). Qed.
Lemma lem4776531 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4776532 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term361 A s n f) = (term356 A s n f).
Proof. exact (MK_COMB (@lem4776531 A) (@lem4776530 A s n f)). Qed.
Lemma lem4776533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4776534 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term370 A s n f) = (term371 A s n f).
Proof. exact (MK_COMB (@lem4776533) (@lem4776532 A s n f)). Qed.
Lemma lem4776535 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (y : A) : (term364 A s n f y) = (term353 A s n f y).
Proof. exact (eq_refl (term364 A s n f y)). Qed.
Lemma lem4776536 {A : Type'} (m : A -> nat) (y : A) : (m y) = (m y).
Proof. exact (eq_refl (m y)). Qed.
Lemma lem4776537 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (y : A) : (term372 A s n f m y) = (term373 A s n f m y).
Proof. exact (MK_COMB (@lem4776535 A s n f y) (@lem4776536 A m y)). Qed.
Lemma lem4776538 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (y : A) : (term373 A s n f m y) = (term374 A s n f m y).
Proof. exact (eq_refl (term373 A s n f m y)). Qed.
Lemma lem4776539 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (y : A) : (term372 A s n f m y) = (term374 A s n f m y).
Proof. exact (TRANS (@lem4776537 A s n f m y) (@lem4776538 A s n f m y)). Qed.
Lemma lem4776540 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) : (term375 A s n f m) = (term376 A s n f m).
Proof. exact (fun_ext (fun y : A => @lem4776539 A s n f m y)). Qed.
Lemma lem4776541 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4776542 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) : (term377 A s n f m) = (term378 A s n f m).
Proof. exact (MK_COMB (@lem4776541 A) (@lem4776540 A s n f m)). Qed.
Lemma lem4776543 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term379 A s n f) = (term380 A s n f).
Proof. exact (fun_ext (fun m : A -> nat => @lem4776542 A s n f m)). Qed.
Lemma lem4776544 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem4776545 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term362 A s n f) = (term381 A s n f).
Proof. exact (MK_COMB (@lem4776544 A) (@lem4776543 A s n f)). Qed.
Lemma lem4776546 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : ((term361 A s n f) = (term362 A s n f)) = ((term356 A s n f) = (term381 A s n f)).
Proof. exact (MK_COMB (@lem4776534 A s n f) (@lem4776545 A s n f)). Qed.
Lemma lem4776547 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term356 A s n f) = (term381 A s n f).
Proof. exact (EQ_MP (@lem4776546 A s n f) (@lem4776521 A s n f)). Qed.
Lemma lem4776549 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term337 A s n f) = (term381 A s n f).
Proof. exact (TRANS (@lem4776517 A s n f) (@lem4776547 A s n f)). Qed.
Lemma lem4776550 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term291 A s n f) = (term381 A s n f).
Proof. exact (TRANS (@lem4776397 A s n f) (@lem4776549 A s n f)). Qed.
Lemma lem4776551 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term291 A s n f) : term381 A s n f.
Proof. exact (EQ_MP (@lem4776550 A s n f) (@lem4776248 A s n f h1)). Qed.
Lemma lem4776552 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term378 A s n f m.
Proof. exact (h1). Qed.
Lemma lem4776553 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : term302 A s x f n.
Proof. exact (h1). Qed.
Lemma lem4776580 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (y : A) : (term374 A s n f m y) = (term374 A s n f m y).
Proof. exact (eq_refl (term374 A s n f m y)). Qed.
Lemma lem4776581 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) : (term376 A s n f m) = (term376 A s n f m).
Proof. exact (fun_ext (fun y : A => @lem4776580 A s n f m y)). Qed.
Lemma lem4776582 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4776583 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) : (term378 A s n f m) = (term378 A s n f m).
Proof. exact (MK_COMB (@lem4776582 A) (@lem4776581 A s n f m)). Qed.
Lemma lem4776584 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term378 A s n f m.
Proof. exact (EQ_MP (@lem4776583 A s n f m) (@lem4776552 A s n f m h1)). Qed.
Lemma lem4776603 {A : Type'} (x : A) (f : nat -> A) (x' : nat) (n : nat) : (term293 A x f x' n) = (term293 A x f x' n).
Proof. exact (eq_refl (term293 A x f x' n)). Qed.
Lemma lem4776604 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term300 A x f n) = (term300 A x f n).
Proof. exact (fun_ext (fun x' : nat => @lem4776603 A x f x' n)). Qed.
Lemma lem4776605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4776606 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term301 A x f n) = (term301 A x f n).
Proof. exact (MK_COMB (@lem4776605) (@lem4776604 A x f n)). Qed.
Lemma lem4776611 {A : Type'} (s : A -> Prop) (x : A) : (term223 A s x) = (term223 A s x).
Proof. exact (eq_refl (term223 A s x)). Qed.
Lemma lem4776612 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) : (term302 A s x f n) = (term302 A s x f n).
Proof. exact (MK_COMB (@lem4776611 A s x) (@lem4776606 A x f n)). Qed.
Lemma lem4776613 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : term302 A s x f n.
Proof. exact (EQ_MP (@lem4776612 A s x f n) (@lem4776553 A s x f n h1)). Qed.
Lemma lem4776614 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : term301 A x f n.
Proof. exact (proj2 (@lem4776613 A s x f n h1)). Qed.
Lemma lem4776633 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) (m : A -> nat) (y : A) : (term374 A s n f m y) = (term382 A n s f m y).
Proof. exact (@lem19490 (term383 A m y n) (term344 A s y) ((term384 A f m y) = y)). Qed.
Lemma lem4776634 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) (m : A -> nat) : (term376 A s n f m) = (term385 A n s f m).
Proof. exact (fun_ext (fun y : A => @lem4776633 A n s f m y)). Qed.
Lemma lem4776635 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4776637 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) (m : A -> nat) : (term378 A s n f m) = (term386 A n s f m).
Proof. exact (MK_COMB (@lem4776635 A) (@lem4776634 A n s f m)). Qed.
Lemma lem4776638 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term386 A n s f m.
Proof. exact (EQ_MP (@lem4776637 A n s f m) (@lem4776584 A s n f m h1)). Qed.
Lemma lem4776650 {A : Type'} (x : A) (f : nat -> A) (x' : nat) (n : nat) : (term293 A x f x' n) = (term293 A x f x' n).
Proof. exact (eq_refl (term293 A x f x' n)). Qed.
Lemma lem4776651 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term300 A x f n) = (term300 A x f n).
Proof. exact (fun_ext (fun x' : nat => @lem4776650 A x f x' n)). Qed.
Lemma lem4776652 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4776654 {A : Type'} (x : A) (f : nat -> A) (n : nat) : (term301 A x f n) = (term301 A x f n).
Proof. exact (MK_COMB (@lem4776652) (@lem4776651 A x f n)). Qed.
Lemma lem4776655 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : term301 A x f n.
Proof. exact (EQ_MP (@lem4776654 A x f n) (@lem4776614 A s x f n h1)). Qed.
Lemma lem4776656 {A : Type'} (_58894 : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term387 A n s f m _58894.
Proof. exact (@lem4776638 A s n f m h1 _58894). Qed.
Lemma lem4776657 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) (m : A -> nat) (_58894 : A) : (term387 A n s f m _58894) = (term382 A n s f m _58894).
Proof. exact (eq_refl (term387 A n s f m _58894)). Qed.
Lemma lem4776658 {A : Type'} (_58894 : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term382 A n s f m _58894.
Proof. exact (EQ_MP (@lem4776657 A n s f m _58894) (@lem4776656 A _58894 s n f m h1)). Qed.
Lemma lem4776659 {A : Type'} (_58895 : nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : term388 A x f n _58895.
Proof. exact (@lem4776655 A s x f n h1 _58895). Qed.
Lemma lem4776660 {A : Type'} (x : A) (f : nat -> A) (_58895 : nat) (n : nat) : (term388 A x f n _58895) = (term293 A x f _58895 n).
Proof. exact (eq_refl (term388 A x f n _58895)). Qed.
Lemma lem4776671 {A : Type'} (_58895 : nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : term293 A x f _58895 n.
Proof. exact (EQ_MP (@lem4776660 A x f _58895 n) (@lem4776659 A _58895 s x f n h1)). Qed.
Lemma lem4776677 {A : Type'} (_58894 : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term389 A s m _58894 n.
Proof. exact (proj1 (@lem4776658 A _58894 s n f m h1)). Qed.
Lemma lem4776683 {A : Type'} (_58894 : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term390 A s f m _58894.
Proof. exact (proj2 (@lem4776658 A _58894 s n f m h1)). Qed.
Lemma lem4776732 {A : Type'} (x : A) (y : A) (z : A) : term391 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem4776736 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : s x.
Proof. exact (proj1 (@lem4776613 A s x f n h1)). Qed.
Lemma lem4776737 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : term392 A s x.
Proof. exact (fun h0 : term344 A s x => @lem4776736 A s x f n h1). Qed.
Lemma lem4776739 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4776740 {A : Type'} (s : A -> Prop) (x : A) : (term392 A s x) = (s x).
Proof. exact (@lem4776739 (s x)). Qed.
Lemma lem4776741 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : s x.
Proof. exact (EQ_MP (@lem4776740 A s x) (@lem4776737 A s x f n h1)). Qed.
Lemma lem4776747 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4776748 {A : Type'} (f : nat -> A) (m : A -> nat) (s : A -> Prop) (_58894 : A) : (term390 A s f m _58894) = (term394 A f m s _58894).
Proof. exact (@lem4776747 ((term384 A f m _58894) = _58894) (term344 A s _58894)). Qed.
Lemma lem4776756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4776757 {A : Type'} (f : nat -> A) (m : A -> nat) (s : A -> Prop) (_58894 : A) : (term395 A s f m _58894) = (term396 A f m s _58894).
Proof. exact (MK_COMB (@lem4776756) (@lem4776748 A f m s _58894)). Qed.
Lemma lem4776765 {A : Type'} (f : nat -> A) (m : A -> nat) (s : A -> Prop) (_58894 : A) : (term394 A f m s _58894) = (term394 A f m s _58894).
Proof. exact (eq_refl (term394 A f m s _58894)). Qed.
Lemma lem4776766 {A : Type'} (f : nat -> A) (m : A -> nat) (s : A -> Prop) (_58894 : A) : ((term390 A s f m _58894) = (term394 A f m s _58894)) = ((term394 A f m s _58894) = (term394 A f m s _58894)).
Proof. exact (MK_COMB (@lem4776757 A f m s _58894) (@lem4776765 A f m s _58894)). Qed.
Lemma lem4776768 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4776769 (x : Prop) : (x = x) = True.
Proof. exact (@lem4776768 Prop x). Qed.
Lemma lem4776770 {A : Type'} (f : nat -> A) (m : A -> nat) (s : A -> Prop) (_58894 : A) : ((term394 A f m s _58894) = (term394 A f m s _58894)) = True.
Proof. exact (@lem4776769 (term394 A f m s _58894)). Qed.
Lemma lem4776771 {A : Type'} (f : nat -> A) (m : A -> nat) (s : A -> Prop) (_58894 : A) : ((term390 A s f m _58894) = (term394 A f m s _58894)) = True.
Proof. exact (TRANS (@lem4776766 A f m s _58894) (@lem4776770 A f m s _58894)). Qed.
Lemma lem4776772 {A : Type'} (f : nat -> A) (m : A -> nat) (s : A -> Prop) (_58894 : A) : True = ((term390 A s f m _58894) = (term394 A f m s _58894)).
Proof. exact (SYM (@lem4776771 A f m s _58894)). Qed.
Lemma lem4776773 {A : Type'} (f : nat -> A) (m : A -> nat) (s : A -> Prop) (_58894 : A) : (term390 A s f m _58894) = (term394 A f m s _58894).
Proof. exact (EQ_MP (@lem4776772 A f m s _58894) (@lem0)). Qed.
Lemma lem4776774 {A : Type'} (_58894 : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term394 A f m s _58894.
Proof. exact (EQ_MP (@lem4776773 A f m s _58894) (@lem4776683 A _58894 s n f m h1)). Qed.
Lemma lem4776776 (b : Prop) (a : Prop) : (a \/ b) = (term397 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4776777 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : A -> nat) (_58894 : A) : (term394 A f m s _58894) = (term398 A s f m _58894).
Proof. exact (@lem4776776 (term344 A s _58894) ((term384 A f m _58894) = _58894)). Qed.
Lemma lem4776779 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4776780 {A : Type'} (s : A -> Prop) (_58894 : A) : (term399 A s _58894) = (s _58894).
Proof. exact (@lem4776779 (s _58894)). Qed.
Lemma lem4776781 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4776782 {A : Type'} (s : A -> Prop) (_58894 : A) : (term400 A s _58894) = (term401 A s _58894).
Proof. exact (MK_COMB (@lem4776781) (@lem4776780 A s _58894)). Qed.
Lemma lem4776783 {A : Type'} (f : nat -> A) (m : A -> nat) (_58894 : A) : ((term384 A f m _58894) = _58894) = ((term384 A f m _58894) = _58894).
Proof. exact (eq_refl ((term384 A f m _58894) = _58894)). Qed.
Lemma lem4776784 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : A -> nat) (_58894 : A) : (term398 A s f m _58894) = (term402 A s f m _58894).
Proof. exact (MK_COMB (@lem4776782 A s _58894) (@lem4776783 A f m _58894)). Qed.
Lemma lem4776785 {A : Type'} (s : A -> Prop) (f : nat -> A) (m : A -> nat) (_58894 : A) : (term394 A f m s _58894) = (term402 A s f m _58894).
Proof. exact (TRANS (@lem4776777 A s f m _58894) (@lem4776784 A s f m _58894)). Qed.
Lemma lem4776788 {A : Type'} (_58894 : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term402 A s f m _58894.
Proof. exact (EQ_MP (@lem4776785 A s f m _58894) (@lem4776774 A _58894 s n f m h1)). Qed.
Lemma lem4776789 {A : Type'} (_58894 : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term402 A s f m _58894.
Proof. exact (@lem4776788 A _58894 s n f m h1). Qed.
Lemma lem4776790 {A : Type'} (x : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term402 A s f m x.
Proof. exact (@lem4776789 A x s n f m h1). Qed.
Lemma lem4776793 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : (term384 A f m x) = x.
Proof. exact (@lem4776790 A x s n f m h1 (@lem4776741 A s x f n h2)). Qed.
Lemma lem4776794 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : term403 A f m x.
Proof. exact (fun h0 : term404 A f m x => @lem4776793 A m s x f n h1 h2). Qed.
Lemma lem4776796 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4776797 {A : Type'} (f : nat -> A) (m : A -> nat) (x : A) : (term403 A f m x) = ((term384 A f m x) = x).
Proof. exact (@lem4776796 ((term384 A f m x) = x)). Qed.
Lemma lem4776798 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : (term384 A f m x) = x.
Proof. exact (EQ_MP (@lem4776797 A f m x) (@lem4776794 A m s x f n h1 h2)). Qed.
Lemma lem4776800 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4776801 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4776800 A x). Qed.
Lemma lem4776802 {A : Type'} (f : nat -> A) (m : A -> nat) (x : A) : (term384 A f m x) = (term384 A f m x).
Proof. exact (@lem4776801 A (term384 A f m x)). Qed.
Lemma lem4776803 {A : Type'} (f : nat -> A) (m : A -> nat) (x : A) : term405 A f m x.
Proof. exact (fun h0 : term406 A f m x => @lem4776802 A f m x). Qed.
Lemma lem4776805 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4776806 {A : Type'} (f : nat -> A) (m : A -> nat) (x : A) : (term405 A f m x) = ((term384 A f m x) = (term384 A f m x)).
Proof. exact (@lem4776805 ((term384 A f m x) = (term384 A f m x))). Qed.
Lemma lem4776807 {A : Type'} (f : nat -> A) (m : A -> nat) (x : A) : (term384 A f m x) = (term384 A f m x).
Proof. exact (EQ_MP (@lem4776806 A f m x) (@lem4776803 A f m x)). Qed.
Lemma lem4776825 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4776826 {A : Type'} (y : A) (x : A) (z : A) : (term407 A x y z) = (term408 A y x z).
Proof. exact (@lem4776825 (y = z) (term409 A x z)). Qed.
Lemma lem4776836 {A : Type'} (x : A) (y : A) : (term410 A x y) = (term410 A x y).
Proof. exact (eq_refl (term410 A x y)). Qed.
Lemma lem4776837 {A : Type'} (y : A) (x : A) (z : A) : (term391 A x y z) = (term411 A y x z).
Proof. exact (MK_COMB (@lem4776836 A x y) (@lem4776826 A y x z)). Qed.
Lemma lem4776841 (q : Prop) (p : Prop) (r : Prop) : (term412 p q r) = (term412 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4776842 {A : Type'} (y : A) (x : A) (z : A) : (term411 A y x z) = (term413 A y x z).
Proof. exact (@lem4776841 (y = z) (term409 A x y) (term409 A x z)). Qed.
Lemma lem4776864 {A : Type'} (y : A) (x : A) (z : A) : (term391 A x y z) = (term413 A y x z).
Proof. exact (TRANS (@lem4776837 A y x z) (@lem4776842 A y x z)). Qed.
Lemma lem4776865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4776866 {A : Type'} (y : A) (x : A) (z : A) : (term414 A x y z) = (term415 A y x z).
Proof. exact (MK_COMB (@lem4776865) (@lem4776864 A y x z)). Qed.
Lemma lem4776888 {A : Type'} (y : A) (x : A) (z : A) : (term413 A y x z) = (term413 A y x z).
Proof. exact (eq_refl (term413 A y x z)). Qed.
Lemma lem4776889 {A : Type'} (y : A) (x : A) (z : A) : ((term391 A x y z) = (term413 A y x z)) = ((term413 A y x z) = (term413 A y x z)).
Proof. exact (MK_COMB (@lem4776866 A y x z) (@lem4776888 A y x z)). Qed.
Lemma lem4776891 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4776892 (x : Prop) : (x = x) = True.
Proof. exact (@lem4776891 Prop x). Qed.
Lemma lem4776893 {A : Type'} (y : A) (x : A) (z : A) : ((term413 A y x z) = (term413 A y x z)) = True.
Proof. exact (@lem4776892 (term413 A y x z)). Qed.
Lemma lem4776894 {A : Type'} (y : A) (x : A) (z : A) : ((term391 A x y z) = (term413 A y x z)) = True.
Proof. exact (TRANS (@lem4776889 A y x z) (@lem4776893 A y x z)). Qed.
Lemma lem4776895 {A : Type'} (y : A) (x : A) (z : A) : True = ((term391 A x y z) = (term413 A y x z)).
Proof. exact (SYM (@lem4776894 A y x z)). Qed.
Lemma lem4776896 {A : Type'} (y : A) (x : A) (z : A) : (term391 A x y z) = (term413 A y x z).
Proof. exact (EQ_MP (@lem4776895 A y x z) (@lem0)). Qed.
Lemma lem4776897 {A : Type'} (y : A) (x : A) (z : A) : term413 A y x z.
Proof. exact (EQ_MP (@lem4776896 A y x z) (@lem4776732 A x y z)). Qed.
Lemma lem4776899 (b : Prop) (a : Prop) : (a \/ b) = (term397 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4776900 {A : Type'} (x : A) (y : A) (z : A) : (term413 A y x z) = (term416 A x y z).
Proof. exact (@lem4776899 (term417 A y x z) (y = z)). Qed.
Lemma lem4776902 (a : Prop) (b : Prop) : (term418 a b) = (term419 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4776903 {A : Type'} (y : A) (x : A) (z : A) : (term420 A y x z) = (term421 A y x z).
Proof. exact (@lem4776902 (term409 A x y) (term409 A x z)). Qed.
Lemma lem4776905 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4776906 {A : Type'} (x : A) (y : A) : (term422 A x y) = (x = y).
Proof. exact (@lem4776905 (x = y)). Qed.
Lemma lem4776907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4776908 {A : Type'} (x : A) (y : A) : (term423 A x y) = (term424 A x y).
Proof. exact (MK_COMB (@lem4776907) (@lem4776906 A x y)). Qed.
Lemma lem4776910 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4776911 {A : Type'} (x : A) (z : A) : (term422 A x z) = (x = z).
Proof. exact (@lem4776910 (x = z)). Qed.
Lemma lem4776912 {A : Type'} (y : A) (x : A) (z : A) : (term421 A y x z) = (term425 A y x z).
Proof. exact (MK_COMB (@lem4776908 A x y) (@lem4776911 A x z)). Qed.
Lemma lem4776913 {A : Type'} (y : A) (x : A) (z : A) : (term420 A y x z) = (term425 A y x z).
Proof. exact (TRANS (@lem4776903 A y x z) (@lem4776912 A y x z)). Qed.
Lemma lem4776914 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4776915 {A : Type'} (y : A) (x : A) (z : A) : (term426 A y x z) = (term427 A y x z).
Proof. exact (MK_COMB (@lem4776914) (@lem4776913 A y x z)). Qed.
Lemma lem4776916 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4776917 {A : Type'} (x : A) (y : A) (z : A) : (term416 A x y z) = (term428 A x y z).
Proof. exact (MK_COMB (@lem4776915 A y x z) (@lem4776916 A y z)). Qed.
Lemma lem4776918 {A : Type'} (x : A) (y : A) (z : A) : (term413 A y x z) = (term428 A x y z).
Proof. exact (TRANS (@lem4776900 A x y z) (@lem4776917 A x y z)). Qed.
Lemma lem4776920 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : term429 A f m x.
Proof. exact (conj (@lem4776798 A m s x f n h1 h2) (@lem4776807 A f m x)). Qed.
Lemma lem4776922 {A : Type'} (x : A) (y : A) (z : A) : term428 A x y z.
Proof. exact (EQ_MP (@lem4776918 A x y z) (@lem4776897 A y x z)). Qed.
Lemma lem4776923 {A : Type'} (x : A) (y : A) (z : A) : term428 A x y z.
Proof. exact (@lem4776922 A x y z). Qed.
Lemma lem4776924 {A : Type'} (f : nat -> A) (m : A -> nat) (x : A) : term430 A f m x.
Proof. exact (@lem4776923 A (term384 A f m x) x (term384 A f m x)). Qed.
Lemma lem4776927 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : x = (term384 A f m x).
Proof. exact (@lem4776924 A f m x (@lem4776920 A m s x f n h1 h2)). Qed.
Lemma lem4776928 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : term431 A f m x.
Proof. exact (fun h0 : term432 A f m x => @lem4776927 A m s x f n h1 h2). Qed.
Lemma lem4776930 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4776931 {A : Type'} (f : nat -> A) (m : A -> nat) (x : A) : (term431 A f m x) = (x = (term384 A f m x)).
Proof. exact (@lem4776930 (x = (term384 A f m x))). Qed.
Lemma lem4776932 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : x = (term384 A f m x).
Proof. exact (EQ_MP (@lem4776931 A f m x) (@lem4776928 A m s x f n h1 h2)). Qed.
Lemma lem4776934 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : s x.
Proof. exact (proj1 (@lem4776613 A s x f n h1)). Qed.
Lemma lem4776935 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : term392 A s x.
Proof. exact (fun h0 : term344 A s x => @lem4776934 A s x f n h1). Qed.
Lemma lem4776937 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4776938 {A : Type'} (s : A -> Prop) (x : A) : (term392 A s x) = (s x).
Proof. exact (@lem4776937 (s x)). Qed.
Lemma lem4776939 {A : Type'} (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : s x.
Proof. exact (EQ_MP (@lem4776938 A s x) (@lem4776935 A s x f n h1)). Qed.
Lemma lem4776945 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4776946 {A : Type'} (m : A -> nat) (n : nat) (s : A -> Prop) (_58894 : A) : (term389 A s m _58894 n) = (term433 A m n s _58894).
Proof. exact (@lem4776945 (term383 A m _58894 n) (term344 A s _58894)). Qed.
Lemma lem4776952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4776953 {A : Type'} (m : A -> nat) (n : nat) (s : A -> Prop) (_58894 : A) : (term434 A s m _58894 n) = (term435 A m n s _58894).
Proof. exact (MK_COMB (@lem4776952) (@lem4776946 A m n s _58894)). Qed.
Lemma lem4776959 {A : Type'} (m : A -> nat) (n : nat) (s : A -> Prop) (_58894 : A) : (term433 A m n s _58894) = (term433 A m n s _58894).
Proof. exact (eq_refl (term433 A m n s _58894)). Qed.
Lemma lem4776960 {A : Type'} (m : A -> nat) (n : nat) (s : A -> Prop) (_58894 : A) : ((term389 A s m _58894 n) = (term433 A m n s _58894)) = ((term433 A m n s _58894) = (term433 A m n s _58894)).
Proof. exact (MK_COMB (@lem4776953 A m n s _58894) (@lem4776959 A m n s _58894)). Qed.
Lemma lem4776962 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4776963 (x : Prop) : (x = x) = True.
Proof. exact (@lem4776962 Prop x). Qed.
Lemma lem4776964 {A : Type'} (m : A -> nat) (n : nat) (s : A -> Prop) (_58894 : A) : ((term433 A m n s _58894) = (term433 A m n s _58894)) = True.
Proof. exact (@lem4776963 (term433 A m n s _58894)). Qed.
Lemma lem4776965 {A : Type'} (m : A -> nat) (n : nat) (s : A -> Prop) (_58894 : A) : ((term389 A s m _58894 n) = (term433 A m n s _58894)) = True.
Proof. exact (TRANS (@lem4776960 A m n s _58894) (@lem4776964 A m n s _58894)). Qed.
Lemma lem4776966 {A : Type'} (m : A -> nat) (n : nat) (s : A -> Prop) (_58894 : A) : True = ((term389 A s m _58894 n) = (term433 A m n s _58894)).
Proof. exact (SYM (@lem4776965 A m n s _58894)). Qed.
Lemma lem4776967 {A : Type'} (m : A -> nat) (n : nat) (s : A -> Prop) (_58894 : A) : (term389 A s m _58894 n) = (term433 A m n s _58894).
Proof. exact (EQ_MP (@lem4776966 A m n s _58894) (@lem0)). Qed.
Lemma lem4776968 {A : Type'} (_58894 : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term433 A m n s _58894.
Proof. exact (EQ_MP (@lem4776967 A m n s _58894) (@lem4776677 A _58894 s n f m h1)). Qed.
Lemma lem4776970 (b : Prop) (a : Prop) : (a \/ b) = (term397 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4776971 {A : Type'} (s : A -> Prop) (m : A -> nat) (_58894 : A) (n : nat) : (term433 A m n s _58894) = (term436 A s m _58894 n).
Proof. exact (@lem4776970 (term344 A s _58894) (term383 A m _58894 n)). Qed.
Lemma lem4776973 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4776974 {A : Type'} (s : A -> Prop) (_58894 : A) : (term399 A s _58894) = (s _58894).
Proof. exact (@lem4776973 (s _58894)). Qed.
Lemma lem4776975 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4776976 {A : Type'} (s : A -> Prop) (_58894 : A) : (term400 A s _58894) = (term401 A s _58894).
Proof. exact (MK_COMB (@lem4776975) (@lem4776974 A s _58894)). Qed.
Lemma lem4776977 {A : Type'} (m : A -> nat) (_58894 : A) (n : nat) : (term383 A m _58894 n) = (term383 A m _58894 n).
Proof. exact (eq_refl (term383 A m _58894 n)). Qed.
Lemma lem4776978 {A : Type'} (s : A -> Prop) (m : A -> nat) (_58894 : A) (n : nat) : (term436 A s m _58894 n) = (term437 A s m _58894 n).
Proof. exact (MK_COMB (@lem4776976 A s _58894) (@lem4776977 A m _58894 n)). Qed.
Lemma lem4776979 {A : Type'} (s : A -> Prop) (m : A -> nat) (_58894 : A) (n : nat) : (term433 A m n s _58894) = (term437 A s m _58894 n).
Proof. exact (TRANS (@lem4776971 A s m _58894 n) (@lem4776978 A s m _58894 n)). Qed.
Lemma lem4776982 {A : Type'} (_58894 : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term437 A s m _58894 n.
Proof. exact (EQ_MP (@lem4776979 A s m _58894 n) (@lem4776968 A _58894 s n f m h1)). Qed.
Lemma lem4776983 {A : Type'} (_58894 : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term437 A s m _58894 n.
Proof. exact (@lem4776982 A _58894 s n f m h1). Qed.
Lemma lem4776984 {A : Type'} (x : A) (s : A -> Prop) (n : nat) (f : nat -> A) (m : A -> nat) (h1 : term378 A s n f m) : term437 A s m x n.
Proof. exact (@lem4776983 A x s n f m h1). Qed.
Lemma lem4776987 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : term383 A m x n.
Proof. exact (@lem4776984 A x s n f m h1 (@lem4776939 A s x f n h2)). Qed.
Lemma lem4776988 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : term438 A m x n.
Proof. exact (fun h0 : term439 A m x n => @lem4776987 A m s x f n h1 h2). Qed.
Lemma lem4776990 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4776991 {A : Type'} (m : A -> nat) (x : A) (n : nat) : (term438 A m x n) = (term383 A m x n).
Proof. exact (@lem4776990 (term383 A m x n)). Qed.
Lemma lem4776992 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : term383 A m x n.
Proof. exact (EQ_MP (@lem4776991 A m x n) (@lem4776988 A m s x f n h1 h2)). Qed.
Lemma lem4776994 (a : Prop) (b : Prop) : (term440 a b) = (term441 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4776995 {A : Type'} (x : A) (f : nat -> A) (_58895 : nat) (n : nat) : (term293 A x f _58895 n) = (term292 A x f _58895 n).
Proof. exact (@lem4776994 (x = (f _58895)) (Peano.lt _58895 n)). Qed.
Lemma lem4776997 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4776998 {A : Type'} (x : A) (f : nat -> A) (_58895 : nat) (n : nat) : (term292 A x f _58895 n) = (term442 A x f _58895 n).
Proof. exact (@lem4776997 (term251 A x f _58895 n)). Qed.
Lemma lem4776999 {A : Type'} (x : A) (f : nat -> A) (_58895 : nat) (n : nat) : (term293 A x f _58895 n) = (term442 A x f _58895 n).
Proof. exact (TRANS (@lem4776995 A x f _58895 n) (@lem4776998 A x f _58895 n)). Qed.
Lemma lem4777001 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : term443 A f m x n.
Proof. exact (conj (@lem4776932 A m s x f n h1 h2) (@lem4776992 A m s x f n h1 h2)). Qed.
Lemma lem4777003 {A : Type'} (_58895 : nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : term442 A x f _58895 n.
Proof. exact (EQ_MP (@lem4776999 A x f _58895 n) (@lem4776671 A _58895 s x f n h1)). Qed.
Lemma lem4777004 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term302 A s x f n) : term444 A f m x n.
Proof. exact (@lem4777003 A (m x) s x f n h1). Qed.
Lemma lem4777007 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : False.
Proof. exact (@lem4777004 A m s x f n h2 (@lem4777001 A m s x f n h1 h2)). Qed.
Lemma lem4777008 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : term445.
Proof. exact (fun h0 : ~ False => @lem4777007 A m s x f n h1 h2). Qed.
Lemma lem4777010 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4777011 : term445 = False.
Proof. exact (@lem4777010 False). Qed.
Lemma lem4777012 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : False.
Proof. exact (EQ_MP (@lem4777011) (@lem4777008 A m s x f n h1 h2)). Qed.
Lemma lem4777013 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : (term302 A s x f n) = False.
Proof. exact (prop_ext (fun h3 : term302 A s x f n => @lem4777012 A m s x f n h1 h2) (fun h3 : False => @lem4776613 A s x f n h2)). Qed.
Lemma lem4777014 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : False.
Proof. exact (EQ_MP (@lem4777013 A m s x f n h1 h2) (@lem4776613 A s x f n h2)). Qed.
Lemma lem4777015 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : (term378 A s n f m) = False.
Proof. exact (prop_ext (fun h3 : term378 A s n f m => @lem4777014 A m s x f n h1 h2) (fun h3 : False => @lem4776584 A s n f m h1)). Qed.
Lemma lem4777016 {A : Type'} (m : A -> nat) (s : A -> Prop) (x : A) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term302 A s x f n) : False.
Proof. exact (EQ_MP (@lem4777015 A m s x f n h1 h2) (@lem4776584 A s n f m h1)). Qed.
Lemma lem4777017 {A : Type'} (m : A -> nat) (s : A -> Prop) (f : nat -> A) (n : nat) (h1 : term378 A s n f m) (h2 : term264 A s f n) : False.
Proof. exact (ex_elim (@lem4776362 A s f n h2) (fun x : A => fun h0 : term310 A s f n x => @lem4777016 A m s x f n h1 h0)). Qed.
Lemma lem4777018 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term264 A s f n) (h2 : term291 A s n f) : False.
Proof. exact (ex_elim (@lem4776551 A s n f h2) (fun m : A -> nat => fun h0 : term380 A s n f m => @lem4777017 A m s f n h0 h1)). Qed.
Lemma lem4777019 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term264 A s f n) (h2 : term291 A s n f) : (term291 A s n f) = False.
Proof. exact (prop_ext (fun h3 : term291 A s n f => @lem4777018 A s n f h1 h2) (fun h3 : False => @lem4776248 A s n f h2)). Qed.
Lemma lem4777020 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term264 A s f n) (h2 : term291 A s n f) : False.
Proof. exact (EQ_MP (@lem4777019 A s n f h1 h2) (@lem4776248 A s n f h2)). Qed.
Lemma lem4777021 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (h1 : term264 A s f n) : term290 A s n f.
Proof. exact (fun h0 : term291 A s n f => @lem4777020 A s n f h1 h0). Qed.
Lemma lem4777022 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (h1 : term264 A s f n) : term268 A s n f.
Proof. exact (EQ_MP (@lem4776247 A s n f) (@lem4777021 A s f n h1)). Qed.
Lemma lem4777023 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term269 A s n f.
Proof. exact (fun h0 : term264 A s f n => @lem4777022 A s f n h0). Qed.
Lemma lem4777028 {A : Type'} (n : nat) (f : nat -> A) : term281 A n f.
Proof. exact (fun s : A -> Prop => @lem4777023 A s n f). Qed.
Lemma lem4777033 {A : Type'} (f : nat -> A) : term285 A f.
Proof. exact (fun n : nat => @lem4777028 A n f). Qed.
Lemma lem4777038 {A : Type'} : term289 A.
Proof. exact (fun f : nat -> A => @lem4777033 A f). Qed.
Lemma lem4777039 {A : Type'} : term288 A.
Proof. exact (EQ_MP (@lem4776242 A) (@lem4777038 A)). Qed.
Lemma lem4777040 {A : Type'} (f : nat -> A) : term446 A f.
Proof. exact (@lem4777039 A f). Qed.
Lemma lem4777041 {A : Type'} (f : nat -> A) : (term446 A f) = (term284 A f).
Proof. exact (eq_refl (term446 A f)). Qed.
Lemma lem4777042 {A : Type'} (f : nat -> A) : term284 A f.
Proof. exact (EQ_MP (@lem4777041 A f) (@lem4777040 A f)). Qed.
Lemma lem4777043 {A : Type'} (f : nat -> A) (n : nat) : term447 A f n.
Proof. exact (@lem4777042 A f n). Qed.
Lemma lem4777044 {A : Type'} (n : nat) (f : nat -> A) : (term447 A f n) = (term280 A n f).
Proof. exact (eq_refl (term447 A f n)). Qed.
Lemma lem4777045 {A : Type'} (n : nat) (f : nat -> A) : term280 A n f.
Proof. exact (EQ_MP (@lem4777044 A n f) (@lem4777043 A f n)). Qed.
Lemma lem4777046 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) : term448 A n f s.
Proof. exact (@lem4777045 A n f s). Qed.
Lemma lem4777047 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : (term448 A n f s) = (term271 A s n f).
Proof. exact (eq_refl (term448 A n f s)). Qed.
Lemma lem4777048 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term271 A s n f.
Proof. exact (EQ_MP (@lem4777047 A s n f) (@lem4777046 A n f s)). Qed.
Lemma lem4777050 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term271 A s n f.
Proof. exact (@lem4775998 A s n f (@lem4777048 A s n f)). Qed.
Lemma lem4777051 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term272 A s n f) : False.
Proof. exact (@lem4777050 A s n f (@lem4775982 A s n f h1)). Qed.
Lemma lem4777052 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term272 A s n f) : (term272 A s n f) = False.
Proof. exact (prop_ext (fun h2 : term272 A s n f => @lem4777051 A s n f h1) (fun h2 : False => @lem4775982 A s n f h1)). Qed.
Lemma lem4777053 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) (h1 : term272 A s n f) : False.
Proof. exact (EQ_MP (@lem4777052 A s n f h1) (@lem4775982 A s n f h1)). Qed.
Lemma lem4777054 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term271 A s n f.
Proof. exact (fun h0 : term272 A s n f => @lem4777053 A s n f h0). Qed.
Lemma lem4777055 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term269 A s n f.
Proof. exact (EQ_MP (@lem4775981 A s n f) (@lem4777054 A s n f)). Qed.
Lemma lem4777056 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term218 A s n f.
Proof. exact (EQ_MP (@lem4775977 A s n f) (@lem4777055 A s n f)). Qed.
Lemma lem4777057 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term217 A s n f.
Proof. exact (EQ_MP (@lem4775839 A s n f) (@lem4777056 A s n f)). Qed.
Lemma lem4777058 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) (h1 : term189 A s f n) : term115 A s n f.
Proof. exact (@lem4777057 A s n f (@lem4775794 A s f n h1)). Qed.
Lemma lem4777059 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term208 A s n f.
Proof. exact (fun h0 : term189 A s f n => @lem4777058 A s f n h0). Qed.
Lemma lem4777060 {A : Type'} (s : A -> Prop) (n : nat) (f : nat -> A) : term207 A s n f.
Proof. exact (EQ_MP (@lem4775788 A s n f) (@lem4777059 A s n f)). Qed.
Lemma lem4777061 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (h1 : @INFINITE A s) : term115 A s n f.
Proof. exact (@lem4777060 A s n f (@lem4775578 A f n s h1)). Qed.
Lemma lem4777062 {A : Type'} (n : nat) (f : nat -> A) (s : A -> Prop) (h1 : @INFINITE A s) : term117 A s n f.
Proof. exact (fun h0 : term110 A n s f => @lem4777061 A n f s h1). Qed.
Lemma lem4777067 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : @INFINITE A s) : term121 A s f.
Proof. exact (fun n : nat => @lem4777062 A n f s h1). Qed.
Lemma lem4777072 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : term125 A s.
Proof. exact (fun f : nat -> A => @lem4777067 A f s h1). Qed.
Lemma lem4777073 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : term127 A s.
Proof. exact (EQ_MP (@lem4775568 A s) (@lem4777072 A s h1)). Qed.
Lemma lem4777074 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : term67 A s.
Proof. exact (@lem4774514 A s (@lem4777073 A s h1)). Qed.
Lemma lem4777076 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term18 A P Q.
Proof. exact (@lem4774310 A P Q (@lem7401 A P Q)). Qed.
Lemma lem4777077 {A : Type'} (P : type976 A) (Q : type976 A) : term449 A P Q.
Proof. exact (@lem4777076 (nat -> A) P Q). Qed.
Lemma lem4777078 {A : Type'} (s : A -> Prop) : term450 A s.
Proof. exact (@lem4777077 A (term135 A s) (term451 A s)). Qed.
Lemma lem4777079 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term452 A s f) = (term133 A s f).
Proof. exact (eq_refl (term452 A s f)). Qed.
Lemma lem4777080 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4777081 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term453 A s f) = (term454 A s f).
Proof. exact (MK_COMB (@lem4777080) (@lem4777079 A s f)). Qed.
Lemma lem4777082 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term455 A s f) = (term64 A s f).
Proof. exact (eq_refl (term455 A s f)). Qed.
Lemma lem4777083 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term456 A s f) = (term457 A s f).
Proof. exact (MK_COMB (@lem4777081 A s f) (@lem4777082 A s f)). Qed.
Lemma lem4777084 {A : Type'} (s : A -> Prop) : (term458 A s) = (term459 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem4777083 A s f)). Qed.
Lemma lem4777085 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4777086 {A : Type'} (s : A -> Prop) : (term460 A s) = (term461 A s).
Proof. exact (MK_COMB (@lem4777085 A) (@lem4777084 A s)). Qed.
Lemma lem4777087 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4777088 {A : Type'} (s : A -> Prop) : (term462 A s) = (term463 A s).
Proof. exact (MK_COMB (@lem4777087) (@lem4777086 A s)). Qed.
Lemma lem4777089 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term452 A s f) = (term133 A s f).
Proof. exact (eq_refl (term452 A s f)). Qed.
Lemma lem4777090 {A : Type'} (s : A -> Prop) : (term464 A s) = (term135 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem4777089 A s f)). Qed.
Lemma lem4777091 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem4777092 {A : Type'} (s : A -> Prop) : (term465 A s) = (term67 A s).
Proof. exact (MK_COMB (@lem4777091 A) (@lem4777090 A s)). Qed.
Lemma lem4777093 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4777094 {A : Type'} (s : A -> Prop) : (term466 A s) = (term467 A s).
Proof. exact (MK_COMB (@lem4777093) (@lem4777092 A s)). Qed.
Lemma lem4777095 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term455 A s f) = (term64 A s f).
Proof. exact (eq_refl (term455 A s f)). Qed.
Lemma lem4777096 {A : Type'} (s : A -> Prop) : (term468 A s) = (term451 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem4777095 A s f)). Qed.
Lemma lem4777097 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem4777098 {A : Type'} (s : A -> Prop) : (term469 A s) = (term63 A s).
Proof. exact (MK_COMB (@lem4777097 A) (@lem4777096 A s)). Qed.
Lemma lem4777099 {A : Type'} (s : A -> Prop) : (term470 A s) = (term471 A s).
Proof. exact (MK_COMB (@lem4777094 A s) (@lem4777098 A s)). Qed.
Lemma lem4777100 {A : Type'} (s : A -> Prop) : (term450 A s) = (term472 A s).
Proof. exact (MK_COMB (@lem4777088 A s) (@lem4777099 A s)). Qed.
Lemma lem4777101 {A : Type'} (s : A -> Prop) : term472 A s.
Proof. exact (EQ_MP (@lem4777100 A s) (@lem4777078 A s)). Qed.
Lemma lem4777102 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : term133 A s f.
Proof. exact (h1). Qed.
Lemma lem4777105 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : term473 A s f n.
Proof. exact (@lem4777102 A s f h1 n). Qed.
Lemma lem4777106 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term473 A s f n) = (term103 A s f n).
Proof. exact (eq_refl (term473 A s f n)). Qed.
Lemma lem4777107 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : term103 A s f n.
Proof. exact (EQ_MP (@lem4777106 A s f n) (@lem4777105 A n s f h1)). Qed.
Lemma lem4777114 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : term474 A f n s.
Proof. exact (proj1 (@lem4777107 A n s f h1)). Qed.
Lemma lem4777115 {A : Type'} (f : nat -> A) (n : nat) (s : A -> Prop) : (term474 A f n s) = ((term474 A f n s) = True).
Proof. exact (@lem7 (term474 A f n s)). Qed.
Lemma lem4777124 {A : Type'} (n : nat) (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : (term474 A f n s) = True.
Proof. exact (EQ_MP (@lem4777115 A f n s) (@lem4777114 A n s f h1)). Qed.
Lemma lem4777125 {A : Type'} (x : nat) (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : (term474 A f x s) = True.
Proof. exact (@lem4777124 A x s f h1). Qed.
Lemma lem4777126 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : (term475 A f s) = term172.
Proof. exact (fun_ext (fun x : nat => @lem4777125 A x s f h1)). Qed.
Lemma lem4777127 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777128 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : (term66 A f s) = term173.
Proof. exact (MK_COMB (@lem4777127) (@lem4777126 A s f h1)). Qed.
Lemma lem4777130 {A : Type'} (t : Prop) : (term171 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4777131 (t : Prop) : (term174 t) = t.
Proof. exact (@lem4777130 nat t). Qed.
Lemma lem4777132 : term173 = True.
Proof. exact (@lem4777131 True). Qed.
Lemma lem4777133 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : (term66 A f s) = True.
Proof. exact (TRANS (@lem4777128 A s f h1) (@lem4777132)). Qed.
Lemma lem4777134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777135 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : (term476 A f s) = (and True).
Proof. exact (MK_COMB (@lem4777134) (@lem4777133 A s f h1)). Qed.
Lemma lem4777152 {A : Type'} (f : nat -> A) : (term65 A f) = (term65 A f).
Proof. exact (eq_refl (term65 A f)). Qed.
Lemma lem4777153 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : (term64 A s f) = (term477 A f).
Proof. exact (MK_COMB (@lem4777135 A s f h1) (@lem4777152 A f)). Qed.
Lemma lem4777155 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4777156 {A : Type'} (f : nat -> A) : (term477 A f) = (term65 A f).
Proof. exact (@lem4777155 (term65 A f)). Qed.
Lemma lem4777173 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : (term64 A s f) = (term65 A f).
Proof. exact (TRANS (@lem4777153 A s f h1) (@lem4777156 A f)). Qed.
Lemma lem4777174 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term133 A s f) : (term65 A f) = (term64 A s f).
Proof. exact (SYM (@lem4777173 A s f h1)). Qed.
Lemma lem4777176 (P : type1605) : term13 P.
Proof. exact (@lem4774301 P (@lem111142 P)). Qed.
Lemma lem4777177 {A : Type'} (f : nat -> A) : term478 A f.
Proof. exact (@lem4777176 (term479 A f)). Qed.
Lemma lem4777178 {A : Type'} (f : nat -> A) (x : nat) : (term480 A f x) = (term481 A f x).
Proof. exact (eq_refl (term480 A f x)). Qed.
Lemma lem4777179 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4777180 {A : Type'} (f : nat -> A) (x : nat) : (term482 A f x) = (term483 A f x).
Proof. exact (MK_COMB (@lem4777178 A f x) (@lem4777179 x)). Qed.
Lemma lem4777181 {A : Type'} (f : nat -> A) (x : nat) : (term483 A f x) = (term484 A f x).
Proof. exact (eq_refl (term483 A f x)). Qed.
Lemma lem4777182 {A : Type'} (f : nat -> A) (x : nat) : (term482 A f x) = (term484 A f x).
Proof. exact (TRANS (@lem4777180 A f x) (@lem4777181 A f x)). Qed.
Lemma lem4777183 {A : Type'} (f : nat -> A) : (term485 A f) = (term486 A f).
Proof. exact (fun_ext (fun x : nat => @lem4777182 A f x)). Qed.
Lemma lem4777184 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777185 {A : Type'} (f : nat -> A) : (term487 A f) = (term488 A f).
Proof. exact (MK_COMB (@lem4777184) (@lem4777183 A f)). Qed.
Lemma lem4777186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777187 {A : Type'} (f : nat -> A) : (term489 A f) = (term490 A f).
Proof. exact (MK_COMB (@lem4777186) (@lem4777185 A f)). Qed.
Lemma lem4777188 {A : Type'} (f : nat -> A) (x : nat) : (term480 A f x) = (term481 A f x).
Proof. exact (eq_refl (term480 A f x)). Qed.
Lemma lem4777189 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4777190 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term491 A f x n) = (term492 A f x n).
Proof. exact (MK_COMB (@lem4777188 A f x) (@lem4777189 n)). Qed.
Lemma lem4777191 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term492 A f x n) = (term493 A f x n).
Proof. exact (eq_refl (term492 A f x n)). Qed.
Lemma lem4777192 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term491 A f x n) = (term493 A f x n).
Proof. exact (TRANS (@lem4777190 A f x n) (@lem4777191 A f x n)). Qed.
Lemma lem4777193 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4777194 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term494 A f x n) = (term495 A f x n).
Proof. exact (MK_COMB (@lem4777193) (@lem4777192 A f x n)). Qed.
Lemma lem4777195 {A : Type'} (f : nat -> A) (n : nat) : (term480 A f n) = (term481 A f n).
Proof. exact (eq_refl (term480 A f n)). Qed.
Lemma lem4777196 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4777197 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term491 A f n x) = (term492 A f n x).
Proof. exact (MK_COMB (@lem4777195 A f n) (@lem4777196 x)). Qed.
Lemma lem4777198 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term492 A f n x) = (term493 A f n x).
Proof. exact (eq_refl (term492 A f n x)). Qed.
Lemma lem4777199 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term491 A f n x) = (term493 A f n x).
Proof. exact (TRANS (@lem4777197 A f n x) (@lem4777198 A f n x)). Qed.
Lemma lem4777200 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : ((term491 A f x n) = (term491 A f n x)) = ((term493 A f x n) = (term493 A f n x)).
Proof. exact (MK_COMB (@lem4777194 A f x n) (@lem4777199 A f n x)). Qed.
Lemma lem4777201 {A : Type'} (f : nat -> A) (x : nat) : (term496 A f x) = (term497 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4777200 A f n x)). Qed.
Lemma lem4777202 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777203 {A : Type'} (f : nat -> A) (x : nat) : (term498 A f x) = (term499 A f x).
Proof. exact (MK_COMB (@lem4777202) (@lem4777201 A f x)). Qed.
Lemma lem4777204 {A : Type'} (f : nat -> A) : (term500 A f) = (term501 A f).
Proof. exact (fun_ext (fun x : nat => @lem4777203 A f x)). Qed.
Lemma lem4777205 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777206 {A : Type'} (f : nat -> A) : (term502 A f) = (term503 A f).
Proof. exact (MK_COMB (@lem4777205) (@lem4777204 A f)). Qed.
Lemma lem4777207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777208 {A : Type'} (f : nat -> A) : (term504 A f) = (term505 A f).
Proof. exact (MK_COMB (@lem4777207) (@lem4777206 A f)). Qed.
Lemma lem4777209 {A : Type'} (f : nat -> A) (x : nat) : (term480 A f x) = (term481 A f x).
Proof. exact (eq_refl (term480 A f x)). Qed.
Lemma lem4777210 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4777211 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term491 A f x n) = (term492 A f x n).
Proof. exact (MK_COMB (@lem4777209 A f x) (@lem4777210 n)). Qed.
Lemma lem4777212 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term492 A f x n) = (term493 A f x n).
Proof. exact (eq_refl (term492 A f x n)). Qed.
Lemma lem4777213 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term491 A f x n) = (term493 A f x n).
Proof. exact (TRANS (@lem4777211 A f x n) (@lem4777212 A f x n)). Qed.
Lemma lem4777214 (x : nat) (n : nat) : (term104 x n) = (term104 x n).
Proof. exact (eq_refl (term104 x n)). Qed.
Lemma lem4777215 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term506 A f x n) = (term507 A f x n).
Proof. exact (MK_COMB (@lem4777214 x n) (@lem4777213 A f x n)). Qed.
Lemma lem4777216 {A : Type'} (f : nat -> A) (x : nat) : (term508 A f x) = (term509 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4777215 A f x n)). Qed.
Lemma lem4777217 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777218 {A : Type'} (f : nat -> A) (x : nat) : (term510 A f x) = (term511 A f x).
Proof. exact (MK_COMB (@lem4777217) (@lem4777216 A f x)). Qed.
Lemma lem4777219 {A : Type'} (f : nat -> A) : (term512 A f) = (term513 A f).
Proof. exact (fun_ext (fun x : nat => @lem4777218 A f x)). Qed.
Lemma lem4777220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777221 {A : Type'} (f : nat -> A) : (term514 A f) = (term515 A f).
Proof. exact (MK_COMB (@lem4777220) (@lem4777219 A f)). Qed.
Lemma lem4777222 {A : Type'} (f : nat -> A) : (term516 A f) = (term517 A f).
Proof. exact (MK_COMB (@lem4777208 A f) (@lem4777221 A f)). Qed.
Lemma lem4777223 {A : Type'} (f : nat -> A) : (term518 A f) = (term519 A f).
Proof. exact (MK_COMB (@lem4777187 A f) (@lem4777222 A f)). Qed.
Lemma lem4777224 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4777225 {A : Type'} (f : nat -> A) : (term520 A f) = (term521 A f).
Proof. exact (MK_COMB (@lem4777224) (@lem4777223 A f)). Qed.
Lemma lem4777226 {A : Type'} (f : nat -> A) (x : nat) : (term480 A f x) = (term481 A f x).
Proof. exact (eq_refl (term480 A f x)). Qed.
Lemma lem4777227 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4777228 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term491 A f x y) = (term492 A f x y).
Proof. exact (MK_COMB (@lem4777226 A f x) (@lem4777227 y)). Qed.
Lemma lem4777229 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term492 A f x y) = (term493 A f x y).
Proof. exact (eq_refl (term492 A f x y)). Qed.
Lemma lem4777230 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term491 A f x y) = (term493 A f x y).
Proof. exact (TRANS (@lem4777228 A f x y) (@lem4777229 A f x y)). Qed.
Lemma lem4777231 {A : Type'} (f : nat -> A) (x : nat) : (term522 A f x) = (term481 A f x).
Proof. exact (fun_ext (fun y : nat => @lem4777230 A f x y)). Qed.
Lemma lem4777232 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777233 {A : Type'} (f : nat -> A) (x : nat) : (term523 A f x) = (term524 A f x).
Proof. exact (MK_COMB (@lem4777232) (@lem4777231 A f x)). Qed.
Lemma lem4777234 {A : Type'} (f : nat -> A) : (term525 A f) = (term526 A f).
Proof. exact (fun_ext (fun x : nat => @lem4777233 A f x)). Qed.
Lemma lem4777235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777236 {A : Type'} (f : nat -> A) : (term527 A f) = (term65 A f).
Proof. exact (MK_COMB (@lem4777235) (@lem4777234 A f)). Qed.
Lemma lem4777237 {A : Type'} (f : nat -> A) : (term478 A f) = (term528 A f).
Proof. exact (MK_COMB (@lem4777225 A f) (@lem4777236 A f)). Qed.
Lemma lem4777238 {A : Type'} (f : nat -> A) : term528 A f.
Proof. exact (EQ_MP (@lem4777237 A f) (@lem4777177 A f)). Qed.
Lemma lem4777249 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term133 A s f) (h2 : @INFINITE A s) : term529 A f s.
Proof. exact (conj (@lem4777102 A s f h1) (@lem4774413 A s h2)). Qed.
Lemma lem4777277 {_739 : Type'} (x : _739) (p : Prop) : (term530 _739 x p) = p.
Proof. exact (EQ_MP (@lem1804 _739 x p) (@lem0)). Qed.
Lemma lem4777278 {A : Type'} (x : A) (p : Prop) : (term530 A x p) = p.
Proof. exact (@lem4777277 A x p). Qed.
Lemma lem4777279 {A : Type'} (f : nat -> A) (x : nat) : (term484 A f x) = (x = x).
Proof. exact (@lem4777278 A (f x) (x = x)). Qed.
Lemma lem4777281 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4777282 (x : nat) : (x = x) = True.
Proof. exact (@lem4777281 nat x). Qed.
Lemma lem4777283 {A : Type'} (f : nat -> A) (x : nat) : (term484 A f x) = True.
Proof. exact (TRANS (@lem4777279 A f x) (@lem4777282 x)). Qed.
Lemma lem4777284 {A : Type'} (f : nat -> A) : (term486 A f) = term172.
Proof. exact (fun_ext (fun x : nat => @lem4777283 A f x)). Qed.
Lemma lem4777285 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777286 {A : Type'} (f : nat -> A) : (term488 A f) = term173.
Proof. exact (MK_COMB (@lem4777285) (@lem4777284 A f)). Qed.
Lemma lem4777288 {A : Type'} (t : Prop) : (term171 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4777289 (t : Prop) : (term174 t) = t.
Proof. exact (@lem4777288 nat t). Qed.
Lemma lem4777290 : term173 = True.
Proof. exact (@lem4777289 True). Qed.
Lemma lem4777291 {A : Type'} (f : nat -> A) : (term488 A f) = True.
Proof. exact (TRANS (@lem4777286 A f) (@lem4777290)). Qed.
Lemma lem4777292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777293 {A : Type'} (f : nat -> A) : (term490 A f) = (and True).
Proof. exact (MK_COMB (@lem4777292) (@lem4777291 A f)). Qed.
Lemma lem4777354 {A : Type'} (f : nat -> A) : (term517 A f) = (term517 A f).
Proof. exact (eq_refl (term517 A f)). Qed.
Lemma lem4777355 {A : Type'} (f : nat -> A) : (term519 A f) = (term531 A f).
Proof. exact (MK_COMB (@lem4777293 A f) (@lem4777354 A f)). Qed.
Lemma lem4777357 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4777358 {A : Type'} (f : nat -> A) : (term531 A f) = (term517 A f).
Proof. exact (@lem4777357 (term517 A f)). Qed.
Lemma lem4777419 {A : Type'} (f : nat -> A) : (term519 A f) = (term517 A f).
Proof. exact (TRANS (@lem4777355 A f) (@lem4777358 A f)). Qed.
Lemma lem4777420 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term532 A f s) = (term532 A f s).
Proof. exact (eq_refl (term532 A f s)). Qed.
Lemma lem4777421 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term533 A s f) = (term534 A s f).
Proof. exact (MK_COMB (@lem4777420 A f s) (@lem4777419 A f)). Qed.
Lemma lem4777424 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term534 A s f) = (term533 A s f).
Proof. exact (SYM (@lem4777421 A s f)). Qed.
Lemma lem4777436 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4777437 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4777436 A P x). Qed.
Lemma lem4777438 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term474 A f n s) = (term535 A s f n).
Proof. exact (@lem4777437 A s (f n)). Qed.
Lemma lem4777439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777440 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term536 A f n s) = (term537 A s f n).
Proof. exact (MK_COMB (@lem4777439) (@lem4777438 A s f n)). Qed.
Lemma lem4777449 {A : Type'} (f : nat -> A) (n : nat) : (term538 A f n) = (term538 A f n).
Proof. exact (eq_refl (term538 A f n)). Qed.
Lemma lem4777450 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term103 A s f n) = (term539 A s f n).
Proof. exact (MK_COMB (@lem4777440 A s f n) (@lem4777449 A f n)). Qed.
Lemma lem4777453 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term131 A s f) = (term540 A s f).
Proof. exact (fun_ext (fun n : nat => @lem4777450 A s f n)). Qed.
Lemma lem4777454 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777455 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term133 A s f) = (term541 A s f).
Proof. exact (MK_COMB (@lem4777454) (@lem4777453 A s f)). Qed.
Lemma lem4777460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777461 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term542 A s f) = (term543 A s f).
Proof. exact (MK_COMB (@lem4777460) (@lem4777455 A s f)). Qed.
Lemma lem4777462 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (@INFINITE A s).
Proof. exact (eq_refl (@INFINITE A s)). Qed.
Lemma lem4777463 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term529 A f s) = (term544 A f s).
Proof. exact (MK_COMB (@lem4777461 A s f) (@lem4777462 A s)). Qed.
Lemma lem4777466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4777467 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term532 A f s) = (term545 A f s).
Proof. exact (MK_COMB (@lem4777466) (@lem4777463 A f s)). Qed.
Lemma lem4777514 {A : Type'} (f : nat -> A) : (term517 A f) = (term517 A f).
Proof. exact (eq_refl (term517 A f)). Qed.
Lemma lem4777515 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term534 A s f) = (term546 A s f).
Proof. exact (MK_COMB (@lem4777467 A f s) (@lem4777514 A f)). Qed.
Lemma lem4777518 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term546 A s f) = (term534 A s f).
Proof. exact (SYM (@lem4777515 A s f)). Qed.
Lemma lem4777520 (p : Prop) : p = (term270 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4777521 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term546 A s f) = (term547 A s f).
Proof. exact (@lem4777520 (term546 A s f)). Qed.
Lemma lem4777522 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term547 A s f) = (term546 A s f).
Proof. exact (SYM (@lem4777521 A s f)). Qed.
Lemma lem4777523 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term548 A s f) : term548 A s f.
Proof. exact (h1). Qed.
Lemma lem4777526 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term547 A s f) : term547 A s f.
Proof. exact (h1). Qed.
Lemma lem4777527 {A : Type'} (s : A -> Prop) (f : nat -> A) : term549 A s f.
Proof. exact (fun h0 : term547 A s f => @lem4777526 A s f h0). Qed.
Lemma lem4777528 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term549 A s f) : term549 A s f.
Proof. exact (h1). Qed.
Lemma lem4777529 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term547 A s f) : term547 A s f.
Proof. exact (h1). Qed.
Lemma lem4777530 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term547 A s f) (h2 : term549 A s f) : term547 A s f.
Proof. exact (@lem4777528 A s f h2 (@lem4777529 A s f h1)). Qed.
Lemma lem4777531 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term547 A s f) : term550 A s f.
Proof. exact (fun h0 : term549 A s f => @lem4777530 A s f h1 h0). Qed.
Lemma lem4777532 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term549 A s f) : term549 A s f.
Proof. exact (h1). Qed.
Lemma lem4777533 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term547 A s f) (h2 : term549 A s f) : term547 A s f.
Proof. exact (@lem4777531 A s f h1 (@lem4777532 A s f h2)). Qed.
Lemma lem4777534 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term549 A s f) : term549 A s f.
Proof. exact (fun h0 : term547 A s f => @lem4777533 A s f h0 h1). Qed.
Lemma lem4777535 {A : Type'} (s : A -> Prop) (f : nat -> A) : term551 A s f.
Proof. exact (fun h0 : term549 A s f => @lem4777534 A s f h0). Qed.
Lemma lem4777538 {A : Type'} (s : A -> Prop) (f : nat -> A) : term549 A s f.
Proof. exact (@lem4777535 A s f (@lem4777527 A s f)). Qed.
Lemma lem4777539 {A : Type'} (s : A -> Prop) (f : nat -> A) : term549 A s f.
Proof. exact (@lem4777538 A s f). Qed.
Lemma lem4777549 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4777550 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term547 A s f) = (term552 A s f).
Proof. exact (@lem4777549 (term548 A s f)). Qed.
Lemma lem4777552 (t : Prop) : (term277 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4777553 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term552 A s f) = (term546 A s f).
Proof. exact (@lem4777552 (term546 A s f)). Qed.
Lemma lem4777556 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term547 A s f) = (term546 A s f).
Proof. exact (TRANS (@lem4777550 A s f) (@lem4777553 A s f)). Qed.
Lemma lem4777560 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term554 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem4777561 (P : nat -> Prop) (Q : nat -> Prop) : (term555 P Q) = (term556 P Q).
Proof. exact (@lem4777560 nat P Q). Qed.
Lemma lem4777562 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term557 A s f) = (term558 A s f).
Proof. exact (@lem4777561 (term559 A s f) (term560 A f)). Qed.
Lemma lem4777563 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term561 A s f n) = (term535 A s f n).
Proof. exact (eq_refl (term561 A s f n)). Qed.
Lemma lem4777564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777565 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term562 A s f n) = (term537 A s f n).
Proof. exact (MK_COMB (@lem4777564) (@lem4777563 A s f n)). Qed.
Lemma lem4777566 {A : Type'} (f : nat -> A) (n : nat) : (term563 A f n) = (term538 A f n).
Proof. exact (eq_refl (term563 A f n)). Qed.
Lemma lem4777567 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term564 A s f n) = (term539 A s f n).
Proof. exact (MK_COMB (@lem4777565 A s f n) (@lem4777566 A f n)). Qed.
Lemma lem4777568 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term565 A s f) = (term540 A s f).
Proof. exact (fun_ext (fun n : nat => @lem4777567 A s f n)). Qed.
Lemma lem4777569 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777570 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term557 A s f) = (term541 A s f).
Proof. exact (MK_COMB (@lem4777569) (@lem4777568 A s f)). Qed.
Lemma lem4777571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4777572 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term566 A s f) = (term567 A s f).
Proof. exact (MK_COMB (@lem4777571) (@lem4777570 A s f)). Qed.
Lemma lem4777573 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term561 A s f n) = (term535 A s f n).
Proof. exact (eq_refl (term561 A s f n)). Qed.
Lemma lem4777574 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term568 A s f) = (term559 A s f).
Proof. exact (fun_ext (fun n : nat => @lem4777573 A s f n)). Qed.
Lemma lem4777575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777576 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term569 A s f) = (term570 A s f).
Proof. exact (MK_COMB (@lem4777575) (@lem4777574 A s f)). Qed.
Lemma lem4777577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777578 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term571 A s f) = (term572 A s f).
Proof. exact (MK_COMB (@lem4777577) (@lem4777576 A s f)). Qed.
Lemma lem4777579 {A : Type'} (f : nat -> A) (n : nat) : (term563 A f n) = (term538 A f n).
Proof. exact (eq_refl (term563 A f n)). Qed.
Lemma lem4777580 {A : Type'} (f : nat -> A) : (term573 A f) = (term560 A f).
Proof. exact (fun_ext (fun n : nat => @lem4777579 A f n)). Qed.
Lemma lem4777581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777582 {A : Type'} (f : nat -> A) : (term574 A f) = (term575 A f).
Proof. exact (MK_COMB (@lem4777581) (@lem4777580 A f)). Qed.
Lemma lem4777583 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term558 A s f) = (term576 A s f).
Proof. exact (MK_COMB (@lem4777578 A s f) (@lem4777582 A f)). Qed.
Lemma lem4777584 {A : Type'} (s : A -> Prop) (f : nat -> A) : ((term557 A s f) = (term558 A s f)) = ((term541 A s f) = (term576 A s f)).
Proof. exact (MK_COMB (@lem4777572 A s f) (@lem4777583 A s f)). Qed.
Lemma lem4777585 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term541 A s f) = (term576 A s f).
Proof. exact (EQ_MP (@lem4777584 A s f) (@lem4777562 A s f)). Qed.
Lemma lem4777602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777603 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term543 A s f) = (term577 A s f).
Proof. exact (MK_COMB (@lem4777602) (@lem4777585 A s f)). Qed.
Lemma lem4777604 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (@INFINITE A s).
Proof. exact (eq_refl (@INFINITE A s)). Qed.
Lemma lem4777605 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term544 A f s) = (term578 A f s).
Proof. exact (MK_COMB (@lem4777603 A s f) (@lem4777604 A s)). Qed.
Lemma lem4777608 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4777609 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term545 A f s) = (term579 A f s).
Proof. exact (MK_COMB (@lem4777608) (@lem4777605 A f s)). Qed.
Lemma lem4777636 {A : Type'} (f : nat -> A) : (term517 A f) = (term517 A f).
Proof. exact (eq_refl (term517 A f)). Qed.
Lemma lem4777637 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term546 A s f) = (term580 A s f).
Proof. exact (MK_COMB (@lem4777609 A f s) (@lem4777636 A f)). Qed.
Lemma lem4777640 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term547 A s f) = (term580 A s f).
Proof. exact (TRANS (@lem4777556 A s f) (@lem4777637 A s f)). Qed.
Lemma lem4777641 {A : Type'} (f : nat -> A) : (term581 A f) = (term582 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4777640 A s f)). Qed.
Lemma lem4777642 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4777643 {A : Type'} (f : nat -> A) : (term583 A f) = (term584 A f).
Proof. exact (MK_COMB (@lem4777642 A) (@lem4777641 A f)). Qed.
Lemma lem4777648 {A : Type'} : (term585 A) = (term586 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem4777643 A f)). Qed.
Lemma lem4777649 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4777658 {A : Type'} : (term587 A) = (term588 A).
Proof. exact (MK_COMB (@lem4777649 A) (@lem4777648 A)). Qed.
Lemma lem4777667 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term507 A f x n) = (term507 A f x n).
Proof. exact (eq_refl (term507 A f x n)). Qed.
Lemma lem4777668 {A : Type'} (f : nat -> A) (x : nat) : (term509 A f x) = (term509 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4777667 A f x n)). Qed.
Lemma lem4777669 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777670 {A : Type'} (f : nat -> A) (x : nat) : (term511 A f x) = (term511 A f x).
Proof. exact (MK_COMB (@lem4777669) (@lem4777668 A f x)). Qed.
Lemma lem4777671 {A : Type'} (f : nat -> A) : (term513 A f) = (term513 A f).
Proof. exact (fun_ext (fun x : nat => @lem4777670 A f x)). Qed.
Lemma lem4777672 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777673 {A : Type'} (f : nat -> A) : (term515 A f) = (term515 A f).
Proof. exact (MK_COMB (@lem4777672) (@lem4777671 A f)). Qed.
Lemma lem4777686 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : ((term493 A f x n) = (term493 A f n x)) = ((term493 A f x n) = (term493 A f n x)).
Proof. exact (eq_refl ((term493 A f x n) = (term493 A f n x))). Qed.
Lemma lem4777687 {A : Type'} (f : nat -> A) (x : nat) : (term497 A f x) = (term497 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4777686 A f n x)). Qed.
Lemma lem4777688 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777689 {A : Type'} (f : nat -> A) (x : nat) : (term499 A f x) = (term499 A f x).
Proof. exact (MK_COMB (@lem4777688) (@lem4777687 A f x)). Qed.
Lemma lem4777690 {A : Type'} (f : nat -> A) : (term501 A f) = (term501 A f).
Proof. exact (fun_ext (fun x : nat => @lem4777689 A f x)). Qed.
Lemma lem4777691 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777692 {A : Type'} (f : nat -> A) : (term503 A f) = (term503 A f).
Proof. exact (MK_COMB (@lem4777691) (@lem4777690 A f)). Qed.
Lemma lem4777693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777694 {A : Type'} (f : nat -> A) : (term505 A f) = (term505 A f).
Proof. exact (MK_COMB (@lem4777693) (@lem4777692 A f)). Qed.
Lemma lem4777695 {A : Type'} (f : nat -> A) : (term517 A f) = (term517 A f).
Proof. exact (MK_COMB (@lem4777694 A f) (@lem4777673 A f)). Qed.
Lemma lem4777696 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (@INFINITE A s).
Proof. exact (eq_refl (@INFINITE A s)). Qed.
Lemma lem4777703 {A : Type'} (m : nat) (f : nat -> A) (n : nat) : (term589 A m f n) = (term589 A m f n).
Proof. exact (eq_refl (term589 A m f n)). Qed.
Lemma lem4777704 {A : Type'} (f : nat -> A) (n : nat) : (term590 A f n) = (term590 A f n).
Proof. exact (fun_ext (fun m : nat => @lem4777703 A m f n)). Qed.
Lemma lem4777705 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777706 {A : Type'} (f : nat -> A) (n : nat) : (term538 A f n) = (term538 A f n).
Proof. exact (MK_COMB (@lem4777705) (@lem4777704 A f n)). Qed.
Lemma lem4777707 {A : Type'} (f : nat -> A) : (term560 A f) = (term560 A f).
Proof. exact (fun_ext (fun n : nat => @lem4777706 A f n)). Qed.
Lemma lem4777708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777709 {A : Type'} (f : nat -> A) : (term575 A f) = (term575 A f).
Proof. exact (MK_COMB (@lem4777708) (@lem4777707 A f)). Qed.
Lemma lem4777710 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term535 A s f n) = (term535 A s f n).
Proof. exact (eq_refl (term535 A s f n)). Qed.
Lemma lem4777711 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term559 A s f) = (term559 A s f).
Proof. exact (fun_ext (fun n : nat => @lem4777710 A s f n)). Qed.
Lemma lem4777712 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777713 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term570 A s f) = (term570 A s f).
Proof. exact (MK_COMB (@lem4777712) (@lem4777711 A s f)). Qed.
Lemma lem4777714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777715 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term572 A s f) = (term572 A s f).
Proof. exact (MK_COMB (@lem4777714) (@lem4777713 A s f)). Qed.
Lemma lem4777716 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term576 A s f) = (term576 A s f).
Proof. exact (MK_COMB (@lem4777715 A s f) (@lem4777709 A f)). Qed.
Lemma lem4777717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777718 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term577 A s f) = (term577 A s f).
Proof. exact (MK_COMB (@lem4777717) (@lem4777716 A s f)). Qed.
Lemma lem4777719 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term578 A f s) = (term578 A f s).
Proof. exact (MK_COMB (@lem4777718 A s f) (@lem4777696 A s)). Qed.
Lemma lem4777720 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4777721 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term579 A f s) = (term579 A f s).
Proof. exact (MK_COMB (@lem4777720) (@lem4777719 A f s)). Qed.
Lemma lem4777722 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term580 A s f) = (term580 A s f).
Proof. exact (MK_COMB (@lem4777721 A f s) (@lem4777695 A f)). Qed.
Lemma lem4777723 {A : Type'} (f : nat -> A) : (term582 A f) = (term582 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4777722 A s f)). Qed.
Lemma lem4777724 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4777725 {A : Type'} (f : nat -> A) : (term584 A f) = (term584 A f).
Proof. exact (MK_COMB (@lem4777724 A) (@lem4777723 A f)). Qed.
Lemma lem4777726 {A : Type'} : (term586 A) = (term586 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem4777725 A f)). Qed.
Lemma lem4777727 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4777728 {A : Type'} : (term588 A) = (term588 A).
Proof. exact (MK_COMB (@lem4777727 A) (@lem4777726 A)). Qed.
Lemma lem4777803 {A : Type'} : (term587 A) = (term588 A).
Proof. exact (TRANS (@lem4777658 A) (@lem4777728 A)). Qed.
Lemma lem4777804 {A : Type'} : (term588 A) = (term587 A).
Proof. exact (SYM (@lem4777803 A)). Qed.
Lemma lem4777805 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term578 A f s.
Proof. exact (h1). Qed.
Lemma lem4777807 (p : Prop) : p = (term270 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4777808 {A : Type'} (f : nat -> A) : (term517 A f) = (term591 A f).
Proof. exact (@lem4777807 (term517 A f)). Qed.
Lemma lem4777809 {A : Type'} (f : nat -> A) : (term591 A f) = (term517 A f).
Proof. exact (SYM (@lem4777808 A f)). Qed.
Lemma lem4777810 {A : Type'} (f : nat -> A) (h1 : term592 A f) : term592 A f.
Proof. exact (h1). Qed.
Lemma lem4777811 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term535 A s f n) = (term535 A s f n).
Proof. exact (eq_refl (term535 A s f n)). Qed.
Lemma lem4777812 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term559 A s f) = (term559 A s f).
Proof. exact (fun_ext (fun n : nat => @lem4777811 A s f n)). Qed.
Lemma lem4777813 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777814 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term570 A s f) = (term570 A s f).
Proof. exact (MK_COMB (@lem4777813) (@lem4777812 A s f)). Qed.
Lemma lem4777821 {A : Type'} (m : nat) (f : nat -> A) (n : nat) : (term589 A m f n) = (term593 A m f n).
Proof. exact (@lem17265 (Peano.lt m n) (term594 A m f n)). Qed.
Lemma lem4777822 {A : Type'} (f : nat -> A) (n : nat) : (term590 A f n) = (term595 A f n).
Proof. exact (fun_ext (fun m : nat => @lem4777821 A m f n)). Qed.
Lemma lem4777823 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777824 {A : Type'} (f : nat -> A) (n : nat) : (term538 A f n) = (term596 A f n).
Proof. exact (MK_COMB (@lem4777823) (@lem4777822 A f n)). Qed.
Lemma lem4777825 {A : Type'} (f : nat -> A) : (term560 A f) = (term597 A f).
Proof. exact (fun_ext (fun n : nat => @lem4777824 A f n)). Qed.
Lemma lem4777826 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4777827 {A : Type'} (f : nat -> A) : (term575 A f) = (term598 A f).
Proof. exact (MK_COMB (@lem4777826) (@lem4777825 A f)). Qed.
Lemma lem4777828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777829 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term572 A s f) = (term572 A s f).
Proof. exact (MK_COMB (@lem4777828) (@lem4777814 A s f)). Qed.
Lemma lem4777830 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term576 A s f) = (term599 A s f).
Proof. exact (MK_COMB (@lem4777829 A s f) (@lem4777827 A f)). Qed.
Lemma lem4777831 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (@INFINITE A s).
Proof. exact (eq_refl (@INFINITE A s)). Qed.
Lemma lem4777832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777833 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term577 A s f) = (term600 A s f).
Proof. exact (MK_COMB (@lem4777832) (@lem4777830 A s f)). Qed.
Lemma lem4777894 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term578 A f s) = (term601 A f s).
Proof. exact (MK_COMB (@lem4777833 A s f) (@lem4777831 A s)). Qed.
Lemma lem4777895 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term601 A f s.
Proof. exact (EQ_MP (@lem4777894 A f s) (@lem4777805 A f s h1)). Qed.
Lemma lem4777904 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term602 A f x n) = (term603 A f x n).
Proof. exact (@lem17362 ((f x) = (f n)) (x = n)). Qed.
Lemma lem4777909 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term493 A f x n) = (term604 A f x n).
Proof. exact (@lem17265 ((f x) = (f n)) (x = n)). Qed.
Lemma lem4777918 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term602 A f n x) = (term603 A f n x).
Proof. exact (@lem17362 ((f n) = (f x)) (n = x)). Qed.
Lemma lem4777923 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term493 A f n x) = (term604 A f n x).
Proof. exact (@lem17265 ((f n) = (f x)) (n = x)). Qed.
Lemma lem4777924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777925 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term605 A f x n) = (term606 A f x n).
Proof. exact (MK_COMB (@lem4777924) (@lem4777904 A f x n)). Qed.
Lemma lem4777926 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term607 A f n x) = (term608 A f n x).
Proof. exact (MK_COMB (@lem4777925 A f x n) (@lem4777923 A f n x)). Qed.
Lemma lem4777927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4777928 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term609 A f x n) = (term610 A f x n).
Proof. exact (MK_COMB (@lem4777927) (@lem4777909 A f x n)). Qed.
Lemma lem4777929 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term611 A f n x) = (term612 A f n x).
Proof. exact (MK_COMB (@lem4777928 A f x n) (@lem4777918 A f n x)). Qed.
Lemma lem4777930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4777931 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term613 A f n x) = (term614 A f n x).
Proof. exact (MK_COMB (@lem4777930) (@lem4777929 A f n x)). Qed.
Lemma lem4777932 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term615 A f n x) = (term616 A f n x).
Proof. exact (MK_COMB (@lem4777931 A f n x) (@lem4777926 A f n x)). Qed.
Lemma lem4777933 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term617 A f n x) = (term615 A f n x).
Proof. exact (@lem17646 (term493 A f x n) (term493 A f n x)). Qed.
Lemma lem4777934 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term617 A f n x) = (term616 A f n x).
Proof. exact (TRANS (@lem4777933 A f n x) (@lem4777932 A f n x)). Qed.
Lemma lem4777935 (P : nat -> Prop) : (term317 P) = (term318 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4777936 {A : Type'} (f : nat -> A) (x : nat) : (term618 A f x) = (term619 A f x).
Proof. exact (@lem4777935 (term497 A f x)). Qed.
Lemma lem4777937 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term620 A f x n) = ((term493 A f x n) = (term493 A f n x)).
Proof. exact (eq_refl (term620 A f x n)). Qed.
Lemma lem4777938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4777939 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term621 A f x n) = (term617 A f n x).
Proof. exact (MK_COMB (@lem4777938) (@lem4777937 A f n x)). Qed.
Lemma lem4777940 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term621 A f x n) = (term616 A f n x).
Proof. exact (TRANS (@lem4777939 A f n x) (@lem4777934 A f n x)). Qed.
Lemma lem4777941 {A : Type'} (f : nat -> A) (x : nat) : (term622 A f x) = (term623 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4777940 A f n x)). Qed.
Lemma lem4777942 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4777943 {A : Type'} (f : nat -> A) (x : nat) : (term619 A f x) = (term624 A f x).
Proof. exact (MK_COMB (@lem4777942) (@lem4777941 A f x)). Qed.
Lemma lem4777944 {A : Type'} (f : nat -> A) (x : nat) : (term618 A f x) = (term624 A f x).
Proof. exact (TRANS (@lem4777936 A f x) (@lem4777943 A f x)). Qed.
Lemma lem4777945 (P : nat -> Prop) : (term317 P) = (term318 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4777946 {A : Type'} (f : nat -> A) : (term625 A f) = (term626 A f).
Proof. exact (@lem4777945 (term501 A f)). Qed.
Lemma lem4777947 {A : Type'} (f : nat -> A) (x : nat) : (term627 A f x) = (term499 A f x).
Proof. exact (eq_refl (term627 A f x)). Qed.
Lemma lem4777948 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4777949 {A : Type'} (f : nat -> A) (x : nat) : (term628 A f x) = (term618 A f x).
Proof. exact (MK_COMB (@lem4777948) (@lem4777947 A f x)). Qed.
Lemma lem4777950 {A : Type'} (f : nat -> A) (x : nat) : (term628 A f x) = (term624 A f x).
Proof. exact (TRANS (@lem4777949 A f x) (@lem4777944 A f x)). Qed.
Lemma lem4777951 {A : Type'} (f : nat -> A) : (term629 A f) = (term630 A f).
Proof. exact (fun_ext (fun x : nat => @lem4777950 A f x)). Qed.
Lemma lem4777952 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4777953 {A : Type'} (f : nat -> A) : (term626 A f) = (term631 A f).
Proof. exact (MK_COMB (@lem4777952) (@lem4777951 A f)). Qed.
Lemma lem4777954 {A : Type'} (f : nat -> A) : (term625 A f) = (term631 A f).
Proof. exact (TRANS (@lem4777946 A f) (@lem4777953 A f)). Qed.
Lemma lem4777962 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term602 A f x n) = (term603 A f x n).
Proof. exact (@lem17362 ((f x) = (f n)) (x = n)). Qed.
Lemma lem4777964 (x : nat) (n : nat) : (term313 x n) = (term313 x n).
Proof. exact (eq_refl (term313 x n)). Qed.
Lemma lem4777965 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term632 A f x n) = (term633 A f x n).
Proof. exact (MK_COMB (@lem4777964 x n) (@lem4777962 A f x n)). Qed.
Lemma lem4777966 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term634 A f x n) = (term632 A f x n).
Proof. exact (@lem17362 (Peano.lt x n) (term493 A f x n)). Qed.
Lemma lem4777967 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term634 A f x n) = (term633 A f x n).
Proof. exact (TRANS (@lem4777966 A f x n) (@lem4777965 A f x n)). Qed.
Lemma lem4777968 (P : nat -> Prop) : (term317 P) = (term318 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4777969 {A : Type'} (f : nat -> A) (x : nat) : (term635 A f x) = (term636 A f x).
Proof. exact (@lem4777968 (term509 A f x)). Qed.
Lemma lem4777970 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term637 A f x n) = (term507 A f x n).
Proof. exact (eq_refl (term637 A f x n)). Qed.
Lemma lem4777971 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4777972 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term638 A f x n) = (term634 A f x n).
Proof. exact (MK_COMB (@lem4777971) (@lem4777970 A f x n)). Qed.
Lemma lem4777973 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term638 A f x n) = (term633 A f x n).
Proof. exact (TRANS (@lem4777972 A f x n) (@lem4777967 A f x n)). Qed.
Lemma lem4777974 {A : Type'} (f : nat -> A) (x : nat) : (term639 A f x) = (term640 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4777973 A f x n)). Qed.
Lemma lem4777975 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4777976 {A : Type'} (f : nat -> A) (x : nat) : (term636 A f x) = (term641 A f x).
Proof. exact (MK_COMB (@lem4777975) (@lem4777974 A f x)). Qed.
Lemma lem4777977 {A : Type'} (f : nat -> A) (x : nat) : (term635 A f x) = (term641 A f x).
Proof. exact (TRANS (@lem4777969 A f x) (@lem4777976 A f x)). Qed.
Lemma lem4777978 (P : nat -> Prop) : (term317 P) = (term318 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4777979 {A : Type'} (f : nat -> A) : (term642 A f) = (term643 A f).
Proof. exact (@lem4777978 (term513 A f)). Qed.
Lemma lem4777980 {A : Type'} (f : nat -> A) (x : nat) : (term644 A f x) = (term511 A f x).
Proof. exact (eq_refl (term644 A f x)). Qed.
Lemma lem4777981 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4777982 {A : Type'} (f : nat -> A) (x : nat) : (term645 A f x) = (term635 A f x).
Proof. exact (MK_COMB (@lem4777981) (@lem4777980 A f x)). Qed.
Lemma lem4777983 {A : Type'} (f : nat -> A) (x : nat) : (term645 A f x) = (term641 A f x).
Proof. exact (TRANS (@lem4777982 A f x) (@lem4777977 A f x)). Qed.
Lemma lem4777984 {A : Type'} (f : nat -> A) : (term646 A f) = (term647 A f).
Proof. exact (fun_ext (fun x : nat => @lem4777983 A f x)). Qed.
Lemma lem4777985 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4777986 {A : Type'} (f : nat -> A) : (term643 A f) = (term648 A f).
Proof. exact (MK_COMB (@lem4777985) (@lem4777984 A f)). Qed.
Lemma lem4777987 {A : Type'} (f : nat -> A) : (term642 A f) = (term648 A f).
Proof. exact (TRANS (@lem4777979 A f) (@lem4777986 A f)). Qed.
Lemma lem4777988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4777989 {A : Type'} (f : nat -> A) : (term649 A f) = (term650 A f).
Proof. exact (MK_COMB (@lem4777988) (@lem4777954 A f)). Qed.
Lemma lem4777990 {A : Type'} (f : nat -> A) : (term651 A f) = (term652 A f).
Proof. exact (MK_COMB (@lem4777989 A f) (@lem4777987 A f)). Qed.
Lemma lem4777991 {A : Type'} (f : nat -> A) : (term592 A f) = (term651 A f).
Proof. exact (@lem17045 (term503 A f) (term515 A f)). Qed.
Lemma lem4777992 {A : Type'} (f : nat -> A) : (term592 A f) = (term652 A f).
Proof. exact (TRANS (@lem4777991 A f) (@lem4777990 A f)). Qed.
Lemma lem4777998 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term653 A P Q) = (term654 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4777999 (P : nat -> Prop) (Q : nat -> Prop) : (term655 P Q) = (term656 P Q).
Proof. exact (@lem4777998 nat P Q). Qed.
Lemma lem4778000 {A : Type'} (f : nat -> A) (x : nat) : (term657 A f x) = (term658 A f x).
Proof. exact (@lem4777999 (term659 A f x) (term660 A f x)). Qed.
Lemma lem4778001 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term661 A f x n) = (term612 A f n x).
Proof. exact (eq_refl (term661 A f x n)). Qed.
Lemma lem4778002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778003 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term662 A f x n) = (term614 A f n x).
Proof. exact (MK_COMB (@lem4778002) (@lem4778001 A f n x)). Qed.
Lemma lem4778004 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term663 A f x n) = (term608 A f n x).
Proof. exact (eq_refl (term663 A f x n)). Qed.
Lemma lem4778005 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term664 A f x n) = (term616 A f n x).
Proof. exact (MK_COMB (@lem4778003 A f n x) (@lem4778004 A f n x)). Qed.
Lemma lem4778006 {A : Type'} (f : nat -> A) (x : nat) : (term665 A f x) = (term623 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4778005 A f n x)). Qed.
Lemma lem4778007 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778008 {A : Type'} (f : nat -> A) (x : nat) : (term657 A f x) = (term624 A f x).
Proof. exact (MK_COMB (@lem4778007) (@lem4778006 A f x)). Qed.
Lemma lem4778009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4778010 {A : Type'} (f : nat -> A) (x : nat) : (term666 A f x) = (term667 A f x).
Proof. exact (MK_COMB (@lem4778009) (@lem4778008 A f x)). Qed.
Lemma lem4778011 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term661 A f x n) = (term612 A f n x).
Proof. exact (eq_refl (term661 A f x n)). Qed.
Lemma lem4778012 {A : Type'} (f : nat -> A) (x : nat) : (term668 A f x) = (term659 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4778011 A f n x)). Qed.
Lemma lem4778013 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778014 {A : Type'} (f : nat -> A) (x : nat) : (term669 A f x) = (term670 A f x).
Proof. exact (MK_COMB (@lem4778013) (@lem4778012 A f x)). Qed.
Lemma lem4778015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778016 {A : Type'} (f : nat -> A) (x : nat) : (term671 A f x) = (term672 A f x).
Proof. exact (MK_COMB (@lem4778015) (@lem4778014 A f x)). Qed.
Lemma lem4778017 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term663 A f x n) = (term608 A f n x).
Proof. exact (eq_refl (term663 A f x n)). Qed.
Lemma lem4778018 {A : Type'} (f : nat -> A) (x : nat) : (term673 A f x) = (term660 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4778017 A f n x)). Qed.
Lemma lem4778019 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778020 {A : Type'} (f : nat -> A) (x : nat) : (term674 A f x) = (term675 A f x).
Proof. exact (MK_COMB (@lem4778019) (@lem4778018 A f x)). Qed.
Lemma lem4778021 {A : Type'} (f : nat -> A) (x : nat) : (term658 A f x) = (term676 A f x).
Proof. exact (MK_COMB (@lem4778016 A f x) (@lem4778020 A f x)). Qed.
Lemma lem4778022 {A : Type'} (f : nat -> A) (x : nat) : ((term657 A f x) = (term658 A f x)) = ((term624 A f x) = (term676 A f x)).
Proof. exact (MK_COMB (@lem4778010 A f x) (@lem4778021 A f x)). Qed.
Lemma lem4778023 {A : Type'} (f : nat -> A) (x : nat) : (term624 A f x) = (term676 A f x).
Proof. exact (EQ_MP (@lem4778022 A f x) (@lem4778000 A f x)). Qed.
Lemma lem4778120 {A : Type'} (f : nat -> A) : (term630 A f) = (term677 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778023 A f x)). Qed.
Lemma lem4778121 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778122 {A : Type'} (f : nat -> A) : (term631 A f) = (term678 A f).
Proof. exact (MK_COMB (@lem4778121) (@lem4778120 A f)). Qed.
Lemma lem4778124 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term653 A P Q) = (term654 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4778125 (P : nat -> Prop) (Q : nat -> Prop) : (term655 P Q) = (term656 P Q).
Proof. exact (@lem4778124 nat P Q). Qed.
Lemma lem4778126 {A : Type'} (f : nat -> A) : (term679 A f) = (term680 A f).
Proof. exact (@lem4778125 (term681 A f) (term682 A f)). Qed.
Lemma lem4778127 {A : Type'} (f : nat -> A) (x : nat) : (term683 A f x) = (term670 A f x).
Proof. exact (eq_refl (term683 A f x)). Qed.
Lemma lem4778128 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778129 {A : Type'} (f : nat -> A) (x : nat) : (term684 A f x) = (term672 A f x).
Proof. exact (MK_COMB (@lem4778128) (@lem4778127 A f x)). Qed.
Lemma lem4778130 {A : Type'} (f : nat -> A) (x : nat) : (term685 A f x) = (term675 A f x).
Proof. exact (eq_refl (term685 A f x)). Qed.
Lemma lem4778131 {A : Type'} (f : nat -> A) (x : nat) : (term686 A f x) = (term676 A f x).
Proof. exact (MK_COMB (@lem4778129 A f x) (@lem4778130 A f x)). Qed.
Lemma lem4778132 {A : Type'} (f : nat -> A) : (term687 A f) = (term677 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778131 A f x)). Qed.
Lemma lem4778133 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778134 {A : Type'} (f : nat -> A) : (term679 A f) = (term678 A f).
Proof. exact (MK_COMB (@lem4778133) (@lem4778132 A f)). Qed.
Lemma lem4778135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4778136 {A : Type'} (f : nat -> A) : (term688 A f) = (term689 A f).
Proof. exact (MK_COMB (@lem4778135) (@lem4778134 A f)). Qed.
Lemma lem4778137 {A : Type'} (f : nat -> A) (x : nat) : (term683 A f x) = (term670 A f x).
Proof. exact (eq_refl (term683 A f x)). Qed.
Lemma lem4778138 {A : Type'} (f : nat -> A) : (term690 A f) = (term681 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778137 A f x)). Qed.
Lemma lem4778139 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778140 {A : Type'} (f : nat -> A) : (term691 A f) = (term692 A f).
Proof. exact (MK_COMB (@lem4778139) (@lem4778138 A f)). Qed.
Lemma lem4778141 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778142 {A : Type'} (f : nat -> A) : (term693 A f) = (term694 A f).
Proof. exact (MK_COMB (@lem4778141) (@lem4778140 A f)). Qed.
Lemma lem4778143 {A : Type'} (f : nat -> A) (x : nat) : (term685 A f x) = (term675 A f x).
Proof. exact (eq_refl (term685 A f x)). Qed.
Lemma lem4778144 {A : Type'} (f : nat -> A) : (term695 A f) = (term682 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778143 A f x)). Qed.
Lemma lem4778145 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778146 {A : Type'} (f : nat -> A) : (term696 A f) = (term697 A f).
Proof. exact (MK_COMB (@lem4778145) (@lem4778144 A f)). Qed.
Lemma lem4778147 {A : Type'} (f : nat -> A) : (term680 A f) = (term698 A f).
Proof. exact (MK_COMB (@lem4778142 A f) (@lem4778146 A f)). Qed.
Lemma lem4778148 {A : Type'} (f : nat -> A) : ((term679 A f) = (term680 A f)) = ((term678 A f) = (term698 A f)).
Proof. exact (MK_COMB (@lem4778136 A f) (@lem4778147 A f)). Qed.
Lemma lem4778149 {A : Type'} (f : nat -> A) : (term678 A f) = (term698 A f).
Proof. exact (EQ_MP (@lem4778148 A f) (@lem4778126 A f)). Qed.
Lemma lem4778254 {A : Type'} (f : nat -> A) : (term631 A f) = (term698 A f).
Proof. exact (TRANS (@lem4778122 A f) (@lem4778149 A f)). Qed.
Lemma lem4778255 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778256 {A : Type'} (f : nat -> A) : (term650 A f) = (term699 A f).
Proof. exact (MK_COMB (@lem4778255) (@lem4778254 A f)). Qed.
Lemma lem4778309 {A : Type'} (f : nat -> A) : (term648 A f) = (term648 A f).
Proof. exact (eq_refl (term648 A f)). Qed.
Lemma lem4778310 {A : Type'} (f : nat -> A) : (term652 A f) = (term700 A f).
Proof. exact (MK_COMB (@lem4778256 A f) (@lem4778309 A f)). Qed.
Lemma lem4778312 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term654 A P Q) = (term653 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4778313 (P : nat -> Prop) (Q : nat -> Prop) : (term656 P Q) = (term655 P Q).
Proof. exact (@lem4778312 nat P Q). Qed.
Lemma lem4778314 {A : Type'} (f : nat -> A) : (term680 A f) = (term679 A f).
Proof. exact (@lem4778313 (term681 A f) (term682 A f)). Qed.
Lemma lem4778315 {A : Type'} (f : nat -> A) (x : nat) : (term683 A f x) = (term670 A f x).
Proof. exact (eq_refl (term683 A f x)). Qed.
Lemma lem4778316 {A : Type'} (f : nat -> A) : (term690 A f) = (term681 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778315 A f x)). Qed.
Lemma lem4778317 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778318 {A : Type'} (f : nat -> A) : (term691 A f) = (term692 A f).
Proof. exact (MK_COMB (@lem4778317) (@lem4778316 A f)). Qed.
Lemma lem4778319 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778320 {A : Type'} (f : nat -> A) : (term693 A f) = (term694 A f).
Proof. exact (MK_COMB (@lem4778319) (@lem4778318 A f)). Qed.
Lemma lem4778321 {A : Type'} (f : nat -> A) (x : nat) : (term685 A f x) = (term675 A f x).
Proof. exact (eq_refl (term685 A f x)). Qed.
Lemma lem4778322 {A : Type'} (f : nat -> A) : (term695 A f) = (term682 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778321 A f x)). Qed.
Lemma lem4778323 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778324 {A : Type'} (f : nat -> A) : (term696 A f) = (term697 A f).
Proof. exact (MK_COMB (@lem4778323) (@lem4778322 A f)). Qed.
Lemma lem4778325 {A : Type'} (f : nat -> A) : (term680 A f) = (term698 A f).
Proof. exact (MK_COMB (@lem4778320 A f) (@lem4778324 A f)). Qed.
Lemma lem4778326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4778327 {A : Type'} (f : nat -> A) : (term701 A f) = (term702 A f).
Proof. exact (MK_COMB (@lem4778326) (@lem4778325 A f)). Qed.
Lemma lem4778328 {A : Type'} (f : nat -> A) (x : nat) : (term683 A f x) = (term670 A f x).
Proof. exact (eq_refl (term683 A f x)). Qed.
Lemma lem4778329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778330 {A : Type'} (f : nat -> A) (x : nat) : (term684 A f x) = (term672 A f x).
Proof. exact (MK_COMB (@lem4778329) (@lem4778328 A f x)). Qed.
Lemma lem4778331 {A : Type'} (f : nat -> A) (x : nat) : (term685 A f x) = (term675 A f x).
Proof. exact (eq_refl (term685 A f x)). Qed.
Lemma lem4778332 {A : Type'} (f : nat -> A) (x : nat) : (term686 A f x) = (term676 A f x).
Proof. exact (MK_COMB (@lem4778330 A f x) (@lem4778331 A f x)). Qed.
Lemma lem4778333 {A : Type'} (f : nat -> A) : (term687 A f) = (term677 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778332 A f x)). Qed.
Lemma lem4778334 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778335 {A : Type'} (f : nat -> A) : (term679 A f) = (term678 A f).
Proof. exact (MK_COMB (@lem4778334) (@lem4778333 A f)). Qed.
Lemma lem4778336 {A : Type'} (f : nat -> A) : ((term680 A f) = (term679 A f)) = ((term698 A f) = (term678 A f)).
Proof. exact (MK_COMB (@lem4778327 A f) (@lem4778335 A f)). Qed.
Lemma lem4778337 {A : Type'} (f : nat -> A) : (term698 A f) = (term678 A f).
Proof. exact (EQ_MP (@lem4778336 A f) (@lem4778314 A f)). Qed.
Lemma lem4778339 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term654 A P Q) = (term653 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4778340 (P : nat -> Prop) (Q : nat -> Prop) : (term656 P Q) = (term655 P Q).
Proof. exact (@lem4778339 nat P Q). Qed.
Lemma lem4778341 {A : Type'} (f : nat -> A) (x : nat) : (term658 A f x) = (term657 A f x).
Proof. exact (@lem4778340 (term659 A f x) (term660 A f x)). Qed.
Lemma lem4778342 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term661 A f x n) = (term612 A f n x).
Proof. exact (eq_refl (term661 A f x n)). Qed.
Lemma lem4778343 {A : Type'} (f : nat -> A) (x : nat) : (term668 A f x) = (term659 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4778342 A f n x)). Qed.
Lemma lem4778344 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778345 {A : Type'} (f : nat -> A) (x : nat) : (term669 A f x) = (term670 A f x).
Proof. exact (MK_COMB (@lem4778344) (@lem4778343 A f x)). Qed.
Lemma lem4778346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778347 {A : Type'} (f : nat -> A) (x : nat) : (term671 A f x) = (term672 A f x).
Proof. exact (MK_COMB (@lem4778346) (@lem4778345 A f x)). Qed.
Lemma lem4778348 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term663 A f x n) = (term608 A f n x).
Proof. exact (eq_refl (term663 A f x n)). Qed.
Lemma lem4778349 {A : Type'} (f : nat -> A) (x : nat) : (term673 A f x) = (term660 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4778348 A f n x)). Qed.
Lemma lem4778350 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778351 {A : Type'} (f : nat -> A) (x : nat) : (term674 A f x) = (term675 A f x).
Proof. exact (MK_COMB (@lem4778350) (@lem4778349 A f x)). Qed.
Lemma lem4778352 {A : Type'} (f : nat -> A) (x : nat) : (term658 A f x) = (term676 A f x).
Proof. exact (MK_COMB (@lem4778347 A f x) (@lem4778351 A f x)). Qed.
Lemma lem4778353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4778354 {A : Type'} (f : nat -> A) (x : nat) : (term703 A f x) = (term704 A f x).
Proof. exact (MK_COMB (@lem4778353) (@lem4778352 A f x)). Qed.
Lemma lem4778355 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term661 A f x n) = (term612 A f n x).
Proof. exact (eq_refl (term661 A f x n)). Qed.
Lemma lem4778356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778357 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term662 A f x n) = (term614 A f n x).
Proof. exact (MK_COMB (@lem4778356) (@lem4778355 A f n x)). Qed.
Lemma lem4778358 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term663 A f x n) = (term608 A f n x).
Proof. exact (eq_refl (term663 A f x n)). Qed.
Lemma lem4778359 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term664 A f x n) = (term616 A f n x).
Proof. exact (MK_COMB (@lem4778357 A f n x) (@lem4778358 A f n x)). Qed.
Lemma lem4778360 {A : Type'} (f : nat -> A) (x : nat) : (term665 A f x) = (term623 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4778359 A f n x)). Qed.
Lemma lem4778361 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778362 {A : Type'} (f : nat -> A) (x : nat) : (term657 A f x) = (term624 A f x).
Proof. exact (MK_COMB (@lem4778361) (@lem4778360 A f x)). Qed.
Lemma lem4778363 {A : Type'} (f : nat -> A) (x : nat) : ((term658 A f x) = (term657 A f x)) = ((term676 A f x) = (term624 A f x)).
Proof. exact (MK_COMB (@lem4778354 A f x) (@lem4778362 A f x)). Qed.
Lemma lem4778364 {A : Type'} (f : nat -> A) (x : nat) : (term676 A f x) = (term624 A f x).
Proof. exact (EQ_MP (@lem4778363 A f x) (@lem4778341 A f x)). Qed.
Lemma lem4778365 {A : Type'} (f : nat -> A) : (term677 A f) = (term630 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778364 A f x)). Qed.
Lemma lem4778366 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778367 {A : Type'} (f : nat -> A) : (term678 A f) = (term631 A f).
Proof. exact (MK_COMB (@lem4778366) (@lem4778365 A f)). Qed.
Lemma lem4778368 {A : Type'} (f : nat -> A) : (term698 A f) = (term631 A f).
Proof. exact (TRANS (@lem4778337 A f) (@lem4778367 A f)). Qed.
Lemma lem4778369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778370 {A : Type'} (f : nat -> A) : (term699 A f) = (term650 A f).
Proof. exact (MK_COMB (@lem4778369) (@lem4778368 A f)). Qed.
Lemma lem4778371 {A : Type'} (f : nat -> A) : (term648 A f) = (term648 A f).
Proof. exact (eq_refl (term648 A f)). Qed.
Lemma lem4778372 {A : Type'} (f : nat -> A) : (term700 A f) = (term652 A f).
Proof. exact (MK_COMB (@lem4778370 A f) (@lem4778371 A f)). Qed.
Lemma lem4778374 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term654 A P Q) = (term653 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4778375 (P : nat -> Prop) (Q : nat -> Prop) : (term656 P Q) = (term655 P Q).
Proof. exact (@lem4778374 nat P Q). Qed.
Lemma lem4778376 {A : Type'} (f : nat -> A) : (term705 A f) = (term706 A f).
Proof. exact (@lem4778375 (term630 A f) (term647 A f)). Qed.
Lemma lem4778377 {A : Type'} (f : nat -> A) (x : nat) : (term707 A f x) = (term624 A f x).
Proof. exact (eq_refl (term707 A f x)). Qed.
Lemma lem4778378 {A : Type'} (f : nat -> A) : (term708 A f) = (term630 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778377 A f x)). Qed.
Lemma lem4778379 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778380 {A : Type'} (f : nat -> A) : (term709 A f) = (term631 A f).
Proof. exact (MK_COMB (@lem4778379) (@lem4778378 A f)). Qed.
Lemma lem4778381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778382 {A : Type'} (f : nat -> A) : (term710 A f) = (term650 A f).
Proof. exact (MK_COMB (@lem4778381) (@lem4778380 A f)). Qed.
Lemma lem4778383 {A : Type'} (f : nat -> A) (x : nat) : (term711 A f x) = (term641 A f x).
Proof. exact (eq_refl (term711 A f x)). Qed.
Lemma lem4778384 {A : Type'} (f : nat -> A) : (term712 A f) = (term647 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778383 A f x)). Qed.
Lemma lem4778385 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778386 {A : Type'} (f : nat -> A) : (term713 A f) = (term648 A f).
Proof. exact (MK_COMB (@lem4778385) (@lem4778384 A f)). Qed.
Lemma lem4778387 {A : Type'} (f : nat -> A) : (term705 A f) = (term652 A f).
Proof. exact (MK_COMB (@lem4778382 A f) (@lem4778386 A f)). Qed.
Lemma lem4778388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4778389 {A : Type'} (f : nat -> A) : (term714 A f) = (term715 A f).
Proof. exact (MK_COMB (@lem4778388) (@lem4778387 A f)). Qed.
Lemma lem4778390 {A : Type'} (f : nat -> A) (x : nat) : (term707 A f x) = (term624 A f x).
Proof. exact (eq_refl (term707 A f x)). Qed.
Lemma lem4778391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778392 {A : Type'} (f : nat -> A) (x : nat) : (term716 A f x) = (term717 A f x).
Proof. exact (MK_COMB (@lem4778391) (@lem4778390 A f x)). Qed.
Lemma lem4778393 {A : Type'} (f : nat -> A) (x : nat) : (term711 A f x) = (term641 A f x).
Proof. exact (eq_refl (term711 A f x)). Qed.
Lemma lem4778394 {A : Type'} (f : nat -> A) (x : nat) : (term718 A f x) = (term719 A f x).
Proof. exact (MK_COMB (@lem4778392 A f x) (@lem4778393 A f x)). Qed.
Lemma lem4778395 {A : Type'} (f : nat -> A) : (term720 A f) = (term721 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778394 A f x)). Qed.
Lemma lem4778396 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778397 {A : Type'} (f : nat -> A) : (term706 A f) = (term722 A f).
Proof. exact (MK_COMB (@lem4778396) (@lem4778395 A f)). Qed.
Lemma lem4778398 {A : Type'} (f : nat -> A) : ((term705 A f) = (term706 A f)) = ((term652 A f) = (term722 A f)).
Proof. exact (MK_COMB (@lem4778389 A f) (@lem4778397 A f)). Qed.
Lemma lem4778399 {A : Type'} (f : nat -> A) : (term652 A f) = (term722 A f).
Proof. exact (EQ_MP (@lem4778398 A f) (@lem4778376 A f)). Qed.
Lemma lem4778401 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term654 A P Q) = (term653 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4778402 (P : nat -> Prop) (Q : nat -> Prop) : (term656 P Q) = (term655 P Q).
Proof. exact (@lem4778401 nat P Q). Qed.
Lemma lem4778403 {A : Type'} (f : nat -> A) (x : nat) : (term723 A f x) = (term724 A f x).
Proof. exact (@lem4778402 (term623 A f x) (term640 A f x)). Qed.
Lemma lem4778404 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term725 A f x n) = (term616 A f n x).
Proof. exact (eq_refl (term725 A f x n)). Qed.
Lemma lem4778405 {A : Type'} (f : nat -> A) (x : nat) : (term726 A f x) = (term623 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4778404 A f n x)). Qed.
Lemma lem4778406 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778407 {A : Type'} (f : nat -> A) (x : nat) : (term727 A f x) = (term624 A f x).
Proof. exact (MK_COMB (@lem4778406) (@lem4778405 A f x)). Qed.
Lemma lem4778408 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778409 {A : Type'} (f : nat -> A) (x : nat) : (term728 A f x) = (term717 A f x).
Proof. exact (MK_COMB (@lem4778408) (@lem4778407 A f x)). Qed.
Lemma lem4778410 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term729 A f x n) = (term633 A f x n).
Proof. exact (eq_refl (term729 A f x n)). Qed.
Lemma lem4778411 {A : Type'} (f : nat -> A) (x : nat) : (term730 A f x) = (term640 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4778410 A f x n)). Qed.
Lemma lem4778412 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778413 {A : Type'} (f : nat -> A) (x : nat) : (term731 A f x) = (term641 A f x).
Proof. exact (MK_COMB (@lem4778412) (@lem4778411 A f x)). Qed.
Lemma lem4778414 {A : Type'} (f : nat -> A) (x : nat) : (term723 A f x) = (term719 A f x).
Proof. exact (MK_COMB (@lem4778409 A f x) (@lem4778413 A f x)). Qed.
Lemma lem4778415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4778416 {A : Type'} (f : nat -> A) (x : nat) : (term732 A f x) = (term733 A f x).
Proof. exact (MK_COMB (@lem4778415) (@lem4778414 A f x)). Qed.
Lemma lem4778417 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term725 A f x n) = (term616 A f n x).
Proof. exact (eq_refl (term725 A f x n)). Qed.
Lemma lem4778418 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4778419 {A : Type'} (f : nat -> A) (n : nat) (x : nat) : (term734 A f x n) = (term735 A f n x).
Proof. exact (MK_COMB (@lem4778418) (@lem4778417 A f n x)). Qed.
Lemma lem4778420 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term729 A f x n) = (term633 A f x n).
Proof. exact (eq_refl (term729 A f x n)). Qed.
Lemma lem4778421 {A : Type'} (f : nat -> A) (x : nat) (n : nat) : (term736 A f x n) = (term737 A f x n).
Proof. exact (MK_COMB (@lem4778419 A f n x) (@lem4778420 A f x n)). Qed.
Lemma lem4778422 {A : Type'} (f : nat -> A) (x : nat) : (term738 A f x) = (term739 A f x).
Proof. exact (fun_ext (fun n : nat => @lem4778421 A f x n)). Qed.
Lemma lem4778423 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778424 {A : Type'} (f : nat -> A) (x : nat) : (term724 A f x) = (term740 A f x).
Proof. exact (MK_COMB (@lem4778423) (@lem4778422 A f x)). Qed.
Lemma lem4778425 {A : Type'} (f : nat -> A) (x : nat) : ((term723 A f x) = (term724 A f x)) = ((term719 A f x) = (term740 A f x)).
Proof. exact (MK_COMB (@lem4778416 A f x) (@lem4778424 A f x)). Qed.
Lemma lem4778426 {A : Type'} (f : nat -> A) (x : nat) : (term719 A f x) = (term740 A f x).
Proof. exact (EQ_MP (@lem4778425 A f x) (@lem4778403 A f x)). Qed.
Lemma lem4778427 {A : Type'} (f : nat -> A) : (term721 A f) = (term741 A f).
Proof. exact (fun_ext (fun x : nat => @lem4778426 A f x)). Qed.
Lemma lem4778428 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4778429 {A : Type'} (f : nat -> A) : (term722 A f) = (term742 A f).
Proof. exact (MK_COMB (@lem4778428) (@lem4778427 A f)). Qed.
Lemma lem4778430 {A : Type'} (f : nat -> A) : (term652 A f) = (term742 A f).
Proof. exact (TRANS (@lem4778399 A f) (@lem4778429 A f)). Qed.
Lemma lem4778431 {A : Type'} (f : nat -> A) : (term700 A f) = (term742 A f).
Proof. exact (TRANS (@lem4778372 A f) (@lem4778430 A f)). Qed.
Lemma lem4778432 {A : Type'} (f : nat -> A) : (term652 A f) = (term742 A f).
Proof. exact (TRANS (@lem4778310 A f) (@lem4778431 A f)). Qed.
Lemma lem4778433 {A : Type'} (f : nat -> A) : (term592 A f) = (term742 A f).
Proof. exact (TRANS (@lem4777992 A f) (@lem4778432 A f)). Qed.
Lemma lem4778434 {A : Type'} (f : nat -> A) (h1 : term592 A f) : term742 A f.
Proof. exact (EQ_MP (@lem4778433 A f) (@lem4777810 A f h1)). Qed.
Lemma lem4778435 {A : Type'} (f : nat -> A) (x : nat) (h1 : term740 A f x) : term740 A f x.
Proof. exact (h1). Qed.
Lemma lem4778439 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (@INFINITE A s).
Proof. exact (eq_refl (@INFINITE A s)). Qed.
Lemma lem4778460 {A : Type'} (m : nat) (f : nat -> A) (n : nat) : (term593 A m f n) = (term593 A m f n).
Proof. exact (eq_refl (term593 A m f n)). Qed.
Lemma lem4778461 {A : Type'} (f : nat -> A) (n : nat) : (term595 A f n) = (term595 A f n).
Proof. exact (fun_ext (fun m : nat => @lem4778460 A m f n)). Qed.
Lemma lem4778462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4778463 {A : Type'} (f : nat -> A) (n : nat) : (term596 A f n) = (term596 A f n).
Proof. exact (MK_COMB (@lem4778462) (@lem4778461 A f n)). Qed.
Lemma lem4778464 {A : Type'} (f : nat -> A) : (term597 A f) = (term597 A f).
Proof. exact (fun_ext (fun n : nat => @lem4778463 A f n)). Qed.
Lemma lem4778465 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4778466 {A : Type'} (f : nat -> A) : (term598 A f) = (term598 A f).
Proof. exact (MK_COMB (@lem4778465) (@lem4778464 A f)). Qed.
Lemma lem4778473 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4778474 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4778473 A Prop f x). Qed.
Lemma lem4778476 {A : Type'} (s : A -> Prop) (f : nat -> A) (n : nat) : (term535 A s f n) = (term743 A s f n).
Proof. exact (@lem4778474 A s (f n)). Qed.
Lemma lem4778477 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term559 A s f) = (term744 A s f).
Proof. exact (fun_ext (fun n : nat => @lem4778476 A s f n)). Qed.
Lemma lem4778478 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4778479 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term570 A s f) = (term745 A s f).
Proof. exact (MK_COMB (@lem4778478) (@lem4778477 A s f)). Qed.
Lemma lem4778480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4778481 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term572 A s f) = (term746 A s f).
Proof. exact (MK_COMB (@lem4778480) (@lem4778479 A s f)). Qed.
Lemma lem4778482 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term599 A s f) = (term747 A s f).
Proof. exact (MK_COMB (@lem4778481 A s f) (@lem4778466 A f)). Qed.
Lemma lem4778483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4778484 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term600 A s f) = (term748 A s f).
Proof. exact (MK_COMB (@lem4778483) (@lem4778482 A s f)). Qed.
Lemma lem4778485 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term601 A f s) = (term749 A f s).
Proof. exact (MK_COMB (@lem4778484 A s f) (@lem4778439 A s)). Qed.
Lemma lem4778486 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term749 A f s.
Proof. exact (EQ_MP (@lem4778485 A f s) (@lem4777895 A f s h1)). Qed.
Lemma lem4778602 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term737 A f x n) : term737 A f x n.
Proof. exact (h1). Qed.
Lemma lem4778604 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term747 A s f.
Proof. exact (proj1 (@lem4778486 A f s h1)). Qed.
Lemma lem4778605 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term598 A f.
Proof. exact (proj2 (@lem4778604 A f s h1)). Qed.
Lemma lem4778607 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term616 A f n x) : term616 A f n x.
Proof. exact (h1). Qed.
Lemma lem4778608 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term633 A f x n) : term633 A f x n.
Proof. exact (h1). Qed.
Lemma lem4778609 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : term612 A f n x.
Proof. exact (h1). Qed.
Lemma lem4778610 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : term608 A f n x.
Proof. exact (h1). Qed.
Lemma lem4778611 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : term603 A f n x.
Proof. exact (proj2 (@lem4778609 A f n x h1)). Qed.
Lemma lem4778612 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : term604 A f x n.
Proof. exact (proj1 (@lem4778609 A f n x h1)). Qed.
Lemma lem4778617 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : term604 A f n x.
Proof. exact (proj2 (@lem4778610 A f n x h1)). Qed.
Lemma lem4778618 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : term603 A f x n.
Proof. exact (proj1 (@lem4778610 A f n x h1)). Qed.
Lemma lem4778623 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term633 A f x n) : term603 A f x n.
Proof. exact (proj2 (@lem4778608 A f x n h1)). Qed.
Lemma lem4778665 {A : Type'} (x : nat) (f : nat -> A) (n : nat) (h1 : term594 A x f n) : term594 A x f n.
Proof. exact (h1). Qed.
Lemma lem4778704 (x : nat) (n : nat) (h1 : x = n) : x = n.
Proof. exact (h1). Qed.
Lemma lem4778743 {A : Type'} (n : nat) (f : nat -> A) (x : nat) (h1 : term594 A n f x) : term594 A n f x.
Proof. exact (h1). Qed.
Lemma lem4778782 (n : nat) (x : nat) (h1 : n = x) : n = x.
Proof. exact (h1). Qed.
Lemma lem4778801 {A : Type'} (m : nat) (f : nat -> A) (n : nat) : (term593 A m f n) = (term593 A m f n).
Proof. exact (eq_refl (term593 A m f n)). Qed.
Lemma lem4778802 {A : Type'} (f : nat -> A) (n : nat) : (term595 A f n) = (term595 A f n).
Proof. exact (fun_ext (fun m : nat => @lem4778801 A m f n)). Qed.
Lemma lem4778803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4778804 {A : Type'} (f : nat -> A) (n : nat) : (term596 A f n) = (term596 A f n).
Proof. exact (MK_COMB (@lem4778803) (@lem4778802 A f n)). Qed.
Lemma lem4778805 {A : Type'} (f : nat -> A) : (term597 A f) = (term597 A f).
Proof. exact (fun_ext (fun n : nat => @lem4778804 A f n)). Qed.
Lemma lem4778806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4778808 {A : Type'} (f : nat -> A) : (term598 A f) = (term598 A f).
Proof. exact (MK_COMB (@lem4778806) (@lem4778805 A f)). Qed.
Lemma lem4778809 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term598 A f.
Proof. exact (EQ_MP (@lem4778808 A f) (@lem4778605 A f s h1)). Qed.
Lemma lem4778861 {A : Type'} (_58919 : nat) (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term750 A f _58919.
Proof. exact (@lem4778809 A f s h1 _58919). Qed.
Lemma lem4778862 {A : Type'} (f : nat -> A) (_58919 : nat) : (term750 A f _58919) = (term596 A f _58919).
Proof. exact (eq_refl (term750 A f _58919)). Qed.
Lemma lem4778863 {A : Type'} (_58919 : nat) (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term596 A f _58919.
Proof. exact (EQ_MP (@lem4778862 A f _58919) (@lem4778861 A _58919 f s h1)). Qed.
Lemma lem4778864 {A : Type'} (_58919 : nat) (_58920 : nat) (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term751 A f _58919 _58920.
Proof. exact (@lem4778863 A _58919 f s h1 _58920). Qed.
Lemma lem4778865 {A : Type'} (_58920 : nat) (f : nat -> A) (_58919 : nat) : (term751 A f _58919 _58920) = (term593 A _58920 f _58919).
Proof. exact (eq_refl (term751 A f _58919 _58920)). Qed.
Lemma lem4778882 {A : Type'} (x : nat) (f : nat -> A) (n : nat) (h1 : term594 A x f n) : term594 A x f n.
Proof. exact (h1). Qed.
Lemma lem4778896 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : term752 n x.
Proof. exact (proj2 (@lem4778611 A f n x h1)). Qed.
Lemma lem4778898 (x : nat) (n : nat) (h1 : x = n) : x = n.
Proof. exact (h1). Qed.
Lemma lem4778914 {A : Type'} (n : nat) (f : nat -> A) (x : nat) (h1 : term594 A n f x) : term594 A n f x.
Proof. exact (h1). Qed.
Lemma lem4778928 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : term752 x n.
Proof. exact (proj2 (@lem4778618 A f n x h1)). Qed.
Lemma lem4778930 (n : nat) (x : nat) (h1 : n = x) : n = x.
Proof. exact (h1). Qed.
Lemma lem4778940 {A : Type'} (_58920 : nat) (_58919 : nat) (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term593 A _58920 f _58919.
Proof. exact (EQ_MP (@lem4778865 A _58920 f _58919) (@lem4778864 A _58919 _58920 f s h1)). Qed.
Lemma lem4779016 (n : nat) : (term753 n) = (term753 n).
Proof. exact (eq_refl (term753 n)). Qed.
Lemma lem4779017 (x : nat) (n : nat) (h1 : x = n) : (term754 n x) = (term755 n).
Proof. exact (MK_COMB (@lem4779016 n) (@lem4778898 x n h1)). Qed.
Lemma lem4779018 (n : nat) : (term755 n) = (term756 n).
Proof. exact (eq_refl (term755 n)). Qed.
Lemma lem4779019 (n : nat) (x : nat) : (term757 n x) = (term757 n x).
Proof. exact (eq_refl (term757 n x)). Qed.
Lemma lem4779020 (x : nat) (n : nat) : ((term754 n x) = (term755 n)) = ((term754 n x) = (term756 n)).
Proof. exact (MK_COMB (@lem4779019 n x) (@lem4779018 n)). Qed.
Lemma lem4779021 (n : nat) (x : nat) : (term754 n x) = (term752 n x).
Proof. exact (eq_refl (term754 n x)). Qed.
Lemma lem4779022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4779023 (n : nat) (x : nat) : (term757 n x) = (term758 n x).
Proof. exact (MK_COMB (@lem4779022) (@lem4779021 n x)). Qed.
Lemma lem4779024 (n : nat) : (term756 n) = (term756 n).
Proof. exact (eq_refl (term756 n)). Qed.
Lemma lem4779025 (x : nat) (n : nat) : ((term754 n x) = (term756 n)) = ((term752 n x) = (term756 n)).
Proof. exact (MK_COMB (@lem4779023 n x) (@lem4779024 n)). Qed.
Lemma lem4779026 (x : nat) (n : nat) : ((term754 n x) = (term755 n)) = ((term752 n x) = (term756 n)).
Proof. exact (TRANS (@lem4779020 x n) (@lem4779025 x n)). Qed.
Lemma lem4779027 (x : nat) (n : nat) (h1 : x = n) : (term752 n x) = (term756 n).
Proof. exact (EQ_MP (@lem4779026 x n) (@lem4779017 x n h1)). Qed.
Lemma lem4779028 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : term756 n.
Proof. exact (EQ_MP (@lem4779027 x n h2) (@lem4778896 A f n x h1)). Qed.
Lemma lem4779098 (x : nat) : (term753 x) = (term753 x).
Proof. exact (eq_refl (term753 x)). Qed.
Lemma lem4779099 (n : nat) (x : nat) (h1 : n = x) : (term754 x n) = (term755 x).
Proof. exact (MK_COMB (@lem4779098 x) (@lem4778930 n x h1)). Qed.
Lemma lem4779100 (x : nat) : (term755 x) = (term756 x).
Proof. exact (eq_refl (term755 x)). Qed.
Lemma lem4779101 (x : nat) (n : nat) : (term757 x n) = (term757 x n).
Proof. exact (eq_refl (term757 x n)). Qed.
Lemma lem4779102 (n : nat) (x : nat) : ((term754 x n) = (term755 x)) = ((term754 x n) = (term756 x)).
Proof. exact (MK_COMB (@lem4779101 x n) (@lem4779100 x)). Qed.
Lemma lem4779103 (x : nat) (n : nat) : (term754 x n) = (term752 x n).
Proof. exact (eq_refl (term754 x n)). Qed.
Lemma lem4779104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4779105 (x : nat) (n : nat) : (term757 x n) = (term758 x n).
Proof. exact (MK_COMB (@lem4779104) (@lem4779103 x n)). Qed.
Lemma lem4779106 (x : nat) : (term756 x) = (term756 x).
Proof. exact (eq_refl (term756 x)). Qed.
Lemma lem4779107 (n : nat) (x : nat) : ((term754 x n) = (term756 x)) = ((term752 x n) = (term756 x)).
Proof. exact (MK_COMB (@lem4779105 x n) (@lem4779106 x)). Qed.
Lemma lem4779108 (n : nat) (x : nat) : ((term754 x n) = (term755 x)) = ((term752 x n) = (term756 x)).
Proof. exact (TRANS (@lem4779102 n x) (@lem4779107 n x)). Qed.
Lemma lem4779109 (n : nat) (x : nat) (h1 : n = x) : (term752 x n) = (term756 x).
Proof. exact (EQ_MP (@lem4779108 n x) (@lem4779099 n x h1)). Qed.
Lemma lem4779110 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : term756 x.
Proof. exact (EQ_MP (@lem4779109 n x h2) (@lem4778928 A f n x h1)). Qed.
Lemma lem4779170 {A : Type'} (x : A) (y : A) (z : A) : term391 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem4779176 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : (f n) = (f x).
Proof. exact (proj1 (@lem4778611 A f n x h1)). Qed.
Lemma lem4779177 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : term759 A n f x.
Proof. exact (fun h0 : term594 A n f x => @lem4779176 A f n x h1). Qed.
Lemma lem4779179 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779180 {A : Type'} (n : nat) (f : nat -> A) (x : nat) : (term759 A n f x) = ((f n) = (f x)).
Proof. exact (@lem4779179 ((f n) = (f x))). Qed.
Lemma lem4779181 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : (f n) = (f x).
Proof. exact (EQ_MP (@lem4779180 A n f x) (@lem4779177 A f n x h1)). Qed.
Lemma lem4779183 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4779184 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4779183 A x). Qed.
Lemma lem4779185 {A : Type'} (f : nat -> A) (n : nat) : (f n) = (f n).
Proof. exact (@lem4779184 A (f n)). Qed.
Lemma lem4779186 {A : Type'} (f : nat -> A) (n : nat) : term760 A f n.
Proof. exact (fun h0 : term761 A f n => @lem4779185 A f n). Qed.
Lemma lem4779188 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779189 {A : Type'} (f : nat -> A) (n : nat) : (term760 A f n) = ((f n) = (f n)).
Proof. exact (@lem4779188 ((f n) = (f n))). Qed.
Lemma lem4779190 {A : Type'} (f : nat -> A) (n : nat) : (f n) = (f n).
Proof. exact (EQ_MP (@lem4779189 A f n) (@lem4779186 A f n)). Qed.
Lemma lem4779208 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4779209 {A : Type'} (y : A) (x : A) (z : A) : (term407 A x y z) = (term408 A y x z).
Proof. exact (@lem4779208 (y = z) (term409 A x z)). Qed.
Lemma lem4779219 {A : Type'} (x : A) (y : A) : (term410 A x y) = (term410 A x y).
Proof. exact (eq_refl (term410 A x y)). Qed.
Lemma lem4779220 {A : Type'} (y : A) (x : A) (z : A) : (term391 A x y z) = (term411 A y x z).
Proof. exact (MK_COMB (@lem4779219 A x y) (@lem4779209 A y x z)). Qed.
Lemma lem4779224 (q : Prop) (p : Prop) (r : Prop) : (term412 p q r) = (term412 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4779225 {A : Type'} (y : A) (x : A) (z : A) : (term411 A y x z) = (term413 A y x z).
Proof. exact (@lem4779224 (y = z) (term409 A x y) (term409 A x z)). Qed.
Lemma lem4779247 {A : Type'} (y : A) (x : A) (z : A) : (term391 A x y z) = (term413 A y x z).
Proof. exact (TRANS (@lem4779220 A y x z) (@lem4779225 A y x z)). Qed.
Lemma lem4779248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4779249 {A : Type'} (y : A) (x : A) (z : A) : (term414 A x y z) = (term415 A y x z).
Proof. exact (MK_COMB (@lem4779248) (@lem4779247 A y x z)). Qed.
Lemma lem4779271 {A : Type'} (y : A) (x : A) (z : A) : (term413 A y x z) = (term413 A y x z).
Proof. exact (eq_refl (term413 A y x z)). Qed.
Lemma lem4779272 {A : Type'} (y : A) (x : A) (z : A) : ((term391 A x y z) = (term413 A y x z)) = ((term413 A y x z) = (term413 A y x z)).
Proof. exact (MK_COMB (@lem4779249 A y x z) (@lem4779271 A y x z)). Qed.
Lemma lem4779274 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4779275 (x : Prop) : (x = x) = True.
Proof. exact (@lem4779274 Prop x). Qed.
Lemma lem4779276 {A : Type'} (y : A) (x : A) (z : A) : ((term413 A y x z) = (term413 A y x z)) = True.
Proof. exact (@lem4779275 (term413 A y x z)). Qed.
Lemma lem4779277 {A : Type'} (y : A) (x : A) (z : A) : ((term391 A x y z) = (term413 A y x z)) = True.
Proof. exact (TRANS (@lem4779272 A y x z) (@lem4779276 A y x z)). Qed.
Lemma lem4779278 {A : Type'} (y : A) (x : A) (z : A) : True = ((term391 A x y z) = (term413 A y x z)).
Proof. exact (SYM (@lem4779277 A y x z)). Qed.
Lemma lem4779279 {A : Type'} (y : A) (x : A) (z : A) : (term391 A x y z) = (term413 A y x z).
Proof. exact (EQ_MP (@lem4779278 A y x z) (@lem0)). Qed.
Lemma lem4779280 {A : Type'} (y : A) (x : A) (z : A) : term413 A y x z.
Proof. exact (EQ_MP (@lem4779279 A y x z) (@lem4779170 A x y z)). Qed.
Lemma lem4779282 (b : Prop) (a : Prop) : (a \/ b) = (term397 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4779283 {A : Type'} (x : A) (y : A) (z : A) : (term413 A y x z) = (term416 A x y z).
Proof. exact (@lem4779282 (term417 A y x z) (y = z)). Qed.
Lemma lem4779285 (a : Prop) (b : Prop) : (term418 a b) = (term419 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4779286 {A : Type'} (y : A) (x : A) (z : A) : (term420 A y x z) = (term421 A y x z).
Proof. exact (@lem4779285 (term409 A x y) (term409 A x z)). Qed.
Lemma lem4779288 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4779289 {A : Type'} (x : A) (y : A) : (term422 A x y) = (x = y).
Proof. exact (@lem4779288 (x = y)). Qed.
Lemma lem4779290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4779291 {A : Type'} (x : A) (y : A) : (term423 A x y) = (term424 A x y).
Proof. exact (MK_COMB (@lem4779290) (@lem4779289 A x y)). Qed.
Lemma lem4779293 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4779294 {A : Type'} (x : A) (z : A) : (term422 A x z) = (x = z).
Proof. exact (@lem4779293 (x = z)). Qed.
Lemma lem4779295 {A : Type'} (y : A) (x : A) (z : A) : (term421 A y x z) = (term425 A y x z).
Proof. exact (MK_COMB (@lem4779291 A x y) (@lem4779294 A x z)). Qed.
Lemma lem4779296 {A : Type'} (y : A) (x : A) (z : A) : (term420 A y x z) = (term425 A y x z).
Proof. exact (TRANS (@lem4779286 A y x z) (@lem4779295 A y x z)). Qed.
Lemma lem4779297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4779298 {A : Type'} (y : A) (x : A) (z : A) : (term426 A y x z) = (term427 A y x z).
Proof. exact (MK_COMB (@lem4779297) (@lem4779296 A y x z)). Qed.
Lemma lem4779299 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4779300 {A : Type'} (x : A) (y : A) (z : A) : (term416 A x y z) = (term428 A x y z).
Proof. exact (MK_COMB (@lem4779298 A y x z) (@lem4779299 A y z)). Qed.
Lemma lem4779301 {A : Type'} (x : A) (y : A) (z : A) : (term413 A y x z) = (term428 A x y z).
Proof. exact (TRANS (@lem4779283 A x y z) (@lem4779300 A x y z)). Qed.
Lemma lem4779303 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : term762 A x f n.
Proof. exact (conj (@lem4779181 A f n x h1) (@lem4779190 A f n)). Qed.
Lemma lem4779305 {A : Type'} (x : A) (y : A) (z : A) : term428 A x y z.
Proof. exact (EQ_MP (@lem4779301 A x y z) (@lem4779280 A y x z)). Qed.
Lemma lem4779306 {A : Type'} (x : A) (y : A) (z : A) : term428 A x y z.
Proof. exact (@lem4779305 A x y z). Qed.
Lemma lem4779307 {A : Type'} (x : nat) (f : nat -> A) (n : nat) : term763 A x f n.
Proof. exact (@lem4779306 A (f n) (f x) (f n)). Qed.
Lemma lem4779310 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : (f x) = (f n).
Proof. exact (@lem4779307 A x f n (@lem4779303 A f n x h1)). Qed.
Lemma lem4779311 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : term759 A x f n.
Proof. exact (fun h0 : term594 A x f n => @lem4779310 A f n x h1). Qed.
Lemma lem4779313 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779314 {A : Type'} (x : nat) (f : nat -> A) (n : nat) : (term759 A x f n) = ((f x) = (f n)).
Proof. exact (@lem4779313 ((f x) = (f n))). Qed.
Lemma lem4779315 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : (f x) = (f n).
Proof. exact (EQ_MP (@lem4779314 A x f n) (@lem4779311 A f n x h1)). Qed.
Lemma lem4779318 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4779320 {A : Type'} (x : nat) (f : nat -> A) (n : nat) : (term594 A x f n) = (term764 A x f n).
Proof. exact (@lem4779318 ((f x) = (f n))). Qed.
Lemma lem4779323 {A : Type'} (x : nat) (f : nat -> A) (n : nat) (h1 : term594 A x f n) : term764 A x f n.
Proof. exact (EQ_MP (@lem4779320 A x f n) (@lem4778882 A x f n h1)). Qed.
Lemma lem4779326 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A x f n) (h2 : term612 A f n x) : False.
Proof. exact (@lem4779323 A x f n h1 (@lem4779315 A f n x h2)). Qed.
Lemma lem4779327 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A x f n) (h2 : term612 A f n x) : term445.
Proof. exact (fun h0 : ~ False => @lem4779326 A f n x h1 h2). Qed.
Lemma lem4779329 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779330 : term445 = False.
Proof. exact (@lem4779329 False). Qed.
Lemma lem4779331 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A x f n) (h2 : term612 A f n x) : False.
Proof. exact (EQ_MP (@lem4779330) (@lem4779327 A f n x h1 h2)). Qed.
Lemma lem4779397 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4779398 (n : nat) : n = n.
Proof. exact (@lem4779397 n). Qed.
Lemma lem4779399 (n : nat) : term765 n.
Proof. exact (fun h0 : term756 n => @lem4779398 n). Qed.
Lemma lem4779401 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779402 (n : nat) : (term765 n) = (n = n).
Proof. exact (@lem4779401 (n = n)). Qed.
Lemma lem4779403 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem4779402 n) (@lem4779399 n)). Qed.
Lemma lem4779406 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4779408 (n : nat) : (term756 n) = (term766 n).
Proof. exact (@lem4779406 (n = n)). Qed.
Lemma lem4779411 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : term766 n.
Proof. exact (EQ_MP (@lem4779408 n) (@lem4779028 A f x n h1 h2)). Qed.
Lemma lem4779414 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : False.
Proof. exact (@lem4779411 A f x n h1 h2 (@lem4779403 n)). Qed.
Lemma lem4779415 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : term445.
Proof. exact (fun h0 : ~ False => @lem4779414 A f x n h1 h2). Qed.
Lemma lem4779417 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779418 : term445 = False.
Proof. exact (@lem4779417 False). Qed.
Lemma lem4779479 {A : Type'} (x : A) (y : A) (z : A) : term391 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem4779485 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : (f x) = (f n).
Proof. exact (proj1 (@lem4778618 A f n x h1)). Qed.
Lemma lem4779486 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : term759 A x f n.
Proof. exact (fun h0 : term594 A x f n => @lem4779485 A f n x h1). Qed.
Lemma lem4779488 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779489 {A : Type'} (x : nat) (f : nat -> A) (n : nat) : (term759 A x f n) = ((f x) = (f n)).
Proof. exact (@lem4779488 ((f x) = (f n))). Qed.
Lemma lem4779490 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : (f x) = (f n).
Proof. exact (EQ_MP (@lem4779489 A x f n) (@lem4779486 A f n x h1)). Qed.
Lemma lem4779492 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4779493 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4779492 A x). Qed.
Lemma lem4779494 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (f x).
Proof. exact (@lem4779493 A (f x)). Qed.
Lemma lem4779495 {A : Type'} (f : nat -> A) (x : nat) : term760 A f x.
Proof. exact (fun h0 : term761 A f x => @lem4779494 A f x). Qed.
Lemma lem4779497 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779498 {A : Type'} (f : nat -> A) (x : nat) : (term760 A f x) = ((f x) = (f x)).
Proof. exact (@lem4779497 ((f x) = (f x))). Qed.
Lemma lem4779499 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (f x).
Proof. exact (EQ_MP (@lem4779498 A f x) (@lem4779495 A f x)). Qed.
Lemma lem4779517 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4779518 {A : Type'} (y : A) (x : A) (z : A) : (term407 A x y z) = (term408 A y x z).
Proof. exact (@lem4779517 (y = z) (term409 A x z)). Qed.
Lemma lem4779528 {A : Type'} (x : A) (y : A) : (term410 A x y) = (term410 A x y).
Proof. exact (eq_refl (term410 A x y)). Qed.
Lemma lem4779529 {A : Type'} (y : A) (x : A) (z : A) : (term391 A x y z) = (term411 A y x z).
Proof. exact (MK_COMB (@lem4779528 A x y) (@lem4779518 A y x z)). Qed.
Lemma lem4779533 (q : Prop) (p : Prop) (r : Prop) : (term412 p q r) = (term412 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4779534 {A : Type'} (y : A) (x : A) (z : A) : (term411 A y x z) = (term413 A y x z).
Proof. exact (@lem4779533 (y = z) (term409 A x y) (term409 A x z)). Qed.
Lemma lem4779556 {A : Type'} (y : A) (x : A) (z : A) : (term391 A x y z) = (term413 A y x z).
Proof. exact (TRANS (@lem4779529 A y x z) (@lem4779534 A y x z)). Qed.
Lemma lem4779557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4779558 {A : Type'} (y : A) (x : A) (z : A) : (term414 A x y z) = (term415 A y x z).
Proof. exact (MK_COMB (@lem4779557) (@lem4779556 A y x z)). Qed.
Lemma lem4779580 {A : Type'} (y : A) (x : A) (z : A) : (term413 A y x z) = (term413 A y x z).
Proof. exact (eq_refl (term413 A y x z)). Qed.
Lemma lem4779581 {A : Type'} (y : A) (x : A) (z : A) : ((term391 A x y z) = (term413 A y x z)) = ((term413 A y x z) = (term413 A y x z)).
Proof. exact (MK_COMB (@lem4779558 A y x z) (@lem4779580 A y x z)). Qed.
Lemma lem4779583 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4779584 (x : Prop) : (x = x) = True.
Proof. exact (@lem4779583 Prop x). Qed.
Lemma lem4779585 {A : Type'} (y : A) (x : A) (z : A) : ((term413 A y x z) = (term413 A y x z)) = True.
Proof. exact (@lem4779584 (term413 A y x z)). Qed.
Lemma lem4779586 {A : Type'} (y : A) (x : A) (z : A) : ((term391 A x y z) = (term413 A y x z)) = True.
Proof. exact (TRANS (@lem4779581 A y x z) (@lem4779585 A y x z)). Qed.
Lemma lem4779587 {A : Type'} (y : A) (x : A) (z : A) : True = ((term391 A x y z) = (term413 A y x z)).
Proof. exact (SYM (@lem4779586 A y x z)). Qed.
Lemma lem4779588 {A : Type'} (y : A) (x : A) (z : A) : (term391 A x y z) = (term413 A y x z).
Proof. exact (EQ_MP (@lem4779587 A y x z) (@lem0)). Qed.
Lemma lem4779589 {A : Type'} (y : A) (x : A) (z : A) : term413 A y x z.
Proof. exact (EQ_MP (@lem4779588 A y x z) (@lem4779479 A x y z)). Qed.
Lemma lem4779591 (b : Prop) (a : Prop) : (a \/ b) = (term397 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4779592 {A : Type'} (x : A) (y : A) (z : A) : (term413 A y x z) = (term416 A x y z).
Proof. exact (@lem4779591 (term417 A y x z) (y = z)). Qed.
Lemma lem4779594 (a : Prop) (b : Prop) : (term418 a b) = (term419 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4779595 {A : Type'} (y : A) (x : A) (z : A) : (term420 A y x z) = (term421 A y x z).
Proof. exact (@lem4779594 (term409 A x y) (term409 A x z)). Qed.
Lemma lem4779597 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4779598 {A : Type'} (x : A) (y : A) : (term422 A x y) = (x = y).
Proof. exact (@lem4779597 (x = y)). Qed.
Lemma lem4779599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4779600 {A : Type'} (x : A) (y : A) : (term423 A x y) = (term424 A x y).
Proof. exact (MK_COMB (@lem4779599) (@lem4779598 A x y)). Qed.
Lemma lem4779602 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4779603 {A : Type'} (x : A) (z : A) : (term422 A x z) = (x = z).
Proof. exact (@lem4779602 (x = z)). Qed.
Lemma lem4779604 {A : Type'} (y : A) (x : A) (z : A) : (term421 A y x z) = (term425 A y x z).
Proof. exact (MK_COMB (@lem4779600 A x y) (@lem4779603 A x z)). Qed.
Lemma lem4779605 {A : Type'} (y : A) (x : A) (z : A) : (term420 A y x z) = (term425 A y x z).
Proof. exact (TRANS (@lem4779595 A y x z) (@lem4779604 A y x z)). Qed.
Lemma lem4779606 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4779607 {A : Type'} (y : A) (x : A) (z : A) : (term426 A y x z) = (term427 A y x z).
Proof. exact (MK_COMB (@lem4779606) (@lem4779605 A y x z)). Qed.
Lemma lem4779608 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4779609 {A : Type'} (x : A) (y : A) (z : A) : (term416 A x y z) = (term428 A x y z).
Proof. exact (MK_COMB (@lem4779607 A y x z) (@lem4779608 A y z)). Qed.
Lemma lem4779610 {A : Type'} (x : A) (y : A) (z : A) : (term413 A y x z) = (term428 A x y z).
Proof. exact (TRANS (@lem4779592 A x y z) (@lem4779609 A x y z)). Qed.
Lemma lem4779612 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : term762 A n f x.
Proof. exact (conj (@lem4779490 A f n x h1) (@lem4779499 A f x)). Qed.
Lemma lem4779614 {A : Type'} (x : A) (y : A) (z : A) : term428 A x y z.
Proof. exact (EQ_MP (@lem4779610 A x y z) (@lem4779589 A y x z)). Qed.
Lemma lem4779615 {A : Type'} (x : A) (y : A) (z : A) : term428 A x y z.
Proof. exact (@lem4779614 A x y z). Qed.
Lemma lem4779616 {A : Type'} (n : nat) (f : nat -> A) (x : nat) : term763 A n f x.
Proof. exact (@lem4779615 A (f x) (f n) (f x)). Qed.
Lemma lem4779619 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : (f n) = (f x).
Proof. exact (@lem4779616 A n f x (@lem4779612 A f n x h1)). Qed.
Lemma lem4779620 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : term759 A n f x.
Proof. exact (fun h0 : term594 A n f x => @lem4779619 A f n x h1). Qed.
Lemma lem4779622 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779623 {A : Type'} (n : nat) (f : nat -> A) (x : nat) : (term759 A n f x) = ((f n) = (f x)).
Proof. exact (@lem4779622 ((f n) = (f x))). Qed.
Lemma lem4779624 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : (f n) = (f x).
Proof. exact (EQ_MP (@lem4779623 A n f x) (@lem4779620 A f n x h1)). Qed.
Lemma lem4779627 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4779629 {A : Type'} (n : nat) (f : nat -> A) (x : nat) : (term594 A n f x) = (term764 A n f x).
Proof. exact (@lem4779627 ((f n) = (f x))). Qed.
Lemma lem4779632 {A : Type'} (n : nat) (f : nat -> A) (x : nat) (h1 : term594 A n f x) : term764 A n f x.
Proof. exact (EQ_MP (@lem4779629 A n f x) (@lem4778914 A n f x h1)). Qed.
Lemma lem4779635 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A n f x) (h2 : term608 A f n x) : False.
Proof. exact (@lem4779632 A n f x h1 (@lem4779624 A f n x h2)). Qed.
Lemma lem4779636 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A n f x) (h2 : term608 A f n x) : term445.
Proof. exact (fun h0 : ~ False => @lem4779635 A f n x h1 h2). Qed.
Lemma lem4779638 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779639 : term445 = False.
Proof. exact (@lem4779638 False). Qed.
Lemma lem4779640 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A n f x) (h2 : term608 A f n x) : False.
Proof. exact (EQ_MP (@lem4779639) (@lem4779636 A f n x h1 h2)). Qed.
Lemma lem4779706 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4779707 (x : nat) : term765 x.
Proof. exact (fun h0 : term756 x => @lem4779706 x). Qed.
Lemma lem4779709 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779710 (x : nat) : (term765 x) = (x = x).
Proof. exact (@lem4779709 (x = x)). Qed.
Lemma lem4779711 (x : nat) : x = x.
Proof. exact (EQ_MP (@lem4779710 x) (@lem4779707 x)). Qed.
Lemma lem4779714 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4779716 (x : nat) : (term756 x) = (term766 x).
Proof. exact (@lem4779714 (x = x)). Qed.
Lemma lem4779719 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : term766 x.
Proof. exact (EQ_MP (@lem4779716 x) (@lem4779110 A f n x h1 h2)). Qed.
Lemma lem4779722 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : False.
Proof. exact (@lem4779719 A f n x h1 h2 (@lem4779711 x)). Qed.
Lemma lem4779723 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : term445.
Proof. exact (fun h0 : ~ False => @lem4779722 A f n x h1 h2). Qed.
Lemma lem4779725 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779726 : term445 = False.
Proof. exact (@lem4779725 False). Qed.
Lemma lem4779793 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term633 A f x n) : Peano.lt x n.
Proof. exact (proj1 (@lem4778608 A f x n h1)). Qed.
Lemma lem4779794 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term633 A f x n) : term767 x n.
Proof. exact (fun h0 : term768 x n => @lem4779793 A f x n h1). Qed.
Lemma lem4779796 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779797 (x : nat) (n : nat) : (term767 x n) = (Peano.lt x n).
Proof. exact (@lem4779796 (Peano.lt x n)). Qed.
Lemma lem4779798 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term633 A f x n) : Peano.lt x n.
Proof. exact (EQ_MP (@lem4779797 x n) (@lem4779794 A f x n h1)). Qed.
Lemma lem4779800 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term633 A f x n) : (f x) = (f n).
Proof. exact (proj1 (@lem4778623 A f x n h1)). Qed.
Lemma lem4779801 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term633 A f x n) : term759 A x f n.
Proof. exact (fun h0 : term594 A x f n => @lem4779800 A f x n h1). Qed.
Lemma lem4779803 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779804 {A : Type'} (x : nat) (f : nat -> A) (n : nat) : (term759 A x f n) = ((f x) = (f n)).
Proof. exact (@lem4779803 ((f x) = (f n))). Qed.
Lemma lem4779805 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term633 A f x n) : (f x) = (f n).
Proof. exact (EQ_MP (@lem4779804 A x f n) (@lem4779801 A f x n h1)). Qed.
Lemma lem4779807 (a : Prop) (b : Prop) : (term440 a b) = (term441 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4779808 {A : Type'} (_58920 : nat) (f : nat -> A) (_58919 : nat) : (term593 A _58920 f _58919) = (term769 A _58920 f _58919).
Proof. exact (@lem4779807 (Peano.lt _58920 _58919) ((f _58920) = (f _58919))). Qed.
Lemma lem4779810 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4779811 {A : Type'} (_58920 : nat) (f : nat -> A) (_58919 : nat) : (term769 A _58920 f _58919) = (term770 A _58920 f _58919).
Proof. exact (@lem4779810 (term771 A _58920 f _58919)). Qed.
Lemma lem4779812 {A : Type'} (_58920 : nat) (f : nat -> A) (_58919 : nat) : (term593 A _58920 f _58919) = (term770 A _58920 f _58919).
Proof. exact (TRANS (@lem4779808 A _58920 f _58919) (@lem4779811 A _58920 f _58919)). Qed.
Lemma lem4779814 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term633 A f x n) : term771 A x f n.
Proof. exact (conj (@lem4779798 A f x n h1) (@lem4779805 A f x n h1)). Qed.
Lemma lem4779816 {A : Type'} (_58920 : nat) (_58919 : nat) (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term770 A _58920 f _58919.
Proof. exact (EQ_MP (@lem4779812 A _58920 f _58919) (@lem4778940 A _58920 _58919 f s h1)). Qed.
Lemma lem4779817 {A : Type'} (x : nat) (n : nat) (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term770 A x f n.
Proof. exact (@lem4779816 A x n f s h1). Qed.
Lemma lem4779820 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : nat) (n : nat) (h1 : term578 A f s) (h2 : term633 A f x n) : False.
Proof. exact (@lem4779817 A x n f s h1 (@lem4779814 A f x n h2)). Qed.
Lemma lem4779821 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : nat) (n : nat) (h1 : term578 A f s) (h2 : term633 A f x n) : term445.
Proof. exact (fun h0 : ~ False => @lem4779820 A s f x n h1 h2). Qed.
Lemma lem4779823 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4779824 : term445 = False.
Proof. exact (@lem4779823 False). Qed.
Lemma lem4779825 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : nat) (n : nat) (h1 : term578 A f s) (h2 : term633 A f x n) : False.
Proof. exact (EQ_MP (@lem4779824) (@lem4779821 A s f x n h1 h2)). Qed.
Lemma lem4779826 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : False.
Proof. exact (EQ_MP (@lem4779726) (@lem4779723 A f n x h1 h2)). Qed.
Lemma lem4779827 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : False.
Proof. exact (EQ_MP (@lem4779418) (@lem4779415 A f x n h1 h2)). Qed.
Lemma lem4779828 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : (n = x) = False.
Proof. exact (prop_ext (fun h3 : n = x => @lem4779826 A f n x h1 h2) (fun h3 : False => @lem4778930 n x h2)). Qed.
Lemma lem4779829 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : False.
Proof. exact (EQ_MP (@lem4779828 A f n x h1 h2) (@lem4778930 n x h2)). Qed.
Lemma lem4779830 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A n f x) (h2 : term608 A f n x) : (term594 A n f x) = False.
Proof. exact (prop_ext (fun h3 : term594 A n f x => @lem4779640 A f n x h1 h2) (fun h3 : False => @lem4778914 A n f x h1)). Qed.
Lemma lem4779831 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A n f x) (h2 : term608 A f n x) : False.
Proof. exact (EQ_MP (@lem4779830 A f n x h1 h2) (@lem4778914 A n f x h1)). Qed.
Lemma lem4779832 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : (x = n) = False.
Proof. exact (prop_ext (fun h3 : x = n => @lem4779827 A f x n h1 h2) (fun h3 : False => @lem4778898 x n h2)). Qed.
Lemma lem4779833 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : False.
Proof. exact (EQ_MP (@lem4779832 A f x n h1 h2) (@lem4778898 x n h2)). Qed.
Lemma lem4779834 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A x f n) (h2 : term612 A f n x) : (term594 A x f n) = False.
Proof. exact (prop_ext (fun h3 : term594 A x f n => @lem4779331 A f n x h1 h2) (fun h3 : False => @lem4778882 A x f n h1)). Qed.
Lemma lem4779835 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A x f n) (h2 : term612 A f n x) : False.
Proof. exact (EQ_MP (@lem4779834 A f n x h1 h2) (@lem4778882 A x f n h1)). Qed.
Lemma lem4779836 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : (n = x) = False.
Proof. exact (prop_ext (fun h3 : n = x => @lem4779829 A f n x h1 h2) (fun h3 : False => @lem4778782 n x h2)). Qed.
Lemma lem4779837 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : False.
Proof. exact (EQ_MP (@lem4779836 A f n x h1 h2) (@lem4778782 n x h2)). Qed.
Lemma lem4779838 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A n f x) (h2 : term608 A f n x) : (term594 A n f x) = False.
Proof. exact (prop_ext (fun h3 : term594 A n f x => @lem4779831 A f n x h1 h2) (fun h3 : False => @lem4778743 A n f x h1)). Qed.
Lemma lem4779839 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A n f x) (h2 : term608 A f n x) : False.
Proof. exact (EQ_MP (@lem4779838 A f n x h1 h2) (@lem4778743 A n f x h1)). Qed.
Lemma lem4779840 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : (x = n) = False.
Proof. exact (prop_ext (fun h3 : x = n => @lem4779833 A f x n h1 h2) (fun h3 : False => @lem4778704 x n h2)). Qed.
Lemma lem4779841 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : False.
Proof. exact (EQ_MP (@lem4779840 A f x n h1 h2) (@lem4778704 x n h2)). Qed.
Lemma lem4779842 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A x f n) (h2 : term612 A f n x) : (term594 A x f n) = False.
Proof. exact (prop_ext (fun h3 : term594 A x f n => @lem4779835 A f n x h1 h2) (fun h3 : False => @lem4778665 A x f n h1)). Qed.
Lemma lem4779843 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A x f n) (h2 : term612 A f n x) : False.
Proof. exact (EQ_MP (@lem4779842 A f n x h1 h2) (@lem4778665 A x f n h1)). Qed.
Lemma lem4779844 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : (n = x) = False.
Proof. exact (prop_ext (fun h3 : n = x => @lem4779837 A f n x h1 h2) (fun h3 : False => @lem4778782 n x h2)). Qed.
Lemma lem4779845 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) (h2 : n = x) : False.
Proof. exact (EQ_MP (@lem4779844 A f n x h1 h2) (@lem4778782 n x h2)). Qed.
Lemma lem4779846 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A n f x) (h2 : term608 A f n x) : (term594 A n f x) = False.
Proof. exact (prop_ext (fun h3 : term594 A n f x => @lem4779839 A f n x h1 h2) (fun h3 : False => @lem4778743 A n f x h1)). Qed.
Lemma lem4779847 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A n f x) (h2 : term608 A f n x) : False.
Proof. exact (EQ_MP (@lem4779846 A f n x h1 h2) (@lem4778743 A n f x h1)). Qed.
Lemma lem4779848 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : (x = n) = False.
Proof. exact (prop_ext (fun h3 : x = n => @lem4779841 A f x n h1 h2) (fun h3 : False => @lem4778704 x n h2)). Qed.
Lemma lem4779849 {A : Type'} (f : nat -> A) (x : nat) (n : nat) (h1 : term612 A f n x) (h2 : x = n) : False.
Proof. exact (EQ_MP (@lem4779848 A f x n h1 h2) (@lem4778704 x n h2)). Qed.
Lemma lem4779850 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A x f n) (h2 : term612 A f n x) : (term594 A x f n) = False.
Proof. exact (prop_ext (fun h3 : term594 A x f n => @lem4779843 A f n x h1 h2) (fun h3 : False => @lem4778665 A x f n h1)). Qed.
Lemma lem4779851 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term594 A x f n) (h2 : term612 A f n x) : False.
Proof. exact (EQ_MP (@lem4779850 A f n x h1 h2) (@lem4778665 A x f n h1)). Qed.
Lemma lem4779852 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term608 A f n x) : False.
Proof. exact (or_elim (@lem4778617 A f n x h1) (fun h0 : term594 A n f x => @lem4779847 A f n x h0 h1) (fun h0 : n = x => @lem4779845 A f n x h1 h0)). Qed.
Lemma lem4779853 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term612 A f n x) : False.
Proof. exact (or_elim (@lem4778612 A f n x h1) (fun h0 : term594 A x f n => @lem4779851 A f n x h0 h1) (fun h0 : x = n => @lem4779849 A f x n h1 h0)). Qed.
Lemma lem4779854 {A : Type'} (f : nat -> A) (n : nat) (x : nat) (h1 : term616 A f n x) : False.
Proof. exact (or_elim (@lem4778607 A f n x h1) (fun h0 : term612 A f n x => @lem4779853 A f n x h0) (fun h0 : term608 A f n x => @lem4779852 A f n x h0)). Qed.
Lemma lem4779855 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : nat) (n : nat) (h1 : term578 A f s) (h2 : term737 A f x n) : False.
Proof. exact (or_elim (@lem4778602 A f x n h2) (fun h0 : term616 A f n x => @lem4779854 A f n x h0) (fun h0 : term633 A f x n => @lem4779825 A s f x n h1 h0)). Qed.
Lemma lem4779856 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : nat) (n : nat) (h1 : term578 A f s) (h2 : term737 A f x n) : (term737 A f x n) = False.
Proof. exact (prop_ext (fun h3 : term737 A f x n => @lem4779855 A s f x n h1 h2) (fun h3 : False => @lem4778602 A f x n h2)). Qed.
Lemma lem4779857 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : nat) (n : nat) (h1 : term578 A f s) (h2 : term737 A f x n) : False.
Proof. exact (EQ_MP (@lem4779856 A s f x n h1 h2) (@lem4778602 A f x n h2)). Qed.
Lemma lem4779858 {A : Type'} (x : nat) (f : nat -> A) (s : A -> Prop) (h1 : term740 A f x) (h2 : term578 A f s) : False.
Proof. exact (ex_elim (@lem4778435 A f x h1) (fun n : nat => fun h0 : term739 A f x n => @lem4779857 A s f x n h2 h0)). Qed.
Lemma lem4779859 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term592 A f) (h2 : term578 A f s) : False.
Proof. exact (ex_elim (@lem4778434 A f h1) (fun x : nat => fun h0 : term741 A f x => @lem4779858 A x f s h0 h2)). Qed.
Lemma lem4779860 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term592 A f) (h2 : term578 A f s) : (term592 A f) = False.
Proof. exact (prop_ext (fun h3 : term592 A f => @lem4779859 A f s h1 h2) (fun h3 : False => @lem4777810 A f h1)). Qed.
Lemma lem4779861 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term592 A f) (h2 : term578 A f s) : False.
Proof. exact (EQ_MP (@lem4779860 A f s h1 h2) (@lem4777810 A f h1)). Qed.
Lemma lem4779862 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term591 A f.
Proof. exact (fun h0 : term592 A f => @lem4779861 A f s h0 h1). Qed.
Lemma lem4779863 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term578 A f s) : term517 A f.
Proof. exact (EQ_MP (@lem4777809 A f) (@lem4779862 A f s h1)). Qed.
Lemma lem4779864 {A : Type'} (s : A -> Prop) (f : nat -> A) : term580 A s f.
Proof. exact (fun h0 : term578 A f s => @lem4779863 A f s h0). Qed.
Lemma lem4779869 {A : Type'} (f : nat -> A) : term584 A f.
Proof. exact (fun s : A -> Prop => @lem4779864 A s f). Qed.
Lemma lem4779874 {A : Type'} : term588 A.
Proof. exact (fun f : nat -> A => @lem4779869 A f). Qed.
Lemma lem4779875 {A : Type'} : term587 A.
Proof. exact (EQ_MP (@lem4777804 A) (@lem4779874 A)). Qed.
Lemma lem4779876 {A : Type'} (f : nat -> A) : term772 A f.
Proof. exact (@lem4779875 A f). Qed.
Lemma lem4779877 {A : Type'} (f : nat -> A) : (term772 A f) = (term583 A f).
Proof. exact (eq_refl (term772 A f)). Qed.
Lemma lem4779878 {A : Type'} (f : nat -> A) : term583 A f.
Proof. exact (EQ_MP (@lem4779877 A f) (@lem4779876 A f)). Qed.
Lemma lem4779879 {A : Type'} (f : nat -> A) (s : A -> Prop) : term773 A f s.
Proof. exact (@lem4779878 A f s). Qed.
Lemma lem4779880 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term773 A f s) = (term547 A s f).
Proof. exact (eq_refl (term773 A f s)). Qed.
Lemma lem4779881 {A : Type'} (s : A -> Prop) (f : nat -> A) : term547 A s f.
Proof. exact (EQ_MP (@lem4779880 A s f) (@lem4779879 A f s)). Qed.
Lemma lem4779883 {A : Type'} (s : A -> Prop) (f : nat -> A) : term547 A s f.
Proof. exact (@lem4777539 A s f (@lem4779881 A s f)). Qed.
Lemma lem4779884 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term548 A s f) : False.
Proof. exact (@lem4779883 A s f (@lem4777523 A s f h1)). Qed.
Lemma lem4779885 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term548 A s f) : (term548 A s f) = False.
Proof. exact (prop_ext (fun h2 : term548 A s f => @lem4779884 A s f h1) (fun h2 : False => @lem4777523 A s f h1)). Qed.
Lemma lem4779886 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term548 A s f) : False.
Proof. exact (EQ_MP (@lem4779885 A s f h1) (@lem4777523 A s f h1)). Qed.
Lemma lem4779887 {A : Type'} (s : A -> Prop) (f : nat -> A) : term547 A s f.
Proof. exact (fun h0 : term548 A s f => @lem4779886 A s f h0). Qed.
Lemma lem4779888 {A : Type'} (s : A -> Prop) (f : nat -> A) : term546 A s f.
Proof. exact (EQ_MP (@lem4777522 A s f) (@lem4779887 A s f)). Qed.
Lemma lem4779889 {A : Type'} (s : A -> Prop) (f : nat -> A) : term534 A s f.
Proof. exact (EQ_MP (@lem4777518 A s f) (@lem4779888 A s f)). Qed.
Lemma lem4779890 {A : Type'} (s : A -> Prop) (f : nat -> A) : term533 A s f.
Proof. exact (EQ_MP (@lem4777424 A s f) (@lem4779889 A s f)). Qed.
Lemma lem4779891 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term133 A s f) (h2 : @INFINITE A s) : term519 A f.
Proof. exact (@lem4779890 A s f (@lem4777249 A f s h1 h2)). Qed.
Lemma lem4779892 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term133 A s f) (h2 : @INFINITE A s) : term65 A f.
Proof. exact (@lem4777238 A f (@lem4779891 A f s h1 h2)). Qed.
Lemma lem4779893 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term133 A s f) (h2 : @INFINITE A s) : term64 A s f.
Proof. exact (EQ_MP (@lem4777174 A s f h1) (@lem4779892 A f s h1 h2)). Qed.
Lemma lem4779894 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term133 A s f) (h2 : @INFINITE A s) : (term133 A s f) = (term64 A s f).
Proof. exact (prop_ext (fun h3 : term133 A s f => @lem4779893 A f s h1 h2) (fun h3 : term64 A s f => @lem4777102 A s f h1)). Qed.
Lemma lem4779895 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term133 A s f) (h2 : @INFINITE A s) : term64 A s f.
Proof. exact (EQ_MP (@lem4779894 A f s h1 h2) (@lem4777102 A s f h1)). Qed.
Lemma lem4779896 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : @INFINITE A s) : term457 A s f.
Proof. exact (fun h0 : term133 A s f => @lem4779895 A f s h0 h1). Qed.
Lemma lem4779901 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : term461 A s.
Proof. exact (fun f : nat -> A => @lem4779896 A f s h1). Qed.
Lemma lem4779902 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : term471 A s.
Proof. exact (@lem4777101 A s (@lem4779901 A s h1)). Qed.
Lemma lem4779903 {A : Type'} (s : A -> Prop) (h1 : term67 A s) (h2 : @INFINITE A s) : term63 A s.
Proof. exact (@lem4779902 A s h2 (@lem4774418 A s h1)). Qed.
Lemma lem4779904 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : (term67 A s) = (term63 A s).
Proof. exact (prop_ext (fun h2 : term67 A s => @lem4779903 A s h2 h1) (fun h2 : term63 A s => @lem4777074 A s h1)). Qed.
Lemma lem4779905 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : term63 A s.
Proof. exact (EQ_MP (@lem4779904 A s h1) (@lem4777074 A s h1)). Qed.
Lemma lem4779907 {_97990 : Type'} (t : _97990 -> Prop) : term9 _97990 t.
Proof. exact (EQ_MP (@lem4774292 _97990 t) (@lem4774291 _97990 t)). Qed.
Lemma lem4779908 {A : Type'} (t : A -> Prop) : term9 A t.
Proof. exact (@lem4779907 A t). Qed.
Lemma lem4779909 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem4779908 A s). Qed.
Lemma lem4779910 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term774 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4779911 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term774 _87967 _87968 P f) = (term775 _87967 _87968 P f).
Proof. exact (eq_refl (term774 _87967 _87968 P f)). Qed.
Lemma lem4779912 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term775 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4779911 _87967 _87968 P f) (@lem4779910 _87967 _87968 P f)). Qed.
Lemma lem4779913 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term776 _87967 _87968 P f s.
Proof. exact (@lem4779912 _87967 _87968 P f s). Qed.
Lemma lem4779914 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term776 _87967 _87968 P f s) = ((term777 _87967 _87968 f s P) = (term778 _87967 _87968 s P f)).
Proof. exact (eq_refl (term776 _87967 _87968 P f s)). Qed.
Lemma lem4779916 {A : Type'} (s : A -> Prop) : term779 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4779917 {A : Type'} (s : A -> Prop) : (term779 A s) = (term780 A s).
Proof. exact (eq_refl (term779 A s)). Qed.
Lemma lem4779918 {A : Type'} (s : A -> Prop) : term780 A s.
Proof. exact (EQ_MP (@lem4779917 A s) (@lem4779916 A s)). Qed.
Lemma lem4779919 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term781 A s t.
Proof. exact (@lem4779918 A s t). Qed.
Lemma lem4779920 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term781 A s t) = ((@SUBSET A s t) = (term782 A s t)).
Proof. exact (eq_refl (term781 A s t)). Qed.
Lemma lem4779922 {A : Type'} (x : nat) (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : term783 A f s x.
Proof. exact (@lem4774417 A f s h1 x). Qed.
Lemma lem4779923 {A : Type'} (f : nat -> A) (x : nat) (s : A -> Prop) : (term783 A f s x) = (term474 A f x s).
Proof. exact (eq_refl (term783 A f s x)). Qed.
Lemma lem4779924 {A : Type'} (x : nat) (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : term474 A f x s.
Proof. exact (EQ_MP (@lem4779923 A f x s) (@lem4779922 A x f s h1)). Qed.
Lemma lem4779925 {A : Type'} (f : nat -> A) (x : nat) (s : A -> Prop) : (term474 A f x s) = ((term474 A f x s) = True).
Proof. exact (@lem7 (term474 A f x s)). Qed.
Lemma lem4779938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term782 A s t).
Proof. exact (EQ_MP (@lem4779920 A s t) (@lem4779919 A s t)). Qed.
Lemma lem4779939 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term782 A s t).
Proof. exact (@lem4779938 A s t). Qed.
Lemma lem4779940 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term784 A f s) = (term785 A f s).
Proof. exact (@lem4779939 A (@IMAGE nat A f (@UNIV nat)) s). Qed.
Lemma lem4779942 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term777 _87967 _87968 f s P) = (term778 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4779914 _87967 _87968 s P f) (@lem4779913 _87967 _87968 P f s)). Qed.
Lemma lem4779943 {A : Type'} (s : nat -> Prop) (P : A -> Prop) (f : nat -> A) : (term786 A f s P) = (term787 A s P f).
Proof. exact (@lem4779942 A nat s P f). Qed.
Lemma lem4779944 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term788 A f s) = (term789 A s f).
Proof. exact (@lem4779943 A (@UNIV nat) (term790 A s) f). Qed.
Lemma lem4779945 {A : Type'} (x : A) (s : A -> Prop) : (term791 A s x) = (@IN A x s).
Proof. exact (eq_refl (term791 A s x)). Qed.
Lemma lem4779946 {A : Type'} (x : A) (f : nat -> A) : (term792 A x f) = (term792 A x f).
Proof. exact (eq_refl (term792 A x f)). Qed.
Lemma lem4779947 {A : Type'} (f : nat -> A) (x : A) (s : A -> Prop) : (term793 A f s x) = (term794 A f x s).
Proof. exact (MK_COMB (@lem4779946 A x f) (@lem4779945 A x s)). Qed.
Lemma lem4779948 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term795 A f s) = (term796 A f s).
Proof. exact (fun_ext (fun x : A => @lem4779947 A f x s)). Qed.
Lemma lem4779949 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4779950 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term788 A f s) = (term785 A f s).
Proof. exact (MK_COMB (@lem4779949 A) (@lem4779948 A f s)). Qed.
Lemma lem4779951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4779952 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term797 A f s) = (term798 A f s).
Proof. exact (MK_COMB (@lem4779951) (@lem4779950 A f s)). Qed.
Lemma lem4779953 {A : Type'} (f : nat -> A) (x : nat) (s : A -> Prop) : (term799 A s f x) = (term474 A f x s).
Proof. exact (eq_refl (term799 A s f x)). Qed.
Lemma lem4779954 (x : nat) : (term800 x) = (term800 x).
Proof. exact (eq_refl (term800 x)). Qed.
Lemma lem4779955 {A : Type'} (f : nat -> A) (x : nat) (s : A -> Prop) : (term801 A s f x) = (term802 A f x s).
Proof. exact (MK_COMB (@lem4779954 x) (@lem4779953 A f x s)). Qed.
Lemma lem4779956 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term803 A s f) = (term804 A f s).
Proof. exact (fun_ext (fun x : nat => @lem4779955 A f x s)). Qed.
Lemma lem4779957 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4779958 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term789 A s f) = (term805 A f s).
Proof. exact (MK_COMB (@lem4779957) (@lem4779956 A f s)). Qed.
Lemma lem4779959 {A : Type'} (f : nat -> A) (s : A -> Prop) : ((term788 A f s) = (term789 A s f)) = ((term785 A f s) = (term805 A f s)).
Proof. exact (MK_COMB (@lem4779952 A f s) (@lem4779958 A f s)). Qed.
Lemma lem4779960 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term785 A f s) = (term805 A f s).
Proof. exact (EQ_MP (@lem4779959 A f s) (@lem4779944 A s f)). Qed.
Lemma lem4779965 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term784 A f s) = (term805 A f s).
Proof. exact (TRANS (@lem4779940 A f s) (@lem4779960 A f s)). Qed.
Lemma lem4779969 {A : Type'} (x : nat) (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : (term474 A f x s) = True.
Proof. exact (EQ_MP (@lem4779925 A f x s) (@lem4779924 A x f s h1)). Qed.
Lemma lem4779970 (x : nat) : (term800 x) = (term800 x).
Proof. exact (eq_refl (term800 x)). Qed.
Lemma lem4779971 {A : Type'} (x : nat) (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : (term802 A f x s) = (term806 x).
Proof. exact (MK_COMB (@lem4779970 x) (@lem4779969 A x f s h1)). Qed.
Lemma lem4779973 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4779974 (x : nat) : (term806 x) = True.
Proof. exact (@lem4779973 (@IN nat x (@UNIV nat))). Qed.
Lemma lem4779975 {A : Type'} (x : nat) (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : (term802 A f x s) = True.
Proof. exact (TRANS (@lem4779971 A x f s h1) (@lem4779974 x)). Qed.
Lemma lem4779976 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : (term804 A f s) = term172.
Proof. exact (fun_ext (fun x : nat => @lem4779975 A x f s h1)). Qed.
Lemma lem4779977 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4779978 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : (term805 A f s) = term173.
Proof. exact (MK_COMB (@lem4779977) (@lem4779976 A f s h1)). Qed.
Lemma lem4779980 {A : Type'} (t : Prop) : (term171 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4779981 (t : Prop) : (term174 t) = t.
Proof. exact (@lem4779980 nat t). Qed.
Lemma lem4779982 : term173 = True.
Proof. exact (@lem4779981 True). Qed.
Lemma lem4779983 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : (term805 A f s) = True.
Proof. exact (TRANS (@lem4779978 A f s h1) (@lem4779982)). Qed.
Lemma lem4779984 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : (term784 A f s) = True.
Proof. exact (TRANS (@lem4779965 A f s) (@lem4779983 A f s h1)). Qed.
Lemma lem4779985 {A : Type'} (f : nat -> A) : (term807 A f) = (term807 A f).
Proof. exact (eq_refl (term807 A f)). Qed.
Lemma lem4779986 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : (term808 A f s) = (term809 A f).
Proof. exact (MK_COMB (@lem4779985 A f) (@lem4779984 A f s h1)). Qed.
Lemma lem4779988 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4779989 {A : Type'} (f : nat -> A) : (term809 A f) = (term810 A f).
Proof. exact (@lem4779988 (term810 A f)). Qed.
Lemma lem4779990 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : (term808 A f s) = (term810 A f).
Proof. exact (TRANS (@lem4779986 A f s h1) (@lem4779989 A f)). Qed.
Lemma lem4779991 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : (term810 A f) = (term808 A f s).
Proof. exact (SYM (@lem4779990 A f s h1)). Qed.
Lemma lem4779993 (p : Prop) : p = (term270 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4779994 {A : Type'} (f : nat -> A) : (term810 A f) = (term811 A f).
Proof. exact (@lem4779993 (term810 A f)). Qed.
Lemma lem4779995 {A : Type'} (f : nat -> A) : (term811 A f) = (term810 A f).
Proof. exact (SYM (@lem4779994 A f)). Qed.
Lemma lem4779996 {A : Type'} (f : nat -> A) (h1 : term812 A f) : term812 A f.
Proof. exact (h1). Qed.
Lemma lem4779997 {A : Type'} : term813 A.
Proof. exact (@lem3630638 A A). Qed.
Lemma lem4779998 {A : Type'} : term814 A.
Proof. exact (@lem3630638 A nat). Qed.
Lemma lem4779999 {A B : Type'} : term815 A B.
Proof. exact (@lem3630638 A B). Qed.
Lemma lem4780000 {B : Type'} : term816 B.
Proof. exact (@lem3630638 nat B). Qed.
Lemma lem4780003 {A : Type'} : term816 A.
Proof. exact (@lem3630638 nat A). Qed.
Lemma lem4780006 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term817 A B s f) : term817 A B s f.
Proof. exact (h1). Qed.
Lemma lem4780007 {A B : Type'} (s : A -> Prop) (f : nat -> A) : term818 A B s f.
Proof. exact (fun h0 : term817 A B s f => @lem4780006 A B s f h0). Qed.
Lemma lem4780008 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term818 A B s f) : term818 A B s f.
Proof. exact (h1). Qed.
Lemma lem4780009 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term817 A B s f) : term817 A B s f.
Proof. exact (h1). Qed.
Lemma lem4780010 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term817 A B s f) (h2 : term818 A B s f) : term817 A B s f.
Proof. exact (@lem4780008 A B s f h2 (@lem4780009 A B s f h1)). Qed.
Lemma lem4780011 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term817 A B s f) : term819 A B s f.
Proof. exact (fun h0 : term818 A B s f => @lem4780010 A B s f h1 h0). Qed.
Lemma lem4780012 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term818 A B s f) : term818 A B s f.
Proof. exact (h1). Qed.
Lemma lem4780013 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term817 A B s f) (h2 : term818 A B s f) : term817 A B s f.
Proof. exact (@lem4780011 A B s f h1 (@lem4780012 A B s f h2)). Qed.
Lemma lem4780014 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term818 A B s f) : term818 A B s f.
Proof. exact (fun h0 : term817 A B s f => @lem4780013 A B s f h0 h1). Qed.
Lemma lem4780015 {A B : Type'} (s : A -> Prop) (f : nat -> A) : term820 A B s f.
Proof. exact (fun h0 : term818 A B s f => @lem4780014 A B s f h0). Qed.
Lemma lem4780018 {A B : Type'} (s : A -> Prop) (f : nat -> A) : term818 A B s f.
Proof. exact (@lem4780015 A B s f (@lem4780007 A B s f)). Qed.
Lemma lem4780019 {A B : Type'} (s : A -> Prop) (f : nat -> A) : term818 A B s f.
Proof. exact (@lem4780018 A B s f). Qed.
Lemma lem4780147 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4780148 {B : Type'} : (term821 B) = (term822 B).
Proof. exact (@lem4780147 (term816 B)). Qed.
Lemma lem4780171 {A : Type'} : (term823 A) = (term823 A).
Proof. exact (eq_refl (term823 A)). Qed.
Lemma lem4780172 {A B : Type'} : (term824 A B) = (term825 A B).
Proof. exact (MK_COMB (@lem4780171 A) (@lem4780148 B)). Qed.
Lemma lem4780175 {A : Type'} : (term826 A) = (term826 A).
Proof. exact (eq_refl (term826 A)). Qed.
Lemma lem4780176 {A B : Type'} : (term827 A B) = (term828 A B).
Proof. exact (MK_COMB (@lem4780175 A) (@lem4780172 A B)). Qed.
Lemma lem4780179 {A B : Type'} : (term829 A B) = (term829 A B).
Proof. exact (eq_refl (term829 A B)). Qed.
Lemma lem4780180 {A B : Type'} : (term830 A B) = (term831 A B).
Proof. exact (MK_COMB (@lem4780179 A B) (@lem4780176 A B)). Qed.
Lemma lem4780183 {A : Type'} : (term832 A) = (term832 A).
Proof. exact (eq_refl (term832 A)). Qed.
Lemma lem4780184 {A B : Type'} : (term833 A B) = (term834 A B).
Proof. exact (MK_COMB (@lem4780183 A) (@lem4780180 A B)). Qed.
Lemma lem4780187 : term835 = term835.
Proof. exact (eq_refl term835). Qed.
Lemma lem4780188 {A B : Type'} : (term836 A B) = (term837 A B).
Proof. exact (MK_COMB (@lem4780187) (@lem4780184 A B)). Qed.
Lemma lem4780191 {A : Type'} (f : nat -> A) : (term838 A f) = (term838 A f).
Proof. exact (eq_refl (term838 A f)). Qed.
Lemma lem4780192 {A B : Type'} (f : nat -> A) : (term839 A B f) = (term840 A B f).
Proof. exact (MK_COMB (@lem4780191 A f) (@lem4780188 A B)). Qed.
Lemma lem4780195 {A : Type'} (f : nat -> A) : (term841 A f) = (term841 A f).
Proof. exact (eq_refl (term841 A f)). Qed.
Lemma lem4780196 {A B : Type'} (f : nat -> A) : (term842 A B f) = (term843 A B f).
Proof. exact (MK_COMB (@lem4780195 A f) (@lem4780192 A B f)). Qed.
Lemma lem4780199 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term844 A f s) = (term844 A f s).
Proof. exact (eq_refl (term844 A f s)). Qed.
Lemma lem4780200 {A B : Type'} (s : A -> Prop) (f : nat -> A) : (term817 A B s f) = (term845 A B s f).
Proof. exact (MK_COMB (@lem4780199 A f s) (@lem4780196 A B f)). Qed.
Lemma lem4780203 {A B : Type'} (f : nat -> A) : (term846 A B f) = (term847 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4780200 A B s f)). Qed.
Lemma lem4780204 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4780205 {A B : Type'} (f : nat -> A) : (term848 A B f) = (term849 A B f).
Proof. exact (MK_COMB (@lem4780204 A) (@lem4780203 A B f)). Qed.
Lemma lem4780210 {A B : Type'} : (term850 A B) = (term851 A B).
Proof. exact (fun_ext (fun f : nat -> A => @lem4780205 A B f)). Qed.
Lemma lem4780211 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4780220 {A B : Type'} : (term852 A B) = (term853 A B).
Proof. exact (MK_COMB (@lem4780211 A) (@lem4780210 A B)). Qed.
Lemma lem4780225 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term854 B f s) = (term854 B f s).
Proof. exact (eq_refl (term854 B f s)). Qed.
Lemma lem4780226 {B : Type'} (f : nat -> B) : (term855 B f) = (term855 B f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4780225 B f s)). Qed.
Lemma lem4780227 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4780228 {B : Type'} (f : nat -> B) : (term856 B f) = (term856 B f).
Proof. exact (MK_COMB (@lem4780227) (@lem4780226 B f)). Qed.
Lemma lem4780233 {B : Type'} (f : nat -> B) (x : nat) (y : nat) : (term493 B f x y) = (term493 B f x y).
Proof. exact (eq_refl (term493 B f x y)). Qed.
Lemma lem4780234 {B : Type'} (f : nat -> B) (x : nat) : (term481 B f x) = (term481 B f x).
Proof. exact (fun_ext (fun y : nat => @lem4780233 B f x y)). Qed.
Lemma lem4780235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4780236 {B : Type'} (f : nat -> B) (x : nat) : (term524 B f x) = (term524 B f x).
Proof. exact (MK_COMB (@lem4780235) (@lem4780234 B f x)). Qed.
Lemma lem4780237 {B : Type'} (f : nat -> B) : (term526 B f) = (term526 B f).
Proof. exact (fun_ext (fun x : nat => @lem4780236 B f x)). Qed.
Lemma lem4780238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4780239 {B : Type'} (f : nat -> B) : (term65 B f) = (term65 B f).
Proof. exact (MK_COMB (@lem4780238) (@lem4780237 B f)). Qed.
Lemma lem4780240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780241 {B : Type'} (f : nat -> B) : (term841 B f) = (term841 B f).
Proof. exact (MK_COMB (@lem4780240) (@lem4780239 B f)). Qed.
Lemma lem4780242 {B : Type'} (f : nat -> B) : (term857 B f) = (term857 B f).
Proof. exact (MK_COMB (@lem4780241 B f) (@lem4780228 B f)). Qed.
Lemma lem4780243 {B : Type'} : (term858 B) = (term858 B).
Proof. exact (fun_ext (fun f : nat -> B => @lem4780242 B f)). Qed.
Lemma lem4780244 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4780245 {B : Type'} : (term816 B) = (term816 B).
Proof. exact (MK_COMB (@lem4780244 B) (@lem4780243 B)). Qed.
Lemma lem4780246 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4780247 {B : Type'} : (term822 B) = (term822 B).
Proof. exact (MK_COMB (@lem4780246) (@lem4780245 B)). Qed.
Lemma lem4780252 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term854 A f s) = (term854 A f s).
Proof. exact (eq_refl (term854 A f s)). Qed.
Lemma lem4780253 {A : Type'} (f : nat -> A) : (term855 A f) = (term855 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4780252 A f s)). Qed.
Lemma lem4780254 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4780255 {A : Type'} (f : nat -> A) : (term856 A f) = (term856 A f).
Proof. exact (MK_COMB (@lem4780254) (@lem4780253 A f)). Qed.
Lemma lem4780260 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term493 A f x y) = (term493 A f x y).
Proof. exact (eq_refl (term493 A f x y)). Qed.
Lemma lem4780261 {A : Type'} (f : nat -> A) (x : nat) : (term481 A f x) = (term481 A f x).
Proof. exact (fun_ext (fun y : nat => @lem4780260 A f x y)). Qed.
Lemma lem4780262 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4780263 {A : Type'} (f : nat -> A) (x : nat) : (term524 A f x) = (term524 A f x).
Proof. exact (MK_COMB (@lem4780262) (@lem4780261 A f x)). Qed.
Lemma lem4780264 {A : Type'} (f : nat -> A) : (term526 A f) = (term526 A f).
Proof. exact (fun_ext (fun x : nat => @lem4780263 A f x)). Qed.
Lemma lem4780265 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4780266 {A : Type'} (f : nat -> A) : (term65 A f) = (term65 A f).
Proof. exact (MK_COMB (@lem4780265) (@lem4780264 A f)). Qed.
Lemma lem4780267 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780268 {A : Type'} (f : nat -> A) : (term841 A f) = (term841 A f).
Proof. exact (MK_COMB (@lem4780267) (@lem4780266 A f)). Qed.
Lemma lem4780269 {A : Type'} (f : nat -> A) : (term857 A f) = (term857 A f).
Proof. exact (MK_COMB (@lem4780268 A f) (@lem4780255 A f)). Qed.
Lemma lem4780270 {A : Type'} : (term858 A) = (term858 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem4780269 A f)). Qed.
Lemma lem4780271 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4780272 {A : Type'} : (term816 A) = (term816 A).
Proof. exact (MK_COMB (@lem4780271 A) (@lem4780270 A)). Qed.
Lemma lem4780273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780274 {A : Type'} : (term823 A) = (term823 A).
Proof. exact (MK_COMB (@lem4780273) (@lem4780272 A)). Qed.
Lemma lem4780275 {A B : Type'} : (term825 A B) = (term825 A B).
Proof. exact (MK_COMB (@lem4780274 A) (@lem4780247 B)). Qed.
Lemma lem4780280 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term859 A f s) = (term859 A f s).
Proof. exact (eq_refl (term859 A f s)). Qed.
Lemma lem4780281 {A : Type'} (f : A -> nat) : (term860 A f) = (term860 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4780280 A f s)). Qed.
Lemma lem4780282 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4780283 {A : Type'} (f : A -> nat) : (term861 A f) = (term861 A f).
Proof. exact (MK_COMB (@lem4780282 A) (@lem4780281 A f)). Qed.
Lemma lem4780288 {A : Type'} (f : A -> nat) (x : A) (y : A) : (term862 A f x y) = (term862 A f x y).
Proof. exact (eq_refl (term862 A f x y)). Qed.
Lemma lem4780289 {A : Type'} (f : A -> nat) (x : A) : (term863 A f x) = (term863 A f x).
Proof. exact (fun_ext (fun y : A => @lem4780288 A f x y)). Qed.
Lemma lem4780290 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4780291 {A : Type'} (f : A -> nat) (x : A) : (term864 A f x) = (term864 A f x).
Proof. exact (MK_COMB (@lem4780290 A) (@lem4780289 A f x)). Qed.
Lemma lem4780292 {A : Type'} (f : A -> nat) : (term865 A f) = (term865 A f).
Proof. exact (fun_ext (fun x : A => @lem4780291 A f x)). Qed.
Lemma lem4780293 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4780294 {A : Type'} (f : A -> nat) : (term866 A f) = (term866 A f).
Proof. exact (MK_COMB (@lem4780293 A) (@lem4780292 A f)). Qed.
Lemma lem4780295 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780296 {A : Type'} (f : A -> nat) : (term867 A f) = (term867 A f).
Proof. exact (MK_COMB (@lem4780295) (@lem4780294 A f)). Qed.
Lemma lem4780297 {A : Type'} (f : A -> nat) : (term868 A f) = (term868 A f).
Proof. exact (MK_COMB (@lem4780296 A f) (@lem4780283 A f)). Qed.
Lemma lem4780298 {A : Type'} : (term869 A) = (term869 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem4780297 A f)). Qed.
Lemma lem4780299 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4780300 {A : Type'} : (term814 A) = (term814 A).
Proof. exact (MK_COMB (@lem4780299 A) (@lem4780298 A)). Qed.
Lemma lem4780301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780302 {A : Type'} : (term826 A) = (term826 A).
Proof. exact (MK_COMB (@lem4780301) (@lem4780300 A)). Qed.
Lemma lem4780303 {A B : Type'} : (term828 A B) = (term828 A B).
Proof. exact (MK_COMB (@lem4780302 A) (@lem4780275 A B)). Qed.
Lemma lem4780308 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term870 A B f s) = (term870 A B f s).
Proof. exact (eq_refl (term870 A B f s)). Qed.
Lemma lem4780309 {A B : Type'} (f : A -> B) : (term871 A B f) = (term871 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4780308 A B f s)). Qed.
Lemma lem4780310 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4780311 {A B : Type'} (f : A -> B) : (term872 A B f) = (term872 A B f).
Proof. exact (MK_COMB (@lem4780310 A) (@lem4780309 A B f)). Qed.
Lemma lem4780316 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term873 A B f x y) = (term873 A B f x y).
Proof. exact (eq_refl (term873 A B f x y)). Qed.
Lemma lem4780317 {A B : Type'} (f : A -> B) (x : A) : (term874 A B f x) = (term874 A B f x).
Proof. exact (fun_ext (fun y : A => @lem4780316 A B f x y)). Qed.
Lemma lem4780318 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4780319 {A B : Type'} (f : A -> B) (x : A) : (term875 A B f x) = (term875 A B f x).
Proof. exact (MK_COMB (@lem4780318 A) (@lem4780317 A B f x)). Qed.
Lemma lem4780320 {A B : Type'} (f : A -> B) : (term876 A B f) = (term876 A B f).
Proof. exact (fun_ext (fun x : A => @lem4780319 A B f x)). Qed.
Lemma lem4780321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4780322 {A B : Type'} (f : A -> B) : (term877 A B f) = (term877 A B f).
Proof. exact (MK_COMB (@lem4780321 A) (@lem4780320 A B f)). Qed.
Lemma lem4780323 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780324 {A B : Type'} (f : A -> B) : (term878 A B f) = (term878 A B f).
Proof. exact (MK_COMB (@lem4780323) (@lem4780322 A B f)). Qed.
Lemma lem4780325 {A B : Type'} (f : A -> B) : (term879 A B f) = (term879 A B f).
Proof. exact (MK_COMB (@lem4780324 A B f) (@lem4780311 A B f)). Qed.
Lemma lem4780326 {A B : Type'} : (term880 A B) = (term880 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4780325 A B f)). Qed.
Lemma lem4780327 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4780328 {A B : Type'} : (term815 A B) = (term815 A B).
Proof. exact (MK_COMB (@lem4780327 A B) (@lem4780326 A B)). Qed.
Lemma lem4780329 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780330 {A B : Type'} : (term829 A B) = (term829 A B).
Proof. exact (MK_COMB (@lem4780329) (@lem4780328 A B)). Qed.
Lemma lem4780331 {A B : Type'} : (term831 A B) = (term831 A B).
Proof. exact (MK_COMB (@lem4780330 A B) (@lem4780303 A B)). Qed.
Lemma lem4780336 {A : Type'} (f : A -> A) (s : A -> Prop) : (term881 A f s) = (term881 A f s).
Proof. exact (eq_refl (term881 A f s)). Qed.
Lemma lem4780337 {A : Type'} (f : A -> A) : (term882 A f) = (term882 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4780336 A f s)). Qed.
Lemma lem4780338 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4780339 {A : Type'} (f : A -> A) : (term883 A f) = (term883 A f).
Proof. exact (MK_COMB (@lem4780338 A) (@lem4780337 A f)). Qed.
Lemma lem4780344 {A : Type'} (f : A -> A) (x : A) (y : A) : (term884 A f x y) = (term884 A f x y).
Proof. exact (eq_refl (term884 A f x y)). Qed.
Lemma lem4780345 {A : Type'} (f : A -> A) (x : A) : (term885 A f x) = (term885 A f x).
Proof. exact (fun_ext (fun y : A => @lem4780344 A f x y)). Qed.
Lemma lem4780346 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4780347 {A : Type'} (f : A -> A) (x : A) : (term886 A f x) = (term886 A f x).
Proof. exact (MK_COMB (@lem4780346 A) (@lem4780345 A f x)). Qed.
Lemma lem4780348 {A : Type'} (f : A -> A) : (term887 A f) = (term887 A f).
Proof. exact (fun_ext (fun x : A => @lem4780347 A f x)). Qed.
Lemma lem4780349 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4780350 {A : Type'} (f : A -> A) : (term888 A f) = (term888 A f).
Proof. exact (MK_COMB (@lem4780349 A) (@lem4780348 A f)). Qed.
Lemma lem4780351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780352 {A : Type'} (f : A -> A) : (term889 A f) = (term889 A f).
Proof. exact (MK_COMB (@lem4780351) (@lem4780350 A f)). Qed.
Lemma lem4780353 {A : Type'} (f : A -> A) : (term890 A f) = (term890 A f).
Proof. exact (MK_COMB (@lem4780352 A f) (@lem4780339 A f)). Qed.
Lemma lem4780354 {A : Type'} : (term891 A) = (term891 A).
Proof. exact (fun_ext (fun f : A -> A => @lem4780353 A f)). Qed.
Lemma lem4780355 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4780356 {A : Type'} : (term813 A) = (term813 A).
Proof. exact (MK_COMB (@lem4780355 A) (@lem4780354 A)). Qed.
Lemma lem4780357 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780358 {A : Type'} : (term832 A) = (term832 A).
Proof. exact (MK_COMB (@lem4780357) (@lem4780356 A)). Qed.
Lemma lem4780359 {A B : Type'} : (term834 A B) = (term834 A B).
Proof. exact (MK_COMB (@lem4780358 A) (@lem4780331 A B)). Qed.
Lemma lem4780362 : term835 = term835.
Proof. exact (eq_refl term835). Qed.
Lemma lem4780363 {A B : Type'} : (term837 A B) = (term837 A B).
Proof. exact (MK_COMB (@lem4780362) (@lem4780359 A B)). Qed.
Lemma lem4780368 {A : Type'} (f : nat -> A) : (term838 A f) = (term838 A f).
Proof. exact (eq_refl (term838 A f)). Qed.
Lemma lem4780369 {A B : Type'} (f : nat -> A) : (term840 A B f) = (term840 A B f).
Proof. exact (MK_COMB (@lem4780368 A f) (@lem4780363 A B)). Qed.
Lemma lem4780374 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term493 A f x y) = (term493 A f x y).
Proof. exact (eq_refl (term493 A f x y)). Qed.
Lemma lem4780375 {A : Type'} (f : nat -> A) (x : nat) : (term481 A f x) = (term481 A f x).
Proof. exact (fun_ext (fun y : nat => @lem4780374 A f x y)). Qed.
Lemma lem4780376 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4780377 {A : Type'} (f : nat -> A) (x : nat) : (term524 A f x) = (term524 A f x).
Proof. exact (MK_COMB (@lem4780376) (@lem4780375 A f x)). Qed.
Lemma lem4780378 {A : Type'} (f : nat -> A) : (term526 A f) = (term526 A f).
Proof. exact (fun_ext (fun x : nat => @lem4780377 A f x)). Qed.
Lemma lem4780379 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4780380 {A : Type'} (f : nat -> A) : (term65 A f) = (term65 A f).
Proof. exact (MK_COMB (@lem4780379) (@lem4780378 A f)). Qed.
Lemma lem4780381 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780382 {A : Type'} (f : nat -> A) : (term841 A f) = (term841 A f).
Proof. exact (MK_COMB (@lem4780381) (@lem4780380 A f)). Qed.
Lemma lem4780383 {A B : Type'} (f : nat -> A) : (term843 A B f) = (term843 A B f).
Proof. exact (MK_COMB (@lem4780382 A f) (@lem4780369 A B f)). Qed.
Lemma lem4780384 {A : Type'} (f : nat -> A) (x : nat) (s : A -> Prop) : (term474 A f x s) = (term474 A f x s).
Proof. exact (eq_refl (term474 A f x s)). Qed.
Lemma lem4780385 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term475 A f s) = (term475 A f s).
Proof. exact (fun_ext (fun x : nat => @lem4780384 A f x s)). Qed.
Lemma lem4780386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4780387 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term66 A f s) = (term66 A f s).
Proof. exact (MK_COMB (@lem4780386) (@lem4780385 A f s)). Qed.
Lemma lem4780388 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4780389 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term844 A f s) = (term844 A f s).
Proof. exact (MK_COMB (@lem4780388) (@lem4780387 A f s)). Qed.
Lemma lem4780390 {A B : Type'} (s : A -> Prop) (f : nat -> A) : (term845 A B s f) = (term845 A B s f).
Proof. exact (MK_COMB (@lem4780389 A f s) (@lem4780383 A B f)). Qed.
Lemma lem4780391 {A B : Type'} (f : nat -> A) : (term847 A B f) = (term847 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4780390 A B s f)). Qed.
Lemma lem4780392 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4780393 {A B : Type'} (f : nat -> A) : (term849 A B f) = (term849 A B f).
Proof. exact (MK_COMB (@lem4780392 A) (@lem4780391 A B f)). Qed.
Lemma lem4780394 {A B : Type'} : (term851 A B) = (term851 A B).
Proof. exact (fun_ext (fun f : nat -> A => @lem4780393 A B f)). Qed.
Lemma lem4780395 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4780396 {A B : Type'} : (term853 A B) = (term853 A B).
Proof. exact (MK_COMB (@lem4780395 A) (@lem4780394 A B)). Qed.
Lemma lem4780597 {A B : Type'} : (term852 A B) = (term853 A B).
Proof. exact (TRANS (@lem4780220 A B) (@lem4780396 A B)). Qed.
Lemma lem4780598 {A B : Type'} : (term853 A B) = (term852 A B).
Proof. exact (SYM (@lem4780597 A B)). Qed.
Lemma lem4780600 {A : Type'} (f : nat -> A) (h1 : term65 A f) : term65 A f.
Proof. exact (h1). Qed.
Lemma lem4780603 {A : Type'} (h1 : term813 A) : term813 A.
Proof. exact (h1). Qed.
Lemma lem4780604 {A B : Type'} (h1 : term815 A B) : term815 A B.
Proof. exact (h1). Qed.
Lemma lem4780605 {A : Type'} (h1 : term814 A) : term814 A.
Proof. exact (h1). Qed.
Lemma lem4780606 {A : Type'} (h1 : term816 A) : term816 A.
Proof. exact (h1). Qed.
Lemma lem4780607 {B : Type'} (h1 : term816 B) : term816 B.
Proof. exact (h1). Qed.
Lemma lem4780627 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term493 A f x y) = (term604 A f x y).
Proof. exact (@lem17265 ((f x) = (f y)) (x = y)). Qed.
Lemma lem4780628 {A : Type'} (f : nat -> A) (x : nat) : (term481 A f x) = (term892 A f x).
Proof. exact (fun_ext (fun y : nat => @lem4780627 A f x y)). Qed.
Lemma lem4780629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4780630 {A : Type'} (f : nat -> A) (x : nat) : (term524 A f x) = (term893 A f x).
Proof. exact (MK_COMB (@lem4780629) (@lem4780628 A f x)). Qed.
Lemma lem4780631 {A : Type'} (f : nat -> A) : (term526 A f) = (term894 A f).
Proof. exact (fun_ext (fun x : nat => @lem4780630 A f x)). Qed.
Lemma lem4780632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4780689 {A : Type'} (f : nat -> A) : (term65 A f) = (term895 A f).
Proof. exact (MK_COMB (@lem4780632) (@lem4780631 A f)). Qed.
Lemma lem4780690 {A : Type'} (f : nat -> A) (h1 : term65 A f) : term895 A f.
Proof. exact (EQ_MP (@lem4780689 A f) (@lem4780600 A f h1)). Qed.
Lemma lem4780696 {A : Type'} (f : nat -> A) (h1 : term812 A f) : term812 A f.
Proof. exact (h1). Qed.
Lemma lem4780702 (h1 : @INFINITE nat (@UNIV nat)) : @INFINITE nat (@UNIV nat).
Proof. exact (h1). Qed.
Lemma lem4780709 {A : Type'} (f : A -> A) (x : A) (y : A) : (term896 A f x y) = (term897 A f x y).
Proof. exact (@lem17362 ((f x) = (f y)) (x = y)). Qed.
Lemma lem4780710 {A : Type'} (P : A -> Prop) : (term304 A P) = (term305 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4780711 {A : Type'} (f : A -> A) (x : A) : (term898 A f x) = (term899 A f x).
Proof. exact (@lem4780710 A (term885 A f x)). Qed.
Lemma lem4780712 {A : Type'} (f : A -> A) (x : A) (y : A) : (term900 A f x y) = (term884 A f x y).
Proof. exact (eq_refl (term900 A f x y)). Qed.
Lemma lem4780713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4780714 {A : Type'} (f : A -> A) (x : A) (y : A) : (term901 A f x y) = (term896 A f x y).
Proof. exact (MK_COMB (@lem4780713) (@lem4780712 A f x y)). Qed.
Lemma lem4780715 {A : Type'} (f : A -> A) (x : A) (y : A) : (term901 A f x y) = (term897 A f x y).
Proof. exact (TRANS (@lem4780714 A f x y) (@lem4780709 A f x y)). Qed.
Lemma lem4780716 {A : Type'} (f : A -> A) (x : A) : (term902 A f x) = (term903 A f x).
Proof. exact (fun_ext (fun y : A => @lem4780715 A f x y)). Qed.
Lemma lem4780717 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4780718 {A : Type'} (f : A -> A) (x : A) : (term899 A f x) = (term904 A f x).
Proof. exact (MK_COMB (@lem4780717 A) (@lem4780716 A f x)). Qed.
Lemma lem4780719 {A : Type'} (f : A -> A) (x : A) : (term898 A f x) = (term904 A f x).
Proof. exact (TRANS (@lem4780711 A f x) (@lem4780718 A f x)). Qed.
Lemma lem4780720 {A : Type'} (P : A -> Prop) : (term304 A P) = (term305 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4780721 {A : Type'} (f : A -> A) : (term905 A f) = (term906 A f).
Proof. exact (@lem4780720 A (term887 A f)). Qed.
Lemma lem4780722 {A : Type'} (f : A -> A) (x : A) : (term907 A f x) = (term886 A f x).
Proof. exact (eq_refl (term907 A f x)). Qed.
Lemma lem4780723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4780724 {A : Type'} (f : A -> A) (x : A) : (term908 A f x) = (term898 A f x).
Proof. exact (MK_COMB (@lem4780723) (@lem4780722 A f x)). Qed.
Lemma lem4780725 {A : Type'} (f : A -> A) (x : A) : (term908 A f x) = (term904 A f x).
Proof. exact (TRANS (@lem4780724 A f x) (@lem4780719 A f x)). Qed.
Lemma lem4780726 {A : Type'} (f : A -> A) : (term909 A f) = (term910 A f).
Proof. exact (fun_ext (fun x : A => @lem4780725 A f x)). Qed.
Lemma lem4780727 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4780728 {A : Type'} (f : A -> A) : (term906 A f) = (term911 A f).
Proof. exact (MK_COMB (@lem4780727 A) (@lem4780726 A f)). Qed.
Lemma lem4780729 {A : Type'} (f : A -> A) : (term905 A f) = (term911 A f).
Proof. exact (TRANS (@lem4780721 A f) (@lem4780728 A f)). Qed.
Lemma lem4780736 {A : Type'} (f : A -> A) (s : A -> Prop) : (term881 A f s) = (term912 A f s).
Proof. exact (@lem17265 (@INFINITE A s) (term913 A f s)). Qed.
Lemma lem4780737 {A : Type'} (f : A -> A) : (term882 A f) = (term914 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4780736 A f s)). Qed.
Lemma lem4780738 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4780739 {A : Type'} (f : A -> A) : (term883 A f) = (term915 A f).
Proof. exact (MK_COMB (@lem4780738 A) (@lem4780737 A f)). Qed.
Lemma lem4780740 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4780741 {A : Type'} (f : A -> A) : (term916 A f) = (term917 A f).
Proof. exact (MK_COMB (@lem4780740) (@lem4780729 A f)). Qed.
Lemma lem4780742 {A : Type'} (f : A -> A) : (term918 A f) = (term919 A f).
Proof. exact (MK_COMB (@lem4780741 A f) (@lem4780739 A f)). Qed.
Lemma lem4780743 {A : Type'} (f : A -> A) : (term890 A f) = (term918 A f).
Proof. exact (@lem17265 (term888 A f) (term883 A f)). Qed.
Lemma lem4780744 {A : Type'} (f : A -> A) : (term890 A f) = (term919 A f).
Proof. exact (TRANS (@lem4780743 A f) (@lem4780742 A f)). Qed.
Lemma lem4780745 {A : Type'} : (term891 A) = (term920 A).
Proof. exact (fun_ext (fun f : A -> A => @lem4780744 A f)). Qed.
Lemma lem4780746 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4780747 {A : Type'} : (term813 A) = (term921 A).
Proof. exact (MK_COMB (@lem4780746 A) (@lem4780745 A)). Qed.
Lemma lem4780898 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4780899 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (@lem4780898 A P Q). Qed.
Lemma lem4780900 {A : Type'} (f : A -> A) : (term924 A f) = (term925 A f).
Proof. exact (@lem4780899 A (term910 A f) (term915 A f)). Qed.
Lemma lem4780901 {A : Type'} (f : A -> A) (x : A) : (term926 A f x) = (term904 A f x).
Proof. exact (eq_refl (term926 A f x)). Qed.
Lemma lem4780902 {A : Type'} (f : A -> A) : (term927 A f) = (term910 A f).
Proof. exact (fun_ext (fun x : A => @lem4780901 A f x)). Qed.
Lemma lem4780903 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4780904 {A : Type'} (f : A -> A) : (term928 A f) = (term911 A f).
Proof. exact (MK_COMB (@lem4780903 A) (@lem4780902 A f)). Qed.
Lemma lem4780905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4780906 {A : Type'} (f : A -> A) : (term929 A f) = (term917 A f).
Proof. exact (MK_COMB (@lem4780905) (@lem4780904 A f)). Qed.
Lemma lem4780907 {A : Type'} (f : A -> A) : (term915 A f) = (term915 A f).
Proof. exact (eq_refl (term915 A f)). Qed.
Lemma lem4780908 {A : Type'} (f : A -> A) : (term924 A f) = (term919 A f).
Proof. exact (MK_COMB (@lem4780906 A f) (@lem4780907 A f)). Qed.
Lemma lem4780909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4780910 {A : Type'} (f : A -> A) : (term930 A f) = (term931 A f).
Proof. exact (MK_COMB (@lem4780909) (@lem4780908 A f)). Qed.
Lemma lem4780911 {A : Type'} (f : A -> A) (x : A) : (term926 A f x) = (term904 A f x).
Proof. exact (eq_refl (term926 A f x)). Qed.
Lemma lem4780912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4780913 {A : Type'} (f : A -> A) (x : A) : (term932 A f x) = (term933 A f x).
Proof. exact (MK_COMB (@lem4780912) (@lem4780911 A f x)). Qed.
Lemma lem4780914 {A : Type'} (f : A -> A) : (term915 A f) = (term915 A f).
Proof. exact (eq_refl (term915 A f)). Qed.
Lemma lem4780915 {A : Type'} (x : A) (f : A -> A) : (term934 A x f) = (term935 A x f).
Proof. exact (MK_COMB (@lem4780913 A f x) (@lem4780914 A f)). Qed.
Lemma lem4780916 {A : Type'} (f : A -> A) : (term936 A f) = (term937 A f).
Proof. exact (fun_ext (fun x : A => @lem4780915 A x f)). Qed.
Lemma lem4780917 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4780918 {A : Type'} (f : A -> A) : (term925 A f) = (term938 A f).
Proof. exact (MK_COMB (@lem4780917 A) (@lem4780916 A f)). Qed.
Lemma lem4780919 {A : Type'} (f : A -> A) : ((term924 A f) = (term925 A f)) = ((term919 A f) = (term938 A f)).
Proof. exact (MK_COMB (@lem4780910 A f) (@lem4780918 A f)). Qed.
Lemma lem4780920 {A : Type'} (f : A -> A) : (term919 A f) = (term938 A f).
Proof. exact (EQ_MP (@lem4780919 A f) (@lem4780900 A f)). Qed.
Lemma lem4780922 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4780923 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (@lem4780922 A P Q). Qed.
Lemma lem4780924 {A : Type'} (x : A) (f : A -> A) : (term939 A x f) = (term940 A x f).
Proof. exact (@lem4780923 A (term903 A f x) (term915 A f)). Qed.
Lemma lem4780925 {A : Type'} (f : A -> A) (x : A) (y : A) : (term941 A f x y) = (term897 A f x y).
Proof. exact (eq_refl (term941 A f x y)). Qed.
Lemma lem4780926 {A : Type'} (f : A -> A) (x : A) : (term942 A f x) = (term903 A f x).
Proof. exact (fun_ext (fun y : A => @lem4780925 A f x y)). Qed.
Lemma lem4780927 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4780928 {A : Type'} (f : A -> A) (x : A) : (term943 A f x) = (term904 A f x).
Proof. exact (MK_COMB (@lem4780927 A) (@lem4780926 A f x)). Qed.
Lemma lem4780929 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4780930 {A : Type'} (f : A -> A) (x : A) : (term944 A f x) = (term933 A f x).
Proof. exact (MK_COMB (@lem4780929) (@lem4780928 A f x)). Qed.
Lemma lem4780931 {A : Type'} (f : A -> A) : (term915 A f) = (term915 A f).
Proof. exact (eq_refl (term915 A f)). Qed.
Lemma lem4780932 {A : Type'} (x : A) (f : A -> A) : (term939 A x f) = (term935 A x f).
Proof. exact (MK_COMB (@lem4780930 A f x) (@lem4780931 A f)). Qed.
Lemma lem4780933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4780934 {A : Type'} (x : A) (f : A -> A) : (term945 A x f) = (term946 A x f).
Proof. exact (MK_COMB (@lem4780933) (@lem4780932 A x f)). Qed.
Lemma lem4780935 {A : Type'} (f : A -> A) (x : A) (y : A) : (term941 A f x y) = (term897 A f x y).
Proof. exact (eq_refl (term941 A f x y)). Qed.
Lemma lem4780936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4780937 {A : Type'} (f : A -> A) (x : A) (y : A) : (term947 A f x y) = (term948 A f x y).
Proof. exact (MK_COMB (@lem4780936) (@lem4780935 A f x y)). Qed.
Lemma lem4780938 {A : Type'} (f : A -> A) : (term915 A f) = (term915 A f).
Proof. exact (eq_refl (term915 A f)). Qed.
Lemma lem4780939 {A : Type'} (x : A) (y : A) (f : A -> A) : (term949 A x y f) = (term950 A x y f).
Proof. exact (MK_COMB (@lem4780937 A f x y) (@lem4780938 A f)). Qed.
Lemma lem4780940 {A : Type'} (x : A) (f : A -> A) : (term951 A x f) = (term952 A x f).
Proof. exact (fun_ext (fun y : A => @lem4780939 A x y f)). Qed.
Lemma lem4780941 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4780942 {A : Type'} (x : A) (f : A -> A) : (term940 A x f) = (term953 A x f).
Proof. exact (MK_COMB (@lem4780941 A) (@lem4780940 A x f)). Qed.
Lemma lem4780943 {A : Type'} (x : A) (f : A -> A) : ((term939 A x f) = (term940 A x f)) = ((term935 A x f) = (term953 A x f)).
Proof. exact (MK_COMB (@lem4780934 A x f) (@lem4780942 A x f)). Qed.
Lemma lem4780944 {A : Type'} (x : A) (f : A -> A) : (term935 A x f) = (term953 A x f).
Proof. exact (EQ_MP (@lem4780943 A x f) (@lem4780924 A x f)). Qed.
Lemma lem4780945 {A : Type'} (f : A -> A) : (term937 A f) = (term954 A f).
Proof. exact (fun_ext (fun x : A => @lem4780944 A x f)). Qed.
Lemma lem4780946 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4780947 {A : Type'} (f : A -> A) : (term938 A f) = (term955 A f).
Proof. exact (MK_COMB (@lem4780946 A) (@lem4780945 A f)). Qed.
Lemma lem4780948 {A : Type'} (f : A -> A) : (term919 A f) = (term955 A f).
Proof. exact (TRANS (@lem4780920 A f) (@lem4780947 A f)). Qed.
Lemma lem4780949 {A : Type'} : (term920 A) = (term956 A).
Proof. exact (fun_ext (fun f : A -> A => @lem4780948 A f)). Qed.
Lemma lem4780950 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4780951 {A : Type'} : (term921 A) = (term957 A).
Proof. exact (MK_COMB (@lem4780950 A) (@lem4780949 A)). Qed.
Lemma lem4780953 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4780954 {A : Type'} (P : type486 A) : (term958 A P) = (term959 A P).
Proof. exact (@lem4780953 (A -> A) A P). Qed.
Lemma lem4780955 {A : Type'} : (term960 A) = (term961 A).
Proof. exact (@lem4780954 A (term962 A)). Qed.
Lemma lem4780956 {A : Type'} (f : A -> A) : (term963 A f) = (term954 A f).
Proof. exact (eq_refl (term963 A f)). Qed.
Lemma lem4780957 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4780958 {A : Type'} (f : A -> A) (x : A) : (term964 A f x) = (term965 A f x).
Proof. exact (MK_COMB (@lem4780956 A f) (@lem4780957 A x)). Qed.
Lemma lem4780959 {A : Type'} (x : A) (f : A -> A) : (term965 A f x) = (term953 A x f).
Proof. exact (eq_refl (term965 A f x)). Qed.
Lemma lem4780960 {A : Type'} (x : A) (f : A -> A) : (term964 A f x) = (term953 A x f).
Proof. exact (TRANS (@lem4780958 A f x) (@lem4780959 A x f)). Qed.
Lemma lem4780961 {A : Type'} (f : A -> A) : (term966 A f) = (term954 A f).
Proof. exact (fun_ext (fun x : A => @lem4780960 A x f)). Qed.
Lemma lem4780962 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4780963 {A : Type'} (f : A -> A) : (term967 A f) = (term955 A f).
Proof. exact (MK_COMB (@lem4780962 A) (@lem4780961 A f)). Qed.
Lemma lem4780964 {A : Type'} : (term968 A) = (term956 A).
Proof. exact (fun_ext (fun f : A -> A => @lem4780963 A f)). Qed.
Lemma lem4780965 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4780966 {A : Type'} : (term960 A) = (term957 A).
Proof. exact (MK_COMB (@lem4780965 A) (@lem4780964 A)). Qed.
Lemma lem4780967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4780968 {A : Type'} : (term969 A) = (term970 A).
Proof. exact (MK_COMB (@lem4780967) (@lem4780966 A)). Qed.
Lemma lem4780969 {A : Type'} (f : A -> A) : (term963 A f) = (term954 A f).
Proof. exact (eq_refl (term963 A f)). Qed.
Lemma lem4780970 {A : Type'} (x : type487 A) (f : A -> A) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4780971 {A : Type'} (x : type487 A) (f : A -> A) : (term971 A x f) = (term972 A x f).
Proof. exact (MK_COMB (@lem4780969 A f) (@lem4780970 A x f)). Qed.
Lemma lem4780972 {A : Type'} (x : type487 A) (f : A -> A) : (term972 A x f) = (term973 A x f).
Proof. exact (eq_refl (term972 A x f)). Qed.
Lemma lem4780973 {A : Type'} (x : type487 A) (f : A -> A) : (term971 A x f) = (term973 A x f).
Proof. exact (TRANS (@lem4780971 A x f) (@lem4780972 A x f)). Qed.
Lemma lem4780974 {A : Type'} (x : type487 A) : (term974 A x) = (term975 A x).
Proof. exact (fun_ext (fun f : A -> A => @lem4780973 A x f)). Qed.
Lemma lem4780975 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4780976 {A : Type'} (x : type487 A) : (term976 A x) = (term977 A x).
Proof. exact (MK_COMB (@lem4780975 A) (@lem4780974 A x)). Qed.
Lemma lem4780977 {A : Type'} : (term978 A) = (term979 A).
Proof. exact (fun_ext (fun x : type487 A => @lem4780976 A x)). Qed.
Lemma lem4780978 {A : Type'} : (@ex ((A -> A) -> A)) = (@ex ((A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> A))). Qed.
Lemma lem4780979 {A : Type'} : (term961 A) = (term980 A).
Proof. exact (MK_COMB (@lem4780978 A) (@lem4780977 A)). Qed.
Lemma lem4780980 {A : Type'} : ((term960 A) = (term961 A)) = ((term957 A) = (term980 A)).
Proof. exact (MK_COMB (@lem4780968 A) (@lem4780979 A)). Qed.
Lemma lem4780981 {A : Type'} : (term957 A) = (term980 A).
Proof. exact (EQ_MP (@lem4780980 A) (@lem4780955 A)). Qed.
Lemma lem4780983 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4780984 {A : Type'} (P : type486 A) : (term958 A P) = (term959 A P).
Proof. exact (@lem4780983 (A -> A) A P). Qed.
Lemma lem4780985 {A : Type'} (x : type487 A) : (term981 A x) = (term982 A x).
Proof. exact (@lem4780984 A (term983 A x)). Qed.
Lemma lem4780986 {A : Type'} (x : type487 A) (f : A -> A) : (term984 A x f) = (term985 A x f).
Proof. exact (eq_refl (term984 A x f)). Qed.
Lemma lem4780987 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4780988 {A : Type'} (x : type487 A) (f : A -> A) (y : A) : (term986 A x f y) = (term987 A x f y).
Proof. exact (MK_COMB (@lem4780986 A x f) (@lem4780987 A y)). Qed.
Lemma lem4780989 {A : Type'} (x : type487 A) (y : A) (f : A -> A) : (term987 A x f y) = (term988 A x y f).
Proof. exact (eq_refl (term987 A x f y)). Qed.
Lemma lem4780990 {A : Type'} (x : type487 A) (y : A) (f : A -> A) : (term986 A x f y) = (term988 A x y f).
Proof. exact (TRANS (@lem4780988 A x f y) (@lem4780989 A x y f)). Qed.
Lemma lem4780991 {A : Type'} (x : type487 A) (f : A -> A) : (term989 A x f) = (term985 A x f).
Proof. exact (fun_ext (fun y : A => @lem4780990 A x y f)). Qed.
Lemma lem4780992 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4780993 {A : Type'} (x : type487 A) (f : A -> A) : (term990 A x f) = (term973 A x f).
Proof. exact (MK_COMB (@lem4780992 A) (@lem4780991 A x f)). Qed.
Lemma lem4780994 {A : Type'} (x : type487 A) : (term991 A x) = (term975 A x).
Proof. exact (fun_ext (fun f : A -> A => @lem4780993 A x f)). Qed.
Lemma lem4780995 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4780996 {A : Type'} (x : type487 A) : (term981 A x) = (term977 A x).
Proof. exact (MK_COMB (@lem4780995 A) (@lem4780994 A x)). Qed.
Lemma lem4780997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4780998 {A : Type'} (x : type487 A) : (term992 A x) = (term993 A x).
Proof. exact (MK_COMB (@lem4780997) (@lem4780996 A x)). Qed.
Lemma lem4780999 {A : Type'} (x : type487 A) (f : A -> A) : (term984 A x f) = (term985 A x f).
Proof. exact (eq_refl (term984 A x f)). Qed.
Lemma lem4781000 {A : Type'} (y : type487 A) (f : A -> A) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem4781001 {A : Type'} (x : type487 A) (y : type487 A) (f : A -> A) : (term994 A x y f) = (term995 A x y f).
Proof. exact (MK_COMB (@lem4780999 A x f) (@lem4781000 A y f)). Qed.
Lemma lem4781002 {A : Type'} (x : type487 A) (y : type487 A) (f : A -> A) : (term995 A x y f) = (term996 A x y f).
Proof. exact (eq_refl (term995 A x y f)). Qed.
Lemma lem4781003 {A : Type'} (x : type487 A) (y : type487 A) (f : A -> A) : (term994 A x y f) = (term996 A x y f).
Proof. exact (TRANS (@lem4781001 A x y f) (@lem4781002 A x y f)). Qed.
Lemma lem4781004 {A : Type'} (x : type487 A) (y : type487 A) : (term997 A x y) = (term998 A x y).
Proof. exact (fun_ext (fun f : A -> A => @lem4781003 A x y f)). Qed.
Lemma lem4781005 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4781006 {A : Type'} (x : type487 A) (y : type487 A) : (term999 A x y) = (term1000 A x y).
Proof. exact (MK_COMB (@lem4781005 A) (@lem4781004 A x y)). Qed.
Lemma lem4781007 {A : Type'} (x : type487 A) : (term1001 A x) = (term1002 A x).
Proof. exact (fun_ext (fun y : type487 A => @lem4781006 A x y)). Qed.
Lemma lem4781008 {A : Type'} : (@ex ((A -> A) -> A)) = (@ex ((A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> A))). Qed.
Lemma lem4781009 {A : Type'} (x : type487 A) : (term982 A x) = (term1003 A x).
Proof. exact (MK_COMB (@lem4781008 A) (@lem4781007 A x)). Qed.
Lemma lem4781010 {A : Type'} (x : type487 A) : ((term981 A x) = (term982 A x)) = ((term977 A x) = (term1003 A x)).
Proof. exact (MK_COMB (@lem4780998 A x) (@lem4781009 A x)). Qed.
Lemma lem4781011 {A : Type'} (x : type487 A) : (term977 A x) = (term1003 A x).
Proof. exact (EQ_MP (@lem4781010 A x) (@lem4780985 A x)). Qed.
Lemma lem4781012 {A : Type'} : (term979 A) = (term1004 A).
Proof. exact (fun_ext (fun x : type487 A => @lem4781011 A x)). Qed.
Lemma lem4781013 {A : Type'} : (@ex ((A -> A) -> A)) = (@ex ((A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> A))). Qed.
Lemma lem4781014 {A : Type'} : (term980 A) = (term1005 A).
Proof. exact (MK_COMB (@lem4781013 A) (@lem4781012 A)). Qed.
Lemma lem4781015 {A : Type'} : (term957 A) = (term1005 A).
Proof. exact (TRANS (@lem4780981 A) (@lem4781014 A)). Qed.
Lemma lem4781017 {A : Type'} : (term921 A) = (term1005 A).
Proof. exact (TRANS (@lem4780951 A) (@lem4781015 A)). Qed.
Lemma lem4781018 {A : Type'} : (term813 A) = (term1005 A).
Proof. exact (TRANS (@lem4780747 A) (@lem4781017 A)). Qed.
Lemma lem4781019 {A : Type'} (h1 : term813 A) : term1005 A.
Proof. exact (EQ_MP (@lem4781018 A) (@lem4780603 A h1)). Qed.
Lemma lem4781026 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term1006 A B f x y) = (term1007 A B f x y).
Proof. exact (@lem17362 ((f x) = (f y)) (x = y)). Qed.
Lemma lem4781027 {A : Type'} (P : A -> Prop) : (term304 A P) = (term305 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4781028 {A B : Type'} (f : A -> B) (x : A) : (term1008 A B f x) = (term1009 A B f x).
Proof. exact (@lem4781027 A (term874 A B f x)). Qed.
Lemma lem4781029 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term1010 A B f x y) = (term873 A B f x y).
Proof. exact (eq_refl (term1010 A B f x y)). Qed.
Lemma lem4781030 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4781031 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term1011 A B f x y) = (term1006 A B f x y).
Proof. exact (MK_COMB (@lem4781030) (@lem4781029 A B f x y)). Qed.
Lemma lem4781032 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term1011 A B f x y) = (term1007 A B f x y).
Proof. exact (TRANS (@lem4781031 A B f x y) (@lem4781026 A B f x y)). Qed.
Lemma lem4781033 {A B : Type'} (f : A -> B) (x : A) : (term1012 A B f x) = (term1013 A B f x).
Proof. exact (fun_ext (fun y : A => @lem4781032 A B f x y)). Qed.
Lemma lem4781034 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781035 {A B : Type'} (f : A -> B) (x : A) : (term1009 A B f x) = (term1014 A B f x).
Proof. exact (MK_COMB (@lem4781034 A) (@lem4781033 A B f x)). Qed.
Lemma lem4781036 {A B : Type'} (f : A -> B) (x : A) : (term1008 A B f x) = (term1014 A B f x).
Proof. exact (TRANS (@lem4781028 A B f x) (@lem4781035 A B f x)). Qed.
Lemma lem4781037 {A : Type'} (P : A -> Prop) : (term304 A P) = (term305 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4781038 {A B : Type'} (f : A -> B) : (term1015 A B f) = (term1016 A B f).
Proof. exact (@lem4781037 A (term876 A B f)). Qed.
Lemma lem4781039 {A B : Type'} (f : A -> B) (x : A) : (term1017 A B f x) = (term875 A B f x).
Proof. exact (eq_refl (term1017 A B f x)). Qed.
Lemma lem4781040 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4781041 {A B : Type'} (f : A -> B) (x : A) : (term1018 A B f x) = (term1008 A B f x).
Proof. exact (MK_COMB (@lem4781040) (@lem4781039 A B f x)). Qed.
Lemma lem4781042 {A B : Type'} (f : A -> B) (x : A) : (term1018 A B f x) = (term1014 A B f x).
Proof. exact (TRANS (@lem4781041 A B f x) (@lem4781036 A B f x)). Qed.
Lemma lem4781043 {A B : Type'} (f : A -> B) : (term1019 A B f) = (term1020 A B f).
Proof. exact (fun_ext (fun x : A => @lem4781042 A B f x)). Qed.
Lemma lem4781044 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781045 {A B : Type'} (f : A -> B) : (term1016 A B f) = (term1021 A B f).
Proof. exact (MK_COMB (@lem4781044 A) (@lem4781043 A B f)). Qed.
Lemma lem4781046 {A B : Type'} (f : A -> B) : (term1015 A B f) = (term1021 A B f).
Proof. exact (TRANS (@lem4781038 A B f) (@lem4781045 A B f)). Qed.
Lemma lem4781053 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term870 A B f s) = (term1022 A B f s).
Proof. exact (@lem17265 (@INFINITE A s) (term1023 A B f s)). Qed.
Lemma lem4781054 {A B : Type'} (f : A -> B) : (term871 A B f) = (term1024 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4781053 A B f s)). Qed.
Lemma lem4781055 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4781056 {A B : Type'} (f : A -> B) : (term872 A B f) = (term1025 A B f).
Proof. exact (MK_COMB (@lem4781055 A) (@lem4781054 A B f)). Qed.
Lemma lem4781057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781058 {A B : Type'} (f : A -> B) : (term1026 A B f) = (term1027 A B f).
Proof. exact (MK_COMB (@lem4781057) (@lem4781046 A B f)). Qed.
Lemma lem4781059 {A B : Type'} (f : A -> B) : (term1028 A B f) = (term1029 A B f).
Proof. exact (MK_COMB (@lem4781058 A B f) (@lem4781056 A B f)). Qed.
Lemma lem4781060 {A B : Type'} (f : A -> B) : (term879 A B f) = (term1028 A B f).
Proof. exact (@lem17265 (term877 A B f) (term872 A B f)). Qed.
Lemma lem4781061 {A B : Type'} (f : A -> B) : (term879 A B f) = (term1029 A B f).
Proof. exact (TRANS (@lem4781060 A B f) (@lem4781059 A B f)). Qed.
Lemma lem4781062 {A B : Type'} : (term880 A B) = (term1030 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4781061 A B f)). Qed.
Lemma lem4781063 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4781064 {A B : Type'} : (term815 A B) = (term1031 A B).
Proof. exact (MK_COMB (@lem4781063 A B) (@lem4781062 A B)). Qed.
Lemma lem4781215 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4781216 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (@lem4781215 A P Q). Qed.
Lemma lem4781217 {A B : Type'} (f : A -> B) : (term1032 A B f) = (term1033 A B f).
Proof. exact (@lem4781216 A (term1020 A B f) (term1025 A B f)). Qed.
Lemma lem4781218 {A B : Type'} (f : A -> B) (x : A) : (term1034 A B f x) = (term1014 A B f x).
Proof. exact (eq_refl (term1034 A B f x)). Qed.
Lemma lem4781219 {A B : Type'} (f : A -> B) : (term1035 A B f) = (term1020 A B f).
Proof. exact (fun_ext (fun x : A => @lem4781218 A B f x)). Qed.
Lemma lem4781220 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781221 {A B : Type'} (f : A -> B) : (term1036 A B f) = (term1021 A B f).
Proof. exact (MK_COMB (@lem4781220 A) (@lem4781219 A B f)). Qed.
Lemma lem4781222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781223 {A B : Type'} (f : A -> B) : (term1037 A B f) = (term1027 A B f).
Proof. exact (MK_COMB (@lem4781222) (@lem4781221 A B f)). Qed.
Lemma lem4781224 {A B : Type'} (f : A -> B) : (term1025 A B f) = (term1025 A B f).
Proof. exact (eq_refl (term1025 A B f)). Qed.
Lemma lem4781225 {A B : Type'} (f : A -> B) : (term1032 A B f) = (term1029 A B f).
Proof. exact (MK_COMB (@lem4781223 A B f) (@lem4781224 A B f)). Qed.
Lemma lem4781226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781227 {A B : Type'} (f : A -> B) : (term1038 A B f) = (term1039 A B f).
Proof. exact (MK_COMB (@lem4781226) (@lem4781225 A B f)). Qed.
Lemma lem4781228 {A B : Type'} (f : A -> B) (x : A) : (term1034 A B f x) = (term1014 A B f x).
Proof. exact (eq_refl (term1034 A B f x)). Qed.
Lemma lem4781229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781230 {A B : Type'} (f : A -> B) (x : A) : (term1040 A B f x) = (term1041 A B f x).
Proof. exact (MK_COMB (@lem4781229) (@lem4781228 A B f x)). Qed.
Lemma lem4781231 {A B : Type'} (f : A -> B) : (term1025 A B f) = (term1025 A B f).
Proof. exact (eq_refl (term1025 A B f)). Qed.
Lemma lem4781232 {A B : Type'} (x : A) (f : A -> B) : (term1042 A B x f) = (term1043 A B x f).
Proof. exact (MK_COMB (@lem4781230 A B f x) (@lem4781231 A B f)). Qed.
Lemma lem4781233 {A B : Type'} (f : A -> B) : (term1044 A B f) = (term1045 A B f).
Proof. exact (fun_ext (fun x : A => @lem4781232 A B x f)). Qed.
Lemma lem4781234 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781235 {A B : Type'} (f : A -> B) : (term1033 A B f) = (term1046 A B f).
Proof. exact (MK_COMB (@lem4781234 A) (@lem4781233 A B f)). Qed.
Lemma lem4781236 {A B : Type'} (f : A -> B) : ((term1032 A B f) = (term1033 A B f)) = ((term1029 A B f) = (term1046 A B f)).
Proof. exact (MK_COMB (@lem4781227 A B f) (@lem4781235 A B f)). Qed.
Lemma lem4781237 {A B : Type'} (f : A -> B) : (term1029 A B f) = (term1046 A B f).
Proof. exact (EQ_MP (@lem4781236 A B f) (@lem4781217 A B f)). Qed.
Lemma lem4781239 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4781240 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (@lem4781239 A P Q). Qed.
Lemma lem4781241 {A B : Type'} (x : A) (f : A -> B) : (term1047 A B x f) = (term1048 A B x f).
Proof. exact (@lem4781240 A (term1013 A B f x) (term1025 A B f)). Qed.
Lemma lem4781242 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term1049 A B f x y) = (term1007 A B f x y).
Proof. exact (eq_refl (term1049 A B f x y)). Qed.
Lemma lem4781243 {A B : Type'} (f : A -> B) (x : A) : (term1050 A B f x) = (term1013 A B f x).
Proof. exact (fun_ext (fun y : A => @lem4781242 A B f x y)). Qed.
Lemma lem4781244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781245 {A B : Type'} (f : A -> B) (x : A) : (term1051 A B f x) = (term1014 A B f x).
Proof. exact (MK_COMB (@lem4781244 A) (@lem4781243 A B f x)). Qed.
Lemma lem4781246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781247 {A B : Type'} (f : A -> B) (x : A) : (term1052 A B f x) = (term1041 A B f x).
Proof. exact (MK_COMB (@lem4781246) (@lem4781245 A B f x)). Qed.
Lemma lem4781248 {A B : Type'} (f : A -> B) : (term1025 A B f) = (term1025 A B f).
Proof. exact (eq_refl (term1025 A B f)). Qed.
Lemma lem4781249 {A B : Type'} (x : A) (f : A -> B) : (term1047 A B x f) = (term1043 A B x f).
Proof. exact (MK_COMB (@lem4781247 A B f x) (@lem4781248 A B f)). Qed.
Lemma lem4781250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781251 {A B : Type'} (x : A) (f : A -> B) : (term1053 A B x f) = (term1054 A B x f).
Proof. exact (MK_COMB (@lem4781250) (@lem4781249 A B x f)). Qed.
Lemma lem4781252 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term1049 A B f x y) = (term1007 A B f x y).
Proof. exact (eq_refl (term1049 A B f x y)). Qed.
Lemma lem4781253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781254 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term1055 A B f x y) = (term1056 A B f x y).
Proof. exact (MK_COMB (@lem4781253) (@lem4781252 A B f x y)). Qed.
Lemma lem4781255 {A B : Type'} (f : A -> B) : (term1025 A B f) = (term1025 A B f).
Proof. exact (eq_refl (term1025 A B f)). Qed.
Lemma lem4781256 {A B : Type'} (x : A) (y : A) (f : A -> B) : (term1057 A B x y f) = (term1058 A B x y f).
Proof. exact (MK_COMB (@lem4781254 A B f x y) (@lem4781255 A B f)). Qed.
Lemma lem4781257 {A B : Type'} (x : A) (f : A -> B) : (term1059 A B x f) = (term1060 A B x f).
Proof. exact (fun_ext (fun y : A => @lem4781256 A B x y f)). Qed.
Lemma lem4781258 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781259 {A B : Type'} (x : A) (f : A -> B) : (term1048 A B x f) = (term1061 A B x f).
Proof. exact (MK_COMB (@lem4781258 A) (@lem4781257 A B x f)). Qed.
Lemma lem4781260 {A B : Type'} (x : A) (f : A -> B) : ((term1047 A B x f) = (term1048 A B x f)) = ((term1043 A B x f) = (term1061 A B x f)).
Proof. exact (MK_COMB (@lem4781251 A B x f) (@lem4781259 A B x f)). Qed.
Lemma lem4781261 {A B : Type'} (x : A) (f : A -> B) : (term1043 A B x f) = (term1061 A B x f).
Proof. exact (EQ_MP (@lem4781260 A B x f) (@lem4781241 A B x f)). Qed.
Lemma lem4781262 {A B : Type'} (f : A -> B) : (term1045 A B f) = (term1062 A B f).
Proof. exact (fun_ext (fun x : A => @lem4781261 A B x f)). Qed.
Lemma lem4781263 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781264 {A B : Type'} (f : A -> B) : (term1046 A B f) = (term1063 A B f).
Proof. exact (MK_COMB (@lem4781263 A) (@lem4781262 A B f)). Qed.
Lemma lem4781265 {A B : Type'} (f : A -> B) : (term1029 A B f) = (term1063 A B f).
Proof. exact (TRANS (@lem4781237 A B f) (@lem4781264 A B f)). Qed.
Lemma lem4781266 {A B : Type'} : (term1030 A B) = (term1064 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4781265 A B f)). Qed.
Lemma lem4781267 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4781268 {A B : Type'} : (term1031 A B) = (term1065 A B).
Proof. exact (MK_COMB (@lem4781267 A B) (@lem4781266 A B)). Qed.
Lemma lem4781270 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4781271 {A B : Type'} (P : type551 A B) : (term1066 A B P) = (term1067 A B P).
Proof. exact (@lem4781270 (A -> B) A P). Qed.
Lemma lem4781272 {A B : Type'} : (term1068 A B) = (term1069 A B).
Proof. exact (@lem4781271 A B (term1070 A B)). Qed.
Lemma lem4781273 {A B : Type'} (f : A -> B) : (term1071 A B f) = (term1062 A B f).
Proof. exact (eq_refl (term1071 A B f)). Qed.
Lemma lem4781274 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4781275 {A B : Type'} (f : A -> B) (x : A) : (term1072 A B f x) = (term1073 A B f x).
Proof. exact (MK_COMB (@lem4781273 A B f) (@lem4781274 A x)). Qed.
Lemma lem4781276 {A B : Type'} (x : A) (f : A -> B) : (term1073 A B f x) = (term1061 A B x f).
Proof. exact (eq_refl (term1073 A B f x)). Qed.
Lemma lem4781277 {A B : Type'} (x : A) (f : A -> B) : (term1072 A B f x) = (term1061 A B x f).
Proof. exact (TRANS (@lem4781275 A B f x) (@lem4781276 A B x f)). Qed.
Lemma lem4781278 {A B : Type'} (f : A -> B) : (term1074 A B f) = (term1062 A B f).
Proof. exact (fun_ext (fun x : A => @lem4781277 A B x f)). Qed.
Lemma lem4781279 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781280 {A B : Type'} (f : A -> B) : (term1075 A B f) = (term1063 A B f).
Proof. exact (MK_COMB (@lem4781279 A) (@lem4781278 A B f)). Qed.
Lemma lem4781281 {A B : Type'} : (term1076 A B) = (term1064 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4781280 A B f)). Qed.
Lemma lem4781282 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4781283 {A B : Type'} : (term1068 A B) = (term1065 A B).
Proof. exact (MK_COMB (@lem4781282 A B) (@lem4781281 A B)). Qed.
Lemma lem4781284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781285 {A B : Type'} : (term1077 A B) = (term1078 A B).
Proof. exact (MK_COMB (@lem4781284) (@lem4781283 A B)). Qed.
Lemma lem4781286 {A B : Type'} (f : A -> B) : (term1071 A B f) = (term1062 A B f).
Proof. exact (eq_refl (term1071 A B f)). Qed.
Lemma lem4781287 {A B : Type'} (x : type569 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4781288 {A B : Type'} (x : type569 A B) (f : A -> B) : (term1079 A B x f) = (term1080 A B x f).
Proof. exact (MK_COMB (@lem4781286 A B f) (@lem4781287 A B x f)). Qed.
Lemma lem4781289 {A B : Type'} (x : type569 A B) (f : A -> B) : (term1080 A B x f) = (term1081 A B x f).
Proof. exact (eq_refl (term1080 A B x f)). Qed.
Lemma lem4781290 {A B : Type'} (x : type569 A B) (f : A -> B) : (term1079 A B x f) = (term1081 A B x f).
Proof. exact (TRANS (@lem4781288 A B x f) (@lem4781289 A B x f)). Qed.
Lemma lem4781291 {A B : Type'} (x : type569 A B) : (term1082 A B x) = (term1083 A B x).
Proof. exact (fun_ext (fun f : A -> B => @lem4781290 A B x f)). Qed.
Lemma lem4781292 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4781293 {A B : Type'} (x : type569 A B) : (term1084 A B x) = (term1085 A B x).
Proof. exact (MK_COMB (@lem4781292 A B) (@lem4781291 A B x)). Qed.
Lemma lem4781294 {A B : Type'} : (term1086 A B) = (term1087 A B).
Proof. exact (fun_ext (fun x : type569 A B => @lem4781293 A B x)). Qed.
Lemma lem4781295 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem4781296 {A B : Type'} : (term1069 A B) = (term1088 A B).
Proof. exact (MK_COMB (@lem4781295 A B) (@lem4781294 A B)). Qed.
Lemma lem4781297 {A B : Type'} : ((term1068 A B) = (term1069 A B)) = ((term1065 A B) = (term1088 A B)).
Proof. exact (MK_COMB (@lem4781285 A B) (@lem4781296 A B)). Qed.
Lemma lem4781298 {A B : Type'} : (term1065 A B) = (term1088 A B).
Proof. exact (EQ_MP (@lem4781297 A B) (@lem4781272 A B)). Qed.
Lemma lem4781300 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4781301 {A B : Type'} (P : type551 A B) : (term1066 A B P) = (term1067 A B P).
Proof. exact (@lem4781300 (A -> B) A P). Qed.
Lemma lem4781302 {A B : Type'} (x : type569 A B) : (term1089 A B x) = (term1090 A B x).
Proof. exact (@lem4781301 A B (term1091 A B x)). Qed.
Lemma lem4781303 {A B : Type'} (x : type569 A B) (f : A -> B) : (term1092 A B x f) = (term1093 A B x f).
Proof. exact (eq_refl (term1092 A B x f)). Qed.
Lemma lem4781304 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4781305 {A B : Type'} (x : type569 A B) (f : A -> B) (y : A) : (term1094 A B x f y) = (term1095 A B x f y).
Proof. exact (MK_COMB (@lem4781303 A B x f) (@lem4781304 A y)). Qed.
Lemma lem4781306 {A B : Type'} (x : type569 A B) (y : A) (f : A -> B) : (term1095 A B x f y) = (term1096 A B x y f).
Proof. exact (eq_refl (term1095 A B x f y)). Qed.
Lemma lem4781307 {A B : Type'} (x : type569 A B) (y : A) (f : A -> B) : (term1094 A B x f y) = (term1096 A B x y f).
Proof. exact (TRANS (@lem4781305 A B x f y) (@lem4781306 A B x y f)). Qed.
Lemma lem4781308 {A B : Type'} (x : type569 A B) (f : A -> B) : (term1097 A B x f) = (term1093 A B x f).
Proof. exact (fun_ext (fun y : A => @lem4781307 A B x y f)). Qed.
Lemma lem4781309 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781310 {A B : Type'} (x : type569 A B) (f : A -> B) : (term1098 A B x f) = (term1081 A B x f).
Proof. exact (MK_COMB (@lem4781309 A) (@lem4781308 A B x f)). Qed.
Lemma lem4781311 {A B : Type'} (x : type569 A B) : (term1099 A B x) = (term1083 A B x).
Proof. exact (fun_ext (fun f : A -> B => @lem4781310 A B x f)). Qed.
Lemma lem4781312 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4781313 {A B : Type'} (x : type569 A B) : (term1089 A B x) = (term1085 A B x).
Proof. exact (MK_COMB (@lem4781312 A B) (@lem4781311 A B x)). Qed.
Lemma lem4781314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781315 {A B : Type'} (x : type569 A B) : (term1100 A B x) = (term1101 A B x).
Proof. exact (MK_COMB (@lem4781314) (@lem4781313 A B x)). Qed.
Lemma lem4781316 {A B : Type'} (x : type569 A B) (f : A -> B) : (term1092 A B x f) = (term1093 A B x f).
Proof. exact (eq_refl (term1092 A B x f)). Qed.
Lemma lem4781317 {A B : Type'} (y : type569 A B) (f : A -> B) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem4781318 {A B : Type'} (x : type569 A B) (y : type569 A B) (f : A -> B) : (term1102 A B x y f) = (term1103 A B x y f).
Proof. exact (MK_COMB (@lem4781316 A B x f) (@lem4781317 A B y f)). Qed.
Lemma lem4781319 {A B : Type'} (x : type569 A B) (y : type569 A B) (f : A -> B) : (term1103 A B x y f) = (term1104 A B x y f).
Proof. exact (eq_refl (term1103 A B x y f)). Qed.
Lemma lem4781320 {A B : Type'} (x : type569 A B) (y : type569 A B) (f : A -> B) : (term1102 A B x y f) = (term1104 A B x y f).
Proof. exact (TRANS (@lem4781318 A B x y f) (@lem4781319 A B x y f)). Qed.
Lemma lem4781321 {A B : Type'} (x : type569 A B) (y : type569 A B) : (term1105 A B x y) = (term1106 A B x y).
Proof. exact (fun_ext (fun f : A -> B => @lem4781320 A B x y f)). Qed.
Lemma lem4781322 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4781323 {A B : Type'} (x : type569 A B) (y : type569 A B) : (term1107 A B x y) = (term1108 A B x y).
Proof. exact (MK_COMB (@lem4781322 A B) (@lem4781321 A B x y)). Qed.
Lemma lem4781324 {A B : Type'} (x : type569 A B) : (term1109 A B x) = (term1110 A B x).
Proof. exact (fun_ext (fun y : type569 A B => @lem4781323 A B x y)). Qed.
Lemma lem4781325 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem4781326 {A B : Type'} (x : type569 A B) : (term1090 A B x) = (term1111 A B x).
Proof. exact (MK_COMB (@lem4781325 A B) (@lem4781324 A B x)). Qed.
Lemma lem4781327 {A B : Type'} (x : type569 A B) : ((term1089 A B x) = (term1090 A B x)) = ((term1085 A B x) = (term1111 A B x)).
Proof. exact (MK_COMB (@lem4781315 A B x) (@lem4781326 A B x)). Qed.
Lemma lem4781328 {A B : Type'} (x : type569 A B) : (term1085 A B x) = (term1111 A B x).
Proof. exact (EQ_MP (@lem4781327 A B x) (@lem4781302 A B x)). Qed.
Lemma lem4781329 {A B : Type'} : (term1087 A B) = (term1112 A B).
Proof. exact (fun_ext (fun x : type569 A B => @lem4781328 A B x)). Qed.
Lemma lem4781330 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem4781331 {A B : Type'} : (term1088 A B) = (term1113 A B).
Proof. exact (MK_COMB (@lem4781330 A B) (@lem4781329 A B)). Qed.
Lemma lem4781332 {A B : Type'} : (term1065 A B) = (term1113 A B).
Proof. exact (TRANS (@lem4781298 A B) (@lem4781331 A B)). Qed.
Lemma lem4781334 {A B : Type'} : (term1031 A B) = (term1113 A B).
Proof. exact (TRANS (@lem4781268 A B) (@lem4781332 A B)). Qed.
Lemma lem4781335 {A B : Type'} : (term815 A B) = (term1113 A B).
Proof. exact (TRANS (@lem4781064 A B) (@lem4781334 A B)). Qed.
Lemma lem4781336 {A B : Type'} (h1 : term815 A B) : term1113 A B.
Proof. exact (EQ_MP (@lem4781335 A B) (@lem4780604 A B h1)). Qed.
Lemma lem4781343 {A : Type'} (f : A -> nat) (x : A) (y : A) : (term1114 A f x y) = (term1115 A f x y).
Proof. exact (@lem17362 ((f x) = (f y)) (x = y)). Qed.
Lemma lem4781344 {A : Type'} (P : A -> Prop) : (term304 A P) = (term305 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4781345 {A : Type'} (f : A -> nat) (x : A) : (term1116 A f x) = (term1117 A f x).
Proof. exact (@lem4781344 A (term863 A f x)). Qed.
Lemma lem4781346 {A : Type'} (f : A -> nat) (x : A) (y : A) : (term1118 A f x y) = (term862 A f x y).
Proof. exact (eq_refl (term1118 A f x y)). Qed.
Lemma lem4781347 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4781348 {A : Type'} (f : A -> nat) (x : A) (y : A) : (term1119 A f x y) = (term1114 A f x y).
Proof. exact (MK_COMB (@lem4781347) (@lem4781346 A f x y)). Qed.
Lemma lem4781349 {A : Type'} (f : A -> nat) (x : A) (y : A) : (term1119 A f x y) = (term1115 A f x y).
Proof. exact (TRANS (@lem4781348 A f x y) (@lem4781343 A f x y)). Qed.
Lemma lem4781350 {A : Type'} (f : A -> nat) (x : A) : (term1120 A f x) = (term1121 A f x).
Proof. exact (fun_ext (fun y : A => @lem4781349 A f x y)). Qed.
Lemma lem4781351 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781352 {A : Type'} (f : A -> nat) (x : A) : (term1117 A f x) = (term1122 A f x).
Proof. exact (MK_COMB (@lem4781351 A) (@lem4781350 A f x)). Qed.
Lemma lem4781353 {A : Type'} (f : A -> nat) (x : A) : (term1116 A f x) = (term1122 A f x).
Proof. exact (TRANS (@lem4781345 A f x) (@lem4781352 A f x)). Qed.
Lemma lem4781354 {A : Type'} (P : A -> Prop) : (term304 A P) = (term305 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4781355 {A : Type'} (f : A -> nat) : (term1123 A f) = (term1124 A f).
Proof. exact (@lem4781354 A (term865 A f)). Qed.
Lemma lem4781356 {A : Type'} (f : A -> nat) (x : A) : (term1125 A f x) = (term864 A f x).
Proof. exact (eq_refl (term1125 A f x)). Qed.
Lemma lem4781357 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4781358 {A : Type'} (f : A -> nat) (x : A) : (term1126 A f x) = (term1116 A f x).
Proof. exact (MK_COMB (@lem4781357) (@lem4781356 A f x)). Qed.
Lemma lem4781359 {A : Type'} (f : A -> nat) (x : A) : (term1126 A f x) = (term1122 A f x).
Proof. exact (TRANS (@lem4781358 A f x) (@lem4781353 A f x)). Qed.
Lemma lem4781360 {A : Type'} (f : A -> nat) : (term1127 A f) = (term1128 A f).
Proof. exact (fun_ext (fun x : A => @lem4781359 A f x)). Qed.
Lemma lem4781361 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781362 {A : Type'} (f : A -> nat) : (term1124 A f) = (term1129 A f).
Proof. exact (MK_COMB (@lem4781361 A) (@lem4781360 A f)). Qed.
Lemma lem4781363 {A : Type'} (f : A -> nat) : (term1123 A f) = (term1129 A f).
Proof. exact (TRANS (@lem4781355 A f) (@lem4781362 A f)). Qed.
Lemma lem4781370 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term859 A f s) = (term1130 A f s).
Proof. exact (@lem17265 (@INFINITE A s) (term1131 A f s)). Qed.
Lemma lem4781371 {A : Type'} (f : A -> nat) : (term860 A f) = (term1132 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4781370 A f s)). Qed.
Lemma lem4781372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4781373 {A : Type'} (f : A -> nat) : (term861 A f) = (term1133 A f).
Proof. exact (MK_COMB (@lem4781372 A) (@lem4781371 A f)). Qed.
Lemma lem4781374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781375 {A : Type'} (f : A -> nat) : (term1134 A f) = (term1135 A f).
Proof. exact (MK_COMB (@lem4781374) (@lem4781363 A f)). Qed.
Lemma lem4781376 {A : Type'} (f : A -> nat) : (term1136 A f) = (term1137 A f).
Proof. exact (MK_COMB (@lem4781375 A f) (@lem4781373 A f)). Qed.
Lemma lem4781377 {A : Type'} (f : A -> nat) : (term868 A f) = (term1136 A f).
Proof. exact (@lem17265 (term866 A f) (term861 A f)). Qed.
Lemma lem4781378 {A : Type'} (f : A -> nat) : (term868 A f) = (term1137 A f).
Proof. exact (TRANS (@lem4781377 A f) (@lem4781376 A f)). Qed.
Lemma lem4781379 {A : Type'} : (term869 A) = (term1138 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem4781378 A f)). Qed.
Lemma lem4781380 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4781381 {A : Type'} : (term814 A) = (term1139 A).
Proof. exact (MK_COMB (@lem4781380 A) (@lem4781379 A)). Qed.
Lemma lem4781532 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4781533 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (@lem4781532 A P Q). Qed.
Lemma lem4781534 {A : Type'} (f : A -> nat) : (term1140 A f) = (term1141 A f).
Proof. exact (@lem4781533 A (term1128 A f) (term1133 A f)). Qed.
Lemma lem4781535 {A : Type'} (f : A -> nat) (x : A) : (term1142 A f x) = (term1122 A f x).
Proof. exact (eq_refl (term1142 A f x)). Qed.
Lemma lem4781536 {A : Type'} (f : A -> nat) : (term1143 A f) = (term1128 A f).
Proof. exact (fun_ext (fun x : A => @lem4781535 A f x)). Qed.
Lemma lem4781537 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781538 {A : Type'} (f : A -> nat) : (term1144 A f) = (term1129 A f).
Proof. exact (MK_COMB (@lem4781537 A) (@lem4781536 A f)). Qed.
Lemma lem4781539 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781540 {A : Type'} (f : A -> nat) : (term1145 A f) = (term1135 A f).
Proof. exact (MK_COMB (@lem4781539) (@lem4781538 A f)). Qed.
Lemma lem4781541 {A : Type'} (f : A -> nat) : (term1133 A f) = (term1133 A f).
Proof. exact (eq_refl (term1133 A f)). Qed.
Lemma lem4781542 {A : Type'} (f : A -> nat) : (term1140 A f) = (term1137 A f).
Proof. exact (MK_COMB (@lem4781540 A f) (@lem4781541 A f)). Qed.
Lemma lem4781543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781544 {A : Type'} (f : A -> nat) : (term1146 A f) = (term1147 A f).
Proof. exact (MK_COMB (@lem4781543) (@lem4781542 A f)). Qed.
Lemma lem4781545 {A : Type'} (f : A -> nat) (x : A) : (term1142 A f x) = (term1122 A f x).
Proof. exact (eq_refl (term1142 A f x)). Qed.
Lemma lem4781546 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781547 {A : Type'} (f : A -> nat) (x : A) : (term1148 A f x) = (term1149 A f x).
Proof. exact (MK_COMB (@lem4781546) (@lem4781545 A f x)). Qed.
Lemma lem4781548 {A : Type'} (f : A -> nat) : (term1133 A f) = (term1133 A f).
Proof. exact (eq_refl (term1133 A f)). Qed.
Lemma lem4781549 {A : Type'} (x : A) (f : A -> nat) : (term1150 A x f) = (term1151 A x f).
Proof. exact (MK_COMB (@lem4781547 A f x) (@lem4781548 A f)). Qed.
Lemma lem4781550 {A : Type'} (f : A -> nat) : (term1152 A f) = (term1153 A f).
Proof. exact (fun_ext (fun x : A => @lem4781549 A x f)). Qed.
Lemma lem4781551 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781552 {A : Type'} (f : A -> nat) : (term1141 A f) = (term1154 A f).
Proof. exact (MK_COMB (@lem4781551 A) (@lem4781550 A f)). Qed.
Lemma lem4781553 {A : Type'} (f : A -> nat) : ((term1140 A f) = (term1141 A f)) = ((term1137 A f) = (term1154 A f)).
Proof. exact (MK_COMB (@lem4781544 A f) (@lem4781552 A f)). Qed.
Lemma lem4781554 {A : Type'} (f : A -> nat) : (term1137 A f) = (term1154 A f).
Proof. exact (EQ_MP (@lem4781553 A f) (@lem4781534 A f)). Qed.
Lemma lem4781556 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4781557 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (@lem4781556 A P Q). Qed.
Lemma lem4781558 {A : Type'} (x : A) (f : A -> nat) : (term1155 A x f) = (term1156 A x f).
Proof. exact (@lem4781557 A (term1121 A f x) (term1133 A f)). Qed.
Lemma lem4781559 {A : Type'} (f : A -> nat) (x : A) (y : A) : (term1157 A f x y) = (term1115 A f x y).
Proof. exact (eq_refl (term1157 A f x y)). Qed.
Lemma lem4781560 {A : Type'} (f : A -> nat) (x : A) : (term1158 A f x) = (term1121 A f x).
Proof. exact (fun_ext (fun y : A => @lem4781559 A f x y)). Qed.
Lemma lem4781561 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781562 {A : Type'} (f : A -> nat) (x : A) : (term1159 A f x) = (term1122 A f x).
Proof. exact (MK_COMB (@lem4781561 A) (@lem4781560 A f x)). Qed.
Lemma lem4781563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781564 {A : Type'} (f : A -> nat) (x : A) : (term1160 A f x) = (term1149 A f x).
Proof. exact (MK_COMB (@lem4781563) (@lem4781562 A f x)). Qed.
Lemma lem4781565 {A : Type'} (f : A -> nat) : (term1133 A f) = (term1133 A f).
Proof. exact (eq_refl (term1133 A f)). Qed.
Lemma lem4781566 {A : Type'} (x : A) (f : A -> nat) : (term1155 A x f) = (term1151 A x f).
Proof. exact (MK_COMB (@lem4781564 A f x) (@lem4781565 A f)). Qed.
Lemma lem4781567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781568 {A : Type'} (x : A) (f : A -> nat) : (term1161 A x f) = (term1162 A x f).
Proof. exact (MK_COMB (@lem4781567) (@lem4781566 A x f)). Qed.
Lemma lem4781569 {A : Type'} (f : A -> nat) (x : A) (y : A) : (term1157 A f x y) = (term1115 A f x y).
Proof. exact (eq_refl (term1157 A f x y)). Qed.
Lemma lem4781570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781571 {A : Type'} (f : A -> nat) (x : A) (y : A) : (term1163 A f x y) = (term1164 A f x y).
Proof. exact (MK_COMB (@lem4781570) (@lem4781569 A f x y)). Qed.
Lemma lem4781572 {A : Type'} (f : A -> nat) : (term1133 A f) = (term1133 A f).
Proof. exact (eq_refl (term1133 A f)). Qed.
Lemma lem4781573 {A : Type'} (x : A) (y : A) (f : A -> nat) : (term1165 A x y f) = (term1166 A x y f).
Proof. exact (MK_COMB (@lem4781571 A f x y) (@lem4781572 A f)). Qed.
Lemma lem4781574 {A : Type'} (x : A) (f : A -> nat) : (term1167 A x f) = (term1168 A x f).
Proof. exact (fun_ext (fun y : A => @lem4781573 A x y f)). Qed.
Lemma lem4781575 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781576 {A : Type'} (x : A) (f : A -> nat) : (term1156 A x f) = (term1169 A x f).
Proof. exact (MK_COMB (@lem4781575 A) (@lem4781574 A x f)). Qed.
Lemma lem4781577 {A : Type'} (x : A) (f : A -> nat) : ((term1155 A x f) = (term1156 A x f)) = ((term1151 A x f) = (term1169 A x f)).
Proof. exact (MK_COMB (@lem4781568 A x f) (@lem4781576 A x f)). Qed.
Lemma lem4781578 {A : Type'} (x : A) (f : A -> nat) : (term1151 A x f) = (term1169 A x f).
Proof. exact (EQ_MP (@lem4781577 A x f) (@lem4781558 A x f)). Qed.
Lemma lem4781579 {A : Type'} (f : A -> nat) : (term1153 A f) = (term1170 A f).
Proof. exact (fun_ext (fun x : A => @lem4781578 A x f)). Qed.
Lemma lem4781580 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781581 {A : Type'} (f : A -> nat) : (term1154 A f) = (term1171 A f).
Proof. exact (MK_COMB (@lem4781580 A) (@lem4781579 A f)). Qed.
Lemma lem4781582 {A : Type'} (f : A -> nat) : (term1137 A f) = (term1171 A f).
Proof. exact (TRANS (@lem4781554 A f) (@lem4781581 A f)). Qed.
Lemma lem4781583 {A : Type'} : (term1138 A) = (term1172 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem4781582 A f)). Qed.
Lemma lem4781584 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4781585 {A : Type'} : (term1139 A) = (term1173 A).
Proof. exact (MK_COMB (@lem4781584 A) (@lem4781583 A)). Qed.
Lemma lem4781587 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4781588 {A : Type'} (P : type699 A) : (term1174 A P) = (term1175 A P).
Proof. exact (@lem4781587 (A -> nat) A P). Qed.
Lemma lem4781589 {A : Type'} : (term1176 A) = (term1177 A).
Proof. exact (@lem4781588 A (term1178 A)). Qed.
Lemma lem4781590 {A : Type'} (f : A -> nat) : (term1179 A f) = (term1170 A f).
Proof. exact (eq_refl (term1179 A f)). Qed.
Lemma lem4781591 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4781592 {A : Type'} (f : A -> nat) (x : A) : (term1180 A f x) = (term1181 A f x).
Proof. exact (MK_COMB (@lem4781590 A f) (@lem4781591 A x)). Qed.
Lemma lem4781593 {A : Type'} (x : A) (f : A -> nat) : (term1181 A f x) = (term1169 A x f).
Proof. exact (eq_refl (term1181 A f x)). Qed.
Lemma lem4781594 {A : Type'} (x : A) (f : A -> nat) : (term1180 A f x) = (term1169 A x f).
Proof. exact (TRANS (@lem4781592 A f x) (@lem4781593 A x f)). Qed.
Lemma lem4781595 {A : Type'} (f : A -> nat) : (term1182 A f) = (term1170 A f).
Proof. exact (fun_ext (fun x : A => @lem4781594 A x f)). Qed.
Lemma lem4781596 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781597 {A : Type'} (f : A -> nat) : (term1183 A f) = (term1171 A f).
Proof. exact (MK_COMB (@lem4781596 A) (@lem4781595 A f)). Qed.
Lemma lem4781598 {A : Type'} : (term1184 A) = (term1172 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem4781597 A f)). Qed.
Lemma lem4781599 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4781600 {A : Type'} : (term1176 A) = (term1173 A).
Proof. exact (MK_COMB (@lem4781599 A) (@lem4781598 A)). Qed.
Lemma lem4781601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781602 {A : Type'} : (term1185 A) = (term1186 A).
Proof. exact (MK_COMB (@lem4781601) (@lem4781600 A)). Qed.
Lemma lem4781603 {A : Type'} (f : A -> nat) : (term1179 A f) = (term1170 A f).
Proof. exact (eq_refl (term1179 A f)). Qed.
Lemma lem4781604 {A : Type'} (x : type703 A) (f : A -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4781605 {A : Type'} (x : type703 A) (f : A -> nat) : (term1187 A x f) = (term1188 A x f).
Proof. exact (MK_COMB (@lem4781603 A f) (@lem4781604 A x f)). Qed.
Lemma lem4781606 {A : Type'} (x : type703 A) (f : A -> nat) : (term1188 A x f) = (term1189 A x f).
Proof. exact (eq_refl (term1188 A x f)). Qed.
Lemma lem4781607 {A : Type'} (x : type703 A) (f : A -> nat) : (term1187 A x f) = (term1189 A x f).
Proof. exact (TRANS (@lem4781605 A x f) (@lem4781606 A x f)). Qed.
Lemma lem4781608 {A : Type'} (x : type703 A) : (term1190 A x) = (term1191 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem4781607 A x f)). Qed.
Lemma lem4781609 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4781610 {A : Type'} (x : type703 A) : (term1192 A x) = (term1193 A x).
Proof. exact (MK_COMB (@lem4781609 A) (@lem4781608 A x)). Qed.
Lemma lem4781611 {A : Type'} : (term1194 A) = (term1195 A).
Proof. exact (fun_ext (fun x : type703 A => @lem4781610 A x)). Qed.
Lemma lem4781612 {A : Type'} : (@ex ((A -> nat) -> A)) = (@ex ((A -> nat) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> A))). Qed.
Lemma lem4781613 {A : Type'} : (term1177 A) = (term1196 A).
Proof. exact (MK_COMB (@lem4781612 A) (@lem4781611 A)). Qed.
Lemma lem4781614 {A : Type'} : ((term1176 A) = (term1177 A)) = ((term1173 A) = (term1196 A)).
Proof. exact (MK_COMB (@lem4781602 A) (@lem4781613 A)). Qed.
Lemma lem4781615 {A : Type'} : (term1173 A) = (term1196 A).
Proof. exact (EQ_MP (@lem4781614 A) (@lem4781589 A)). Qed.
Lemma lem4781617 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4781618 {A : Type'} (P : type699 A) : (term1174 A P) = (term1175 A P).
Proof. exact (@lem4781617 (A -> nat) A P). Qed.
Lemma lem4781619 {A : Type'} (x : type703 A) : (term1197 A x) = (term1198 A x).
Proof. exact (@lem4781618 A (term1199 A x)). Qed.
Lemma lem4781620 {A : Type'} (x : type703 A) (f : A -> nat) : (term1200 A x f) = (term1201 A x f).
Proof. exact (eq_refl (term1200 A x f)). Qed.
Lemma lem4781621 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4781622 {A : Type'} (x : type703 A) (f : A -> nat) (y : A) : (term1202 A x f y) = (term1203 A x f y).
Proof. exact (MK_COMB (@lem4781620 A x f) (@lem4781621 A y)). Qed.
Lemma lem4781623 {A : Type'} (x : type703 A) (y : A) (f : A -> nat) : (term1203 A x f y) = (term1204 A x y f).
Proof. exact (eq_refl (term1203 A x f y)). Qed.
Lemma lem4781624 {A : Type'} (x : type703 A) (y : A) (f : A -> nat) : (term1202 A x f y) = (term1204 A x y f).
Proof. exact (TRANS (@lem4781622 A x f y) (@lem4781623 A x y f)). Qed.
Lemma lem4781625 {A : Type'} (x : type703 A) (f : A -> nat) : (term1205 A x f) = (term1201 A x f).
Proof. exact (fun_ext (fun y : A => @lem4781624 A x y f)). Qed.
Lemma lem4781626 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4781627 {A : Type'} (x : type703 A) (f : A -> nat) : (term1206 A x f) = (term1189 A x f).
Proof. exact (MK_COMB (@lem4781626 A) (@lem4781625 A x f)). Qed.
Lemma lem4781628 {A : Type'} (x : type703 A) : (term1207 A x) = (term1191 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem4781627 A x f)). Qed.
Lemma lem4781629 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4781630 {A : Type'} (x : type703 A) : (term1197 A x) = (term1193 A x).
Proof. exact (MK_COMB (@lem4781629 A) (@lem4781628 A x)). Qed.
Lemma lem4781631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781632 {A : Type'} (x : type703 A) : (term1208 A x) = (term1209 A x).
Proof. exact (MK_COMB (@lem4781631) (@lem4781630 A x)). Qed.
Lemma lem4781633 {A : Type'} (x : type703 A) (f : A -> nat) : (term1200 A x f) = (term1201 A x f).
Proof. exact (eq_refl (term1200 A x f)). Qed.
Lemma lem4781634 {A : Type'} (y : type703 A) (f : A -> nat) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem4781635 {A : Type'} (x : type703 A) (y : type703 A) (f : A -> nat) : (term1210 A x y f) = (term1211 A x y f).
Proof. exact (MK_COMB (@lem4781633 A x f) (@lem4781634 A y f)). Qed.
Lemma lem4781636 {A : Type'} (x : type703 A) (y : type703 A) (f : A -> nat) : (term1211 A x y f) = (term1212 A x y f).
Proof. exact (eq_refl (term1211 A x y f)). Qed.
Lemma lem4781637 {A : Type'} (x : type703 A) (y : type703 A) (f : A -> nat) : (term1210 A x y f) = (term1212 A x y f).
Proof. exact (TRANS (@lem4781635 A x y f) (@lem4781636 A x y f)). Qed.
Lemma lem4781638 {A : Type'} (x : type703 A) (y : type703 A) : (term1213 A x y) = (term1214 A x y).
Proof. exact (fun_ext (fun f : A -> nat => @lem4781637 A x y f)). Qed.
Lemma lem4781639 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4781640 {A : Type'} (x : type703 A) (y : type703 A) : (term1215 A x y) = (term1216 A x y).
Proof. exact (MK_COMB (@lem4781639 A) (@lem4781638 A x y)). Qed.
Lemma lem4781641 {A : Type'} (x : type703 A) : (term1217 A x) = (term1218 A x).
Proof. exact (fun_ext (fun y : type703 A => @lem4781640 A x y)). Qed.
Lemma lem4781642 {A : Type'} : (@ex ((A -> nat) -> A)) = (@ex ((A -> nat) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> A))). Qed.
Lemma lem4781643 {A : Type'} (x : type703 A) : (term1198 A x) = (term1219 A x).
Proof. exact (MK_COMB (@lem4781642 A) (@lem4781641 A x)). Qed.
Lemma lem4781644 {A : Type'} (x : type703 A) : ((term1197 A x) = (term1198 A x)) = ((term1193 A x) = (term1219 A x)).
Proof. exact (MK_COMB (@lem4781632 A x) (@lem4781643 A x)). Qed.
Lemma lem4781645 {A : Type'} (x : type703 A) : (term1193 A x) = (term1219 A x).
Proof. exact (EQ_MP (@lem4781644 A x) (@lem4781619 A x)). Qed.
Lemma lem4781646 {A : Type'} : (term1195 A) = (term1220 A).
Proof. exact (fun_ext (fun x : type703 A => @lem4781645 A x)). Qed.
Lemma lem4781647 {A : Type'} : (@ex ((A -> nat) -> A)) = (@ex ((A -> nat) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> A))). Qed.
Lemma lem4781648 {A : Type'} : (term1196 A) = (term1221 A).
Proof. exact (MK_COMB (@lem4781647 A) (@lem4781646 A)). Qed.
Lemma lem4781649 {A : Type'} : (term1173 A) = (term1221 A).
Proof. exact (TRANS (@lem4781615 A) (@lem4781648 A)). Qed.
Lemma lem4781651 {A : Type'} : (term1139 A) = (term1221 A).
Proof. exact (TRANS (@lem4781585 A) (@lem4781649 A)). Qed.
Lemma lem4781652 {A : Type'} : (term814 A) = (term1221 A).
Proof. exact (TRANS (@lem4781381 A) (@lem4781651 A)). Qed.
Lemma lem4781653 {A : Type'} (h1 : term814 A) : term1221 A.
Proof. exact (EQ_MP (@lem4781652 A) (@lem4780605 A h1)). Qed.
Lemma lem4781660 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term602 A f x y) = (term603 A f x y).
Proof. exact (@lem17362 ((f x) = (f y)) (x = y)). Qed.
Lemma lem4781661 (P : nat -> Prop) : (term317 P) = (term318 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4781662 {A : Type'} (f : nat -> A) (x : nat) : (term1222 A f x) = (term1223 A f x).
Proof. exact (@lem4781661 (term481 A f x)). Qed.
Lemma lem4781663 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term492 A f x y) = (term493 A f x y).
Proof. exact (eq_refl (term492 A f x y)). Qed.
Lemma lem4781664 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4781665 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term1224 A f x y) = (term602 A f x y).
Proof. exact (MK_COMB (@lem4781664) (@lem4781663 A f x y)). Qed.
Lemma lem4781666 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term1224 A f x y) = (term603 A f x y).
Proof. exact (TRANS (@lem4781665 A f x y) (@lem4781660 A f x y)). Qed.
Lemma lem4781667 {A : Type'} (f : nat -> A) (x : nat) : (term1225 A f x) = (term1226 A f x).
Proof. exact (fun_ext (fun y : nat => @lem4781666 A f x y)). Qed.
Lemma lem4781668 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781669 {A : Type'} (f : nat -> A) (x : nat) : (term1223 A f x) = (term1227 A f x).
Proof. exact (MK_COMB (@lem4781668) (@lem4781667 A f x)). Qed.
Lemma lem4781670 {A : Type'} (f : nat -> A) (x : nat) : (term1222 A f x) = (term1227 A f x).
Proof. exact (TRANS (@lem4781662 A f x) (@lem4781669 A f x)). Qed.
Lemma lem4781671 (P : nat -> Prop) : (term317 P) = (term318 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4781672 {A : Type'} (f : nat -> A) : (term1228 A f) = (term1229 A f).
Proof. exact (@lem4781671 (term526 A f)). Qed.
Lemma lem4781673 {A : Type'} (f : nat -> A) (x : nat) : (term1230 A f x) = (term524 A f x).
Proof. exact (eq_refl (term1230 A f x)). Qed.
Lemma lem4781674 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4781675 {A : Type'} (f : nat -> A) (x : nat) : (term1231 A f x) = (term1222 A f x).
Proof. exact (MK_COMB (@lem4781674) (@lem4781673 A f x)). Qed.
Lemma lem4781676 {A : Type'} (f : nat -> A) (x : nat) : (term1231 A f x) = (term1227 A f x).
Proof. exact (TRANS (@lem4781675 A f x) (@lem4781670 A f x)). Qed.
Lemma lem4781677 {A : Type'} (f : nat -> A) : (term1232 A f) = (term1233 A f).
Proof. exact (fun_ext (fun x : nat => @lem4781676 A f x)). Qed.
Lemma lem4781678 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781679 {A : Type'} (f : nat -> A) : (term1229 A f) = (term1234 A f).
Proof. exact (MK_COMB (@lem4781678) (@lem4781677 A f)). Qed.
Lemma lem4781680 {A : Type'} (f : nat -> A) : (term1228 A f) = (term1234 A f).
Proof. exact (TRANS (@lem4781672 A f) (@lem4781679 A f)). Qed.
Lemma lem4781687 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term854 A f s) = (term1235 A f s).
Proof. exact (@lem17265 (@INFINITE nat s) (term1236 A f s)). Qed.
Lemma lem4781688 {A : Type'} (f : nat -> A) : (term855 A f) = (term1237 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4781687 A f s)). Qed.
Lemma lem4781689 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4781690 {A : Type'} (f : nat -> A) : (term856 A f) = (term1238 A f).
Proof. exact (MK_COMB (@lem4781689) (@lem4781688 A f)). Qed.
Lemma lem4781691 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781692 {A : Type'} (f : nat -> A) : (term1239 A f) = (term1240 A f).
Proof. exact (MK_COMB (@lem4781691) (@lem4781680 A f)). Qed.
Lemma lem4781693 {A : Type'} (f : nat -> A) : (term1241 A f) = (term1242 A f).
Proof. exact (MK_COMB (@lem4781692 A f) (@lem4781690 A f)). Qed.
Lemma lem4781694 {A : Type'} (f : nat -> A) : (term857 A f) = (term1241 A f).
Proof. exact (@lem17265 (term65 A f) (term856 A f)). Qed.
Lemma lem4781695 {A : Type'} (f : nat -> A) : (term857 A f) = (term1242 A f).
Proof. exact (TRANS (@lem4781694 A f) (@lem4781693 A f)). Qed.
Lemma lem4781696 {A : Type'} : (term858 A) = (term1243 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem4781695 A f)). Qed.
Lemma lem4781697 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4781698 {A : Type'} : (term816 A) = (term1244 A).
Proof. exact (MK_COMB (@lem4781697 A) (@lem4781696 A)). Qed.
Lemma lem4781849 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4781850 (P : nat -> Prop) (Q : Prop) : (term1245 P Q) = (term1246 P Q).
Proof. exact (@lem4781849 nat P Q). Qed.
Lemma lem4781851 {A : Type'} (f : nat -> A) : (term1247 A f) = (term1248 A f).
Proof. exact (@lem4781850 (term1233 A f) (term1238 A f)). Qed.
Lemma lem4781852 {A : Type'} (f : nat -> A) (x : nat) : (term1249 A f x) = (term1227 A f x).
Proof. exact (eq_refl (term1249 A f x)). Qed.
Lemma lem4781853 {A : Type'} (f : nat -> A) : (term1250 A f) = (term1233 A f).
Proof. exact (fun_ext (fun x : nat => @lem4781852 A f x)). Qed.
Lemma lem4781854 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781855 {A : Type'} (f : nat -> A) : (term1251 A f) = (term1234 A f).
Proof. exact (MK_COMB (@lem4781854) (@lem4781853 A f)). Qed.
Lemma lem4781856 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781857 {A : Type'} (f : nat -> A) : (term1252 A f) = (term1240 A f).
Proof. exact (MK_COMB (@lem4781856) (@lem4781855 A f)). Qed.
Lemma lem4781858 {A : Type'} (f : nat -> A) : (term1238 A f) = (term1238 A f).
Proof. exact (eq_refl (term1238 A f)). Qed.
Lemma lem4781859 {A : Type'} (f : nat -> A) : (term1247 A f) = (term1242 A f).
Proof. exact (MK_COMB (@lem4781857 A f) (@lem4781858 A f)). Qed.
Lemma lem4781860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781861 {A : Type'} (f : nat -> A) : (term1253 A f) = (term1254 A f).
Proof. exact (MK_COMB (@lem4781860) (@lem4781859 A f)). Qed.
Lemma lem4781862 {A : Type'} (f : nat -> A) (x : nat) : (term1249 A f x) = (term1227 A f x).
Proof. exact (eq_refl (term1249 A f x)). Qed.
Lemma lem4781863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781864 {A : Type'} (f : nat -> A) (x : nat) : (term1255 A f x) = (term1256 A f x).
Proof. exact (MK_COMB (@lem4781863) (@lem4781862 A f x)). Qed.
Lemma lem4781865 {A : Type'} (f : nat -> A) : (term1238 A f) = (term1238 A f).
Proof. exact (eq_refl (term1238 A f)). Qed.
Lemma lem4781866 {A : Type'} (x : nat) (f : nat -> A) : (term1257 A x f) = (term1258 A x f).
Proof. exact (MK_COMB (@lem4781864 A f x) (@lem4781865 A f)). Qed.
Lemma lem4781867 {A : Type'} (f : nat -> A) : (term1259 A f) = (term1260 A f).
Proof. exact (fun_ext (fun x : nat => @lem4781866 A x f)). Qed.
Lemma lem4781868 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781869 {A : Type'} (f : nat -> A) : (term1248 A f) = (term1261 A f).
Proof. exact (MK_COMB (@lem4781868) (@lem4781867 A f)). Qed.
Lemma lem4781870 {A : Type'} (f : nat -> A) : ((term1247 A f) = (term1248 A f)) = ((term1242 A f) = (term1261 A f)).
Proof. exact (MK_COMB (@lem4781861 A f) (@lem4781869 A f)). Qed.
Lemma lem4781871 {A : Type'} (f : nat -> A) : (term1242 A f) = (term1261 A f).
Proof. exact (EQ_MP (@lem4781870 A f) (@lem4781851 A f)). Qed.
Lemma lem4781873 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4781874 (P : nat -> Prop) (Q : Prop) : (term1245 P Q) = (term1246 P Q).
Proof. exact (@lem4781873 nat P Q). Qed.
Lemma lem4781875 {A : Type'} (x : nat) (f : nat -> A) : (term1262 A x f) = (term1263 A x f).
Proof. exact (@lem4781874 (term1226 A f x) (term1238 A f)). Qed.
Lemma lem4781876 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term1264 A f x y) = (term603 A f x y).
Proof. exact (eq_refl (term1264 A f x y)). Qed.
Lemma lem4781877 {A : Type'} (f : nat -> A) (x : nat) : (term1265 A f x) = (term1226 A f x).
Proof. exact (fun_ext (fun y : nat => @lem4781876 A f x y)). Qed.
Lemma lem4781878 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781879 {A : Type'} (f : nat -> A) (x : nat) : (term1266 A f x) = (term1227 A f x).
Proof. exact (MK_COMB (@lem4781878) (@lem4781877 A f x)). Qed.
Lemma lem4781880 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781881 {A : Type'} (f : nat -> A) (x : nat) : (term1267 A f x) = (term1256 A f x).
Proof. exact (MK_COMB (@lem4781880) (@lem4781879 A f x)). Qed.
Lemma lem4781882 {A : Type'} (f : nat -> A) : (term1238 A f) = (term1238 A f).
Proof. exact (eq_refl (term1238 A f)). Qed.
Lemma lem4781883 {A : Type'} (x : nat) (f : nat -> A) : (term1262 A x f) = (term1258 A x f).
Proof. exact (MK_COMB (@lem4781881 A f x) (@lem4781882 A f)). Qed.
Lemma lem4781884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781885 {A : Type'} (x : nat) (f : nat -> A) : (term1268 A x f) = (term1269 A x f).
Proof. exact (MK_COMB (@lem4781884) (@lem4781883 A x f)). Qed.
Lemma lem4781886 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term1264 A f x y) = (term603 A f x y).
Proof. exact (eq_refl (term1264 A f x y)). Qed.
Lemma lem4781887 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4781888 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term1270 A f x y) = (term1271 A f x y).
Proof. exact (MK_COMB (@lem4781887) (@lem4781886 A f x y)). Qed.
Lemma lem4781889 {A : Type'} (f : nat -> A) : (term1238 A f) = (term1238 A f).
Proof. exact (eq_refl (term1238 A f)). Qed.
Lemma lem4781890 {A : Type'} (x : nat) (y : nat) (f : nat -> A) : (term1272 A x y f) = (term1273 A x y f).
Proof. exact (MK_COMB (@lem4781888 A f x y) (@lem4781889 A f)). Qed.
Lemma lem4781891 {A : Type'} (x : nat) (f : nat -> A) : (term1274 A x f) = (term1275 A x f).
Proof. exact (fun_ext (fun y : nat => @lem4781890 A x y f)). Qed.
Lemma lem4781892 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781893 {A : Type'} (x : nat) (f : nat -> A) : (term1263 A x f) = (term1276 A x f).
Proof. exact (MK_COMB (@lem4781892) (@lem4781891 A x f)). Qed.
Lemma lem4781894 {A : Type'} (x : nat) (f : nat -> A) : ((term1262 A x f) = (term1263 A x f)) = ((term1258 A x f) = (term1276 A x f)).
Proof. exact (MK_COMB (@lem4781885 A x f) (@lem4781893 A x f)). Qed.
Lemma lem4781895 {A : Type'} (x : nat) (f : nat -> A) : (term1258 A x f) = (term1276 A x f).
Proof. exact (EQ_MP (@lem4781894 A x f) (@lem4781875 A x f)). Qed.
Lemma lem4781896 {A : Type'} (f : nat -> A) : (term1260 A f) = (term1277 A f).
Proof. exact (fun_ext (fun x : nat => @lem4781895 A x f)). Qed.
Lemma lem4781897 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781898 {A : Type'} (f : nat -> A) : (term1261 A f) = (term1278 A f).
Proof. exact (MK_COMB (@lem4781897) (@lem4781896 A f)). Qed.
Lemma lem4781899 {A : Type'} (f : nat -> A) : (term1242 A f) = (term1278 A f).
Proof. exact (TRANS (@lem4781871 A f) (@lem4781898 A f)). Qed.
Lemma lem4781900 {A : Type'} : (term1243 A) = (term1279 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem4781899 A f)). Qed.
Lemma lem4781901 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4781902 {A : Type'} : (term1244 A) = (term1280 A).
Proof. exact (MK_COMB (@lem4781901 A) (@lem4781900 A)). Qed.
Lemma lem4781904 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4781905 {A : Type'} (P : type973 A) : (term1281 A P) = (term1282 A P).
Proof. exact (@lem4781904 (nat -> A) nat P). Qed.
Lemma lem4781906 {A : Type'} : (term1283 A) = (term1284 A).
Proof. exact (@lem4781905 A (term1285 A)). Qed.
Lemma lem4781907 {A : Type'} (f : nat -> A) : (term1286 A f) = (term1277 A f).
Proof. exact (eq_refl (term1286 A f)). Qed.
Lemma lem4781908 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4781909 {A : Type'} (f : nat -> A) (x : nat) : (term1287 A f x) = (term1288 A f x).
Proof. exact (MK_COMB (@lem4781907 A f) (@lem4781908 x)). Qed.
Lemma lem4781910 {A : Type'} (x : nat) (f : nat -> A) : (term1288 A f x) = (term1276 A x f).
Proof. exact (eq_refl (term1288 A f x)). Qed.
Lemma lem4781911 {A : Type'} (x : nat) (f : nat -> A) : (term1287 A f x) = (term1276 A x f).
Proof. exact (TRANS (@lem4781909 A f x) (@lem4781910 A x f)). Qed.
Lemma lem4781912 {A : Type'} (f : nat -> A) : (term1289 A f) = (term1277 A f).
Proof. exact (fun_ext (fun x : nat => @lem4781911 A x f)). Qed.
Lemma lem4781913 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781914 {A : Type'} (f : nat -> A) : (term1290 A f) = (term1278 A f).
Proof. exact (MK_COMB (@lem4781913) (@lem4781912 A f)). Qed.
Lemma lem4781915 {A : Type'} : (term1291 A) = (term1279 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem4781914 A f)). Qed.
Lemma lem4781916 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4781917 {A : Type'} : (term1283 A) = (term1280 A).
Proof. exact (MK_COMB (@lem4781916 A) (@lem4781915 A)). Qed.
Lemma lem4781918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781919 {A : Type'} : (term1292 A) = (term1293 A).
Proof. exact (MK_COMB (@lem4781918) (@lem4781917 A)). Qed.
Lemma lem4781920 {A : Type'} (f : nat -> A) : (term1286 A f) = (term1277 A f).
Proof. exact (eq_refl (term1286 A f)). Qed.
Lemma lem4781921 {A : Type'} (x : type977 A) (f : nat -> A) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4781922 {A : Type'} (x : type977 A) (f : nat -> A) : (term1294 A x f) = (term1295 A x f).
Proof. exact (MK_COMB (@lem4781920 A f) (@lem4781921 A x f)). Qed.
Lemma lem4781923 {A : Type'} (x : type977 A) (f : nat -> A) : (term1295 A x f) = (term1296 A x f).
Proof. exact (eq_refl (term1295 A x f)). Qed.
Lemma lem4781924 {A : Type'} (x : type977 A) (f : nat -> A) : (term1294 A x f) = (term1296 A x f).
Proof. exact (TRANS (@lem4781922 A x f) (@lem4781923 A x f)). Qed.
Lemma lem4781925 {A : Type'} (x : type977 A) : (term1297 A x) = (term1298 A x).
Proof. exact (fun_ext (fun f : nat -> A => @lem4781924 A x f)). Qed.
Lemma lem4781926 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4781927 {A : Type'} (x : type977 A) : (term1299 A x) = (term1300 A x).
Proof. exact (MK_COMB (@lem4781926 A) (@lem4781925 A x)). Qed.
Lemma lem4781928 {A : Type'} : (term1301 A) = (term1302 A).
Proof. exact (fun_ext (fun x : type977 A => @lem4781927 A x)). Qed.
Lemma lem4781929 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem4781930 {A : Type'} : (term1284 A) = (term1303 A).
Proof. exact (MK_COMB (@lem4781929 A) (@lem4781928 A)). Qed.
Lemma lem4781931 {A : Type'} : ((term1283 A) = (term1284 A)) = ((term1280 A) = (term1303 A)).
Proof. exact (MK_COMB (@lem4781919 A) (@lem4781930 A)). Qed.
Lemma lem4781932 {A : Type'} : (term1280 A) = (term1303 A).
Proof. exact (EQ_MP (@lem4781931 A) (@lem4781906 A)). Qed.
Lemma lem4781934 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4781935 {A : Type'} (P : type973 A) : (term1281 A P) = (term1282 A P).
Proof. exact (@lem4781934 (nat -> A) nat P). Qed.
Lemma lem4781936 {A : Type'} (x : type977 A) : (term1304 A x) = (term1305 A x).
Proof. exact (@lem4781935 A (term1306 A x)). Qed.
Lemma lem4781937 {A : Type'} (x : type977 A) (f : nat -> A) : (term1307 A x f) = (term1308 A x f).
Proof. exact (eq_refl (term1307 A x f)). Qed.
Lemma lem4781938 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4781939 {A : Type'} (x : type977 A) (f : nat -> A) (y : nat) : (term1309 A x f y) = (term1310 A x f y).
Proof. exact (MK_COMB (@lem4781937 A x f) (@lem4781938 y)). Qed.
Lemma lem4781940 {A : Type'} (x : type977 A) (y : nat) (f : nat -> A) : (term1310 A x f y) = (term1311 A x y f).
Proof. exact (eq_refl (term1310 A x f y)). Qed.
Lemma lem4781941 {A : Type'} (x : type977 A) (y : nat) (f : nat -> A) : (term1309 A x f y) = (term1311 A x y f).
Proof. exact (TRANS (@lem4781939 A x f y) (@lem4781940 A x y f)). Qed.
Lemma lem4781942 {A : Type'} (x : type977 A) (f : nat -> A) : (term1312 A x f) = (term1308 A x f).
Proof. exact (fun_ext (fun y : nat => @lem4781941 A x y f)). Qed.
Lemma lem4781943 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781944 {A : Type'} (x : type977 A) (f : nat -> A) : (term1313 A x f) = (term1296 A x f).
Proof. exact (MK_COMB (@lem4781943) (@lem4781942 A x f)). Qed.
Lemma lem4781945 {A : Type'} (x : type977 A) : (term1314 A x) = (term1298 A x).
Proof. exact (fun_ext (fun f : nat -> A => @lem4781944 A x f)). Qed.
Lemma lem4781946 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4781947 {A : Type'} (x : type977 A) : (term1304 A x) = (term1300 A x).
Proof. exact (MK_COMB (@lem4781946 A) (@lem4781945 A x)). Qed.
Lemma lem4781948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4781949 {A : Type'} (x : type977 A) : (term1315 A x) = (term1316 A x).
Proof. exact (MK_COMB (@lem4781948) (@lem4781947 A x)). Qed.
Lemma lem4781950 {A : Type'} (x : type977 A) (f : nat -> A) : (term1307 A x f) = (term1308 A x f).
Proof. exact (eq_refl (term1307 A x f)). Qed.
Lemma lem4781951 {A : Type'} (y : type977 A) (f : nat -> A) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem4781952 {A : Type'} (x : type977 A) (y : type977 A) (f : nat -> A) : (term1317 A x y f) = (term1318 A x y f).
Proof. exact (MK_COMB (@lem4781950 A x f) (@lem4781951 A y f)). Qed.
Lemma lem4781953 {A : Type'} (x : type977 A) (y : type977 A) (f : nat -> A) : (term1318 A x y f) = (term1319 A x y f).
Proof. exact (eq_refl (term1318 A x y f)). Qed.
Lemma lem4781954 {A : Type'} (x : type977 A) (y : type977 A) (f : nat -> A) : (term1317 A x y f) = (term1319 A x y f).
Proof. exact (TRANS (@lem4781952 A x y f) (@lem4781953 A x y f)). Qed.
Lemma lem4781955 {A : Type'} (x : type977 A) (y : type977 A) : (term1320 A x y) = (term1321 A x y).
Proof. exact (fun_ext (fun f : nat -> A => @lem4781954 A x y f)). Qed.
Lemma lem4781956 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4781957 {A : Type'} (x : type977 A) (y : type977 A) : (term1322 A x y) = (term1323 A x y).
Proof. exact (MK_COMB (@lem4781956 A) (@lem4781955 A x y)). Qed.
Lemma lem4781958 {A : Type'} (x : type977 A) : (term1324 A x) = (term1325 A x).
Proof. exact (fun_ext (fun y : type977 A => @lem4781957 A x y)). Qed.
Lemma lem4781959 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem4781960 {A : Type'} (x : type977 A) : (term1305 A x) = (term1326 A x).
Proof. exact (MK_COMB (@lem4781959 A) (@lem4781958 A x)). Qed.
Lemma lem4781961 {A : Type'} (x : type977 A) : ((term1304 A x) = (term1305 A x)) = ((term1300 A x) = (term1326 A x)).
Proof. exact (MK_COMB (@lem4781949 A x) (@lem4781960 A x)). Qed.
Lemma lem4781962 {A : Type'} (x : type977 A) : (term1300 A x) = (term1326 A x).
Proof. exact (EQ_MP (@lem4781961 A x) (@lem4781936 A x)). Qed.
Lemma lem4781963 {A : Type'} : (term1302 A) = (term1327 A).
Proof. exact (fun_ext (fun x : type977 A => @lem4781962 A x)). Qed.
Lemma lem4781964 {A : Type'} : (@ex ((nat -> A) -> nat)) = (@ex ((nat -> A) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> A) -> nat))). Qed.
Lemma lem4781965 {A : Type'} : (term1303 A) = (term1328 A).
Proof. exact (MK_COMB (@lem4781964 A) (@lem4781963 A)). Qed.
Lemma lem4781966 {A : Type'} : (term1280 A) = (term1328 A).
Proof. exact (TRANS (@lem4781932 A) (@lem4781965 A)). Qed.
Lemma lem4781968 {A : Type'} : (term1244 A) = (term1328 A).
Proof. exact (TRANS (@lem4781902 A) (@lem4781966 A)). Qed.
Lemma lem4781969 {A : Type'} : (term816 A) = (term1328 A).
Proof. exact (TRANS (@lem4781698 A) (@lem4781968 A)). Qed.
Lemma lem4781970 {A : Type'} (h1 : term816 A) : term1328 A.
Proof. exact (EQ_MP (@lem4781969 A) (@lem4780606 A h1)). Qed.
Lemma lem4781977 {B : Type'} (f : nat -> B) (x : nat) (y : nat) : (term602 B f x y) = (term603 B f x y).
Proof. exact (@lem17362 ((f x) = (f y)) (x = y)). Qed.
Lemma lem4781978 (P : nat -> Prop) : (term317 P) = (term318 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4781979 {B : Type'} (f : nat -> B) (x : nat) : (term1222 B f x) = (term1223 B f x).
Proof. exact (@lem4781978 (term481 B f x)). Qed.
Lemma lem4781980 {B : Type'} (f : nat -> B) (x : nat) (y : nat) : (term492 B f x y) = (term493 B f x y).
Proof. exact (eq_refl (term492 B f x y)). Qed.
Lemma lem4781981 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4781982 {B : Type'} (f : nat -> B) (x : nat) (y : nat) : (term1224 B f x y) = (term602 B f x y).
Proof. exact (MK_COMB (@lem4781981) (@lem4781980 B f x y)). Qed.
Lemma lem4781983 {B : Type'} (f : nat -> B) (x : nat) (y : nat) : (term1224 B f x y) = (term603 B f x y).
Proof. exact (TRANS (@lem4781982 B f x y) (@lem4781977 B f x y)). Qed.
Lemma lem4781984 {B : Type'} (f : nat -> B) (x : nat) : (term1225 B f x) = (term1226 B f x).
Proof. exact (fun_ext (fun y : nat => @lem4781983 B f x y)). Qed.
Lemma lem4781985 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781986 {B : Type'} (f : nat -> B) (x : nat) : (term1223 B f x) = (term1227 B f x).
Proof. exact (MK_COMB (@lem4781985) (@lem4781984 B f x)). Qed.
Lemma lem4781987 {B : Type'} (f : nat -> B) (x : nat) : (term1222 B f x) = (term1227 B f x).
Proof. exact (TRANS (@lem4781979 B f x) (@lem4781986 B f x)). Qed.
Lemma lem4781988 (P : nat -> Prop) : (term317 P) = (term318 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4781989 {B : Type'} (f : nat -> B) : (term1228 B f) = (term1229 B f).
Proof. exact (@lem4781988 (term526 B f)). Qed.
Lemma lem4781990 {B : Type'} (f : nat -> B) (x : nat) : (term1230 B f x) = (term524 B f x).
Proof. exact (eq_refl (term1230 B f x)). Qed.
Lemma lem4781991 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4781992 {B : Type'} (f : nat -> B) (x : nat) : (term1231 B f x) = (term1222 B f x).
Proof. exact (MK_COMB (@lem4781991) (@lem4781990 B f x)). Qed.
Lemma lem4781993 {B : Type'} (f : nat -> B) (x : nat) : (term1231 B f x) = (term1227 B f x).
Proof. exact (TRANS (@lem4781992 B f x) (@lem4781987 B f x)). Qed.
Lemma lem4781994 {B : Type'} (f : nat -> B) : (term1232 B f) = (term1233 B f).
Proof. exact (fun_ext (fun x : nat => @lem4781993 B f x)). Qed.
Lemma lem4781995 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4781996 {B : Type'} (f : nat -> B) : (term1229 B f) = (term1234 B f).
Proof. exact (MK_COMB (@lem4781995) (@lem4781994 B f)). Qed.
Lemma lem4781997 {B : Type'} (f : nat -> B) : (term1228 B f) = (term1234 B f).
Proof. exact (TRANS (@lem4781989 B f) (@lem4781996 B f)). Qed.
Lemma lem4782004 {B : Type'} (f : nat -> B) (s : nat -> Prop) : (term854 B f s) = (term1235 B f s).
Proof. exact (@lem17265 (@INFINITE nat s) (term1236 B f s)). Qed.
Lemma lem4782005 {B : Type'} (f : nat -> B) : (term855 B f) = (term1237 B f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4782004 B f s)). Qed.
Lemma lem4782006 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4782007 {B : Type'} (f : nat -> B) : (term856 B f) = (term1238 B f).
Proof. exact (MK_COMB (@lem4782006) (@lem4782005 B f)). Qed.
Lemma lem4782008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4782009 {B : Type'} (f : nat -> B) : (term1239 B f) = (term1240 B f).
Proof. exact (MK_COMB (@lem4782008) (@lem4781997 B f)). Qed.
Lemma lem4782010 {B : Type'} (f : nat -> B) : (term1241 B f) = (term1242 B f).
Proof. exact (MK_COMB (@lem4782009 B f) (@lem4782007 B f)). Qed.
Lemma lem4782011 {B : Type'} (f : nat -> B) : (term857 B f) = (term1241 B f).
Proof. exact (@lem17265 (term65 B f) (term856 B f)). Qed.
Lemma lem4782012 {B : Type'} (f : nat -> B) : (term857 B f) = (term1242 B f).
Proof. exact (TRANS (@lem4782011 B f) (@lem4782010 B f)). Qed.
Lemma lem4782013 {B : Type'} : (term858 B) = (term1243 B).
Proof. exact (fun_ext (fun f : nat -> B => @lem4782012 B f)). Qed.
Lemma lem4782014 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4782015 {B : Type'} : (term816 B) = (term1244 B).
Proof. exact (MK_COMB (@lem4782014 B) (@lem4782013 B)). Qed.
Lemma lem4782166 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4782167 (P : nat -> Prop) (Q : Prop) : (term1245 P Q) = (term1246 P Q).
Proof. exact (@lem4782166 nat P Q). Qed.
Lemma lem4782168 {B : Type'} (f : nat -> B) : (term1247 B f) = (term1248 B f).
Proof. exact (@lem4782167 (term1233 B f) (term1238 B f)). Qed.
Lemma lem4782169 {B : Type'} (f : nat -> B) (x : nat) : (term1249 B f x) = (term1227 B f x).
Proof. exact (eq_refl (term1249 B f x)). Qed.
Lemma lem4782170 {B : Type'} (f : nat -> B) : (term1250 B f) = (term1233 B f).
Proof. exact (fun_ext (fun x : nat => @lem4782169 B f x)). Qed.
Lemma lem4782171 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4782172 {B : Type'} (f : nat -> B) : (term1251 B f) = (term1234 B f).
Proof. exact (MK_COMB (@lem4782171) (@lem4782170 B f)). Qed.
Lemma lem4782173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4782174 {B : Type'} (f : nat -> B) : (term1252 B f) = (term1240 B f).
Proof. exact (MK_COMB (@lem4782173) (@lem4782172 B f)). Qed.
Lemma lem4782175 {B : Type'} (f : nat -> B) : (term1238 B f) = (term1238 B f).
Proof. exact (eq_refl (term1238 B f)). Qed.
Lemma lem4782176 {B : Type'} (f : nat -> B) : (term1247 B f) = (term1242 B f).
Proof. exact (MK_COMB (@lem4782174 B f) (@lem4782175 B f)). Qed.
Lemma lem4782177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4782178 {B : Type'} (f : nat -> B) : (term1253 B f) = (term1254 B f).
Proof. exact (MK_COMB (@lem4782177) (@lem4782176 B f)). Qed.
Lemma lem4782179 {B : Type'} (f : nat -> B) (x : nat) : (term1249 B f x) = (term1227 B f x).
Proof. exact (eq_refl (term1249 B f x)). Qed.
Lemma lem4782180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4782181 {B : Type'} (f : nat -> B) (x : nat) : (term1255 B f x) = (term1256 B f x).
Proof. exact (MK_COMB (@lem4782180) (@lem4782179 B f x)). Qed.
Lemma lem4782182 {B : Type'} (f : nat -> B) : (term1238 B f) = (term1238 B f).
Proof. exact (eq_refl (term1238 B f)). Qed.
Lemma lem4782183 {B : Type'} (x : nat) (f : nat -> B) : (term1257 B x f) = (term1258 B x f).
Proof. exact (MK_COMB (@lem4782181 B f x) (@lem4782182 B f)). Qed.
Lemma lem4782184 {B : Type'} (f : nat -> B) : (term1259 B f) = (term1260 B f).
Proof. exact (fun_ext (fun x : nat => @lem4782183 B x f)). Qed.
Lemma lem4782185 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4782186 {B : Type'} (f : nat -> B) : (term1248 B f) = (term1261 B f).
Proof. exact (MK_COMB (@lem4782185) (@lem4782184 B f)). Qed.
Lemma lem4782187 {B : Type'} (f : nat -> B) : ((term1247 B f) = (term1248 B f)) = ((term1242 B f) = (term1261 B f)).
Proof. exact (MK_COMB (@lem4782178 B f) (@lem4782186 B f)). Qed.
Lemma lem4782188 {B : Type'} (f : nat -> B) : (term1242 B f) = (term1261 B f).
Proof. exact (EQ_MP (@lem4782187 B f) (@lem4782168 B f)). Qed.
Lemma lem4782190 {A : Type'} (P : A -> Prop) (Q : Prop) : (term922 A P Q) = (term923 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4782191 (P : nat -> Prop) (Q : Prop) : (term1245 P Q) = (term1246 P Q).
Proof. exact (@lem4782190 nat P Q). Qed.
Lemma lem4782192 {B : Type'} (x : nat) (f : nat -> B) : (term1262 B x f) = (term1263 B x f).
Proof. exact (@lem4782191 (term1226 B f x) (term1238 B f)). Qed.
Lemma lem4782193 {B : Type'} (f : nat -> B) (x : nat) (y : nat) : (term1264 B f x y) = (term603 B f x y).
Proof. exact (eq_refl (term1264 B f x y)). Qed.
Lemma lem4782194 {B : Type'} (f : nat -> B) (x : nat) : (term1265 B f x) = (term1226 B f x).
Proof. exact (fun_ext (fun y : nat => @lem4782193 B f x y)). Qed.
Lemma lem4782195 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4782196 {B : Type'} (f : nat -> B) (x : nat) : (term1266 B f x) = (term1227 B f x).
Proof. exact (MK_COMB (@lem4782195) (@lem4782194 B f x)). Qed.
Lemma lem4782197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4782198 {B : Type'} (f : nat -> B) (x : nat) : (term1267 B f x) = (term1256 B f x).
Proof. exact (MK_COMB (@lem4782197) (@lem4782196 B f x)). Qed.
Lemma lem4782199 {B : Type'} (f : nat -> B) : (term1238 B f) = (term1238 B f).
Proof. exact (eq_refl (term1238 B f)). Qed.
Lemma lem4782200 {B : Type'} (x : nat) (f : nat -> B) : (term1262 B x f) = (term1258 B x f).
Proof. exact (MK_COMB (@lem4782198 B f x) (@lem4782199 B f)). Qed.
Lemma lem4782201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4782202 {B : Type'} (x : nat) (f : nat -> B) : (term1268 B x f) = (term1269 B x f).
Proof. exact (MK_COMB (@lem4782201) (@lem4782200 B x f)). Qed.
Lemma lem4782203 {B : Type'} (f : nat -> B) (x : nat) (y : nat) : (term1264 B f x y) = (term603 B f x y).
Proof. exact (eq_refl (term1264 B f x y)). Qed.
Lemma lem4782204 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4782205 {B : Type'} (f : nat -> B) (x : nat) (y : nat) : (term1270 B f x y) = (term1271 B f x y).
Proof. exact (MK_COMB (@lem4782204) (@lem4782203 B f x y)). Qed.
Lemma lem4782206 {B : Type'} (f : nat -> B) : (term1238 B f) = (term1238 B f).
Proof. exact (eq_refl (term1238 B f)). Qed.
Lemma lem4782207 {B : Type'} (x : nat) (y : nat) (f : nat -> B) : (term1272 B x y f) = (term1273 B x y f).
Proof. exact (MK_COMB (@lem4782205 B f x y) (@lem4782206 B f)). Qed.
Lemma lem4782208 {B : Type'} (x : nat) (f : nat -> B) : (term1274 B x f) = (term1275 B x f).
Proof. exact (fun_ext (fun y : nat => @lem4782207 B x y f)). Qed.
Lemma lem4782209 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4782210 {B : Type'} (x : nat) (f : nat -> B) : (term1263 B x f) = (term1276 B x f).
Proof. exact (MK_COMB (@lem4782209) (@lem4782208 B x f)). Qed.
Lemma lem4782211 {B : Type'} (x : nat) (f : nat -> B) : ((term1262 B x f) = (term1263 B x f)) = ((term1258 B x f) = (term1276 B x f)).
Proof. exact (MK_COMB (@lem4782202 B x f) (@lem4782210 B x f)). Qed.
Lemma lem4782212 {B : Type'} (x : nat) (f : nat -> B) : (term1258 B x f) = (term1276 B x f).
Proof. exact (EQ_MP (@lem4782211 B x f) (@lem4782192 B x f)). Qed.
Lemma lem4782213 {B : Type'} (f : nat -> B) : (term1260 B f) = (term1277 B f).
Proof. exact (fun_ext (fun x : nat => @lem4782212 B x f)). Qed.
Lemma lem4782214 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4782215 {B : Type'} (f : nat -> B) : (term1261 B f) = (term1278 B f).
Proof. exact (MK_COMB (@lem4782214) (@lem4782213 B f)). Qed.
Lemma lem4782216 {B : Type'} (f : nat -> B) : (term1242 B f) = (term1278 B f).
Proof. exact (TRANS (@lem4782188 B f) (@lem4782215 B f)). Qed.
Lemma lem4782217 {B : Type'} : (term1243 B) = (term1279 B).
Proof. exact (fun_ext (fun f : nat -> B => @lem4782216 B f)). Qed.
Lemma lem4782218 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4782219 {B : Type'} : (term1244 B) = (term1280 B).
Proof. exact (MK_COMB (@lem4782218 B) (@lem4782217 B)). Qed.
Lemma lem4782221 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4782222 {B : Type'} (P : type973 B) : (term1281 B P) = (term1282 B P).
Proof. exact (@lem4782221 (nat -> B) nat P). Qed.
Lemma lem4782223 {B : Type'} : (term1283 B) = (term1284 B).
Proof. exact (@lem4782222 B (term1285 B)). Qed.
Lemma lem4782224 {B : Type'} (f : nat -> B) : (term1286 B f) = (term1277 B f).
Proof. exact (eq_refl (term1286 B f)). Qed.
Lemma lem4782225 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4782226 {B : Type'} (f : nat -> B) (x : nat) : (term1287 B f x) = (term1288 B f x).
Proof. exact (MK_COMB (@lem4782224 B f) (@lem4782225 x)). Qed.
Lemma lem4782227 {B : Type'} (x : nat) (f : nat -> B) : (term1288 B f x) = (term1276 B x f).
Proof. exact (eq_refl (term1288 B f x)). Qed.
Lemma lem4782228 {B : Type'} (x : nat) (f : nat -> B) : (term1287 B f x) = (term1276 B x f).
Proof. exact (TRANS (@lem4782226 B f x) (@lem4782227 B x f)). Qed.
Lemma lem4782229 {B : Type'} (f : nat -> B) : (term1289 B f) = (term1277 B f).
Proof. exact (fun_ext (fun x : nat => @lem4782228 B x f)). Qed.
Lemma lem4782230 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4782231 {B : Type'} (f : nat -> B) : (term1290 B f) = (term1278 B f).
Proof. exact (MK_COMB (@lem4782230) (@lem4782229 B f)). Qed.
Lemma lem4782232 {B : Type'} : (term1291 B) = (term1279 B).
Proof. exact (fun_ext (fun f : nat -> B => @lem4782231 B f)). Qed.
Lemma lem4782233 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4782234 {B : Type'} : (term1283 B) = (term1280 B).
Proof. exact (MK_COMB (@lem4782233 B) (@lem4782232 B)). Qed.
Lemma lem4782235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4782236 {B : Type'} : (term1292 B) = (term1293 B).
Proof. exact (MK_COMB (@lem4782235) (@lem4782234 B)). Qed.
Lemma lem4782237 {B : Type'} (f : nat -> B) : (term1286 B f) = (term1277 B f).
Proof. exact (eq_refl (term1286 B f)). Qed.
Lemma lem4782238 {B : Type'} (x : type977 B) (f : nat -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4782239 {B : Type'} (x : type977 B) (f : nat -> B) : (term1294 B x f) = (term1295 B x f).
Proof. exact (MK_COMB (@lem4782237 B f) (@lem4782238 B x f)). Qed.
Lemma lem4782240 {B : Type'} (x : type977 B) (f : nat -> B) : (term1295 B x f) = (term1296 B x f).
Proof. exact (eq_refl (term1295 B x f)). Qed.
Lemma lem4782241 {B : Type'} (x : type977 B) (f : nat -> B) : (term1294 B x f) = (term1296 B x f).
Proof. exact (TRANS (@lem4782239 B x f) (@lem4782240 B x f)). Qed.
Lemma lem4782242 {B : Type'} (x : type977 B) : (term1297 B x) = (term1298 B x).
Proof. exact (fun_ext (fun f : nat -> B => @lem4782241 B x f)). Qed.
Lemma lem4782243 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4782244 {B : Type'} (x : type977 B) : (term1299 B x) = (term1300 B x).
Proof. exact (MK_COMB (@lem4782243 B) (@lem4782242 B x)). Qed.
Lemma lem4782245 {B : Type'} : (term1301 B) = (term1302 B).
Proof. exact (fun_ext (fun x : type977 B => @lem4782244 B x)). Qed.
Lemma lem4782246 {B : Type'} : (@ex ((nat -> B) -> nat)) = (@ex ((nat -> B) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> B) -> nat))). Qed.
Lemma lem4782247 {B : Type'} : (term1284 B) = (term1303 B).
Proof. exact (MK_COMB (@lem4782246 B) (@lem4782245 B)). Qed.
Lemma lem4782248 {B : Type'} : ((term1283 B) = (term1284 B)) = ((term1280 B) = (term1303 B)).
Proof. exact (MK_COMB (@lem4782236 B) (@lem4782247 B)). Qed.
Lemma lem4782249 {B : Type'} : (term1280 B) = (term1303 B).
Proof. exact (EQ_MP (@lem4782248 B) (@lem4782223 B)). Qed.
Lemma lem4782251 {A B : Type'} (P : type1413 A B) : (term357 A B P) = (term358 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4782252 {B : Type'} (P : type973 B) : (term1281 B P) = (term1282 B P).
Proof. exact (@lem4782251 (nat -> B) nat P). Qed.
Lemma lem4782253 {B : Type'} (x : type977 B) : (term1304 B x) = (term1305 B x).
Proof. exact (@lem4782252 B (term1306 B x)). Qed.
Lemma lem4782254 {B : Type'} (x : type977 B) (f : nat -> B) : (term1307 B x f) = (term1308 B x f).
Proof. exact (eq_refl (term1307 B x f)). Qed.
Lemma lem4782255 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4782256 {B : Type'} (x : type977 B) (f : nat -> B) (y : nat) : (term1309 B x f y) = (term1310 B x f y).
Proof. exact (MK_COMB (@lem4782254 B x f) (@lem4782255 y)). Qed.
Lemma lem4782257 {B : Type'} (x : type977 B) (y : nat) (f : nat -> B) : (term1310 B x f y) = (term1311 B x y f).
Proof. exact (eq_refl (term1310 B x f y)). Qed.
Lemma lem4782258 {B : Type'} (x : type977 B) (y : nat) (f : nat -> B) : (term1309 B x f y) = (term1311 B x y f).
Proof. exact (TRANS (@lem4782256 B x f y) (@lem4782257 B x y f)). Qed.
Lemma lem4782259 {B : Type'} (x : type977 B) (f : nat -> B) : (term1312 B x f) = (term1308 B x f).
Proof. exact (fun_ext (fun y : nat => @lem4782258 B x y f)). Qed.
Lemma lem4782260 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4782261 {B : Type'} (x : type977 B) (f : nat -> B) : (term1313 B x f) = (term1296 B x f).
Proof. exact (MK_COMB (@lem4782260) (@lem4782259 B x f)). Qed.
Lemma lem4782262 {B : Type'} (x : type977 B) : (term1314 B x) = (term1298 B x).
Proof. exact (fun_ext (fun f : nat -> B => @lem4782261 B x f)). Qed.
Lemma lem4782263 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4782264 {B : Type'} (x : type977 B) : (term1304 B x) = (term1300 B x).
Proof. exact (MK_COMB (@lem4782263 B) (@lem4782262 B x)). Qed.
Lemma lem4782265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4782266 {B : Type'} (x : type977 B) : (term1315 B x) = (term1316 B x).
Proof. exact (MK_COMB (@lem4782265) (@lem4782264 B x)). Qed.
Lemma lem4782267 {B : Type'} (x : type977 B) (f : nat -> B) : (term1307 B x f) = (term1308 B x f).
Proof. exact (eq_refl (term1307 B x f)). Qed.
Lemma lem4782268 {B : Type'} (y : type977 B) (f : nat -> B) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem4782269 {B : Type'} (x : type977 B) (y : type977 B) (f : nat -> B) : (term1317 B x y f) = (term1318 B x y f).
Proof. exact (MK_COMB (@lem4782267 B x f) (@lem4782268 B y f)). Qed.
Lemma lem4782270 {B : Type'} (x : type977 B) (y : type977 B) (f : nat -> B) : (term1318 B x y f) = (term1319 B x y f).
Proof. exact (eq_refl (term1318 B x y f)). Qed.
Lemma lem4782271 {B : Type'} (x : type977 B) (y : type977 B) (f : nat -> B) : (term1317 B x y f) = (term1319 B x y f).
Proof. exact (TRANS (@lem4782269 B x y f) (@lem4782270 B x y f)). Qed.
Lemma lem4782272 {B : Type'} (x : type977 B) (y : type977 B) : (term1320 B x y) = (term1321 B x y).
Proof. exact (fun_ext (fun f : nat -> B => @lem4782271 B x y f)). Qed.
Lemma lem4782273 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem4782274 {B : Type'} (x : type977 B) (y : type977 B) : (term1322 B x y) = (term1323 B x y).
Proof. exact (MK_COMB (@lem4782273 B) (@lem4782272 B x y)). Qed.
Lemma lem4782275 {B : Type'} (x : type977 B) : (term1324 B x) = (term1325 B x).
Proof. exact (fun_ext (fun y : type977 B => @lem4782274 B x y)). Qed.
Lemma lem4782276 {B : Type'} : (@ex ((nat -> B) -> nat)) = (@ex ((nat -> B) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> B) -> nat))). Qed.
Lemma lem4782277 {B : Type'} (x : type977 B) : (term1305 B x) = (term1326 B x).
Proof. exact (MK_COMB (@lem4782276 B) (@lem4782275 B x)). Qed.
Lemma lem4782278 {B : Type'} (x : type977 B) : ((term1304 B x) = (term1305 B x)) = ((term1300 B x) = (term1326 B x)).
Proof. exact (MK_COMB (@lem4782266 B x) (@lem4782277 B x)). Qed.
Lemma lem4782279 {B : Type'} (x : type977 B) : (term1300 B x) = (term1326 B x).
Proof. exact (EQ_MP (@lem4782278 B x) (@lem4782253 B x)). Qed.
Lemma lem4782280 {B : Type'} : (term1302 B) = (term1327 B).
Proof. exact (fun_ext (fun x : type977 B => @lem4782279 B x)). Qed.
Lemma lem4782281 {B : Type'} : (@ex ((nat -> B) -> nat)) = (@ex ((nat -> B) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> B) -> nat))). Qed.
Lemma lem4782282 {B : Type'} : (term1303 B) = (term1328 B).
Proof. exact (MK_COMB (@lem4782281 B) (@lem4782280 B)). Qed.
Lemma lem4782283 {B : Type'} : (term1280 B) = (term1328 B).
Proof. exact (TRANS (@lem4782249 B) (@lem4782282 B)). Qed.
Lemma lem4782285 {B : Type'} : (term1244 B) = (term1328 B).
Proof. exact (TRANS (@lem4782219 B) (@lem4782283 B)). Qed.
Lemma lem4782286 {B : Type'} : (term816 B) = (term1328 B).
Proof. exact (TRANS (@lem4782015 B) (@lem4782285 B)). Qed.
Lemma lem4782287 {B : Type'} (h1 : term816 B) : term1328 B.
Proof. exact (EQ_MP (@lem4782286 B) (@lem4780607 B h1)). Qed.
Lemma lem4782288 {B : Type'} (x : type977 B) (h1 : term1326 B x) : term1326 B x.
Proof. exact (h1). Qed.
Lemma lem4782290 {A : Type'} (x' : type977 A) (h1 : term1326 A x') : term1326 A x'.
Proof. exact (h1). Qed.
Lemma lem4782291 {A : Type'} (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1323 A x' y'.
Proof. exact (h1). Qed.
Lemma lem4782292 {A : Type'} (x'' : type703 A) (h1 : term1219 A x'') : term1219 A x''.
Proof. exact (h1). Qed.
Lemma lem4782294 {A B : Type'} (x''' : type569 A B) (h1 : term1111 A B x''') : term1111 A B x'''.
Proof. exact (h1). Qed.
Lemma lem4782296 {A : Type'} (x'''' : type487 A) (h1 : term1003 A x'''') : term1003 A x''''.
Proof. exact (h1). Qed.
Lemma lem4782329 (x : nat) (y : nat) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4782330 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4782331 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4782336 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782338 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem4782336 nat A f x). Qed.
Lemma lem4782343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782344 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem4782343 nat A f x). Qed.
Lemma lem4782346 {A : Type'} (f : nat -> A) (y : nat) : (f y) = (@I (nat -> A) f y).
Proof. exact (@lem4782344 A f y). Qed.
Lemma lem4782347 {A : Type'} (f : nat -> A) (x : nat) : (term159 A f x) = (term1329 A f x).
Proof. exact (MK_COMB (@lem4782331 A) (@lem4782338 A f x)). Qed.
Lemma lem4782348 {A : Type'} (x : nat) (f : nat -> A) (y : nat) : ((f x) = (f y)) = ((@I (nat -> A) f x) = (@I (nat -> A) f y)).
Proof. exact (MK_COMB (@lem4782347 A f x) (@lem4782346 A f y)). Qed.
Lemma lem4782349 {A : Type'} (x : nat) (f : nat -> A) (y : nat) : (term594 A x f y) = (term1330 A x f y).
Proof. exact (MK_COMB (@lem4782330) (@lem4782348 A x f y)). Qed.
Lemma lem4782350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4782351 {A : Type'} (x : nat) (f : nat -> A) (y : nat) : (term1331 A x f y) = (term1332 A x f y).
Proof. exact (MK_COMB (@lem4782350) (@lem4782349 A x f y)). Qed.
Lemma lem4782352 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term604 A f x y) = (term1333 A f x y).
Proof. exact (MK_COMB (@lem4782351 A x f y) (@lem4782329 x y)). Qed.
Lemma lem4782353 {A : Type'} (f : nat -> A) (x : nat) : (term892 A f x) = (term1334 A f x).
Proof. exact (fun_ext (fun y : nat => @lem4782352 A f x y)). Qed.
Lemma lem4782354 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4782355 {A : Type'} (f : nat -> A) (x : nat) : (term893 A f x) = (term1335 A f x).
Proof. exact (MK_COMB (@lem4782354) (@lem4782353 A f x)). Qed.
Lemma lem4782356 {A : Type'} (f : nat -> A) : (term894 A f) = (term1336 A f).
Proof. exact (fun_ext (fun x : nat => @lem4782355 A f x)). Qed.
Lemma lem4782357 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4782358 {A : Type'} (f : nat -> A) : (term895 A f) = (term1337 A f).
Proof. exact (MK_COMB (@lem4782357) (@lem4782356 A f)). Qed.
Lemma lem4782359 {A : Type'} (f : nat -> A) (h1 : term65 A f) : term1337 A f.
Proof. exact (EQ_MP (@lem4782358 A f) (@lem4780690 A f h1)). Qed.
Lemma lem4782360 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4782361 {A : Type'} : (@INFINITE A) = (@INFINITE A).
Proof. exact (eq_refl (@INFINITE A)). Qed.
Lemma lem4782368 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782369 {A : Type'} (f : type968 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4782368 (nat -> A) (type989 A) f x). Qed.
Lemma lem4782370 {A : Type'} (f : nat -> A) : (@IMAGE nat A f) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f).
Proof. exact (@lem4782369 A (@IMAGE nat A) f). Qed.
Lemma lem4782371 : (@UNIV nat) = (@UNIV nat).
Proof. exact (eq_refl (@UNIV nat)). Qed.
Lemma lem4782372 {A : Type'} (f : nat -> A) : (@IMAGE nat A f (@UNIV nat)) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f (@UNIV nat)).
Proof. exact (MK_COMB (@lem4782370 A f) (@lem4782371)). Qed.
Lemma lem4782374 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782375 {A : Type'} (f : type989 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4782374 (nat -> Prop) (A -> Prop) f x). Qed.
Lemma lem4782376 {A : Type'} (f : nat -> A) : (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f (@UNIV nat)) = (term1338 A f).
Proof. exact (@lem4782375 A (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f) (@UNIV nat)). Qed.
Lemma lem4782378 {A : Type'} (f : nat -> A) : (@IMAGE nat A f (@UNIV nat)) = (term1338 A f).
Proof. exact (TRANS (@lem4782372 A f) (@lem4782376 A f)). Qed.
Lemma lem4782379 {A : Type'} (f : nat -> A) : (term810 A f) = (term1339 A f).
Proof. exact (MK_COMB (@lem4782361 A) (@lem4782378 A f)). Qed.
Lemma lem4782381 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782382 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4782381 (A -> Prop) Prop f x). Qed.
Lemma lem4782383 {A : Type'} (f : nat -> A) : (term1339 A f) = (term1340 A f).
Proof. exact (@lem4782382 A (@INFINITE A) (term1338 A f)). Qed.
Lemma lem4782384 {A : Type'} (f : nat -> A) : (term810 A f) = (term1340 A f).
Proof. exact (TRANS (@lem4782379 A f) (@lem4782383 A f)). Qed.
Lemma lem4782385 {A : Type'} (f : nat -> A) : (term812 A f) = (term1341 A f).
Proof. exact (MK_COMB (@lem4782360) (@lem4782384 A f)). Qed.
Lemma lem4782391 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782392 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem4782391 (nat -> Prop) Prop f x). Qed.
Lemma lem4782394 : (@INFINITE nat (@UNIV nat)) = (@I ((nat -> Prop) -> Prop) (@INFINITE nat) (@UNIV nat)).
Proof. exact (@lem4782392 (@INFINITE nat) (@UNIV nat)). Qed.
Lemma lem4782500 {A : Type'} : (@INFINITE A) = (@INFINITE A).
Proof. exact (eq_refl (@INFINITE A)). Qed.
Lemma lem4782507 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782508 {A : Type'} (f : type968 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4782507 (nat -> A) (type989 A) f x). Qed.
Lemma lem4782509 {A : Type'} (f : nat -> A) : (@IMAGE nat A f) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f).
Proof. exact (@lem4782508 A (@IMAGE nat A) f). Qed.
Lemma lem4782510 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4782511 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (@IMAGE nat A f s) = (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f s).
Proof. exact (MK_COMB (@lem4782509 A f) (@lem4782510 s)). Qed.
Lemma lem4782513 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782514 {A : Type'} (f : type989 A) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4782513 (nat -> Prop) (A -> Prop) f x). Qed.
Lemma lem4782515 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f s) = (term1342 A f s).
Proof. exact (@lem4782514 A (@I ((nat -> A) -> (nat -> Prop) -> A -> Prop) (@IMAGE nat A) f) s). Qed.
Lemma lem4782517 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (@IMAGE nat A f s) = (term1342 A f s).
Proof. exact (TRANS (@lem4782511 A f s) (@lem4782515 A f s)). Qed.
Lemma lem4782518 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term1236 A f s) = (term1343 A f s).
Proof. exact (MK_COMB (@lem4782500 A) (@lem4782517 A f s)). Qed.
Lemma lem4782520 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782521 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4782520 (A -> Prop) Prop f x). Qed.
Lemma lem4782522 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term1343 A f s) = (term1344 A f s).
Proof. exact (@lem4782521 A (@INFINITE A) (term1342 A f s)). Qed.
Lemma lem4782523 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term1236 A f s) = (term1344 A f s).
Proof. exact (TRANS (@lem4782518 A f s) (@lem4782522 A f s)). Qed.
Lemma lem4782524 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4782529 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782530 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem4782529 (nat -> Prop) Prop f x). Qed.
Lemma lem4782532 (s : nat -> Prop) : (@INFINITE nat s) = (@I ((nat -> Prop) -> Prop) (@INFINITE nat) s).
Proof. exact (@lem4782530 (@INFINITE nat) s). Qed.
Lemma lem4782533 (s : nat -> Prop) : (term1345 s) = (term1346 s).
Proof. exact (MK_COMB (@lem4782524) (@lem4782532 s)). Qed.
Lemma lem4782534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4782535 (s : nat -> Prop) : (term1347 s) = (term1348 s).
Proof. exact (MK_COMB (@lem4782534) (@lem4782533 s)). Qed.
Lemma lem4782536 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term1235 A f s) = (term1349 A f s).
Proof. exact (MK_COMB (@lem4782535 s) (@lem4782523 A f s)). Qed.
Lemma lem4782537 {A : Type'} (f : nat -> A) : (term1237 A f) = (term1350 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4782536 A f s)). Qed.
Lemma lem4782538 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4782539 {A : Type'} (f : nat -> A) : (term1238 A f) = (term1351 A f).
Proof. exact (MK_COMB (@lem4782538) (@lem4782537 A f)). Qed.
Lemma lem4782540 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4782541 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4782546 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782547 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem4782546 (nat -> A) nat f x). Qed.
Lemma lem4782549 {A : Type'} (x' : type977 A) (f : nat -> A) : (x' f) = (@I ((nat -> A) -> nat) x' f).
Proof. exact (@lem4782547 A x' f). Qed.
Lemma lem4782554 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782555 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem4782554 (nat -> A) nat f x). Qed.
Lemma lem4782557 {A : Type'} (y' : type977 A) (f : nat -> A) : (y' f) = (@I ((nat -> A) -> nat) y' f).
Proof. exact (@lem4782555 A y' f). Qed.
Lemma lem4782558 {A : Type'} (x' : type977 A) (f : nat -> A) : (term1352 A x' f) = (term1353 A x' f).
Proof. exact (MK_COMB (@lem4782541) (@lem4782549 A x' f)). Qed.
Lemma lem4782559 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : ((x' f) = (y' f)) = ((@I ((nat -> A) -> nat) x' f) = (@I ((nat -> A) -> nat) y' f)).
Proof. exact (MK_COMB (@lem4782558 A x' f) (@lem4782557 A y' f)). Qed.
Lemma lem4782560 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1354 A x' y' f) = (term1355 A x' y' f).
Proof. exact (MK_COMB (@lem4782540) (@lem4782559 A x' y' f)). Qed.
Lemma lem4782561 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4782562 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4782567 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782568 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem4782567 (nat -> A) nat f x). Qed.
Lemma lem4782570 {A : Type'} (x' : type977 A) (f : nat -> A) : (x' f) = (@I ((nat -> A) -> nat) x' f).
Proof. exact (@lem4782568 A x' f). Qed.
Lemma lem4782571 {A : Type'} (x' : type977 A) (f : nat -> A) : (term1356 A x' f) = (term1357 A x' f).
Proof. exact (MK_COMB (@lem4782562 A f) (@lem4782570 A x' f)). Qed.
Lemma lem4782573 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782574 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem4782573 nat A f x). Qed.
Lemma lem4782575 {A : Type'} (x' : type977 A) (f : nat -> A) : (term1357 A x' f) = (term1358 A x' f).
Proof. exact (@lem4782574 A f (@I ((nat -> A) -> nat) x' f)). Qed.
Lemma lem4782576 {A : Type'} (x' : type977 A) (f : nat -> A) : (term1356 A x' f) = (term1358 A x' f).
Proof. exact (TRANS (@lem4782571 A x' f) (@lem4782575 A x' f)). Qed.
Lemma lem4782577 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4782582 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782583 {A : Type'} (f : type977 A) (x : nat -> A) : (f x) = (@I ((nat -> A) -> nat) f x).
Proof. exact (@lem4782582 (nat -> A) nat f x). Qed.
Lemma lem4782585 {A : Type'} (y' : type977 A) (f : nat -> A) : (y' f) = (@I ((nat -> A) -> nat) y' f).
Proof. exact (@lem4782583 A y' f). Qed.
Lemma lem4782586 {A : Type'} (y' : type977 A) (f : nat -> A) : (term1356 A y' f) = (term1357 A y' f).
Proof. exact (MK_COMB (@lem4782577 A f) (@lem4782585 A y' f)). Qed.
Lemma lem4782588 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4782589 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem4782588 nat A f x). Qed.
Lemma lem4782590 {A : Type'} (y' : type977 A) (f : nat -> A) : (term1357 A y' f) = (term1358 A y' f).
Proof. exact (@lem4782589 A f (@I ((nat -> A) -> nat) y' f)). Qed.
Lemma lem4782591 {A : Type'} (y' : type977 A) (f : nat -> A) : (term1356 A y' f) = (term1358 A y' f).
Proof. exact (TRANS (@lem4782586 A y' f) (@lem4782590 A y' f)). Qed.
Lemma lem4782592 {A : Type'} (x' : type977 A) (f : nat -> A) : (term1359 A x' f) = (term1360 A x' f).
Proof. exact (MK_COMB (@lem4782561 A) (@lem4782576 A x' f)). Qed.
Lemma lem4782593 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : ((term1356 A x' f) = (term1356 A y' f)) = ((term1358 A x' f) = (term1358 A y' f)).
Proof. exact (MK_COMB (@lem4782592 A x' f) (@lem4782591 A y' f)). Qed.
Lemma lem4782594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4782595 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1361 A x' y' f) = (term1362 A x' y' f).
Proof. exact (MK_COMB (@lem4782594) (@lem4782593 A x' y' f)). Qed.
Lemma lem4782596 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1363 A x' y' f) = (term1364 A x' y' f).
Proof. exact (MK_COMB (@lem4782595 A x' y' f) (@lem4782560 A x' y' f)). Qed.
Lemma lem4782597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4782598 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1365 A x' y' f) = (term1366 A x' y' f).
Proof. exact (MK_COMB (@lem4782597) (@lem4782596 A x' y' f)). Qed.
Lemma lem4782599 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1319 A x' y' f) = (term1367 A x' y' f).
Proof. exact (MK_COMB (@lem4782598 A x' y' f) (@lem4782539 A f)). Qed.
Lemma lem4782600 {A : Type'} (x' : type977 A) (y' : type977 A) : (term1321 A x' y') = (term1368 A x' y').
Proof. exact (fun_ext (fun f : nat -> A => @lem4782599 A x' y' f)). Qed.
Lemma lem4782601 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4782602 {A : Type'} (x' : type977 A) (y' : type977 A) : (term1323 A x' y') = (term1369 A x' y').
Proof. exact (MK_COMB (@lem4782601 A) (@lem4782600 A x' y')). Qed.
Lemma lem4782603 {A : Type'} (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1369 A x' y'.
Proof. exact (EQ_MP (@lem4782602 A x' y') (@lem4782291 A x' y' h1)). Qed.
Lemma lem4782930 {A : Type'} (f : nat -> A) (x : nat) (y : nat) : (term1333 A f x y) = (term1333 A f x y).
Proof. exact (eq_refl (term1333 A f x y)). Qed.
Lemma lem4782931 {A : Type'} (f : nat -> A) (x : nat) : (term1334 A f x) = (term1334 A f x).
Proof. exact (fun_ext (fun y : nat => @lem4782930 A f x y)). Qed.
Lemma lem4782932 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4782933 {A : Type'} (f : nat -> A) (x : nat) : (term1335 A f x) = (term1335 A f x).
Proof. exact (MK_COMB (@lem4782932) (@lem4782931 A f x)). Qed.
Lemma lem4782934 {A : Type'} (f : nat -> A) : (term1336 A f) = (term1336 A f).
Proof. exact (fun_ext (fun x : nat => @lem4782933 A f x)). Qed.
Lemma lem4782935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4782937 {A : Type'} (f : nat -> A) : (term1337 A f) = (term1337 A f).
Proof. exact (MK_COMB (@lem4782935) (@lem4782934 A f)). Qed.
Lemma lem4782938 {A : Type'} (f : nat -> A) (h1 : term65 A f) : term1337 A f.
Proof. exact (EQ_MP (@lem4782937 A f) (@lem4782359 A f h1)). Qed.
Lemma lem4783002 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1370 A P Q) = (term1371 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4783003 (P : Prop) (Q : type993) : (term1372 P Q) = (term1373 P Q).
Proof. exact (@lem4783002 (nat -> Prop) P Q). Qed.
Lemma lem4783004 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1374 A x' y' f) = (term1375 A x' y' f).
Proof. exact (@lem4783003 (term1364 A x' y' f) (term1350 A f)). Qed.
Lemma lem4783005 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term1376 A f s) = (term1349 A f s).
Proof. exact (eq_refl (term1376 A f s)). Qed.
Lemma lem4783006 {A : Type'} (f : nat -> A) : (term1377 A f) = (term1350 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4783005 A f s)). Qed.
Lemma lem4783007 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4783008 {A : Type'} (f : nat -> A) : (term1378 A f) = (term1351 A f).
Proof. exact (MK_COMB (@lem4783007) (@lem4783006 A f)). Qed.
Lemma lem4783009 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1366 A x' y' f) = (term1366 A x' y' f).
Proof. exact (eq_refl (term1366 A x' y' f)). Qed.
Lemma lem4783010 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1374 A x' y' f) = (term1367 A x' y' f).
Proof. exact (MK_COMB (@lem4783009 A x' y' f) (@lem4783008 A f)). Qed.
Lemma lem4783011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4783012 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1379 A x' y' f) = (term1380 A x' y' f).
Proof. exact (MK_COMB (@lem4783011) (@lem4783010 A x' y' f)). Qed.
Lemma lem4783013 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term1376 A f s) = (term1349 A f s).
Proof. exact (eq_refl (term1376 A f s)). Qed.
Lemma lem4783014 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1366 A x' y' f) = (term1366 A x' y' f).
Proof. exact (eq_refl (term1366 A x' y' f)). Qed.
Lemma lem4783015 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (s : nat -> Prop) : (term1381 A x' y' f s) = (term1382 A x' y' f s).
Proof. exact (MK_COMB (@lem4783014 A x' y' f) (@lem4783013 A f s)). Qed.
Lemma lem4783016 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1383 A x' y' f) = (term1384 A x' y' f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4783015 A x' y' f s)). Qed.
Lemma lem4783017 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4783018 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1375 A x' y' f) = (term1385 A x' y' f).
Proof. exact (MK_COMB (@lem4783017) (@lem4783016 A x' y' f)). Qed.
Lemma lem4783019 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : ((term1374 A x' y' f) = (term1375 A x' y' f)) = ((term1367 A x' y' f) = (term1385 A x' y' f)).
Proof. exact (MK_COMB (@lem4783012 A x' y' f) (@lem4783018 A x' y' f)). Qed.
Lemma lem4783020 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1367 A x' y' f) = (term1385 A x' y' f).
Proof. exact (EQ_MP (@lem4783019 A x' y' f) (@lem4783004 A x' y' f)). Qed.
Lemma lem4783021 {A : Type'} (x' : type977 A) (y' : type977 A) : (term1368 A x' y') = (term1386 A x' y').
Proof. exact (fun_ext (fun f : nat -> A => @lem4783020 A x' y' f)). Qed.
Lemma lem4783022 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4783023 {A : Type'} (x' : type977 A) (y' : type977 A) : (term1369 A x' y') = (term1387 A x' y').
Proof. exact (MK_COMB (@lem4783022 A) (@lem4783021 A x' y')). Qed.
Lemma lem4783046 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (s : nat -> Prop) : (term1382 A x' y' f s) = (term1388 A x' y' f s).
Proof. exact (@lem19699 ((term1358 A x' f) = (term1358 A y' f)) (term1355 A x' y' f) (term1349 A f s)). Qed.
Lemma lem4783047 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1384 A x' y' f) = (term1389 A x' y' f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4783046 A x' y' f s)). Qed.
Lemma lem4783048 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4783049 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1385 A x' y' f) = (term1390 A x' y' f).
Proof. exact (MK_COMB (@lem4783048) (@lem4783047 A x' y' f)). Qed.
Lemma lem4783050 {A : Type'} (x' : type977 A) (y' : type977 A) : (term1386 A x' y') = (term1391 A x' y').
Proof. exact (fun_ext (fun f : nat -> A => @lem4783049 A x' y' f)). Qed.
Lemma lem4783051 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem4783052 {A : Type'} (x' : type977 A) (y' : type977 A) : (term1387 A x' y') = (term1392 A x' y').
Proof. exact (MK_COMB (@lem4783051 A) (@lem4783050 A x' y')). Qed.
Lemma lem4783053 {A : Type'} (x' : type977 A) (y' : type977 A) : (term1369 A x' y') = (term1392 A x' y').
Proof. exact (TRANS (@lem4783023 A x' y') (@lem4783052 A x' y')). Qed.
Lemma lem4783054 {A : Type'} (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1392 A x' y'.
Proof. exact (EQ_MP (@lem4783053 A x' y') (@lem4782603 A x' y' h1)). Qed.
Lemma lem4783220 {A : Type'} (_59006 : nat) (f : nat -> A) (h1 : term65 A f) : term1393 A f _59006.
Proof. exact (@lem4782938 A f h1 _59006). Qed.
Lemma lem4783221 {A : Type'} (f : nat -> A) (_59006 : nat) : (term1393 A f _59006) = (term1335 A f _59006).
Proof. exact (eq_refl (term1393 A f _59006)). Qed.
Lemma lem4783222 {A : Type'} (_59006 : nat) (f : nat -> A) (h1 : term65 A f) : term1335 A f _59006.
Proof. exact (EQ_MP (@lem4783221 A f _59006) (@lem4783220 A _59006 f h1)). Qed.
Lemma lem4783223 {A : Type'} (_59006 : nat) (_59007 : nat) (f : nat -> A) (h1 : term65 A f) : term1394 A f _59006 _59007.
Proof. exact (@lem4783222 A _59006 f h1 _59007). Qed.
Lemma lem4783224 {A : Type'} (f : nat -> A) (_59006 : nat) (_59007 : nat) : (term1394 A f _59006 _59007) = (term1333 A f _59006 _59007).
Proof. exact (eq_refl (term1394 A f _59006 _59007)). Qed.
Lemma lem4783232 {A : Type'} (_59010 : nat -> A) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1395 A x' y' _59010.
Proof. exact (@lem4783054 A x' y' h1 _59010). Qed.
Lemma lem4783233 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) : (term1395 A x' y' _59010) = (term1390 A x' y' _59010).
Proof. exact (eq_refl (term1395 A x' y' _59010)). Qed.
Lemma lem4783234 {A : Type'} (_59010 : nat -> A) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1390 A x' y' _59010.
Proof. exact (EQ_MP (@lem4783233 A x' y' _59010) (@lem4783232 A _59010 x' y' h1)). Qed.
Lemma lem4783235 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1396 A x' y' _59010 _59011.
Proof. exact (@lem4783234 A _59010 x' y' h1 _59011). Qed.
Lemma lem4783236 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1396 A x' y' _59010 _59011) = (term1388 A x' y' _59010 _59011).
Proof. exact (eq_refl (term1396 A x' y' _59010 _59011)). Qed.
Lemma lem4783237 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1388 A x' y' _59010 _59011.
Proof. exact (EQ_MP (@lem4783236 A x' y' _59010 _59011) (@lem4783235 A _59010 _59011 x' y' h1)). Qed.
Lemma lem4783273 {A : Type'} (_59006 : nat) (_59007 : nat) (f : nat -> A) (h1 : term65 A f) : term1333 A f _59006 _59007.
Proof. exact (EQ_MP (@lem4783224 A f _59006 _59007) (@lem4783223 A _59006 _59007 f h1)). Qed.
Lemma lem4783275 {A : Type'} (f : nat -> A) (h1 : term812 A f) : term1341 A f.
Proof. exact (EQ_MP (@lem4782385 A f) (@lem4780696 A f h1)). Qed.
Lemma lem4783347 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1397 A x' y' _59010 _59011.
Proof. exact (proj1 (@lem4783237 A _59010 _59011 x' y' h1)). Qed.
Lemma lem4783357 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1398 A x' y' _59010 _59011.
Proof. exact (proj2 (@lem4783237 A _59010 _59011 x' y' h1)). Qed.
Lemma lem4783811 (h1 : @INFINITE nat (@UNIV nat)) : @I ((nat -> Prop) -> Prop) (@INFINITE nat) (@UNIV nat).
Proof. exact (EQ_MP (@lem4782394) (@lem4780702 h1)). Qed.
Lemma lem4783812 (h1 : @INFINITE nat (@UNIV nat)) : term1399.
Proof. exact (fun h0 : term1400 => @lem4783811 h1). Qed.
Lemma lem4783814 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4783815 : term1399 = (@I ((nat -> Prop) -> Prop) (@INFINITE nat) (@UNIV nat)).
Proof. exact (@lem4783814 (@I ((nat -> Prop) -> Prop) (@INFINITE nat) (@UNIV nat))). Qed.
Lemma lem4783816 (h1 : @INFINITE nat (@UNIV nat)) : @I ((nat -> Prop) -> Prop) (@INFINITE nat) (@UNIV nat).
Proof. exact (EQ_MP (@lem4783815) (@lem4783812 h1)). Qed.
Lemma lem4783819 {A : Type'} (f : nat -> A) (h1 : term1341 A f) : term1341 A f.
Proof. exact (h1). Qed.
Lemma lem4783820 {A : Type'} (f : nat -> A) (h1 : term1341 A f) : term1401 A f.
Proof. exact (fun h0 : term1340 A f => @lem4783819 A f h1). Qed.
Lemma lem4783822 (p : Prop) : (term1402 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4783823 {A : Type'} (f : nat -> A) : (term1401 A f) = (term1341 A f).
Proof. exact (@lem4783822 (term1340 A f)). Qed.
Lemma lem4783824 {A : Type'} (f : nat -> A) (h1 : term1341 A f) : term1341 A f.
Proof. exact (EQ_MP (@lem4783823 A f) (@lem4783820 A f h1)). Qed.
Lemma lem4783826 (b : Prop) (a : Prop) : (a \/ b) = (term397 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4783827 {A : Type'} (_59011 : nat -> Prop) (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) : (term1397 A x' y' _59010 _59011) = (term1403 A _59011 x' y' _59010).
Proof. exact (@lem4783826 (term1349 A _59010 _59011) ((term1358 A x' _59010) = (term1358 A y' _59010))). Qed.
Lemma lem4783829 (a : Prop) (b : Prop) : (term418 a b) = (term419 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4783830 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1404 A _59010 _59011) = (term1405 A _59010 _59011).
Proof. exact (@lem4783829 (term1346 _59011) (term1344 A _59010 _59011)). Qed.
Lemma lem4783832 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4783833 (_59011 : nat -> Prop) : (term1406 _59011) = (@I ((nat -> Prop) -> Prop) (@INFINITE nat) _59011).
Proof. exact (@lem4783832 (@I ((nat -> Prop) -> Prop) (@INFINITE nat) _59011)). Qed.
Lemma lem4783834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4783835 (_59011 : nat -> Prop) : (term1407 _59011) = (term1408 _59011).
Proof. exact (MK_COMB (@lem4783834) (@lem4783833 _59011)). Qed.
Lemma lem4783836 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1409 A _59010 _59011) = (term1409 A _59010 _59011).
Proof. exact (eq_refl (term1409 A _59010 _59011)). Qed.
Lemma lem4783837 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1405 A _59010 _59011) = (term1410 A _59010 _59011).
Proof. exact (MK_COMB (@lem4783835 _59011) (@lem4783836 A _59010 _59011)). Qed.
Lemma lem4783838 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1404 A _59010 _59011) = (term1410 A _59010 _59011).
Proof. exact (TRANS (@lem4783830 A _59010 _59011) (@lem4783837 A _59010 _59011)). Qed.
Lemma lem4783839 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4783840 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1411 A _59010 _59011) = (term1412 A _59010 _59011).
Proof. exact (MK_COMB (@lem4783839) (@lem4783838 A _59010 _59011)). Qed.
Lemma lem4783841 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) : ((term1358 A x' _59010) = (term1358 A y' _59010)) = ((term1358 A x' _59010) = (term1358 A y' _59010)).
Proof. exact (eq_refl ((term1358 A x' _59010) = (term1358 A y' _59010))). Qed.
Lemma lem4783842 {A : Type'} (_59011 : nat -> Prop) (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) : (term1403 A _59011 x' y' _59010) = (term1413 A _59011 x' y' _59010).
Proof. exact (MK_COMB (@lem4783840 A _59010 _59011) (@lem4783841 A x' y' _59010)). Qed.
Lemma lem4783843 {A : Type'} (_59011 : nat -> Prop) (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) : (term1397 A x' y' _59010 _59011) = (term1413 A _59011 x' y' _59010).
Proof. exact (TRANS (@lem4783827 A _59011 x' y' _59010) (@lem4783842 A _59011 x' y' _59010)). Qed.
Lemma lem4783845 {A : Type'} (f : nat -> A) (h1 : @INFINITE nat (@UNIV nat)) (h2 : term1341 A f) : term1414 A f.
Proof. exact (conj (@lem4783816 h1) (@lem4783824 A f h2)). Qed.
Lemma lem4783847 {A : Type'} (_59011 : nat -> Prop) (_59010 : nat -> A) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1413 A _59011 x' y' _59010.
Proof. exact (EQ_MP (@lem4783843 A _59011 x' y' _59010) (@lem4783347 A _59010 _59011 x' y' h1)). Qed.
Lemma lem4783848 {A : Type'} (_59011 : nat -> Prop) (_59010 : nat -> A) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1413 A _59011 x' y' _59010.
Proof. exact (@lem4783847 A _59011 _59010 x' y' h1). Qed.
Lemma lem4783849 {A : Type'} (f : nat -> A) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1415 A x' y' f.
Proof. exact (@lem4783848 A (@UNIV nat) f x' y' h1). Qed.
Lemma lem4783852 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : @INFINITE nat (@UNIV nat)) (h3 : term1341 A f) : (term1358 A x' f) = (term1358 A y' f).
Proof. exact (@lem4783849 A f x' y' h1 (@lem4783845 A f h2 h3)). Qed.
Lemma lem4783853 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : @INFINITE nat (@UNIV nat)) (h3 : term1341 A f) : term1416 A x' y' f.
Proof. exact (fun h0 : term1417 A x' y' f => @lem4783852 A x' y' f h1 h2 h3). Qed.
Lemma lem4783855 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4783856 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1416 A x' y' f) = ((term1358 A x' f) = (term1358 A y' f)).
Proof. exact (@lem4783855 ((term1358 A x' f) = (term1358 A y' f))). Qed.
Lemma lem4783857 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : @INFINITE nat (@UNIV nat)) (h3 : term1341 A f) : (term1358 A x' f) = (term1358 A y' f).
Proof. exact (EQ_MP (@lem4783856 A x' y' f) (@lem4783853 A x' y' f h1 h2 h3)). Qed.
Lemma lem4783863 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4783864 {A : Type'} (_59006 : nat) (f : nat -> A) (_59007 : nat) : (term1333 A f _59006 _59007) = (term1418 A _59006 f _59007).
Proof. exact (@lem4783863 (_59006 = _59007) (term1330 A _59006 f _59007)). Qed.
Lemma lem4783874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4783875 {A : Type'} (_59006 : nat) (f : nat -> A) (_59007 : nat) : (term1419 A f _59006 _59007) = (term1420 A _59006 f _59007).
Proof. exact (MK_COMB (@lem4783874) (@lem4783864 A _59006 f _59007)). Qed.
Lemma lem4783885 {A : Type'} (_59006 : nat) (f : nat -> A) (_59007 : nat) : (term1418 A _59006 f _59007) = (term1418 A _59006 f _59007).
Proof. exact (eq_refl (term1418 A _59006 f _59007)). Qed.
Lemma lem4783886 {A : Type'} (_59006 : nat) (f : nat -> A) (_59007 : nat) : ((term1333 A f _59006 _59007) = (term1418 A _59006 f _59007)) = ((term1418 A _59006 f _59007) = (term1418 A _59006 f _59007)).
Proof. exact (MK_COMB (@lem4783875 A _59006 f _59007) (@lem4783885 A _59006 f _59007)). Qed.
Lemma lem4783888 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4783889 (x : Prop) : (x = x) = True.
Proof. exact (@lem4783888 Prop x). Qed.
Lemma lem4783890 {A : Type'} (_59006 : nat) (f : nat -> A) (_59007 : nat) : ((term1418 A _59006 f _59007) = (term1418 A _59006 f _59007)) = True.
Proof. exact (@lem4783889 (term1418 A _59006 f _59007)). Qed.
Lemma lem4783891 {A : Type'} (_59006 : nat) (f : nat -> A) (_59007 : nat) : ((term1333 A f _59006 _59007) = (term1418 A _59006 f _59007)) = True.
Proof. exact (TRANS (@lem4783886 A _59006 f _59007) (@lem4783890 A _59006 f _59007)). Qed.
Lemma lem4783892 {A : Type'} (_59006 : nat) (f : nat -> A) (_59007 : nat) : True = ((term1333 A f _59006 _59007) = (term1418 A _59006 f _59007)).
Proof. exact (SYM (@lem4783891 A _59006 f _59007)). Qed.
Lemma lem4783893 {A : Type'} (_59006 : nat) (f : nat -> A) (_59007 : nat) : (term1333 A f _59006 _59007) = (term1418 A _59006 f _59007).
Proof. exact (EQ_MP (@lem4783892 A _59006 f _59007) (@lem0)). Qed.
Lemma lem4783894 {A : Type'} (_59006 : nat) (_59007 : nat) (f : nat -> A) (h1 : term65 A f) : term1418 A _59006 f _59007.
Proof. exact (EQ_MP (@lem4783893 A _59006 f _59007) (@lem4783273 A _59006 _59007 f h1)). Qed.
Lemma lem4783896 (b : Prop) (a : Prop) : (a \/ b) = (term397 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4783897 {A : Type'} (f : nat -> A) (_59006 : nat) (_59007 : nat) : (term1418 A _59006 f _59007) = (term1421 A f _59006 _59007).
Proof. exact (@lem4783896 (term1330 A _59006 f _59007) (_59006 = _59007)). Qed.
Lemma lem4783899 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4783900 {A : Type'} (_59006 : nat) (f : nat -> A) (_59007 : nat) : (term1422 A _59006 f _59007) = ((@I (nat -> A) f _59006) = (@I (nat -> A) f _59007)).
Proof. exact (@lem4783899 ((@I (nat -> A) f _59006) = (@I (nat -> A) f _59007))). Qed.
Lemma lem4783901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4783902 {A : Type'} (_59006 : nat) (f : nat -> A) (_59007 : nat) : (term1423 A _59006 f _59007) = (term1424 A _59006 f _59007).
Proof. exact (MK_COMB (@lem4783901) (@lem4783900 A _59006 f _59007)). Qed.
Lemma lem4783903 (_59006 : nat) (_59007 : nat) : (_59006 = _59007) = (_59006 = _59007).
Proof. exact (eq_refl (_59006 = _59007)). Qed.
Lemma lem4783904 {A : Type'} (f : nat -> A) (_59006 : nat) (_59007 : nat) : (term1421 A f _59006 _59007) = (term1425 A f _59006 _59007).
Proof. exact (MK_COMB (@lem4783902 A _59006 f _59007) (@lem4783903 _59006 _59007)). Qed.
Lemma lem4783905 {A : Type'} (f : nat -> A) (_59006 : nat) (_59007 : nat) : (term1418 A _59006 f _59007) = (term1425 A f _59006 _59007).
Proof. exact (TRANS (@lem4783897 A f _59006 _59007) (@lem4783904 A f _59006 _59007)). Qed.
Lemma lem4783908 {A : Type'} (_59006 : nat) (_59007 : nat) (f : nat -> A) (h1 : term65 A f) : term1425 A f _59006 _59007.
Proof. exact (EQ_MP (@lem4783905 A f _59006 _59007) (@lem4783894 A _59006 _59007 f h1)). Qed.
Lemma lem4783909 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term65 A f) : term1426 A x' y' f.
Proof. exact (@lem4783908 A (@I ((nat -> A) -> nat) x' f) (@I ((nat -> A) -> nat) y' f) f h1). Qed.
Lemma lem4783912 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) (h4 : term1341 A f) : (@I ((nat -> A) -> nat) x' f) = (@I ((nat -> A) -> nat) y' f).
Proof. exact (@lem4783909 A x' y' f h2 (@lem4783857 A x' y' f h1 h3 h4)). Qed.
Lemma lem4783913 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) (h4 : term1341 A f) : term1427 A x' y' f.
Proof. exact (fun h0 : term1355 A x' y' f => @lem4783912 A x' y' f h1 h2 h3 h4). Qed.
Lemma lem4783915 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4783916 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) : (term1427 A x' y' f) = ((@I ((nat -> A) -> nat) x' f) = (@I ((nat -> A) -> nat) y' f)).
Proof. exact (@lem4783915 ((@I ((nat -> A) -> nat) x' f) = (@I ((nat -> A) -> nat) y' f))). Qed.
Lemma lem4783917 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) (h4 : term1341 A f) : (@I ((nat -> A) -> nat) x' f) = (@I ((nat -> A) -> nat) y' f).
Proof. exact (EQ_MP (@lem4783916 A x' y' f) (@lem4783913 A x' y' f h1 h2 h3 h4)). Qed.
Lemma lem4783919 (h1 : @INFINITE nat (@UNIV nat)) : @I ((nat -> Prop) -> Prop) (@INFINITE nat) (@UNIV nat).
Proof. exact (EQ_MP (@lem4782394) (@lem4780702 h1)). Qed.
Lemma lem4783920 (h1 : @INFINITE nat (@UNIV nat)) : term1399.
Proof. exact (fun h0 : term1400 => @lem4783919 h1). Qed.
Lemma lem4783922 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4783923 : term1399 = (@I ((nat -> Prop) -> Prop) (@INFINITE nat) (@UNIV nat)).
Proof. exact (@lem4783922 (@I ((nat -> Prop) -> Prop) (@INFINITE nat) (@UNIV nat))). Qed.
Lemma lem4783924 (h1 : @INFINITE nat (@UNIV nat)) : @I ((nat -> Prop) -> Prop) (@INFINITE nat) (@UNIV nat).
Proof. exact (EQ_MP (@lem4783923) (@lem4783920 h1)). Qed.
Lemma lem4783942 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4783943 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1349 A _59010 _59011) = (term1428 A _59010 _59011).
Proof. exact (@lem4783942 (term1344 A _59010 _59011) (term1346 _59011)). Qed.
Lemma lem4783949 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) : (term1429 A x' y' _59010) = (term1429 A x' y' _59010).
Proof. exact (eq_refl (term1429 A x' y' _59010)). Qed.
Lemma lem4783950 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1398 A x' y' _59010 _59011) = (term1430 A x' y' _59010 _59011).
Proof. exact (MK_COMB (@lem4783949 A x' y' _59010) (@lem4783943 A _59010 _59011)). Qed.
Lemma lem4783954 (q : Prop) (p : Prop) (r : Prop) : (term412 p q r) = (term412 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4783955 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1430 A x' y' _59010 _59011) = (term1431 A x' y' _59010 _59011).
Proof. exact (@lem4783954 (term1344 A _59010 _59011) (term1355 A x' y' _59010) (term1346 _59011)). Qed.
Lemma lem4783973 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1398 A x' y' _59010 _59011) = (term1431 A x' y' _59010 _59011).
Proof. exact (TRANS (@lem4783950 A x' y' _59010 _59011) (@lem4783955 A x' y' _59010 _59011)). Qed.
Lemma lem4783974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4783975 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1432 A x' y' _59010 _59011) = (term1433 A x' y' _59010 _59011).
Proof. exact (MK_COMB (@lem4783974) (@lem4783973 A x' y' _59010 _59011)). Qed.
Lemma lem4783993 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1431 A x' y' _59010 _59011) = (term1431 A x' y' _59010 _59011).
Proof. exact (eq_refl (term1431 A x' y' _59010 _59011)). Qed.
Lemma lem4783994 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : ((term1398 A x' y' _59010 _59011) = (term1431 A x' y' _59010 _59011)) = ((term1431 A x' y' _59010 _59011) = (term1431 A x' y' _59010 _59011)).
Proof. exact (MK_COMB (@lem4783975 A x' y' _59010 _59011) (@lem4783993 A x' y' _59010 _59011)). Qed.
Lemma lem4783996 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4783997 (x : Prop) : (x = x) = True.
Proof. exact (@lem4783996 Prop x). Qed.
Lemma lem4783998 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : ((term1431 A x' y' _59010 _59011) = (term1431 A x' y' _59010 _59011)) = True.
Proof. exact (@lem4783997 (term1431 A x' y' _59010 _59011)). Qed.
Lemma lem4783999 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : ((term1398 A x' y' _59010 _59011) = (term1431 A x' y' _59010 _59011)) = True.
Proof. exact (TRANS (@lem4783994 A x' y' _59010 _59011) (@lem4783998 A x' y' _59010 _59011)). Qed.
Lemma lem4784000 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : True = ((term1398 A x' y' _59010 _59011) = (term1431 A x' y' _59010 _59011)).
Proof. exact (SYM (@lem4783999 A x' y' _59010 _59011)). Qed.
Lemma lem4784001 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1398 A x' y' _59010 _59011) = (term1431 A x' y' _59010 _59011).
Proof. exact (EQ_MP (@lem4784000 A x' y' _59010 _59011) (@lem0)). Qed.
Lemma lem4784002 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1431 A x' y' _59010 _59011.
Proof. exact (EQ_MP (@lem4784001 A x' y' _59010 _59011) (@lem4783357 A _59010 _59011 x' y' h1)). Qed.
Lemma lem4784004 (b : Prop) (a : Prop) : (a \/ b) = (term397 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4784005 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1431 A x' y' _59010 _59011) = (term1434 A x' y' _59010 _59011).
Proof. exact (@lem4784004 (term1435 A x' y' _59010 _59011) (term1344 A _59010 _59011)). Qed.
Lemma lem4784007 (a : Prop) (b : Prop) : (term418 a b) = (term419 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4784008 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1436 A x' y' _59010 _59011) = (term1437 A x' y' _59010 _59011).
Proof. exact (@lem4784007 (term1355 A x' y' _59010) (term1346 _59011)). Qed.
Lemma lem4784010 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4784011 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) : (term1438 A x' y' _59010) = ((@I ((nat -> A) -> nat) x' _59010) = (@I ((nat -> A) -> nat) y' _59010)).
Proof. exact (@lem4784010 ((@I ((nat -> A) -> nat) x' _59010) = (@I ((nat -> A) -> nat) y' _59010))). Qed.
Lemma lem4784012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4784013 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) : (term1439 A x' y' _59010) = (term1440 A x' y' _59010).
Proof. exact (MK_COMB (@lem4784012) (@lem4784011 A x' y' _59010)). Qed.
Lemma lem4784015 (a : Prop) : (term277 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4784016 (_59011 : nat -> Prop) : (term1406 _59011) = (@I ((nat -> Prop) -> Prop) (@INFINITE nat) _59011).
Proof. exact (@lem4784015 (@I ((nat -> Prop) -> Prop) (@INFINITE nat) _59011)). Qed.
Lemma lem4784017 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1437 A x' y' _59010 _59011) = (term1441 A x' y' _59010 _59011).
Proof. exact (MK_COMB (@lem4784013 A x' y' _59010) (@lem4784016 _59011)). Qed.
Lemma lem4784018 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1436 A x' y' _59010 _59011) = (term1441 A x' y' _59010 _59011).
Proof. exact (TRANS (@lem4784008 A x' y' _59010 _59011) (@lem4784017 A x' y' _59010 _59011)). Qed.
Lemma lem4784019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4784020 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1442 A x' y' _59010 _59011) = (term1443 A x' y' _59010 _59011).
Proof. exact (MK_COMB (@lem4784019) (@lem4784018 A x' y' _59010 _59011)). Qed.
Lemma lem4784021 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1344 A _59010 _59011) = (term1344 A _59010 _59011).
Proof. exact (eq_refl (term1344 A _59010 _59011)). Qed.
Lemma lem4784022 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1434 A x' y' _59010 _59011) = (term1444 A x' y' _59010 _59011).
Proof. exact (MK_COMB (@lem4784020 A x' y' _59010 _59011) (@lem4784021 A _59010 _59011)). Qed.
Lemma lem4784023 {A : Type'} (x' : type977 A) (y' : type977 A) (_59010 : nat -> A) (_59011 : nat -> Prop) : (term1431 A x' y' _59010 _59011) = (term1444 A x' y' _59010 _59011).
Proof. exact (TRANS (@lem4784005 A x' y' _59010 _59011) (@lem4784022 A x' y' _59010 _59011)). Qed.
Lemma lem4784025 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) (h4 : term1341 A f) : term1445 A x' y' f.
Proof. exact (conj (@lem4783917 A x' y' f h1 h2 h3 h4) (@lem4783924 h3)). Qed.
Lemma lem4784027 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1444 A x' y' _59010 _59011.
Proof. exact (EQ_MP (@lem4784023 A x' y' _59010 _59011) (@lem4784002 A _59010 _59011 x' y' h1)). Qed.
Lemma lem4784028 {A : Type'} (_59010 : nat -> A) (_59011 : nat -> Prop) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1444 A x' y' _59010 _59011.
Proof. exact (@lem4784027 A _59010 _59011 x' y' h1). Qed.
Lemma lem4784029 {A : Type'} (f : nat -> A) (x' : type977 A) (y' : type977 A) (h1 : term1323 A x' y') : term1446 A x' y' f.
Proof. exact (@lem4784028 A f (@UNIV nat) x' y' h1). Qed.
Lemma lem4784032 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) (h4 : term1341 A f) : term1340 A f.
Proof. exact (@lem4784029 A f x' y' h1 (@lem4784025 A x' y' f h1 h2 h3 h4)). Qed.
Lemma lem4784033 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) : term1447 A f.
Proof. exact (fun h0 : term1341 A f => @lem4784032 A x' y' f h1 h2 h3 h0). Qed.
Lemma lem4784035 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4784036 {A : Type'} (f : nat -> A) : (term1447 A f) = (term1340 A f).
Proof. exact (@lem4784035 (term1340 A f)). Qed.
Lemma lem4784037 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) : term1340 A f.
Proof. exact (EQ_MP (@lem4784036 A f) (@lem4784033 A x' y' f h1 h2 h3)). Qed.
Lemma lem4784040 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4784042 {A : Type'} (f : nat -> A) : (term1341 A f) = (term1448 A f).
Proof. exact (@lem4784040 (term1340 A f)). Qed.
Lemma lem4784045 {A : Type'} (f : nat -> A) (h1 : term812 A f) : term1448 A f.
Proof. exact (EQ_MP (@lem4784042 A f) (@lem4783275 A f h1)). Qed.
Lemma lem4784048 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) (h4 : term812 A f) : False.
Proof. exact (@lem4784045 A f h4 (@lem4784037 A x' y' f h1 h2 h3)). Qed.
Lemma lem4784049 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) (h4 : term812 A f) : term445.
Proof. exact (fun h0 : ~ False => @lem4784048 A x' y' f h1 h2 h3 h4). Qed.
Lemma lem4784051 (p : Prop) : (term393 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4784052 : term445 = False.
Proof. exact (@lem4784051 False). Qed.
Lemma lem4784053 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) (h4 : term812 A f) : False.
Proof. exact (EQ_MP (@lem4784052) (@lem4784049 A x' y' f h1 h2 h3 h4)). Qed.
Lemma lem4784054 {A : Type'} (x' : type977 A) (y' : type977 A) (x'''' : type487 A) (f : nat -> A) (h1 : term1323 A x' y') (h2 : term65 A f) (h3 : term1003 A x'''') (h4 : @INFINITE nat (@UNIV nat)) (h5 : term812 A f) : False.
Proof. exact (ex_elim (@lem4782296 A x'''' h3) (fun y'''' : type487 A => fun h0 : term1002 A x'''' y'''' => @lem4784053 A x' y' f h1 h2 h4 h5)). Qed.
Lemma lem4784055 {A : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term813 A) (h2 : term1323 A x' y') (h3 : term65 A f) (h4 : @INFINITE nat (@UNIV nat)) (h5 : term812 A f) : False.
Proof. exact (ex_elim (@lem4781019 A h1) (fun x'''' : type487 A => fun h0 : term1004 A x'''' => @lem4784054 A x' y' x'''' f h2 h3 h0 h4 h5)). Qed.
Lemma lem4784056 {A B : Type'} (x' : type977 A) (y' : type977 A) (x''' : type569 A B) (f : nat -> A) (h1 : term813 A) (h2 : term1323 A x' y') (h3 : term65 A f) (h4 : term1111 A B x''') (h5 : @INFINITE nat (@UNIV nat)) (h6 : term812 A f) : False.
Proof. exact (ex_elim (@lem4782294 A B x''' h4) (fun y''' : type569 A B => fun h0 : term1110 A B x''' y''' => @lem4784055 A x' y' f h1 h2 h3 h5 h6)). Qed.
Lemma lem4784057 {A B : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term1323 A x' y') (h4 : term65 A f) (h5 : @INFINITE nat (@UNIV nat)) (h6 : term812 A f) : False.
Proof. exact (ex_elim (@lem4781336 A B h2) (fun x''' : type569 A B => fun h0 : term1112 A B x''' => @lem4784056 A B x' y' x''' f h1 h3 h4 h0 h5 h6)). Qed.
Lemma lem4784058 {A B : Type'} (x' : type977 A) (y' : type977 A) (x'' : type703 A) (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term1323 A x' y') (h4 : term65 A f) (h5 : term1219 A x'') (h6 : @INFINITE nat (@UNIV nat)) (h7 : term812 A f) : False.
Proof. exact (ex_elim (@lem4782292 A x'' h5) (fun y'' : type703 A => fun h0 : term1218 A x'' y'' => @lem4784057 A B x' y' f h1 h2 h3 h4 h6 h7)). Qed.
Lemma lem4784059 {A B : Type'} (x' : type977 A) (y' : type977 A) (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term1323 A x' y') (h5 : term65 A f) (h6 : @INFINITE nat (@UNIV nat)) (h7 : term812 A f) : False.
Proof. exact (ex_elim (@lem4781653 A h3) (fun x'' : type703 A => fun h0 : term1220 A x'' => @lem4784058 A B x' y' x'' f h1 h2 h4 h5 h0 h6 h7)). Qed.
Lemma lem4784060 {A B : Type'} (x' : type977 A) (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term65 A f) (h5 : term1326 A x') (h6 : @INFINITE nat (@UNIV nat)) (h7 : term812 A f) : False.
Proof. exact (ex_elim (@lem4782290 A x' h5) (fun y' : type977 A => fun h0 : term1325 A x' y' => @lem4784059 A B x' y' f h1 h2 h3 h0 h4 h6 h7)). Qed.
Lemma lem4784061 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term816 A) (h5 : term65 A f) (h6 : @INFINITE nat (@UNIV nat)) (h7 : term812 A f) : False.
Proof. exact (ex_elim (@lem4781970 A h4) (fun x' : type977 A => fun h0 : term1327 A x' => @lem4784060 A B x' f h1 h2 h3 h5 h0 h6 h7)). Qed.
Lemma lem4784062 {A B : Type'} (x : type977 B) (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term816 A) (h5 : term65 A f) (h6 : term1326 B x) (h7 : @INFINITE nat (@UNIV nat)) (h8 : term812 A f) : False.
Proof. exact (ex_elim (@lem4782288 B x h6) (fun y : type977 B => fun h0 : term1325 B x y => @lem4784061 A B f h1 h2 h3 h4 h5 h7 h8)). Qed.
Lemma lem4784063 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term816 A) (h5 : term816 B) (h6 : term65 A f) (h7 : @INFINITE nat (@UNIV nat)) (h8 : term812 A f) : False.
Proof. exact (ex_elim (@lem4782287 B h5) (fun x : type977 B => fun h0 : term1327 B x => @lem4784062 A B x f h1 h2 h3 h4 h6 h0 h7 h8)). Qed.
Lemma lem4784064 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term816 A) (h5 : term816 B) (h6 : term65 A f) (h7 : @INFINITE nat (@UNIV nat)) (h8 : term812 A f) : (@INFINITE nat (@UNIV nat)) = False.
Proof. exact (prop_ext (fun h9 : @INFINITE nat (@UNIV nat) => @lem4784063 A B f h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem4780702 h7)). Qed.
Lemma lem4784065 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term816 A) (h5 : term816 B) (h6 : term65 A f) (h7 : @INFINITE nat (@UNIV nat)) (h8 : term812 A f) : False.
Proof. exact (EQ_MP (@lem4784064 A B f h1 h2 h3 h4 h5 h6 h7 h8) (@lem4780702 h7)). Qed.
Lemma lem4784066 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term816 A) (h5 : term816 B) (h6 : term65 A f) (h7 : @INFINITE nat (@UNIV nat)) (h8 : term812 A f) : (term812 A f) = False.
Proof. exact (prop_ext (fun h9 : term812 A f => @lem4784065 A B f h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem4780696 A f h8)). Qed.
Lemma lem4784067 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term816 A) (h5 : term816 B) (h6 : term65 A f) (h7 : @INFINITE nat (@UNIV nat)) (h8 : term812 A f) : False.
Proof. exact (EQ_MP (@lem4784066 A B f h1 h2 h3 h4 h5 h6 h7 h8) (@lem4780696 A f h8)). Qed.
Lemma lem4784068 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term816 A) (h5 : term65 A f) (h6 : @INFINITE nat (@UNIV nat)) (h7 : term812 A f) : term821 B.
Proof. exact (fun h0 : term816 B => @lem4784067 A B f h1 h2 h3 h4 h0 h5 h6 h7). Qed.
Lemma lem4784069 {B : Type'} : (term821 B) = (term822 B).
Proof. exact (@lem69 (term816 B)). Qed.
Lemma lem4784070 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term816 A) (h5 : term65 A f) (h6 : @INFINITE nat (@UNIV nat)) (h7 : term812 A f) : term822 B.
Proof. exact (EQ_MP (@lem4784069 B) (@lem4784068 A B f h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem4784071 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term814 A) (h4 : term65 A f) (h5 : @INFINITE nat (@UNIV nat)) (h6 : term812 A f) : term825 A B.
Proof. exact (fun h0 : term816 A => @lem4784070 A B f h1 h2 h3 h0 h4 h5 h6). Qed.
Lemma lem4784072 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term815 A B) (h3 : term65 A f) (h4 : @INFINITE nat (@UNIV nat)) (h5 : term812 A f) : term828 A B.
Proof. exact (fun h0 : term814 A => @lem4784071 A B f h1 h2 h0 h3 h4 h5). Qed.
Lemma lem4784073 {A B : Type'} (f : nat -> A) (h1 : term813 A) (h2 : term65 A f) (h3 : @INFINITE nat (@UNIV nat)) (h4 : term812 A f) : term831 A B.
Proof. exact (fun h0 : term815 A B => @lem4784072 A B f h1 h0 h2 h3 h4). Qed.
Lemma lem4784074 {A B : Type'} (f : nat -> A) (h1 : term65 A f) (h2 : @INFINITE nat (@UNIV nat)) (h3 : term812 A f) : term834 A B.
Proof. exact (fun h0 : term813 A => @lem4784073 A B f h0 h1 h2 h3). Qed.
Lemma lem4784075 {A B : Type'} (f : nat -> A) (h1 : term65 A f) (h2 : term812 A f) : term837 A B.
Proof. exact (fun h0 : @INFINITE nat (@UNIV nat) => @lem4784074 A B f h1 h0 h2). Qed.
Lemma lem4784076 {A B : Type'} (f : nat -> A) (h1 : term65 A f) : term840 A B f.
Proof. exact (fun h0 : term812 A f => @lem4784075 A B f h1 h0). Qed.
Lemma lem4784077 {A B : Type'} (f : nat -> A) : term843 A B f.
Proof. exact (fun h0 : term65 A f => @lem4784076 A B f h0). Qed.
Lemma lem4784078 {A B : Type'} (s : A -> Prop) (f : nat -> A) : term845 A B s f.
Proof. exact (fun h0 : term66 A f s => @lem4784077 A B f). Qed.
Lemma lem4784083 {A B : Type'} (f : nat -> A) : term849 A B f.
Proof. exact (fun s : A -> Prop => @lem4784078 A B s f). Qed.
Lemma lem4784088 {A B : Type'} : term853 A B.
Proof. exact (fun f : nat -> A => @lem4784083 A B f). Qed.
Lemma lem4784089 {A B : Type'} : term852 A B.
Proof. exact (EQ_MP (@lem4780598 A B) (@lem4784088 A B)). Qed.
Lemma lem4784090 {A B : Type'} (f : nat -> A) : term1449 A B f.
Proof. exact (@lem4784089 A B f). Qed.
Lemma lem4784091 {A B : Type'} (f : nat -> A) : (term1449 A B f) = (term848 A B f).
Proof. exact (eq_refl (term1449 A B f)). Qed.
Lemma lem4784092 {A B : Type'} (f : nat -> A) : term848 A B f.
Proof. exact (EQ_MP (@lem4784091 A B f) (@lem4784090 A B f)). Qed.
Lemma lem4784093 {A B : Type'} (f : nat -> A) (s : A -> Prop) : term1450 A B f s.
Proof. exact (@lem4784092 A B f s). Qed.
Lemma lem4784094 {A B : Type'} (s : A -> Prop) (f : nat -> A) : (term1450 A B f s) = (term817 A B s f).
Proof. exact (eq_refl (term1450 A B f s)). Qed.
Lemma lem4784095 {A B : Type'} (s : A -> Prop) (f : nat -> A) : term817 A B s f.
Proof. exact (EQ_MP (@lem4784094 A B s f) (@lem4784093 A B f s)). Qed.
Lemma lem4784097 {A B : Type'} (s : A -> Prop) (f : nat -> A) : term817 A B s f.
Proof. exact (@lem4780019 A B s f (@lem4784095 A B s f)). Qed.
Lemma lem4784098 {A B : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term66 A f s) : term842 A B f.
Proof. exact (@lem4784097 A B s f (@lem4774417 A f s h1)). Qed.
Lemma lem4784099 {A B : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term65 A f) (h2 : term66 A f s) : term839 A B f.
Proof. exact (@lem4784098 A B f s h2 (@lem4774416 A f h1)). Qed.
Lemma lem4784100 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term65 A f) (h2 : term66 A f s) (h3 : term812 A f) : term836 A B.
Proof. exact (@lem4784099 A B f s h1 h2 (@lem4779996 A f h3)). Qed.
Lemma lem4784101 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term65 A f) (h2 : term66 A f s) (h3 : term812 A f) : term833 A B.
Proof. exact (@lem4784100 A B s f h1 h2 h3 (@lem4629194)). Qed.
Lemma lem4784102 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term65 A f) (h2 : term66 A f s) (h3 : term812 A f) : term830 A B.
Proof. exact (@lem4784101 A B s f h1 h2 h3 (@lem4779997 A)). Qed.
Lemma lem4784103 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term65 A f) (h2 : term66 A f s) (h3 : term812 A f) : term827 A B.
Proof. exact (@lem4784102 A B s f h1 h2 h3 (@lem4779999 A B)). Qed.
Lemma lem4784104 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term65 A f) (h2 : term66 A f s) (h3 : term812 A f) : term824 A B.
Proof. exact (@lem4784103 A B s f h1 h2 h3 (@lem4779998 A)). Qed.
Lemma lem4784105 {A B : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term65 A f) (h2 : term66 A f s) (h3 : term812 A f) : term821 B.
Proof. exact (@lem4784104 A B s f h1 h2 h3 (@lem4780003 A)). Qed.
Lemma lem4784106 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term65 A f) (h2 : term66 A f s) (h3 : term812 A f) : False.
Proof. exact (@lem4784105 A Prop s f h1 h2 h3 (@lem4780000 Prop)). Qed.
Lemma lem4784107 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term65 A f) (h2 : term66 A f s) (h3 : term812 A f) : (term812 A f) = False.
Proof. exact (prop_ext (fun h4 : term812 A f => @lem4784106 A s f h1 h2 h3) (fun h4 : False => @lem4779996 A f h3)). Qed.
Lemma lem4784108 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term65 A f) (h2 : term66 A f s) (h3 : term812 A f) : False.
Proof. exact (EQ_MP (@lem4784107 A s f h1 h2 h3) (@lem4779996 A f h3)). Qed.
Lemma lem4784109 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term65 A f) (h2 : term66 A f s) : term811 A f.
Proof. exact (fun h0 : term812 A f => @lem4784108 A s f h1 h2 h0). Qed.
Lemma lem4784110 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term65 A f) (h2 : term66 A f s) : term810 A f.
Proof. exact (EQ_MP (@lem4779995 A f) (@lem4784109 A f s h1 h2)). Qed.
Lemma lem4784111 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term65 A f) (h2 : term66 A f s) : term808 A f s.
Proof. exact (EQ_MP (@lem4779991 A f s h2) (@lem4784110 A f s h1 h2)). Qed.
Lemma lem4784112 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term65 A f) (h2 : term66 A f s) : term7 A s.
Proof. exact (ex_intro (term8 A s) (@IMAGE nat A f (@UNIV nat)) (@lem4784111 A f s h1 h2)). Qed.
Lemma lem4784113 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term65 A f) (h2 : term66 A f s) : @INFINITE A s.
Proof. exact (@lem4779909 A s (@lem4784112 A f s h1 h2)). Qed.
Lemma lem4784114 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term64 A s f) : term65 A f.
Proof. exact (proj2 (@lem4774415 A s f h1)). Qed.
Lemma lem4784115 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term64 A s f) : term66 A f s.
Proof. exact (proj1 (@lem4774415 A s f h1)). Qed.
Lemma lem4784116 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term65 A f) (h2 : term66 A f s) : (term65 A f) = (@INFINITE A s).
Proof. exact (prop_ext (fun h3 : term65 A f => @lem4784113 A f s h1 h2) (fun h3 : @INFINITE A s => @lem4774416 A f h1)). Qed.
Lemma lem4784117 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term65 A f) (h2 : term66 A f s) : @INFINITE A s.
Proof. exact (EQ_MP (@lem4784116 A f s h1 h2) (@lem4774416 A f h1)). Qed.
Lemma lem4784118 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term65 A f) (h2 : term66 A f s) : (term66 A f s) = (@INFINITE A s).
Proof. exact (prop_ext (fun h3 : term66 A f s => @lem4784117 A f s h1 h2) (fun h3 : @INFINITE A s => @lem4774417 A f s h2)). Qed.
Lemma lem4784119 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term65 A f) (h2 : term66 A f s) : @INFINITE A s.
Proof. exact (EQ_MP (@lem4784118 A f s h1 h2) (@lem4774417 A f s h2)). Qed.
Lemma lem4784120 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term66 A f s) (h2 : term64 A s f) : (term65 A f) = (@INFINITE A s).
Proof. exact (prop_ext (fun h3 : term65 A f => @lem4784119 A f s h3 h1) (fun h3 : @INFINITE A s => @lem4784114 A s f h2)). Qed.
Lemma lem4784121 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term66 A f s) (h2 : term64 A s f) : @INFINITE A s.
Proof. exact (EQ_MP (@lem4784120 A s f h1 h2) (@lem4784114 A s f h2)). Qed.
Lemma lem4784122 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term64 A s f) : (term66 A f s) = (@INFINITE A s).
Proof. exact (prop_ext (fun h2 : term66 A f s => @lem4784121 A s f h2 h1) (fun h2 : @INFINITE A s => @lem4784115 A s f h1)). Qed.
Lemma lem4784123 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term64 A s f) : @INFINITE A s.
Proof. exact (EQ_MP (@lem4784122 A s f h1) (@lem4784115 A s f h1)). Qed.
Lemma lem4784124 {A : Type'} (s : A -> Prop) (h1 : term63 A s) : @INFINITE A s.
Proof. exact (ex_elim (@lem4774414 A s h1) (fun f : nat -> A => fun h0 : term451 A s f => @lem4784123 A s f h0)). Qed.
Lemma lem4784125 {A : Type'} (s : A -> Prop) : term1451 A s.
Proof. exact (fun h0 : term63 A s => @lem4784124 A s h0). Qed.
Lemma lem4784126 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : (@INFINITE A s) = (term63 A s).
Proof. exact (prop_ext (fun h2 : @INFINITE A s => @lem4779905 A s h1) (fun h2 : term63 A s => @lem4774413 A s h1)). Qed.
Lemma lem4784127 {A : Type'} (s : A -> Prop) (h1 : @INFINITE A s) : term63 A s.
Proof. exact (EQ_MP (@lem4784126 A s h1) (@lem4774413 A s h1)). Qed.
Lemma lem4784128 {A : Type'} (s : A -> Prop) : term1452 A s.
Proof. exact (fun h0 : @INFINITE A s => @lem4784127 A s h0). Qed.
Lemma lem4784129 {A : Type'} (s : A -> Prop) : term1453 A s.
Proof. exact (conj (@lem4784128 A s) (@lem4784125 A s)). Qed.
Lemma lem4784130 {A : Type'} (s : A -> Prop) : (term1453 A s) = ((@INFINITE A s) = (term63 A s)).
Proof. exact (@lem32 (@INFINITE A s) (term63 A s)). Qed.
Lemma lem4784131 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term63 A s).
Proof. exact (EQ_MP (@lem4784130 A s) (@lem4784129 A s)). Qed.
Lemma lem4784136 {A : Type'} : term1454 A.
Proof. exact (fun s : A -> Prop => @lem4784131 A s). Qed.
