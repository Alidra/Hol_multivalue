Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SUBSET_SIMPLE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import IN_DIFF_spec.
Require Import SUBSET_spec.
Require Import SUM_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem7173280 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7173281 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7173282 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7173281 t1) (@lem7173280 t1)). Qed.
Lemma lem7173283 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7173282 t1 t2). Qed.
Lemma lem7173284 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7173285 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7173284 t1 t2) (@lem7173283 t1 t2)). Qed.
Lemma lem7173286 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7173285 t1 t2 t3). Qed.
Lemma lem7173287 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7173288 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7173287 t1 t2 t3) (@lem7173286 t1 t2 t3)). Qed.
Lemma lem7173289 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7173288 t1 t2 t3)). Qed.
Lemma lem7173290 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7173291 {A : Type'} (u : A -> Prop) (h1 : term7 A) : term8 A u.
Proof. exact (@lem7173290 A h1 u). Qed.
Lemma lem7173292 {A : Type'} (u : A -> Prop) : (term8 A u) = (term9 A u).
Proof. exact (eq_refl (term8 A u)). Qed.
Lemma lem7173293 {A : Type'} (u : A -> Prop) (h1 : term7 A) : term9 A u.
Proof. exact (EQ_MP (@lem7173292 A u) (@lem7173291 A u h1)). Qed.
Lemma lem7173294 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term7 A) : term10 A u v.
Proof. exact (@lem7173293 A u h1 v). Qed.
Lemma lem7173295 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term10 A u v) = (term11 A u v).
Proof. exact (eq_refl (term10 A u v)). Qed.
Lemma lem7173296 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term7 A) : term11 A u v.
Proof. exact (EQ_MP (@lem7173295 A u v) (@lem7173294 A u v h1)). Qed.
Lemma lem7173297 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term7 A) : term12 A u v f.
Proof. exact (@lem7173296 A u v h1 f). Qed.
Lemma lem7173298 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term12 A u v f) = (term13 A u v f).
Proof. exact (eq_refl (term12 A u v f)). Qed.
Lemma lem7173299 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term7 A) : term13 A u v f.
Proof. exact (EQ_MP (@lem7173298 A u v f) (@lem7173297 A u v f h1)). Qed.
Lemma lem7173300 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term14 A v u f) : term14 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173301 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term7 A) (h2 : term14 A v u f) : term15 A u v f.
Proof. exact (@lem7173299 A u v f h1 (@lem7173300 A v u f h2)). Qed.
Lemma lem7173302 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term14 A v u f) : term16 A u v f.
Proof. exact (fun h0 : term7 A => @lem7173301 A v u f h0 h1). Qed.
Lemma lem7173303 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7173304 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term7 A) (h2 : term14 A v u f) : term15 A u v f.
Proof. exact (@lem7173302 A v u f h2 (@lem7173303 A h1)). Qed.
Lemma lem7173305 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term7 A) : term13 A u v f.
Proof. exact (fun h0 : term14 A v u f => @lem7173304 A v u f h1 h0). Qed.
Lemma lem7173306 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term7 A) : term11 A u v.
Proof. exact (fun f : A -> real => @lem7173305 A u v f h1). Qed.
Lemma lem7173307 {A : Type'} (u : A -> Prop) (h1 : term7 A) : term9 A u.
Proof. exact (fun v : A -> Prop => @lem7173306 A u v h1). Qed.
Lemma lem7173308 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (fun u : A -> Prop => @lem7173307 A u h1). Qed.
Lemma lem7173309 {A : Type'} : term17 A.
Proof. exact (fun h0 : term7 A => @lem7173308 A h0). Qed.
Lemma lem7173310 {A : Type'} : term7 A.
Proof. exact (@lem7173309 A (@lem7173279 A)). Qed.
Lemma lem7173311 {A : Type'} (u : A -> Prop) : term8 A u.
Proof. exact (@lem7173310 A u). Qed.
Lemma lem7173312 {A : Type'} (u : A -> Prop) : (term8 A u) = (term9 A u).
Proof. exact (eq_refl (term8 A u)). Qed.
Lemma lem7173313 {A : Type'} (u : A -> Prop) : term9 A u.
Proof. exact (EQ_MP (@lem7173312 A u) (@lem7173311 A u)). Qed.
Lemma lem7173314 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term10 A u v.
Proof. exact (@lem7173313 A u v). Qed.
Lemma lem7173315 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term10 A u v) = (term11 A u v).
Proof. exact (eq_refl (term10 A u v)). Qed.
Lemma lem7173316 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term11 A u v.
Proof. exact (EQ_MP (@lem7173315 A u v) (@lem7173314 A u v)). Qed.
Lemma lem7173317 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term12 A u v f.
Proof. exact (@lem7173316 A u v f). Qed.
Lemma lem7173318 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term12 A u v f) = (term13 A u v f).
Proof. exact (eq_refl (term12 A u v f)). Qed.
Lemma lem7173320 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term18 A v u f) : term18 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173321 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term19 A v u f) : term19 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173322 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7173323 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term20 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173324 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem7173326 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term13 A u v f.
Proof. exact (EQ_MP (@lem7173318 A u v f) (@lem7173317 A u v f)). Qed.
Lemma lem7173327 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term13 A u v f.
Proof. exact (@lem7173326 A u v f). Qed.
Lemma lem7173329 (p : Prop) : p = (term21 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7173330 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term14 A v u f) = (term22 A v u f).
Proof. exact (@lem7173329 (term14 A v u f)). Qed.
Lemma lem7173331 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term22 A v u f) = (term14 A v u f).
Proof. exact (SYM (@lem7173330 A v u f)). Qed.
Lemma lem7173332 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term23 A v u f) : term23 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173333 {A : Type'} : term24 A.
Proof. exact (@lem3205495 A). Qed.
Lemma lem7173335 {A : Type'} : term25 A.
Proof. exact (@lem3194148 A). Qed.
Lemma lem7173337 {A : Type'} : term26 A.
Proof. exact (@lem3599924 A). Qed.
Lemma lem7173341 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term27 A v u f) : term27 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173342 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term28 A v u f.
Proof. exact (fun h0 : term27 A v u f => @lem7173341 A v u f h0). Qed.
Lemma lem7173343 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term28 A v u f) : term28 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173344 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term27 A v u f) : term27 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173345 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term27 A v u f) (h2 : term28 A v u f) : term27 A v u f.
Proof. exact (@lem7173343 A v u f h2 (@lem7173344 A v u f h1)). Qed.
Lemma lem7173346 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term27 A v u f) : term29 A v u f.
Proof. exact (fun h0 : term28 A v u f => @lem7173345 A v u f h1 h0). Qed.
Lemma lem7173347 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term28 A v u f) : term28 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173348 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term27 A v u f) (h2 : term28 A v u f) : term27 A v u f.
Proof. exact (@lem7173346 A v u f h1 (@lem7173347 A v u f h2)). Qed.
Lemma lem7173349 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term28 A v u f) : term28 A v u f.
Proof. exact (fun h0 : term27 A v u f => @lem7173348 A v u f h0 h1). Qed.
Lemma lem7173350 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term30 A v u f.
Proof. exact (fun h0 : term28 A v u f => @lem7173349 A v u f h0). Qed.
Lemma lem7173353 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term28 A v u f.
Proof. exact (@lem7173350 A v u f (@lem7173342 A v u f)). Qed.
Lemma lem7173354 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term28 A v u f.
Proof. exact (@lem7173353 A v u f). Qed.
Lemma lem7173430 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7173431 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (@lem7173430 (term24 A)). Qed.
Lemma lem7173446 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (eq_refl (term33 A)). Qed.
Lemma lem7173447 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (MK_COMB (@lem7173446 A) (@lem7173431 A)). Qed.
Lemma lem7173450 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (eq_refl (term36 A)). Qed.
Lemma lem7173451 {A : Type'} : (term37 A) = (term38 A).
Proof. exact (MK_COMB (@lem7173450 A) (@lem7173447 A)). Qed.
Lemma lem7173454 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term39 A v u f) = (term39 A v u f).
Proof. exact (eq_refl (term39 A v u f)). Qed.
Lemma lem7173455 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term40 A v u f) = (term41 A v u f).
Proof. exact (MK_COMB (@lem7173454 A v u f) (@lem7173451 A)). Qed.
Lemma lem7173458 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term42 A v u f) = (term42 A v u f).
Proof. exact (eq_refl (term42 A v u f)). Qed.
Lemma lem7173459 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term43 A v u f) = (term44 A v u f).
Proof. exact (MK_COMB (@lem7173458 A v u f) (@lem7173455 A v u f)). Qed.
Lemma lem7173462 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term45 A u v) = (term45 A u v).
Proof. exact (eq_refl (term45 A u v)). Qed.
Lemma lem7173463 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term46 A v u f) = (term47 A v u f).
Proof. exact (MK_COMB (@lem7173462 A u v) (@lem7173459 A v u f)). Qed.
Lemma lem7173466 {A : Type'} (v : A -> Prop) : (term48 A v) = (term48 A v).
Proof. exact (eq_refl (term48 A v)). Qed.
Lemma lem7173467 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term27 A v u f) = (term49 A v u f).
Proof. exact (MK_COMB (@lem7173466 A v) (@lem7173463 A v u f)). Qed.
Lemma lem7173470 {A : Type'} (u : A -> Prop) (f : A -> real) : (term50 A u f) = (term51 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7173467 A v u f)). Qed.
Lemma lem7173471 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7173472 {A : Type'} (u : A -> Prop) (f : A -> real) : (term52 A u f) = (term53 A u f).
Proof. exact (MK_COMB (@lem7173471 A) (@lem7173470 A u f)). Qed.
Lemma lem7173477 {A : Type'} (f : A -> real) : (term54 A f) = (term55 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7173472 A u f)). Qed.
Lemma lem7173478 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7173479 {A : Type'} (f : A -> real) : (term56 A f) = (term57 A f).
Proof. exact (MK_COMB (@lem7173478 A) (@lem7173477 A f)). Qed.
Lemma lem7173484 {A : Type'} : (term58 A) = (term59 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7173479 A f)). Qed.
Lemma lem7173485 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7173494 {A : Type'} : (term60 A) = (term61 A).
Proof. exact (MK_COMB (@lem7173485 A) (@lem7173484 A)). Qed.
Lemma lem7173505 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term62 A x s t) = (term63 A s x t)) = ((term62 A x s t) = (term63 A s x t)).
Proof. exact (eq_refl ((term62 A x s t) = (term63 A s x t))). Qed.
Lemma lem7173506 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (fun_ext (fun x : A => @lem7173505 A s x t)). Qed.
Lemma lem7173507 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7173508 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem7173507 A) (@lem7173506 A s t)). Qed.
Lemma lem7173509 {A : Type'} (s : A -> Prop) : (term66 A s) = (term66 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7173508 A s t)). Qed.
Lemma lem7173510 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7173511 {A : Type'} (s : A -> Prop) : (term67 A s) = (term67 A s).
Proof. exact (MK_COMB (@lem7173510 A) (@lem7173509 A s)). Qed.
Lemma lem7173512 {A : Type'} : (term68 A) = (term68 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7173511 A s)). Qed.
Lemma lem7173513 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7173514 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem7173513 A) (@lem7173512 A)). Qed.
Lemma lem7173515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7173516 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (MK_COMB (@lem7173515) (@lem7173514 A)). Qed.
Lemma lem7173521 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term69 A s x t) = (term69 A s x t).
Proof. exact (eq_refl (term69 A s x t)). Qed.
Lemma lem7173522 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term70 A s t) = (term70 A s t).
Proof. exact (fun_ext (fun x : A => @lem7173521 A s x t)). Qed.
Lemma lem7173523 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7173524 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term71 A s t) = (term71 A s t).
Proof. exact (MK_COMB (@lem7173523 A) (@lem7173522 A s t)). Qed.
Lemma lem7173527 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term72 A s t) = (term72 A s t).
Proof. exact (eq_refl (term72 A s t)). Qed.
Lemma lem7173528 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term71 A s t)) = ((@SUBSET A s t) = (term71 A s t)).
Proof. exact (MK_COMB (@lem7173527 A s t) (@lem7173524 A s t)). Qed.
Lemma lem7173529 {A : Type'} (s : A -> Prop) : (term73 A s) = (term73 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7173528 A s t)). Qed.
Lemma lem7173530 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7173531 {A : Type'} (s : A -> Prop) : (term74 A s) = (term74 A s).
Proof. exact (MK_COMB (@lem7173530 A) (@lem7173529 A s)). Qed.
Lemma lem7173532 {A : Type'} : (term75 A) = (term75 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7173531 A s)). Qed.
Lemma lem7173533 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7173534 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem7173533 A) (@lem7173532 A)). Qed.
Lemma lem7173535 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7173536 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem7173535) (@lem7173534 A)). Qed.
Lemma lem7173537 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (MK_COMB (@lem7173536 A) (@lem7173516 A)). Qed.
Lemma lem7173546 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term76 A t s) = (term76 A t s).
Proof. exact (eq_refl (term76 A t s)). Qed.
Lemma lem7173547 {A : Type'} (s : A -> Prop) : (term77 A s) = (term77 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7173546 A t s)). Qed.
Lemma lem7173548 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7173549 {A : Type'} (s : A -> Prop) : (term78 A s) = (term78 A s).
Proof. exact (MK_COMB (@lem7173548 A) (@lem7173547 A s)). Qed.
Lemma lem7173550 {A : Type'} : (term79 A) = (term79 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7173549 A s)). Qed.
Lemma lem7173551 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7173552 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem7173551 A) (@lem7173550 A)). Qed.
Lemma lem7173553 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7173554 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem7173553) (@lem7173552 A)). Qed.
Lemma lem7173555 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (MK_COMB (@lem7173554 A) (@lem7173537 A)). Qed.
Lemma lem7173560 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term80 A v u f x) = (term80 A v u f x).
Proof. exact (eq_refl (term80 A v u f x)). Qed.
Lemma lem7173561 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term81 A v u f) = (term81 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7173560 A v u f x)). Qed.
Lemma lem7173562 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7173563 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term20 A v u f) = (term20 A v u f).
Proof. exact (MK_COMB (@lem7173562 A) (@lem7173561 A v u f)). Qed.
Lemma lem7173568 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term82 A u v f x) = (term82 A u v f x).
Proof. exact (eq_refl (term82 A u v f x)). Qed.
Lemma lem7173569 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term83 A u v f) = (term83 A u v f).
Proof. exact (fun_ext (fun x : A => @lem7173568 A u v f x)). Qed.
Lemma lem7173570 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7173571 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term84 A u v f) = (term84 A u v f).
Proof. exact (MK_COMB (@lem7173570 A) (@lem7173569 A u v f)). Qed.
Lemma lem7173572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7173573 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term85 A u v f) = (term85 A u v f).
Proof. exact (MK_COMB (@lem7173572) (@lem7173571 A u v f)). Qed.
Lemma lem7173574 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term86 A v u f) = (term86 A v u f).
Proof. exact (MK_COMB (@lem7173573 A u v f) (@lem7173563 A v u f)). Qed.
Lemma lem7173577 {A : Type'} (v : A -> Prop) : (term87 A v) = (term87 A v).
Proof. exact (eq_refl (term87 A v)). Qed.
Lemma lem7173578 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term88 A v u f) = (term88 A v u f).
Proof. exact (MK_COMB (@lem7173577 A v) (@lem7173574 A v u f)). Qed.
Lemma lem7173581 {A : Type'} (u : A -> Prop) : (term87 A u) = (term87 A u).
Proof. exact (eq_refl (term87 A u)). Qed.
Lemma lem7173582 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term14 A v u f) = (term14 A v u f).
Proof. exact (MK_COMB (@lem7173581 A u) (@lem7173578 A v u f)). Qed.
Lemma lem7173583 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7173584 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term23 A v u f) = (term23 A v u f).
Proof. exact (MK_COMB (@lem7173583) (@lem7173582 A v u f)). Qed.
Lemma lem7173585 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7173586 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term39 A v u f) = (term39 A v u f).
Proof. exact (MK_COMB (@lem7173585) (@lem7173584 A v u f)). Qed.
Lemma lem7173587 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term41 A v u f) = (term41 A v u f).
Proof. exact (MK_COMB (@lem7173586 A v u f) (@lem7173555 A)). Qed.
Lemma lem7173592 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term80 A v u f x) = (term80 A v u f x).
Proof. exact (eq_refl (term80 A v u f x)). Qed.
Lemma lem7173593 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term81 A v u f) = (term81 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7173592 A v u f x)). Qed.
Lemma lem7173594 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7173595 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term20 A v u f) = (term20 A v u f).
Proof. exact (MK_COMB (@lem7173594 A) (@lem7173593 A v u f)). Qed.
Lemma lem7173596 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7173597 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term42 A v u f) = (term42 A v u f).
Proof. exact (MK_COMB (@lem7173596) (@lem7173595 A v u f)). Qed.
Lemma lem7173598 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term44 A v u f) = (term44 A v u f).
Proof. exact (MK_COMB (@lem7173597 A v u f) (@lem7173587 A v u f)). Qed.
Lemma lem7173601 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term45 A u v) = (term45 A u v).
Proof. exact (eq_refl (term45 A u v)). Qed.
Lemma lem7173602 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term47 A v u f) = (term47 A v u f).
Proof. exact (MK_COMB (@lem7173601 A u v) (@lem7173598 A v u f)). Qed.
Lemma lem7173605 {A : Type'} (v : A -> Prop) : (term48 A v) = (term48 A v).
Proof. exact (eq_refl (term48 A v)). Qed.
Lemma lem7173606 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term49 A v u f) = (term49 A v u f).
Proof. exact (MK_COMB (@lem7173605 A v) (@lem7173602 A v u f)). Qed.
Lemma lem7173607 {A : Type'} (u : A -> Prop) (f : A -> real) : (term51 A u f) = (term51 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7173606 A v u f)). Qed.
Lemma lem7173608 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7173609 {A : Type'} (u : A -> Prop) (f : A -> real) : (term53 A u f) = (term53 A u f).
Proof. exact (MK_COMB (@lem7173608 A) (@lem7173607 A u f)). Qed.
Lemma lem7173610 {A : Type'} (f : A -> real) : (term55 A f) = (term55 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7173609 A u f)). Qed.
Lemma lem7173611 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7173612 {A : Type'} (f : A -> real) : (term57 A f) = (term57 A f).
Proof. exact (MK_COMB (@lem7173611 A) (@lem7173610 A f)). Qed.
Lemma lem7173613 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7173612 A f)). Qed.
Lemma lem7173614 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7173615 {A : Type'} : (term61 A) = (term61 A).
Proof. exact (MK_COMB (@lem7173614 A) (@lem7173613 A)). Qed.
Lemma lem7173734 {A : Type'} : (term60 A) = (term61 A).
Proof. exact (TRANS (@lem7173494 A) (@lem7173615 A)). Qed.
Lemma lem7173735 {A : Type'} : (term61 A) = (term60 A).
Proof. exact (SYM (@lem7173734 A)). Qed.
Lemma lem7173738 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term20 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173739 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term23 A v u f) : term23 A v u f.
Proof. exact (h1). Qed.
Lemma lem7173740 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem7173741 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem7173742 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem7173748 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7173754 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem7173761 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term80 A v u f x) = (term89 A v u f x).
Proof. exact (@lem17265 (term62 A x v u) (term90 A f x)). Qed.
Lemma lem7173762 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term81 A v u f) = (term91 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7173761 A v u f x)). Qed.
Lemma lem7173763 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7173816 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term20 A v u f) = (term92 A v u f).
Proof. exact (MK_COMB (@lem7173763 A) (@lem7173762 A v u f)). Qed.
Lemma lem7173817 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term92 A v u f.
Proof. exact (EQ_MP (@lem7173816 A v u f) (@lem7173738 A v u f h1)). Qed.
Lemma lem7173826 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term93 A u v f x) = (term94 A u v f x).
Proof. exact (@lem17362 (term62 A x u v) (term95 A f x)). Qed.
Lemma lem7173827 {A : Type'} (P : A -> Prop) : (term96 A P) = (term97 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7173828 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term98 A u v f) = (term99 A u v f).
Proof. exact (@lem7173827 A (term83 A u v f)). Qed.
Lemma lem7173829 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term100 A u v f x) = (term82 A u v f x).
Proof. exact (eq_refl (term100 A u v f x)). Qed.
Lemma lem7173830 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7173831 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term101 A u v f x) = (term93 A u v f x).
Proof. exact (MK_COMB (@lem7173830) (@lem7173829 A u v f x)). Qed.
Lemma lem7173832 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term101 A u v f x) = (term94 A u v f x).
Proof. exact (TRANS (@lem7173831 A u v f x) (@lem7173826 A u v f x)). Qed.
Lemma lem7173833 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term102 A u v f) = (term103 A u v f).
Proof. exact (fun_ext (fun x : A => @lem7173832 A u v f x)). Qed.
Lemma lem7173834 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7173835 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term99 A u v f) = (term104 A u v f).
Proof. exact (MK_COMB (@lem7173834 A) (@lem7173833 A u v f)). Qed.
Lemma lem7173836 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term98 A u v f) = (term104 A u v f).
Proof. exact (TRANS (@lem7173828 A u v f) (@lem7173835 A u v f)). Qed.
Lemma lem7173843 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term105 A v u f x) = (term106 A v u f x).
Proof. exact (@lem17362 (term62 A x v u) (term90 A f x)). Qed.
Lemma lem7173844 {A : Type'} (P : A -> Prop) : (term96 A P) = (term97 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7173845 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term107 A v u f) = (term108 A v u f).
Proof. exact (@lem7173844 A (term81 A v u f)). Qed.
Lemma lem7173846 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term109 A v u f x) = (term80 A v u f x).
Proof. exact (eq_refl (term109 A v u f x)). Qed.
Lemma lem7173847 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7173848 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term110 A v u f x) = (term105 A v u f x).
Proof. exact (MK_COMB (@lem7173847) (@lem7173846 A v u f x)). Qed.
Lemma lem7173849 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term110 A v u f x) = (term106 A v u f x).
Proof. exact (TRANS (@lem7173848 A v u f x) (@lem7173843 A v u f x)). Qed.
Lemma lem7173850 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term111 A v u f) = (term112 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7173849 A v u f x)). Qed.
Lemma lem7173851 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7173852 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term108 A v u f) = (term113 A v u f).
Proof. exact (MK_COMB (@lem7173851 A) (@lem7173850 A v u f)). Qed.
Lemma lem7173853 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term107 A v u f) = (term113 A v u f).
Proof. exact (TRANS (@lem7173845 A v u f) (@lem7173852 A v u f)). Qed.
Lemma lem7173854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7173855 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term114 A u v f) = (term115 A u v f).
Proof. exact (MK_COMB (@lem7173854) (@lem7173836 A u v f)). Qed.
Lemma lem7173856 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term116 A v u f) = (term117 A v u f).
Proof. exact (MK_COMB (@lem7173855 A u v f) (@lem7173853 A v u f)). Qed.
Lemma lem7173857 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term118 A v u f) = (term116 A v u f).
Proof. exact (@lem17045 (term84 A u v f) (term20 A v u f)). Qed.
Lemma lem7173858 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term118 A v u f) = (term117 A v u f).
Proof. exact (TRANS (@lem7173857 A v u f) (@lem7173856 A v u f)). Qed.
Lemma lem7173860 {A : Type'} (v : A -> Prop) : (term119 A v) = (term119 A v).
Proof. exact (eq_refl (term119 A v)). Qed.
Lemma lem7173861 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term120 A v u f) = (term121 A v u f).
Proof. exact (MK_COMB (@lem7173860 A v) (@lem7173858 A v u f)). Qed.
Lemma lem7173862 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term122 A v u f) = (term120 A v u f).
Proof. exact (@lem17045 (@FINITE A v) (term86 A v u f)). Qed.
Lemma lem7173863 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term122 A v u f) = (term121 A v u f).
Proof. exact (TRANS (@lem7173862 A v u f) (@lem7173861 A v u f)). Qed.
Lemma lem7173865 {A : Type'} (u : A -> Prop) : (term119 A u) = (term119 A u).
Proof. exact (eq_refl (term119 A u)). Qed.
Lemma lem7173866 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term123 A v u f) = (term124 A v u f).
Proof. exact (MK_COMB (@lem7173865 A u) (@lem7173863 A v u f)). Qed.
Lemma lem7173867 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term23 A v u f) = (term123 A v u f).
Proof. exact (@lem17045 (@FINITE A u) (term88 A v u f)). Qed.
Lemma lem7173868 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term23 A v u f) = (term124 A v u f).
Proof. exact (TRANS (@lem7173867 A v u f) (@lem7173866 A v u f)). Qed.
Lemma lem7173967 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7173968 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (@lem7173967 A P Q). Qed.
Lemma lem7173969 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term127 A v u f) = (term128 A v u f).
Proof. exact (@lem7173968 A (term103 A u v f) (term112 A v u f)). Qed.
Lemma lem7173970 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term129 A u v f x) = (term94 A u v f x).
Proof. exact (eq_refl (term129 A u v f x)). Qed.
Lemma lem7173971 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term130 A u v f) = (term103 A u v f).
Proof. exact (fun_ext (fun x : A => @lem7173970 A u v f x)). Qed.
Lemma lem7173972 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7173973 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term131 A u v f) = (term104 A u v f).
Proof. exact (MK_COMB (@lem7173972 A) (@lem7173971 A u v f)). Qed.
Lemma lem7173974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7173975 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term132 A u v f) = (term115 A u v f).
Proof. exact (MK_COMB (@lem7173974) (@lem7173973 A u v f)). Qed.
Lemma lem7173976 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term133 A v u f x) = (term106 A v u f x).
Proof. exact (eq_refl (term133 A v u f x)). Qed.
Lemma lem7173977 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term134 A v u f) = (term112 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7173976 A v u f x)). Qed.
Lemma lem7173978 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7173979 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term135 A v u f) = (term113 A v u f).
Proof. exact (MK_COMB (@lem7173978 A) (@lem7173977 A v u f)). Qed.
Lemma lem7173980 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term127 A v u f) = (term117 A v u f).
Proof. exact (MK_COMB (@lem7173975 A u v f) (@lem7173979 A v u f)). Qed.
Lemma lem7173981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7173982 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term136 A v u f) = (term137 A v u f).
Proof. exact (MK_COMB (@lem7173981) (@lem7173980 A v u f)). Qed.
Lemma lem7173983 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term129 A u v f x) = (term94 A u v f x).
Proof. exact (eq_refl (term129 A u v f x)). Qed.
Lemma lem7173984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7173985 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term138 A u v f x) = (term139 A u v f x).
Proof. exact (MK_COMB (@lem7173984) (@lem7173983 A u v f x)). Qed.
Lemma lem7173986 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term133 A v u f x) = (term106 A v u f x).
Proof. exact (eq_refl (term133 A v u f x)). Qed.
Lemma lem7173987 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term140 A v u f x) = (term141 A v u f x).
Proof. exact (MK_COMB (@lem7173985 A u v f x) (@lem7173986 A v u f x)). Qed.
Lemma lem7173988 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term142 A v u f) = (term143 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7173987 A v u f x)). Qed.
Lemma lem7173989 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7173990 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term128 A v u f) = (term144 A v u f).
Proof. exact (MK_COMB (@lem7173989 A) (@lem7173988 A v u f)). Qed.
Lemma lem7173991 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term127 A v u f) = (term128 A v u f)) = ((term117 A v u f) = (term144 A v u f)).
Proof. exact (MK_COMB (@lem7173982 A v u f) (@lem7173990 A v u f)). Qed.
Lemma lem7173992 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term117 A v u f) = (term144 A v u f).
Proof. exact (EQ_MP (@lem7173991 A v u f) (@lem7173969 A v u f)). Qed.
Lemma lem7173993 {A : Type'} (v : A -> Prop) : (term119 A v) = (term119 A v).
Proof. exact (eq_refl (term119 A v)). Qed.
Lemma lem7173994 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term121 A v u f) = (term145 A v u f).
Proof. exact (MK_COMB (@lem7173993 A v) (@lem7173992 A v u f)). Qed.
Lemma lem7173996 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7173997 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (@lem7173996 A P Q). Qed.
Lemma lem7173998 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term148 A v u f) = (term149 A v u f).
Proof. exact (@lem7173997 A (term150 A v) (term143 A v u f)). Qed.
Lemma lem7173999 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term151 A v u f x) = (term141 A v u f x).
Proof. exact (eq_refl (term151 A v u f x)). Qed.
Lemma lem7174000 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term152 A v u f) = (term143 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7173999 A v u f x)). Qed.
Lemma lem7174001 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7174002 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term153 A v u f) = (term144 A v u f).
Proof. exact (MK_COMB (@lem7174001 A) (@lem7174000 A v u f)). Qed.
Lemma lem7174003 {A : Type'} (v : A -> Prop) : (term119 A v) = (term119 A v).
Proof. exact (eq_refl (term119 A v)). Qed.
Lemma lem7174004 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term148 A v u f) = (term145 A v u f).
Proof. exact (MK_COMB (@lem7174003 A v) (@lem7174002 A v u f)). Qed.
Lemma lem7174005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174006 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term154 A v u f) = (term155 A v u f).
Proof. exact (MK_COMB (@lem7174005) (@lem7174004 A v u f)). Qed.
Lemma lem7174007 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term151 A v u f x) = (term141 A v u f x).
Proof. exact (eq_refl (term151 A v u f x)). Qed.
Lemma lem7174008 {A : Type'} (v : A -> Prop) : (term119 A v) = (term119 A v).
Proof. exact (eq_refl (term119 A v)). Qed.
Lemma lem7174009 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term156 A v u f x) = (term157 A v u f x).
Proof. exact (MK_COMB (@lem7174008 A v) (@lem7174007 A v u f x)). Qed.
Lemma lem7174010 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term158 A v u f) = (term159 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7174009 A v u f x)). Qed.
Lemma lem7174011 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7174012 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term149 A v u f) = (term160 A v u f).
Proof. exact (MK_COMB (@lem7174011 A) (@lem7174010 A v u f)). Qed.
Lemma lem7174013 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term148 A v u f) = (term149 A v u f)) = ((term145 A v u f) = (term160 A v u f)).
Proof. exact (MK_COMB (@lem7174006 A v u f) (@lem7174012 A v u f)). Qed.
Lemma lem7174014 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term145 A v u f) = (term160 A v u f).
Proof. exact (EQ_MP (@lem7174013 A v u f) (@lem7173998 A v u f)). Qed.
Lemma lem7174015 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term121 A v u f) = (term160 A v u f).
Proof. exact (TRANS (@lem7173994 A v u f) (@lem7174014 A v u f)). Qed.
Lemma lem7174016 {A : Type'} (u : A -> Prop) : (term119 A u) = (term119 A u).
Proof. exact (eq_refl (term119 A u)). Qed.
Lemma lem7174017 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term124 A v u f) = (term161 A v u f).
Proof. exact (MK_COMB (@lem7174016 A u) (@lem7174015 A v u f)). Qed.
Lemma lem7174019 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7174020 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (@lem7174019 A P Q). Qed.
Lemma lem7174021 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term162 A v u f) = (term163 A v u f).
Proof. exact (@lem7174020 A (term150 A u) (term159 A v u f)). Qed.
Lemma lem7174022 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term164 A v u f x) = (term157 A v u f x).
Proof. exact (eq_refl (term164 A v u f x)). Qed.
Lemma lem7174023 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term165 A v u f) = (term159 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7174022 A v u f x)). Qed.
Lemma lem7174024 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7174025 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term166 A v u f) = (term160 A v u f).
Proof. exact (MK_COMB (@lem7174024 A) (@lem7174023 A v u f)). Qed.
Lemma lem7174026 {A : Type'} (u : A -> Prop) : (term119 A u) = (term119 A u).
Proof. exact (eq_refl (term119 A u)). Qed.
Lemma lem7174027 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term162 A v u f) = (term161 A v u f).
Proof. exact (MK_COMB (@lem7174026 A u) (@lem7174025 A v u f)). Qed.
Lemma lem7174028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174029 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term167 A v u f) = (term168 A v u f).
Proof. exact (MK_COMB (@lem7174028) (@lem7174027 A v u f)). Qed.
Lemma lem7174030 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term164 A v u f x) = (term157 A v u f x).
Proof. exact (eq_refl (term164 A v u f x)). Qed.
Lemma lem7174031 {A : Type'} (u : A -> Prop) : (term119 A u) = (term119 A u).
Proof. exact (eq_refl (term119 A u)). Qed.
Lemma lem7174032 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term169 A v u f x) = (term170 A v u f x).
Proof. exact (MK_COMB (@lem7174031 A u) (@lem7174030 A v u f x)). Qed.
Lemma lem7174033 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term171 A v u f) = (term172 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7174032 A v u f x)). Qed.
Lemma lem7174034 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7174035 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term163 A v u f) = (term173 A v u f).
Proof. exact (MK_COMB (@lem7174034 A) (@lem7174033 A v u f)). Qed.
Lemma lem7174036 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term162 A v u f) = (term163 A v u f)) = ((term161 A v u f) = (term173 A v u f)).
Proof. exact (MK_COMB (@lem7174029 A v u f) (@lem7174035 A v u f)). Qed.
Lemma lem7174037 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term161 A v u f) = (term173 A v u f).
Proof. exact (EQ_MP (@lem7174036 A v u f) (@lem7174021 A v u f)). Qed.
Lemma lem7174039 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term124 A v u f) = (term173 A v u f).
Proof. exact (TRANS (@lem7174017 A v u f) (@lem7174037 A v u f)). Qed.
Lemma lem7174040 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term23 A v u f) = (term173 A v u f).
Proof. exact (TRANS (@lem7173868 A v u f) (@lem7174039 A v u f)). Qed.
Lemma lem7174041 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term23 A v u f) : term173 A v u f.
Proof. exact (EQ_MP (@lem7174040 A v u f) (@lem7173739 A v u f h1)). Qed.
Lemma lem7174048 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term174 A s t) = (term175 A s t).
Proof. exact (@lem17045 (@FINITE A t) (@SUBSET A s t)). Qed.
Lemma lem7174049 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7174050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7174051 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term176 A s t) = (term177 A s t).
Proof. exact (MK_COMB (@lem7174050) (@lem7174048 A s t)). Qed.
Lemma lem7174052 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term178 A t s) = (term179 A t s).
Proof. exact (MK_COMB (@lem7174051 A s t) (@lem7174049 A s)). Qed.
Lemma lem7174053 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term76 A t s) = (term178 A t s).
Proof. exact (@lem17265 (term180 A s t) (@FINITE A s)). Qed.
Lemma lem7174054 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term76 A t s) = (term179 A t s).
Proof. exact (TRANS (@lem7174053 A t s) (@lem7174052 A t s)). Qed.
Lemma lem7174055 {A : Type'} (s : A -> Prop) : (term77 A s) = (term181 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174054 A t s)). Qed.
Lemma lem7174056 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174057 {A : Type'} (s : A -> Prop) : (term78 A s) = (term182 A s).
Proof. exact (MK_COMB (@lem7174056 A) (@lem7174055 A s)). Qed.
Lemma lem7174058 {A : Type'} : (term79 A) = (term183 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174057 A s)). Qed.
Lemma lem7174059 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174060 {A : Type'} : (term26 A) = (term184 A).
Proof. exact (MK_COMB (@lem7174059 A) (@lem7174058 A)). Qed.
Lemma lem7174086 {A : Type'} (P : A -> Prop) (Q : Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem7174087 {A : Type'} (P : type686 A) (Q : Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (@lem7174086 (A -> Prop) P Q). Qed.
Lemma lem7174088 {A : Type'} (s : A -> Prop) : (term189 A s) = (term190 A s).
Proof. exact (@lem7174087 A (term191 A s) (@FINITE A s)). Qed.
Lemma lem7174089 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term192 A s t) = (term175 A s t).
Proof. exact (eq_refl (term192 A s t)). Qed.
Lemma lem7174090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7174091 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term193 A s t) = (term177 A s t).
Proof. exact (MK_COMB (@lem7174090) (@lem7174089 A s t)). Qed.
Lemma lem7174092 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7174093 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term194 A t s) = (term179 A t s).
Proof. exact (MK_COMB (@lem7174091 A s t) (@lem7174092 A s)). Qed.
Lemma lem7174094 {A : Type'} (s : A -> Prop) : (term195 A s) = (term181 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174093 A t s)). Qed.
Lemma lem7174095 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174096 {A : Type'} (s : A -> Prop) : (term189 A s) = (term182 A s).
Proof. exact (MK_COMB (@lem7174095 A) (@lem7174094 A s)). Qed.
Lemma lem7174097 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174098 {A : Type'} (s : A -> Prop) : (term196 A s) = (term197 A s).
Proof. exact (MK_COMB (@lem7174097) (@lem7174096 A s)). Qed.
Lemma lem7174099 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term192 A s t) = (term175 A s t).
Proof. exact (eq_refl (term192 A s t)). Qed.
Lemma lem7174100 {A : Type'} (s : A -> Prop) : (term198 A s) = (term191 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174099 A s t)). Qed.
Lemma lem7174101 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174102 {A : Type'} (s : A -> Prop) : (term199 A s) = (term200 A s).
Proof. exact (MK_COMB (@lem7174101 A) (@lem7174100 A s)). Qed.
Lemma lem7174103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7174104 {A : Type'} (s : A -> Prop) : (term201 A s) = (term202 A s).
Proof. exact (MK_COMB (@lem7174103) (@lem7174102 A s)). Qed.
Lemma lem7174105 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7174106 {A : Type'} (s : A -> Prop) : (term190 A s) = (term203 A s).
Proof. exact (MK_COMB (@lem7174104 A s) (@lem7174105 A s)). Qed.
Lemma lem7174107 {A : Type'} (s : A -> Prop) : ((term189 A s) = (term190 A s)) = ((term182 A s) = (term203 A s)).
Proof. exact (MK_COMB (@lem7174098 A s) (@lem7174106 A s)). Qed.
Lemma lem7174108 {A : Type'} (s : A -> Prop) : (term182 A s) = (term203 A s).
Proof. exact (EQ_MP (@lem7174107 A s) (@lem7174088 A s)). Qed.
Lemma lem7174157 {A : Type'} : (term183 A) = (term204 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174108 A s)). Qed.
Lemma lem7174158 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174193 {A : Type'} : (term184 A) = (term205 A).
Proof. exact (MK_COMB (@lem7174158 A) (@lem7174157 A)). Qed.
Lemma lem7174194 {A : Type'} : (term26 A) = (term205 A).
Proof. exact (TRANS (@lem7174060 A) (@lem7174193 A)). Qed.
Lemma lem7174195 {A : Type'} (h1 : term26 A) : term205 A.
Proof. exact (EQ_MP (@lem7174194 A) (@lem7173740 A h1)). Qed.
Lemma lem7174206 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term206 A s x t) = (term63 A s x t).
Proof. exact (@lem17362 (@IN A x s) (@IN A x t)). Qed.
Lemma lem7174211 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term69 A s x t) = (term207 A s x t).
Proof. exact (@lem17265 (@IN A x s) (@IN A x t)). Qed.
Lemma lem7174212 {A : Type'} (P : A -> Prop) : (term96 A P) = (term97 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7174213 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term208 A s t) = (term209 A s t).
Proof. exact (@lem7174212 A (term70 A s t)). Qed.
Lemma lem7174214 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term210 A s t x) = (term69 A s x t).
Proof. exact (eq_refl (term210 A s t x)). Qed.
Lemma lem7174215 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7174216 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term211 A s t x) = (term206 A s x t).
Proof. exact (MK_COMB (@lem7174215) (@lem7174214 A s x t)). Qed.
Lemma lem7174217 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term211 A s t x) = (term63 A s x t).
Proof. exact (TRANS (@lem7174216 A s x t) (@lem7174206 A s x t)). Qed.
Lemma lem7174218 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term212 A s t) = (term213 A s t).
Proof. exact (fun_ext (fun x : A => @lem7174217 A s x t)). Qed.
Lemma lem7174219 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7174220 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term209 A s t) = (term214 A s t).
Proof. exact (MK_COMB (@lem7174219 A) (@lem7174218 A s t)). Qed.
Lemma lem7174221 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term208 A s t) = (term214 A s t).
Proof. exact (TRANS (@lem7174213 A s t) (@lem7174220 A s t)). Qed.
Lemma lem7174222 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term70 A s t) = (term215 A s t).
Proof. exact (fun_ext (fun x : A => @lem7174211 A s x t)). Qed.
Lemma lem7174223 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7174224 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term71 A s t) = (term216 A s t).
Proof. exact (MK_COMB (@lem7174223 A) (@lem7174222 A s t)). Qed.
Lemma lem7174226 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term217 A s t) = (term217 A s t).
Proof. exact (eq_refl (term217 A s t)). Qed.
Lemma lem7174227 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term218 A s t) = (term219 A s t).
Proof. exact (MK_COMB (@lem7174226 A s t) (@lem7174224 A s t)). Qed.
Lemma lem7174229 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term220 A s t) = (term220 A s t).
Proof. exact (eq_refl (term220 A s t)). Qed.
Lemma lem7174230 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term221 A s t) = (term222 A s t).
Proof. exact (MK_COMB (@lem7174229 A s t) (@lem7174221 A s t)). Qed.
Lemma lem7174231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174232 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term223 A s t) = (term224 A s t).
Proof. exact (MK_COMB (@lem7174231) (@lem7174230 A s t)). Qed.
Lemma lem7174233 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term225 A s t) = (term226 A s t).
Proof. exact (MK_COMB (@lem7174232 A s t) (@lem7174227 A s t)). Qed.
Lemma lem7174234 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term71 A s t)) = (term225 A s t).
Proof. exact (@lem17784 (@SUBSET A s t) (term71 A s t)). Qed.
Lemma lem7174235 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term71 A s t)) = (term226 A s t).
Proof. exact (TRANS (@lem7174234 A s t) (@lem7174233 A s t)). Qed.
Lemma lem7174236 {A : Type'} (s : A -> Prop) : (term73 A s) = (term227 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174235 A s t)). Qed.
Lemma lem7174237 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174238 {A : Type'} (s : A -> Prop) : (term74 A s) = (term228 A s).
Proof. exact (MK_COMB (@lem7174237 A) (@lem7174236 A s)). Qed.
Lemma lem7174239 {A : Type'} : (term75 A) = (term229 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174238 A s)). Qed.
Lemma lem7174240 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174241 {A : Type'} : (term25 A) = (term230 A).
Proof. exact (MK_COMB (@lem7174240 A) (@lem7174239 A)). Qed.
Lemma lem7174247 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term231 A P Q) = (term232 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7174248 {A : Type'} (P : type686 A) (Q : type686 A) : (term233 A P Q) = (term234 A P Q).
Proof. exact (@lem7174247 (A -> Prop) P Q). Qed.
Lemma lem7174249 {A : Type'} (s : A -> Prop) : (term235 A s) = (term236 A s).
Proof. exact (@lem7174248 A (term237 A s) (term238 A s)). Qed.
Lemma lem7174250 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term239 A s t) = (term222 A s t).
Proof. exact (eq_refl (term239 A s t)). Qed.
Lemma lem7174251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174252 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term240 A s t) = (term224 A s t).
Proof. exact (MK_COMB (@lem7174251) (@lem7174250 A s t)). Qed.
Lemma lem7174253 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term241 A s t) = (term219 A s t).
Proof. exact (eq_refl (term241 A s t)). Qed.
Lemma lem7174254 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term242 A s t) = (term226 A s t).
Proof. exact (MK_COMB (@lem7174252 A s t) (@lem7174253 A s t)). Qed.
Lemma lem7174255 {A : Type'} (s : A -> Prop) : (term243 A s) = (term227 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174254 A s t)). Qed.
Lemma lem7174256 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174257 {A : Type'} (s : A -> Prop) : (term235 A s) = (term228 A s).
Proof. exact (MK_COMB (@lem7174256 A) (@lem7174255 A s)). Qed.
Lemma lem7174258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174259 {A : Type'} (s : A -> Prop) : (term244 A s) = (term245 A s).
Proof. exact (MK_COMB (@lem7174258) (@lem7174257 A s)). Qed.
Lemma lem7174260 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term239 A s t) = (term222 A s t).
Proof. exact (eq_refl (term239 A s t)). Qed.
Lemma lem7174261 {A : Type'} (s : A -> Prop) : (term246 A s) = (term237 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174260 A s t)). Qed.
Lemma lem7174262 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174263 {A : Type'} (s : A -> Prop) : (term247 A s) = (term248 A s).
Proof. exact (MK_COMB (@lem7174262 A) (@lem7174261 A s)). Qed.
Lemma lem7174264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174265 {A : Type'} (s : A -> Prop) : (term249 A s) = (term250 A s).
Proof. exact (MK_COMB (@lem7174264) (@lem7174263 A s)). Qed.
Lemma lem7174266 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term241 A s t) = (term219 A s t).
Proof. exact (eq_refl (term241 A s t)). Qed.
Lemma lem7174267 {A : Type'} (s : A -> Prop) : (term251 A s) = (term238 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174266 A s t)). Qed.
Lemma lem7174268 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174269 {A : Type'} (s : A -> Prop) : (term252 A s) = (term253 A s).
Proof. exact (MK_COMB (@lem7174268 A) (@lem7174267 A s)). Qed.
Lemma lem7174270 {A : Type'} (s : A -> Prop) : (term236 A s) = (term254 A s).
Proof. exact (MK_COMB (@lem7174265 A s) (@lem7174269 A s)). Qed.
Lemma lem7174271 {A : Type'} (s : A -> Prop) : ((term235 A s) = (term236 A s)) = ((term228 A s) = (term254 A s)).
Proof. exact (MK_COMB (@lem7174259 A s) (@lem7174270 A s)). Qed.
Lemma lem7174272 {A : Type'} (s : A -> Prop) : (term228 A s) = (term254 A s).
Proof. exact (EQ_MP (@lem7174271 A s) (@lem7174249 A s)). Qed.
Lemma lem7174465 {A : Type'} : (term229 A) = (term255 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174272 A s)). Qed.
Lemma lem7174466 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174467 {A : Type'} : (term230 A) = (term256 A).
Proof. exact (MK_COMB (@lem7174466 A) (@lem7174465 A)). Qed.
Lemma lem7174469 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term231 A P Q) = (term232 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7174470 {A : Type'} (P : type686 A) (Q : type686 A) : (term233 A P Q) = (term234 A P Q).
Proof. exact (@lem7174469 (A -> Prop) P Q). Qed.
Lemma lem7174471 {A : Type'} : (term257 A) = (term258 A).
Proof. exact (@lem7174470 A (term259 A) (term260 A)). Qed.
Lemma lem7174472 {A : Type'} (s : A -> Prop) : (term261 A s) = (term248 A s).
Proof. exact (eq_refl (term261 A s)). Qed.
Lemma lem7174473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174474 {A : Type'} (s : A -> Prop) : (term262 A s) = (term250 A s).
Proof. exact (MK_COMB (@lem7174473) (@lem7174472 A s)). Qed.
Lemma lem7174475 {A : Type'} (s : A -> Prop) : (term263 A s) = (term253 A s).
Proof. exact (eq_refl (term263 A s)). Qed.
Lemma lem7174476 {A : Type'} (s : A -> Prop) : (term264 A s) = (term254 A s).
Proof. exact (MK_COMB (@lem7174474 A s) (@lem7174475 A s)). Qed.
Lemma lem7174477 {A : Type'} : (term265 A) = (term255 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174476 A s)). Qed.
Lemma lem7174478 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174479 {A : Type'} : (term257 A) = (term256 A).
Proof. exact (MK_COMB (@lem7174478 A) (@lem7174477 A)). Qed.
Lemma lem7174480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174481 {A : Type'} : (term266 A) = (term267 A).
Proof. exact (MK_COMB (@lem7174480) (@lem7174479 A)). Qed.
Lemma lem7174482 {A : Type'} (s : A -> Prop) : (term261 A s) = (term248 A s).
Proof. exact (eq_refl (term261 A s)). Qed.
Lemma lem7174483 {A : Type'} : (term268 A) = (term259 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174482 A s)). Qed.
Lemma lem7174484 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174485 {A : Type'} : (term269 A) = (term270 A).
Proof. exact (MK_COMB (@lem7174484 A) (@lem7174483 A)). Qed.
Lemma lem7174486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174487 {A : Type'} : (term271 A) = (term272 A).
Proof. exact (MK_COMB (@lem7174486) (@lem7174485 A)). Qed.
Lemma lem7174488 {A : Type'} (s : A -> Prop) : (term263 A s) = (term253 A s).
Proof. exact (eq_refl (term263 A s)). Qed.
Lemma lem7174489 {A : Type'} : (term273 A) = (term260 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174488 A s)). Qed.
Lemma lem7174490 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174491 {A : Type'} : (term274 A) = (term275 A).
Proof. exact (MK_COMB (@lem7174490 A) (@lem7174489 A)). Qed.
Lemma lem7174492 {A : Type'} : (term258 A) = (term276 A).
Proof. exact (MK_COMB (@lem7174487 A) (@lem7174491 A)). Qed.
Lemma lem7174493 {A : Type'} : ((term257 A) = (term258 A)) = ((term256 A) = (term276 A)).
Proof. exact (MK_COMB (@lem7174481 A) (@lem7174492 A)). Qed.
Lemma lem7174494 {A : Type'} : (term256 A) = (term276 A).
Proof. exact (EQ_MP (@lem7174493 A) (@lem7174471 A)). Qed.
Lemma lem7174695 {A : Type'} : (term230 A) = (term276 A).
Proof. exact (TRANS (@lem7174467 A) (@lem7174494 A)). Qed.
Lemma lem7174697 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7174698 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (@lem7174697 A P Q). Qed.
Lemma lem7174699 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term277 A s t) = (term278 A s t).
Proof. exact (@lem7174698 A (@SUBSET A s t) (term213 A s t)). Qed.
Lemma lem7174700 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term279 A s t x) = (term63 A s x t).
Proof. exact (eq_refl (term279 A s t x)). Qed.
Lemma lem7174701 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term280 A s t) = (term213 A s t).
Proof. exact (fun_ext (fun x : A => @lem7174700 A s x t)). Qed.
Lemma lem7174702 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7174703 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term281 A s t) = (term214 A s t).
Proof. exact (MK_COMB (@lem7174702 A) (@lem7174701 A s t)). Qed.
Lemma lem7174704 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term220 A s t) = (term220 A s t).
Proof. exact (eq_refl (term220 A s t)). Qed.
Lemma lem7174705 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term277 A s t) = (term222 A s t).
Proof. exact (MK_COMB (@lem7174704 A s t) (@lem7174703 A s t)). Qed.
Lemma lem7174706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174707 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term282 A s t) = (term283 A s t).
Proof. exact (MK_COMB (@lem7174706) (@lem7174705 A s t)). Qed.
Lemma lem7174708 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term279 A s t x) = (term63 A s x t).
Proof. exact (eq_refl (term279 A s t x)). Qed.
Lemma lem7174709 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term220 A s t) = (term220 A s t).
Proof. exact (eq_refl (term220 A s t)). Qed.
Lemma lem7174710 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term284 A s t x) = (term285 A s x t).
Proof. exact (MK_COMB (@lem7174709 A s t) (@lem7174708 A s x t)). Qed.
Lemma lem7174711 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term286 A s t) = (term287 A s t).
Proof. exact (fun_ext (fun x : A => @lem7174710 A s x t)). Qed.
Lemma lem7174712 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7174713 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term278 A s t) = (term288 A s t).
Proof. exact (MK_COMB (@lem7174712 A) (@lem7174711 A s t)). Qed.
Lemma lem7174714 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term277 A s t) = (term278 A s t)) = ((term222 A s t) = (term288 A s t)).
Proof. exact (MK_COMB (@lem7174707 A s t) (@lem7174713 A s t)). Qed.
Lemma lem7174715 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term222 A s t) = (term288 A s t).
Proof. exact (EQ_MP (@lem7174714 A s t) (@lem7174699 A s t)). Qed.
Lemma lem7174716 {A : Type'} (s : A -> Prop) : (term237 A s) = (term289 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174715 A s t)). Qed.
Lemma lem7174717 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174718 {A : Type'} (s : A -> Prop) : (term248 A s) = (term290 A s).
Proof. exact (MK_COMB (@lem7174717 A) (@lem7174716 A s)). Qed.
Lemma lem7174720 {A B : Type'} (P : type1413 A B) : (term291 A B P) = (term292 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7174721 {A : Type'} (P : type672 A) : (term293 A P) = (term294 A P).
Proof. exact (@lem7174720 (A -> Prop) A P). Qed.
Lemma lem7174722 {A : Type'} (s : A -> Prop) : (term295 A s) = (term296 A s).
Proof. exact (@lem7174721 A (term297 A s)). Qed.
Lemma lem7174723 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term298 A s t) = (term287 A s t).
Proof. exact (eq_refl (term298 A s t)). Qed.
Lemma lem7174724 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7174725 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term299 A s t x) = (term300 A s t x).
Proof. exact (MK_COMB (@lem7174723 A s t) (@lem7174724 A x)). Qed.
Lemma lem7174726 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term300 A s t x) = (term285 A s x t).
Proof. exact (eq_refl (term300 A s t x)). Qed.
Lemma lem7174727 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term299 A s t x) = (term285 A s x t).
Proof. exact (TRANS (@lem7174725 A s t x) (@lem7174726 A s x t)). Qed.
Lemma lem7174728 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term301 A s t) = (term287 A s t).
Proof. exact (fun_ext (fun x : A => @lem7174727 A s x t)). Qed.
Lemma lem7174729 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7174730 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term302 A s t) = (term288 A s t).
Proof. exact (MK_COMB (@lem7174729 A) (@lem7174728 A s t)). Qed.
Lemma lem7174731 {A : Type'} (s : A -> Prop) : (term303 A s) = (term289 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174730 A s t)). Qed.
Lemma lem7174732 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174733 {A : Type'} (s : A -> Prop) : (term295 A s) = (term290 A s).
Proof. exact (MK_COMB (@lem7174732 A) (@lem7174731 A s)). Qed.
Lemma lem7174734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174735 {A : Type'} (s : A -> Prop) : (term304 A s) = (term305 A s).
Proof. exact (MK_COMB (@lem7174734) (@lem7174733 A s)). Qed.
Lemma lem7174736 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term298 A s t) = (term287 A s t).
Proof. exact (eq_refl (term298 A s t)). Qed.
Lemma lem7174737 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem7174738 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term306 A s x t) = (term307 A s x t).
Proof. exact (MK_COMB (@lem7174736 A s t) (@lem7174737 A x t)). Qed.
Lemma lem7174739 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term307 A s x t) = (term308 A s x t).
Proof. exact (eq_refl (term307 A s x t)). Qed.
Lemma lem7174740 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term306 A s x t) = (term308 A s x t).
Proof. exact (TRANS (@lem7174738 A s x t) (@lem7174739 A s x t)). Qed.
Lemma lem7174741 {A : Type'} (s : A -> Prop) (x : type684 A) : (term309 A s x) = (term310 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174740 A s x t)). Qed.
Lemma lem7174742 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174743 {A : Type'} (s : A -> Prop) (x : type684 A) : (term311 A s x) = (term312 A s x).
Proof. exact (MK_COMB (@lem7174742 A) (@lem7174741 A s x)). Qed.
Lemma lem7174744 {A : Type'} (s : A -> Prop) : (term313 A s) = (term314 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem7174743 A s x)). Qed.
Lemma lem7174745 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7174746 {A : Type'} (s : A -> Prop) : (term296 A s) = (term315 A s).
Proof. exact (MK_COMB (@lem7174745 A) (@lem7174744 A s)). Qed.
Lemma lem7174747 {A : Type'} (s : A -> Prop) : ((term295 A s) = (term296 A s)) = ((term290 A s) = (term315 A s)).
Proof. exact (MK_COMB (@lem7174735 A s) (@lem7174746 A s)). Qed.
Lemma lem7174748 {A : Type'} (s : A -> Prop) : (term290 A s) = (term315 A s).
Proof. exact (EQ_MP (@lem7174747 A s) (@lem7174722 A s)). Qed.
Lemma lem7174749 {A : Type'} (s : A -> Prop) : (term248 A s) = (term315 A s).
Proof. exact (TRANS (@lem7174718 A s) (@lem7174748 A s)). Qed.
Lemma lem7174750 {A : Type'} : (term259 A) = (term316 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174749 A s)). Qed.
Lemma lem7174751 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174752 {A : Type'} : (term270 A) = (term317 A).
Proof. exact (MK_COMB (@lem7174751 A) (@lem7174750 A)). Qed.
Lemma lem7174754 {A B : Type'} (P : type1413 A B) : (term291 A B P) = (term292 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7174755 {A : Type'} (P : type597 A) : (term318 A P) = (term319 A P).
Proof. exact (@lem7174754 (A -> Prop) (type684 A) P). Qed.
Lemma lem7174756 {A : Type'} : (term320 A) = (term321 A).
Proof. exact (@lem7174755 A (term322 A)). Qed.
Lemma lem7174757 {A : Type'} (s : A -> Prop) : (term323 A s) = (term314 A s).
Proof. exact (eq_refl (term323 A s)). Qed.
Lemma lem7174758 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7174759 {A : Type'} (s : A -> Prop) (x : type684 A) : (term324 A s x) = (term325 A s x).
Proof. exact (MK_COMB (@lem7174757 A s) (@lem7174758 A x)). Qed.
Lemma lem7174760 {A : Type'} (s : A -> Prop) (x : type684 A) : (term325 A s x) = (term312 A s x).
Proof. exact (eq_refl (term325 A s x)). Qed.
Lemma lem7174761 {A : Type'} (s : A -> Prop) (x : type684 A) : (term324 A s x) = (term312 A s x).
Proof. exact (TRANS (@lem7174759 A s x) (@lem7174760 A s x)). Qed.
Lemma lem7174762 {A : Type'} (s : A -> Prop) : (term326 A s) = (term314 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem7174761 A s x)). Qed.
Lemma lem7174763 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7174764 {A : Type'} (s : A -> Prop) : (term327 A s) = (term315 A s).
Proof. exact (MK_COMB (@lem7174763 A) (@lem7174762 A s)). Qed.
Lemma lem7174765 {A : Type'} : (term328 A) = (term316 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174764 A s)). Qed.
Lemma lem7174766 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174767 {A : Type'} : (term320 A) = (term317 A).
Proof. exact (MK_COMB (@lem7174766 A) (@lem7174765 A)). Qed.
Lemma lem7174768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174769 {A : Type'} : (term329 A) = (term330 A).
Proof. exact (MK_COMB (@lem7174768) (@lem7174767 A)). Qed.
Lemma lem7174770 {A : Type'} (s : A -> Prop) : (term323 A s) = (term314 A s).
Proof. exact (eq_refl (term323 A s)). Qed.
Lemma lem7174771 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7174772 {A : Type'} (x : type638 A) (s : A -> Prop) : (term331 A x s) = (term332 A x s).
Proof. exact (MK_COMB (@lem7174770 A s) (@lem7174771 A x s)). Qed.
Lemma lem7174773 {A : Type'} (x : type638 A) (s : A -> Prop) : (term332 A x s) = (term333 A x s).
Proof. exact (eq_refl (term332 A x s)). Qed.
Lemma lem7174774 {A : Type'} (x : type638 A) (s : A -> Prop) : (term331 A x s) = (term333 A x s).
Proof. exact (TRANS (@lem7174772 A x s) (@lem7174773 A x s)). Qed.
Lemma lem7174775 {A : Type'} (x : type638 A) : (term334 A x) = (term335 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174774 A x s)). Qed.
Lemma lem7174776 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174777 {A : Type'} (x : type638 A) : (term336 A x) = (term337 A x).
Proof. exact (MK_COMB (@lem7174776 A) (@lem7174775 A x)). Qed.
Lemma lem7174778 {A : Type'} : (term338 A) = (term339 A).
Proof. exact (fun_ext (fun x : type638 A => @lem7174777 A x)). Qed.
Lemma lem7174779 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7174780 {A : Type'} : (term321 A) = (term340 A).
Proof. exact (MK_COMB (@lem7174779 A) (@lem7174778 A)). Qed.
Lemma lem7174781 {A : Type'} : ((term320 A) = (term321 A)) = ((term317 A) = (term340 A)).
Proof. exact (MK_COMB (@lem7174769 A) (@lem7174780 A)). Qed.
Lemma lem7174782 {A : Type'} : (term317 A) = (term340 A).
Proof. exact (EQ_MP (@lem7174781 A) (@lem7174756 A)). Qed.
Lemma lem7174783 {A : Type'} : (term270 A) = (term340 A).
Proof. exact (TRANS (@lem7174752 A) (@lem7174782 A)). Qed.
Lemma lem7174784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174785 {A : Type'} : (term272 A) = (term341 A).
Proof. exact (MK_COMB (@lem7174784) (@lem7174783 A)). Qed.
Lemma lem7174786 {A : Type'} : (term275 A) = (term275 A).
Proof. exact (eq_refl (term275 A)). Qed.
Lemma lem7174787 {A : Type'} : (term276 A) = (term342 A).
Proof. exact (MK_COMB (@lem7174785 A) (@lem7174786 A)). Qed.
Lemma lem7174789 {A : Type'} (P : A -> Prop) (Q : Prop) : (term343 A P Q) = (term344 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7174790 {A : Type'} (P : type139 A) (Q : Prop) : (term345 A P Q) = (term346 A P Q).
Proof. exact (@lem7174789 (type638 A) P Q). Qed.
Lemma lem7174791 {A : Type'} : (term347 A) = (term348 A).
Proof. exact (@lem7174790 A (term339 A) (term275 A)). Qed.
Lemma lem7174792 {A : Type'} (x : type638 A) : (term349 A x) = (term337 A x).
Proof. exact (eq_refl (term349 A x)). Qed.
Lemma lem7174793 {A : Type'} : (term350 A) = (term339 A).
Proof. exact (fun_ext (fun x : type638 A => @lem7174792 A x)). Qed.
Lemma lem7174794 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7174795 {A : Type'} : (term351 A) = (term340 A).
Proof. exact (MK_COMB (@lem7174794 A) (@lem7174793 A)). Qed.
Lemma lem7174796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174797 {A : Type'} : (term352 A) = (term341 A).
Proof. exact (MK_COMB (@lem7174796) (@lem7174795 A)). Qed.
Lemma lem7174798 {A : Type'} : (term275 A) = (term275 A).
Proof. exact (eq_refl (term275 A)). Qed.
Lemma lem7174799 {A : Type'} : (term347 A) = (term342 A).
Proof. exact (MK_COMB (@lem7174797 A) (@lem7174798 A)). Qed.
Lemma lem7174800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174801 {A : Type'} : (term353 A) = (term354 A).
Proof. exact (MK_COMB (@lem7174800) (@lem7174799 A)). Qed.
Lemma lem7174802 {A : Type'} (x : type638 A) : (term349 A x) = (term337 A x).
Proof. exact (eq_refl (term349 A x)). Qed.
Lemma lem7174803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174804 {A : Type'} (x : type638 A) : (term355 A x) = (term356 A x).
Proof. exact (MK_COMB (@lem7174803) (@lem7174802 A x)). Qed.
Lemma lem7174805 {A : Type'} : (term275 A) = (term275 A).
Proof. exact (eq_refl (term275 A)). Qed.
Lemma lem7174806 {A : Type'} (x : type638 A) : (term357 A x) = (term358 A x).
Proof. exact (MK_COMB (@lem7174804 A x) (@lem7174805 A)). Qed.
Lemma lem7174807 {A : Type'} : (term359 A) = (term360 A).
Proof. exact (fun_ext (fun x : type638 A => @lem7174806 A x)). Qed.
Lemma lem7174808 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7174809 {A : Type'} : (term348 A) = (term361 A).
Proof. exact (MK_COMB (@lem7174808 A) (@lem7174807 A)). Qed.
Lemma lem7174810 {A : Type'} : ((term347 A) = (term348 A)) = ((term342 A) = (term361 A)).
Proof. exact (MK_COMB (@lem7174801 A) (@lem7174809 A)). Qed.
Lemma lem7174811 {A : Type'} : (term342 A) = (term361 A).
Proof. exact (EQ_MP (@lem7174810 A) (@lem7174791 A)). Qed.
Lemma lem7174812 {A : Type'} : (term276 A) = (term361 A).
Proof. exact (TRANS (@lem7174787 A) (@lem7174811 A)). Qed.
Lemma lem7174813 {A : Type'} : (term230 A) = (term361 A).
Proof. exact (TRANS (@lem7174695 A) (@lem7174812 A)). Qed.
Lemma lem7174814 {A : Type'} : (term25 A) = (term361 A).
Proof. exact (TRANS (@lem7174241 A) (@lem7174813 A)). Qed.
Lemma lem7174815 {A : Type'} (h1 : term25 A) : term361 A.
Proof. exact (EQ_MP (@lem7174814 A) (@lem7173741 A h1)). Qed.
Lemma lem7174823 {A : Type'} (x : A) (t : A -> Prop) : (term362 A x t) = (@IN A x t).
Proof. exact (@lem16933 (@IN A x t)). Qed.
Lemma lem7174825 {A : Type'} (x : A) (s : A -> Prop) : (term363 A x s) = (term363 A x s).
Proof. exact (eq_refl (term363 A x s)). Qed.
Lemma lem7174826 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term364 A s x t) = (term207 A s x t).
Proof. exact (MK_COMB (@lem7174825 A x s) (@lem7174823 A x t)). Qed.
Lemma lem7174827 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term365 A s x t) = (term364 A s x t).
Proof. exact (@lem17045 (@IN A x s) (term366 A x t)). Qed.
Lemma lem7174828 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term365 A s x t) = (term207 A s x t).
Proof. exact (TRANS (@lem7174827 A s x t) (@lem7174826 A s x t)). Qed.
Lemma lem7174834 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term367 A s x t) = (term367 A s x t).
Proof. exact (eq_refl (term367 A s x t)). Qed.
Lemma lem7174836 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term368 A x s t) = (term368 A x s t).
Proof. exact (eq_refl (term368 A x s t)). Qed.
Lemma lem7174837 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term369 A s x t) = (term370 A s x t).
Proof. exact (MK_COMB (@lem7174836 A x s t) (@lem7174828 A s x t)). Qed.
Lemma lem7174838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174839 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term371 A s x t) = (term372 A s x t).
Proof. exact (MK_COMB (@lem7174838) (@lem7174837 A s x t)). Qed.
Lemma lem7174840 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term373 A s x t) = (term374 A s x t).
Proof. exact (MK_COMB (@lem7174839 A s x t) (@lem7174834 A s x t)). Qed.
Lemma lem7174841 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term62 A x s t) = (term63 A s x t)) = (term373 A s x t).
Proof. exact (@lem17784 (term62 A x s t) (term63 A s x t)). Qed.
Lemma lem7174842 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term62 A x s t) = (term63 A s x t)) = (term374 A s x t).
Proof. exact (TRANS (@lem7174841 A s x t) (@lem7174840 A s x t)). Qed.
Lemma lem7174843 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term375 A s t).
Proof. exact (fun_ext (fun x : A => @lem7174842 A s x t)). Qed.
Lemma lem7174844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7174845 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term376 A s t).
Proof. exact (MK_COMB (@lem7174844 A) (@lem7174843 A s t)). Qed.
Lemma lem7174846 {A : Type'} (s : A -> Prop) : (term66 A s) = (term377 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174845 A s t)). Qed.
Lemma lem7174847 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174848 {A : Type'} (s : A -> Prop) : (term67 A s) = (term378 A s).
Proof. exact (MK_COMB (@lem7174847 A) (@lem7174846 A s)). Qed.
Lemma lem7174849 {A : Type'} : (term68 A) = (term379 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7174848 A s)). Qed.
Lemma lem7174850 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174851 {A : Type'} : (term24 A) = (term380 A).
Proof. exact (MK_COMB (@lem7174850 A) (@lem7174849 A)). Qed.
Lemma lem7174861 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term231 A P Q) = (term232 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7174862 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term231 A P Q) = (term232 A P Q).
Proof. exact (@lem7174861 A P Q). Qed.
Lemma lem7174863 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term381 A s t) = (term382 A s t).
Proof. exact (@lem7174862 A (term383 A s t) (term384 A s t)). Qed.
Lemma lem7174864 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term385 A s t x) = (term370 A s x t).
Proof. exact (eq_refl (term385 A s t x)). Qed.
Lemma lem7174865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174866 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term386 A s t x) = (term372 A s x t).
Proof. exact (MK_COMB (@lem7174865) (@lem7174864 A s x t)). Qed.
Lemma lem7174867 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term387 A s t x) = (term367 A s x t).
Proof. exact (eq_refl (term387 A s t x)). Qed.
Lemma lem7174868 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term388 A s t x) = (term374 A s x t).
Proof. exact (MK_COMB (@lem7174866 A s x t) (@lem7174867 A s x t)). Qed.
Lemma lem7174869 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term389 A s t) = (term375 A s t).
Proof. exact (fun_ext (fun x : A => @lem7174868 A s x t)). Qed.
Lemma lem7174870 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7174871 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term381 A s t) = (term376 A s t).
Proof. exact (MK_COMB (@lem7174870 A) (@lem7174869 A s t)). Qed.
Lemma lem7174872 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174873 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term390 A s t) = (term391 A s t).
Proof. exact (MK_COMB (@lem7174872) (@lem7174871 A s t)). Qed.
Lemma lem7174874 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term385 A s t x) = (term370 A s x t).
Proof. exact (eq_refl (term385 A s t x)). Qed.
Lemma lem7174875 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term392 A s t) = (term383 A s t).
Proof. exact (fun_ext (fun x : A => @lem7174874 A s x t)). Qed.
Lemma lem7174876 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7174877 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term393 A s t) = (term394 A s t).
Proof. exact (MK_COMB (@lem7174876 A) (@lem7174875 A s t)). Qed.
Lemma lem7174878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174879 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term395 A s t) = (term396 A s t).
Proof. exact (MK_COMB (@lem7174878) (@lem7174877 A s t)). Qed.
Lemma lem7174880 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term387 A s t x) = (term367 A s x t).
Proof. exact (eq_refl (term387 A s t x)). Qed.
Lemma lem7174881 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term397 A s t) = (term384 A s t).
Proof. exact (fun_ext (fun x : A => @lem7174880 A s x t)). Qed.
Lemma lem7174882 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7174883 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term398 A s t) = (term399 A s t).
Proof. exact (MK_COMB (@lem7174882 A) (@lem7174881 A s t)). Qed.
Lemma lem7174884 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term382 A s t) = (term400 A s t).
Proof. exact (MK_COMB (@lem7174879 A s t) (@lem7174883 A s t)). Qed.
Lemma lem7174885 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term381 A s t) = (term382 A s t)) = ((term376 A s t) = (term400 A s t)).
Proof. exact (MK_COMB (@lem7174873 A s t) (@lem7174884 A s t)). Qed.
Lemma lem7174886 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term376 A s t) = (term400 A s t).
Proof. exact (EQ_MP (@lem7174885 A s t) (@lem7174863 A s t)). Qed.
Lemma lem7174983 {A : Type'} (s : A -> Prop) : (term377 A s) = (term401 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174886 A s t)). Qed.
Lemma lem7174984 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174985 {A : Type'} (s : A -> Prop) : (term378 A s) = (term402 A s).
Proof. exact (MK_COMB (@lem7174984 A) (@lem7174983 A s)). Qed.
Lemma lem7174987 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term231 A P Q) = (term232 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7174988 {A : Type'} (P : type686 A) (Q : type686 A) : (term233 A P Q) = (term234 A P Q).
Proof. exact (@lem7174987 (A -> Prop) P Q). Qed.
Lemma lem7174989 {A : Type'} (s : A -> Prop) : (term403 A s) = (term404 A s).
Proof. exact (@lem7174988 A (term405 A s) (term406 A s)). Qed.
Lemma lem7174990 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term407 A s t) = (term394 A s t).
Proof. exact (eq_refl (term407 A s t)). Qed.
Lemma lem7174991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7174992 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term408 A s t) = (term396 A s t).
Proof. exact (MK_COMB (@lem7174991) (@lem7174990 A s t)). Qed.
Lemma lem7174993 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term409 A s t) = (term399 A s t).
Proof. exact (eq_refl (term409 A s t)). Qed.
Lemma lem7174994 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term410 A s t) = (term400 A s t).
Proof. exact (MK_COMB (@lem7174992 A s t) (@lem7174993 A s t)). Qed.
Lemma lem7174995 {A : Type'} (s : A -> Prop) : (term411 A s) = (term401 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7174994 A s t)). Qed.
Lemma lem7174996 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7174997 {A : Type'} (s : A -> Prop) : (term403 A s) = (term402 A s).
Proof. exact (MK_COMB (@lem7174996 A) (@lem7174995 A s)). Qed.
Lemma lem7174998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7174999 {A : Type'} (s : A -> Prop) : (term412 A s) = (term413 A s).
Proof. exact (MK_COMB (@lem7174998) (@lem7174997 A s)). Qed.
Lemma lem7175000 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term407 A s t) = (term394 A s t).
Proof. exact (eq_refl (term407 A s t)). Qed.
Lemma lem7175001 {A : Type'} (s : A -> Prop) : (term414 A s) = (term405 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7175000 A s t)). Qed.
Lemma lem7175002 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175003 {A : Type'} (s : A -> Prop) : (term415 A s) = (term416 A s).
Proof. exact (MK_COMB (@lem7175002 A) (@lem7175001 A s)). Qed.
Lemma lem7175004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7175005 {A : Type'} (s : A -> Prop) : (term417 A s) = (term418 A s).
Proof. exact (MK_COMB (@lem7175004) (@lem7175003 A s)). Qed.
Lemma lem7175006 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term409 A s t) = (term399 A s t).
Proof. exact (eq_refl (term409 A s t)). Qed.
Lemma lem7175007 {A : Type'} (s : A -> Prop) : (term419 A s) = (term406 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7175006 A s t)). Qed.
Lemma lem7175008 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175009 {A : Type'} (s : A -> Prop) : (term420 A s) = (term421 A s).
Proof. exact (MK_COMB (@lem7175008 A) (@lem7175007 A s)). Qed.
Lemma lem7175010 {A : Type'} (s : A -> Prop) : (term404 A s) = (term422 A s).
Proof. exact (MK_COMB (@lem7175005 A s) (@lem7175009 A s)). Qed.
Lemma lem7175011 {A : Type'} (s : A -> Prop) : ((term403 A s) = (term404 A s)) = ((term402 A s) = (term422 A s)).
Proof. exact (MK_COMB (@lem7174999 A s) (@lem7175010 A s)). Qed.
Lemma lem7175012 {A : Type'} (s : A -> Prop) : (term402 A s) = (term422 A s).
Proof. exact (EQ_MP (@lem7175011 A s) (@lem7174989 A s)). Qed.
Lemma lem7175117 {A : Type'} (s : A -> Prop) : (term378 A s) = (term422 A s).
Proof. exact (TRANS (@lem7174985 A s) (@lem7175012 A s)). Qed.
Lemma lem7175118 {A : Type'} : (term379 A) = (term423 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175117 A s)). Qed.
Lemma lem7175119 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175120 {A : Type'} : (term380 A) = (term424 A).
Proof. exact (MK_COMB (@lem7175119 A) (@lem7175118 A)). Qed.
Lemma lem7175122 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term231 A P Q) = (term232 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7175123 {A : Type'} (P : type686 A) (Q : type686 A) : (term233 A P Q) = (term234 A P Q).
Proof. exact (@lem7175122 (A -> Prop) P Q). Qed.
Lemma lem7175124 {A : Type'} : (term425 A) = (term426 A).
Proof. exact (@lem7175123 A (term427 A) (term428 A)). Qed.
Lemma lem7175125 {A : Type'} (s : A -> Prop) : (term429 A s) = (term416 A s).
Proof. exact (eq_refl (term429 A s)). Qed.
Lemma lem7175126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7175127 {A : Type'} (s : A -> Prop) : (term430 A s) = (term418 A s).
Proof. exact (MK_COMB (@lem7175126) (@lem7175125 A s)). Qed.
Lemma lem7175128 {A : Type'} (s : A -> Prop) : (term431 A s) = (term421 A s).
Proof. exact (eq_refl (term431 A s)). Qed.
Lemma lem7175129 {A : Type'} (s : A -> Prop) : (term432 A s) = (term422 A s).
Proof. exact (MK_COMB (@lem7175127 A s) (@lem7175128 A s)). Qed.
Lemma lem7175130 {A : Type'} : (term433 A) = (term423 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175129 A s)). Qed.
Lemma lem7175131 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175132 {A : Type'} : (term425 A) = (term424 A).
Proof. exact (MK_COMB (@lem7175131 A) (@lem7175130 A)). Qed.
Lemma lem7175133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7175134 {A : Type'} : (term434 A) = (term435 A).
Proof. exact (MK_COMB (@lem7175133) (@lem7175132 A)). Qed.
Lemma lem7175135 {A : Type'} (s : A -> Prop) : (term429 A s) = (term416 A s).
Proof. exact (eq_refl (term429 A s)). Qed.
Lemma lem7175136 {A : Type'} : (term436 A) = (term427 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175135 A s)). Qed.
Lemma lem7175137 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175138 {A : Type'} : (term437 A) = (term438 A).
Proof. exact (MK_COMB (@lem7175137 A) (@lem7175136 A)). Qed.
Lemma lem7175139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7175140 {A : Type'} : (term439 A) = (term440 A).
Proof. exact (MK_COMB (@lem7175139) (@lem7175138 A)). Qed.
Lemma lem7175141 {A : Type'} (s : A -> Prop) : (term431 A s) = (term421 A s).
Proof. exact (eq_refl (term431 A s)). Qed.
Lemma lem7175142 {A : Type'} : (term441 A) = (term428 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175141 A s)). Qed.
Lemma lem7175143 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175144 {A : Type'} : (term442 A) = (term443 A).
Proof. exact (MK_COMB (@lem7175143 A) (@lem7175142 A)). Qed.
Lemma lem7175145 {A : Type'} : (term426 A) = (term444 A).
Proof. exact (MK_COMB (@lem7175140 A) (@lem7175144 A)). Qed.
Lemma lem7175146 {A : Type'} : ((term425 A) = (term426 A)) = ((term424 A) = (term444 A)).
Proof. exact (MK_COMB (@lem7175134 A) (@lem7175145 A)). Qed.
Lemma lem7175147 {A : Type'} : (term424 A) = (term444 A).
Proof. exact (EQ_MP (@lem7175146 A) (@lem7175124 A)). Qed.
Lemma lem7175262 {A : Type'} : (term380 A) = (term444 A).
Proof. exact (TRANS (@lem7175120 A) (@lem7175147 A)). Qed.
Lemma lem7175263 {A : Type'} : (term24 A) = (term444 A).
Proof. exact (TRANS (@lem7174851 A) (@lem7175262 A)). Qed.
Lemma lem7175264 {A : Type'} (h1 : term24 A) : term444 A.
Proof. exact (EQ_MP (@lem7175263 A) (@lem7173742 A h1)). Qed.
Lemma lem7175265 {A : Type'} (x : type638 A) (h1 : term358 A x) : term358 A x.
Proof. exact (h1). Qed.
Lemma lem7175270 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7175276 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem7175301 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term89 A v u f x) = (term89 A v u f x).
Proof. exact (eq_refl (term89 A v u f x)). Qed.
Lemma lem7175302 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term91 A v u f) = (term91 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7175301 A v u f x)). Qed.
Lemma lem7175303 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7175304 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term92 A v u f) = (term92 A v u f).
Proof. exact (MK_COMB (@lem7175303 A) (@lem7175302 A v u f)). Qed.
Lemma lem7175305 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term92 A v u f.
Proof. exact (EQ_MP (@lem7175304 A v u f) (@lem7173817 A v u f h1)). Qed.
Lemma lem7175308 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7175323 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term175 A s t) = (term175 A s t).
Proof. exact (eq_refl (term175 A s t)). Qed.
Lemma lem7175324 {A : Type'} (s : A -> Prop) : (term191 A s) = (term191 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7175323 A s t)). Qed.
Lemma lem7175325 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175326 {A : Type'} (s : A -> Prop) : (term200 A s) = (term200 A s).
Proof. exact (MK_COMB (@lem7175325 A) (@lem7175324 A s)). Qed.
Lemma lem7175327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7175328 {A : Type'} (s : A -> Prop) : (term202 A s) = (term202 A s).
Proof. exact (MK_COMB (@lem7175327) (@lem7175326 A s)). Qed.
Lemma lem7175329 {A : Type'} (s : A -> Prop) : (term203 A s) = (term203 A s).
Proof. exact (MK_COMB (@lem7175328 A s) (@lem7175308 A s)). Qed.
Lemma lem7175330 {A : Type'} : (term204 A) = (term204 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175329 A s)). Qed.
Lemma lem7175331 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175332 {A : Type'} : (term205 A) = (term205 A).
Proof. exact (MK_COMB (@lem7175331 A) (@lem7175330 A)). Qed.
Lemma lem7175333 {A : Type'} (h1 : term26 A) : term205 A.
Proof. exact (EQ_MP (@lem7175332 A) (@lem7174195 A h1)). Qed.
Lemma lem7175362 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term367 A s x t) = (term367 A s x t).
Proof. exact (eq_refl (term367 A s x t)). Qed.
Lemma lem7175363 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term384 A s t) = (term384 A s t).
Proof. exact (fun_ext (fun x : A => @lem7175362 A s x t)). Qed.
Lemma lem7175364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7175365 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term399 A s t) = (term399 A s t).
Proof. exact (MK_COMB (@lem7175364 A) (@lem7175363 A s t)). Qed.
Lemma lem7175366 {A : Type'} (s : A -> Prop) : (term406 A s) = (term406 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7175365 A s t)). Qed.
Lemma lem7175367 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175368 {A : Type'} (s : A -> Prop) : (term421 A s) = (term421 A s).
Proof. exact (MK_COMB (@lem7175367 A) (@lem7175366 A s)). Qed.
Lemma lem7175369 {A : Type'} : (term428 A) = (term428 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175368 A s)). Qed.
Lemma lem7175370 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175371 {A : Type'} : (term443 A) = (term443 A).
Proof. exact (MK_COMB (@lem7175370 A) (@lem7175369 A)). Qed.
Lemma lem7175398 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term370 A s x t) = (term370 A s x t).
Proof. exact (eq_refl (term370 A s x t)). Qed.
Lemma lem7175399 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term383 A s t) = (term383 A s t).
Proof. exact (fun_ext (fun x : A => @lem7175398 A s x t)). Qed.
Lemma lem7175400 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7175401 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term394 A s t) = (term394 A s t).
Proof. exact (MK_COMB (@lem7175400 A) (@lem7175399 A s t)). Qed.
Lemma lem7175402 {A : Type'} (s : A -> Prop) : (term405 A s) = (term405 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7175401 A s t)). Qed.
Lemma lem7175403 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175404 {A : Type'} (s : A -> Prop) : (term416 A s) = (term416 A s).
Proof. exact (MK_COMB (@lem7175403 A) (@lem7175402 A s)). Qed.
Lemma lem7175405 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175404 A s)). Qed.
Lemma lem7175406 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175407 {A : Type'} : (term438 A) = (term438 A).
Proof. exact (MK_COMB (@lem7175406 A) (@lem7175405 A)). Qed.
Lemma lem7175408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7175409 {A : Type'} : (term440 A) = (term440 A).
Proof. exact (MK_COMB (@lem7175408) (@lem7175407 A)). Qed.
Lemma lem7175410 {A : Type'} : (term444 A) = (term444 A).
Proof. exact (MK_COMB (@lem7175409 A) (@lem7175371 A)). Qed.
Lemma lem7175411 {A : Type'} (h1 : term24 A) : term444 A.
Proof. exact (EQ_MP (@lem7175410 A) (@lem7175264 A h1)). Qed.
Lemma lem7175426 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term207 A s x t) = (term207 A s x t).
Proof. exact (eq_refl (term207 A s x t)). Qed.
Lemma lem7175427 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term215 A s t) = (term215 A s t).
Proof. exact (fun_ext (fun x : A => @lem7175426 A s x t)). Qed.
Lemma lem7175428 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7175429 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term216 A s t) = (term216 A s t).
Proof. exact (MK_COMB (@lem7175428 A) (@lem7175427 A s t)). Qed.
Lemma lem7175438 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term217 A s t) = (term217 A s t).
Proof. exact (eq_refl (term217 A s t)). Qed.
Lemma lem7175439 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term219 A s t) = (term219 A s t).
Proof. exact (MK_COMB (@lem7175438 A s t) (@lem7175429 A s t)). Qed.
Lemma lem7175440 {A : Type'} (s : A -> Prop) : (term238 A s) = (term238 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7175439 A s t)). Qed.
Lemma lem7175441 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175442 {A : Type'} (s : A -> Prop) : (term253 A s) = (term253 A s).
Proof. exact (MK_COMB (@lem7175441 A) (@lem7175440 A s)). Qed.
Lemma lem7175443 {A : Type'} : (term260 A) = (term260 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175442 A s)). Qed.
Lemma lem7175444 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175445 {A : Type'} : (term275 A) = (term275 A).
Proof. exact (MK_COMB (@lem7175444 A) (@lem7175443 A)). Qed.
Lemma lem7175476 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term445 A x s t) = (term445 A x s t).
Proof. exact (eq_refl (term445 A x s t)). Qed.
Lemma lem7175477 {A : Type'} (x : type638 A) (s : A -> Prop) : (term446 A x s) = (term446 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7175476 A x s t)). Qed.
Lemma lem7175478 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175479 {A : Type'} (x : type638 A) (s : A -> Prop) : (term333 A x s) = (term333 A x s).
Proof. exact (MK_COMB (@lem7175478 A) (@lem7175477 A x s)). Qed.
Lemma lem7175480 {A : Type'} (x : type638 A) : (term335 A x) = (term335 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175479 A x s)). Qed.
Lemma lem7175481 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175482 {A : Type'} (x : type638 A) : (term337 A x) = (term337 A x).
Proof. exact (MK_COMB (@lem7175481 A) (@lem7175480 A x)). Qed.
Lemma lem7175483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7175484 {A : Type'} (x : type638 A) : (term356 A x) = (term356 A x).
Proof. exact (MK_COMB (@lem7175483) (@lem7175482 A x)). Qed.
Lemma lem7175485 {A : Type'} (x : type638 A) : (term358 A x) = (term358 A x).
Proof. exact (MK_COMB (@lem7175484 A x) (@lem7175445 A)). Qed.
Lemma lem7175486 {A : Type'} (x : type638 A) (h1 : term358 A x) : term358 A x.
Proof. exact (EQ_MP (@lem7175485 A x) (@lem7175265 A x h1)). Qed.
Lemma lem7175556 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term170 A v u f x') : term170 A v u f x'.
Proof. exact (h1). Qed.
Lemma lem7175557 {A : Type'} (x : type638 A) (h1 : term358 A x) : term275 A.
Proof. exact (proj2 (@lem7175486 A x h1)). Qed.
Lemma lem7175559 {A : Type'} (h1 : term24 A) : term443 A.
Proof. exact (proj2 (@lem7175411 A h1)). Qed.
Lemma lem7175562 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term157 A v u f x') : term157 A v u f x'.
Proof. exact (h1). Qed.
Lemma lem7175564 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term141 A v u f x') : term141 A v u f x'.
Proof. exact (h1). Qed.
Lemma lem7175565 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x' : A) (h1 : term94 A u v f x') : term94 A u v f x'.
Proof. exact (h1). Qed.
Lemma lem7175566 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term106 A v u f x') : term106 A v u f x'.
Proof. exact (h1). Qed.
Lemma lem7175574 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7175578 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem7175593 {A : Type'} (P : A -> Prop) (Q : Prop) : (term186 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem7175594 {A : Type'} (P : type686 A) (Q : Prop) : (term188 A P Q) = (term187 A P Q).
Proof. exact (@lem7175593 (A -> Prop) P Q). Qed.
Lemma lem7175595 {A : Type'} (s : A -> Prop) : (term190 A s) = (term189 A s).
Proof. exact (@lem7175594 A (term191 A s) (@FINITE A s)). Qed.
Lemma lem7175596 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term192 A s t) = (term175 A s t).
Proof. exact (eq_refl (term192 A s t)). Qed.
Lemma lem7175597 {A : Type'} (s : A -> Prop) : (term198 A s) = (term191 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7175596 A s t)). Qed.
Lemma lem7175598 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175599 {A : Type'} (s : A -> Prop) : (term199 A s) = (term200 A s).
Proof. exact (MK_COMB (@lem7175598 A) (@lem7175597 A s)). Qed.
Lemma lem7175600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7175601 {A : Type'} (s : A -> Prop) : (term201 A s) = (term202 A s).
Proof. exact (MK_COMB (@lem7175600) (@lem7175599 A s)). Qed.
Lemma lem7175602 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7175603 {A : Type'} (s : A -> Prop) : (term190 A s) = (term203 A s).
Proof. exact (MK_COMB (@lem7175601 A s) (@lem7175602 A s)). Qed.
Lemma lem7175604 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7175605 {A : Type'} (s : A -> Prop) : (term447 A s) = (term448 A s).
Proof. exact (MK_COMB (@lem7175604) (@lem7175603 A s)). Qed.
Lemma lem7175606 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term192 A s t) = (term175 A s t).
Proof. exact (eq_refl (term192 A s t)). Qed.
Lemma lem7175607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7175608 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term193 A s t) = (term177 A s t).
Proof. exact (MK_COMB (@lem7175607) (@lem7175606 A s t)). Qed.
Lemma lem7175609 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7175610 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term194 A t s) = (term179 A t s).
Proof. exact (MK_COMB (@lem7175608 A s t) (@lem7175609 A s)). Qed.
Lemma lem7175611 {A : Type'} (s : A -> Prop) : (term195 A s) = (term181 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7175610 A t s)). Qed.
Lemma lem7175612 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175613 {A : Type'} (s : A -> Prop) : (term189 A s) = (term182 A s).
Proof. exact (MK_COMB (@lem7175612 A) (@lem7175611 A s)). Qed.
Lemma lem7175614 {A : Type'} (s : A -> Prop) : ((term190 A s) = (term189 A s)) = ((term203 A s) = (term182 A s)).
Proof. exact (MK_COMB (@lem7175605 A s) (@lem7175613 A s)). Qed.
Lemma lem7175615 {A : Type'} (s : A -> Prop) : (term203 A s) = (term182 A s).
Proof. exact (EQ_MP (@lem7175614 A s) (@lem7175595 A s)). Qed.
Lemma lem7175616 {A : Type'} : (term204 A) = (term183 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175615 A s)). Qed.
Lemma lem7175617 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175618 {A : Type'} : (term205 A) = (term184 A).
Proof. exact (MK_COMB (@lem7175617 A) (@lem7175616 A)). Qed.
Lemma lem7175631 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term179 A t s) = (term179 A t s).
Proof. exact (eq_refl (term179 A t s)). Qed.
Lemma lem7175632 {A : Type'} (s : A -> Prop) : (term181 A s) = (term181 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7175631 A t s)). Qed.
Lemma lem7175633 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175634 {A : Type'} (s : A -> Prop) : (term182 A s) = (term182 A s).
Proof. exact (MK_COMB (@lem7175633 A) (@lem7175632 A s)). Qed.
Lemma lem7175635 {A : Type'} : (term183 A) = (term183 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7175634 A s)). Qed.
Lemma lem7175636 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7175637 {A : Type'} : (term184 A) = (term184 A).
Proof. exact (MK_COMB (@lem7175636 A) (@lem7175635 A)). Qed.
Lemma lem7175638 {A : Type'} : (term205 A) = (term184 A).
Proof. exact (TRANS (@lem7175618 A) (@lem7175637 A)). Qed.
Lemma lem7175639 {A : Type'} (h1 : term26 A) : term184 A.
Proof. exact (EQ_MP (@lem7175638 A) (@lem7175333 A h1)). Qed.
Lemma lem7175773 {A : Type'} (u : A -> Prop) (h1 : term150 A u) : term150 A u.
Proof. exact (h1). Qed.
Lemma lem7175777 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7175976 {A : Type'} (v : A -> Prop) (h1 : term150 A v) : term150 A v.
Proof. exact (h1). Qed.
Lemma lem7175984 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem7176073 {A : Type'} (P : Prop) (Q : A -> Prop) : (term449 A P Q) = (term450 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7176074 {A : Type'} (P : Prop) (Q : A -> Prop) : (term449 A P Q) = (term450 A P Q).
Proof. exact (@lem7176073 A P Q). Qed.
Lemma lem7176075 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term451 A s t) = (term452 A s t).
Proof. exact (@lem7176074 A (term453 A s t) (term215 A s t)). Qed.
Lemma lem7176076 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term454 A s t x) = (term207 A s x t).
Proof. exact (eq_refl (term454 A s t x)). Qed.
Lemma lem7176077 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term455 A s t) = (term215 A s t).
Proof. exact (fun_ext (fun x : A => @lem7176076 A s x t)). Qed.
Lemma lem7176078 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7176079 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term456 A s t) = (term216 A s t).
Proof. exact (MK_COMB (@lem7176078 A) (@lem7176077 A s t)). Qed.
Lemma lem7176080 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term217 A s t) = (term217 A s t).
Proof. exact (eq_refl (term217 A s t)). Qed.
Lemma lem7176081 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term451 A s t) = (term219 A s t).
Proof. exact (MK_COMB (@lem7176080 A s t) (@lem7176079 A s t)). Qed.
Lemma lem7176082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7176083 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term457 A s t) = (term458 A s t).
Proof. exact (MK_COMB (@lem7176082) (@lem7176081 A s t)). Qed.
Lemma lem7176084 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term454 A s t x) = (term207 A s x t).
Proof. exact (eq_refl (term454 A s t x)). Qed.
Lemma lem7176085 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term217 A s t) = (term217 A s t).
Proof. exact (eq_refl (term217 A s t)). Qed.
Lemma lem7176086 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term459 A s t x) = (term460 A s x t).
Proof. exact (MK_COMB (@lem7176085 A s t) (@lem7176084 A s x t)). Qed.
Lemma lem7176087 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term461 A s t) = (term462 A s t).
Proof. exact (fun_ext (fun x : A => @lem7176086 A s x t)). Qed.
Lemma lem7176088 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7176089 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term452 A s t) = (term463 A s t).
Proof. exact (MK_COMB (@lem7176088 A) (@lem7176087 A s t)). Qed.
Lemma lem7176090 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term451 A s t) = (term452 A s t)) = ((term219 A s t) = (term463 A s t)).
Proof. exact (MK_COMB (@lem7176083 A s t) (@lem7176089 A s t)). Qed.
Lemma lem7176091 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term219 A s t) = (term463 A s t).
Proof. exact (EQ_MP (@lem7176090 A s t) (@lem7176075 A s t)). Qed.
Lemma lem7176092 {A : Type'} (s : A -> Prop) : (term238 A s) = (term464 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7176091 A s t)). Qed.
Lemma lem7176093 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7176094 {A : Type'} (s : A -> Prop) : (term253 A s) = (term465 A s).
Proof. exact (MK_COMB (@lem7176093 A) (@lem7176092 A s)). Qed.
Lemma lem7176095 {A : Type'} : (term260 A) = (term466 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7176094 A s)). Qed.
Lemma lem7176096 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7176097 {A : Type'} : (term275 A) = (term467 A).
Proof. exact (MK_COMB (@lem7176096 A) (@lem7176095 A)). Qed.
Lemma lem7176110 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term460 A s x t) = (term460 A s x t).
Proof. exact (eq_refl (term460 A s x t)). Qed.
Lemma lem7176111 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term462 A s t) = (term462 A s t).
Proof. exact (fun_ext (fun x : A => @lem7176110 A s x t)). Qed.
Lemma lem7176112 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7176113 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term463 A s t) = (term463 A s t).
Proof. exact (MK_COMB (@lem7176112 A) (@lem7176111 A s t)). Qed.
Lemma lem7176114 {A : Type'} (s : A -> Prop) : (term464 A s) = (term464 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7176113 A s t)). Qed.
Lemma lem7176115 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7176116 {A : Type'} (s : A -> Prop) : (term465 A s) = (term465 A s).
Proof. exact (MK_COMB (@lem7176115 A) (@lem7176114 A s)). Qed.
Lemma lem7176117 {A : Type'} : (term466 A) = (term466 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7176116 A s)). Qed.
Lemma lem7176118 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7176119 {A : Type'} : (term467 A) = (term467 A).
Proof. exact (MK_COMB (@lem7176118 A) (@lem7176117 A)). Qed.
Lemma lem7176120 {A : Type'} : (term275 A) = (term467 A).
Proof. exact (TRANS (@lem7176097 A) (@lem7176119 A)). Qed.
Lemma lem7176121 {A : Type'} (x : type638 A) (h1 : term358 A x) : term467 A.
Proof. exact (EQ_MP (@lem7176120 A) (@lem7175557 A x h1)). Qed.
Lemma lem7176164 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term367 A s x t) = (term468 A s x t).
Proof. exact (@lem19490 (@IN A x s) (term469 A x s t) (term366 A x t)). Qed.
Lemma lem7176165 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term384 A s t) = (term470 A s t).
Proof. exact (fun_ext (fun x : A => @lem7176164 A s x t)). Qed.
Lemma lem7176166 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7176167 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term399 A s t) = (term471 A s t).
Proof. exact (MK_COMB (@lem7176166 A) (@lem7176165 A s t)). Qed.
Lemma lem7176168 {A : Type'} (s : A -> Prop) : (term406 A s) = (term472 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7176167 A s t)). Qed.
Lemma lem7176169 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7176170 {A : Type'} (s : A -> Prop) : (term421 A s) = (term473 A s).
Proof. exact (MK_COMB (@lem7176169 A) (@lem7176168 A s)). Qed.
Lemma lem7176171 {A : Type'} : (term428 A) = (term474 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7176170 A s)). Qed.
Lemma lem7176172 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7176174 {A : Type'} : (term443 A) = (term475 A).
Proof. exact (MK_COMB (@lem7176172 A) (@lem7176171 A)). Qed.
Lemma lem7176175 {A : Type'} (h1 : term24 A) : term475 A.
Proof. exact (EQ_MP (@lem7176174 A) (@lem7175559 A h1)). Qed.
Lemma lem7176199 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term89 A v u f x) = (term89 A v u f x).
Proof. exact (eq_refl (term89 A v u f x)). Qed.
Lemma lem7176200 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term91 A v u f) = (term91 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7176199 A v u f x)). Qed.
Lemma lem7176201 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7176203 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term92 A v u f) = (term92 A v u f).
Proof. exact (MK_COMB (@lem7176201 A) (@lem7176200 A v u f)). Qed.
Lemma lem7176204 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term92 A v u f.
Proof. exact (EQ_MP (@lem7176203 A v u f) (@lem7175305 A v u f h1)). Qed.
Lemma lem7176394 {A : Type'} (_96099 : A -> Prop) (h1 : term26 A) : term476 A _96099.
Proof. exact (@lem7175639 A h1 _96099). Qed.
Lemma lem7176395 {A : Type'} (_96099 : A -> Prop) : (term476 A _96099) = (term182 A _96099).
Proof. exact (eq_refl (term476 A _96099)). Qed.
Lemma lem7176396 {A : Type'} (_96099 : A -> Prop) (h1 : term26 A) : term182 A _96099.
Proof. exact (EQ_MP (@lem7176395 A _96099) (@lem7176394 A _96099 h1)). Qed.
Lemma lem7176397 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) (h1 : term26 A) : term477 A _96099 _96100.
Proof. exact (@lem7176396 A _96099 h1 _96100). Qed.
Lemma lem7176398 {A : Type'} (_96100 : A -> Prop) (_96099 : A -> Prop) : (term477 A _96099 _96100) = (term179 A _96100 _96099).
Proof. exact (eq_refl (term477 A _96099 _96100)). Qed.
Lemma lem7176399 {A : Type'} (_96100 : A -> Prop) (_96099 : A -> Prop) (h1 : term26 A) : term179 A _96100 _96099.
Proof. exact (EQ_MP (@lem7176398 A _96100 _96099) (@lem7176397 A _96099 _96100 h1)). Qed.
Lemma lem7176490 {A : Type'} (_96131 : A -> Prop) (x : type638 A) (h1 : term358 A x) : term478 A _96131.
Proof. exact (@lem7176121 A x h1 _96131). Qed.
Lemma lem7176491 {A : Type'} (_96131 : A -> Prop) : (term478 A _96131) = (term465 A _96131).
Proof. exact (eq_refl (term478 A _96131)). Qed.
Lemma lem7176492 {A : Type'} (_96131 : A -> Prop) (x : type638 A) (h1 : term358 A x) : term465 A _96131.
Proof. exact (EQ_MP (@lem7176491 A _96131) (@lem7176490 A _96131 x h1)). Qed.
Lemma lem7176493 {A : Type'} (_96131 : A -> Prop) (_96132 : A -> Prop) (x : type638 A) (h1 : term358 A x) : term479 A _96131 _96132.
Proof. exact (@lem7176492 A _96131 x h1 _96132). Qed.
Lemma lem7176494 {A : Type'} (_96131 : A -> Prop) (_96132 : A -> Prop) : (term479 A _96131 _96132) = (term463 A _96131 _96132).
Proof. exact (eq_refl (term479 A _96131 _96132)). Qed.
Lemma lem7176495 {A : Type'} (_96131 : A -> Prop) (_96132 : A -> Prop) (x : type638 A) (h1 : term358 A x) : term463 A _96131 _96132.
Proof. exact (EQ_MP (@lem7176494 A _96131 _96132) (@lem7176493 A _96131 _96132 x h1)). Qed.
Lemma lem7176496 {A : Type'} (_96131 : A -> Prop) (_96132 : A -> Prop) (_96133 : A) (x : type638 A) (h1 : term358 A x) : term480 A _96131 _96132 _96133.
Proof. exact (@lem7176495 A _96131 _96132 x h1 _96133). Qed.
Lemma lem7176497 {A : Type'} (_96131 : A -> Prop) (_96133 : A) (_96132 : A -> Prop) : (term480 A _96131 _96132 _96133) = (term460 A _96131 _96133 _96132).
Proof. exact (eq_refl (term480 A _96131 _96132 _96133)). Qed.
Lemma lem7176508 {A : Type'} (_96137 : A -> Prop) (h1 : term24 A) : term481 A _96137.
Proof. exact (@lem7176175 A h1 _96137). Qed.
Lemma lem7176509 {A : Type'} (_96137 : A -> Prop) : (term481 A _96137) = (term473 A _96137).
Proof. exact (eq_refl (term481 A _96137)). Qed.
Lemma lem7176510 {A : Type'} (_96137 : A -> Prop) (h1 : term24 A) : term473 A _96137.
Proof. exact (EQ_MP (@lem7176509 A _96137) (@lem7176508 A _96137 h1)). Qed.
Lemma lem7176511 {A : Type'} (_96137 : A -> Prop) (_96138 : A -> Prop) (h1 : term24 A) : term482 A _96137 _96138.
Proof. exact (@lem7176510 A _96137 h1 _96138). Qed.
Lemma lem7176512 {A : Type'} (_96137 : A -> Prop) (_96138 : A -> Prop) : (term482 A _96137 _96138) = (term471 A _96137 _96138).
Proof. exact (eq_refl (term482 A _96137 _96138)). Qed.
Lemma lem7176513 {A : Type'} (_96137 : A -> Prop) (_96138 : A -> Prop) (h1 : term24 A) : term471 A _96137 _96138.
Proof. exact (EQ_MP (@lem7176512 A _96137 _96138) (@lem7176511 A _96137 _96138 h1)). Qed.
Lemma lem7176514 {A : Type'} (_96137 : A -> Prop) (_96138 : A -> Prop) (_96139 : A) (h1 : term24 A) : term483 A _96137 _96138 _96139.
Proof. exact (@lem7176513 A _96137 _96138 h1 _96139). Qed.
Lemma lem7176515 {A : Type'} (_96137 : A -> Prop) (_96139 : A) (_96138 : A -> Prop) : (term483 A _96137 _96138 _96139) = (term468 A _96137 _96139 _96138).
Proof. exact (eq_refl (term483 A _96137 _96138 _96139)). Qed.
Lemma lem7176516 {A : Type'} (_96137 : A -> Prop) (_96139 : A) (_96138 : A -> Prop) (h1 : term24 A) : term468 A _96137 _96139 _96138.
Proof. exact (EQ_MP (@lem7176515 A _96137 _96139 _96138) (@lem7176514 A _96137 _96138 _96139 h1)). Qed.
Lemma lem7176517 {A : Type'} (_96140 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term484 A v u f _96140.
Proof. exact (@lem7176204 A v u f h1 _96140). Qed.
Lemma lem7176518 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (_96140 : A) : (term484 A v u f _96140) = (term89 A v u f _96140).
Proof. exact (eq_refl (term484 A v u f _96140)). Qed.
Lemma lem7176576 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7176578 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem7176595 {A : Type'} (_96100 : A -> Prop) (_96099 : A -> Prop) : (term179 A _96100 _96099) = (term485 A _96100 _96099).
Proof. exact (@lem7173289 (term150 A _96100) (term453 A _96099 _96100) (@FINITE A _96099)). Qed.
Lemma lem7176596 {A : Type'} (_96100 : A -> Prop) (_96099 : A -> Prop) (h1 : term26 A) : term485 A _96100 _96099.
Proof. exact (EQ_MP (@lem7176595 A _96100 _96099) (@lem7176399 A _96100 _96099 h1)). Qed.
Lemma lem7176618 {A : Type'} (u : A -> Prop) (h1 : term150 A u) : term150 A u.
Proof. exact (h1). Qed.
Lemma lem7176644 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7176686 {A : Type'} (v : A -> Prop) (h1 : term150 A v) : term150 A v.
Proof. exact (h1). Qed.
Lemma lem7176714 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem7176742 {A : Type'} (_96131 : A -> Prop) (_96133 : A) (_96132 : A -> Prop) (x : type638 A) (h1 : term358 A x) : term460 A _96131 _96133 _96132.
Proof. exact (EQ_MP (@lem7176497 A _96131 _96133 _96132) (@lem7176496 A _96131 _96132 _96133 x h1)). Qed.
Lemma lem7176762 {A : Type'} (_96138 : A -> Prop) (_96139 : A) (_96137 : A -> Prop) (h1 : term24 A) : term486 A _96138 _96139 _96137.
Proof. exact (proj1 (@lem7176516 A _96137 _96139 _96138 h1)). Qed.
Lemma lem7176768 {A : Type'} (_96137 : A -> Prop) (_96139 : A) (_96138 : A -> Prop) (h1 : term24 A) : term487 A _96137 _96139 _96138.
Proof. exact (proj2 (@lem7176516 A _96137 _96139 _96138 h1)). Qed.
Lemma lem7176790 {A : Type'} (_96140 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term89 A v u f _96140.
Proof. exact (EQ_MP (@lem7176518 A v u f _96140) (@lem7176517 A _96140 v u f h1)). Qed.
Lemma lem7176826 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term106 A v u f x') : term488 A f x'.
Proof. exact (proj2 (@lem7175566 A v u f x' h1)). Qed.
Lemma lem7176852 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7176853 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : term489 A v.
Proof. exact (fun h0 : term150 A v => @lem7176852 A v h1). Qed.
Lemma lem7176855 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7176856 {A : Type'} (v : A -> Prop) : (term489 A v) = (@FINITE A v).
Proof. exact (@lem7176855 (@FINITE A v)). Qed.
Lemma lem7176857 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (EQ_MP (@lem7176856 A v) (@lem7176853 A v h1)). Qed.
Lemma lem7176859 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem7176860 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : term491 A u v.
Proof. exact (fun h0 : term453 A u v => @lem7176859 A u v h1). Qed.
Lemma lem7176862 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7176863 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term491 A u v) = (@SUBSET A u v).
Proof. exact (@lem7176862 (@SUBSET A u v)). Qed.
Lemma lem7176864 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (EQ_MP (@lem7176863 A u v) (@lem7176860 A u v h1)). Qed.
Lemma lem7176880 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7176881 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term492 A _96100 _96099) = (term493 A _96099 _96100).
Proof. exact (@lem7176880 (@FINITE A _96099) (term453 A _96099 _96100)). Qed.
Lemma lem7176887 {A : Type'} (_96100 : A -> Prop) : (term119 A _96100) = (term119 A _96100).
Proof. exact (eq_refl (term119 A _96100)). Qed.
Lemma lem7176888 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term485 A _96100 _96099) = (term494 A _96099 _96100).
Proof. exact (MK_COMB (@lem7176887 A _96100) (@lem7176881 A _96099 _96100)). Qed.
Lemma lem7176892 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7176893 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term494 A _96099 _96100) = (term495 A _96099 _96100).
Proof. exact (@lem7176892 (@FINITE A _96099) (term150 A _96100) (term453 A _96099 _96100)). Qed.
Lemma lem7176909 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term485 A _96100 _96099) = (term495 A _96099 _96100).
Proof. exact (TRANS (@lem7176888 A _96099 _96100) (@lem7176893 A _96099 _96100)). Qed.
Lemma lem7176910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7176911 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term496 A _96100 _96099) = (term497 A _96099 _96100).
Proof. exact (MK_COMB (@lem7176910) (@lem7176909 A _96099 _96100)). Qed.
Lemma lem7176927 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term495 A _96099 _96100) = (term495 A _96099 _96100).
Proof. exact (eq_refl (term495 A _96099 _96100)). Qed.
Lemma lem7176928 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : ((term485 A _96100 _96099) = (term495 A _96099 _96100)) = ((term495 A _96099 _96100) = (term495 A _96099 _96100)).
Proof. exact (MK_COMB (@lem7176911 A _96099 _96100) (@lem7176927 A _96099 _96100)). Qed.
Lemma lem7176930 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7176931 (x : Prop) : (x = x) = True.
Proof. exact (@lem7176930 Prop x). Qed.
Lemma lem7176932 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : ((term495 A _96099 _96100) = (term495 A _96099 _96100)) = True.
Proof. exact (@lem7176931 (term495 A _96099 _96100)). Qed.
Lemma lem7176933 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : ((term485 A _96100 _96099) = (term495 A _96099 _96100)) = True.
Proof. exact (TRANS (@lem7176928 A _96099 _96100) (@lem7176932 A _96099 _96100)). Qed.
Lemma lem7176934 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : True = ((term485 A _96100 _96099) = (term495 A _96099 _96100)).
Proof. exact (SYM (@lem7176933 A _96099 _96100)). Qed.
Lemma lem7176935 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term485 A _96100 _96099) = (term495 A _96099 _96100).
Proof. exact (EQ_MP (@lem7176934 A _96099 _96100) (@lem0)). Qed.
Lemma lem7176936 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) (h1 : term26 A) : term495 A _96099 _96100.
Proof. exact (EQ_MP (@lem7176935 A _96099 _96100) (@lem7176596 A _96100 _96099 h1)). Qed.
Lemma lem7176938 (b : Prop) (a : Prop) : (a \/ b) = (term498 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7176939 {A : Type'} (_96100 : A -> Prop) (_96099 : A -> Prop) : (term495 A _96099 _96100) = (term499 A _96100 _96099).
Proof. exact (@lem7176938 (term175 A _96099 _96100) (@FINITE A _96099)). Qed.
Lemma lem7176941 (a : Prop) (b : Prop) : (term500 a b) = (term501 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7176942 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term502 A _96099 _96100) = (term503 A _96099 _96100).
Proof. exact (@lem7176941 (term150 A _96100) (term453 A _96099 _96100)). Qed.
Lemma lem7176944 (a : Prop) : (term504 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7176945 {A : Type'} (_96100 : A -> Prop) : (term505 A _96100) = (@FINITE A _96100).
Proof. exact (@lem7176944 (@FINITE A _96100)). Qed.
Lemma lem7176946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7176947 {A : Type'} (_96100 : A -> Prop) : (term506 A _96100) = (term87 A _96100).
Proof. exact (MK_COMB (@lem7176946) (@lem7176945 A _96100)). Qed.
Lemma lem7176949 (a : Prop) : (term504 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7176950 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term507 A _96099 _96100) = (@SUBSET A _96099 _96100).
Proof. exact (@lem7176949 (@SUBSET A _96099 _96100)). Qed.
Lemma lem7176951 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term503 A _96099 _96100) = (term180 A _96099 _96100).
Proof. exact (MK_COMB (@lem7176947 A _96100) (@lem7176950 A _96099 _96100)). Qed.
Lemma lem7176952 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term502 A _96099 _96100) = (term180 A _96099 _96100).
Proof. exact (TRANS (@lem7176942 A _96099 _96100) (@lem7176951 A _96099 _96100)). Qed.
Lemma lem7176953 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7176954 {A : Type'} (_96099 : A -> Prop) (_96100 : A -> Prop) : (term508 A _96099 _96100) = (term509 A _96099 _96100).
Proof. exact (MK_COMB (@lem7176953) (@lem7176952 A _96099 _96100)). Qed.
Lemma lem7176955 {A : Type'} (_96099 : A -> Prop) : (@FINITE A _96099) = (@FINITE A _96099).
Proof. exact (eq_refl (@FINITE A _96099)). Qed.
Lemma lem7176956 {A : Type'} (_96100 : A -> Prop) (_96099 : A -> Prop) : (term499 A _96100 _96099) = (term76 A _96100 _96099).
Proof. exact (MK_COMB (@lem7176954 A _96099 _96100) (@lem7176955 A _96099)). Qed.
Lemma lem7176957 {A : Type'} (_96100 : A -> Prop) (_96099 : A -> Prop) : (term495 A _96099 _96100) = (term76 A _96100 _96099).
Proof. exact (TRANS (@lem7176939 A _96100 _96099) (@lem7176956 A _96100 _96099)). Qed.
Lemma lem7176959 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) (h2 : @SUBSET A u v) : term180 A u v.
Proof. exact (conj (@lem7176857 A v h1) (@lem7176864 A u v h2)). Qed.
Lemma lem7176961 {A : Type'} (_96100 : A -> Prop) (_96099 : A -> Prop) (h1 : term26 A) : term76 A _96100 _96099.
Proof. exact (EQ_MP (@lem7176957 A _96100 _96099) (@lem7176936 A _96099 _96100 h1)). Qed.
Lemma lem7176962 {A : Type'} (_96100 : A -> Prop) (_96099 : A -> Prop) (h1 : term26 A) : term76 A _96100 _96099.
Proof. exact (@lem7176961 A _96100 _96099 h1). Qed.
Lemma lem7176963 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term26 A) : term76 A v u.
Proof. exact (@lem7176962 A v u h1). Qed.
Lemma lem7176966 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : @FINITE A u.
Proof. exact (@lem7176963 A v u h1 (@lem7176959 A u v h2 h3)). Qed.
Lemma lem7176967 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : term489 A u.
Proof. exact (fun h0 : term150 A u => @lem7176966 A u v h1 h2 h3). Qed.
Lemma lem7176969 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7176970 {A : Type'} (u : A -> Prop) : (term489 A u) = (@FINITE A u).
Proof. exact (@lem7176969 (@FINITE A u)). Qed.
Lemma lem7176971 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : @FINITE A u.
Proof. exact (EQ_MP (@lem7176970 A u) (@lem7176967 A u v h1 h2 h3)). Qed.
Lemma lem7176974 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7176976 {A : Type'} (u : A -> Prop) : (term150 A u) = (term510 A u).
Proof. exact (@lem7176974 (@FINITE A u)). Qed.
Lemma lem7176979 {A : Type'} (u : A -> Prop) (h1 : term150 A u) : term510 A u.
Proof. exact (EQ_MP (@lem7176976 A u) (@lem7176618 A u h1)). Qed.
Lemma lem7176982 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (@lem7176979 A u h3 (@lem7176971 A u v h1 h2 h4)). Qed.
Lemma lem7176983 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : term511.
Proof. exact (fun h0 : ~ False => @lem7176982 A u v h1 h2 h3 h4). Qed.
Lemma lem7176985 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7176986 : term511 = False.
Proof. exact (@lem7176985 False). Qed.
Lemma lem7176987 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7176986) (@lem7176983 A u v h1 h2 h3 h4)). Qed.
Lemma lem7176989 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7176990 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : term489 A v.
Proof. exact (fun h0 : term150 A v => @lem7176989 A v h1). Qed.
Lemma lem7176992 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7176993 {A : Type'} (v : A -> Prop) : (term489 A v) = (@FINITE A v).
Proof. exact (@lem7176992 (@FINITE A v)). Qed.
Lemma lem7176994 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (EQ_MP (@lem7176993 A v) (@lem7176990 A v h1)). Qed.
Lemma lem7176997 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7176999 {A : Type'} (v : A -> Prop) : (term150 A v) = (term510 A v).
Proof. exact (@lem7176997 (@FINITE A v)). Qed.
Lemma lem7177002 {A : Type'} (v : A -> Prop) (h1 : term150 A v) : term510 A v.
Proof. exact (EQ_MP (@lem7176999 A v) (@lem7176686 A v h1)). Qed.
Lemma lem7177005 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : False.
Proof. exact (@lem7177002 A v h2 (@lem7176994 A v h1)). Qed.
Lemma lem7177006 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : term511.
Proof. exact (fun h0 : ~ False => @lem7177005 A v h1 h2). Qed.
Lemma lem7177008 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7177009 : term511 = False.
Proof. exact (@lem7177008 False). Qed.
Lemma lem7177010 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : False.
Proof. exact (EQ_MP (@lem7177009) (@lem7177006 A v h1 h2)). Qed.
Lemma lem7177012 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x' : A) (h1 : term94 A u v f x') : term62 A x' u v.
Proof. exact (proj1 (@lem7175565 A u v f x' h1)). Qed.
Lemma lem7177013 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x' : A) (h1 : term94 A u v f x') : term512 A x' u v.
Proof. exact (fun h0 : term469 A x' u v => @lem7177012 A u v f x' h1). Qed.
Lemma lem7177015 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7177016 {A : Type'} (x' : A) (u : A -> Prop) (v : A -> Prop) : (term512 A x' u v) = (term62 A x' u v).
Proof. exact (@lem7177015 (term62 A x' u v)). Qed.
Lemma lem7177017 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x' : A) (h1 : term94 A u v f x') : term62 A x' u v.
Proof. exact (EQ_MP (@lem7177016 A x' u v) (@lem7177013 A u v f x' h1)). Qed.
Lemma lem7177019 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (h1). Qed.
Lemma lem7177020 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : term491 A u v.
Proof. exact (fun h0 : term453 A u v => @lem7177019 A u v h1). Qed.
Lemma lem7177022 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7177023 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term491 A u v) = (@SUBSET A u v).
Proof. exact (@lem7177022 (@SUBSET A u v)). Qed.
Lemma lem7177024 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @SUBSET A u v) : @SUBSET A u v.
Proof. exact (EQ_MP (@lem7177023 A u v) (@lem7177020 A u v h1)). Qed.
Lemma lem7177026 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x' : A) (h1 : term94 A u v f x') : term62 A x' u v.
Proof. exact (proj1 (@lem7175565 A u v f x' h1)). Qed.
Lemma lem7177027 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x' : A) (h1 : term94 A u v f x') : term512 A x' u v.
Proof. exact (fun h0 : term469 A x' u v => @lem7177026 A u v f x' h1). Qed.
Lemma lem7177029 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7177030 {A : Type'} (x' : A) (u : A -> Prop) (v : A -> Prop) : (term512 A x' u v) = (term62 A x' u v).
Proof. exact (@lem7177029 (term62 A x' u v)). Qed.
Lemma lem7177031 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x' : A) (h1 : term94 A u v f x') : term62 A x' u v.
Proof. exact (EQ_MP (@lem7177030 A x' u v) (@lem7177027 A u v f x' h1)). Qed.
Lemma lem7177037 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7177038 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) : (term486 A _96138 _96139 _96137) = (term513 A _96139 _96137 _96138).
Proof. exact (@lem7177037 (@IN A _96139 _96137) (term469 A _96139 _96137 _96138)). Qed.
Lemma lem7177044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7177045 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) : (term514 A _96138 _96139 _96137) = (term515 A _96139 _96137 _96138).
Proof. exact (MK_COMB (@lem7177044) (@lem7177038 A _96139 _96137 _96138)). Qed.
Lemma lem7177051 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) : (term513 A _96139 _96137 _96138) = (term513 A _96139 _96137 _96138).
Proof. exact (eq_refl (term513 A _96139 _96137 _96138)). Qed.
Lemma lem7177052 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) : ((term486 A _96138 _96139 _96137) = (term513 A _96139 _96137 _96138)) = ((term513 A _96139 _96137 _96138) = (term513 A _96139 _96137 _96138)).
Proof. exact (MK_COMB (@lem7177045 A _96139 _96137 _96138) (@lem7177051 A _96139 _96137 _96138)). Qed.
Lemma lem7177054 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7177055 (x : Prop) : (x = x) = True.
Proof. exact (@lem7177054 Prop x). Qed.
Lemma lem7177056 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) : ((term513 A _96139 _96137 _96138) = (term513 A _96139 _96137 _96138)) = True.
Proof. exact (@lem7177055 (term513 A _96139 _96137 _96138)). Qed.
Lemma lem7177057 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) : ((term486 A _96138 _96139 _96137) = (term513 A _96139 _96137 _96138)) = True.
Proof. exact (TRANS (@lem7177052 A _96139 _96137 _96138) (@lem7177056 A _96139 _96137 _96138)). Qed.
Lemma lem7177058 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) : True = ((term486 A _96138 _96139 _96137) = (term513 A _96139 _96137 _96138)).
Proof. exact (SYM (@lem7177057 A _96139 _96137 _96138)). Qed.
Lemma lem7177059 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) : (term486 A _96138 _96139 _96137) = (term513 A _96139 _96137 _96138).
Proof. exact (EQ_MP (@lem7177058 A _96139 _96137 _96138) (@lem0)). Qed.
Lemma lem7177060 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) (h1 : term24 A) : term513 A _96139 _96137 _96138.
Proof. exact (EQ_MP (@lem7177059 A _96139 _96137 _96138) (@lem7176762 A _96138 _96139 _96137 h1)). Qed.
Lemma lem7177062 (b : Prop) (a : Prop) : (a \/ b) = (term498 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7177063 {A : Type'} (_96138 : A -> Prop) (_96139 : A) (_96137 : A -> Prop) : (term513 A _96139 _96137 _96138) = (term516 A _96138 _96139 _96137).
Proof. exact (@lem7177062 (term469 A _96139 _96137 _96138) (@IN A _96139 _96137)). Qed.
Lemma lem7177065 (a : Prop) : (term504 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7177066 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) : (term517 A _96139 _96137 _96138) = (term62 A _96139 _96137 _96138).
Proof. exact (@lem7177065 (term62 A _96139 _96137 _96138)). Qed.
Lemma lem7177067 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7177068 {A : Type'} (_96139 : A) (_96137 : A -> Prop) (_96138 : A -> Prop) : (term518 A _96139 _96137 _96138) = (term519 A _96139 _96137 _96138).
Proof. exact (MK_COMB (@lem7177067) (@lem7177066 A _96139 _96137 _96138)). Qed.
Lemma lem7177069 {A : Type'} (_96139 : A) (_96137 : A -> Prop) : (@IN A _96139 _96137) = (@IN A _96139 _96137).
Proof. exact (eq_refl (@IN A _96139 _96137)). Qed.
Lemma lem7177070 {A : Type'} (_96138 : A -> Prop) (_96139 : A) (_96137 : A -> Prop) : (term516 A _96138 _96139 _96137) = (term520 A _96138 _96139 _96137).
Proof. exact (MK_COMB (@lem7177068 A _96139 _96137 _96138) (@lem7177069 A _96139 _96137)). Qed.
Lemma lem7177071 {A : Type'} (_96138 : A -> Prop) (_96139 : A) (_96137 : A -> Prop) : (term513 A _96139 _96137 _96138) = (term520 A _96138 _96139 _96137).
Proof. exact (TRANS (@lem7177063 A _96138 _96139 _96137) (@lem7177070 A _96138 _96139 _96137)). Qed.
Lemma lem7177074 {A : Type'} (_96138 : A -> Prop) (_96139 : A) (_96137 : A -> Prop) (h1 : term24 A) : term520 A _96138 _96139 _96137.
Proof. exact (EQ_MP (@lem7177071 A _96138 _96139 _96137) (@lem7177060 A _96139 _96137 _96138 h1)). Qed.
Lemma lem7177075 {A : Type'} (_96138 : A -> Prop) (_96139 : A) (_96137 : A -> Prop) (h1 : term24 A) : term520 A _96138 _96139 _96137.
Proof. exact (@lem7177074 A _96138 _96139 _96137 h1). Qed.
Lemma lem7177076 {A : Type'} (v : A -> Prop) (x' : A) (u : A -> Prop) (h1 : term24 A) : term520 A v x' u.
Proof. exact (@lem7177075 A v x' u h1). Qed.
Lemma lem7177079 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x' : A) (h1 : term24 A) (h2 : term94 A u v f x') : @IN A x' u.
Proof. exact (@lem7177076 A v x' u h1 (@lem7177031 A u v f x' h2)). Qed.
Lemma lem7177080 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x' : A) (h1 : term24 A) (h2 : term94 A u v f x') : term521 A x' u.
Proof. exact (fun h0 : term366 A x' u => @lem7177079 A u v f x' h1 h2). Qed.
Lemma lem7177082 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7177083 {A : Type'} (x' : A) (u : A -> Prop) : (term521 A x' u) = (@IN A x' u).
Proof. exact (@lem7177082 (@IN A x' u)). Qed.
Lemma lem7177084 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x' : A) (h1 : term24 A) (h2 : term94 A u v f x') : @IN A x' u.
Proof. exact (EQ_MP (@lem7177083 A x' u) (@lem7177080 A u v f x' h1 h2)). Qed.
Lemma lem7177090 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7177091 {A : Type'} (_96131 : A -> Prop) (_96133 : A) (_96132 : A -> Prop) : (term460 A _96131 _96133 _96132) = (term522 A _96131 _96133 _96132).
Proof. exact (@lem7177090 (term366 A _96133 _96131) (term453 A _96131 _96132) (@IN A _96133 _96132)). Qed.
Lemma lem7177105 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7177106 {A : Type'} (_96133 : A) (_96131 : A -> Prop) (_96132 : A -> Prop) : (term523 A _96131 _96133 _96132) = (term524 A _96133 _96131 _96132).
Proof. exact (@lem7177105 (@IN A _96133 _96132) (term453 A _96131 _96132)). Qed.
Lemma lem7177112 {A : Type'} (_96133 : A) (_96131 : A -> Prop) : (term363 A _96133 _96131) = (term363 A _96133 _96131).
Proof. exact (eq_refl (term363 A _96133 _96131)). Qed.
Lemma lem7177113 {A : Type'} (_96133 : A) (_96131 : A -> Prop) (_96132 : A -> Prop) : (term522 A _96131 _96133 _96132) = (term525 A _96133 _96131 _96132).
Proof. exact (MK_COMB (@lem7177112 A _96133 _96131) (@lem7177106 A _96133 _96131 _96132)). Qed.
Lemma lem7177117 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7177118 {A : Type'} (_96133 : A) (_96131 : A -> Prop) (_96132 : A -> Prop) : (term525 A _96133 _96131 _96132) = (term526 A _96133 _96131 _96132).
Proof. exact (@lem7177117 (@IN A _96133 _96132) (term366 A _96133 _96131) (term453 A _96131 _96132)). Qed.
Lemma lem7177134 {A : Type'} (_96133 : A) (_96131 : A -> Prop) (_96132 : A -> Prop) : (term522 A _96131 _96133 _96132) = (term526 A _96133 _96131 _96132).
Proof. exact (TRANS (@lem7177113 A _96133 _96131 _96132) (@lem7177118 A _96133 _96131 _96132)). Qed.
Lemma lem7177135 {A : Type'} (_96133 : A) (_96131 : A -> Prop) (_96132 : A -> Prop) : (term460 A _96131 _96133 _96132) = (term526 A _96133 _96131 _96132).
Proof. exact (TRANS (@lem7177091 A _96131 _96133 _96132) (@lem7177134 A _96133 _96131 _96132)). Qed.
Lemma lem7177136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7177137 {A : Type'} (_96133 : A) (_96131 : A -> Prop) (_96132 : A -> Prop) : (term527 A _96131 _96133 _96132) = (term528 A _96133 _96131 _96132).
Proof. exact (MK_COMB (@lem7177136) (@lem7177135 A _96133 _96131 _96132)). Qed.
Lemma lem7177151 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7177152 {A : Type'} (_96133 : A) (_96131 : A -> Prop) (_96132 : A -> Prop) : (term529 A _96132 _96133 _96131) = (term530 A _96133 _96131 _96132).
Proof. exact (@lem7177151 (term366 A _96133 _96131) (term453 A _96131 _96132)). Qed.
Lemma lem7177158 {A : Type'} (_96133 : A) (_96132 : A -> Prop) : (term531 A _96133 _96132) = (term531 A _96133 _96132).
Proof. exact (eq_refl (term531 A _96133 _96132)). Qed.
Lemma lem7177159 {A : Type'} (_96133 : A) (_96131 : A -> Prop) (_96132 : A -> Prop) : (term532 A _96132 _96133 _96131) = (term526 A _96133 _96131 _96132).
Proof. exact (MK_COMB (@lem7177158 A _96133 _96132) (@lem7177152 A _96133 _96131 _96132)). Qed.
Lemma lem7177170 {A : Type'} (_96133 : A) (_96131 : A -> Prop) (_96132 : A -> Prop) : ((term460 A _96131 _96133 _96132) = (term532 A _96132 _96133 _96131)) = ((term526 A _96133 _96131 _96132) = (term526 A _96133 _96131 _96132)).
Proof. exact (MK_COMB (@lem7177137 A _96133 _96131 _96132) (@lem7177159 A _96133 _96131 _96132)). Qed.
Lemma lem7177172 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7177173 (x : Prop) : (x = x) = True.
Proof. exact (@lem7177172 Prop x). Qed.
Lemma lem7177174 {A : Type'} (_96133 : A) (_96131 : A -> Prop) (_96132 : A -> Prop) : ((term526 A _96133 _96131 _96132) = (term526 A _96133 _96131 _96132)) = True.
Proof. exact (@lem7177173 (term526 A _96133 _96131 _96132)). Qed.
Lemma lem7177175 {A : Type'} (_96132 : A -> Prop) (_96133 : A) (_96131 : A -> Prop) : ((term460 A _96131 _96133 _96132) = (term532 A _96132 _96133 _96131)) = True.
Proof. exact (TRANS (@lem7177170 A _96133 _96131 _96132) (@lem7177174 A _96133 _96131 _96132)). Qed.
Lemma lem7177176 {A : Type'} (_96132 : A -> Prop) (_96133 : A) (_96131 : A -> Prop) : True = ((term460 A _96131 _96133 _96132) = (term532 A _96132 _96133 _96131)).
Proof. exact (SYM (@lem7177175 A _96132 _96133 _96131)). Qed.
Lemma lem7177177 {A : Type'} (_96132 : A -> Prop) (_96133 : A) (_96131 : A -> Prop) : (term460 A _96131 _96133 _96132) = (term532 A _96132 _96133 _96131).
Proof. exact (EQ_MP (@lem7177176 A _96132 _96133 _96131) (@lem0)). Qed.
Lemma lem7177178 {A : Type'} (_96132 : A -> Prop) (_96133 : A) (_96131 : A -> Prop) (x : type638 A) (h1 : term358 A x) : term532 A _96132 _96133 _96131.
Proof. exact (EQ_MP (@lem7177177 A _96132 _96133 _96131) (@lem7176742 A _96131 _96133 _96132 x h1)). Qed.
Lemma lem7177180 (b : Prop) (a : Prop) : (a \/ b) = (term498 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7177181 {A : Type'} (_96131 : A -> Prop) (_96133 : A) (_96132 : A -> Prop) : (term532 A _96132 _96133 _96131) = (term533 A _96131 _96133 _96132).
Proof. exact (@lem7177180 (term529 A _96132 _96133 _96131) (@IN A _96133 _96132)). Qed.
Lemma lem7177183 (a : Prop) (b : Prop) : (term500 a b) = (term501 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7177184 {A : Type'} (_96132 : A -> Prop) (_96133 : A) (_96131 : A -> Prop) : (term534 A _96132 _96133 _96131) = (term535 A _96132 _96133 _96131).
Proof. exact (@lem7177183 (term453 A _96131 _96132) (term366 A _96133 _96131)). Qed.
Lemma lem7177186 (a : Prop) : (term504 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7177187 {A : Type'} (_96131 : A -> Prop) (_96132 : A -> Prop) : (term507 A _96131 _96132) = (@SUBSET A _96131 _96132).
Proof. exact (@lem7177186 (@SUBSET A _96131 _96132)). Qed.
Lemma lem7177188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7177189 {A : Type'} (_96131 : A -> Prop) (_96132 : A -> Prop) : (term536 A _96131 _96132) = (term537 A _96131 _96132).
Proof. exact (MK_COMB (@lem7177188) (@lem7177187 A _96131 _96132)). Qed.
Lemma lem7177191 (a : Prop) : (term504 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7177192 {A : Type'} (_96133 : A) (_96131 : A -> Prop) : (term362 A _96133 _96131) = (@IN A _96133 _96131).
Proof. exact (@lem7177191 (@IN A _96133 _96131)). Qed.
Lemma lem7177193 {A : Type'} (_96132 : A -> Prop) (_96133 : A) (_96131 : A -> Prop) : (term535 A _96132 _96133 _96131) = (term538 A _96132 _96133 _96131).
Proof. exact (MK_COMB (@lem7177189 A _96131 _96132) (@lem7177192 A _96133 _96131)). Qed.
Lemma lem7177194 {A : Type'} (_96132 : A -> Prop) (_96133 : A) (_96131 : A -> Prop) : (term534 A _96132 _96133 _96131) = (term538 A _96132 _96133 _96131).
Proof. exact (TRANS (@lem7177184 A _96132 _96133 _96131) (@lem7177193 A _96132 _96133 _96131)). Qed.
Lemma lem7177195 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7177196 {A : Type'} (_96132 : A -> Prop) (_96133 : A) (_96131 : A -> Prop) : (term539 A _96132 _96133 _96131) = (term540 A _96132 _96133 _96131).
Proof. exact (MK_COMB (@lem7177195) (@lem7177194 A _96132 _96133 _96131)). Qed.
Lemma lem7177197 {A : Type'} (_96133 : A) (_96132 : A -> Prop) : (@IN A _96133 _96132) = (@IN A _96133 _96132).
Proof. exact (eq_refl (@IN A _96133 _96132)). Qed.
Lemma lem7177198 {A : Type'} (_96131 : A -> Prop) (_96133 : A) (_96132 : A -> Prop) : (term533 A _96131 _96133 _96132) = (term541 A _96131 _96133 _96132).
Proof. exact (MK_COMB (@lem7177196 A _96132 _96133 _96131) (@lem7177197 A _96133 _96132)). Qed.
Lemma lem7177199 {A : Type'} (_96131 : A -> Prop) (_96133 : A) (_96132 : A -> Prop) : (term532 A _96132 _96133 _96131) = (term541 A _96131 _96133 _96132).
Proof. exact (TRANS (@lem7177181 A _96131 _96133 _96132) (@lem7177198 A _96131 _96133 _96132)). Qed.
Lemma lem7177201 {A : Type'} (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term94 A u v f x') (h3 : @SUBSET A u v) : term538 A v x' u.
Proof. exact (conj (@lem7177024 A u v h3) (@lem7177084 A u v f x' h1 h2)). Qed.
Lemma lem7177203 {A : Type'} (_96131 : A -> Prop) (_96133 : A) (_96132 : A -> Prop) (x : type638 A) (h1 : term358 A x) : term541 A _96131 _96133 _96132.
Proof. exact (EQ_MP (@lem7177199 A _96131 _96133 _96132) (@lem7177178 A _96132 _96133 _96131 x h1)). Qed.
Lemma lem7177204 {A : Type'} (_96131 : A -> Prop) (_96133 : A) (_96132 : A -> Prop) (x : type638 A) (h1 : term358 A x) : term541 A _96131 _96133 _96132.
Proof. exact (@lem7177203 A _96131 _96133 _96132 x h1). Qed.
Lemma lem7177205 {A : Type'} (u : A -> Prop) (x' : A) (v : A -> Prop) (x : type638 A) (h1 : term358 A x) : term541 A u x' v.
Proof. exact (@lem7177204 A u x' v x h1). Qed.
Lemma lem7177208 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : @IN A x' v.
Proof. exact (@lem7177205 A u x' v x h2 (@lem7177201 A f x' u v h1 h3 h4)). Qed.
Lemma lem7177209 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : term521 A x' v.
Proof. exact (fun h0 : term366 A x' v => @lem7177208 A x f x' u v h1 h2 h3 h4). Qed.
Lemma lem7177211 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7177212 {A : Type'} (x' : A) (v : A -> Prop) : (term521 A x' v) = (@IN A x' v).
Proof. exact (@lem7177211 (@IN A x' v)). Qed.
Lemma lem7177213 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : @IN A x' v.
Proof. exact (EQ_MP (@lem7177212 A x' v) (@lem7177209 A x f x' u v h1 h2 h3 h4)). Qed.
Lemma lem7177215 (a : Prop) (b : Prop) : (term542 a b) = (term543 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7177216 {A : Type'} (_96137 : A -> Prop) (_96139 : A) (_96138 : A -> Prop) : (term487 A _96137 _96139 _96138) = (term544 A _96137 _96139 _96138).
Proof. exact (@lem7177215 (term62 A _96139 _96137 _96138) (@IN A _96139 _96138)). Qed.
Lemma lem7177218 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7177219 {A : Type'} (_96137 : A -> Prop) (_96139 : A) (_96138 : A -> Prop) : (term544 A _96137 _96139 _96138) = (term545 A _96137 _96139 _96138).
Proof. exact (@lem7177218 (term546 A _96137 _96139 _96138)). Qed.
Lemma lem7177220 {A : Type'} (_96137 : A -> Prop) (_96139 : A) (_96138 : A -> Prop) : (term487 A _96137 _96139 _96138) = (term545 A _96137 _96139 _96138).
Proof. exact (TRANS (@lem7177216 A _96137 _96139 _96138) (@lem7177219 A _96137 _96139 _96138)). Qed.
Lemma lem7177222 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : term546 A u x' v.
Proof. exact (conj (@lem7177017 A u v f x' h3) (@lem7177213 A x f x' u v h1 h2 h3 h4)). Qed.
Lemma lem7177224 {A : Type'} (_96137 : A -> Prop) (_96139 : A) (_96138 : A -> Prop) (h1 : term24 A) : term545 A _96137 _96139 _96138.
Proof. exact (EQ_MP (@lem7177220 A _96137 _96139 _96138) (@lem7176768 A _96137 _96139 _96138 h1)). Qed.
Lemma lem7177225 {A : Type'} (_96137 : A -> Prop) (_96139 : A) (_96138 : A -> Prop) (h1 : term24 A) : term545 A _96137 _96139 _96138.
Proof. exact (@lem7177224 A _96137 _96139 _96138 h1). Qed.
Lemma lem7177226 {A : Type'} (u : A -> Prop) (x' : A) (v : A -> Prop) (h1 : term24 A) : term545 A u x' v.
Proof. exact (@lem7177225 A u x' v h1). Qed.
Lemma lem7177229 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : False.
Proof. exact (@lem7177226 A u x' v h1 (@lem7177222 A x f x' u v h1 h2 h3 h4)). Qed.
Lemma lem7177230 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : term511.
Proof. exact (fun h0 : ~ False => @lem7177229 A x f x' u v h1 h2 h3 h4). Qed.
Lemma lem7177232 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7177233 : term511 = False.
Proof. exact (@lem7177232 False). Qed.
Lemma lem7177234 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177233) (@lem7177230 A x f x' u v h1 h2 h3 h4)). Qed.
Lemma lem7177236 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term106 A v u f x') : term62 A x' v u.
Proof. exact (proj1 (@lem7175566 A v u f x' h1)). Qed.
Lemma lem7177237 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term106 A v u f x') : term512 A x' v u.
Proof. exact (fun h0 : term469 A x' v u => @lem7177236 A v u f x' h1). Qed.
Lemma lem7177239 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7177240 {A : Type'} (x' : A) (v : A -> Prop) (u : A -> Prop) : (term512 A x' v u) = (term62 A x' v u).
Proof. exact (@lem7177239 (term62 A x' v u)). Qed.
Lemma lem7177241 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term106 A v u f x') : term62 A x' v u.
Proof. exact (EQ_MP (@lem7177240 A x' v u) (@lem7177237 A v u f x' h1)). Qed.
Lemma lem7177247 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7177248 {A : Type'} (f : A -> real) (_96140 : A) (v : A -> Prop) (u : A -> Prop) : (term89 A v u f _96140) = (term547 A f _96140 v u).
Proof. exact (@lem7177247 (term90 A f _96140) (term469 A _96140 v u)). Qed.
Lemma lem7177254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7177255 {A : Type'} (f : A -> real) (_96140 : A) (v : A -> Prop) (u : A -> Prop) : (term548 A v u f _96140) = (term549 A f _96140 v u).
Proof. exact (MK_COMB (@lem7177254) (@lem7177248 A f _96140 v u)). Qed.
Lemma lem7177261 {A : Type'} (f : A -> real) (_96140 : A) (v : A -> Prop) (u : A -> Prop) : (term547 A f _96140 v u) = (term547 A f _96140 v u).
Proof. exact (eq_refl (term547 A f _96140 v u)). Qed.
Lemma lem7177262 {A : Type'} (f : A -> real) (_96140 : A) (v : A -> Prop) (u : A -> Prop) : ((term89 A v u f _96140) = (term547 A f _96140 v u)) = ((term547 A f _96140 v u) = (term547 A f _96140 v u)).
Proof. exact (MK_COMB (@lem7177255 A f _96140 v u) (@lem7177261 A f _96140 v u)). Qed.
Lemma lem7177264 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7177265 (x : Prop) : (x = x) = True.
Proof. exact (@lem7177264 Prop x). Qed.
Lemma lem7177266 {A : Type'} (f : A -> real) (_96140 : A) (v : A -> Prop) (u : A -> Prop) : ((term547 A f _96140 v u) = (term547 A f _96140 v u)) = True.
Proof. exact (@lem7177265 (term547 A f _96140 v u)). Qed.
Lemma lem7177267 {A : Type'} (f : A -> real) (_96140 : A) (v : A -> Prop) (u : A -> Prop) : ((term89 A v u f _96140) = (term547 A f _96140 v u)) = True.
Proof. exact (TRANS (@lem7177262 A f _96140 v u) (@lem7177266 A f _96140 v u)). Qed.
Lemma lem7177268 {A : Type'} (f : A -> real) (_96140 : A) (v : A -> Prop) (u : A -> Prop) : True = ((term89 A v u f _96140) = (term547 A f _96140 v u)).
Proof. exact (SYM (@lem7177267 A f _96140 v u)). Qed.
Lemma lem7177269 {A : Type'} (f : A -> real) (_96140 : A) (v : A -> Prop) (u : A -> Prop) : (term89 A v u f _96140) = (term547 A f _96140 v u).
Proof. exact (EQ_MP (@lem7177268 A f _96140 v u) (@lem0)). Qed.
Lemma lem7177270 {A : Type'} (_96140 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term547 A f _96140 v u.
Proof. exact (EQ_MP (@lem7177269 A f _96140 v u) (@lem7176790 A _96140 v u f h1)). Qed.
Lemma lem7177272 (b : Prop) (a : Prop) : (a \/ b) = (term498 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7177273 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (_96140 : A) : (term547 A f _96140 v u) = (term550 A v u f _96140).
Proof. exact (@lem7177272 (term469 A _96140 v u) (term90 A f _96140)). Qed.
Lemma lem7177275 (a : Prop) : (term504 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7177276 {A : Type'} (_96140 : A) (v : A -> Prop) (u : A -> Prop) : (term517 A _96140 v u) = (term62 A _96140 v u).
Proof. exact (@lem7177275 (term62 A _96140 v u)). Qed.
Lemma lem7177277 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7177278 {A : Type'} (_96140 : A) (v : A -> Prop) (u : A -> Prop) : (term518 A _96140 v u) = (term519 A _96140 v u).
Proof. exact (MK_COMB (@lem7177277) (@lem7177276 A _96140 v u)). Qed.
Lemma lem7177279 {A : Type'} (f : A -> real) (_96140 : A) : (term90 A f _96140) = (term90 A f _96140).
Proof. exact (eq_refl (term90 A f _96140)). Qed.
Lemma lem7177280 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (_96140 : A) : (term550 A v u f _96140) = (term80 A v u f _96140).
Proof. exact (MK_COMB (@lem7177278 A _96140 v u) (@lem7177279 A f _96140)). Qed.
Lemma lem7177281 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (_96140 : A) : (term547 A f _96140 v u) = (term80 A v u f _96140).
Proof. exact (TRANS (@lem7177273 A v u f _96140) (@lem7177280 A v u f _96140)). Qed.
Lemma lem7177284 {A : Type'} (_96140 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term80 A v u f _96140.
Proof. exact (EQ_MP (@lem7177281 A v u f _96140) (@lem7177270 A _96140 v u f h1)). Qed.
Lemma lem7177285 {A : Type'} (_96140 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term80 A v u f _96140.
Proof. exact (@lem7177284 A _96140 v u f h1). Qed.
Lemma lem7177286 {A : Type'} (x' : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term80 A v u f x'.
Proof. exact (@lem7177285 A x' v u f h1). Qed.
Lemma lem7177289 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term106 A v u f x') : term90 A f x'.
Proof. exact (@lem7177286 A x' v u f h1 (@lem7177241 A v u f x' h2)). Qed.
Lemma lem7177290 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term106 A v u f x') : term551 A f x'.
Proof. exact (fun h0 : term488 A f x' => @lem7177289 A v u f x' h1 h2). Qed.
Lemma lem7177292 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7177293 {A : Type'} (f : A -> real) (x' : A) : (term551 A f x') = (term90 A f x').
Proof. exact (@lem7177292 (term90 A f x')). Qed.
Lemma lem7177294 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term106 A v u f x') : term90 A f x'.
Proof. exact (EQ_MP (@lem7177293 A f x') (@lem7177290 A v u f x' h1 h2)). Qed.
Lemma lem7177297 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7177299 {A : Type'} (f : A -> real) (x' : A) : (term488 A f x') = (term552 A f x').
Proof. exact (@lem7177297 (term90 A f x')). Qed.
Lemma lem7177302 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term106 A v u f x') : term552 A f x'.
Proof. exact (EQ_MP (@lem7177299 A f x') (@lem7176826 A v u f x' h1)). Qed.
Lemma lem7177305 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term106 A v u f x') : False.
Proof. exact (@lem7177302 A v u f x' h2 (@lem7177294 A v u f x' h1 h2)). Qed.
Lemma lem7177306 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term106 A v u f x') : term511.
Proof. exact (fun h0 : ~ False => @lem7177305 A v u f x' h1 h2). Qed.
Lemma lem7177308 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7177309 : term511 = False.
Proof. exact (@lem7177308 False). Qed.
Lemma lem7177310 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term106 A v u f x') : False.
Proof. exact (EQ_MP (@lem7177309) (@lem7177306 A v u f x' h1 h2)). Qed.
Lemma lem7177311 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem7177234 A x f x' u v h1 h2 h3 h4) (fun h5 : False => @lem7176714 A u v h4)). Qed.
Lemma lem7177312 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177311 A x f x' u v h1 h2 h3 h4) (@lem7176714 A u v h4)). Qed.
Lemma lem7177313 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : (term150 A v) = False.
Proof. exact (prop_ext (fun h3 : term150 A v => @lem7177010 A v h1 h2) (fun h3 : False => @lem7176686 A v h2)). Qed.
Lemma lem7177314 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : False.
Proof. exact (EQ_MP (@lem7177313 A v h1 h2) (@lem7176686 A v h2)). Qed.
Lemma lem7177315 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : (@FINITE A v) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A v => @lem7177314 A v h1 h2) (fun h3 : False => @lem7176644 A v h1)). Qed.
Lemma lem7177316 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : False.
Proof. exact (EQ_MP (@lem7177315 A v h1 h2) (@lem7176644 A v h1)). Qed.
Lemma lem7177317 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : (term150 A u) = False.
Proof. exact (prop_ext (fun h5 : term150 A u => @lem7176987 A u v h1 h2 h3 h4) (fun h5 : False => @lem7176618 A u h3)). Qed.
Lemma lem7177318 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177317 A u v h1 h2 h3 h4) (@lem7176618 A u h3)). Qed.
Lemma lem7177319 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem7177318 A u v h1 h2 h3 h4) (fun h5 : False => @lem7176578 A u v h4)). Qed.
Lemma lem7177320 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177319 A u v h1 h2 h3 h4) (@lem7176578 A u v h4)). Qed.
Lemma lem7177321 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : (@FINITE A v) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A v => @lem7177320 A u v h1 h2 h3 h4) (fun h5 : False => @lem7176576 A v h2)). Qed.
Lemma lem7177322 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177321 A u v h1 h2 h3 h4) (@lem7176576 A v h2)). Qed.
Lemma lem7177323 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem7177312 A x f x' u v h1 h2 h3 h4) (fun h5 : False => @lem7175984 A u v h4)). Qed.
Lemma lem7177324 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177323 A x f x' u v h1 h2 h3 h4) (@lem7175984 A u v h4)). Qed.
Lemma lem7177325 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : (term150 A v) = False.
Proof. exact (prop_ext (fun h3 : term150 A v => @lem7177316 A v h1 h2) (fun h3 : False => @lem7175976 A v h2)). Qed.
Lemma lem7177326 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : False.
Proof. exact (EQ_MP (@lem7177325 A v h1 h2) (@lem7175976 A v h2)). Qed.
Lemma lem7177327 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : (@FINITE A v) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A v => @lem7177326 A v h1 h2) (fun h3 : False => @lem7175777 A v h1)). Qed.
Lemma lem7177328 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : False.
Proof. exact (EQ_MP (@lem7177327 A v h1 h2) (@lem7175777 A v h1)). Qed.
Lemma lem7177329 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : (term150 A u) = False.
Proof. exact (prop_ext (fun h5 : term150 A u => @lem7177322 A u v h1 h2 h3 h4) (fun h5 : False => @lem7175773 A u h3)). Qed.
Lemma lem7177330 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177329 A u v h1 h2 h3 h4) (@lem7175773 A u h3)). Qed.
Lemma lem7177331 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem7177330 A u v h1 h2 h3 h4) (fun h5 : False => @lem7175578 A u v h4)). Qed.
Lemma lem7177332 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177331 A u v h1 h2 h3 h4) (@lem7175578 A u v h4)). Qed.
Lemma lem7177333 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : (@FINITE A v) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A v => @lem7177332 A u v h1 h2 h3 h4) (fun h5 : False => @lem7175574 A v h2)). Qed.
Lemma lem7177334 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177333 A u v h1 h2 h3 h4) (@lem7175574 A v h2)). Qed.
Lemma lem7177335 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem7177324 A x f x' u v h1 h2 h3 h4) (fun h5 : False => @lem7175984 A u v h4)). Qed.
Lemma lem7177336 {A : Type'} (x : type638 A) (f : A -> real) (x' : A) (u : A -> Prop) (v : A -> Prop) (h1 : term24 A) (h2 : term358 A x) (h3 : term94 A u v f x') (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177335 A x f x' u v h1 h2 h3 h4) (@lem7175984 A u v h4)). Qed.
Lemma lem7177337 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : (term150 A v) = False.
Proof. exact (prop_ext (fun h3 : term150 A v => @lem7177328 A v h1 h2) (fun h3 : False => @lem7175976 A v h2)). Qed.
Lemma lem7177338 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : False.
Proof. exact (EQ_MP (@lem7177337 A v h1 h2) (@lem7175976 A v h2)). Qed.
Lemma lem7177339 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : (@FINITE A v) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A v => @lem7177338 A v h1 h2) (fun h3 : False => @lem7175777 A v h1)). Qed.
Lemma lem7177340 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) (h2 : term150 A v) : False.
Proof. exact (EQ_MP (@lem7177339 A v h1 h2) (@lem7175777 A v h1)). Qed.
Lemma lem7177341 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : (term150 A u) = False.
Proof. exact (prop_ext (fun h5 : term150 A u => @lem7177334 A u v h1 h2 h3 h4) (fun h5 : False => @lem7175773 A u h3)). Qed.
Lemma lem7177342 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177341 A u v h1 h2 h3 h4) (@lem7175773 A u h3)). Qed.
Lemma lem7177343 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A u v => @lem7177342 A u v h1 h2 h3 h4) (fun h5 : False => @lem7175578 A u v h4)). Qed.
Lemma lem7177344 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177343 A u v h1 h2 h3 h4) (@lem7175578 A u v h4)). Qed.
Lemma lem7177345 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : (@FINITE A v) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A v => @lem7177344 A u v h1 h2 h3 h4) (fun h5 : False => @lem7175574 A v h2)). Qed.
Lemma lem7177346 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term26 A) (h2 : @FINITE A v) (h3 : term150 A u) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177345 A u v h1 h2 h3 h4) (@lem7175574 A v h2)). Qed.
Lemma lem7177347 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term358 A x) (h4 : @SUBSET A u v) (h5 : term141 A v u f x') : False.
Proof. exact (or_elim (@lem7175564 A v u f x' h5) (fun h0 : term94 A u v f x' => @lem7177336 A x f x' u v h2 h3 h0 h4) (fun h0 : term106 A v u f x' => @lem7177310 A v u f x' h1 h0)). Qed.
Lemma lem7177348 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : @FINITE A v) (h4 : term358 A x) (h5 : @SUBSET A u v) (h6 : term157 A v u f x') : False.
Proof. exact (or_elim (@lem7175562 A v u f x' h6) (fun h0 : term150 A v => @lem7177340 A v h3 h0) (fun h0 : term141 A v u f x' => @lem7177347 A x v u f x' h1 h2 h4 h5 h0)). Qed.
Lemma lem7177349 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term358 A x) (h6 : @SUBSET A u v) (h7 : term170 A v u f x') : False.
Proof. exact (or_elim (@lem7175556 A v u f x' h7) (fun h0 : term150 A u => @lem7177346 A u v h3 h4 h0 h6) (fun h0 : term157 A v u f x' => @lem7177348 A x v u f x' h1 h2 h4 h5 h6 h0)). Qed.
Lemma lem7177350 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term358 A x) (h6 : @SUBSET A u v) (h7 : term170 A v u f x') : (term170 A v u f x') = False.
Proof. exact (prop_ext (fun h8 : term170 A v u f x' => @lem7177349 A x v u f x' h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem7175556 A v u f x' h7)). Qed.
Lemma lem7177351 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term358 A x) (h6 : @SUBSET A u v) (h7 : term170 A v u f x') : False.
Proof. exact (EQ_MP (@lem7177350 A x v u f x' h1 h2 h3 h4 h5 h6 h7) (@lem7175556 A v u f x' h7)). Qed.
Lemma lem7177352 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term358 A x) (h6 : @SUBSET A u v) (h7 : term170 A v u f x') : (term358 A x) = False.
Proof. exact (prop_ext (fun h8 : term358 A x => @lem7177351 A x v u f x' h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem7175486 A x h5)). Qed.
Lemma lem7177353 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term358 A x) (h6 : @SUBSET A u v) (h7 : term170 A v u f x') : False.
Proof. exact (EQ_MP (@lem7177352 A x v u f x' h1 h2 h3 h4 h5 h6 h7) (@lem7175486 A x h5)). Qed.
Lemma lem7177354 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term358 A x) (h6 : @SUBSET A u v) (h7 : term170 A v u f x') : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h8 : @SUBSET A u v => @lem7177353 A x v u f x' h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem7175276 A u v h6)). Qed.
Lemma lem7177355 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term358 A x) (h6 : @SUBSET A u v) (h7 : term170 A v u f x') : False.
Proof. exact (EQ_MP (@lem7177354 A x v u f x' h1 h2 h3 h4 h5 h6 h7) (@lem7175276 A u v h6)). Qed.
Lemma lem7177356 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term358 A x) (h6 : @SUBSET A u v) (h7 : term170 A v u f x') : (@FINITE A v) = False.
Proof. exact (prop_ext (fun h8 : @FINITE A v => @lem7177355 A x v u f x' h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem7175270 A v h4)). Qed.
Lemma lem7177357 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term358 A x) (h6 : @SUBSET A u v) (h7 : term170 A v u f x') : False.
Proof. exact (EQ_MP (@lem7177356 A x v u f x' h1 h2 h3 h4 h5 h6 h7) (@lem7175270 A v h4)). Qed.
Lemma lem7177358 {A : Type'} (f : A -> real) (x : type638 A) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term23 A v u f) (h6 : term358 A x) (h7 : @SUBSET A u v) : False.
Proof. exact (ex_elim (@lem7174041 A v u f h5) (fun x' : A => fun h0 : term172 A v u f x' => @lem7177357 A x v u f x' h1 h2 h3 h4 h6 h7 h0)). Qed.
Lemma lem7177359 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term25 A) (h4 : term26 A) (h5 : @FINITE A v) (h6 : term23 A v u f) (h7 : @SUBSET A u v) : False.
Proof. exact (ex_elim (@lem7174815 A h3) (fun x : type638 A => fun h0 : term360 A x => @lem7177358 A f x u v h1 h2 h4 h5 h6 h0 h7)). Qed.
Lemma lem7177360 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term25 A) (h4 : term26 A) (h5 : @FINITE A v) (h6 : term23 A v u f) (h7 : @SUBSET A u v) : (@SUBSET A u v) = False.
Proof. exact (prop_ext (fun h8 : @SUBSET A u v => @lem7177359 A f u v h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem7173754 A u v h7)). Qed.
Lemma lem7177361 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term25 A) (h4 : term26 A) (h5 : @FINITE A v) (h6 : term23 A v u f) (h7 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177360 A f u v h1 h2 h3 h4 h5 h6 h7) (@lem7173754 A u v h7)). Qed.
Lemma lem7177362 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term25 A) (h4 : term26 A) (h5 : @FINITE A v) (h6 : term23 A v u f) (h7 : @SUBSET A u v) : (@FINITE A v) = False.
Proof. exact (prop_ext (fun h8 : @FINITE A v => @lem7177361 A f u v h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem7173748 A v h5)). Qed.
Lemma lem7177363 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : term24 A) (h3 : term25 A) (h4 : term26 A) (h5 : @FINITE A v) (h6 : term23 A v u f) (h7 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177362 A f u v h1 h2 h3 h4 h5 h6 h7) (@lem7173748 A v h5)). Qed.
Lemma lem7177364 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : term25 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term23 A v u f) (h6 : @SUBSET A u v) : term31 A.
Proof. exact (fun h0 : term24 A => @lem7177363 A f u v h1 h0 h2 h3 h4 h5 h6). Qed.
Lemma lem7177365 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (@lem69 (term24 A)). Qed.
Lemma lem7177366 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : term25 A) (h3 : term26 A) (h4 : @FINITE A v) (h5 : term23 A v u f) (h6 : @SUBSET A u v) : term32 A.
Proof. exact (EQ_MP (@lem7177365 A) (@lem7177364 A f u v h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem7177367 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : term26 A) (h3 : @FINITE A v) (h4 : term23 A v u f) (h5 : @SUBSET A u v) : term35 A.
Proof. exact (fun h0 : term25 A => @lem7177366 A f u v h1 h0 h2 h3 h4 h5). Qed.
Lemma lem7177368 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : term23 A v u f) (h4 : @SUBSET A u v) : term38 A.
Proof. exact (fun h0 : term26 A => @lem7177367 A f u v h1 h0 h2 h3 h4). Qed.
Lemma lem7177369 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : term41 A v u f.
Proof. exact (fun h0 : term23 A v u f => @lem7177368 A f u v h1 h2 h0 h3). Qed.
Lemma lem7177370 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) (h2 : @SUBSET A u v) : term44 A v u f.
Proof. exact (fun h0 : term20 A v u f => @lem7177369 A f u v h0 h1 h2). Qed.
Lemma lem7177371 {A : Type'} (u : A -> Prop) (f : A -> real) (v : A -> Prop) (h1 : @FINITE A v) : term47 A v u f.
Proof. exact (fun h0 : @SUBSET A u v => @lem7177370 A f u v h1 h0). Qed.
Lemma lem7177372 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term49 A v u f.
Proof. exact (fun h0 : @FINITE A v => @lem7177371 A u f v h0). Qed.
Lemma lem7177377 {A : Type'} (u : A -> Prop) (f : A -> real) : term53 A u f.
Proof. exact (fun v : A -> Prop => @lem7177372 A v u f). Qed.
Lemma lem7177382 {A : Type'} (f : A -> real) : term57 A f.
Proof. exact (fun u : A -> Prop => @lem7177377 A u f). Qed.
Lemma lem7177387 {A : Type'} : term61 A.
Proof. exact (fun f : A -> real => @lem7177382 A f). Qed.
Lemma lem7177388 {A : Type'} : term60 A.
Proof. exact (EQ_MP (@lem7173735 A) (@lem7177387 A)). Qed.
Lemma lem7177389 {A : Type'} (f : A -> real) : term553 A f.
Proof. exact (@lem7177388 A f). Qed.
Lemma lem7177390 {A : Type'} (f : A -> real) : (term553 A f) = (term56 A f).
Proof. exact (eq_refl (term553 A f)). Qed.
Lemma lem7177391 {A : Type'} (f : A -> real) : term56 A f.
Proof. exact (EQ_MP (@lem7177390 A f) (@lem7177389 A f)). Qed.
Lemma lem7177392 {A : Type'} (f : A -> real) (u : A -> Prop) : term554 A f u.
Proof. exact (@lem7177391 A f u). Qed.
Lemma lem7177393 {A : Type'} (u : A -> Prop) (f : A -> real) : (term554 A f u) = (term52 A u f).
Proof. exact (eq_refl (term554 A f u)). Qed.
Lemma lem7177394 {A : Type'} (u : A -> Prop) (f : A -> real) : term52 A u f.
Proof. exact (EQ_MP (@lem7177393 A u f) (@lem7177392 A f u)). Qed.
Lemma lem7177395 {A : Type'} (u : A -> Prop) (f : A -> real) (v : A -> Prop) : term555 A u f v.
Proof. exact (@lem7177394 A u f v). Qed.
Lemma lem7177396 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term555 A u f v) = (term27 A v u f).
Proof. exact (eq_refl (term555 A u f v)). Qed.
Lemma lem7177397 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term27 A v u f.
Proof. exact (EQ_MP (@lem7177396 A v u f) (@lem7177395 A u f v)). Qed.
Lemma lem7177399 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term27 A v u f.
Proof. exact (@lem7173354 A v u f (@lem7177397 A v u f)). Qed.
Lemma lem7177400 {A : Type'} (u : A -> Prop) (f : A -> real) (v : A -> Prop) (h1 : @FINITE A v) : term46 A v u f.
Proof. exact (@lem7177399 A v u f (@lem7173322 A v h1)). Qed.
Lemma lem7177401 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) (h2 : @SUBSET A u v) : term43 A v u f.
Proof. exact (@lem7177400 A u f v h1 (@lem7173324 A u v h2)). Qed.
Lemma lem7177402 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : term40 A v u f.
Proof. exact (@lem7177401 A f u v h2 h3 (@lem7173323 A v u f h1)). Qed.
Lemma lem7177403 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : term23 A v u f) (h4 : @SUBSET A u v) : term37 A.
Proof. exact (@lem7177402 A f u v h1 h2 h4 (@lem7173332 A v u f h3)). Qed.
Lemma lem7177404 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : term23 A v u f) (h4 : @SUBSET A u v) : term34 A.
Proof. exact (@lem7177403 A f u v h1 h2 h3 h4 (@lem7173337 A)). Qed.
Lemma lem7177405 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : term23 A v u f) (h4 : @SUBSET A u v) : term31 A.
Proof. exact (@lem7177404 A f u v h1 h2 h3 h4 (@lem7173335 A)). Qed.
Lemma lem7177406 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : term23 A v u f) (h4 : @SUBSET A u v) : False.
Proof. exact (@lem7177405 A f u v h1 h2 h3 h4 (@lem7173333 A)). Qed.
Lemma lem7177407 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : term23 A v u f) (h4 : @SUBSET A u v) : (term23 A v u f) = False.
Proof. exact (prop_ext (fun h5 : term23 A v u f => @lem7177406 A f u v h1 h2 h3 h4) (fun h5 : False => @lem7173332 A v u f h3)). Qed.
Lemma lem7177408 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : term23 A v u f) (h4 : @SUBSET A u v) : False.
Proof. exact (EQ_MP (@lem7177407 A f u v h1 h2 h3 h4) (@lem7173332 A v u f h3)). Qed.
Lemma lem7177409 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : term22 A v u f.
Proof. exact (fun h0 : term23 A v u f => @lem7177408 A f u v h1 h2 h0 h3). Qed.
Lemma lem7177410 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : term14 A v u f.
Proof. exact (EQ_MP (@lem7173331 A v u f) (@lem7177409 A f u v h1 h2 h3)). Qed.
Lemma lem7177411 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : term15 A u v f.
Proof. exact (@lem7173327 A u v f (@lem7177410 A f u v h1 h2 h3)). Qed.
Lemma lem7177412 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term18 A v u f) : term19 A v u f.
Proof. exact (proj2 (@lem7173320 A v u f h1)). Qed.
Lemma lem7177413 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term18 A v u f) : @FINITE A v.
Proof. exact (proj1 (@lem7173320 A v u f h1)). Qed.
Lemma lem7177414 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term19 A v u f) : term20 A v u f.
Proof. exact (proj2 (@lem7173321 A v u f h1)). Qed.
Lemma lem7177415 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term19 A v u f) : @SUBSET A u v.
Proof. exact (proj1 (@lem7173321 A v u f h1)). Qed.
Lemma lem7177416 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : (term20 A v u f) = (term15 A u v f).
Proof. exact (prop_ext (fun h4 : term20 A v u f => @lem7177411 A f u v h1 h2 h3) (fun h4 : term15 A u v f => @lem7173323 A v u f h1)). Qed.
Lemma lem7177417 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : term15 A u v f.
Proof. exact (EQ_MP (@lem7177416 A f u v h1 h2 h3) (@lem7173323 A v u f h1)). Qed.
Lemma lem7177418 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : (@SUBSET A u v) = (term15 A u v f).
Proof. exact (prop_ext (fun h4 : @SUBSET A u v => @lem7177417 A f u v h1 h2 h3) (fun h4 : term15 A u v f => @lem7173324 A u v h3)). Qed.
Lemma lem7177419 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term20 A v u f) (h2 : @FINITE A v) (h3 : @SUBSET A u v) : term15 A u v f.
Proof. exact (EQ_MP (@lem7177418 A f u v h1 h2 h3) (@lem7173324 A u v h3)). Qed.
Lemma lem7177420 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) (h2 : term19 A v u f) (h3 : @SUBSET A u v) : (term20 A v u f) = (term15 A u v f).
Proof. exact (prop_ext (fun h4 : term20 A v u f => @lem7177419 A f u v h4 h1 h3) (fun h4 : term15 A u v f => @lem7177414 A v u f h2)). Qed.
Lemma lem7177421 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) (h2 : term19 A v u f) (h3 : @SUBSET A u v) : term15 A u v f.
Proof. exact (EQ_MP (@lem7177420 A f u v h1 h2 h3) (@lem7177414 A v u f h2)). Qed.
Lemma lem7177422 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A v) (h2 : term19 A v u f) : (@SUBSET A u v) = (term15 A u v f).
Proof. exact (prop_ext (fun h3 : @SUBSET A u v => @lem7177421 A f u v h1 h2 h3) (fun h3 : term15 A u v f => @lem7177415 A v u f h2)). Qed.
Lemma lem7177423 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A v) (h2 : term19 A v u f) : term15 A u v f.
Proof. exact (EQ_MP (@lem7177422 A v u f h1 h2) (@lem7177415 A v u f h2)). Qed.
Lemma lem7177424 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A v) (h2 : term19 A v u f) : (@FINITE A v) = (term15 A u v f).
Proof. exact (prop_ext (fun h3 : @FINITE A v => @lem7177423 A v u f h1 h2) (fun h3 : term15 A u v f => @lem7173322 A v h1)). Qed.
Lemma lem7177425 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A v) (h2 : term19 A v u f) : term15 A u v f.
Proof. exact (EQ_MP (@lem7177424 A v u f h1 h2) (@lem7173322 A v h1)). Qed.
Lemma lem7177426 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A v) (h2 : term18 A v u f) : (term19 A v u f) = (term15 A u v f).
Proof. exact (prop_ext (fun h3 : term19 A v u f => @lem7177425 A v u f h1 h3) (fun h3 : term15 A u v f => @lem7177412 A v u f h2)). Qed.
Lemma lem7177427 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A v) (h2 : term18 A v u f) : term15 A u v f.
Proof. exact (EQ_MP (@lem7177426 A v u f h1 h2) (@lem7177412 A v u f h2)). Qed.
Lemma lem7177428 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term18 A v u f) : (@FINITE A v) = (term15 A u v f).
Proof. exact (prop_ext (fun h2 : @FINITE A v => @lem7177427 A v u f h2 h1) (fun h2 : term15 A u v f => @lem7177413 A v u f h1)). Qed.
Lemma lem7177429 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term18 A v u f) : term15 A u v f.
Proof. exact (EQ_MP (@lem7177428 A v u f h1) (@lem7177413 A v u f h1)). Qed.
Lemma lem7177430 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term556 A u v f.
Proof. exact (fun h0 : term18 A v u f => @lem7177429 A v u f h0). Qed.
Lemma lem7177435 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term557 A u v.
Proof. exact (fun f : A -> real => @lem7177430 A u v f). Qed.
Lemma lem7177440 {A : Type'} (u : A -> Prop) : term558 A u.
Proof. exact (fun v : A -> Prop => @lem7177435 A u v). Qed.
Lemma lem7177445 {A : Type'} : term559 A.
Proof. exact (fun u : A -> Prop => @lem7177440 A u). Qed.
