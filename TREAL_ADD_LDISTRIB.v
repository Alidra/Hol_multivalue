Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_ADD_LDISTRIB_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_ADD_AC_spec.
Require Import PAIR_EQ_spec.
Require Import TREAL_EQ_AP_spec.
Require Import thm0_spec.
Require Import thm1321091_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import treal_add_spec.
Require Import treal_mul_spec.
Lemma lem1329300 (n : hreal) (m : hreal) (p : hreal) : term0 n m p.
Proof. exact (proj2 (@lem1322003 n m p)). Qed.
Lemma lem1329304 {A B : Type'} (x : A) : term1 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem1329305 {A B : Type'} (x : A) : (term1 A B x) = (term2 A B x).
Proof. exact (eq_refl (term1 A B x)). Qed.
Lemma lem1329306 {A B : Type'} (x : A) : term2 A B x.
Proof. exact (EQ_MP (@lem1329305 A B x) (@lem1329304 A B x)). Qed.
Lemma lem1329307 {A B : Type'} (x : A) (y : B) : term3 A B x y.
Proof. exact (@lem1329306 A B x y). Qed.
Lemma lem1329308 {A B : Type'} (x : A) (y : B) : (term3 A B x y) = (term4 A B x y).
Proof. exact (eq_refl (term3 A B x y)). Qed.
Lemma lem1329309 {A B : Type'} (x : A) (y : B) : term4 A B x y.
Proof. exact (EQ_MP (@lem1329308 A B x y) (@lem1329307 A B x y)). Qed.
Lemma lem1329310 {A B : Type'} (x : A) (y : B) (a : A) : term5 A B x y a.
Proof. exact (@lem1329309 A B x y a). Qed.
Lemma lem1329311 {A B : Type'} (x : A) (a : A) (y : B) : (term5 A B x y a) = (term6 A B x a y).
Proof. exact (eq_refl (term5 A B x y a)). Qed.
Lemma lem1329312 {A B : Type'} (x : A) (a : A) (y : B) : term6 A B x a y.
Proof. exact (EQ_MP (@lem1329311 A B x a y) (@lem1329310 A B x y a)). Qed.
Lemma lem1329313 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term7 A B x a y b.
Proof. exact (@lem1329312 A B x a y b). Qed.
Lemma lem1329314 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term7 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term8 A B x a y b)).
Proof. exact (eq_refl (term7 A B x a y b)). Qed.
Lemma lem1329316 (x : hreal) : term9 x.
Proof. exact (@lem1321091 x). Qed.
Lemma lem1329317 (x : hreal) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1329318 (x : hreal) : term10 x.
Proof. exact (EQ_MP (@lem1329317 x) (@lem1329316 x)). Qed.
Lemma lem1329319 (x : hreal) (y : hreal) : term11 x y.
Proof. exact (@lem1329318 x y). Qed.
Lemma lem1329320 (y : hreal) (x : hreal) : (term11 x y) = (term12 y x).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1329321 (y : hreal) (x : hreal) : term12 y x.
Proof. exact (EQ_MP (@lem1329320 y x) (@lem1329319 x y)). Qed.
Lemma lem1329322 (y : hreal) (x : hreal) (z : hreal) : term13 y x z.
Proof. exact (@lem1329321 y x z). Qed.
Lemma lem1329323 (y : hreal) (x : hreal) (z : hreal) : (term13 y x z) = ((term14 x y z) = (term15 y x z)).
Proof. exact (eq_refl (term13 y x z)). Qed.
Lemma lem1329325 (x1 : hreal) : term16 x1.
Proof. exact (@lem1323802 x1). Qed.
Lemma lem1329326 (x1 : hreal) : (term16 x1) = (term17 x1).
Proof. exact (eq_refl (term16 x1)). Qed.
Lemma lem1329327 (x1 : hreal) : term17 x1.
Proof. exact (EQ_MP (@lem1329326 x1) (@lem1329325 x1)). Qed.
Lemma lem1329328 (x1 : hreal) (x2 : hreal) : term18 x1 x2.
Proof. exact (@lem1329327 x1 x2). Qed.
Lemma lem1329329 (x1 : hreal) (x2 : hreal) : (term18 x1 x2) = (term19 x1 x2).
Proof. exact (eq_refl (term18 x1 x2)). Qed.
Lemma lem1329330 (x1 : hreal) (x2 : hreal) : term19 x1 x2.
Proof. exact (EQ_MP (@lem1329329 x1 x2) (@lem1329328 x1 x2)). Qed.
Lemma lem1329331 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term20 x1 x2 y1.
Proof. exact (@lem1329330 x1 x2 y1). Qed.
Lemma lem1329332 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term20 x1 x2 y1) = (term21 x1 x2 y1).
Proof. exact (eq_refl (term20 x1 x2 y1)). Qed.
Lemma lem1329333 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term21 x1 x2 y1.
Proof. exact (EQ_MP (@lem1329332 x1 x2 y1) (@lem1329331 x1 x2 y1)). Qed.
Lemma lem1329334 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : term22 x1 x2 y1 y2.
Proof. exact (@lem1329333 x1 x2 y1 y2). Qed.
Lemma lem1329335 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term22 x1 x2 y1 y2) = ((term23 x1 y1 x2 y2) = (term24 x1 x2 y1 y2)).
Proof. exact (eq_refl (term22 x1 x2 y1 y2)). Qed.
Lemma lem1329337 (x1 : hreal) : term25 x1.
Proof. exact (@lem1324372 x1). Qed.
Lemma lem1329338 (x1 : hreal) : (term25 x1) = (term26 x1).
Proof. exact (eq_refl (term25 x1)). Qed.
Lemma lem1329339 (x1 : hreal) : term26 x1.
Proof. exact (EQ_MP (@lem1329338 x1) (@lem1329337 x1)). Qed.
Lemma lem1329340 (x1 : hreal) (y2 : hreal) : term27 x1 y2.
Proof. exact (@lem1329339 x1 y2). Qed.
Lemma lem1329341 (x1 : hreal) (y2 : hreal) : (term27 x1 y2) = (term28 x1 y2).
Proof. exact (eq_refl (term27 x1 y2)). Qed.
Lemma lem1329342 (x1 : hreal) (y2 : hreal) : term28 x1 y2.
Proof. exact (EQ_MP (@lem1329341 x1 y2) (@lem1329340 x1 y2)). Qed.
Lemma lem1329343 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term29 x1 y2 y1.
Proof. exact (@lem1329342 x1 y2 y1). Qed.
Lemma lem1329344 (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term29 x1 y2 y1) = (term30 x1 y2 y1).
Proof. exact (eq_refl (term29 x1 y2 y1)). Qed.
Lemma lem1329345 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term30 x1 y2 y1.
Proof. exact (EQ_MP (@lem1329344 x1 y2 y1) (@lem1329343 x1 y2 y1)). Qed.
Lemma lem1329346 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : term31 x1 y2 y1 x2.
Proof. exact (@lem1329345 x1 y2 y1 x2). Qed.
Lemma lem1329347 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term31 x1 y2 y1 x2) = ((term32 x1 y1 x2 y2) = (term33 x1 y2 y1 x2)).
Proof. exact (eq_refl (term31 x1 y2 y1 x2)). Qed.
Lemma lem1329349 (x : prod hreal hreal) : term34 x.
Proof. exact (@lem1326851 x). Qed.
Lemma lem1329350 (x : prod hreal hreal) : (term34 x) = (term35 x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem1329351 (x : prod hreal hreal) : term35 x.
Proof. exact (EQ_MP (@lem1329350 x) (@lem1329349 x)). Qed.
Lemma lem1329352 (x : prod hreal hreal) (y : prod hreal hreal) : term36 x y.
Proof. exact (@lem1329351 x y). Qed.
Lemma lem1329353 (x : prod hreal hreal) (y : prod hreal hreal) : (term36 x y) = (term37 x y).
Proof. exact (eq_refl (term36 x y)). Qed.
Lemma lem1329354 (x : prod hreal hreal) (y : prod hreal hreal) : term37 x y.
Proof. exact (EQ_MP (@lem1329353 x y) (@lem1329352 x y)). Qed.
Lemma lem1329355 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1329356 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : treal_eq x y.
Proof. exact (@lem1329354 x y (@lem1329355 x y h1)). Qed.
Lemma lem1329357 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((treal_eq x y) = True).
Proof. exact (@lem7 (treal_eq x y)). Qed.
Lemma lem1329358 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : (treal_eq x y) = True.
Proof. exact (EQ_MP (@lem1329357 x y) (@lem1329356 x y h1)). Qed.
Lemma lem1329364 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term38 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1329365 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term38 _5106 _5107 P) = ((term39 _5106 _5107 P) = (term40 _5106 _5107 P)).
Proof. exact (eq_refl (term38 _5106 _5107 P)). Qed.
Lemma lem1329372 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term39 _5106 _5107 P) = (term40 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1329365 _5106 _5107 P) (@lem1329364 _5106 _5107 P)). Qed.
Lemma lem1329373 (P : type1233) : (term41 P) = (term42 P).
Proof. exact (@lem1329372 hreal hreal P). Qed.
Lemma lem1329374 : term43 = term44.
Proof. exact (@lem1329373 term45). Qed.
Lemma lem1329375 (x : prod hreal hreal) : (term46 x) = (term47 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1329376 : term48 = term45.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1329375 x)). Qed.
Lemma lem1329377 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1329378 : term43 = term49.
Proof. exact (MK_COMB (@lem1329377) (@lem1329376)). Qed.
Lemma lem1329379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1329380 : term50 = term51.
Proof. exact (MK_COMB (@lem1329379) (@lem1329378)). Qed.
Lemma lem1329381 (p1 : hreal) (p2 : hreal) : (term52 p1 p2) = (term53 p1 p2).
Proof. exact (eq_refl (term52 p1 p2)). Qed.
Lemma lem1329382 (p1 : hreal) : (term54 p1) = (term55 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1329381 p1 p2)). Qed.
Lemma lem1329383 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329384 (p1 : hreal) : (term56 p1) = (term57 p1).
Proof. exact (MK_COMB (@lem1329383) (@lem1329382 p1)). Qed.
Lemma lem1329385 : term58 = term59.
Proof. exact (fun_ext (fun p1 : hreal => @lem1329384 p1)). Qed.
Lemma lem1329386 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329387 : term44 = term60.
Proof. exact (MK_COMB (@lem1329386) (@lem1329385)). Qed.
Lemma lem1329388 : (term43 = term44) = (term49 = term60).
Proof. exact (MK_COMB (@lem1329380) (@lem1329387)). Qed.
Lemma lem1329389 : term49 = term60.
Proof. exact (EQ_MP (@lem1329388) (@lem1329374)). Qed.
Lemma lem1329407 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term39 _5106 _5107 P) = (term40 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1329365 _5106 _5107 P) (@lem1329364 _5106 _5107 P)). Qed.
Lemma lem1329408 (P : type1233) : (term41 P) = (term42 P).
Proof. exact (@lem1329407 hreal hreal P). Qed.
Lemma lem1329409 (p1 : hreal) (p2 : hreal) : (term61 p1 p2) = (term62 p1 p2).
Proof. exact (@lem1329408 (term63 p1 p2)). Qed.
Lemma lem1329410 (y : prod hreal hreal) (p1 : hreal) (p2 : hreal) : (term64 p1 p2 y) = (term65 y p1 p2).
Proof. exact (eq_refl (term64 p1 p2 y)). Qed.
Lemma lem1329411 (p1 : hreal) (p2 : hreal) : (term66 p1 p2) = (term63 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1329410 y p1 p2)). Qed.
Lemma lem1329412 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1329413 (p1 : hreal) (p2 : hreal) : (term61 p1 p2) = (term53 p1 p2).
Proof. exact (MK_COMB (@lem1329412) (@lem1329411 p1 p2)). Qed.
Lemma lem1329414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1329415 (p1 : hreal) (p2 : hreal) : (term67 p1 p2) = (term68 p1 p2).
Proof. exact (MK_COMB (@lem1329414) (@lem1329413 p1 p2)). Qed.
Lemma lem1329416 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term69 p1 p2 p1' p2') = (term70 p1' p2' p1 p2).
Proof. exact (eq_refl (term69 p1 p2 p1' p2')). Qed.
Lemma lem1329417 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term71 p1 p2 p1') = (term72 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1329416 p1' p2' p1 p2)). Qed.
Lemma lem1329418 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329419 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term73 p1 p2 p1') = (term74 p1' p1 p2).
Proof. exact (MK_COMB (@lem1329418) (@lem1329417 p1' p1 p2)). Qed.
Lemma lem1329420 (p1 : hreal) (p2 : hreal) : (term75 p1 p2) = (term76 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1329419 p1' p1 p2)). Qed.
Lemma lem1329421 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329422 (p1 : hreal) (p2 : hreal) : (term62 p1 p2) = (term77 p1 p2).
Proof. exact (MK_COMB (@lem1329421) (@lem1329420 p1 p2)). Qed.
Lemma lem1329423 (p1 : hreal) (p2 : hreal) : ((term61 p1 p2) = (term62 p1 p2)) = ((term53 p1 p2) = (term77 p1 p2)).
Proof. exact (MK_COMB (@lem1329415 p1 p2) (@lem1329422 p1 p2)). Qed.
Lemma lem1329424 (p1 : hreal) (p2 : hreal) : (term53 p1 p2) = (term77 p1 p2).
Proof. exact (EQ_MP (@lem1329423 p1 p2) (@lem1329409 p1 p2)). Qed.
Lemma lem1329442 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term39 _5106 _5107 P) = (term40 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1329365 _5106 _5107 P) (@lem1329364 _5106 _5107 P)). Qed.
Lemma lem1329443 (P : type1233) : (term41 P) = (term42 P).
Proof. exact (@lem1329442 hreal hreal P). Qed.
Lemma lem1329444 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term78 p1' p2' p1 p2) = (term79 p1' p2' p1 p2).
Proof. exact (@lem1329443 (term80 p1' p2' p1 p2)). Qed.
Lemma lem1329445 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (z : prod hreal hreal) : (term81 p1' p2' p1 p2 z) = (term82 p1' p2' p1 p2 z).
Proof. exact (eq_refl (term81 p1' p2' p1 p2 z)). Qed.
Lemma lem1329446 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term83 p1' p2' p1 p2) = (term80 p1' p2' p1 p2).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1329445 p1' p2' p1 p2 z)). Qed.
Lemma lem1329447 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1329448 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term78 p1' p2' p1 p2) = (term70 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1329447) (@lem1329446 p1' p2' p1 p2)). Qed.
Lemma lem1329449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1329450 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term84 p1' p2' p1 p2) = (term85 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1329449) (@lem1329448 p1' p2' p1 p2)). Qed.
Lemma lem1329451 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2'' : hreal) : (term86 p1' p2' p1 p2 p1'' p2'') = (term87 p1' p2' p1 p2 p1'' p2'').
Proof. exact (eq_refl (term86 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1329452 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term88 p1' p2' p1 p2 p1'') = (term89 p1' p2' p1 p2 p1'').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1329451 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1329453 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329454 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term90 p1' p2' p1 p2 p1'') = (term91 p1' p2' p1 p2 p1'').
Proof. exact (MK_COMB (@lem1329453) (@lem1329452 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1329455 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term92 p1' p2' p1 p2) = (term93 p1' p2' p1 p2).
Proof. exact (fun_ext (fun p1'' : hreal => @lem1329454 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1329456 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329457 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term79 p1' p2' p1 p2) = (term94 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1329456) (@lem1329455 p1' p2' p1 p2)). Qed.
Lemma lem1329458 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : ((term78 p1' p2' p1 p2) = (term79 p1' p2' p1 p2)) = ((term70 p1' p2' p1 p2) = (term94 p1' p2' p1 p2)).
Proof. exact (MK_COMB (@lem1329450 p1' p2' p1 p2) (@lem1329457 p1' p2' p1 p2)). Qed.
Lemma lem1329459 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term70 p1' p2' p1 p2) = (term94 p1' p2' p1 p2).
Proof. exact (EQ_MP (@lem1329458 p1' p2' p1 p2) (@lem1329444 p1' p2' p1 p2)). Qed.
Lemma lem1329473 (x : prod hreal hreal) (y : prod hreal hreal) : term95 x y.
Proof. exact (fun h0 : x = y => @lem1329358 x y h0). Qed.
Lemma lem1329474 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2'' : hreal) : term96 p1' p2' p1 p2 p1'' p2''.
Proof. exact (@lem1329473 (term97 p1 p2 p1' p2' p1'' p2'') (term98 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1329478 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term23 x1 y1 x2 y2) = (term24 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1329335 x1 x2 y1 y2) (@lem1329334 x1 x2 y1 y2)). Qed.
Lemma lem1329479 (p1' : hreal) (p1'' : hreal) (p2' : hreal) (p2'' : hreal) : (term23 p1' p2' p1'' p2'') = (term24 p1' p1'' p2' p2'').
Proof. exact (@lem1329478 p1' p1'' p2' p2''). Qed.
Lemma lem1329486 (p1 : hreal) (p2 : hreal) : (term99 p1 p2) = (term99 p1 p2).
Proof. exact (eq_refl (term99 p1 p2)). Qed.
Lemma lem1329487 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) (p2' : hreal) (p2'' : hreal) : (term97 p1 p2 p1' p2' p1'' p2'') = (term100 p1 p2 p1' p1'' p2' p2'').
Proof. exact (MK_COMB (@lem1329486 p1 p2) (@lem1329479 p1' p1'' p2' p2'')). Qed.
Lemma lem1329489 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term32 x1 y1 x2 y2) = (term33 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1329347 x1 y2 y1 x2) (@lem1329346 x1 y2 y1 x2)). Qed.
Lemma lem1329490 (p1 : hreal) (p2' : hreal) (p2'' : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term100 p1 p2 p1' p1'' p2' p2'') = (term101 p1 p2' p2'' p2 p1' p1'').
Proof. exact (@lem1329489 p1 (hreal_add p2' p2'') p2 (hreal_add p1' p1'')). Qed.
Lemma lem1329495 (y : hreal) (x : hreal) (z : hreal) : (term14 x y z) = (term15 y x z).
Proof. exact (EQ_MP (@lem1329323 y x z) (@lem1329322 y x z)). Qed.
Lemma lem1329496 (p1' : hreal) (p1 : hreal) (p1'' : hreal) : (term14 p1 p1' p1'') = (term15 p1' p1 p1'').
Proof. exact (@lem1329495 p1' p1 p1''). Qed.
Lemma lem1329500 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1329501 (p1' : hreal) (p1 : hreal) (p1'' : hreal) : (term102 p1 p1' p1'') = (term103 p1' p1 p1'').
Proof. exact (MK_COMB (@lem1329500) (@lem1329496 p1' p1 p1'')). Qed.
Lemma lem1329506 (y : hreal) (x : hreal) (z : hreal) : (term14 x y z) = (term15 y x z).
Proof. exact (EQ_MP (@lem1329323 y x z) (@lem1329322 y x z)). Qed.
Lemma lem1329507 (p2' : hreal) (p2 : hreal) (p2'' : hreal) : (term14 p2 p2' p2'') = (term15 p2' p2 p2'').
Proof. exact (@lem1329506 p2' p2 p2''). Qed.
Lemma lem1329511 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2 : hreal) (p2'' : hreal) : (term104 p1 p1' p1'' p2 p2' p2'') = (term105 p1' p1 p1'' p2' p2 p2'').
Proof. exact (MK_COMB (@lem1329501 p1' p1 p1'') (@lem1329507 p2' p2 p2'')). Qed.
Lemma lem1329513 (m : hreal) (n : hreal) (p : hreal) : (term106 m n p) = (term107 m n p).
Proof. exact (proj1 (@lem1329300 n m p)). Qed.
Lemma lem1329514 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2 : hreal) (p2'' : hreal) : (term105 p1' p1 p1'' p2' p2 p2'') = (term108 p1' p1 p1'' p2' p2 p2'').
Proof. exact (@lem1329513 (hreal_mul p1 p1') (hreal_mul p1 p1'') (term15 p2' p2 p2'')). Qed.
Lemma lem1329530 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2 : hreal) (p2'' : hreal) : (term104 p1 p1' p1'' p2 p2' p2'') = (term108 p1' p1 p1'' p2' p2 p2'').
Proof. exact (TRANS (@lem1329511 p1' p1 p1'' p2' p2 p2'') (@lem1329514 p1' p1 p1'' p2' p2 p2'')). Qed.
Lemma lem1329531 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1329532 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2 : hreal) (p2'' : hreal) : (term109 p1 p1' p1'' p2 p2' p2'') = (term110 p1' p1 p1'' p2' p2 p2'').
Proof. exact (MK_COMB (@lem1329531) (@lem1329530 p1' p1 p1'' p2' p2 p2'')). Qed.
Lemma lem1329552 (y : hreal) (x : hreal) (z : hreal) : (term14 x y z) = (term15 y x z).
Proof. exact (EQ_MP (@lem1329323 y x z) (@lem1329322 y x z)). Qed.
Lemma lem1329553 (p2' : hreal) (p1 : hreal) (p2'' : hreal) : (term14 p1 p2' p2'') = (term15 p2' p1 p2'').
Proof. exact (@lem1329552 p2' p1 p2''). Qed.
Lemma lem1329557 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1329558 (p2' : hreal) (p1 : hreal) (p2'' : hreal) : (term102 p1 p2' p2'') = (term103 p2' p1 p2'').
Proof. exact (MK_COMB (@lem1329557) (@lem1329553 p2' p1 p2'')). Qed.
Lemma lem1329563 (y : hreal) (x : hreal) (z : hreal) : (term14 x y z) = (term15 y x z).
Proof. exact (EQ_MP (@lem1329323 y x z) (@lem1329322 y x z)). Qed.
Lemma lem1329564 (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term14 p2 p1' p1'') = (term15 p1' p2 p1'').
Proof. exact (@lem1329563 p1' p2 p1''). Qed.
Lemma lem1329568 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term104 p1 p2' p2'' p2 p1' p1'') = (term105 p2' p1 p2'' p1' p2 p1'').
Proof. exact (MK_COMB (@lem1329558 p2' p1 p2'') (@lem1329564 p1' p2 p1'')). Qed.
Lemma lem1329570 (m : hreal) (n : hreal) (p : hreal) : (term106 m n p) = (term107 m n p).
Proof. exact (proj1 (@lem1329300 n m p)). Qed.
Lemma lem1329571 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term105 p2' p1 p2'' p1' p2 p1'') = (term108 p2' p1 p2'' p1' p2 p1'').
Proof. exact (@lem1329570 (hreal_mul p1 p2') (hreal_mul p1 p2'') (term15 p1' p2 p1'')). Qed.
Lemma lem1329587 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term104 p1 p2' p2'' p2 p1' p1'') = (term108 p2' p1 p2'' p1' p2 p1'').
Proof. exact (TRANS (@lem1329568 p2' p1 p2'' p1' p2 p1'') (@lem1329571 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329588 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term101 p1 p2' p2'' p2 p1' p1'') = (term111 p2' p1 p2'' p1' p2 p1'').
Proof. exact (MK_COMB (@lem1329532 p1' p1 p1'' p2' p2 p2'') (@lem1329587 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329619 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term100 p1 p2 p1' p1'' p2' p2'') = (term111 p2' p1 p2'' p1' p2 p1'').
Proof. exact (TRANS (@lem1329490 p1 p2' p2'' p2 p1' p1'') (@lem1329588 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329620 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term97 p1 p2 p1' p2' p1'' p2'') = (term111 p2' p1 p2'' p1' p2 p1'').
Proof. exact (TRANS (@lem1329487 p1 p2 p1' p1'' p2' p2'') (@lem1329619 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329621 : (@eq (prod hreal hreal)) = (@eq (prod hreal hreal)).
Proof. exact (eq_refl (@eq (prod hreal hreal))). Qed.
Lemma lem1329622 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term112 p1 p2 p1' p2' p1'' p2'') = (term113 p2' p1 p2'' p1' p2 p1'').
Proof. exact (MK_COMB (@lem1329621) (@lem1329620 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329654 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term32 x1 y1 x2 y2) = (term33 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1329347 x1 y2 y1 x2) (@lem1329346 x1 y2 y1 x2)). Qed.
Lemma lem1329655 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) : (term32 p1 p2 p1' p2') = (term33 p1 p2' p2 p1').
Proof. exact (@lem1329654 p1 p2' p2 p1'). Qed.
Lemma lem1329662 : treal_add = treal_add.
Proof. exact (eq_refl treal_add). Qed.
Lemma lem1329663 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) : (term114 p1 p2 p1' p2') = (term115 p1 p2' p2 p1').
Proof. exact (MK_COMB (@lem1329662) (@lem1329655 p1 p2' p2 p1')). Qed.
Lemma lem1329671 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term32 x1 y1 x2 y2) = (term33 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1329347 x1 y2 y1 x2) (@lem1329346 x1 y2 y1 x2)). Qed.
Lemma lem1329672 (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : (term32 p1 p2 p1'' p2'') = (term33 p1 p2'' p2 p1'').
Proof. exact (@lem1329671 p1 p2'' p2 p1''). Qed.
Lemma lem1329679 (p2' : hreal) (p1' : hreal) (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : (term98 p1' p2' p1 p2 p1'' p2'') = (term116 p2' p1' p1 p2'' p2 p1'').
Proof. exact (MK_COMB (@lem1329663 p1 p2' p2 p1') (@lem1329672 p1 p2'' p2 p1'')). Qed.
Lemma lem1329681 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term23 x1 y1 x2 y2) = (term24 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1329335 x1 x2 y1 y2) (@lem1329334 x1 x2 y1 y2)). Qed.
Lemma lem1329682 (p2' : hreal) (p1' : hreal) (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : (term116 p2' p1' p1 p2'' p2 p1'') = (term117 p2' p1' p1 p2'' p2 p1'').
Proof. exact (@lem1329681 (term118 p1 p1' p2 p2') (term118 p1 p1'' p2 p2'') (term118 p1 p2' p2 p1') (term118 p1 p2'' p2 p1'')). Qed.
Lemma lem1329684 (m : hreal) (n : hreal) (p : hreal) : (term106 m n p) = (term107 m n p).
Proof. exact (proj1 (@lem1329300 n m p)). Qed.
Lemma lem1329685 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2'' : hreal) : (term119 p1' p2' p1 p1'' p2 p2'') = (term120 p1' p2' p1 p1'' p2 p2'').
Proof. exact (@lem1329684 (hreal_mul p1 p1') (hreal_mul p2 p2') (term118 p1 p1'' p2 p2'')). Qed.
Lemma lem1329693 (n : hreal) (m : hreal) (p : hreal) : (term107 m n p) = (term107 n m p).
Proof. exact (proj2 (@lem1329300 n m p)). Qed.
Lemma lem1329694 (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2 : hreal) (p2'' : hreal) : (term121 p2' p1 p1'' p2 p2'') = (term122 p1 p1'' p2' p2 p2'').
Proof. exact (@lem1329693 (hreal_mul p1 p1'') (hreal_mul p2 p2') (hreal_mul p2 p2'')). Qed.
Lemma lem1329704 (p1 : hreal) (p1' : hreal) : (term123 p1 p1') = (term123 p1 p1').
Proof. exact (eq_refl (term123 p1 p1')). Qed.
Lemma lem1329705 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2 : hreal) (p2'' : hreal) : (term120 p1' p2' p1 p1'' p2 p2'') = (term108 p1' p1 p1'' p2' p2 p2'').
Proof. exact (MK_COMB (@lem1329704 p1 p1') (@lem1329694 p1 p1'' p2' p2 p2'')). Qed.
Lemma lem1329721 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2 : hreal) (p2'' : hreal) : (term119 p1' p2' p1 p1'' p2 p2'') = (term108 p1' p1 p1'' p2' p2 p2'').
Proof. exact (TRANS (@lem1329685 p1' p2' p1 p1'' p2 p2'') (@lem1329705 p1' p1 p1'' p2' p2 p2'')). Qed.
Lemma lem1329722 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1329723 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2 : hreal) (p2'' : hreal) : (term124 p1' p2' p1 p1'' p2 p2'') = (term110 p1' p1 p1'' p2' p2 p2'').
Proof. exact (MK_COMB (@lem1329722) (@lem1329721 p1' p1 p1'' p2' p2 p2'')). Qed.
Lemma lem1329740 (m : hreal) (n : hreal) (p : hreal) : (term106 m n p) = (term107 m n p).
Proof. exact (proj1 (@lem1329300 n m p)). Qed.
Lemma lem1329741 (p2' : hreal) (p1' : hreal) (p1 : hreal) (p2'' : hreal) (p2 : hreal) (p1'' : hreal) : (term119 p2' p1' p1 p2'' p2 p1'') = (term120 p2' p1' p1 p2'' p2 p1'').
Proof. exact (@lem1329740 (hreal_mul p1 p2') (hreal_mul p2 p1') (term118 p1 p2'' p2 p1'')). Qed.
Lemma lem1329749 (n : hreal) (m : hreal) (p : hreal) : (term107 m n p) = (term107 n m p).
Proof. exact (proj2 (@lem1329300 n m p)). Qed.
Lemma lem1329750 (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term121 p1' p1 p2'' p2 p1'') = (term122 p1 p2'' p1' p2 p1'').
Proof. exact (@lem1329749 (hreal_mul p1 p2'') (hreal_mul p2 p1') (hreal_mul p2 p1'')). Qed.
Lemma lem1329760 (p1 : hreal) (p2' : hreal) : (term123 p1 p2') = (term123 p1 p2').
Proof. exact (eq_refl (term123 p1 p2')). Qed.
Lemma lem1329761 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term120 p2' p1' p1 p2'' p2 p1'') = (term108 p2' p1 p2'' p1' p2 p1'').
Proof. exact (MK_COMB (@lem1329760 p1 p2') (@lem1329750 p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329777 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term119 p2' p1' p1 p2'' p2 p1'') = (term108 p2' p1 p2'' p1' p2 p1'').
Proof. exact (TRANS (@lem1329741 p2' p1' p1 p2'' p2 p1'') (@lem1329761 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329778 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term117 p2' p1' p1 p2'' p2 p1'') = (term111 p2' p1 p2'' p1' p2 p1'').
Proof. exact (MK_COMB (@lem1329723 p1' p1 p1'' p2' p2 p2'') (@lem1329777 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329809 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term116 p2' p1' p1 p2'' p2 p1'') = (term111 p2' p1 p2'' p1' p2 p1'').
Proof. exact (TRANS (@lem1329682 p2' p1' p1 p2'' p2 p1'') (@lem1329778 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329810 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term98 p1' p2' p1 p2 p1'' p2'') = (term111 p2' p1 p2'' p1' p2 p1'').
Proof. exact (TRANS (@lem1329679 p2' p1' p1 p2'' p2 p1'') (@lem1329809 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329811 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : ((term97 p1 p2 p1' p2' p1'' p2'') = (term98 p1' p2' p1 p2 p1'' p2'')) = ((term111 p2' p1 p2'' p1' p2 p1'') = (term111 p2' p1 p2'' p1' p2 p1'')).
Proof. exact (MK_COMB (@lem1329622 p2' p1 p2'' p1' p2 p1'') (@lem1329810 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329813 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term8 A B x a y b).
Proof. exact (EQ_MP (@lem1329314 A B x a y b) (@lem1329313 A B x a y b)). Qed.
Lemma lem1329814 (x : hreal) (a : hreal) (y : hreal) (b : hreal) : ((@pair hreal hreal x y) = (@pair hreal hreal a b)) = (term125 x a y b).
Proof. exact (@lem1329813 hreal hreal x a y b). Qed.
Lemma lem1329815 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : ((term111 p2' p1 p2'' p1' p2 p1'') = (term111 p2' p1 p2'' p1' p2 p1'')) = (term126 p2' p1 p2'' p1' p2 p1'').
Proof. exact (@lem1329814 (term108 p1' p1 p1'' p2' p2 p2'') (term108 p1' p1 p1'' p2' p2 p2'') (term108 p2' p1 p2'' p1' p2 p1'') (term108 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329819 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1329820 (x : hreal) : (x = x) = True.
Proof. exact (@lem1329819 hreal x). Qed.
Lemma lem1329821 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2 : hreal) (p2'' : hreal) : ((term108 p1' p1 p1'' p2' p2 p2'') = (term108 p1' p1 p1'' p2' p2 p2'')) = True.
Proof. exact (@lem1329820 (term108 p1' p1 p1'' p2' p2 p2'')). Qed.
Lemma lem1329822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1329823 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2 : hreal) (p2'' : hreal) : (term127 p1' p1 p1'' p2' p2 p2'') = (and True).
Proof. exact (MK_COMB (@lem1329822) (@lem1329821 p1' p1 p1'' p2' p2 p2'')). Qed.
Lemma lem1329825 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1329826 (x : hreal) : (x = x) = True.
Proof. exact (@lem1329825 hreal x). Qed.
Lemma lem1329827 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : ((term108 p2' p1 p2'' p1' p2 p1'') = (term108 p2' p1 p2'' p1' p2 p1'')) = True.
Proof. exact (@lem1329826 (term108 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329828 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term126 p2' p1 p2'' p1' p2 p1'') = (True /\ True).
Proof. exact (MK_COMB (@lem1329823 p1' p1 p1'' p2' p2 p2'') (@lem1329827 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329830 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1329831 : (True /\ True) = True.
Proof. exact (@lem1329830 True). Qed.
Lemma lem1329832 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : (term126 p2' p1 p2'' p1' p2 p1'') = True.
Proof. exact (TRANS (@lem1329828 p2' p1 p2'' p1' p2 p1'') (@lem1329831)). Qed.
Lemma lem1329833 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) : ((term111 p2' p1 p2'' p1' p2 p1'') = (term111 p2' p1 p2'' p1' p2 p1'')) = True.
Proof. exact (TRANS (@lem1329815 p2' p1 p2'' p1' p2 p1'') (@lem1329832 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329834 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2'' : hreal) : ((term97 p1 p2 p1' p2' p1'' p2'') = (term98 p1' p2' p1 p2 p1'' p2'')) = True.
Proof. exact (TRANS (@lem1329811 p2' p1 p2'' p1' p2 p1'') (@lem1329833 p2' p1 p2'' p1' p2 p1'')). Qed.
Lemma lem1329835 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2'' : hreal) : True = ((term97 p1 p2 p1' p2' p1'' p2'') = (term98 p1' p2' p1 p2 p1'' p2'')).
Proof. exact (SYM (@lem1329834 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1329836 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2'' : hreal) : (term97 p1 p2 p1' p2' p1'' p2'') = (term98 p1' p2' p1 p2 p1'' p2'').
Proof. exact (EQ_MP (@lem1329835 p1' p2' p1 p2 p1'' p2'') (@lem0)). Qed.
Lemma lem1329837 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2'' : hreal) : (term87 p1' p2' p1 p2 p1'' p2'') = True.
Proof. exact (@lem1329474 p1' p2' p1 p2 p1'' p2'' (@lem1329836 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1329838 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term89 p1' p2' p1 p2 p1'') = term128.
Proof. exact (fun_ext (fun p2'' : hreal => @lem1329837 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1329839 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329840 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term91 p1' p2' p1 p2 p1'') = term129.
Proof. exact (MK_COMB (@lem1329839) (@lem1329838 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1329842 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329843 (t : Prop) : (term131 t) = t.
Proof. exact (@lem1329842 hreal t). Qed.
Lemma lem1329844 : term129 = True.
Proof. exact (@lem1329843 True). Qed.
Lemma lem1329845 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term91 p1' p2' p1 p2 p1'') = True.
Proof. exact (TRANS (@lem1329840 p1' p2' p1 p2 p1'') (@lem1329844)). Qed.
Lemma lem1329846 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term93 p1' p2' p1 p2) = term128.
Proof. exact (fun_ext (fun p1'' : hreal => @lem1329845 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1329847 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329848 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term94 p1' p2' p1 p2) = term129.
Proof. exact (MK_COMB (@lem1329847) (@lem1329846 p1' p2' p1 p2)). Qed.
Lemma lem1329850 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329851 (t : Prop) : (term131 t) = t.
Proof. exact (@lem1329850 hreal t). Qed.
Lemma lem1329852 : term129 = True.
Proof. exact (@lem1329851 True). Qed.
Lemma lem1329853 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term94 p1' p2' p1 p2) = True.
Proof. exact (TRANS (@lem1329848 p1' p2' p1 p2) (@lem1329852)). Qed.
Lemma lem1329854 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term70 p1' p2' p1 p2) = True.
Proof. exact (TRANS (@lem1329459 p1' p2' p1 p2) (@lem1329853 p1' p2' p1 p2)). Qed.
Lemma lem1329855 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term72 p1' p1 p2) = term128.
Proof. exact (fun_ext (fun p2' : hreal => @lem1329854 p1' p2' p1 p2)). Qed.
Lemma lem1329856 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329857 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term74 p1' p1 p2) = term129.
Proof. exact (MK_COMB (@lem1329856) (@lem1329855 p1' p1 p2)). Qed.
Lemma lem1329859 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329860 (t : Prop) : (term131 t) = t.
Proof. exact (@lem1329859 hreal t). Qed.
Lemma lem1329861 : term129 = True.
Proof. exact (@lem1329860 True). Qed.
Lemma lem1329862 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term74 p1' p1 p2) = True.
Proof. exact (TRANS (@lem1329857 p1' p1 p2) (@lem1329861)). Qed.
Lemma lem1329863 (p1 : hreal) (p2 : hreal) : (term76 p1 p2) = term128.
Proof. exact (fun_ext (fun p1' : hreal => @lem1329862 p1' p1 p2)). Qed.
Lemma lem1329864 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329865 (p1 : hreal) (p2 : hreal) : (term77 p1 p2) = term129.
Proof. exact (MK_COMB (@lem1329864) (@lem1329863 p1 p2)). Qed.
Lemma lem1329867 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329868 (t : Prop) : (term131 t) = t.
Proof. exact (@lem1329867 hreal t). Qed.
Lemma lem1329869 : term129 = True.
Proof. exact (@lem1329868 True). Qed.
Lemma lem1329870 (p1 : hreal) (p2 : hreal) : (term77 p1 p2) = True.
Proof. exact (TRANS (@lem1329865 p1 p2) (@lem1329869)). Qed.
Lemma lem1329871 (p1 : hreal) (p2 : hreal) : (term53 p1 p2) = True.
Proof. exact (TRANS (@lem1329424 p1 p2) (@lem1329870 p1 p2)). Qed.
Lemma lem1329872 (p1 : hreal) : (term55 p1) = term128.
Proof. exact (fun_ext (fun p2 : hreal => @lem1329871 p1 p2)). Qed.
Lemma lem1329873 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329874 (p1 : hreal) : (term57 p1) = term129.
Proof. exact (MK_COMB (@lem1329873) (@lem1329872 p1)). Qed.
Lemma lem1329876 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329877 (t : Prop) : (term131 t) = t.
Proof. exact (@lem1329876 hreal t). Qed.
Lemma lem1329878 : term129 = True.
Proof. exact (@lem1329877 True). Qed.
Lemma lem1329879 (p1 : hreal) : (term57 p1) = True.
Proof. exact (TRANS (@lem1329874 p1) (@lem1329878)). Qed.
Lemma lem1329880 : term59 = term128.
Proof. exact (fun_ext (fun p1 : hreal => @lem1329879 p1)). Qed.
Lemma lem1329881 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329882 : term60 = term129.
Proof. exact (MK_COMB (@lem1329881) (@lem1329880)). Qed.
Lemma lem1329884 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329885 (t : Prop) : (term131 t) = t.
Proof. exact (@lem1329884 hreal t). Qed.
Lemma lem1329886 : term129 = True.
Proof. exact (@lem1329885 True). Qed.
Lemma lem1329887 : term60 = True.
Proof. exact (TRANS (@lem1329882) (@lem1329886)). Qed.
Lemma lem1329888 : term49 = True.
Proof. exact (TRANS (@lem1329389) (@lem1329887)). Qed.
Lemma lem1329889 : True = term49.
Proof. exact (SYM (@lem1329888)). Qed.
Lemma lem1329890 : term49.
Proof. exact (EQ_MP (@lem1329889) (@lem0)). Qed.
