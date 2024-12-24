Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338438_term_abbrevs.
Require Import TREAL_ADD_ASSOC_spec.
Require Import thm1337747_spec.
Require Import thm1337752_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1338297 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1338298 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term1 x y z) = ((term2 x y z) = (term3 x y z)).
Proof. exact (@lem1338297 (term4 x y z) (term5 x y z)). Qed.
Lemma lem1338302 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1338303 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term2 x y z) = (term8 x y z).
Proof. exact (@lem1338302 x (treal_add y z)). Qed.
Lemma lem1338305 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1338306 (y : prod hreal hreal) (z : prod hreal hreal) : (term6 y z) = (term7 y z).
Proof. exact (@lem1338305 y z). Qed.
Lemma lem1338307 (x : prod hreal hreal) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1338308 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term8 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem1338307 x) (@lem1338306 y z)). Qed.
Lemma lem1338309 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term2 x y z) = (term10 x y z).
Proof. exact (TRANS (@lem1338303 x y z) (@lem1338308 x y z)). Qed.
Lemma lem1338310 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1338311 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term11 x y z) = (term12 x y z).
Proof. exact (MK_COMB (@lem1338310) (@lem1338309 x y z)). Qed.
Lemma lem1338313 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1338314 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term3 x y z) = (term13 x y z).
Proof. exact (@lem1338313 (treal_add x y) z). Qed.
Lemma lem1338316 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1338317 (x : prod hreal hreal) (y : prod hreal hreal) : (term6 x y) = (term7 x y).
Proof. exact (@lem1338316 x y). Qed.
Lemma lem1338318 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1338319 (x : prod hreal hreal) (y : prod hreal hreal) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1338318) (@lem1338317 x y)). Qed.
Lemma lem1338320 (z : prod hreal hreal) : (term0 z) = (term0 z).
Proof. exact (eq_refl (term0 z)). Qed.
Lemma lem1338321 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term13 x y z) = (term16 x y z).
Proof. exact (MK_COMB (@lem1338319 x y) (@lem1338320 z)). Qed.
Lemma lem1338322 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term3 x y z) = (term16 x y z).
Proof. exact (TRANS (@lem1338314 x y z) (@lem1338321 x y z)). Qed.
Lemma lem1338323 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : ((term2 x y z) = (term3 x y z)) = ((term10 x y z) = (term16 x y z)).
Proof. exact (MK_COMB (@lem1338311 x y z) (@lem1338322 x y z)). Qed.
Lemma lem1338326 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term1 x y z) = ((term10 x y z) = (term16 x y z)).
Proof. exact (TRANS (@lem1338298 x y z) (@lem1338323 x y z)). Qed.
Lemma lem1338327 (x : prod hreal hreal) (y : prod hreal hreal) : (term17 x y) = (term18 x y).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1338326 x y z)). Qed.
Lemma lem1338328 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338329 (x : prod hreal hreal) (y : prod hreal hreal) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1338328) (@lem1338327 x y)). Qed.
Lemma lem1338335 (P : real -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338336 (x : prod hreal hreal) (y : prod hreal hreal) : (term23 x y) = (term24 x y).
Proof. exact (@lem1338335 (term25 x y)). Qed.
Lemma lem1338337 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) : (term26 x y z) = ((term10 x y z) = (term16 x y z)).
Proof. exact (eq_refl (term26 x y z)). Qed.
Lemma lem1338338 (x : prod hreal hreal) (y : prod hreal hreal) : (term27 x y) = (term18 x y).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1338337 x y z)). Qed.
Lemma lem1338339 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338340 (x : prod hreal hreal) (y : prod hreal hreal) : (term23 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1338339) (@lem1338338 x y)). Qed.
Lemma lem1338341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338342 (x : prod hreal hreal) (y : prod hreal hreal) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1338341) (@lem1338340 x y)). Qed.
Lemma lem1338343 (x : prod hreal hreal) (y : prod hreal hreal) (z : real) : (term30 x y z) = ((term31 x y z) = (term32 x y z)).
Proof. exact (eq_refl (term30 x y z)). Qed.
Lemma lem1338344 (x : prod hreal hreal) (y : prod hreal hreal) : (term33 x y) = (term25 x y).
Proof. exact (fun_ext (fun z : real => @lem1338343 x y z)). Qed.
Lemma lem1338345 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338346 (x : prod hreal hreal) (y : prod hreal hreal) : (term24 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1338345) (@lem1338344 x y)). Qed.
Lemma lem1338347 (x : prod hreal hreal) (y : prod hreal hreal) : ((term23 x y) = (term24 x y)) = ((term20 x y) = (term34 x y)).
Proof. exact (MK_COMB (@lem1338342 x y) (@lem1338346 x y)). Qed.
Lemma lem1338348 (x : prod hreal hreal) (y : prod hreal hreal) : (term20 x y) = (term34 x y).
Proof. exact (EQ_MP (@lem1338347 x y) (@lem1338336 x y)). Qed.
Lemma lem1338357 (x : prod hreal hreal) (y : prod hreal hreal) : (term19 x y) = (term34 x y).
Proof. exact (TRANS (@lem1338329 x y) (@lem1338348 x y)). Qed.
Lemma lem1338358 (x : prod hreal hreal) : (term35 x) = (term36 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1338357 x y)). Qed.
Lemma lem1338359 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338360 (x : prod hreal hreal) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1338359) (@lem1338358 x)). Qed.
Lemma lem1338366 (P : real -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338367 (x : prod hreal hreal) : (term39 x) = (term40 x).
Proof. exact (@lem1338366 (term41 x)). Qed.
Lemma lem1338368 (x : prod hreal hreal) (y : prod hreal hreal) : (term42 x y) = (term34 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1338369 (x : prod hreal hreal) : (term43 x) = (term36 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1338368 x y)). Qed.
Lemma lem1338370 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338371 (x : prod hreal hreal) : (term39 x) = (term38 x).
Proof. exact (MK_COMB (@lem1338370) (@lem1338369 x)). Qed.
Lemma lem1338372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338373 (x : prod hreal hreal) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1338372) (@lem1338371 x)). Qed.
Lemma lem1338374 (x : prod hreal hreal) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1338375 (x : prod hreal hreal) : (term48 x) = (term41 x).
Proof. exact (fun_ext (fun y : real => @lem1338374 x y)). Qed.
Lemma lem1338376 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338377 (x : prod hreal hreal) : (term40 x) = (term49 x).
Proof. exact (MK_COMB (@lem1338376) (@lem1338375 x)). Qed.
Lemma lem1338378 (x : prod hreal hreal) : ((term39 x) = (term40 x)) = ((term38 x) = (term49 x)).
Proof. exact (MK_COMB (@lem1338373 x) (@lem1338377 x)). Qed.
Lemma lem1338379 (x : prod hreal hreal) : (term38 x) = (term49 x).
Proof. exact (EQ_MP (@lem1338378 x) (@lem1338367 x)). Qed.
Lemma lem1338394 (x : prod hreal hreal) : (term37 x) = (term49 x).
Proof. exact (TRANS (@lem1338360 x) (@lem1338379 x)). Qed.
Lemma lem1338395 : term50 = term51.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338394 x)). Qed.
Lemma lem1338396 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338397 : term52 = term53.
Proof. exact (MK_COMB (@lem1338396) (@lem1338395)). Qed.
Lemma lem1338403 (P : real -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338404 : term54 = term55.
Proof. exact (@lem1338403 term56). Qed.
Lemma lem1338405 (x : prod hreal hreal) : (term57 x) = (term49 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1338406 : term58 = term51.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338405 x)). Qed.
Lemma lem1338407 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338408 : term54 = term53.
Proof. exact (MK_COMB (@lem1338407) (@lem1338406)). Qed.
Lemma lem1338409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338410 : term59 = term60.
Proof. exact (MK_COMB (@lem1338409) (@lem1338408)). Qed.
Lemma lem1338411 (x : real) : (term61 x) = (term62 x).
Proof. exact (eq_refl (term61 x)). Qed.
Lemma lem1338412 : term63 = term56.
Proof. exact (fun_ext (fun x : real => @lem1338411 x)). Qed.
Lemma lem1338413 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338414 : term55 = term64.
Proof. exact (MK_COMB (@lem1338413) (@lem1338412)). Qed.
Lemma lem1338415 : (term54 = term55) = (term53 = term64).
Proof. exact (MK_COMB (@lem1338410) (@lem1338414)). Qed.
Lemma lem1338416 : term53 = term64.
Proof. exact (EQ_MP (@lem1338415) (@lem1338404)). Qed.
Lemma lem1338437 : term52 = term64.
Proof. exact (TRANS (@lem1338397) (@lem1338416)). Qed.
Lemma lem1338438 : term64.
Proof. exact (EQ_MP (@lem1338437) (@lem1328039)). Qed.
