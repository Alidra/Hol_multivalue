Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_REVERSE_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import LENGTH_APPEND_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1096517_spec.
Require Import thm1096523_spec.
Require Import thm1096524_spec.
Require Import thm1097080_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1118316 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1118317 : term1.
Proof. exact (proj2 (@lem1118316)). Qed.
Lemma lem1118318 : term2.
Proof. exact (proj2 (@lem1118317)). Qed.
Lemma lem1118319 (m : nat) : term3 m.
Proof. exact (@lem1118318 m). Qed.
Lemma lem1118320 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1118321 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1118320 m) (@lem1118319 m)). Qed.
Lemma lem1118322 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem1118321 m n). Qed.
Lemma lem1118323 (m : nat) (n : nat) : (term5 m n) = ((term6 m n) = (term7 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem1118332 : term8.
Proof. exact (proj1 (@lem1118316)). Qed.
Lemma lem1118333 (m : nat) : term9 m.
Proof. exact (@lem1118332 m). Qed.
Lemma lem1118334 (m : nat) : (term9 m) = ((term10 m) = m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1118341 {A : Type'} (P : type1143 A) : term11 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1118342 {A : Type'} (P : type1143 A) : term11 A P.
Proof. exact (@lem1118341 A P). Qed.
Lemma lem1118343 {A : Type'} : term12 A.
Proof. exact (@lem1118342 A (term13 A)). Qed.
Lemma lem1118344 {A : Type'} : (term14 A) = ((term15 A) = (@List.length A (@nil A))).
Proof. exact (eq_refl (term14 A)). Qed.
Lemma lem1118345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1118346 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (MK_COMB (@lem1118345) (@lem1118344 A)). Qed.
Lemma lem1118347 {A : Type'} (t : list A) : (term18 A t) = ((term19 A t) = (@List.length A t)).
Proof. exact (eq_refl (term18 A t)). Qed.
Lemma lem1118348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118349 {A : Type'} (t : list A) : (term20 A t) = (term21 A t).
Proof. exact (MK_COMB (@lem1118348) (@lem1118347 A t)). Qed.
Lemma lem1118350 {A : Type'} (h : A) (t : list A) : (term22 A h t) = ((term23 A h t) = (term24 A h t)).
Proof. exact (eq_refl (term22 A h t)). Qed.
Lemma lem1118351 {A : Type'} (h : A) (t : list A) : (term25 A h t) = (term26 A h t).
Proof. exact (MK_COMB (@lem1118349 A t) (@lem1118350 A h t)). Qed.
Lemma lem1118352 {A : Type'} (h : A) : (term27 A h) = (term28 A h).
Proof. exact (fun_ext (fun t : list A => @lem1118351 A h t)). Qed.
Lemma lem1118353 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1118354 {A : Type'} (h : A) : (term29 A h) = (term30 A h).
Proof. exact (MK_COMB (@lem1118353 A) (@lem1118352 A h)). Qed.
Lemma lem1118355 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (fun_ext (fun h : A => @lem1118354 A h)). Qed.
Lemma lem1118356 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1118357 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (MK_COMB (@lem1118356 A) (@lem1118355 A)). Qed.
Lemma lem1118358 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem1118346 A) (@lem1118357 A)). Qed.
Lemma lem1118359 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118360 {A : Type'} : (term37 A) = (term38 A).
Proof. exact (MK_COMB (@lem1118359) (@lem1118358 A)). Qed.
Lemma lem1118361 {A : Type'} (l : list A) : (term18 A l) = ((term19 A l) = (@List.length A l)).
Proof. exact (eq_refl (term18 A l)). Qed.
Lemma lem1118362 {A : Type'} : (term39 A) = (term13 A).
Proof. exact (fun_ext (fun l : list A => @lem1118361 A l)). Qed.
Lemma lem1118363 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1118364 {A : Type'} : (term40 A) = (term41 A).
Proof. exact (MK_COMB (@lem1118363 A) (@lem1118362 A)). Qed.
Lemma lem1118365 {A : Type'} : (term12 A) = (term42 A).
Proof. exact (MK_COMB (@lem1118360 A) (@lem1118364 A)). Qed.
Lemma lem1118366 {A : Type'} : term42 A.
Proof. exact (EQ_MP (@lem1118365 A) (@lem1118343 A)). Qed.
Lemma lem1118387 {A : Type'} : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1096517 A)). Qed.
Lemma lem1118388 {A : Type'} : (@List.length A) = (@List.length A).
Proof. exact (eq_refl (@List.length A)). Qed.
Lemma lem1118389 {A : Type'} : (term15 A) = (@List.length A (@nil A)).
Proof. exact (MK_COMB (@lem1118388 A) (@lem1118387 A)). Qed.
Lemma lem1118391 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1118392 {A : Type'} : (term15 A) = (NUMERAL 0).
Proof. exact (TRANS (@lem1118389 A) (@lem1118391 A)). Qed.
Lemma lem1118393 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1118394 {A : Type'} : (term43 A) = term44.
Proof. exact (MK_COMB (@lem1118393) (@lem1118392 A)). Qed.
Lemma lem1118396 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1118397 {A : Type'} : ((term15 A) = (@List.length A (@nil A))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1118394 A) (@lem1118396 A)). Qed.
Lemma lem1118399 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1118400 (x : nat) : (x = x) = True.
Proof. exact (@lem1118399 nat x). Qed.
Lemma lem1118401 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1118400 (NUMERAL 0)). Qed.
Lemma lem1118402 {A : Type'} : ((term15 A) = (@List.length A (@nil A))) = True.
Proof. exact (TRANS (@lem1118397 A) (@lem1118401)). Qed.
Lemma lem1118403 {A : Type'} : True = ((term15 A) = (@List.length A (@nil A))).
Proof. exact (SYM (@lem1118402 A)). Qed.
Lemma lem1118404 {A : Type'} : (term15 A) = (@List.length A (@nil A)).
Proof. exact (EQ_MP (@lem1118403 A) (@lem0)). Qed.
Lemma lem1118405 {A : Type'} : term45 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1118406 {A : Type'} (h : A) : term46 A h.
Proof. exact (@lem1118405 A h). Qed.
Lemma lem1118407 {A : Type'} (h : A) : (term46 A h) = (term47 A h).
Proof. exact (eq_refl (term46 A h)). Qed.
Lemma lem1118408 {A : Type'} (h : A) : term47 A h.
Proof. exact (EQ_MP (@lem1118407 A h) (@lem1118406 A h)). Qed.
Lemma lem1118409 {A : Type'} (h : A) (t : list A) : term48 A h t.
Proof. exact (@lem1118408 A h t). Qed.
Lemma lem1118410 {A : Type'} (h : A) (t : list A) : (term48 A h t) = ((term24 A h t) = (term49 A t)).
Proof. exact (eq_refl (term48 A h t)). Qed.
Lemma lem1118413 {A : Type'} (l : list A) : term50 A l.
Proof. exact (@lem1116558 A l). Qed.
Lemma lem1118414 {A : Type'} (l : list A) : (term50 A l) = (term51 A l).
Proof. exact (eq_refl (term50 A l)). Qed.
Lemma lem1118415 {A : Type'} (l : list A) : term51 A l.
Proof. exact (EQ_MP (@lem1118414 A l) (@lem1118413 A l)). Qed.
Lemma lem1118416 {A : Type'} (l : list A) (m : list A) : term52 A l m.
Proof. exact (@lem1118415 A l m). Qed.
Lemma lem1118417 {A : Type'} (l : list A) (m : list A) : (term52 A l m) = ((term53 A l m) = (term54 A l m)).
Proof. exact (eq_refl (term52 A l m)). Qed.
Lemma lem1118424 {A : Type'} (l : list A) (x : A) : (term55 A x l) = (term56 A l x).
Proof. exact (EQ_MP (@lem1096524 A l x) (@lem1096523 A l x)). Qed.
Lemma lem1118425 {A : Type'} (l : list A) (x : A) : (term55 A x l) = (term56 A l x).
Proof. exact (@lem1118424 A l x). Qed.
Lemma lem1118426 {A : Type'} (t : list A) (h : A) : (term55 A h t) = (term56 A t h).
Proof. exact (@lem1118425 A t h). Qed.
Lemma lem1118427 {A : Type'} : (@List.length A) = (@List.length A).
Proof. exact (eq_refl (@List.length A)). Qed.
Lemma lem1118428 {A : Type'} (t : list A) (h : A) : (term23 A h t) = (term57 A t h).
Proof. exact (MK_COMB (@lem1118427 A) (@lem1118426 A t h)). Qed.
Lemma lem1118430 {A : Type'} (l : list A) (m : list A) : (term53 A l m) = (term54 A l m).
Proof. exact (EQ_MP (@lem1118417 A l m) (@lem1118416 A l m)). Qed.
Lemma lem1118431 {A : Type'} (l : list A) (m : list A) : (term53 A l m) = (term54 A l m).
Proof. exact (@lem1118430 A l m). Qed.
Lemma lem1118432 {A : Type'} (t : list A) (h : A) : (term57 A t h) = (term58 A t h).
Proof. exact (@lem1118431 A (@List.rev A t) (@cons A h (@nil A))). Qed.
Lemma lem1118434 {A : Type'} (t : list A) (h1 : (term19 A t) = (@List.length A t)) : (term19 A t) = (@List.length A t).
Proof. exact (h1). Qed.
Lemma lem1118435 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1118436 {A : Type'} (t : list A) (h1 : (term19 A t) = (@List.length A t)) : (term59 A t) = (term60 A t).
Proof. exact (MK_COMB (@lem1118435) (@lem1118434 A t h1)). Qed.
Lemma lem1118438 {A : Type'} (h : A) (t : list A) : (term24 A h t) = (term49 A t).
Proof. exact (EQ_MP (@lem1118410 A h t) (@lem1118409 A h t)). Qed.
Lemma lem1118439 {A : Type'} (h : A) (t : list A) : (term24 A h t) = (term49 A t).
Proof. exact (@lem1118438 A h t). Qed.
Lemma lem1118440 {A : Type'} (h : A) : (term61 A h) = (term62 A).
Proof. exact (@lem1118439 A h (@nil A)). Qed.
Lemma lem1118442 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1118443 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1118444 {A : Type'} : (term62 A) = term63.
Proof. exact (MK_COMB (@lem1118443) (@lem1118442 A)). Qed.
Lemma lem1118445 {A : Type'} (h : A) : (term61 A h) = term63.
Proof. exact (TRANS (@lem1118440 A h) (@lem1118444 A)). Qed.
Lemma lem1118446 {A : Type'} (h : A) (t : list A) (h1 : (term19 A t) = (@List.length A t)) : (term58 A t h) = (term64 A t).
Proof. exact (MK_COMB (@lem1118436 A t h1) (@lem1118445 A h)). Qed.
Lemma lem1118447 {A : Type'} (h : A) (t : list A) (h1 : (term19 A t) = (@List.length A t)) : (term57 A t h) = (term64 A t).
Proof. exact (TRANS (@lem1118432 A t h) (@lem1118446 A h t h1)). Qed.
Lemma lem1118448 {A : Type'} (h : A) (t : list A) (h1 : (term19 A t) = (@List.length A t)) : (term23 A h t) = (term64 A t).
Proof. exact (TRANS (@lem1118428 A t h) (@lem1118447 A h t h1)). Qed.
Lemma lem1118449 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1118450 {A : Type'} (h : A) (t : list A) (h1 : (term19 A t) = (@List.length A t)) : (term65 A h t) = (term66 A t).
Proof. exact (MK_COMB (@lem1118449) (@lem1118448 A h t h1)). Qed.
Lemma lem1118452 {A : Type'} (h : A) (t : list A) : (term24 A h t) = (term49 A t).
Proof. exact (EQ_MP (@lem1118410 A h t) (@lem1118409 A h t)). Qed.
Lemma lem1118453 {A : Type'} (h : A) (t : list A) : (term24 A h t) = (term49 A t).
Proof. exact (@lem1118452 A h t). Qed.
Lemma lem1118454 {A : Type'} (h : A) (t : list A) (h1 : (term19 A t) = (@List.length A t)) : ((term23 A h t) = (term24 A h t)) = ((term64 A t) = (term49 A t)).
Proof. exact (MK_COMB (@lem1118450 A h t h1) (@lem1118453 A h t)). Qed.
Lemma lem1118457 {A : Type'} (h : A) (t : list A) (h1 : (term19 A t) = (@List.length A t)) : ((term64 A t) = (term49 A t)) = ((term23 A h t) = (term24 A h t)).
Proof. exact (SYM (@lem1118454 A h t h1)). Qed.
Lemma lem1118461 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem1118323 m n) (@lem1118322 m n)). Qed.
Lemma lem1118462 {A : Type'} (t : list A) : (term64 A t) = (term67 A t).
Proof. exact (@lem1118461 (@List.length A t) (NUMERAL 0)). Qed.
Lemma lem1118464 (m : nat) : (term10 m) = m.
Proof. exact (EQ_MP (@lem1118334 m) (@lem1118333 m)). Qed.
Lemma lem1118465 {A : Type'} (t : list A) : (term68 A t) = (@List.length A t).
Proof. exact (@lem1118464 (@List.length A t)). Qed.
Lemma lem1118466 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1118467 {A : Type'} (t : list A) : (term67 A t) = (term49 A t).
Proof. exact (MK_COMB (@lem1118466) (@lem1118465 A t)). Qed.
Lemma lem1118468 {A : Type'} (t : list A) : (term64 A t) = (term49 A t).
Proof. exact (TRANS (@lem1118462 A t) (@lem1118467 A t)). Qed.
Lemma lem1118469 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1118470 {A : Type'} (t : list A) : (term66 A t) = (term69 A t).
Proof. exact (MK_COMB (@lem1118469) (@lem1118468 A t)). Qed.
Lemma lem1118471 {A : Type'} (t : list A) : (term49 A t) = (term49 A t).
Proof. exact (eq_refl (term49 A t)). Qed.
Lemma lem1118472 {A : Type'} (t : list A) : ((term64 A t) = (term49 A t)) = ((term49 A t) = (term49 A t)).
Proof. exact (MK_COMB (@lem1118470 A t) (@lem1118471 A t)). Qed.
Lemma lem1118474 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1118475 (x : nat) : (x = x) = True.
Proof. exact (@lem1118474 nat x). Qed.
Lemma lem1118476 {A : Type'} (t : list A) : ((term49 A t) = (term49 A t)) = True.
Proof. exact (@lem1118475 (term49 A t)). Qed.
Lemma lem1118477 {A : Type'} (t : list A) : ((term64 A t) = (term49 A t)) = True.
Proof. exact (TRANS (@lem1118472 A t) (@lem1118476 A t)). Qed.
Lemma lem1118478 {A : Type'} (t : list A) : True = ((term64 A t) = (term49 A t)).
Proof. exact (SYM (@lem1118477 A t)). Qed.
Lemma lem1118479 {A : Type'} (t : list A) : (term64 A t) = (term49 A t).
Proof. exact (EQ_MP (@lem1118478 A t) (@lem0)). Qed.
Lemma lem1118480 {A : Type'} (h : A) (t : list A) (h1 : (term19 A t) = (@List.length A t)) : (term23 A h t) = (term24 A h t).
Proof. exact (EQ_MP (@lem1118457 A h t h1) (@lem1118479 A t)). Qed.
Lemma lem1118481 {A : Type'} (h : A) (t : list A) : term26 A h t.
Proof. exact (fun h0 : (term19 A t) = (@List.length A t) => @lem1118480 A h t h0). Qed.
Lemma lem1118486 {A : Type'} (h : A) : term30 A h.
Proof. exact (fun t : list A => @lem1118481 A h t). Qed.
Lemma lem1118491 {A : Type'} : term34 A.
Proof. exact (fun h : A => @lem1118486 A h). Qed.
Lemma lem1118492 {A : Type'} : term36 A.
Proof. exact (conj (@lem1118404 A) (@lem1118491 A)). Qed.
Lemma lem1118493 {A : Type'} : term41 A.
Proof. exact (@lem1118366 A (@lem1118492 A)). Qed.
