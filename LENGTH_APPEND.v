Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_APPEND_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1097080_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1116332 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1116333 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1116332 A P). Qed.
Lemma lem1116334 {A : Type'} : term1 A.
Proof. exact (@lem1116333 A (term2 A)). Qed.
Lemma lem1116335 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1116336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1116337 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (MK_COMB (@lem1116336) (@lem1116335 A)). Qed.
Lemma lem1116338 {A : Type'} (t : list A) : (term7 A t) = (term8 A t).
Proof. exact (eq_refl (term7 A t)). Qed.
Lemma lem1116339 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1116340 {A : Type'} (t : list A) : (term9 A t) = (term10 A t).
Proof. exact (MK_COMB (@lem1116339) (@lem1116338 A t)). Qed.
Lemma lem1116341 {A : Type'} (h : A) (t : list A) : (term11 A h t) = (term12 A h t).
Proof. exact (eq_refl (term11 A h t)). Qed.
Lemma lem1116342 {A : Type'} (h : A) (t : list A) : (term13 A h t) = (term14 A h t).
Proof. exact (MK_COMB (@lem1116340 A t) (@lem1116341 A h t)). Qed.
Lemma lem1116343 {A : Type'} (h : A) : (term15 A h) = (term16 A h).
Proof. exact (fun_ext (fun t : list A => @lem1116342 A h t)). Qed.
Lemma lem1116344 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116345 {A : Type'} (h : A) : (term17 A h) = (term18 A h).
Proof. exact (MK_COMB (@lem1116344 A) (@lem1116343 A h)). Qed.
Lemma lem1116346 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (fun_ext (fun h : A => @lem1116345 A h)). Qed.
Lemma lem1116347 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1116348 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem1116347 A) (@lem1116346 A)). Qed.
Lemma lem1116349 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem1116337 A) (@lem1116348 A)). Qed.
Lemma lem1116350 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1116351 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (MK_COMB (@lem1116350) (@lem1116349 A)). Qed.
Lemma lem1116352 {A : Type'} (l : list A) : (term7 A l) = (term8 A l).
Proof. exact (eq_refl (term7 A l)). Qed.
Lemma lem1116353 {A : Type'} : (term27 A) = (term2 A).
Proof. exact (fun_ext (fun l : list A => @lem1116352 A l)). Qed.
Lemma lem1116354 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116355 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem1116354 A) (@lem1116353 A)). Qed.
Lemma lem1116356 {A : Type'} : (term1 A) = (term30 A).
Proof. exact (MK_COMB (@lem1116351 A) (@lem1116355 A)). Qed.
Lemma lem1116357 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem1116356 A) (@lem1116334 A)). Qed.
Lemma lem1116358 {A : Type'} (t : list A) (h1 : term8 A t) : term8 A t.
Proof. exact (h1). Qed.
Lemma lem1116379 : term31.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1116380 (n : nat) : term32 n.
Proof. exact (@lem1116379 n). Qed.
Lemma lem1116381 (n : nat) : (term32 n) = ((term33 n) = n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem1116401 {A : Type'} : term34 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1116402 {A : Type'} (l : list A) : term35 A l.
Proof. exact (@lem1116401 A l). Qed.
Lemma lem1116403 {A : Type'} (l : list A) : (term35 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term35 A l)). Qed.
Lemma lem1116412 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1116403 A l) (@lem1116402 A l)). Qed.
Lemma lem1116413 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1116412 A l). Qed.
Lemma lem1116414 {A : Type'} (m : list A) : (@List.app A (@nil A) m) = m.
Proof. exact (@lem1116413 A m). Qed.
Lemma lem1116415 {A : Type'} : (@List.length A) = (@List.length A).
Proof. exact (eq_refl (@List.length A)). Qed.
Lemma lem1116416 {A : Type'} (m : list A) : (term36 A m) = (@List.length A m).
Proof. exact (MK_COMB (@lem1116415 A) (@lem1116414 A m)). Qed.
Lemma lem1116417 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1116418 {A : Type'} (m : list A) : (term37 A m) = (term38 A m).
Proof. exact (MK_COMB (@lem1116417) (@lem1116416 A m)). Qed.
Lemma lem1116420 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1116421 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1116422 {A : Type'} : (term39 A) = term40.
Proof. exact (MK_COMB (@lem1116421) (@lem1116420 A)). Qed.
Lemma lem1116423 {A : Type'} (m : list A) : (@List.length A m) = (@List.length A m).
Proof. exact (eq_refl (@List.length A m)). Qed.
Lemma lem1116424 {A : Type'} (m : list A) : (term41 A m) = (term42 A m).
Proof. exact (MK_COMB (@lem1116422 A) (@lem1116423 A m)). Qed.
Lemma lem1116426 (n : nat) : (term33 n) = n.
Proof. exact (EQ_MP (@lem1116381 n) (@lem1116380 n)). Qed.
Lemma lem1116427 {A : Type'} (m : list A) : (term42 A m) = (@List.length A m).
Proof. exact (@lem1116426 (@List.length A m)). Qed.
Lemma lem1116428 {A : Type'} (m : list A) : (term41 A m) = (@List.length A m).
Proof. exact (TRANS (@lem1116424 A m) (@lem1116427 A m)). Qed.
Lemma lem1116429 {A : Type'} (m : list A) : ((term36 A m) = (term41 A m)) = ((@List.length A m) = (@List.length A m)).
Proof. exact (MK_COMB (@lem1116418 A m) (@lem1116428 A m)). Qed.
Lemma lem1116431 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1116432 (x : nat) : (x = x) = True.
Proof. exact (@lem1116431 nat x). Qed.
Lemma lem1116433 {A : Type'} (m : list A) : ((@List.length A m) = (@List.length A m)) = True.
Proof. exact (@lem1116432 (@List.length A m)). Qed.
Lemma lem1116434 {A : Type'} (m : list A) : ((term36 A m) = (term41 A m)) = True.
Proof. exact (TRANS (@lem1116429 A m) (@lem1116433 A m)). Qed.
Lemma lem1116435 {A : Type'} : (term43 A) = (term44 A).
Proof. exact (fun_ext (fun m : list A => @lem1116434 A m)). Qed.
Lemma lem1116436 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116437 {A : Type'} : (term4 A) = (term45 A).
Proof. exact (MK_COMB (@lem1116436 A) (@lem1116435 A)). Qed.
Lemma lem1116439 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1116440 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (@lem1116439 (list A) t). Qed.
Lemma lem1116441 {A : Type'} : (term45 A) = True.
Proof. exact (@lem1116440 A True). Qed.
Lemma lem1116442 {A : Type'} : (term4 A) = True.
Proof. exact (TRANS (@lem1116437 A) (@lem1116441 A)). Qed.
Lemma lem1116443 {A : Type'} : True = (term4 A).
Proof. exact (SYM (@lem1116442 A)). Qed.
Lemma lem1116444 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1116443 A) (@lem0)). Qed.
Lemma lem1116445 : term48.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1116446 : term49.
Proof. exact (proj2 (@lem1116445)). Qed.
Lemma lem1116454 : term50.
Proof. exact (proj1 (@lem1116446)). Qed.
Lemma lem1116455 (m : nat) : term51 m.
Proof. exact (@lem1116454 m). Qed.
Lemma lem1116456 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem1116457 (m : nat) : term52 m.
Proof. exact (EQ_MP (@lem1116456 m) (@lem1116455 m)). Qed.
Lemma lem1116458 (m : nat) (n : nat) : term53 m n.
Proof. exact (@lem1116457 m n). Qed.
Lemma lem1116459 (m : nat) (n : nat) : (term53 m n) = ((term54 m n) = (term55 m n)).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem1116469 {A : Type'} : term56 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1116470 {A : Type'} (h : A) : term57 A h.
Proof. exact (@lem1116469 A h). Qed.
Lemma lem1116471 {A : Type'} (h : A) : (term57 A h) = (term58 A h).
Proof. exact (eq_refl (term57 A h)). Qed.
Lemma lem1116472 {A : Type'} (h : A) : term58 A h.
Proof. exact (EQ_MP (@lem1116471 A h) (@lem1116470 A h)). Qed.
Lemma lem1116473 {A : Type'} (h : A) (t : list A) : term59 A h t.
Proof. exact (@lem1116472 A h t). Qed.
Lemma lem1116474 {A : Type'} (h : A) (t : list A) : (term59 A h t) = ((term60 A h t) = (term61 A t)).
Proof. exact (eq_refl (term59 A h t)). Qed.
Lemma lem1116477 {A : Type'} : term62 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1116478 {A : Type'} (h : A) : term63 A h.
Proof. exact (@lem1116477 A h). Qed.
Lemma lem1116479 {A : Type'} (h : A) : (term63 A h) = (term64 A h).
Proof. exact (eq_refl (term63 A h)). Qed.
Lemma lem1116480 {A : Type'} (h : A) : term64 A h.
Proof. exact (EQ_MP (@lem1116479 A h) (@lem1116478 A h)). Qed.
Lemma lem1116481 {A : Type'} (h : A) (t : list A) : term65 A h t.
Proof. exact (@lem1116480 A h t). Qed.
Lemma lem1116482 {A : Type'} (h : A) (t : list A) : (term65 A h t) = (term66 A h t).
Proof. exact (eq_refl (term65 A h t)). Qed.
Lemma lem1116483 {A : Type'} (h : A) (t : list A) : term66 A h t.
Proof. exact (EQ_MP (@lem1116482 A h t) (@lem1116481 A h t)). Qed.
Lemma lem1116484 {A : Type'} (h : A) (t : list A) (l : list A) : term67 A h t l.
Proof. exact (@lem1116483 A h t l). Qed.
Lemma lem1116485 {A : Type'} (h : A) (t : list A) (l : list A) : (term67 A h t l) = ((term68 A h t l) = (term69 A h t l)).
Proof. exact (eq_refl (term67 A h t l)). Qed.
Lemma lem1116491 {A : Type'} (m : list A) (t : list A) (h1 : term8 A t) : term70 A t m.
Proof. exact (@lem1116358 A t h1 m). Qed.
Lemma lem1116492 {A : Type'} (t : list A) (m : list A) : (term70 A t m) = ((term71 A t m) = (term72 A t m)).
Proof. exact (eq_refl (term70 A t m)). Qed.
Lemma lem1116501 {A : Type'} (h : A) (t : list A) (l : list A) : (term68 A h t l) = (term69 A h t l).
Proof. exact (EQ_MP (@lem1116485 A h t l) (@lem1116484 A h t l)). Qed.
Lemma lem1116502 {A : Type'} (h : A) (t : list A) (l : list A) : (term68 A h t l) = (term69 A h t l).
Proof. exact (@lem1116501 A h t l). Qed.
Lemma lem1116503 {A : Type'} (h : A) (t : list A) (m : list A) : (term68 A h t m) = (term69 A h t m).
Proof. exact (@lem1116502 A h t m). Qed.
Lemma lem1116504 {A : Type'} : (@List.length A) = (@List.length A).
Proof. exact (eq_refl (@List.length A)). Qed.
Lemma lem1116505 {A : Type'} (h : A) (t : list A) (m : list A) : (term73 A h t m) = (term74 A h t m).
Proof. exact (MK_COMB (@lem1116504 A) (@lem1116503 A h t m)). Qed.
Lemma lem1116507 {A : Type'} (h : A) (t : list A) : (term60 A h t) = (term61 A t).
Proof. exact (EQ_MP (@lem1116474 A h t) (@lem1116473 A h t)). Qed.
Lemma lem1116508 {A : Type'} (h : A) (t : list A) : (term60 A h t) = (term61 A t).
Proof. exact (@lem1116507 A h t). Qed.
Lemma lem1116509 {A : Type'} (h : A) (t : list A) (m : list A) : (term74 A h t m) = (term75 A t m).
Proof. exact (@lem1116508 A h (@List.app A t m)). Qed.
Lemma lem1116511 {A : Type'} (m : list A) (t : list A) (h1 : term8 A t) : (term71 A t m) = (term72 A t m).
Proof. exact (EQ_MP (@lem1116492 A t m) (@lem1116491 A m t h1)). Qed.
Lemma lem1116512 {A : Type'} (m : list A) (t : list A) (h1 : term8 A t) : (term71 A t m) = (term72 A t m).
Proof. exact (@lem1116511 A m t h1). Qed.
Lemma lem1116513 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1116514 {A : Type'} (m : list A) (t : list A) (h1 : term8 A t) : (term75 A t m) = (term76 A t m).
Proof. exact (MK_COMB (@lem1116513) (@lem1116512 A m t h1)). Qed.
Lemma lem1116515 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term8 A t) : (term74 A h t m) = (term76 A t m).
Proof. exact (TRANS (@lem1116509 A h t m) (@lem1116514 A m t h1)). Qed.
Lemma lem1116516 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term8 A t) : (term73 A h t m) = (term76 A t m).
Proof. exact (TRANS (@lem1116505 A h t m) (@lem1116515 A h m t h1)). Qed.
Lemma lem1116517 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1116518 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term8 A t) : (term77 A h t m) = (term78 A t m).
Proof. exact (MK_COMB (@lem1116517) (@lem1116516 A h m t h1)). Qed.
Lemma lem1116520 {A : Type'} (h : A) (t : list A) : (term60 A h t) = (term61 A t).
Proof. exact (EQ_MP (@lem1116474 A h t) (@lem1116473 A h t)). Qed.
Lemma lem1116521 {A : Type'} (h : A) (t : list A) : (term60 A h t) = (term61 A t).
Proof. exact (@lem1116520 A h t). Qed.
Lemma lem1116522 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1116523 {A : Type'} (h : A) (t : list A) : (term79 A h t) = (term80 A t).
Proof. exact (MK_COMB (@lem1116522) (@lem1116521 A h t)). Qed.
Lemma lem1116524 {A : Type'} (m : list A) : (@List.length A m) = (@List.length A m).
Proof. exact (eq_refl (@List.length A m)). Qed.
Lemma lem1116525 {A : Type'} (h : A) (t : list A) (m : list A) : (term81 A h t m) = (term82 A t m).
Proof. exact (MK_COMB (@lem1116523 A h t) (@lem1116524 A m)). Qed.
Lemma lem1116527 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (EQ_MP (@lem1116459 m n) (@lem1116458 m n)). Qed.
Lemma lem1116528 {A : Type'} (t : list A) (m : list A) : (term82 A t m) = (term76 A t m).
Proof. exact (@lem1116527 (@List.length A t) (@List.length A m)). Qed.
Lemma lem1116529 {A : Type'} (h : A) (t : list A) (m : list A) : (term81 A h t m) = (term76 A t m).
Proof. exact (TRANS (@lem1116525 A h t m) (@lem1116528 A t m)). Qed.
Lemma lem1116530 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term8 A t) : ((term73 A h t m) = (term81 A h t m)) = ((term76 A t m) = (term76 A t m)).
Proof. exact (MK_COMB (@lem1116518 A h m t h1) (@lem1116529 A h t m)). Qed.
Lemma lem1116532 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1116533 (x : nat) : (x = x) = True.
Proof. exact (@lem1116532 nat x). Qed.
Lemma lem1116534 {A : Type'} (t : list A) (m : list A) : ((term76 A t m) = (term76 A t m)) = True.
Proof. exact (@lem1116533 (term76 A t m)). Qed.
Lemma lem1116535 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term8 A t) : ((term73 A h t m) = (term81 A h t m)) = True.
Proof. exact (TRANS (@lem1116530 A h m t h1) (@lem1116534 A t m)). Qed.
Lemma lem1116536 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term83 A h t) = (term44 A).
Proof. exact (fun_ext (fun m : list A => @lem1116535 A h m t h1)). Qed.
Lemma lem1116537 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116538 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term12 A h t) = (term45 A).
Proof. exact (MK_COMB (@lem1116537 A) (@lem1116536 A h t h1)). Qed.
Lemma lem1116540 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1116541 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (@lem1116540 (list A) t). Qed.
Lemma lem1116542 {A : Type'} : (term45 A) = True.
Proof. exact (@lem1116541 A True). Qed.
Lemma lem1116543 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term12 A h t) = True.
Proof. exact (TRANS (@lem1116538 A h t h1) (@lem1116542 A)). Qed.
Lemma lem1116544 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : True = (term12 A h t).
Proof. exact (SYM (@lem1116543 A h t h1)). Qed.
Lemma lem1116545 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : term12 A h t.
Proof. exact (EQ_MP (@lem1116544 A h t h1) (@lem0)). Qed.
Lemma lem1116546 {A : Type'} (h : A) (t : list A) : term14 A h t.
Proof. exact (fun h0 : term8 A t => @lem1116545 A h t h0). Qed.
Lemma lem1116551 {A : Type'} (h : A) : term18 A h.
Proof. exact (fun t : list A => @lem1116546 A h t). Qed.
Lemma lem1116556 {A : Type'} : term22 A.
Proof. exact (fun h : A => @lem1116551 A h). Qed.
Lemma lem1116557 {A : Type'} : term24 A.
Proof. exact (conj (@lem1116444 A) (@lem1116556 A)). Qed.
Lemma lem1116558 {A : Type'} : term29 A.
Proof. exact (@lem1116357 A (@lem1116557 A)). Qed.
