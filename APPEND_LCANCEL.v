Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import APPEND_LCANCEL_term_abbrevs.
Require Import CONS_11_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1187399 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1187400 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1187399 A P). Qed.
Lemma lem1187401 {A : Type'} : term1 A.
Proof. exact (@lem1187400 A (term2 A)). Qed.
Lemma lem1187402 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1187403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1187404 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (MK_COMB (@lem1187403) (@lem1187402 A)). Qed.
Lemma lem1187405 {A : Type'} (t : list A) : (term7 A t) = (term8 A t).
Proof. exact (eq_refl (term7 A t)). Qed.
Lemma lem1187406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1187407 {A : Type'} (t : list A) : (term9 A t) = (term10 A t).
Proof. exact (MK_COMB (@lem1187406) (@lem1187405 A t)). Qed.
Lemma lem1187408 {A : Type'} (h : A) (t : list A) : (term11 A h t) = (term12 A h t).
Proof. exact (eq_refl (term11 A h t)). Qed.
Lemma lem1187409 {A : Type'} (h : A) (t : list A) : (term13 A h t) = (term14 A h t).
Proof. exact (MK_COMB (@lem1187407 A t) (@lem1187408 A h t)). Qed.
Lemma lem1187410 {A : Type'} (h : A) : (term15 A h) = (term16 A h).
Proof. exact (fun_ext (fun t : list A => @lem1187409 A h t)). Qed.
Lemma lem1187411 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1187412 {A : Type'} (h : A) : (term17 A h) = (term18 A h).
Proof. exact (MK_COMB (@lem1187411 A) (@lem1187410 A h)). Qed.
Lemma lem1187413 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (fun_ext (fun h : A => @lem1187412 A h)). Qed.
Lemma lem1187414 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1187415 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem1187414 A) (@lem1187413 A)). Qed.
Lemma lem1187416 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem1187404 A) (@lem1187415 A)). Qed.
Lemma lem1187417 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1187418 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (MK_COMB (@lem1187417) (@lem1187416 A)). Qed.
Lemma lem1187419 {A : Type'} (l1 : list A) : (term7 A l1) = (term8 A l1).
Proof. exact (eq_refl (term7 A l1)). Qed.
Lemma lem1187420 {A : Type'} : (term27 A) = (term2 A).
Proof. exact (fun_ext (fun l1 : list A => @lem1187419 A l1)). Qed.
Lemma lem1187421 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1187422 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem1187421 A) (@lem1187420 A)). Qed.
Lemma lem1187423 {A : Type'} : (term1 A) = (term30 A).
Proof. exact (MK_COMB (@lem1187418 A) (@lem1187422 A)). Qed.
Lemma lem1187424 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem1187423 A) (@lem1187401 A)). Qed.
Lemma lem1187425 {A : Type'} (t : list A) (h1 : term8 A t) : term8 A t.
Proof. exact (h1). Qed.
Lemma lem1187448 {A : Type'} : term31 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1187449 {A : Type'} (l : list A) : term32 A l.
Proof. exact (@lem1187448 A l). Qed.
Lemma lem1187450 {A : Type'} (l : list A) : (term32 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term32 A l)). Qed.
Lemma lem1187465 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1187450 A l) (@lem1187449 A l)). Qed.
Lemma lem1187466 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1187465 A l). Qed.
Lemma lem1187467 {A : Type'} (l2 : list A) : (@List.app A (@nil A) l2) = l2.
Proof. exact (@lem1187466 A l2). Qed.
Lemma lem1187468 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1187469 {A : Type'} (l2 : list A) : (term33 A l2) = (@eq (list A) l2).
Proof. exact (MK_COMB (@lem1187468 A) (@lem1187467 A l2)). Qed.
Lemma lem1187471 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1187450 A l) (@lem1187449 A l)). Qed.
Lemma lem1187472 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1187471 A l). Qed.
Lemma lem1187473 {A : Type'} (l3 : list A) : (@List.app A (@nil A) l3) = l3.
Proof. exact (@lem1187472 A l3). Qed.
Lemma lem1187474 {A : Type'} (l2 : list A) (l3 : list A) : ((@List.app A (@nil A) l2) = (@List.app A (@nil A) l3)) = (l2 = l3).
Proof. exact (MK_COMB (@lem1187469 A l2) (@lem1187473 A l3)). Qed.
Lemma lem1187477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1187478 {A : Type'} (l2 : list A) (l3 : list A) : (term34 A l2 l3) = (term35 A l2 l3).
Proof. exact (MK_COMB (@lem1187477) (@lem1187474 A l2 l3)). Qed.
Lemma lem1187481 {A : Type'} (l2 : list A) (l3 : list A) : (l2 = l3) = (l2 = l3).
Proof. exact (eq_refl (l2 = l3)). Qed.
Lemma lem1187482 {A : Type'} (l2 : list A) (l3 : list A) : (((@List.app A (@nil A) l2) = (@List.app A (@nil A) l3)) = (l2 = l3)) = ((l2 = l3) = (l2 = l3)).
Proof. exact (MK_COMB (@lem1187478 A l2 l3) (@lem1187481 A l2 l3)). Qed.
Lemma lem1187484 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1187485 (x : Prop) : (x = x) = True.
Proof. exact (@lem1187484 Prop x). Qed.
Lemma lem1187486 {A : Type'} (l2 : list A) (l3 : list A) : ((l2 = l3) = (l2 = l3)) = True.
Proof. exact (@lem1187485 (l2 = l3)). Qed.
Lemma lem1187487 {A : Type'} (l2 : list A) (l3 : list A) : (((@List.app A (@nil A) l2) = (@List.app A (@nil A) l3)) = (l2 = l3)) = True.
Proof. exact (TRANS (@lem1187482 A l2 l3) (@lem1187486 A l2 l3)). Qed.
Lemma lem1187488 {A : Type'} (l2 : list A) : (term36 A l2) = (term37 A).
Proof. exact (fun_ext (fun l3 : list A => @lem1187487 A l2 l3)). Qed.
Lemma lem1187489 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1187490 {A : Type'} (l2 : list A) : (term38 A l2) = (term39 A).
Proof. exact (MK_COMB (@lem1187489 A) (@lem1187488 A l2)). Qed.
Lemma lem1187492 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1187493 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (@lem1187492 (list A) t). Qed.
Lemma lem1187494 {A : Type'} : (term39 A) = True.
Proof. exact (@lem1187493 A True). Qed.
Lemma lem1187495 {A : Type'} (l2 : list A) : (term38 A l2) = True.
Proof. exact (TRANS (@lem1187490 A l2) (@lem1187494 A)). Qed.
Lemma lem1187496 {A : Type'} : (term42 A) = (term37 A).
Proof. exact (fun_ext (fun l2 : list A => @lem1187495 A l2)). Qed.
Lemma lem1187497 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1187498 {A : Type'} : (term4 A) = (term39 A).
Proof. exact (MK_COMB (@lem1187497 A) (@lem1187496 A)). Qed.
Lemma lem1187500 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1187501 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (@lem1187500 (list A) t). Qed.
Lemma lem1187502 {A : Type'} : (term39 A) = True.
Proof. exact (@lem1187501 A True). Qed.
Lemma lem1187503 {A : Type'} : (term4 A) = True.
Proof. exact (TRANS (@lem1187498 A) (@lem1187502 A)). Qed.
Lemma lem1187504 {A : Type'} : True = (term4 A).
Proof. exact (SYM (@lem1187503 A)). Qed.
Lemma lem1187505 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1187504 A) (@lem0)). Qed.
Lemma lem1187506 {A : Type'} (h1' : A) : term43 A h1'.
Proof. exact (@lem1113436 A h1'). Qed.
Lemma lem1187507 {A : Type'} (h1' : A) : (term43 A h1') = (term44 A h1').
Proof. exact (eq_refl (term43 A h1')). Qed.
Lemma lem1187508 {A : Type'} (h1' : A) : term44 A h1'.
Proof. exact (EQ_MP (@lem1187507 A h1') (@lem1187506 A h1')). Qed.
Lemma lem1187509 {A : Type'} (h1' : A) (h2' : A) : term45 A h1' h2'.
Proof. exact (@lem1187508 A h1' h2'). Qed.
Lemma lem1187510 {A : Type'} (h1' : A) (h2' : A) : (term45 A h1' h2') = (term46 A h1' h2').
Proof. exact (eq_refl (term45 A h1' h2')). Qed.
Lemma lem1187511 {A : Type'} (h1' : A) (h2' : A) : term46 A h1' h2'.
Proof. exact (EQ_MP (@lem1187510 A h1' h2') (@lem1187509 A h1' h2')). Qed.
Lemma lem1187512 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term47 A h1' h2' t1.
Proof. exact (@lem1187511 A h1' h2' t1). Qed.
Lemma lem1187513 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term47 A h1' h2' t1) = (term48 A h1' h2' t1).
Proof. exact (eq_refl (term47 A h1' h2' t1)). Qed.
Lemma lem1187514 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term48 A h1' h2' t1.
Proof. exact (EQ_MP (@lem1187513 A h1' h2' t1) (@lem1187512 A h1' h2' t1)). Qed.
Lemma lem1187515 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : term49 A h1' h2' t1 t2.
Proof. exact (@lem1187514 A h1' h2' t1 t2). Qed.
Lemma lem1187516 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term49 A h1' h2' t1 t2) = (((@cons A h1' t1) = (@cons A h2' t2)) = (term50 A h1' h2' t1 t2)).
Proof. exact (eq_refl (term49 A h1' h2' t1 t2)). Qed.
Lemma lem1187518 {A : Type'} : term51 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1187519 {A : Type'} (h : A) : term52 A h.
Proof. exact (@lem1187518 A h). Qed.
Lemma lem1187520 {A : Type'} (h : A) : (term52 A h) = (term53 A h).
Proof. exact (eq_refl (term52 A h)). Qed.
Lemma lem1187521 {A : Type'} (h : A) : term53 A h.
Proof. exact (EQ_MP (@lem1187520 A h) (@lem1187519 A h)). Qed.
Lemma lem1187522 {A : Type'} (h : A) (t : list A) : term54 A h t.
Proof. exact (@lem1187521 A h t). Qed.
Lemma lem1187523 {A : Type'} (h : A) (t : list A) : (term54 A h t) = (term55 A h t).
Proof. exact (eq_refl (term54 A h t)). Qed.
Lemma lem1187524 {A : Type'} (h : A) (t : list A) : term55 A h t.
Proof. exact (EQ_MP (@lem1187523 A h t) (@lem1187522 A h t)). Qed.
Lemma lem1187525 {A : Type'} (h : A) (t : list A) (l : list A) : term56 A h t l.
Proof. exact (@lem1187524 A h t l). Qed.
Lemma lem1187526 {A : Type'} (h : A) (t : list A) (l : list A) : (term56 A h t l) = ((term57 A h t l) = (term58 A h t l)).
Proof. exact (eq_refl (term56 A h t l)). Qed.
Lemma lem1187532 {A : Type'} (l2 : list A) (t : list A) (h1 : term8 A t) : term59 A t l2.
Proof. exact (@lem1187425 A t h1 l2). Qed.
Lemma lem1187533 {A : Type'} (t : list A) (l2 : list A) : (term59 A t l2) = (term60 A t l2).
Proof. exact (eq_refl (term59 A t l2)). Qed.
Lemma lem1187534 {A : Type'} (l2 : list A) (t : list A) (h1 : term8 A t) : term60 A t l2.
Proof. exact (EQ_MP (@lem1187533 A t l2) (@lem1187532 A l2 t h1)). Qed.
Lemma lem1187535 {A : Type'} (l2 : list A) (l3 : list A) (t : list A) (h1 : term8 A t) : term61 A t l2 l3.
Proof. exact (@lem1187534 A l2 t h1 l3). Qed.
Lemma lem1187536 {A : Type'} (t : list A) (l2 : list A) (l3 : list A) : (term61 A t l2 l3) = (((@List.app A t l2) = (@List.app A t l3)) = (l2 = l3)).
Proof. exact (eq_refl (term61 A t l2 l3)). Qed.
Lemma lem1187551 {A : Type'} (h : A) (t : list A) (l : list A) : (term57 A h t l) = (term58 A h t l).
Proof. exact (EQ_MP (@lem1187526 A h t l) (@lem1187525 A h t l)). Qed.
Lemma lem1187552 {A : Type'} (h : A) (t : list A) (l : list A) : (term57 A h t l) = (term58 A h t l).
Proof. exact (@lem1187551 A h t l). Qed.
Lemma lem1187553 {A : Type'} (h : A) (t : list A) (l2 : list A) : (term57 A h t l2) = (term58 A h t l2).
Proof. exact (@lem1187552 A h t l2). Qed.
Lemma lem1187554 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1187555 {A : Type'} (h : A) (t : list A) (l2 : list A) : (term62 A h t l2) = (term63 A h t l2).
Proof. exact (MK_COMB (@lem1187554 A) (@lem1187553 A h t l2)). Qed.
Lemma lem1187557 {A : Type'} (h : A) (t : list A) (l : list A) : (term57 A h t l) = (term58 A h t l).
Proof. exact (EQ_MP (@lem1187526 A h t l) (@lem1187525 A h t l)). Qed.
Lemma lem1187558 {A : Type'} (h : A) (t : list A) (l : list A) : (term57 A h t l) = (term58 A h t l).
Proof. exact (@lem1187557 A h t l). Qed.
Lemma lem1187559 {A : Type'} (h : A) (t : list A) (l3 : list A) : (term57 A h t l3) = (term58 A h t l3).
Proof. exact (@lem1187558 A h t l3). Qed.
Lemma lem1187560 {A : Type'} (l2 : list A) (h : A) (t : list A) (l3 : list A) : ((term57 A h t l2) = (term57 A h t l3)) = ((term58 A h t l2) = (term58 A h t l3)).
Proof. exact (MK_COMB (@lem1187555 A h t l2) (@lem1187559 A h t l3)). Qed.
Lemma lem1187562 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term50 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1187516 A h1' h2' t1 t2) (@lem1187515 A h1' h2' t1 t2)). Qed.
Lemma lem1187563 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term50 A h1' h2' t1 t2).
Proof. exact (@lem1187562 A h1' h2' t1 t2). Qed.
Lemma lem1187564 {A : Type'} (h : A) (l2 : list A) (t : list A) (l3 : list A) : ((term58 A h t l2) = (term58 A h t l3)) = (term64 A h l2 t l3).
Proof. exact (@lem1187563 A h h (@List.app A t l2) (@List.app A t l3)). Qed.
Lemma lem1187568 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1187569 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1187568 A x). Qed.
Lemma lem1187570 {A : Type'} (h : A) : (h = h) = True.
Proof. exact (@lem1187569 A h). Qed.
Lemma lem1187571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1187572 {A : Type'} (h : A) : (term65 A h) = (and True).
Proof. exact (MK_COMB (@lem1187571) (@lem1187570 A h)). Qed.
Lemma lem1187574 {A : Type'} (l2 : list A) (l3 : list A) (t : list A) (h1 : term8 A t) : ((@List.app A t l2) = (@List.app A t l3)) = (l2 = l3).
Proof. exact (EQ_MP (@lem1187536 A t l2 l3) (@lem1187535 A l2 l3 t h1)). Qed.
Lemma lem1187575 {A : Type'} (l2 : list A) (l3 : list A) (t : list A) (h1 : term8 A t) : ((@List.app A t l2) = (@List.app A t l3)) = (l2 = l3).
Proof. exact (@lem1187574 A l2 l3 t h1). Qed.
Lemma lem1187578 {A : Type'} (h : A) (l2 : list A) (l3 : list A) (t : list A) (h1 : term8 A t) : (term64 A h l2 t l3) = (term66 A l2 l3).
Proof. exact (MK_COMB (@lem1187572 A h) (@lem1187575 A l2 l3 t h1)). Qed.
Lemma lem1187580 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1187581 {A : Type'} (l2 : list A) (l3 : list A) : (term66 A l2 l3) = (l2 = l3).
Proof. exact (@lem1187580 (l2 = l3)). Qed.
Lemma lem1187584 {A : Type'} (h : A) (l2 : list A) (l3 : list A) (t : list A) (h1 : term8 A t) : (term64 A h l2 t l3) = (l2 = l3).
Proof. exact (TRANS (@lem1187578 A h l2 l3 t h1) (@lem1187581 A l2 l3)). Qed.
Lemma lem1187585 {A : Type'} (h : A) (l2 : list A) (l3 : list A) (t : list A) (h1 : term8 A t) : ((term58 A h t l2) = (term58 A h t l3)) = (l2 = l3).
Proof. exact (TRANS (@lem1187564 A h l2 t l3) (@lem1187584 A h l2 l3 t h1)). Qed.
Lemma lem1187586 {A : Type'} (h : A) (l2 : list A) (l3 : list A) (t : list A) (h1 : term8 A t) : ((term57 A h t l2) = (term57 A h t l3)) = (l2 = l3).
Proof. exact (TRANS (@lem1187560 A l2 h t l3) (@lem1187585 A h l2 l3 t h1)). Qed.
Lemma lem1187587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1187588 {A : Type'} (h : A) (l2 : list A) (l3 : list A) (t : list A) (h1 : term8 A t) : (term67 A l2 h t l3) = (term35 A l2 l3).
Proof. exact (MK_COMB (@lem1187587) (@lem1187586 A h l2 l3 t h1)). Qed.
Lemma lem1187591 {A : Type'} (l2 : list A) (l3 : list A) : (l2 = l3) = (l2 = l3).
Proof. exact (eq_refl (l2 = l3)). Qed.
Lemma lem1187592 {A : Type'} (h : A) (l2 : list A) (l3 : list A) (t : list A) (h1 : term8 A t) : (((term57 A h t l2) = (term57 A h t l3)) = (l2 = l3)) = ((l2 = l3) = (l2 = l3)).
Proof. exact (MK_COMB (@lem1187588 A h l2 l3 t h1) (@lem1187591 A l2 l3)). Qed.
Lemma lem1187594 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1187595 (x : Prop) : (x = x) = True.
Proof. exact (@lem1187594 Prop x). Qed.
Lemma lem1187596 {A : Type'} (l2 : list A) (l3 : list A) : ((l2 = l3) = (l2 = l3)) = True.
Proof. exact (@lem1187595 (l2 = l3)). Qed.
Lemma lem1187597 {A : Type'} (h : A) (l2 : list A) (l3 : list A) (t : list A) (h1 : term8 A t) : (((term57 A h t l2) = (term57 A h t l3)) = (l2 = l3)) = True.
Proof. exact (TRANS (@lem1187592 A h l2 l3 t h1) (@lem1187596 A l2 l3)). Qed.
Lemma lem1187598 {A : Type'} (h : A) (l2 : list A) (t : list A) (h1 : term8 A t) : (term68 A h t l2) = (term37 A).
Proof. exact (fun_ext (fun l3 : list A => @lem1187597 A h l2 l3 t h1)). Qed.
Lemma lem1187599 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1187600 {A : Type'} (h : A) (l2 : list A) (t : list A) (h1 : term8 A t) : (term69 A h t l2) = (term39 A).
Proof. exact (MK_COMB (@lem1187599 A) (@lem1187598 A h l2 t h1)). Qed.
Lemma lem1187602 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1187603 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (@lem1187602 (list A) t). Qed.
Lemma lem1187604 {A : Type'} : (term39 A) = True.
Proof. exact (@lem1187603 A True). Qed.
Lemma lem1187605 {A : Type'} (h : A) (l2 : list A) (t : list A) (h1 : term8 A t) : (term69 A h t l2) = True.
Proof. exact (TRANS (@lem1187600 A h l2 t h1) (@lem1187604 A)). Qed.
Lemma lem1187606 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term70 A h t) = (term37 A).
Proof. exact (fun_ext (fun l2 : list A => @lem1187605 A h l2 t h1)). Qed.
Lemma lem1187607 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1187608 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term12 A h t) = (term39 A).
Proof. exact (MK_COMB (@lem1187607 A) (@lem1187606 A h t h1)). Qed.
Lemma lem1187610 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1187611 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (@lem1187610 (list A) t). Qed.
Lemma lem1187612 {A : Type'} : (term39 A) = True.
Proof. exact (@lem1187611 A True). Qed.
Lemma lem1187613 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term12 A h t) = True.
Proof. exact (TRANS (@lem1187608 A h t h1) (@lem1187612 A)). Qed.
Lemma lem1187614 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : True = (term12 A h t).
Proof. exact (SYM (@lem1187613 A h t h1)). Qed.
Lemma lem1187615 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : term12 A h t.
Proof. exact (EQ_MP (@lem1187614 A h t h1) (@lem0)). Qed.
Lemma lem1187616 {A : Type'} (h : A) (t : list A) : term14 A h t.
Proof. exact (fun h0 : term8 A t => @lem1187615 A h t h0). Qed.
Lemma lem1187621 {A : Type'} (h : A) : term18 A h.
Proof. exact (fun t : list A => @lem1187616 A h t). Qed.
Lemma lem1187626 {A : Type'} : term22 A.
Proof. exact (fun h : A => @lem1187621 A h). Qed.
Lemma lem1187627 {A : Type'} : term24 A.
Proof. exact (conj (@lem1187505 A) (@lem1187626 A)). Qed.
Lemma lem1187628 {A : Type'} : term29 A.
Proof. exact (@lem1187424 A (@lem1187627 A)). Qed.
