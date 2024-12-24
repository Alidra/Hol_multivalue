Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SET_OF_LIST_term_abbrevs.
Require Import FINITE_RULES_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm4785464_spec.
Require Import thm4785470_spec.
Require Import thm4785471_spec.
Require Import thm7_spec.
Lemma lem4788388 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem4788389 {_110366 : Type'} (P : type1143 _110366) : term0 _110366 P.
Proof. exact (@lem4788388 _110366 P). Qed.
Lemma lem4788390 {_110366 : Type'} : term1 _110366.
Proof. exact (@lem4788389 _110366 (term2 _110366)). Qed.
Lemma lem4788391 {_110366 : Type'} : (term3 _110366) = (term4 _110366).
Proof. exact (eq_refl (term3 _110366)). Qed.
Lemma lem4788392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4788393 {_110366 : Type'} : (term5 _110366) = (term6 _110366).
Proof. exact (MK_COMB (@lem4788392) (@lem4788391 _110366)). Qed.
Lemma lem4788394 {_110366 : Type'} (t : list _110366) : (term7 _110366 t) = (term8 _110366 t).
Proof. exact (eq_refl (term7 _110366 t)). Qed.
Lemma lem4788395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4788396 {_110366 : Type'} (t : list _110366) : (term9 _110366 t) = (term10 _110366 t).
Proof. exact (MK_COMB (@lem4788395) (@lem4788394 _110366 t)). Qed.
Lemma lem4788397 {_110366 : Type'} (h : _110366) (t : list _110366) : (term11 _110366 h t) = (term12 _110366 h t).
Proof. exact (eq_refl (term11 _110366 h t)). Qed.
Lemma lem4788398 {_110366 : Type'} (h : _110366) (t : list _110366) : (term13 _110366 h t) = (term14 _110366 h t).
Proof. exact (MK_COMB (@lem4788396 _110366 t) (@lem4788397 _110366 h t)). Qed.
Lemma lem4788399 {_110366 : Type'} (h : _110366) : (term15 _110366 h) = (term16 _110366 h).
Proof. exact (fun_ext (fun t : list _110366 => @lem4788398 _110366 h t)). Qed.
Lemma lem4788400 {_110366 : Type'} : (@all (list _110366)) = (@all (list _110366)).
Proof. exact (eq_refl (@all (list _110366))). Qed.
Lemma lem4788401 {_110366 : Type'} (h : _110366) : (term17 _110366 h) = (term18 _110366 h).
Proof. exact (MK_COMB (@lem4788400 _110366) (@lem4788399 _110366 h)). Qed.
Lemma lem4788402 {_110366 : Type'} : (term19 _110366) = (term20 _110366).
Proof. exact (fun_ext (fun h : _110366 => @lem4788401 _110366 h)). Qed.
Lemma lem4788403 {_110366 : Type'} : (@all _110366) = (@all _110366).
Proof. exact (eq_refl (@all _110366)). Qed.
Lemma lem4788404 {_110366 : Type'} : (term21 _110366) = (term22 _110366).
Proof. exact (MK_COMB (@lem4788403 _110366) (@lem4788402 _110366)). Qed.
Lemma lem4788405 {_110366 : Type'} : (term23 _110366) = (term24 _110366).
Proof. exact (MK_COMB (@lem4788393 _110366) (@lem4788404 _110366)). Qed.
Lemma lem4788406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4788407 {_110366 : Type'} : (term25 _110366) = (term26 _110366).
Proof. exact (MK_COMB (@lem4788406) (@lem4788405 _110366)). Qed.
Lemma lem4788408 {_110366 : Type'} (l : list _110366) : (term7 _110366 l) = (term8 _110366 l).
Proof. exact (eq_refl (term7 _110366 l)). Qed.
Lemma lem4788409 {_110366 : Type'} : (term27 _110366) = (term2 _110366).
Proof. exact (fun_ext (fun l : list _110366 => @lem4788408 _110366 l)). Qed.
Lemma lem4788410 {_110366 : Type'} : (@all (list _110366)) = (@all (list _110366)).
Proof. exact (eq_refl (@all (list _110366))). Qed.
Lemma lem4788411 {_110366 : Type'} : (term28 _110366) = (term29 _110366).
Proof. exact (MK_COMB (@lem4788410 _110366) (@lem4788409 _110366)). Qed.
Lemma lem4788412 {_110366 : Type'} : (term1 _110366) = (term30 _110366).
Proof. exact (MK_COMB (@lem4788407 _110366) (@lem4788411 _110366)). Qed.
Lemma lem4788413 {_110366 : Type'} : term30 _110366.
Proof. exact (EQ_MP (@lem4788412 _110366) (@lem4788390 _110366)). Qed.
Lemma lem4788414 {_110366 : Type'} (t : list _110366) (h1 : term8 _110366 t) : term8 _110366 t.
Proof. exact (h1). Qed.
Lemma lem4788431 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem4788432 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem4788437 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
Lemma lem4788438 {_110366 : Type'} : (@set_of_list _110366 (@nil _110366)) = (@EMPTY _110366).
Proof. exact (@lem4788437 _110366). Qed.
Lemma lem4788439 {_110366 : Type'} : (@FINITE _110366) = (@FINITE _110366).
Proof. exact (eq_refl (@FINITE _110366)). Qed.
Lemma lem4788440 {_110366 : Type'} : (term4 _110366) = (@FINITE _110366 (@EMPTY _110366)).
Proof. exact (MK_COMB (@lem4788439 _110366) (@lem4788438 _110366)). Qed.
Lemma lem4788442 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem4788432 A) (@lem4788431 A)). Qed.
Lemma lem4788443 {_110366 : Type'} : (@FINITE _110366 (@EMPTY _110366)) = True.
Proof. exact (@lem4788442 _110366). Qed.
Lemma lem4788444 {_110366 : Type'} : (term4 _110366) = True.
Proof. exact (TRANS (@lem4788440 _110366) (@lem4788443 _110366)). Qed.
Lemma lem4788445 {_110366 : Type'} : True = (term4 _110366).
Proof. exact (SYM (@lem4788444 _110366)). Qed.
Lemma lem4788446 {_110366 : Type'} : term4 _110366.
Proof. exact (EQ_MP (@lem4788445 _110366) (@lem0)). Qed.
Lemma lem4788447 {A : Type'} : term31 A.
Proof. exact (proj2 (@lem3197565 A)). Qed.
Lemma lem4788448 {A : Type'} (x : A) : term32 A x.
Proof. exact (@lem4788447 A x). Qed.
Lemma lem4788449 {A : Type'} (x : A) : (term32 A x) = (term33 A x).
Proof. exact (eq_refl (term32 A x)). Qed.
Lemma lem4788450 {A : Type'} (x : A) : term33 A x.
Proof. exact (EQ_MP (@lem4788449 A x) (@lem4788448 A x)). Qed.
Lemma lem4788451 {A : Type'} (x : A) (s : A -> Prop) : term34 A x s.
Proof. exact (@lem4788450 A x s). Qed.
Lemma lem4788452 {A : Type'} (x : A) (s : A -> Prop) : (term34 A x s) = (term35 A x s).
Proof. exact (eq_refl (term34 A x s)). Qed.
Lemma lem4788453 {A : Type'} (x : A) (s : A -> Prop) : term35 A x s.
Proof. exact (EQ_MP (@lem4788452 A x s) (@lem4788451 A x s)). Qed.
Lemma lem4788454 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4788455 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term36 A x s.
Proof. exact (@lem4788453 A x s (@lem4788454 A s h1)). Qed.
Lemma lem4788456 {A : Type'} (x : A) (s : A -> Prop) : (term36 A x s) = ((term36 A x s) = True).
Proof. exact (@lem7 (term36 A x s)). Qed.
Lemma lem4788457 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term36 A x s) = True.
Proof. exact (EQ_MP (@lem4788456 A x s) (@lem4788455 A x s h1)). Qed.
Lemma lem4788468 {_110366 : Type'} (t : list _110366) : (term8 _110366 t) = ((term8 _110366 t) = True).
Proof. exact (@lem7 (term8 _110366 t)). Qed.
Lemma lem4788471 {A : Type'} (h : A) (t : list A) : (term37 A h t) = (term38 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4788472 {_110366 : Type'} (h : _110366) (t : list _110366) : (term37 _110366 h t) = (term38 _110366 h t).
Proof. exact (@lem4788471 _110366 h t). Qed.
Lemma lem4788473 {_110366 : Type'} : (@FINITE _110366) = (@FINITE _110366).
Proof. exact (eq_refl (@FINITE _110366)). Qed.
Lemma lem4788474 {_110366 : Type'} (h : _110366) (t : list _110366) : (term12 _110366 h t) = (term39 _110366 h t).
Proof. exact (MK_COMB (@lem4788473 _110366) (@lem4788472 _110366 h t)). Qed.
Lemma lem4788476 {A : Type'} (x : A) (s : A -> Prop) : term40 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4788457 A x s h0). Qed.
Lemma lem4788477 {_110366 : Type'} (x : _110366) (s : _110366 -> Prop) : term40 _110366 x s.
Proof. exact (@lem4788476 _110366 x s). Qed.
Lemma lem4788478 {_110366 : Type'} (h : _110366) (t : list _110366) : term41 _110366 h t.
Proof. exact (@lem4788477 _110366 h (@set_of_list _110366 t)). Qed.
Lemma lem4788480 {_110366 : Type'} (t : list _110366) (h1 : term8 _110366 t) : (term8 _110366 t) = True.
Proof. exact (EQ_MP (@lem4788468 _110366 t) (@lem4788414 _110366 t h1)). Qed.
Lemma lem4788481 {_110366 : Type'} (t : list _110366) (h1 : term8 _110366 t) : True = (term8 _110366 t).
Proof. exact (SYM (@lem4788480 _110366 t h1)). Qed.
Lemma lem4788482 {_110366 : Type'} (t : list _110366) (h1 : term8 _110366 t) : term8 _110366 t.
Proof. exact (EQ_MP (@lem4788481 _110366 t h1) (@lem0)). Qed.
Lemma lem4788483 {_110366 : Type'} (h : _110366) (t : list _110366) (h1 : term8 _110366 t) : (term39 _110366 h t) = True.
Proof. exact (@lem4788478 _110366 h t (@lem4788482 _110366 t h1)). Qed.
Lemma lem4788484 {_110366 : Type'} (h : _110366) (t : list _110366) (h1 : term8 _110366 t) : (term12 _110366 h t) = True.
Proof. exact (TRANS (@lem4788474 _110366 h t) (@lem4788483 _110366 h t h1)). Qed.
Lemma lem4788485 {_110366 : Type'} (h : _110366) (t : list _110366) (h1 : term8 _110366 t) : True = (term12 _110366 h t).
Proof. exact (SYM (@lem4788484 _110366 h t h1)). Qed.
Lemma lem4788486 {_110366 : Type'} (h : _110366) (t : list _110366) (h1 : term8 _110366 t) : term12 _110366 h t.
Proof. exact (EQ_MP (@lem4788485 _110366 h t h1) (@lem0)). Qed.
Lemma lem4788487 {_110366 : Type'} (h : _110366) (t : list _110366) : term14 _110366 h t.
Proof. exact (fun h0 : term8 _110366 t => @lem4788486 _110366 h t h0). Qed.
Lemma lem4788492 {_110366 : Type'} (h : _110366) : term18 _110366 h.
Proof. exact (fun t : list _110366 => @lem4788487 _110366 h t). Qed.
Lemma lem4788497 {_110366 : Type'} : term22 _110366.
Proof. exact (fun h : _110366 => @lem4788492 _110366 h). Qed.
Lemma lem4788498 {_110366 : Type'} : term24 _110366.
Proof. exact (conj (@lem4788446 _110366) (@lem4788497 _110366)). Qed.
Lemma lem4788499 {_110366 : Type'} : term29 _110366.
Proof. exact (@lem4788413 _110366 (@lem4788498 _110366)). Qed.
