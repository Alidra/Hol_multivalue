Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_SND_ZIP_term_abbrevs.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import ZIP_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm1097797_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm82_spec.
Lemma lem1155431 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1155432 {_27145 : Type'} (P : type1143 _27145) : term0 _27145 P.
Proof. exact (@lem1155431 _27145 P). Qed.
Lemma lem1155433 {_27145 _27147 : Type'} : term1 _27145 _27147.
Proof. exact (@lem1155432 _27145 (term2 _27145 _27147)). Qed.
Lemma lem1155434 {_27145 _27147 : Type'} : (term3 _27145 _27147) = (term4 _27145 _27147).
Proof. exact (eq_refl (term3 _27145 _27147)). Qed.
Lemma lem1155435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1155436 {_27145 _27147 : Type'} : (term5 _27145 _27147) = (term6 _27145 _27147).
Proof. exact (MK_COMB (@lem1155435) (@lem1155434 _27145 _27147)). Qed.
Lemma lem1155437 {_27145 _27147 : Type'} (t : list _27145) : (term7 _27145 _27147 t) = (term8 _27145 _27147 t).
Proof. exact (eq_refl (term7 _27145 _27147 t)). Qed.
Lemma lem1155438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1155439 {_27145 _27147 : Type'} (t : list _27145) : (term9 _27145 _27147 t) = (term10 _27145 _27147 t).
Proof. exact (MK_COMB (@lem1155438) (@lem1155437 _27145 _27147 t)). Qed.
Lemma lem1155440 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term11 _27145 _27147 h t) = (term12 _27145 _27147 h t).
Proof. exact (eq_refl (term11 _27145 _27147 h t)). Qed.
Lemma lem1155441 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term13 _27145 _27147 h t) = (term14 _27145 _27147 h t).
Proof. exact (MK_COMB (@lem1155439 _27145 _27147 t) (@lem1155440 _27145 _27147 h t)). Qed.
Lemma lem1155442 {_27145 _27147 : Type'} (h : _27145) : (term15 _27145 _27147 h) = (term16 _27145 _27147 h).
Proof. exact (fun_ext (fun t : list _27145 => @lem1155441 _27145 _27147 h t)). Qed.
Lemma lem1155443 {_27145 : Type'} : (@all (list _27145)) = (@all (list _27145)).
Proof. exact (eq_refl (@all (list _27145))). Qed.
Lemma lem1155444 {_27145 _27147 : Type'} (h : _27145) : (term17 _27145 _27147 h) = (term18 _27145 _27147 h).
Proof. exact (MK_COMB (@lem1155443 _27145) (@lem1155442 _27145 _27147 h)). Qed.
Lemma lem1155445 {_27145 _27147 : Type'} : (term19 _27145 _27147) = (term20 _27145 _27147).
Proof. exact (fun_ext (fun h : _27145 => @lem1155444 _27145 _27147 h)). Qed.
Lemma lem1155446 {_27145 : Type'} : (@all _27145) = (@all _27145).
Proof. exact (eq_refl (@all _27145)). Qed.
Lemma lem1155447 {_27145 _27147 : Type'} : (term21 _27145 _27147) = (term22 _27145 _27147).
Proof. exact (MK_COMB (@lem1155446 _27145) (@lem1155445 _27145 _27147)). Qed.
Lemma lem1155448 {_27145 _27147 : Type'} : (term23 _27145 _27147) = (term24 _27145 _27147).
Proof. exact (MK_COMB (@lem1155436 _27145 _27147) (@lem1155447 _27145 _27147)). Qed.
Lemma lem1155449 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1155450 {_27145 _27147 : Type'} : (term25 _27145 _27147) = (term26 _27145 _27147).
Proof. exact (MK_COMB (@lem1155449) (@lem1155448 _27145 _27147)). Qed.
Lemma lem1155451 {_27145 _27147 : Type'} (l1 : list _27145) : (term7 _27145 _27147 l1) = (term8 _27145 _27147 l1).
Proof. exact (eq_refl (term7 _27145 _27147 l1)). Qed.
Lemma lem1155452 {_27145 _27147 : Type'} : (term27 _27145 _27147) = (term2 _27145 _27147).
Proof. exact (fun_ext (fun l1 : list _27145 => @lem1155451 _27145 _27147 l1)). Qed.
Lemma lem1155453 {_27145 : Type'} : (@all (list _27145)) = (@all (list _27145)).
Proof. exact (eq_refl (@all (list _27145))). Qed.
Lemma lem1155454 {_27145 _27147 : Type'} : (term28 _27145 _27147) = (term29 _27145 _27147).
Proof. exact (MK_COMB (@lem1155453 _27145) (@lem1155452 _27145 _27147)). Qed.
Lemma lem1155455 {_27145 _27147 : Type'} : (term1 _27145 _27147) = (term30 _27145 _27147).
Proof. exact (MK_COMB (@lem1155450 _27145 _27147) (@lem1155454 _27145 _27147)). Qed.
Lemma lem1155456 {_27145 _27147 : Type'} : term30 _27145 _27147.
Proof. exact (EQ_MP (@lem1155455 _27145 _27147) (@lem1155433 _27145 _27147)). Qed.
Lemma lem1155457 {_27145 _27147 : Type'} (t : list _27145) (h1 : term8 _27145 _27147 t) : term8 _27145 _27147 t.
Proof. exact (h1). Qed.
Lemma lem1155459 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1155460 {_27147 : Type'} (P : type1143 _27147) : term0 _27147 P.
Proof. exact (@lem1155459 _27147 P). Qed.
Lemma lem1155461 {_27145 _27147 : Type'} : term31 _27145 _27147.
Proof. exact (@lem1155460 _27147 (term32 _27145 _27147)). Qed.
Lemma lem1155462 {_27145 _27147 : Type'} : (term33 _27145 _27147) = (term34 _27145 _27147).
Proof. exact (eq_refl (term33 _27145 _27147)). Qed.
Lemma lem1155463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1155464 {_27145 _27147 : Type'} : (term35 _27145 _27147) = (term36 _27145 _27147).
Proof. exact (MK_COMB (@lem1155463) (@lem1155462 _27145 _27147)). Qed.
Lemma lem1155465 {_27145 _27147 : Type'} (t : list _27147) : (term37 _27145 _27147 t) = (term38 _27145 _27147 t).
Proof. exact (eq_refl (term37 _27145 _27147 t)). Qed.
Lemma lem1155466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1155467 {_27145 _27147 : Type'} (t : list _27147) : (term39 _27145 _27147 t) = (term40 _27145 _27147 t).
Proof. exact (MK_COMB (@lem1155466) (@lem1155465 _27145 _27147 t)). Qed.
Lemma lem1155468 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : (term41 _27145 _27147 h t) = (term42 _27145 _27147 h t).
Proof. exact (eq_refl (term41 _27145 _27147 h t)). Qed.
Lemma lem1155469 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : (term43 _27145 _27147 h t) = (term44 _27145 _27147 h t).
Proof. exact (MK_COMB (@lem1155467 _27145 _27147 t) (@lem1155468 _27145 _27147 h t)). Qed.
Lemma lem1155470 {_27145 _27147 : Type'} (h : _27147) : (term45 _27145 _27147 h) = (term46 _27145 _27147 h).
Proof. exact (fun_ext (fun t : list _27147 => @lem1155469 _27145 _27147 h t)). Qed.
Lemma lem1155471 {_27147 : Type'} : (@all (list _27147)) = (@all (list _27147)).
Proof. exact (eq_refl (@all (list _27147))). Qed.
Lemma lem1155472 {_27145 _27147 : Type'} (h : _27147) : (term47 _27145 _27147 h) = (term48 _27145 _27147 h).
Proof. exact (MK_COMB (@lem1155471 _27147) (@lem1155470 _27145 _27147 h)). Qed.
Lemma lem1155473 {_27145 _27147 : Type'} : (term49 _27145 _27147) = (term50 _27145 _27147).
Proof. exact (fun_ext (fun h : _27147 => @lem1155472 _27145 _27147 h)). Qed.
Lemma lem1155474 {_27147 : Type'} : (@all _27147) = (@all _27147).
Proof. exact (eq_refl (@all _27147)). Qed.
Lemma lem1155475 {_27145 _27147 : Type'} : (term51 _27145 _27147) = (term52 _27145 _27147).
Proof. exact (MK_COMB (@lem1155474 _27147) (@lem1155473 _27145 _27147)). Qed.
Lemma lem1155476 {_27145 _27147 : Type'} : (term53 _27145 _27147) = (term54 _27145 _27147).
Proof. exact (MK_COMB (@lem1155464 _27145 _27147) (@lem1155475 _27145 _27147)). Qed.
Lemma lem1155477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1155478 {_27145 _27147 : Type'} : (term55 _27145 _27147) = (term56 _27145 _27147).
Proof. exact (MK_COMB (@lem1155477) (@lem1155476 _27145 _27147)). Qed.
Lemma lem1155479 {_27145 _27147 : Type'} (l2 : list _27147) : (term37 _27145 _27147 l2) = (term38 _27145 _27147 l2).
Proof. exact (eq_refl (term37 _27145 _27147 l2)). Qed.
Lemma lem1155480 {_27145 _27147 : Type'} : (term57 _27145 _27147) = (term32 _27145 _27147).
Proof. exact (fun_ext (fun l2 : list _27147 => @lem1155479 _27145 _27147 l2)). Qed.
Lemma lem1155481 {_27147 : Type'} : (@all (list _27147)) = (@all (list _27147)).
Proof. exact (eq_refl (@all (list _27147))). Qed.
Lemma lem1155482 {_27145 _27147 : Type'} : (term58 _27145 _27147) = (term4 _27145 _27147).
Proof. exact (MK_COMB (@lem1155481 _27147) (@lem1155480 _27145 _27147)). Qed.
Lemma lem1155483 {_27145 _27147 : Type'} : (term31 _27145 _27147) = (term59 _27145 _27147).
Proof. exact (MK_COMB (@lem1155478 _27145 _27147) (@lem1155482 _27145 _27147)). Qed.
Lemma lem1155484 {_27145 _27147 : Type'} : term59 _27145 _27147.
Proof. exact (EQ_MP (@lem1155483 _27145 _27147) (@lem1155461 _27145 _27147)). Qed.
Lemma lem1155487 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1155488 {_27147 : Type'} (P : type1143 _27147) : term0 _27147 P.
Proof. exact (@lem1155487 _27147 P). Qed.
Lemma lem1155489 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : term60 _27145 _27147 h t.
Proof. exact (@lem1155488 _27147 (term61 _27145 _27147 h t)). Qed.
Lemma lem1155490 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term62 _27145 _27147 h t) = (term63 _27145 _27147 h t).
Proof. exact (eq_refl (term62 _27145 _27147 h t)). Qed.
Lemma lem1155491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1155492 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term64 _27145 _27147 h t) = (term65 _27145 _27147 h t).
Proof. exact (MK_COMB (@lem1155491) (@lem1155490 _27145 _27147 h t)). Qed.
Lemma lem1155493 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (t' : list _27147) : (term66 _27145 _27147 h t t') = (term67 _27145 _27147 h t t').
Proof. exact (eq_refl (term66 _27145 _27147 h t t')). Qed.
Lemma lem1155494 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1155495 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (t' : list _27147) : (term68 _27145 _27147 h t t') = (term69 _27145 _27147 h t t').
Proof. exact (MK_COMB (@lem1155494) (@lem1155493 _27145 _27147 h t t')). Qed.
Lemma lem1155496 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) (t' : list _27147) : (term70 _27145 _27147 h t h' t') = (term71 _27145 _27147 h t h' t').
Proof. exact (eq_refl (term70 _27145 _27147 h t h' t')). Qed.
Lemma lem1155497 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) (t' : list _27147) : (term72 _27145 _27147 h t h' t') = (term73 _27145 _27147 h t h' t').
Proof. exact (MK_COMB (@lem1155495 _27145 _27147 h t t') (@lem1155496 _27145 _27147 h t h' t')). Qed.
Lemma lem1155498 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) : (term74 _27145 _27147 h t h') = (term75 _27145 _27147 h t h').
Proof. exact (fun_ext (fun t' : list _27147 => @lem1155497 _27145 _27147 h t h' t')). Qed.
Lemma lem1155499 {_27147 : Type'} : (@all (list _27147)) = (@all (list _27147)).
Proof. exact (eq_refl (@all (list _27147))). Qed.
Lemma lem1155500 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) : (term76 _27145 _27147 h t h') = (term77 _27145 _27147 h t h').
Proof. exact (MK_COMB (@lem1155499 _27147) (@lem1155498 _27145 _27147 h t h')). Qed.
Lemma lem1155501 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term78 _27145 _27147 h t) = (term79 _27145 _27147 h t).
Proof. exact (fun_ext (fun h' : _27147 => @lem1155500 _27145 _27147 h t h')). Qed.
Lemma lem1155502 {_27147 : Type'} : (@all _27147) = (@all _27147).
Proof. exact (eq_refl (@all _27147)). Qed.
Lemma lem1155503 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term80 _27145 _27147 h t) = (term81 _27145 _27147 h t).
Proof. exact (MK_COMB (@lem1155502 _27147) (@lem1155501 _27145 _27147 h t)). Qed.
Lemma lem1155504 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term82 _27145 _27147 h t) = (term83 _27145 _27147 h t).
Proof. exact (MK_COMB (@lem1155492 _27145 _27147 h t) (@lem1155503 _27145 _27147 h t)). Qed.
Lemma lem1155505 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1155506 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term84 _27145 _27147 h t) = (term85 _27145 _27147 h t).
Proof. exact (MK_COMB (@lem1155505) (@lem1155504 _27145 _27147 h t)). Qed.
Lemma lem1155507 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (l2 : list _27147) : (term66 _27145 _27147 h t l2) = (term67 _27145 _27147 h t l2).
Proof. exact (eq_refl (term66 _27145 _27147 h t l2)). Qed.
Lemma lem1155508 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term86 _27145 _27147 h t) = (term61 _27145 _27147 h t).
Proof. exact (fun_ext (fun l2 : list _27147 => @lem1155507 _27145 _27147 h t l2)). Qed.
Lemma lem1155509 {_27147 : Type'} : (@all (list _27147)) = (@all (list _27147)).
Proof. exact (eq_refl (@all (list _27147))). Qed.
Lemma lem1155510 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term87 _27145 _27147 h t) = (term12 _27145 _27147 h t).
Proof. exact (MK_COMB (@lem1155509 _27147) (@lem1155508 _27145 _27147 h t)). Qed.
Lemma lem1155511 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term60 _27145 _27147 h t) = (term88 _27145 _27147 h t).
Proof. exact (MK_COMB (@lem1155506 _27145 _27147 h t) (@lem1155510 _27145 _27147 h t)). Qed.
Lemma lem1155512 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : term88 _27145 _27147 h t.
Proof. exact (EQ_MP (@lem1155511 _27145 _27147 h t) (@lem1155489 _27145 _27147 h t)). Qed.
Lemma lem1155548 {A B : Type'} : term89 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1155549 {A B : Type'} (f : A -> B) : term90 A B f.
Proof. exact (@lem1155548 A B f). Qed.
Lemma lem1155550 {A B : Type'} (f : A -> B) : (term90 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term90 A B f)). Qed.
Lemma lem1155571 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1155572 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem1155571 p q p' q'). Qed.
Lemma lem1155573 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem1155572 p q p'). Qed.
Lemma lem1155574 {_27145 _27147 : Type'} : term94 _27145 _27147.
Proof. exact (@lem1155573 ((@List.length _27145 (@nil _27145)) = (@List.length _27147 (@nil _27147))) ((term95 _27145 _27147) = (@nil _27147))). Qed.
Lemma lem1155575 {_27145 _27147 : Type'} (p' : Prop) : term96 _27145 _27147 p'.
Proof. exact (@lem1155574 _27145 _27147 p'). Qed.
Lemma lem1155576 {_27145 _27147 : Type'} (p' : Prop) : (term96 _27145 _27147 p') = (term97 _27145 _27147 p').
Proof. exact (eq_refl (term96 _27145 _27147 p')). Qed.
Lemma lem1155577 {_27145 _27147 : Type'} (p' : Prop) : term97 _27145 _27147 p'.
Proof. exact (EQ_MP (@lem1155576 _27145 _27147 p') (@lem1155575 _27145 _27147 p')). Qed.
Lemma lem1155578 {_27145 _27147 : Type'} (p' : Prop) (q' : Prop) : term98 _27145 _27147 p' q'.
Proof. exact (@lem1155577 _27145 _27147 p' q'). Qed.
Lemma lem1155579 {_27145 _27147 : Type'} (p' : Prop) (q' : Prop) : (term98 _27145 _27147 p' q') = (term99 _27145 _27147 p' q').
Proof. exact (eq_refl (term98 _27145 _27147 p' q')). Qed.
Lemma lem1155580 {_27145 _27147 : Type'} (p' : Prop) (q' : Prop) : term99 _27145 _27147 p' q'.
Proof. exact (EQ_MP (@lem1155579 _27145 _27147 p' q') (@lem1155578 _27145 _27147 p' q')). Qed.
Lemma lem1155584 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1155585 {_27145 : Type'} : (@List.length _27145 (@nil _27145)) = (NUMERAL 0).
Proof. exact (@lem1155584 _27145). Qed.
Lemma lem1155586 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1155587 {_27145 : Type'} : (term100 _27145) = term101.
Proof. exact (MK_COMB (@lem1155586) (@lem1155585 _27145)). Qed.
Lemma lem1155589 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1155590 {_27147 : Type'} : (@List.length _27147 (@nil _27147)) = (NUMERAL 0).
Proof. exact (@lem1155589 _27147). Qed.
Lemma lem1155591 {_27145 _27147 : Type'} : ((@List.length _27145 (@nil _27145)) = (@List.length _27147 (@nil _27147))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1155587 _27145) (@lem1155590 _27147)). Qed.
Lemma lem1155593 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1155594 (x : nat) : (x = x) = True.
Proof. exact (@lem1155593 nat x). Qed.
Lemma lem1155595 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1155594 (NUMERAL 0)). Qed.
Lemma lem1155596 {_27145 _27147 : Type'} : ((@List.length _27145 (@nil _27145)) = (@List.length _27147 (@nil _27147))) = True.
Proof. exact (TRANS (@lem1155591 _27145 _27147) (@lem1155595)). Qed.
Lemma lem1155597 {_27145 _27147 : Type'} (q' : Prop) : term102 _27145 _27147 q'.
Proof. exact (@lem1155580 _27145 _27147 True q'). Qed.
Lemma lem1155598 {_27145 _27147 : Type'} (q' : Prop) : term103 _27145 _27147 q'.
Proof. exact (@lem1155597 _27145 _27147 q' (@lem1155596 _27145 _27147)). Qed.
Lemma lem1155607 {_25738 _25739 : Type'} : (@ZIP _25738 _25739 (@nil _25738) (@nil _25739)) = (@nil (prod _25738 _25739)).
Proof. exact (proj1 (@lem1109008 _25738 _25739 Prop Prop (@el Prop) (@el Prop) (@el (list Prop)) (@el (list Prop)))). Qed.
Lemma lem1155608 {_27145 _27147 : Type'} : (@ZIP _27145 _27147 (@nil _27145) (@nil _27147)) = (@nil (prod _27145 _27147)).
Proof. exact (@lem1155607 _27145 _27147). Qed.
Lemma lem1155609 {_27145 _27147 : Type'} : (@List.map (prod _27145 _27147) _27147 (@snd _27145 _27147)) = (@List.map (prod _27145 _27147) _27147 (@snd _27145 _27147)).
Proof. exact (eq_refl (@List.map (prod _27145 _27147) _27147 (@snd _27145 _27147))). Qed.
Lemma lem1155610 {_27145 _27147 : Type'} : (term95 _27145 _27147) = (@List.map (prod _27145 _27147) _27147 (@snd _27145 _27147) (@nil (prod _27145 _27147))).
Proof. exact (MK_COMB (@lem1155609 _27145 _27147) (@lem1155608 _27145 _27147)). Qed.
Lemma lem1155612 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1155550 A B f) (@lem1155549 A B f)). Qed.
Lemma lem1155613 {_27145 _27147 : Type'} (f : type1208 _27145 _27147) : (@List.map (prod _27145 _27147) _27147 f (@nil (prod _27145 _27147))) = (@nil _27147).
Proof. exact (@lem1155612 (prod _27145 _27147) _27147 f). Qed.
Lemma lem1155614 {_27145 _27147 : Type'} : (@List.map (prod _27145 _27147) _27147 (@snd _27145 _27147) (@nil (prod _27145 _27147))) = (@nil _27147).
Proof. exact (@lem1155613 _27145 _27147 (@snd _27145 _27147)). Qed.
Lemma lem1155615 {_27145 _27147 : Type'} : (term95 _27145 _27147) = (@nil _27147).
Proof. exact (TRANS (@lem1155610 _27145 _27147) (@lem1155614 _27145 _27147)). Qed.
Lemma lem1155616 {_27147 : Type'} : (@eq (list _27147)) = (@eq (list _27147)).
Proof. exact (eq_refl (@eq (list _27147))). Qed.
Lemma lem1155617 {_27145 _27147 : Type'} : (term104 _27145 _27147) = (@eq (list _27147) (@nil _27147)).
Proof. exact (MK_COMB (@lem1155616 _27147) (@lem1155615 _27145 _27147)). Qed.
Lemma lem1155618 {_27147 : Type'} : (@nil _27147) = (@nil _27147).
Proof. exact (eq_refl (@nil _27147)). Qed.
Lemma lem1155619 {_27145 _27147 : Type'} : ((term95 _27145 _27147) = (@nil _27147)) = ((@nil _27147) = (@nil _27147)).
Proof. exact (MK_COMB (@lem1155617 _27145 _27147) (@lem1155618 _27147)). Qed.
Lemma lem1155621 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1155622 {_27147 : Type'} (x : list _27147) : (x = x) = True.
Proof. exact (@lem1155621 (list _27147) x). Qed.
Lemma lem1155623 {_27147 : Type'} : ((@nil _27147) = (@nil _27147)) = True.
Proof. exact (@lem1155622 _27147 (@nil _27147)). Qed.
Lemma lem1155626 {_27145 _27147 : Type'} : ((term95 _27145 _27147) = (@nil _27147)) = True.
Proof. exact (TRANS (@lem1155619 _27145 _27147) (@lem1155623 _27147)). Qed.
Lemma lem1155627 {_27145 _27147 : Type'} : term105 _27145 _27147.
Proof. exact (fun h0 : True => @lem1155626 _27145 _27147). Qed.
Lemma lem1155628 {_27145 _27147 : Type'} : term106 _27145 _27147.
Proof. exact (@lem1155598 _27145 _27147 True). Qed.
Lemma lem1155629 {_27145 _27147 : Type'} : (term34 _27145 _27147) = (True -> True).
Proof. exact (@lem1155628 _27145 _27147 (@lem1155627 _27145 _27147)). Qed.
Lemma lem1155631 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1155632 : (True -> True) = True.
Proof. exact (@lem1155631 True). Qed.
Lemma lem1155633 {_27145 _27147 : Type'} : (term34 _27145 _27147) = True.
Proof. exact (TRANS (@lem1155629 _27145 _27147) (@lem1155632)). Qed.
Lemma lem1155634 {_27145 _27147 : Type'} : True = (term34 _27145 _27147).
Proof. exact (SYM (@lem1155633 _27145 _27147)). Qed.
Lemma lem1155635 {_27145 _27147 : Type'} : term34 _27145 _27147.
Proof. exact (EQ_MP (@lem1155634 _27145 _27147) (@lem0)). Qed.
Lemma lem1155636 (n : nat) : term107 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1155637 (n : nat) : (term107 n) = (term108 n).
Proof. exact (eq_refl (term107 n)). Qed.
Lemma lem1155638 (n : nat) : term108 n.
Proof. exact (EQ_MP (@lem1155637 n) (@lem1155636 n)). Qed.
Lemma lem1155642 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1155643 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem1155642 n h1)). Qed.
Lemma lem1155644 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem1155645 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem1155644 n h1)). Qed.
Lemma lem1155646 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem1155643 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem1155645 n h1)). Qed.
Lemma lem1155647 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1155648 (n : nat) : (term108 n) = (term109 n).
Proof. exact (MK_COMB (@lem1155647) (@lem1155646 n)). Qed.
Lemma lem1155649 (n : nat) : term109 n.
Proof. exact (EQ_MP (@lem1155648 n) (@lem1155638 n)). Qed.
Lemma lem1155650 (n : nat) : term110 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem1155680 {A : Type'} : term111 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1155681 {A : Type'} (h : A) : term112 A h.
Proof. exact (@lem1155680 A h). Qed.
Lemma lem1155682 {A : Type'} (h : A) : (term112 A h) = (term113 A h).
Proof. exact (eq_refl (term112 A h)). Qed.
Lemma lem1155683 {A : Type'} (h : A) : term113 A h.
Proof. exact (EQ_MP (@lem1155682 A h) (@lem1155681 A h)). Qed.
Lemma lem1155684 {A : Type'} (h : A) (t : list A) : term114 A h t.
Proof. exact (@lem1155683 A h t). Qed.
Lemma lem1155685 {A : Type'} (h : A) (t : list A) : (term114 A h t) = ((term115 A h t) = (term116 A t)).
Proof. exact (eq_refl (term114 A h t)). Qed.
Lemma lem1155700 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1155701 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem1155700 p q p' q'). Qed.
Lemma lem1155702 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem1155701 p q p'). Qed.
Lemma lem1155703 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : term117 _27145 _27147 h t.
Proof. exact (@lem1155702 ((@List.length _27145 (@nil _27145)) = (term115 _27147 h t)) ((term118 _27145 _27147 h t) = (@cons _27147 h t))). Qed.
Lemma lem1155704 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) (p' : Prop) : term119 _27145 _27147 h t p'.
Proof. exact (@lem1155703 _27145 _27147 h t p'). Qed.
Lemma lem1155705 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) (p' : Prop) : (term119 _27145 _27147 h t p') = (term120 _27145 _27147 h t p').
Proof. exact (eq_refl (term119 _27145 _27147 h t p')). Qed.
Lemma lem1155706 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) (p' : Prop) : term120 _27145 _27147 h t p'.
Proof. exact (EQ_MP (@lem1155705 _27145 _27147 h t p') (@lem1155704 _27145 _27147 h t p')). Qed.
Lemma lem1155707 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) (p' : Prop) (q' : Prop) : term121 _27145 _27147 h t p' q'.
Proof. exact (@lem1155706 _27145 _27147 h t p' q'). Qed.
Lemma lem1155708 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) (p' : Prop) (q' : Prop) : (term121 _27145 _27147 h t p' q') = (term122 _27145 _27147 h t p' q').
Proof. exact (eq_refl (term121 _27145 _27147 h t p' q')). Qed.
Lemma lem1155709 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) (p' : Prop) (q' : Prop) : term122 _27145 _27147 h t p' q'.
Proof. exact (EQ_MP (@lem1155708 _27145 _27147 h t p' q') (@lem1155707 _27145 _27147 h t p' q')). Qed.
Lemma lem1155713 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1155714 {_27145 : Type'} : (@List.length _27145 (@nil _27145)) = (NUMERAL 0).
Proof. exact (@lem1155713 _27145). Qed.
Lemma lem1155715 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1155716 {_27145 : Type'} : (term100 _27145) = term101.
Proof. exact (MK_COMB (@lem1155715) (@lem1155714 _27145)). Qed.
Lemma lem1155718 {A : Type'} (h : A) (t : list A) : (term115 A h t) = (term116 A t).
Proof. exact (EQ_MP (@lem1155685 A h t) (@lem1155684 A h t)). Qed.
Lemma lem1155719 {_27147 : Type'} (h : _27147) (t : list _27147) : (term115 _27147 h t) = (term116 _27147 t).
Proof. exact (@lem1155718 _27147 h t). Qed.
Lemma lem1155720 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : ((@List.length _27145 (@nil _27145)) = (term115 _27147 h t)) = ((NUMERAL 0) = (term116 _27147 t)).
Proof. exact (MK_COMB (@lem1155716 _27145) (@lem1155719 _27147 h t)). Qed.
Lemma lem1155722 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem1155650 n (@lem1155649 n)). Qed.
Lemma lem1155723 {_27147 : Type'} (t : list _27147) : ((NUMERAL 0) = (term116 _27147 t)) = False.
Proof. exact (@lem1155722 (@List.length _27147 t)). Qed.
Lemma lem1155724 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : ((@List.length _27145 (@nil _27145)) = (term115 _27147 h t)) = False.
Proof. exact (TRANS (@lem1155720 _27145 _27147 h t) (@lem1155723 _27147 t)). Qed.
Lemma lem1155725 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) (q' : Prop) : term123 _27145 _27147 h t q'.
Proof. exact (@lem1155709 _27145 _27147 h t False q'). Qed.
Lemma lem1155726 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) (q' : Prop) : term124 _27145 _27147 h t q'.
Proof. exact (@lem1155725 _27145 _27147 h t q' (@lem1155724 _27145 _27147 h t)). Qed.
Lemma lem1155732 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : ((term118 _27145 _27147 h t) = (@cons _27147 h t)) = ((term118 _27145 _27147 h t) = (@cons _27147 h t)).
Proof. exact (eq_refl ((term118 _27145 _27147 h t) = (@cons _27147 h t))). Qed.
Lemma lem1155733 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : term125 _27145 _27147 h t.
Proof. exact (fun h0 : False => @lem1155732 _27145 _27147 h t). Qed.
Lemma lem1155734 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : term126 _27145 _27147 h t.
Proof. exact (@lem1155726 _27145 _27147 h t ((term118 _27145 _27147 h t) = (@cons _27147 h t))). Qed.
Lemma lem1155735 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : (term42 _27145 _27147 h t) = (term127 _27145 _27147 h t).
Proof. exact (@lem1155734 _27145 _27147 h t (@lem1155733 _27145 _27147 h t)). Qed.
Lemma lem1155737 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1155738 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : (term127 _27145 _27147 h t) = True.
Proof. exact (@lem1155737 ((term118 _27145 _27147 h t) = (@cons _27147 h t))). Qed.
Lemma lem1155739 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : (term42 _27145 _27147 h t) = True.
Proof. exact (TRANS (@lem1155735 _27145 _27147 h t) (@lem1155738 _27145 _27147 h t)). Qed.
Lemma lem1155740 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : True = (term42 _27145 _27147 h t).
Proof. exact (SYM (@lem1155739 _27145 _27147 h t)). Qed.
Lemma lem1155741 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : term42 _27145 _27147 h t.
Proof. exact (EQ_MP (@lem1155740 _27145 _27147 h t) (@lem0)). Qed.
Lemma lem1155742 (n : nat) : term107 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1155743 (n : nat) : (term107 n) = (term108 n).
Proof. exact (eq_refl (term107 n)). Qed.
Lemma lem1155744 (n : nat) : term108 n.
Proof. exact (EQ_MP (@lem1155743 n) (@lem1155742 n)). Qed.
Lemma lem1155745 (n : nat) : term128 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1155786 {A : Type'} : term111 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1155787 {A : Type'} (h : A) : term112 A h.
Proof. exact (@lem1155786 A h). Qed.
Lemma lem1155788 {A : Type'} (h : A) : (term112 A h) = (term113 A h).
Proof. exact (eq_refl (term112 A h)). Qed.
Lemma lem1155789 {A : Type'} (h : A) : term113 A h.
Proof. exact (EQ_MP (@lem1155788 A h) (@lem1155787 A h)). Qed.
Lemma lem1155790 {A : Type'} (h : A) (t : list A) : term114 A h t.
Proof. exact (@lem1155789 A h t). Qed.
Lemma lem1155791 {A : Type'} (h : A) (t : list A) : (term114 A h t) = ((term115 A h t) = (term116 A t)).
Proof. exact (eq_refl (term114 A h t)). Qed.
Lemma lem1155809 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1155810 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem1155809 p q p' q'). Qed.
Lemma lem1155811 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem1155810 p q p'). Qed.
Lemma lem1155812 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : term129 _27145 _27147 h t.
Proof. exact (@lem1155811 ((term115 _27145 h t) = (@List.length _27147 (@nil _27147))) ((term130 _27145 _27147 h t) = (@nil _27147))). Qed.
Lemma lem1155813 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (p' : Prop) : term131 _27145 _27147 h t p'.
Proof. exact (@lem1155812 _27145 _27147 h t p'). Qed.
Lemma lem1155814 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (p' : Prop) : (term131 _27145 _27147 h t p') = (term132 _27145 _27147 h t p').
Proof. exact (eq_refl (term131 _27145 _27147 h t p')). Qed.
Lemma lem1155815 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (p' : Prop) : term132 _27145 _27147 h t p'.
Proof. exact (EQ_MP (@lem1155814 _27145 _27147 h t p') (@lem1155813 _27145 _27147 h t p')). Qed.
Lemma lem1155816 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (p' : Prop) (q' : Prop) : term133 _27145 _27147 h t p' q'.
Proof. exact (@lem1155815 _27145 _27147 h t p' q'). Qed.
Lemma lem1155817 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (p' : Prop) (q' : Prop) : (term133 _27145 _27147 h t p' q') = (term134 _27145 _27147 h t p' q').
Proof. exact (eq_refl (term133 _27145 _27147 h t p' q')). Qed.
Lemma lem1155818 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (p' : Prop) (q' : Prop) : term134 _27145 _27147 h t p' q'.
Proof. exact (EQ_MP (@lem1155817 _27145 _27147 h t p' q') (@lem1155816 _27145 _27147 h t p' q')). Qed.
Lemma lem1155822 {A : Type'} (h : A) (t : list A) : (term115 A h t) = (term116 A t).
Proof. exact (EQ_MP (@lem1155791 A h t) (@lem1155790 A h t)). Qed.
Lemma lem1155823 {_27145 : Type'} (h : _27145) (t : list _27145) : (term115 _27145 h t) = (term116 _27145 t).
Proof. exact (@lem1155822 _27145 h t). Qed.
Lemma lem1155824 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1155825 {_27145 : Type'} (h : _27145) (t : list _27145) : (term135 _27145 h t) = (term136 _27145 t).
Proof. exact (MK_COMB (@lem1155824) (@lem1155823 _27145 h t)). Qed.
Lemma lem1155827 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1155828 {_27147 : Type'} : (@List.length _27147 (@nil _27147)) = (NUMERAL 0).
Proof. exact (@lem1155827 _27147). Qed.
Lemma lem1155829 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : ((term115 _27145 h t) = (@List.length _27147 (@nil _27147))) = ((term116 _27145 t) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1155825 _27145 h t) (@lem1155828 _27147)). Qed.
Lemma lem1155831 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1155745 n (@lem1155744 n)). Qed.
Lemma lem1155832 {_27145 : Type'} (t : list _27145) : ((term116 _27145 t) = (NUMERAL 0)) = False.
Proof. exact (@lem1155831 (@List.length _27145 t)). Qed.
Lemma lem1155833 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : ((term115 _27145 h t) = (@List.length _27147 (@nil _27147))) = False.
Proof. exact (TRANS (@lem1155829 _27145 _27147 h t) (@lem1155832 _27145 t)). Qed.
Lemma lem1155834 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (q' : Prop) : term137 _27145 _27147 h t q'.
Proof. exact (@lem1155818 _27145 _27147 h t False q'). Qed.
Lemma lem1155835 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (q' : Prop) : term138 _27145 _27147 h t q'.
Proof. exact (@lem1155834 _27145 _27147 h t q' (@lem1155833 _27145 _27147 h t)). Qed.
Lemma lem1155841 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : ((term130 _27145 _27147 h t) = (@nil _27147)) = ((term130 _27145 _27147 h t) = (@nil _27147)).
Proof. exact (eq_refl ((term130 _27145 _27147 h t) = (@nil _27147))). Qed.
Lemma lem1155842 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : term139 _27145 _27147 h t.
Proof. exact (fun h0 : False => @lem1155841 _27145 _27147 h t). Qed.
Lemma lem1155843 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : term140 _27145 _27147 h t.
Proof. exact (@lem1155835 _27145 _27147 h t ((term130 _27145 _27147 h t) = (@nil _27147))). Qed.
Lemma lem1155844 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term63 _27145 _27147 h t) = (term141 _27145 _27147 h t).
Proof. exact (@lem1155843 _27145 _27147 h t (@lem1155842 _27145 _27147 h t)). Qed.
Lemma lem1155846 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1155847 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term141 _27145 _27147 h t) = True.
Proof. exact (@lem1155846 ((term130 _27145 _27147 h t) = (@nil _27147))). Qed.
Lemma lem1155848 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : (term63 _27145 _27147 h t) = True.
Proof. exact (TRANS (@lem1155844 _27145 _27147 h t) (@lem1155847 _27145 _27147 h t)). Qed.
Lemma lem1155849 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : True = (term63 _27145 _27147 h t).
Proof. exact (SYM (@lem1155848 _27145 _27147 h t)). Qed.
Lemma lem1155850 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : term63 _27145 _27147 h t.
Proof. exact (EQ_MP (@lem1155849 _27145 _27147 h t) (@lem0)). Qed.
Lemma lem1155875 {A B : Type'} : term142 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1155876 {A B : Type'} (f : A -> B) : term143 A B f.
Proof. exact (@lem1155875 A B f). Qed.
Lemma lem1155877 {A B : Type'} (f : A -> B) : (term143 A B f) = (term144 A B f).
Proof. exact (eq_refl (term143 A B f)). Qed.
Lemma lem1155878 {A B : Type'} (f : A -> B) : term144 A B f.
Proof. exact (EQ_MP (@lem1155877 A B f) (@lem1155876 A B f)). Qed.
Lemma lem1155879 {A B : Type'} (f : A -> B) (h : A) : term145 A B f h.
Proof. exact (@lem1155878 A B f h). Qed.
Lemma lem1155880 {A B : Type'} (h : A) (f : A -> B) : (term145 A B f h) = (term146 A B h f).
Proof. exact (eq_refl (term145 A B f h)). Qed.
Lemma lem1155881 {A B : Type'} (h : A) (f : A -> B) : term146 A B h f.
Proof. exact (EQ_MP (@lem1155880 A B h f) (@lem1155879 A B f h)). Qed.
Lemma lem1155882 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term147 A B h f t.
Proof. exact (@lem1155881 A B h f t). Qed.
Lemma lem1155883 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term147 A B h f t) = ((term148 A B f h t) = (term149 A B h f t)).
Proof. exact (eq_refl (term147 A B h f t)). Qed.
Lemma lem1155889 (m : nat) : term150 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem1155890 (m : nat) : (term150 m) = (term151 m).
Proof. exact (eq_refl (term150 m)). Qed.
Lemma lem1155891 (m : nat) : term151 m.
Proof. exact (EQ_MP (@lem1155890 m) (@lem1155889 m)). Qed.
Lemma lem1155892 (m : nat) (n : nat) : term152 m n.
Proof. exact (@lem1155891 m n). Qed.
Lemma lem1155893 (m : nat) (n : nat) : (term152 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term152 m n)). Qed.
Lemma lem1155895 {A : Type'} : term111 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1155896 {A : Type'} (h : A) : term112 A h.
Proof. exact (@lem1155895 A h). Qed.
Lemma lem1155897 {A : Type'} (h : A) : (term112 A h) = (term113 A h).
Proof. exact (eq_refl (term112 A h)). Qed.
Lemma lem1155898 {A : Type'} (h : A) : term113 A h.
Proof. exact (EQ_MP (@lem1155897 A h) (@lem1155896 A h)). Qed.
Lemma lem1155899 {A : Type'} (h : A) (t : list A) : term114 A h t.
Proof. exact (@lem1155898 A h t). Qed.
Lemma lem1155900 {A : Type'} (h : A) (t : list A) : (term114 A h t) = ((term115 A h t) = (term116 A t)).
Proof. exact (eq_refl (term114 A h t)). Qed.
Lemma lem1155903 {_27145 _27147 : Type'} (l2 : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : term153 _27145 _27147 t l2.
Proof. exact (@lem1155457 _27145 _27147 t h1 l2). Qed.
Lemma lem1155904 {_27145 _27147 : Type'} (t : list _27145) (l2 : list _27147) : (term153 _27145 _27147 t l2) = (term154 _27145 _27147 t l2).
Proof. exact (eq_refl (term153 _27145 _27147 t l2)). Qed.
Lemma lem1155905 {_27145 _27147 : Type'} (l2 : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : term154 _27145 _27147 t l2.
Proof. exact (EQ_MP (@lem1155904 _27145 _27147 t l2) (@lem1155903 _27145 _27147 l2 t h1)). Qed.
Lemma lem1155906 {_27145 _27147 : Type'} (t : list _27145) (l2 : list _27147) (h1 : (@List.length _27145 t) = (@List.length _27147 l2)) : (@List.length _27145 t) = (@List.length _27147 l2).
Proof. exact (h1). Qed.
Lemma lem1155907 {_27145 _27147 : Type'} (t : list _27145) (l2 : list _27147) (h1 : term8 _27145 _27147 t) (h2 : (@List.length _27145 t) = (@List.length _27147 l2)) : (term155 _27145 _27147 t l2) = l2.
Proof. exact (@lem1155905 _27145 _27147 l2 t h1 (@lem1155906 _27145 _27147 t l2 h2)). Qed.
Lemma lem1155925 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1155926 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem1155925 p q p' q'). Qed.
Lemma lem1155927 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem1155926 p q p'). Qed.
Lemma lem1155928 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) (t' : list _27147) : term156 _27145 _27147 h t h' t'.
Proof. exact (@lem1155927 ((term115 _27145 h t) = (term115 _27147 h' t')) ((term157 _27145 _27147 h t h' t') = (@cons _27147 h' t'))). Qed.
Lemma lem1155929 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) (t' : list _27147) (p' : Prop) : term158 _27145 _27147 h t h' t' p'.
Proof. exact (@lem1155928 _27145 _27147 h t h' t' p'). Qed.
Lemma lem1155930 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) (t' : list _27147) (p' : Prop) : (term158 _27145 _27147 h t h' t' p') = (term159 _27145 _27147 h t h' t' p').
Proof. exact (eq_refl (term158 _27145 _27147 h t h' t' p')). Qed.
Lemma lem1155931 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) (t' : list _27147) (p' : Prop) : term159 _27145 _27147 h t h' t' p'.
Proof. exact (EQ_MP (@lem1155930 _27145 _27147 h t h' t' p') (@lem1155929 _27145 _27147 h t h' t' p')). Qed.
Lemma lem1155932 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) (t' : list _27147) (p' : Prop) (q' : Prop) : term160 _27145 _27147 h t h' t' p' q'.
Proof. exact (@lem1155931 _27145 _27147 h t h' t' p' q'). Qed.
Lemma lem1155933 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) (t' : list _27147) (p' : Prop) (q' : Prop) : (term160 _27145 _27147 h t h' t' p' q') = (term161 _27145 _27147 h t h' t' p' q').
Proof. exact (eq_refl (term160 _27145 _27147 h t h' t' p' q')). Qed.
Lemma lem1155934 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h' : _27147) (t' : list _27147) (p' : Prop) (q' : Prop) : term161 _27145 _27147 h t h' t' p' q'.
Proof. exact (EQ_MP (@lem1155933 _27145 _27147 h t h' t' p' q') (@lem1155932 _27145 _27147 h t h' t' p' q')). Qed.
Lemma lem1155938 {A : Type'} (h : A) (t : list A) : (term115 A h t) = (term116 A t).
Proof. exact (EQ_MP (@lem1155900 A h t) (@lem1155899 A h t)). Qed.
Lemma lem1155939 {_27145 : Type'} (h : _27145) (t : list _27145) : (term115 _27145 h t) = (term116 _27145 t).
Proof. exact (@lem1155938 _27145 h t). Qed.
Lemma lem1155940 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1155941 {_27145 : Type'} (h : _27145) (t : list _27145) : (term135 _27145 h t) = (term136 _27145 t).
Proof. exact (MK_COMB (@lem1155940) (@lem1155939 _27145 h t)). Qed.
Lemma lem1155943 {A : Type'} (h : A) (t : list A) : (term115 A h t) = (term116 A t).
Proof. exact (EQ_MP (@lem1155900 A h t) (@lem1155899 A h t)). Qed.
Lemma lem1155944 {_27147 : Type'} (h : _27147) (t : list _27147) : (term115 _27147 h t) = (term116 _27147 t).
Proof. exact (@lem1155943 _27147 h t). Qed.
Lemma lem1155945 {_27147 : Type'} (h' : _27147) (t' : list _27147) : (term115 _27147 h' t') = (term116 _27147 t').
Proof. exact (@lem1155944 _27147 h' t'). Qed.
Lemma lem1155946 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) : ((term115 _27145 h t) = (term115 _27147 h' t')) = ((term116 _27145 t) = (term116 _27147 t')).
Proof. exact (MK_COMB (@lem1155941 _27145 h t) (@lem1155945 _27147 h' t')). Qed.
Lemma lem1155948 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1155893 m n) (@lem1155892 m n)). Qed.
Lemma lem1155949 {_27145 _27147 : Type'} (t : list _27145) (t' : list _27147) : ((term116 _27145 t) = (term116 _27147 t')) = ((@List.length _27145 t) = (@List.length _27147 t')).
Proof. exact (@lem1155948 (@List.length _27145 t) (@List.length _27147 t')). Qed.
Lemma lem1155952 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) : ((term115 _27145 h t) = (term115 _27147 h' t')) = ((@List.length _27145 t) = (@List.length _27147 t')).
Proof. exact (TRANS (@lem1155946 _27145 _27147 h h' t t') (@lem1155949 _27145 _27147 t t')). Qed.
Lemma lem1155953 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) (q' : Prop) : term162 _27145 _27147 h h' t t' q'.
Proof. exact (@lem1155934 _27145 _27147 h t h' t' ((@List.length _27145 t) = (@List.length _27147 t')) q'). Qed.
Lemma lem1155954 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) (q' : Prop) : term163 _27145 _27147 h h' t t' q'.
Proof. exact (@lem1155953 _27145 _27147 h h' t t' q' (@lem1155952 _27145 _27147 h h' t t')). Qed.
Lemma lem1155959 {_25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764) : (term164 _25763 _25764 h1' t1 h2' t2) = (term165 _25763 _25764 h1' h2' t1 t2).
Proof. exact (proj2 (@lem1109008 Prop Prop _25763 _25764 h1' h2' t1 t2)). Qed.
Lemma lem1155960 {_27145 _27147 : Type'} (h1' : _27145) (h2' : _27147) (t1 : list _27145) (t2 : list _27147) : (term164 _27145 _27147 h1' t1 h2' t2) = (term165 _27145 _27147 h1' h2' t1 t2).
Proof. exact (@lem1155959 _27145 _27147 h1' h2' t1 t2). Qed.
Lemma lem1155961 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) : (term164 _27145 _27147 h t h' t') = (term165 _27145 _27147 h h' t t').
Proof. exact (@lem1155960 _27145 _27147 h h' t t'). Qed.
Lemma lem1155962 {_27145 _27147 : Type'} : (@List.map (prod _27145 _27147) _27147 (@snd _27145 _27147)) = (@List.map (prod _27145 _27147) _27147 (@snd _27145 _27147)).
Proof. exact (eq_refl (@List.map (prod _27145 _27147) _27147 (@snd _27145 _27147))). Qed.
Lemma lem1155963 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) : (term157 _27145 _27147 h t h' t') = (term166 _27145 _27147 h h' t t').
Proof. exact (MK_COMB (@lem1155962 _27145 _27147) (@lem1155961 _27145 _27147 h h' t t')). Qed.
Lemma lem1155965 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term148 A B f h t) = (term149 A B h f t).
Proof. exact (EQ_MP (@lem1155883 A B h f t) (@lem1155882 A B h f t)). Qed.
Lemma lem1155966 {_27145 _27147 : Type'} (h : prod _27145 _27147) (f : type1208 _27145 _27147) (t : type1640 _27145 _27147) : (term167 _27145 _27147 f h t) = (term168 _27145 _27147 h f t).
Proof. exact (@lem1155965 (prod _27145 _27147) _27147 h f t). Qed.
Lemma lem1155967 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) : (term166 _27145 _27147 h h' t t') = (term169 _27145 _27147 h h' t t').
Proof. exact (@lem1155966 _27145 _27147 (@pair _27145 _27147 h h') (@snd _27145 _27147) (@ZIP _27145 _27147 t t')). Qed.
Lemma lem1155969 {A B : Type'} (x : A) (y : B) : (term170 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem1155970 {_27145 _27147 : Type'} (x : _27145) (y : _27147) : (term170 _27145 _27147 x y) = y.
Proof. exact (@lem1155969 _27145 _27147 x y). Qed.
Lemma lem1155971 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) : (term170 _27145 _27147 h h') = h'.
Proof. exact (@lem1155970 _27145 _27147 h h'). Qed.
Lemma lem1155972 {_27147 : Type'} : (@cons _27147) = (@cons _27147).
Proof. exact (eq_refl (@cons _27147)). Qed.
Lemma lem1155973 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) : (term171 _27145 _27147 h h') = (@cons _27147 h').
Proof. exact (MK_COMB (@lem1155972 _27147) (@lem1155971 _27145 _27147 h h')). Qed.
Lemma lem1155975 {_27145 _27147 : Type'} (l2 : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : term154 _27145 _27147 t l2.
Proof. exact (fun h0 : (@List.length _27145 t) = (@List.length _27147 l2) => @lem1155907 _27145 _27147 t l2 h1 h0). Qed.
Lemma lem1155976 {_27145 _27147 : Type'} (l2 : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : term154 _27145 _27147 t l2.
Proof. exact (@lem1155975 _27145 _27147 l2 t h1). Qed.
Lemma lem1155977 {_27145 _27147 : Type'} (t' : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : term154 _27145 _27147 t t'.
Proof. exact (@lem1155976 _27145 _27147 t' t h1). Qed.
Lemma lem1155981 {_27145 _27147 : Type'} (t : list _27145) (t' : list _27147) (h1 : (@List.length _27145 t) = (@List.length _27147 t')) : (@List.length _27145 t) = (@List.length _27147 t').
Proof. exact (h1). Qed.
Lemma lem1155982 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1155983 {_27145 _27147 : Type'} (t : list _27145) (t' : list _27147) (h1 : (@List.length _27145 t) = (@List.length _27147 t')) : (term172 _27145 t) = (term172 _27147 t').
Proof. exact (MK_COMB (@lem1155982) (@lem1155981 _27145 _27147 t t' h1)). Qed.
Lemma lem1155984 {_27147 : Type'} (t' : list _27147) : (@List.length _27147 t') = (@List.length _27147 t').
Proof. exact (eq_refl (@List.length _27147 t')). Qed.
Lemma lem1155985 {_27145 _27147 : Type'} (t : list _27145) (t' : list _27147) (h1 : (@List.length _27145 t) = (@List.length _27147 t')) : ((@List.length _27145 t) = (@List.length _27147 t')) = ((@List.length _27147 t') = (@List.length _27147 t')).
Proof. exact (MK_COMB (@lem1155983 _27145 _27147 t t' h1) (@lem1155984 _27147 t')). Qed.
Lemma lem1155987 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1155988 (x : nat) : (x = x) = True.
Proof. exact (@lem1155987 nat x). Qed.
Lemma lem1155989 {_27147 : Type'} (t' : list _27147) : ((@List.length _27147 t') = (@List.length _27147 t')) = True.
Proof. exact (@lem1155988 (@List.length _27147 t')). Qed.
Lemma lem1155990 {_27145 _27147 : Type'} (t : list _27145) (t' : list _27147) (h1 : (@List.length _27145 t) = (@List.length _27147 t')) : ((@List.length _27145 t) = (@List.length _27147 t')) = True.
Proof. exact (TRANS (@lem1155985 _27145 _27147 t t' h1) (@lem1155989 _27147 t')). Qed.
Lemma lem1155991 {_27145 _27147 : Type'} (t : list _27145) (t' : list _27147) (h1 : (@List.length _27145 t) = (@List.length _27147 t')) : True = ((@List.length _27145 t) = (@List.length _27147 t')).
Proof. exact (SYM (@lem1155990 _27145 _27147 t t' h1)). Qed.
Lemma lem1155992 {_27145 _27147 : Type'} (t : list _27145) (t' : list _27147) (h1 : (@List.length _27145 t) = (@List.length _27147 t')) : (@List.length _27145 t) = (@List.length _27147 t').
Proof. exact (EQ_MP (@lem1155991 _27145 _27147 t t' h1) (@lem0)). Qed.
Lemma lem1155993 {_27145 _27147 : Type'} (t : list _27145) (t' : list _27147) (h1 : term8 _27145 _27147 t) (h2 : (@List.length _27145 t) = (@List.length _27147 t')) : (term155 _27145 _27147 t t') = t'.
Proof. exact (@lem1155977 _27145 _27147 t' t h1 (@lem1155992 _27145 _27147 t t' h2)). Qed.
Lemma lem1155994 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) (h1 : term8 _27145 _27147 t) (h2 : (@List.length _27145 t) = (@List.length _27147 t')) : (term169 _27145 _27147 h h' t t') = (@cons _27147 h' t').
Proof. exact (MK_COMB (@lem1155973 _27145 _27147 h h') (@lem1155993 _27145 _27147 t t' h1 h2)). Qed.
Lemma lem1155995 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) (h1 : term8 _27145 _27147 t) (h2 : (@List.length _27145 t) = (@List.length _27147 t')) : (term166 _27145 _27147 h h' t t') = (@cons _27147 h' t').
Proof. exact (TRANS (@lem1155967 _27145 _27147 h h' t t') (@lem1155994 _27145 _27147 h h' t t' h1 h2)). Qed.
Lemma lem1155996 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) (h1 : term8 _27145 _27147 t) (h2 : (@List.length _27145 t) = (@List.length _27147 t')) : (term157 _27145 _27147 h t h' t') = (@cons _27147 h' t').
Proof. exact (TRANS (@lem1155963 _27145 _27147 h h' t t') (@lem1155995 _27145 _27147 h h' t t' h1 h2)). Qed.
Lemma lem1155997 {_27147 : Type'} : (@eq (list _27147)) = (@eq (list _27147)).
Proof. exact (eq_refl (@eq (list _27147))). Qed.
Lemma lem1155998 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) (h1 : term8 _27145 _27147 t) (h2 : (@List.length _27145 t) = (@List.length _27147 t')) : (term173 _27145 _27147 h t h' t') = (term174 _27147 h' t').
Proof. exact (MK_COMB (@lem1155997 _27147) (@lem1155996 _27145 _27147 h h' t t' h1 h2)). Qed.
Lemma lem1155999 {_27147 : Type'} (h' : _27147) (t' : list _27147) : (@cons _27147 h' t') = (@cons _27147 h' t').
Proof. exact (eq_refl (@cons _27147 h' t')). Qed.
Lemma lem1156000 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) (h1 : term8 _27145 _27147 t) (h2 : (@List.length _27145 t) = (@List.length _27147 t')) : ((term157 _27145 _27147 h t h' t') = (@cons _27147 h' t')) = ((@cons _27147 h' t') = (@cons _27147 h' t')).
Proof. exact (MK_COMB (@lem1155998 _27145 _27147 h h' t t' h1 h2) (@lem1155999 _27147 h' t')). Qed.
Lemma lem1156002 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1156003 {_27147 : Type'} (x : list _27147) : (x = x) = True.
Proof. exact (@lem1156002 (list _27147) x). Qed.
Lemma lem1156004 {_27147 : Type'} (h' : _27147) (t' : list _27147) : ((@cons _27147 h' t') = (@cons _27147 h' t')) = True.
Proof. exact (@lem1156003 _27147 (@cons _27147 h' t')). Qed.
Lemma lem1156005 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) (h1 : term8 _27145 _27147 t) (h2 : (@List.length _27145 t) = (@List.length _27147 t')) : ((term157 _27145 _27147 h t h' t') = (@cons _27147 h' t')) = True.
Proof. exact (TRANS (@lem1156000 _27145 _27147 h h' t t' h1 h2) (@lem1156004 _27147 h' t')). Qed.
Lemma lem1156006 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t' : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : term175 _27145 _27147 h t h' t'.
Proof. exact (fun h0 : (@List.length _27145 t) = (@List.length _27147 t') => @lem1156005 _27145 _27147 h h' t t' h1 h0). Qed.
Lemma lem1156007 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (t' : list _27147) : term176 _27145 _27147 h h' t t'.
Proof. exact (@lem1155954 _27145 _27147 h h' t t' True). Qed.
Lemma lem1156008 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t' : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : (term71 _27145 _27147 h t h' t') = (term177 _27145 _27147 t t').
Proof. exact (@lem1156007 _27145 _27147 h h' t t' (@lem1156006 _27145 _27147 h h' t' t h1)). Qed.
Lemma lem1156012 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1156013 {_27145 _27147 : Type'} (t : list _27145) (t' : list _27147) : (term177 _27145 _27147 t t') = True.
Proof. exact (@lem1156012 ((@List.length _27145 t) = (@List.length _27147 t'))). Qed.
Lemma lem1156014 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t' : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : (term71 _27145 _27147 h t h' t') = True.
Proof. exact (TRANS (@lem1156008 _27145 _27147 h h' t' t h1) (@lem1156013 _27145 _27147 t t')). Qed.
Lemma lem1156015 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t' : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : True = (term71 _27145 _27147 h t h' t').
Proof. exact (SYM (@lem1156014 _27145 _27147 h h' t' t h1)). Qed.
Lemma lem1156016 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t' : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : term71 _27145 _27147 h t h' t'.
Proof. exact (EQ_MP (@lem1156015 _27145 _27147 h h' t' t h1) (@lem0)). Qed.
Lemma lem1156017 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t' : list _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : term73 _27145 _27147 h t h' t'.
Proof. exact (fun h0 : term67 _27145 _27147 h t t' => @lem1156016 _27145 _27147 h h' t' t h1). Qed.
Lemma lem1156022 {_27145 _27147 : Type'} (h : _27145) (h' : _27147) (t : list _27145) (h1 : term8 _27145 _27147 t) : term77 _27145 _27147 h t h'.
Proof. exact (fun t' : list _27147 => @lem1156017 _27145 _27147 h h' t' t h1). Qed.
Lemma lem1156027 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h1 : term8 _27145 _27147 t) : term81 _27145 _27147 h t.
Proof. exact (fun h' : _27147 => @lem1156022 _27145 _27147 h h' t h1). Qed.
Lemma lem1156028 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h1 : term8 _27145 _27147 t) : term83 _27145 _27147 h t.
Proof. exact (conj (@lem1155850 _27145 _27147 h t) (@lem1156027 _27145 _27147 h t h1)). Qed.
Lemma lem1156029 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) (h1 : term8 _27145 _27147 t) : term12 _27145 _27147 h t.
Proof. exact (@lem1155512 _27145 _27147 h t (@lem1156028 _27145 _27147 h t h1)). Qed.
Lemma lem1156030 {_27145 _27147 : Type'} (h : _27147) (t : list _27147) : term44 _27145 _27147 h t.
Proof. exact (fun h0 : term38 _27145 _27147 t => @lem1155741 _27145 _27147 h t). Qed.
Lemma lem1156035 {_27145 _27147 : Type'} (h : _27147) : term48 _27145 _27147 h.
Proof. exact (fun t : list _27147 => @lem1156030 _27145 _27147 h t). Qed.
Lemma lem1156040 {_27145 _27147 : Type'} : term52 _27145 _27147.
Proof. exact (fun h : _27147 => @lem1156035 _27145 _27147 h). Qed.
Lemma lem1156041 {_27145 _27147 : Type'} : term54 _27145 _27147.
Proof. exact (conj (@lem1155635 _27145 _27147) (@lem1156040 _27145 _27147)). Qed.
Lemma lem1156042 {_27145 _27147 : Type'} : term4 _27145 _27147.
Proof. exact (@lem1155484 _27145 _27147 (@lem1156041 _27145 _27147)). Qed.
Lemma lem1156043 {_27145 _27147 : Type'} (h : _27145) (t : list _27145) : term14 _27145 _27147 h t.
Proof. exact (fun h0 : term8 _27145 _27147 t => @lem1156029 _27145 _27147 h t h0). Qed.
Lemma lem1156048 {_27145 _27147 : Type'} (h : _27145) : term18 _27145 _27147 h.
Proof. exact (fun t : list _27145 => @lem1156043 _27145 _27147 h t). Qed.
Lemma lem1156053 {_27145 _27147 : Type'} : term22 _27145 _27147.
Proof. exact (fun h : _27145 => @lem1156048 _27145 _27147 h). Qed.
Lemma lem1156054 {_27145 _27147 : Type'} : term24 _27145 _27147.
Proof. exact (conj (@lem1156042 _27145 _27147) (@lem1156053 _27145 _27147)). Qed.
Lemma lem1156055 {_27145 _27147 : Type'} : term29 _27145 _27147.
Proof. exact (@lem1155456 _27145 _27147 (@lem1156054 _27145 _27147)). Qed.
