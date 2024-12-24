Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_REVERSE_term_abbrevs.
Require Import MAP_APPEND_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1096517_spec.
Require Import thm1096523_spec.
Require Import thm1096524_spec.
Require Import thm1097797_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1207494 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1207495 {_28394 : Type'} (P : type1143 _28394) : term0 _28394 P.
Proof. exact (@lem1207494 _28394 P). Qed.
Lemma lem1207496 {_28392 _28394 : Type'} (f : _28394 -> _28392) : term1 _28392 _28394 f.
Proof. exact (@lem1207495 _28394 (term2 _28392 _28394 f)). Qed.
Lemma lem1207497 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term3 _28392 _28394 f) = ((term4 _28392 _28394 f) = (term5 _28392 _28394 f)).
Proof. exact (eq_refl (term3 _28392 _28394 f)). Qed.
Lemma lem1207498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1207499 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term6 _28392 _28394 f) = (term7 _28392 _28394 f).
Proof. exact (MK_COMB (@lem1207498) (@lem1207497 _28392 _28394 f)). Qed.
Lemma lem1207500 {_28392 _28394 : Type'} (f : _28394 -> _28392) (t : list _28394) : (term8 _28392 _28394 f t) = ((term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)).
Proof. exact (eq_refl (term8 _28392 _28394 f t)). Qed.
Lemma lem1207501 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207502 {_28392 _28394 : Type'} (f : _28394 -> _28392) (t : list _28394) : (term11 _28392 _28394 f t) = (term12 _28392 _28394 f t).
Proof. exact (MK_COMB (@lem1207501) (@lem1207500 _28392 _28394 f t)). Qed.
Lemma lem1207503 {_28392 _28394 : Type'} (f : _28394 -> _28392) (h : _28394) (t : list _28394) : (term13 _28392 _28394 f h t) = ((term14 _28392 _28394 f h t) = (term15 _28392 _28394 f h t)).
Proof. exact (eq_refl (term13 _28392 _28394 f h t)). Qed.
Lemma lem1207504 {_28392 _28394 : Type'} (f : _28394 -> _28392) (h : _28394) (t : list _28394) : (term16 _28392 _28394 f h t) = (term17 _28392 _28394 f h t).
Proof. exact (MK_COMB (@lem1207502 _28392 _28394 f t) (@lem1207503 _28392 _28394 f h t)). Qed.
Lemma lem1207505 {_28392 _28394 : Type'} (f : _28394 -> _28392) (h : _28394) : (term18 _28392 _28394 f h) = (term19 _28392 _28394 f h).
Proof. exact (fun_ext (fun t : list _28394 => @lem1207504 _28392 _28394 f h t)). Qed.
Lemma lem1207506 {_28394 : Type'} : (@all (list _28394)) = (@all (list _28394)).
Proof. exact (eq_refl (@all (list _28394))). Qed.
Lemma lem1207507 {_28392 _28394 : Type'} (f : _28394 -> _28392) (h : _28394) : (term20 _28392 _28394 f h) = (term21 _28392 _28394 f h).
Proof. exact (MK_COMB (@lem1207506 _28394) (@lem1207505 _28392 _28394 f h)). Qed.
Lemma lem1207508 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term22 _28392 _28394 f) = (term23 _28392 _28394 f).
Proof. exact (fun_ext (fun h : _28394 => @lem1207507 _28392 _28394 f h)). Qed.
Lemma lem1207509 {_28394 : Type'} : (@all _28394) = (@all _28394).
Proof. exact (eq_refl (@all _28394)). Qed.
Lemma lem1207510 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term24 _28392 _28394 f) = (term25 _28392 _28394 f).
Proof. exact (MK_COMB (@lem1207509 _28394) (@lem1207508 _28392 _28394 f)). Qed.
Lemma lem1207511 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term26 _28392 _28394 f) = (term27 _28392 _28394 f).
Proof. exact (MK_COMB (@lem1207499 _28392 _28394 f) (@lem1207510 _28392 _28394 f)). Qed.
Lemma lem1207512 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207513 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term28 _28392 _28394 f) = (term29 _28392 _28394 f).
Proof. exact (MK_COMB (@lem1207512) (@lem1207511 _28392 _28394 f)). Qed.
Lemma lem1207514 {_28392 _28394 : Type'} (f : _28394 -> _28392) (l : list _28394) : (term8 _28392 _28394 f l) = ((term9 _28392 _28394 f l) = (term10 _28392 _28394 f l)).
Proof. exact (eq_refl (term8 _28392 _28394 f l)). Qed.
Lemma lem1207515 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term30 _28392 _28394 f) = (term2 _28392 _28394 f).
Proof. exact (fun_ext (fun l : list _28394 => @lem1207514 _28392 _28394 f l)). Qed.
Lemma lem1207516 {_28394 : Type'} : (@all (list _28394)) = (@all (list _28394)).
Proof. exact (eq_refl (@all (list _28394))). Qed.
Lemma lem1207517 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term31 _28392 _28394 f) = (term32 _28392 _28394 f).
Proof. exact (MK_COMB (@lem1207516 _28394) (@lem1207515 _28392 _28394 f)). Qed.
Lemma lem1207518 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term1 _28392 _28394 f) = (term33 _28392 _28394 f).
Proof. exact (MK_COMB (@lem1207513 _28392 _28394 f) (@lem1207517 _28392 _28394 f)). Qed.
Lemma lem1207519 {_28392 _28394 : Type'} (f : _28394 -> _28392) : term33 _28392 _28394 f.
Proof. exact (EQ_MP (@lem1207518 _28392 _28394 f) (@lem1207496 _28392 _28394 f)). Qed.
Lemma lem1207542 {A B : Type'} : term34 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1207543 {A B : Type'} (f : A -> B) : term35 A B f.
Proof. exact (@lem1207542 A B f). Qed.
Lemma lem1207544 {A B : Type'} (f : A -> B) : (term35 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term35 A B f)). Qed.
Lemma lem1207549 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1207544 A B f) (@lem1207543 A B f)). Qed.
Lemma lem1207550 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (@List.map _28394 _28392 f (@nil _28394)) = (@nil _28392).
Proof. exact (@lem1207549 _28394 _28392 f). Qed.
Lemma lem1207551 {_28392 : Type'} : (@List.rev _28392) = (@List.rev _28392).
Proof. exact (eq_refl (@List.rev _28392)). Qed.
Lemma lem1207552 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term4 _28392 _28394 f) = (@List.rev _28392 (@nil _28392)).
Proof. exact (MK_COMB (@lem1207551 _28392) (@lem1207550 _28392 _28394 f)). Qed.
Lemma lem1207554 {A : Type'} : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1096517 A)). Qed.
Lemma lem1207555 {_28392 : Type'} : (@List.rev _28392 (@nil _28392)) = (@nil _28392).
Proof. exact (@lem1207554 _28392). Qed.
Lemma lem1207556 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term4 _28392 _28394 f) = (@nil _28392).
Proof. exact (TRANS (@lem1207552 _28392 _28394 f) (@lem1207555 _28392)). Qed.
Lemma lem1207557 {_28392 : Type'} : (@eq (list _28392)) = (@eq (list _28392)).
Proof. exact (eq_refl (@eq (list _28392))). Qed.
Lemma lem1207558 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term36 _28392 _28394 f) = (@eq (list _28392) (@nil _28392)).
Proof. exact (MK_COMB (@lem1207557 _28392) (@lem1207556 _28392 _28394 f)). Qed.
Lemma lem1207560 {A : Type'} : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1096517 A)). Qed.
Lemma lem1207561 {_28394 : Type'} : (@List.rev _28394 (@nil _28394)) = (@nil _28394).
Proof. exact (@lem1207560 _28394). Qed.
Lemma lem1207562 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (@List.map _28394 _28392 f) = (@List.map _28394 _28392 f).
Proof. exact (eq_refl (@List.map _28394 _28392 f)). Qed.
Lemma lem1207563 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term5 _28392 _28394 f) = (@List.map _28394 _28392 f (@nil _28394)).
Proof. exact (MK_COMB (@lem1207562 _28392 _28394 f) (@lem1207561 _28394)). Qed.
Lemma lem1207565 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1207544 A B f) (@lem1207543 A B f)). Qed.
Lemma lem1207566 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (@List.map _28394 _28392 f (@nil _28394)) = (@nil _28392).
Proof. exact (@lem1207565 _28394 _28392 f). Qed.
Lemma lem1207567 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term5 _28392 _28394 f) = (@nil _28392).
Proof. exact (TRANS (@lem1207563 _28392 _28394 f) (@lem1207566 _28392 _28394 f)). Qed.
Lemma lem1207568 {_28392 _28394 : Type'} (f : _28394 -> _28392) : ((term4 _28392 _28394 f) = (term5 _28392 _28394 f)) = ((@nil _28392) = (@nil _28392)).
Proof. exact (MK_COMB (@lem1207558 _28392 _28394 f) (@lem1207567 _28392 _28394 f)). Qed.
Lemma lem1207570 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1207571 {_28392 : Type'} (x : list _28392) : (x = x) = True.
Proof. exact (@lem1207570 (list _28392) x). Qed.
Lemma lem1207572 {_28392 : Type'} : ((@nil _28392) = (@nil _28392)) = True.
Proof. exact (@lem1207571 _28392 (@nil _28392)). Qed.
Lemma lem1207573 {_28392 _28394 : Type'} (f : _28394 -> _28392) : ((term4 _28392 _28394 f) = (term5 _28392 _28394 f)) = True.
Proof. exact (TRANS (@lem1207568 _28392 _28394 f) (@lem1207572 _28392)). Qed.
Lemma lem1207574 {_28392 _28394 : Type'} (f : _28394 -> _28392) : True = ((term4 _28392 _28394 f) = (term5 _28392 _28394 f)).
Proof. exact (SYM (@lem1207573 _28392 _28394 f)). Qed.
Lemma lem1207575 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (term4 _28392 _28394 f) = (term5 _28392 _28394 f).
Proof. exact (EQ_MP (@lem1207574 _28392 _28394 f) (@lem0)). Qed.
Lemma lem1207576 {A B : Type'} (f : A -> B) : term37 A B f.
Proof. exact (@lem1116758 A B f). Qed.
Lemma lem1207577 {A B : Type'} (f : A -> B) : (term37 A B f) = (term38 A B f).
Proof. exact (eq_refl (term37 A B f)). Qed.
Lemma lem1207578 {A B : Type'} (f : A -> B) : term38 A B f.
Proof. exact (EQ_MP (@lem1207577 A B f) (@lem1207576 A B f)). Qed.
Lemma lem1207579 {A B : Type'} (f : A -> B) (l1 : list A) : term39 A B f l1.
Proof. exact (@lem1207578 A B f l1). Qed.
Lemma lem1207580 {A B : Type'} (l1 : list A) (f : A -> B) : (term39 A B f l1) = (term40 A B l1 f).
Proof. exact (eq_refl (term39 A B f l1)). Qed.
Lemma lem1207581 {A B : Type'} (l1 : list A) (f : A -> B) : term40 A B l1 f.
Proof. exact (EQ_MP (@lem1207580 A B l1 f) (@lem1207579 A B f l1)). Qed.
Lemma lem1207582 {A B : Type'} (l1 : list A) (f : A -> B) (l2 : list A) : term41 A B l1 f l2.
Proof. exact (@lem1207581 A B l1 f l2). Qed.
Lemma lem1207583 {A B : Type'} (l1 : list A) (f : A -> B) (l2 : list A) : (term41 A B l1 f l2) = ((term42 A B f l1 l2) = (term43 A B l1 f l2)).
Proof. exact (eq_refl (term41 A B l1 f l2)). Qed.
Lemma lem1207587 {A B : Type'} : term44 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1207588 {A B : Type'} (f : A -> B) : term45 A B f.
Proof. exact (@lem1207587 A B f). Qed.
Lemma lem1207589 {A B : Type'} (f : A -> B) : (term45 A B f) = (term46 A B f).
Proof. exact (eq_refl (term45 A B f)). Qed.
Lemma lem1207590 {A B : Type'} (f : A -> B) : term46 A B f.
Proof. exact (EQ_MP (@lem1207589 A B f) (@lem1207588 A B f)). Qed.
Lemma lem1207591 {A B : Type'} (f : A -> B) (h : A) : term47 A B f h.
Proof. exact (@lem1207590 A B f h). Qed.
Lemma lem1207592 {A B : Type'} (h : A) (f : A -> B) : (term47 A B f h) = (term48 A B h f).
Proof. exact (eq_refl (term47 A B f h)). Qed.
Lemma lem1207593 {A B : Type'} (h : A) (f : A -> B) : term48 A B h f.
Proof. exact (EQ_MP (@lem1207592 A B h f) (@lem1207591 A B f h)). Qed.
Lemma lem1207594 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term49 A B h f t.
Proof. exact (@lem1207593 A B h f t). Qed.
Lemma lem1207595 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term49 A B h f t) = ((term50 A B f h t) = (term51 A B h f t)).
Proof. exact (eq_refl (term49 A B h f t)). Qed.
Lemma lem1207597 {A B : Type'} : term34 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1207598 {A B : Type'} (f : A -> B) : term35 A B f.
Proof. exact (@lem1207597 A B f). Qed.
Lemma lem1207599 {A B : Type'} (f : A -> B) : (term35 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term35 A B f)). Qed.
Lemma lem1207604 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term50 A B f h t) = (term51 A B h f t).
Proof. exact (EQ_MP (@lem1207595 A B h f t) (@lem1207594 A B h f t)). Qed.
Lemma lem1207605 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) : (term52 _28392 _28394 f h t) = (term53 _28392 _28394 h f t).
Proof. exact (@lem1207604 _28394 _28392 h f t). Qed.
Lemma lem1207606 {_28392 : Type'} : (@List.rev _28392) = (@List.rev _28392).
Proof. exact (eq_refl (@List.rev _28392)). Qed.
Lemma lem1207607 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) : (term14 _28392 _28394 f h t) = (term54 _28392 _28394 h f t).
Proof. exact (MK_COMB (@lem1207606 _28392) (@lem1207605 _28392 _28394 h f t)). Qed.
Lemma lem1207609 {A : Type'} (l : list A) (x : A) : (term55 A x l) = (term56 A l x).
Proof. exact (EQ_MP (@lem1096524 A l x) (@lem1096523 A l x)). Qed.
Lemma lem1207610 {_28392 : Type'} (l : list _28392) (x : _28392) : (term55 _28392 x l) = (term56 _28392 l x).
Proof. exact (@lem1207609 _28392 l x). Qed.
Lemma lem1207611 {_28392 _28394 : Type'} (t : list _28394) (f : _28394 -> _28392) (h : _28394) : (term54 _28392 _28394 h f t) = (term57 _28392 _28394 t f h).
Proof. exact (@lem1207610 _28392 (@List.map _28394 _28392 f t) (f h)). Qed.
Lemma lem1207613 {_28392 _28394 : Type'} (f : _28394 -> _28392) (t : list _28394) (h1 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)) : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t).
Proof. exact (h1). Qed.
Lemma lem1207614 {_28392 : Type'} : (@List.app _28392) = (@List.app _28392).
Proof. exact (eq_refl (@List.app _28392)). Qed.
Lemma lem1207615 {_28392 _28394 : Type'} (f : _28394 -> _28392) (t : list _28394) (h1 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)) : (term58 _28392 _28394 f t) = (term59 _28392 _28394 f t).
Proof. exact (MK_COMB (@lem1207614 _28392) (@lem1207613 _28392 _28394 f t h1)). Qed.
Lemma lem1207616 {_28392 _28394 : Type'} (f : _28394 -> _28392) (h : _28394) : (term60 _28392 _28394 f h) = (term60 _28392 _28394 f h).
Proof. exact (eq_refl (term60 _28392 _28394 f h)). Qed.
Lemma lem1207617 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) (h1 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)) : (term57 _28392 _28394 t f h) = (term61 _28392 _28394 t f h).
Proof. exact (MK_COMB (@lem1207615 _28392 _28394 f t h1) (@lem1207616 _28392 _28394 f h)). Qed.
Lemma lem1207618 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) (h1 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)) : (term54 _28392 _28394 h f t) = (term61 _28392 _28394 t f h).
Proof. exact (TRANS (@lem1207611 _28392 _28394 t f h) (@lem1207617 _28392 _28394 h f t h1)). Qed.
Lemma lem1207619 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) (h1 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)) : (term14 _28392 _28394 f h t) = (term61 _28392 _28394 t f h).
Proof. exact (TRANS (@lem1207607 _28392 _28394 h f t) (@lem1207618 _28392 _28394 h f t h1)). Qed.
Lemma lem1207620 {_28392 : Type'} : (@eq (list _28392)) = (@eq (list _28392)).
Proof. exact (eq_refl (@eq (list _28392))). Qed.
Lemma lem1207621 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) (h1 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)) : (term62 _28392 _28394 f h t) = (term63 _28392 _28394 t f h).
Proof. exact (MK_COMB (@lem1207620 _28392) (@lem1207619 _28392 _28394 h f t h1)). Qed.
Lemma lem1207623 {A : Type'} (l : list A) (x : A) : (term55 A x l) = (term56 A l x).
Proof. exact (EQ_MP (@lem1096524 A l x) (@lem1096523 A l x)). Qed.
Lemma lem1207624 {_28394 : Type'} (l : list _28394) (x : _28394) : (term55 _28394 x l) = (term56 _28394 l x).
Proof. exact (@lem1207623 _28394 l x). Qed.
Lemma lem1207625 {_28394 : Type'} (t : list _28394) (h : _28394) : (term55 _28394 h t) = (term56 _28394 t h).
Proof. exact (@lem1207624 _28394 t h). Qed.
Lemma lem1207626 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (@List.map _28394 _28392 f) = (@List.map _28394 _28392 f).
Proof. exact (eq_refl (@List.map _28394 _28392 f)). Qed.
Lemma lem1207627 {_28392 _28394 : Type'} (f : _28394 -> _28392) (t : list _28394) (h : _28394) : (term15 _28392 _28394 f h t) = (term64 _28392 _28394 f t h).
Proof. exact (MK_COMB (@lem1207626 _28392 _28394 f) (@lem1207625 _28394 t h)). Qed.
Lemma lem1207629 {A B : Type'} (l1 : list A) (f : A -> B) (l2 : list A) : (term42 A B f l1 l2) = (term43 A B l1 f l2).
Proof. exact (EQ_MP (@lem1207583 A B l1 f l2) (@lem1207582 A B l1 f l2)). Qed.
Lemma lem1207630 {_28392 _28394 : Type'} (l1 : list _28394) (f : _28394 -> _28392) (l2 : list _28394) : (term65 _28392 _28394 f l1 l2) = (term66 _28392 _28394 l1 f l2).
Proof. exact (@lem1207629 _28394 _28392 l1 f l2). Qed.
Lemma lem1207631 {_28392 _28394 : Type'} (t : list _28394) (f : _28394 -> _28392) (h : _28394) : (term64 _28392 _28394 f t h) = (term67 _28392 _28394 t f h).
Proof. exact (@lem1207630 _28392 _28394 (@List.rev _28394 t) f (@cons _28394 h (@nil _28394))). Qed.
Lemma lem1207633 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term50 A B f h t) = (term51 A B h f t).
Proof. exact (EQ_MP (@lem1207595 A B h f t) (@lem1207594 A B h f t)). Qed.
Lemma lem1207634 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) : (term52 _28392 _28394 f h t) = (term53 _28392 _28394 h f t).
Proof. exact (@lem1207633 _28394 _28392 h f t). Qed.
Lemma lem1207635 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) : (term68 _28392 _28394 f h) = (term69 _28392 _28394 h f).
Proof. exact (@lem1207634 _28392 _28394 h f (@nil _28394)). Qed.
Lemma lem1207637 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1207599 A B f) (@lem1207598 A B f)). Qed.
Lemma lem1207638 {_28392 _28394 : Type'} (f : _28394 -> _28392) : (@List.map _28394 _28392 f (@nil _28394)) = (@nil _28392).
Proof. exact (@lem1207637 _28394 _28392 f). Qed.
Lemma lem1207639 {_28392 _28394 : Type'} (f : _28394 -> _28392) (h : _28394) : (term70 _28392 _28394 f h) = (term70 _28392 _28394 f h).
Proof. exact (eq_refl (term70 _28392 _28394 f h)). Qed.
Lemma lem1207640 {_28392 _28394 : Type'} (f : _28394 -> _28392) (h : _28394) : (term69 _28392 _28394 h f) = (term60 _28392 _28394 f h).
Proof. exact (MK_COMB (@lem1207639 _28392 _28394 f h) (@lem1207638 _28392 _28394 f)). Qed.
Lemma lem1207641 {_28392 _28394 : Type'} (f : _28394 -> _28392) (h : _28394) : (term68 _28392 _28394 f h) = (term60 _28392 _28394 f h).
Proof. exact (TRANS (@lem1207635 _28392 _28394 h f) (@lem1207640 _28392 _28394 f h)). Qed.
Lemma lem1207642 {_28392 _28394 : Type'} (f : _28394 -> _28392) (t : list _28394) : (term59 _28392 _28394 f t) = (term59 _28392 _28394 f t).
Proof. exact (eq_refl (term59 _28392 _28394 f t)). Qed.
Lemma lem1207643 {_28392 _28394 : Type'} (t : list _28394) (f : _28394 -> _28392) (h : _28394) : (term67 _28392 _28394 t f h) = (term61 _28392 _28394 t f h).
Proof. exact (MK_COMB (@lem1207642 _28392 _28394 f t) (@lem1207641 _28392 _28394 f h)). Qed.
Lemma lem1207644 {_28392 _28394 : Type'} (t : list _28394) (f : _28394 -> _28392) (h : _28394) : (term64 _28392 _28394 f t h) = (term61 _28392 _28394 t f h).
Proof. exact (TRANS (@lem1207631 _28392 _28394 t f h) (@lem1207643 _28392 _28394 t f h)). Qed.
Lemma lem1207645 {_28392 _28394 : Type'} (t : list _28394) (f : _28394 -> _28392) (h : _28394) : (term15 _28392 _28394 f h t) = (term61 _28392 _28394 t f h).
Proof. exact (TRANS (@lem1207627 _28392 _28394 f t h) (@lem1207644 _28392 _28394 t f h)). Qed.
Lemma lem1207646 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) (h1 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)) : ((term14 _28392 _28394 f h t) = (term15 _28392 _28394 f h t)) = ((term61 _28392 _28394 t f h) = (term61 _28392 _28394 t f h)).
Proof. exact (MK_COMB (@lem1207621 _28392 _28394 h f t h1) (@lem1207645 _28392 _28394 t f h)). Qed.
Lemma lem1207648 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1207649 {_28392 : Type'} (x : list _28392) : (x = x) = True.
Proof. exact (@lem1207648 (list _28392) x). Qed.
Lemma lem1207650 {_28392 _28394 : Type'} (t : list _28394) (f : _28394 -> _28392) (h : _28394) : ((term61 _28392 _28394 t f h) = (term61 _28392 _28394 t f h)) = True.
Proof. exact (@lem1207649 _28392 (term61 _28392 _28394 t f h)). Qed.
Lemma lem1207651 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) (h1 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)) : ((term14 _28392 _28394 f h t) = (term15 _28392 _28394 f h t)) = True.
Proof. exact (TRANS (@lem1207646 _28392 _28394 h f t h1) (@lem1207650 _28392 _28394 t f h)). Qed.
Lemma lem1207652 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) (h1 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)) : True = ((term14 _28392 _28394 f h t) = (term15 _28392 _28394 f h t)).
Proof. exact (SYM (@lem1207651 _28392 _28394 h f t h1)). Qed.
Lemma lem1207653 {_28392 _28394 : Type'} (h : _28394) (f : _28394 -> _28392) (t : list _28394) (h1 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t)) : (term14 _28392 _28394 f h t) = (term15 _28392 _28394 f h t).
Proof. exact (EQ_MP (@lem1207652 _28392 _28394 h f t h1) (@lem0)). Qed.
Lemma lem1207654 {_28392 _28394 : Type'} (f : _28394 -> _28392) (h : _28394) (t : list _28394) : term17 _28392 _28394 f h t.
Proof. exact (fun h0 : (term9 _28392 _28394 f t) = (term10 _28392 _28394 f t) => @lem1207653 _28392 _28394 h f t h0). Qed.
Lemma lem1207659 {_28392 _28394 : Type'} (f : _28394 -> _28392) (h : _28394) : term21 _28392 _28394 f h.
Proof. exact (fun t : list _28394 => @lem1207654 _28392 _28394 f h t). Qed.
Lemma lem1207664 {_28392 _28394 : Type'} (f : _28394 -> _28392) : term25 _28392 _28394 f.
Proof. exact (fun h : _28394 => @lem1207659 _28392 _28394 f h). Qed.
Lemma lem1207665 {_28392 _28394 : Type'} (f : _28394 -> _28392) : term27 _28392 _28394 f.
Proof. exact (conj (@lem1207575 _28392 _28394 f) (@lem1207664 _28392 _28394 f)). Qed.
Lemma lem1207666 {_28392 _28394 : Type'} (f : _28394 -> _28392) : term32 _28392 _28394 f.
Proof. exact (@lem1207519 _28392 _28394 f (@lem1207665 _28392 _28394 f)). Qed.
Lemma lem1207671 {_28392 _28394 : Type'} : term71 _28392 _28394.
Proof. exact (fun f : _28394 -> _28392 => @lem1207666 _28392 _28394 f). Qed.
