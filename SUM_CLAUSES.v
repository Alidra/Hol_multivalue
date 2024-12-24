Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CLAUSES_term_abbrevs.
Require Import ITERATE_CLAUSES_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import NEUTRAL_REAL_ADD_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7067460 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7067462 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem7067463 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem7067462 _120477 _120519 _120521 h1 op). Qed.
Lemma lem7067464 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem7067465 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem7067464 _120477 _120519 _120521 op) (@lem7067463 _120477 _120519 _120521 op h1)). Qed.
Lemma lem7067466 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem7067467 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem7067465 _120477 _120519 _120521 op h1 (@lem7067466 _120519 op h2)). Qed.
Lemma lem7067468 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term4 _120477 _120519 _120521 op.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem7067467 _120477 _120519 _120521 op h0 h1). Qed.
Lemma lem7067469 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem7067470 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem7067468 _120477 _120519 _120521 op h2 (@lem7067469 _120477 _120519 _120521 h1)). Qed.
Lemma lem7067471 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem7067470 _120477 _120519 _120521 op h1 h0). Qed.
Lemma lem7067472 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (fun op : type1400 _120519 => @lem7067471 _120477 _120519 _120521 op h1). Qed.
Lemma lem7067473 {_120477 _120519 _120521 : Type'} : term5 _120477 _120519 _120521.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem7067472 _120477 _120519 _120521 h0). Qed.
Lemma lem7067474 {_120477 _120519 _120521 : Type'} : term0 _120477 _120519 _120521.
Proof. exact (@lem7067473 _120477 _120519 _120521 (@lem5753565 _120477 _120519 _120521)). Qed.
Lemma lem7067475 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem7067474 _120477 _120519 _120521 op). Qed.
Lemma lem7067476 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem7067478 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem7067479 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term7 A B P) = (term8 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem7067481 (h1 : (@neutral real real_add) = term9) : (@neutral real real_add) = term9.
Proof. exact (h1). Qed.
Lemma lem7067482 (h1 : (@neutral real real_add) = term9) : term9 = (@neutral real real_add).
Proof. exact (SYM (@lem7067481 h1)). Qed.
Lemma lem7067483 (h1 : term9 = (@neutral real real_add)) : term9 = (@neutral real real_add).
Proof. exact (h1). Qed.
Lemma lem7067484 (h1 : term9 = (@neutral real real_add)) : (@neutral real real_add) = term9.
Proof. exact (SYM (@lem7067483 h1)). Qed.
Lemma lem7067485 : ((@neutral real real_add) = term9) = (term9 = (@neutral real real_add)).
Proof. exact (prop_ext (fun h1 : (@neutral real real_add) = term9 => @lem7067482 h1) (fun h1 : term9 = (@neutral real real_add) => @lem7067484 h1)). Qed.
Lemma lem7067496 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7067497 {_131483 : Type'} : (@sum _131483) = (@iterate real _131483 real_add).
Proof. exact (@lem7067496 _131483). Qed.
Lemma lem7067498 {_131483 : Type'} : (@EMPTY _131483) = (@EMPTY _131483).
Proof. exact (eq_refl (@EMPTY _131483)). Qed.
Lemma lem7067499 {_131483 : Type'} : (@sum _131483 (@EMPTY _131483)) = (@iterate real _131483 real_add (@EMPTY _131483)).
Proof. exact (MK_COMB (@lem7067497 _131483) (@lem7067498 _131483)). Qed.
Lemma lem7067500 {_131483 : Type'} (f : _131483 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7067501 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = (@iterate real _131483 real_add (@EMPTY _131483) f).
Proof. exact (MK_COMB (@lem7067499 _131483) (@lem7067500 _131483 f)). Qed.
Lemma lem7067502 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7067503 {_131483 : Type'} (f : _131483 -> real) : (term10 _131483 f) = (term11 _131483 f).
Proof. exact (MK_COMB (@lem7067502) (@lem7067501 _131483 f)). Qed.
Lemma lem7067505 : term9 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7067485) (@lem7065438)). Qed.
Lemma lem7067506 {_131483 : Type'} (f : _131483 -> real) : ((@sum _131483 (@EMPTY _131483) f) = term9) = ((@iterate real _131483 real_add (@EMPTY _131483) f) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7067503 _131483 f) (@lem7067505)). Qed.
Lemma lem7067509 {_131483 : Type'} : (term12 _131483) = (term13 _131483).
Proof. exact (fun_ext (fun f : _131483 -> real => @lem7067506 _131483 f)). Qed.
Lemma lem7067510 {_131483 : Type'} : (@all (_131483 -> real)) = (@all (_131483 -> real)).
Proof. exact (eq_refl (@all (_131483 -> real))). Qed.
Lemma lem7067511 {_131483 : Type'} : (term14 _131483) = (term15 _131483).
Proof. exact (MK_COMB (@lem7067510 _131483) (@lem7067509 _131483)). Qed.
Lemma lem7067516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7067517 {_131483 : Type'} : (term16 _131483) = (term17 _131483).
Proof. exact (MK_COMB (@lem7067516) (@lem7067511 _131483)). Qed.
Lemma lem7067535 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7067536 {_131524 : Type'} : (@sum _131524) = (@iterate real _131524 real_add).
Proof. exact (@lem7067535 _131524). Qed.
Lemma lem7067537 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) : (@INSERT _131524 x s) = (@INSERT _131524 x s).
Proof. exact (eq_refl (@INSERT _131524 x s)). Qed.
Lemma lem7067538 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) : (term18 _131524 x s) = (term19 _131524 x s).
Proof. exact (MK_COMB (@lem7067536 _131524) (@lem7067537 _131524 x s)). Qed.
Lemma lem7067539 {_131524 : Type'} (f : _131524 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7067540 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term20 _131524 x s f) = (term21 _131524 x s f).
Proof. exact (MK_COMB (@lem7067538 _131524 x s) (@lem7067539 _131524 f)). Qed.
Lemma lem7067541 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7067542 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term22 _131524 x s f) = (term23 _131524 x s f).
Proof. exact (MK_COMB (@lem7067541) (@lem7067540 _131524 x s f)). Qed.
Lemma lem7067544 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7067545 {_131524 : Type'} : (@sum _131524) = (@iterate real _131524 real_add).
Proof. exact (@lem7067544 _131524). Qed.
Lemma lem7067546 {_131524 : Type'} (s : _131524 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7067547 {_131524 : Type'} (s : _131524 -> Prop) : (@sum _131524 s) = (@iterate real _131524 real_add s).
Proof. exact (MK_COMB (@lem7067545 _131524) (@lem7067546 _131524 s)). Qed.
Lemma lem7067548 {_131524 : Type'} (f : _131524 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7067549 {_131524 : Type'} (s : _131524 -> Prop) (f : _131524 -> real) : (@sum _131524 s f) = (@iterate real _131524 real_add s f).
Proof. exact (MK_COMB (@lem7067547 _131524 s) (@lem7067548 _131524 f)). Qed.
Lemma lem7067550 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) : (term24 _131524 x s) = (term24 _131524 x s).
Proof. exact (eq_refl (term24 _131524 x s)). Qed.
Lemma lem7067551 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term25 _131524 x s f) = (term26 _131524 x s f).
Proof. exact (MK_COMB (@lem7067550 _131524 x s) (@lem7067549 _131524 s f)). Qed.
Lemma lem7067553 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7067554 {_131524 : Type'} : (@sum _131524) = (@iterate real _131524 real_add).
Proof. exact (@lem7067553 _131524). Qed.
Lemma lem7067555 {_131524 : Type'} (s : _131524 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7067556 {_131524 : Type'} (s : _131524 -> Prop) : (@sum _131524 s) = (@iterate real _131524 real_add s).
Proof. exact (MK_COMB (@lem7067554 _131524) (@lem7067555 _131524 s)). Qed.
Lemma lem7067557 {_131524 : Type'} (f : _131524 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7067558 {_131524 : Type'} (s : _131524 -> Prop) (f : _131524 -> real) : (@sum _131524 s f) = (@iterate real _131524 real_add s f).
Proof. exact (MK_COMB (@lem7067556 _131524 s) (@lem7067557 _131524 f)). Qed.
Lemma lem7067559 {_131524 : Type'} (f : _131524 -> real) (x : _131524) : (term27 _131524 f x) = (term27 _131524 f x).
Proof. exact (eq_refl (term27 _131524 f x)). Qed.
Lemma lem7067560 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term28 _131524 x s f) = (term29 _131524 x s f).
Proof. exact (MK_COMB (@lem7067559 _131524 f x) (@lem7067558 _131524 s f)). Qed.
Lemma lem7067561 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term30 _131524 x s f) = (term31 _131524 x s f).
Proof. exact (MK_COMB (@lem7067551 _131524 x s f) (@lem7067560 _131524 x s f)). Qed.
Lemma lem7067562 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : ((term20 _131524 x s f) = (term30 _131524 x s f)) = ((term21 _131524 x s f) = (term31 _131524 x s f)).
Proof. exact (MK_COMB (@lem7067542 _131524 x s f) (@lem7067561 _131524 x s f)). Qed.
Lemma lem7067565 {_131524 : Type'} (s : _131524 -> Prop) : (term32 _131524 s) = (term32 _131524 s).
Proof. exact (eq_refl (term32 _131524 s)). Qed.
Lemma lem7067566 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term33 _131524 x s f) = (term34 _131524 x s f).
Proof. exact (MK_COMB (@lem7067565 _131524 s) (@lem7067562 _131524 x s f)). Qed.
Lemma lem7067569 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term35 _131524 x f) = (term36 _131524 x f).
Proof. exact (fun_ext (fun s : _131524 -> Prop => @lem7067566 _131524 x s f)). Qed.
Lemma lem7067570 {_131524 : Type'} : (@all (_131524 -> Prop)) = (@all (_131524 -> Prop)).
Proof. exact (eq_refl (@all (_131524 -> Prop))). Qed.
Lemma lem7067571 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term37 _131524 x f) = (term38 _131524 x f).
Proof. exact (MK_COMB (@lem7067570 _131524) (@lem7067569 _131524 x f)). Qed.
Lemma lem7067576 {_131524 : Type'} (x : _131524) : (term39 _131524 x) = (term40 _131524 x).
Proof. exact (fun_ext (fun f : _131524 -> real => @lem7067571 _131524 x f)). Qed.
Lemma lem7067577 {_131524 : Type'} : (@all (_131524 -> real)) = (@all (_131524 -> real)).
Proof. exact (eq_refl (@all (_131524 -> real))). Qed.
Lemma lem7067578 {_131524 : Type'} (x : _131524) : (term41 _131524 x) = (term42 _131524 x).
Proof. exact (MK_COMB (@lem7067577 _131524) (@lem7067576 _131524 x)). Qed.
Lemma lem7067583 {_131524 : Type'} : (term43 _131524) = (term44 _131524).
Proof. exact (fun_ext (fun x : _131524 => @lem7067578 _131524 x)). Qed.
Lemma lem7067584 {_131524 : Type'} : (@all _131524) = (@all _131524).
Proof. exact (eq_refl (@all _131524)). Qed.
Lemma lem7067585 {_131524 : Type'} : (term45 _131524) = (term46 _131524).
Proof. exact (MK_COMB (@lem7067584 _131524) (@lem7067583 _131524)). Qed.
Lemma lem7067590 {_131483 _131524 : Type'} : (term47 _131483 _131524) = (term48 _131483 _131524).
Proof. exact (MK_COMB (@lem7067517 _131483) (@lem7067585 _131524)). Qed.
Lemma lem7067593 {_131483 _131524 : Type'} : (term48 _131483 _131524) = (term47 _131483 _131524).
Proof. exact (SYM (@lem7067590 _131483 _131524)). Qed.
Lemma lem7067603 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (EQ_MP (@lem7067479 A B P) (@lem7067478 A B P)). Qed.
Lemma lem7067604 {_131524 : Type'} (P : type1367 _131524) : (term49 _131524 P) = (term50 _131524 P).
Proof. exact (@lem7067603 _131524 (_131524 -> real) P). Qed.
Lemma lem7067605 {_131524 : Type'} : (term51 _131524) = (term52 _131524).
Proof. exact (@lem7067604 _131524 (term53 _131524)). Qed.
Lemma lem7067606 {_131524 : Type'} (x : _131524) : (term54 _131524 x) = (term40 _131524 x).
Proof. exact (eq_refl (term54 _131524 x)). Qed.
Lemma lem7067607 {_131524 : Type'} (f : _131524 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7067608 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term55 _131524 x f) = (term56 _131524 x f).
Proof. exact (MK_COMB (@lem7067606 _131524 x) (@lem7067607 _131524 f)). Qed.
Lemma lem7067609 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term56 _131524 x f) = (term38 _131524 x f).
Proof. exact (eq_refl (term56 _131524 x f)). Qed.
Lemma lem7067610 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term55 _131524 x f) = (term38 _131524 x f).
Proof. exact (TRANS (@lem7067608 _131524 x f) (@lem7067609 _131524 x f)). Qed.
Lemma lem7067611 {_131524 : Type'} (x : _131524) : (term57 _131524 x) = (term40 _131524 x).
Proof. exact (fun_ext (fun f : _131524 -> real => @lem7067610 _131524 x f)). Qed.
Lemma lem7067612 {_131524 : Type'} : (@all (_131524 -> real)) = (@all (_131524 -> real)).
Proof. exact (eq_refl (@all (_131524 -> real))). Qed.
Lemma lem7067613 {_131524 : Type'} (x : _131524) : (term58 _131524 x) = (term42 _131524 x).
Proof. exact (MK_COMB (@lem7067612 _131524) (@lem7067611 _131524 x)). Qed.
Lemma lem7067614 {_131524 : Type'} : (term59 _131524) = (term44 _131524).
Proof. exact (fun_ext (fun x : _131524 => @lem7067613 _131524 x)). Qed.
Lemma lem7067615 {_131524 : Type'} : (@all _131524) = (@all _131524).
Proof. exact (eq_refl (@all _131524)). Qed.
Lemma lem7067616 {_131524 : Type'} : (term51 _131524) = (term46 _131524).
Proof. exact (MK_COMB (@lem7067615 _131524) (@lem7067614 _131524)). Qed.
Lemma lem7067617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7067618 {_131524 : Type'} : (term60 _131524) = (term61 _131524).
Proof. exact (MK_COMB (@lem7067617) (@lem7067616 _131524)). Qed.
Lemma lem7067619 {_131524 : Type'} (x : _131524) : (term54 _131524 x) = (term40 _131524 x).
Proof. exact (eq_refl (term54 _131524 x)). Qed.
Lemma lem7067620 {_131524 : Type'} (f : _131524 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7067621 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term55 _131524 x f) = (term56 _131524 x f).
Proof. exact (MK_COMB (@lem7067619 _131524 x) (@lem7067620 _131524 f)). Qed.
Lemma lem7067622 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term56 _131524 x f) = (term38 _131524 x f).
Proof. exact (eq_refl (term56 _131524 x f)). Qed.
Lemma lem7067623 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term55 _131524 x f) = (term38 _131524 x f).
Proof. exact (TRANS (@lem7067621 _131524 x f) (@lem7067622 _131524 x f)). Qed.
Lemma lem7067624 {_131524 : Type'} (f : _131524 -> real) : (term62 _131524 f) = (term63 _131524 f).
Proof. exact (fun_ext (fun x : _131524 => @lem7067623 _131524 x f)). Qed.
Lemma lem7067625 {_131524 : Type'} : (@all _131524) = (@all _131524).
Proof. exact (eq_refl (@all _131524)). Qed.
Lemma lem7067626 {_131524 : Type'} (f : _131524 -> real) : (term64 _131524 f) = (term65 _131524 f).
Proof. exact (MK_COMB (@lem7067625 _131524) (@lem7067624 _131524 f)). Qed.
Lemma lem7067627 {_131524 : Type'} : (term66 _131524) = (term67 _131524).
Proof. exact (fun_ext (fun f : _131524 -> real => @lem7067626 _131524 f)). Qed.
Lemma lem7067628 {_131524 : Type'} : (@all (_131524 -> real)) = (@all (_131524 -> real)).
Proof. exact (eq_refl (@all (_131524 -> real))). Qed.
Lemma lem7067629 {_131524 : Type'} : (term52 _131524) = (term68 _131524).
Proof. exact (MK_COMB (@lem7067628 _131524) (@lem7067627 _131524)). Qed.
Lemma lem7067630 {_131524 : Type'} : ((term51 _131524) = (term52 _131524)) = ((term46 _131524) = (term68 _131524)).
Proof. exact (MK_COMB (@lem7067618 _131524) (@lem7067629 _131524)). Qed.
Lemma lem7067631 {_131524 : Type'} : (term46 _131524) = (term68 _131524).
Proof. exact (EQ_MP (@lem7067630 _131524) (@lem7067605 _131524)). Qed.
Lemma lem7067632 {_131483 : Type'} : (term17 _131483) = (term17 _131483).
Proof. exact (eq_refl (term17 _131483)). Qed.
Lemma lem7067633 {_131483 _131524 : Type'} : (term48 _131483 _131524) = (term69 _131483 _131524).
Proof. exact (MK_COMB (@lem7067632 _131483) (@lem7067631 _131524)). Qed.
Lemma lem7067634 {_131483 _131524 : Type'} : (term69 _131483 _131524) = (term48 _131483 _131524).
Proof. exact (SYM (@lem7067633 _131483 _131524)). Qed.
Lemma lem7067636 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem7067476 _120477 _120519 _120521 op) (@lem7067475 _120477 _120519 _120521 op)). Qed.
Lemma lem7067637 {_131483 _131524 : Type'} (op : type1627) : term70 _131483 _131524 op.
Proof. exact (@lem7067636 _131483 real _131524 op). Qed.
Lemma lem7067638 {_131483 _131524 : Type'} : term71 _131483 _131524.
Proof. exact (@lem7067637 _131483 _131524 real_add). Qed.
Lemma lem7067640 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7067460) (@lem7067132)). Qed.
Lemma lem7067641 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7067640)). Qed.
Lemma lem7067642 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7067641) (@lem0)). Qed.
Lemma lem7067643 {_131483 _131524 : Type'} : term69 _131483 _131524.
Proof. exact (@lem7067638 _131483 _131524 (@lem7067642)). Qed.
Lemma lem7067644 {_131483 _131524 : Type'} : term48 _131483 _131524.
Proof. exact (EQ_MP (@lem7067634 _131483 _131524) (@lem7067643 _131483 _131524)). Qed.
Lemma lem7067645 {_131483 _131524 : Type'} : term47 _131483 _131524.
Proof. exact (EQ_MP (@lem7067593 _131483 _131524) (@lem7067644 _131483 _131524)). Qed.
