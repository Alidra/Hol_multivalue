Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1102759_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1102496 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1102497 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1102498 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1102497 A B f) (@lem1102496 A B f)). Qed.
Lemma lem1102499 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1102498 A B f y). Qed.
Lemma lem1102500 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1102503 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : MEM' = (term4 _25376 _17991).
Proof. exact (h1). Qed.
Lemma lem1102504 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1102505 {_25376 : Type'} (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (MEM' x) = (term5 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102503 _25376 MEM' _17991 h1) (@lem1102504 _25376 x)). Qed.
Lemma lem1102507 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1102500 A B f y) (@lem1102499 A B f y)). Qed.
Lemma lem1102508 {_25376 : Type'} (f : type1398 _25376) (y : _25376) : (term6 _25376 f y) = (f y).
Proof. exact (@lem1102507 _25376 (type1143 _25376) f y). Qed.
Lemma lem1102509 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term7 _25376 _17991 x) = (term5 _25376 _17991 x).
Proof. exact (@lem1102508 _25376 (term4 _25376 _17991) x). Qed.
Lemma lem1102510 {_25376 : Type'} (_17991 : type1136 _25376) (_17989 : _25376) : (term5 _25376 _17991 _17989) = (term8 _25376 _17991 _17989).
Proof. exact (eq_refl (term5 _25376 _17991 _17989)). Qed.
Lemma lem1102511 {_25376 : Type'} (_17991 : type1136 _25376) : (term9 _25376 _17991) = (term4 _25376 _17991).
Proof. exact (fun_ext (fun _17989 : _25376 => @lem1102510 _25376 _17991 _17989)). Qed.
Lemma lem1102512 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1102513 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term7 _25376 _17991 x) = (term5 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102511 _25376 _17991) (@lem1102512 _25376 x)). Qed.
Lemma lem1102514 {_25376 : Type'} : (@eq ((list _25376) -> Prop)) = (@eq ((list _25376) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25376) -> Prop))). Qed.
Lemma lem1102515 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term10 _25376 _17991 x) = (term11 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102514 _25376) (@lem1102513 _25376 _17991 x)). Qed.
Lemma lem1102516 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term5 _25376 _17991 x) = (term8 _25376 _17991 x).
Proof. exact (eq_refl (term5 _25376 _17991 x)). Qed.
Lemma lem1102517 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : ((term7 _25376 _17991 x) = (term5 _25376 _17991 x)) = ((term5 _25376 _17991 x) = (term8 _25376 _17991 x)).
Proof. exact (MK_COMB (@lem1102515 _25376 _17991 x) (@lem1102516 _25376 _17991 x)). Qed.
Lemma lem1102518 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term5 _25376 _17991 x) = (term8 _25376 _17991 x).
Proof. exact (EQ_MP (@lem1102517 _25376 _17991 x) (@lem1102509 _25376 _17991 x)). Qed.
Lemma lem1102519 {_25376 : Type'} (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (MEM' x) = (term8 _25376 _17991 x).
Proof. exact (TRANS (@lem1102505 _25376 x MEM' _17991 h1) (@lem1102518 _25376 _17991 x)). Qed.
Lemma lem1102520 {_25376 : Type'} : (@nil _25376) = (@nil _25376).
Proof. exact (eq_refl (@nil _25376)). Qed.
Lemma lem1102521 {_25376 : Type'} (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (MEM' x (@nil _25376)) = (term12 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102519 _25376 x MEM' _17991 h1) (@lem1102520 _25376)). Qed.
Lemma lem1102523 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1102500 A B f y) (@lem1102499 A B f y)). Qed.
Lemma lem1102524 {_25376 : Type'} (f : type1143 _25376) (y : list _25376) : (term13 _25376 f y) = (f y).
Proof. exact (@lem1102523 (list _25376) Prop f y). Qed.
Lemma lem1102525 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term14 _25376 _17991 x) = (term12 _25376 _17991 x).
Proof. exact (@lem1102524 _25376 (term8 _25376 _17991 x) (@nil _25376)). Qed.
Lemma lem1102526 {_25376 : Type'} (_17991 : type1136 _25376) (_17990 : list _25376) (x : _25376) : (term15 _25376 _17991 x _17990) = (_17991 _17990 x).
Proof. exact (eq_refl (term15 _25376 _17991 x _17990)). Qed.
Lemma lem1102527 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term16 _25376 _17991 x) = (term8 _25376 _17991 x).
Proof. exact (fun_ext (fun _17990 : list _25376 => @lem1102526 _25376 _17991 _17990 x)). Qed.
Lemma lem1102528 {_25376 : Type'} : (@nil _25376) = (@nil _25376).
Proof. exact (eq_refl (@nil _25376)). Qed.
Lemma lem1102529 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term14 _25376 _17991 x) = (term12 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102527 _25376 _17991 x) (@lem1102528 _25376)). Qed.
Lemma lem1102530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1102531 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term17 _25376 _17991 x) = (term18 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102530) (@lem1102529 _25376 _17991 x)). Qed.
Lemma lem1102532 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term12 _25376 _17991 x) = (_17991 (@nil _25376) x).
Proof. exact (eq_refl (term12 _25376 _17991 x)). Qed.
Lemma lem1102533 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : ((term14 _25376 _17991 x) = (term12 _25376 _17991 x)) = ((term12 _25376 _17991 x) = (_17991 (@nil _25376) x)).
Proof. exact (MK_COMB (@lem1102531 _25376 _17991 x) (@lem1102532 _25376 _17991 x)). Qed.
Lemma lem1102534 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term12 _25376 _17991 x) = (_17991 (@nil _25376) x).
Proof. exact (EQ_MP (@lem1102533 _25376 _17991 x) (@lem1102525 _25376 _17991 x)). Qed.
Lemma lem1102535 {_25376 : Type'} (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (MEM' x (@nil _25376)) = (_17991 (@nil _25376) x).
Proof. exact (TRANS (@lem1102521 _25376 x MEM' _17991 h1) (@lem1102534 _25376 _17991 x)). Qed.
Lemma lem1102536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1102537 {_25376 : Type'} (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term19 _25376 MEM' x) = (term20 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102536) (@lem1102535 _25376 x MEM' _17991 h1)). Qed.
Lemma lem1102538 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1102539 {_25376 : Type'} (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : ((MEM' x (@nil _25376)) = False) = ((_17991 (@nil _25376) x) = False).
Proof. exact (MK_COMB (@lem1102537 _25376 x MEM' _17991 h1) (@lem1102538)). Qed.
Lemma lem1102540 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term21 _25376 MEM') = (term22 _25376 _17991).
Proof. exact (fun_ext (fun x : _25376 => @lem1102539 _25376 x MEM' _17991 h1)). Qed.
Lemma lem1102541 {_25376 : Type'} : (@all _25376) = (@all _25376).
Proof. exact (eq_refl (@all _25376)). Qed.
Lemma lem1102542 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term23 _25376 MEM') = (term24 _25376 _17991).
Proof. exact (MK_COMB (@lem1102541 _25376) (@lem1102540 _25376 MEM' _17991 h1)). Qed.
Lemma lem1102543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1102544 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term25 _25376 MEM') = (term26 _25376 _17991).
Proof. exact (MK_COMB (@lem1102543) (@lem1102542 _25376 MEM' _17991 h1)). Qed.
Lemma lem1102546 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : MEM' = (term4 _25376 _17991).
Proof. exact (h1). Qed.
Lemma lem1102547 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1102548 {_25376 : Type'} (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (MEM' x) = (term5 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102546 _25376 MEM' _17991 h1) (@lem1102547 _25376 x)). Qed.
Lemma lem1102550 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1102500 A B f y) (@lem1102499 A B f y)). Qed.
Lemma lem1102551 {_25376 : Type'} (f : type1398 _25376) (y : _25376) : (term6 _25376 f y) = (f y).
Proof. exact (@lem1102550 _25376 (type1143 _25376) f y). Qed.
Lemma lem1102552 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term7 _25376 _17991 x) = (term5 _25376 _17991 x).
Proof. exact (@lem1102551 _25376 (term4 _25376 _17991) x). Qed.
Lemma lem1102553 {_25376 : Type'} (_17991 : type1136 _25376) (_17989 : _25376) : (term5 _25376 _17991 _17989) = (term8 _25376 _17991 _17989).
Proof. exact (eq_refl (term5 _25376 _17991 _17989)). Qed.
Lemma lem1102554 {_25376 : Type'} (_17991 : type1136 _25376) : (term9 _25376 _17991) = (term4 _25376 _17991).
Proof. exact (fun_ext (fun _17989 : _25376 => @lem1102553 _25376 _17991 _17989)). Qed.
Lemma lem1102555 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1102556 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term7 _25376 _17991 x) = (term5 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102554 _25376 _17991) (@lem1102555 _25376 x)). Qed.
Lemma lem1102557 {_25376 : Type'} : (@eq ((list _25376) -> Prop)) = (@eq ((list _25376) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25376) -> Prop))). Qed.
Lemma lem1102558 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term10 _25376 _17991 x) = (term11 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102557 _25376) (@lem1102556 _25376 _17991 x)). Qed.
Lemma lem1102559 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term5 _25376 _17991 x) = (term8 _25376 _17991 x).
Proof. exact (eq_refl (term5 _25376 _17991 x)). Qed.
Lemma lem1102560 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : ((term7 _25376 _17991 x) = (term5 _25376 _17991 x)) = ((term5 _25376 _17991 x) = (term8 _25376 _17991 x)).
Proof. exact (MK_COMB (@lem1102558 _25376 _17991 x) (@lem1102559 _25376 _17991 x)). Qed.
Lemma lem1102561 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term5 _25376 _17991 x) = (term8 _25376 _17991 x).
Proof. exact (EQ_MP (@lem1102560 _25376 _17991 x) (@lem1102552 _25376 _17991 x)). Qed.
Lemma lem1102562 {_25376 : Type'} (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (MEM' x) = (term8 _25376 _17991 x).
Proof. exact (TRANS (@lem1102548 _25376 x MEM' _17991 h1) (@lem1102561 _25376 _17991 x)). Qed.
Lemma lem1102563 {_25376 : Type'} (h : _25376) (t : list _25376) : (@cons _25376 h t) = (@cons _25376 h t).
Proof. exact (eq_refl (@cons _25376 h t)). Qed.
Lemma lem1102564 {_25376 : Type'} (x : _25376) (h : _25376) (t : list _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term27 _25376 MEM' x h t) = (term28 _25376 _17991 x h t).
Proof. exact (MK_COMB (@lem1102562 _25376 x MEM' _17991 h1) (@lem1102563 _25376 h t)). Qed.
Lemma lem1102566 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1102500 A B f y) (@lem1102499 A B f y)). Qed.
Lemma lem1102567 {_25376 : Type'} (f : type1143 _25376) (y : list _25376) : (term13 _25376 f y) = (f y).
Proof. exact (@lem1102566 (list _25376) Prop f y). Qed.
Lemma lem1102568 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) (h : _25376) (t : list _25376) : (term29 _25376 _17991 x h t) = (term28 _25376 _17991 x h t).
Proof. exact (@lem1102567 _25376 (term8 _25376 _17991 x) (@cons _25376 h t)). Qed.
Lemma lem1102569 {_25376 : Type'} (_17991 : type1136 _25376) (_17990 : list _25376) (x : _25376) : (term15 _25376 _17991 x _17990) = (_17991 _17990 x).
Proof. exact (eq_refl (term15 _25376 _17991 x _17990)). Qed.
Lemma lem1102570 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term16 _25376 _17991 x) = (term8 _25376 _17991 x).
Proof. exact (fun_ext (fun _17990 : list _25376 => @lem1102569 _25376 _17991 _17990 x)). Qed.
Lemma lem1102571 {_25376 : Type'} (h : _25376) (t : list _25376) : (@cons _25376 h t) = (@cons _25376 h t).
Proof. exact (eq_refl (@cons _25376 h t)). Qed.
Lemma lem1102572 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) (h : _25376) (t : list _25376) : (term29 _25376 _17991 x h t) = (term28 _25376 _17991 x h t).
Proof. exact (MK_COMB (@lem1102570 _25376 _17991 x) (@lem1102571 _25376 h t)). Qed.
Lemma lem1102573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1102574 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) (h : _25376) (t : list _25376) : (term30 _25376 _17991 x h t) = (term31 _25376 _17991 x h t).
Proof. exact (MK_COMB (@lem1102573) (@lem1102572 _25376 _17991 x h t)). Qed.
Lemma lem1102575 {_25376 : Type'} (_17991 : type1136 _25376) (h : _25376) (t : list _25376) (x : _25376) : (term28 _25376 _17991 x h t) = (term32 _25376 _17991 h t x).
Proof. exact (eq_refl (term28 _25376 _17991 x h t)). Qed.
Lemma lem1102576 {_25376 : Type'} (_17991 : type1136 _25376) (h : _25376) (t : list _25376) (x : _25376) : ((term29 _25376 _17991 x h t) = (term28 _25376 _17991 x h t)) = ((term28 _25376 _17991 x h t) = (term32 _25376 _17991 h t x)).
Proof. exact (MK_COMB (@lem1102574 _25376 _17991 x h t) (@lem1102575 _25376 _17991 h t x)). Qed.
Lemma lem1102577 {_25376 : Type'} (_17991 : type1136 _25376) (h : _25376) (t : list _25376) (x : _25376) : (term28 _25376 _17991 x h t) = (term32 _25376 _17991 h t x).
Proof. exact (EQ_MP (@lem1102576 _25376 _17991 h t x) (@lem1102568 _25376 _17991 x h t)). Qed.
Lemma lem1102578 {_25376 : Type'} (h : _25376) (t : list _25376) (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term27 _25376 MEM' x h t) = (term32 _25376 _17991 h t x).
Proof. exact (TRANS (@lem1102564 _25376 x h t MEM' _17991 h1) (@lem1102577 _25376 _17991 h t x)). Qed.
Lemma lem1102579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1102580 {_25376 : Type'} (h : _25376) (t : list _25376) (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term33 _25376 MEM' x h t) = (term34 _25376 _17991 h t x).
Proof. exact (MK_COMB (@lem1102579) (@lem1102578 _25376 h t x MEM' _17991 h1)). Qed.
Lemma lem1102582 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : MEM' = (term4 _25376 _17991).
Proof. exact (h1). Qed.
Lemma lem1102583 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1102584 {_25376 : Type'} (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (MEM' x) = (term5 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102582 _25376 MEM' _17991 h1) (@lem1102583 _25376 x)). Qed.
Lemma lem1102586 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1102500 A B f y) (@lem1102499 A B f y)). Qed.
Lemma lem1102587 {_25376 : Type'} (f : type1398 _25376) (y : _25376) : (term6 _25376 f y) = (f y).
Proof. exact (@lem1102586 _25376 (type1143 _25376) f y). Qed.
Lemma lem1102588 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term7 _25376 _17991 x) = (term5 _25376 _17991 x).
Proof. exact (@lem1102587 _25376 (term4 _25376 _17991) x). Qed.
Lemma lem1102589 {_25376 : Type'} (_17991 : type1136 _25376) (_17989 : _25376) : (term5 _25376 _17991 _17989) = (term8 _25376 _17991 _17989).
Proof. exact (eq_refl (term5 _25376 _17991 _17989)). Qed.
Lemma lem1102590 {_25376 : Type'} (_17991 : type1136 _25376) : (term9 _25376 _17991) = (term4 _25376 _17991).
Proof. exact (fun_ext (fun _17989 : _25376 => @lem1102589 _25376 _17991 _17989)). Qed.
Lemma lem1102591 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1102592 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term7 _25376 _17991 x) = (term5 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102590 _25376 _17991) (@lem1102591 _25376 x)). Qed.
Lemma lem1102593 {_25376 : Type'} : (@eq ((list _25376) -> Prop)) = (@eq ((list _25376) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25376) -> Prop))). Qed.
Lemma lem1102594 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term10 _25376 _17991 x) = (term11 _25376 _17991 x).
Proof. exact (MK_COMB (@lem1102593 _25376) (@lem1102592 _25376 _17991 x)). Qed.
Lemma lem1102595 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term5 _25376 _17991 x) = (term8 _25376 _17991 x).
Proof. exact (eq_refl (term5 _25376 _17991 x)). Qed.
Lemma lem1102596 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : ((term7 _25376 _17991 x) = (term5 _25376 _17991 x)) = ((term5 _25376 _17991 x) = (term8 _25376 _17991 x)).
Proof. exact (MK_COMB (@lem1102594 _25376 _17991 x) (@lem1102595 _25376 _17991 x)). Qed.
Lemma lem1102597 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term5 _25376 _17991 x) = (term8 _25376 _17991 x).
Proof. exact (EQ_MP (@lem1102596 _25376 _17991 x) (@lem1102588 _25376 _17991 x)). Qed.
Lemma lem1102598 {_25376 : Type'} (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (MEM' x) = (term8 _25376 _17991 x).
Proof. exact (TRANS (@lem1102584 _25376 x MEM' _17991 h1) (@lem1102597 _25376 _17991 x)). Qed.
Lemma lem1102599 {_25376 : Type'} (t : list _25376) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1102600 {_25376 : Type'} (x : _25376) (t : list _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (MEM' x t) = (term15 _25376 _17991 x t).
Proof. exact (MK_COMB (@lem1102598 _25376 x MEM' _17991 h1) (@lem1102599 _25376 t)). Qed.
Lemma lem1102602 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1102500 A B f y) (@lem1102499 A B f y)). Qed.
Lemma lem1102603 {_25376 : Type'} (f : type1143 _25376) (y : list _25376) : (term13 _25376 f y) = (f y).
Proof. exact (@lem1102602 (list _25376) Prop f y). Qed.
Lemma lem1102604 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) (t : list _25376) : (term35 _25376 _17991 x t) = (term15 _25376 _17991 x t).
Proof. exact (@lem1102603 _25376 (term8 _25376 _17991 x) t). Qed.
Lemma lem1102605 {_25376 : Type'} (_17991 : type1136 _25376) (_17990 : list _25376) (x : _25376) : (term15 _25376 _17991 x _17990) = (_17991 _17990 x).
Proof. exact (eq_refl (term15 _25376 _17991 x _17990)). Qed.
Lemma lem1102606 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term16 _25376 _17991 x) = (term8 _25376 _17991 x).
Proof. exact (fun_ext (fun _17990 : list _25376 => @lem1102605 _25376 _17991 _17990 x)). Qed.
Lemma lem1102607 {_25376 : Type'} (t : list _25376) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1102608 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) (t : list _25376) : (term35 _25376 _17991 x t) = (term15 _25376 _17991 x t).
Proof. exact (MK_COMB (@lem1102606 _25376 _17991 x) (@lem1102607 _25376 t)). Qed.
Lemma lem1102609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1102610 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) (t : list _25376) : (term36 _25376 _17991 x t) = (term37 _25376 _17991 x t).
Proof. exact (MK_COMB (@lem1102609) (@lem1102608 _25376 _17991 x t)). Qed.
Lemma lem1102611 {_25376 : Type'} (_17991 : type1136 _25376) (t : list _25376) (x : _25376) : (term15 _25376 _17991 x t) = (_17991 t x).
Proof. exact (eq_refl (term15 _25376 _17991 x t)). Qed.
Lemma lem1102612 {_25376 : Type'} (_17991 : type1136 _25376) (t : list _25376) (x : _25376) : ((term35 _25376 _17991 x t) = (term15 _25376 _17991 x t)) = ((term15 _25376 _17991 x t) = (_17991 t x)).
Proof. exact (MK_COMB (@lem1102610 _25376 _17991 x t) (@lem1102611 _25376 _17991 t x)). Qed.
Lemma lem1102613 {_25376 : Type'} (_17991 : type1136 _25376) (t : list _25376) (x : _25376) : (term15 _25376 _17991 x t) = (_17991 t x).
Proof. exact (EQ_MP (@lem1102612 _25376 _17991 t x) (@lem1102604 _25376 _17991 x t)). Qed.
Lemma lem1102614 {_25376 : Type'} (t : list _25376) (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (MEM' x t) = (_17991 t x).
Proof. exact (TRANS (@lem1102600 _25376 x t MEM' _17991 h1) (@lem1102613 _25376 _17991 t x)). Qed.
Lemma lem1102615 {_25376 : Type'} (x : _25376) (h : _25376) : (term38 _25376 x h) = (term38 _25376 x h).
Proof. exact (eq_refl (term38 _25376 x h)). Qed.
Lemma lem1102616 {_25376 : Type'} (h : _25376) (t : list _25376) (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term39 _25376 h MEM' x t) = (term40 _25376 h _17991 t x).
Proof. exact (MK_COMB (@lem1102615 _25376 x h) (@lem1102614 _25376 t x MEM' _17991 h1)). Qed.
Lemma lem1102617 {_25376 : Type'} (h : _25376) (t : list _25376) (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : ((term27 _25376 MEM' x h t) = (term39 _25376 h MEM' x t)) = ((term32 _25376 _17991 h t x) = (term40 _25376 h _17991 t x)).
Proof. exact (MK_COMB (@lem1102580 _25376 h t x MEM' _17991 h1) (@lem1102616 _25376 h t x MEM' _17991 h1)). Qed.
Lemma lem1102618 {_25376 : Type'} (h : _25376) (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term41 _25376 h MEM' x) = (term42 _25376 h _17991 x).
Proof. exact (fun_ext (fun t : list _25376 => @lem1102617 _25376 h t x MEM' _17991 h1)). Qed.
Lemma lem1102619 {_25376 : Type'} : (@all (list _25376)) = (@all (list _25376)).
Proof. exact (eq_refl (@all (list _25376))). Qed.
Lemma lem1102620 {_25376 : Type'} (h : _25376) (x : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term43 _25376 h MEM' x) = (term44 _25376 h _17991 x).
Proof. exact (MK_COMB (@lem1102619 _25376) (@lem1102618 _25376 h x MEM' _17991 h1)). Qed.
Lemma lem1102621 {_25376 : Type'} (h : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term45 _25376 h MEM') = (term46 _25376 h _17991).
Proof. exact (fun_ext (fun x : _25376 => @lem1102620 _25376 h x MEM' _17991 h1)). Qed.
Lemma lem1102622 {_25376 : Type'} : (@all _25376) = (@all _25376).
Proof. exact (eq_refl (@all _25376)). Qed.
Lemma lem1102623 {_25376 : Type'} (h : _25376) (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term47 _25376 h MEM') = (term48 _25376 h _17991).
Proof. exact (MK_COMB (@lem1102622 _25376) (@lem1102621 _25376 h MEM' _17991 h1)). Qed.
Lemma lem1102624 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term49 _25376 MEM') = (term50 _25376 _17991).
Proof. exact (fun_ext (fun h : _25376 => @lem1102623 _25376 h MEM' _17991 h1)). Qed.
Lemma lem1102625 {_25376 : Type'} : (@all _25376) = (@all _25376).
Proof. exact (eq_refl (@all _25376)). Qed.
Lemma lem1102626 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term51 _25376 MEM') = (term52 _25376 _17991).
Proof. exact (MK_COMB (@lem1102625 _25376) (@lem1102624 _25376 MEM' _17991 h1)). Qed.
Lemma lem1102627 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term53 _25376 MEM') = (term54 _25376 _17991).
Proof. exact (MK_COMB (@lem1102544 _25376 MEM' _17991 h1) (@lem1102626 _25376 MEM' _17991 h1)). Qed.
Lemma lem1102628 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : (_17991 (@nil _25376)) = (term55 _25376)) : (_17991 (@nil _25376)) = (term55 _25376).
Proof. exact (h1). Qed.
Lemma lem1102629 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1102630 {_25376 : Type'} (x : _25376) (_17991 : type1136 _25376) (h1 : (_17991 (@nil _25376)) = (term55 _25376)) : (_17991 (@nil _25376) x) = (term56 _25376 x).
Proof. exact (MK_COMB (@lem1102628 _25376 _17991 h1) (@lem1102629 _25376 x)). Qed.
Lemma lem1102631 {_25376 : Type'} (x : _25376) : (term56 _25376 x) = False.
Proof. exact (eq_refl (term56 _25376 x)). Qed.
Lemma lem1102632 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : (term20 _25376 _17991 x) = (term20 _25376 _17991 x).
Proof. exact (eq_refl (term20 _25376 _17991 x)). Qed.
Lemma lem1102633 {_25376 : Type'} (_17991 : type1136 _25376) (x : _25376) : ((_17991 (@nil _25376) x) = (term56 _25376 x)) = ((_17991 (@nil _25376) x) = False).
Proof. exact (MK_COMB (@lem1102632 _25376 _17991 x) (@lem1102631 _25376 x)). Qed.
Lemma lem1102634 {_25376 : Type'} (x : _25376) (_17991 : type1136 _25376) (h1 : (_17991 (@nil _25376)) = (term55 _25376)) : (_17991 (@nil _25376) x) = False.
Proof. exact (EQ_MP (@lem1102633 _25376 _17991 x) (@lem1102630 _25376 x _17991 h1)). Qed.
Lemma lem1102635 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : (_17991 (@nil _25376)) = (term55 _25376)) : term24 _25376 _17991.
Proof. exact (fun x : _25376 => @lem1102634 _25376 x _17991 h1). Qed.
Lemma lem1102636 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term57 _25376 _17991) : term57 _25376 _17991.
Proof. exact (h1). Qed.
Lemma lem1102637 {_25376 : Type'} (h : _25376) (_17991 : type1136 _25376) (h1 : term57 _25376 _17991) : term58 _25376 _17991 h.
Proof. exact (@lem1102636 _25376 _17991 h1 h). Qed.
Lemma lem1102638 {_25376 : Type'} (h : _25376) (_17991 : type1136 _25376) : (term58 _25376 _17991 h) = (term59 _25376 h _17991).
Proof. exact (eq_refl (term58 _25376 _17991 h)). Qed.
Lemma lem1102639 {_25376 : Type'} (h : _25376) (_17991 : type1136 _25376) (h1 : term57 _25376 _17991) : term59 _25376 h _17991.
Proof. exact (EQ_MP (@lem1102638 _25376 h _17991) (@lem1102637 _25376 h _17991 h1)). Qed.
Lemma lem1102640 {_25376 : Type'} (h : _25376) (t : list _25376) (_17991 : type1136 _25376) (h1 : term57 _25376 _17991) : term60 _25376 h _17991 t.
Proof. exact (@lem1102639 _25376 h _17991 h1 t). Qed.
Lemma lem1102641 {_25376 : Type'} (h : _25376) (_17991 : type1136 _25376) (t : list _25376) : (term60 _25376 h _17991 t) = ((term61 _25376 _17991 h t) = (term62 _25376 h _17991 t)).
Proof. exact (eq_refl (term60 _25376 h _17991 t)). Qed.
Lemma lem1102642 {_25376 : Type'} (h : _25376) (t : list _25376) (_17991 : type1136 _25376) (h1 : term57 _25376 _17991) : (term61 _25376 _17991 h t) = (term62 _25376 h _17991 t).
Proof. exact (EQ_MP (@lem1102641 _25376 h _17991 t) (@lem1102640 _25376 h t _17991 h1)). Qed.
Lemma lem1102643 {_25376 : Type'} (x : _25376) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1102644 {_25376 : Type'} (h : _25376) (t : list _25376) (x : _25376) (_17991 : type1136 _25376) (h1 : term57 _25376 _17991) : (term32 _25376 _17991 h t x) = (term63 _25376 h _17991 t x).
Proof. exact (MK_COMB (@lem1102642 _25376 h t _17991 h1) (@lem1102643 _25376 x)). Qed.
Lemma lem1102645 {_25376 : Type'} (h : _25376) (_17991 : type1136 _25376) (t : list _25376) (x : _25376) : (term63 _25376 h _17991 t x) = (term40 _25376 h _17991 t x).
Proof. exact (eq_refl (term63 _25376 h _17991 t x)). Qed.
Lemma lem1102646 {_25376 : Type'} (_17991 : type1136 _25376) (h : _25376) (t : list _25376) (x : _25376) : (term34 _25376 _17991 h t x) = (term34 _25376 _17991 h t x).
Proof. exact (eq_refl (term34 _25376 _17991 h t x)). Qed.
Lemma lem1102647 {_25376 : Type'} (h : _25376) (_17991 : type1136 _25376) (t : list _25376) (x : _25376) : ((term32 _25376 _17991 h t x) = (term63 _25376 h _17991 t x)) = ((term32 _25376 _17991 h t x) = (term40 _25376 h _17991 t x)).
Proof. exact (MK_COMB (@lem1102646 _25376 _17991 h t x) (@lem1102645 _25376 h _17991 t x)). Qed.
Lemma lem1102648 {_25376 : Type'} (h : _25376) (t : list _25376) (x : _25376) (_17991 : type1136 _25376) (h1 : term57 _25376 _17991) : (term32 _25376 _17991 h t x) = (term40 _25376 h _17991 t x).
Proof. exact (EQ_MP (@lem1102647 _25376 h _17991 t x) (@lem1102644 _25376 h t x _17991 h1)). Qed.
Lemma lem1102649 {_25376 : Type'} (h : _25376) (x : _25376) (_17991 : type1136 _25376) (h1 : term57 _25376 _17991) : term44 _25376 h _17991 x.
Proof. exact (fun t : list _25376 => @lem1102648 _25376 h t x _17991 h1). Qed.
Lemma lem1102650 {_25376 : Type'} (h : _25376) (_17991 : type1136 _25376) (h1 : term57 _25376 _17991) : term48 _25376 h _17991.
Proof. exact (fun x : _25376 => @lem1102649 _25376 h x _17991 h1). Qed.
Lemma lem1102651 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term57 _25376 _17991) : term52 _25376 _17991.
Proof. exact (fun h : _25376 => @lem1102650 _25376 h _17991 h1). Qed.
Lemma lem1102652 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : term64 _25376 _17991.
Proof. exact (h1). Qed.
Lemma lem1102653 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : term57 _25376 _17991.
Proof. exact (proj2 (@lem1102652 _25376 _17991 h1)). Qed.
Lemma lem1102654 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : (_17991 (@nil _25376)) = (term55 _25376).
Proof. exact (proj1 (@lem1102652 _25376 _17991 h1)). Qed.
Lemma lem1102655 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : ((_17991 (@nil _25376)) = (term55 _25376)) = (term24 _25376 _17991).
Proof. exact (prop_ext (fun h2 : (_17991 (@nil _25376)) = (term55 _25376) => @lem1102635 _25376 _17991 h2) (fun h2 : term24 _25376 _17991 => @lem1102654 _25376 _17991 h1)). Qed.
Lemma lem1102656 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : term24 _25376 _17991.
Proof. exact (EQ_MP (@lem1102655 _25376 _17991 h1) (@lem1102654 _25376 _17991 h1)). Qed.
Lemma lem1102657 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : (term57 _25376 _17991) = (term52 _25376 _17991).
Proof. exact (prop_ext (fun h2 : term57 _25376 _17991 => @lem1102651 _25376 _17991 h2) (fun h2 : term52 _25376 _17991 => @lem1102653 _25376 _17991 h1)). Qed.
Lemma lem1102658 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : term52 _25376 _17991.
Proof. exact (EQ_MP (@lem1102657 _25376 _17991 h1) (@lem1102653 _25376 _17991 h1)). Qed.
Lemma lem1102659 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : term54 _25376 _17991.
Proof. exact (conj (@lem1102656 _25376 _17991 h1) (@lem1102658 _25376 _17991 h1)). Qed.
Lemma lem1102660 {A Z : Type'} (NIL' : Z) : term65 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1102661 {A Z : Type'} (NIL' : Z) : (term65 A Z NIL') = (term66 A Z NIL').
Proof. exact (eq_refl (term65 A Z NIL')). Qed.
Lemma lem1102662 {A Z : Type'} (NIL' : Z) : term66 A Z NIL'.
Proof. exact (EQ_MP (@lem1102661 A Z NIL') (@lem1102660 A Z NIL')). Qed.
Lemma lem1102663 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term67 A Z NIL' CONS'.
Proof. exact (@lem1102662 A Z NIL' CONS'). Qed.
Lemma lem1102664 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term67 A Z NIL' CONS') = (term68 A Z NIL' CONS').
Proof. exact (eq_refl (term67 A Z NIL' CONS')). Qed.
Lemma lem1102665 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term68 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1102664 A Z NIL' CONS') (@lem1102663 A Z NIL' CONS')). Qed.
Lemma lem1102666 {_25376 : Type'} (NIL' : _25376 -> Prop) (CONS' : type1390 _25376) : term69 _25376 NIL' CONS'.
Proof. exact (@lem1102665 _25376 (_25376 -> Prop) NIL' CONS'). Qed.
Lemma lem1102667 {_25376 : Type'} : term70 _25376.
Proof. exact (@lem1102666 _25376 (term55 _25376) (term71 _25376)). Qed.
Lemma lem1102668 {_25376 : Type'} (a0 : _25376) : (term72 _25376 a0) = (term73 _25376 a0).
Proof. exact (eq_refl (term72 _25376 a0)). Qed.
Lemma lem1102669 {_25376 : Type'} (a1 : list _25376) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1102670 {_25376 : Type'} (a0 : _25376) (a1 : list _25376) : (term74 _25376 a0 a1) = (term75 _25376 a0 a1).
Proof. exact (MK_COMB (@lem1102668 _25376 a0) (@lem1102669 _25376 a1)). Qed.
Lemma lem1102671 {_25376 : Type'} (a1 : list _25376) (a0 : _25376) : (term75 _25376 a0 a1) = (term76 _25376 a0).
Proof. exact (eq_refl (term75 _25376 a0 a1)). Qed.
Lemma lem1102672 {_25376 : Type'} (a1 : list _25376) (a0 : _25376) : (term74 _25376 a0 a1) = (term76 _25376 a0).
Proof. exact (TRANS (@lem1102670 _25376 a0 a1) (@lem1102671 _25376 a1 a0)). Qed.
Lemma lem1102673 {_25376 : Type'} (fn : type1136 _25376) (a1 : list _25376) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1102674 {_25376 : Type'} (a0 : _25376) (fn : type1136 _25376) (a1 : list _25376) : (term77 _25376 a0 fn a1) = (term78 _25376 a0 fn a1).
Proof. exact (MK_COMB (@lem1102672 _25376 a1 a0) (@lem1102673 _25376 fn a1)). Qed.
Lemma lem1102675 {_25376 : Type'} (a0 : _25376) (fn : type1136 _25376) (a1 : list _25376) : (term78 _25376 a0 fn a1) = (term62 _25376 a0 fn a1).
Proof. exact (eq_refl (term78 _25376 a0 fn a1)). Qed.
Lemma lem1102676 {_25376 : Type'} (a0 : _25376) (fn : type1136 _25376) (a1 : list _25376) : (term77 _25376 a0 fn a1) = (term62 _25376 a0 fn a1).
Proof. exact (TRANS (@lem1102674 _25376 a0 fn a1) (@lem1102675 _25376 a0 fn a1)). Qed.
Lemma lem1102677 {_25376 : Type'} (fn : type1136 _25376) (a0 : _25376) (a1 : list _25376) : (term79 _25376 fn a0 a1) = (term79 _25376 fn a0 a1).
Proof. exact (eq_refl (term79 _25376 fn a0 a1)). Qed.
Lemma lem1102678 {_25376 : Type'} (a0 : _25376) (fn : type1136 _25376) (a1 : list _25376) : ((term61 _25376 fn a0 a1) = (term77 _25376 a0 fn a1)) = ((term61 _25376 fn a0 a1) = (term62 _25376 a0 fn a1)).
Proof. exact (MK_COMB (@lem1102677 _25376 fn a0 a1) (@lem1102676 _25376 a0 fn a1)). Qed.
Lemma lem1102679 {_25376 : Type'} (a0 : _25376) (fn : type1136 _25376) : (term80 _25376 a0 fn) = (term81 _25376 a0 fn).
Proof. exact (fun_ext (fun a1 : list _25376 => @lem1102678 _25376 a0 fn a1)). Qed.
Lemma lem1102680 {_25376 : Type'} : (@all (list _25376)) = (@all (list _25376)).
Proof. exact (eq_refl (@all (list _25376))). Qed.
Lemma lem1102681 {_25376 : Type'} (a0 : _25376) (fn : type1136 _25376) : (term82 _25376 a0 fn) = (term59 _25376 a0 fn).
Proof. exact (MK_COMB (@lem1102680 _25376) (@lem1102679 _25376 a0 fn)). Qed.
Lemma lem1102682 {_25376 : Type'} (fn : type1136 _25376) : (term83 _25376 fn) = (term84 _25376 fn).
Proof. exact (fun_ext (fun a0 : _25376 => @lem1102681 _25376 a0 fn)). Qed.
Lemma lem1102683 {_25376 : Type'} : (@all _25376) = (@all _25376).
Proof. exact (eq_refl (@all _25376)). Qed.
Lemma lem1102684 {_25376 : Type'} (fn : type1136 _25376) : (term85 _25376 fn) = (term57 _25376 fn).
Proof. exact (MK_COMB (@lem1102683 _25376) (@lem1102682 _25376 fn)). Qed.
Lemma lem1102685 {_25376 : Type'} (fn : type1136 _25376) : (term86 _25376 fn) = (term86 _25376 fn).
Proof. exact (eq_refl (term86 _25376 fn)). Qed.
Lemma lem1102686 {_25376 : Type'} (fn : type1136 _25376) : (term87 _25376 fn) = (term64 _25376 fn).
Proof. exact (MK_COMB (@lem1102685 _25376 fn) (@lem1102684 _25376 fn)). Qed.
Lemma lem1102687 {_25376 : Type'} : (term88 _25376) = (term89 _25376).
Proof. exact (fun_ext (fun fn : type1136 _25376 => @lem1102686 _25376 fn)). Qed.
Lemma lem1102688 {_25376 : Type'} : (@ex ((list _25376) -> _25376 -> Prop)) = (@ex ((list _25376) -> _25376 -> Prop)).
Proof. exact (eq_refl (@ex ((list _25376) -> _25376 -> Prop))). Qed.
Lemma lem1102689 {_25376 : Type'} : (term70 _25376) = (term90 _25376).
Proof. exact (MK_COMB (@lem1102688 _25376) (@lem1102687 _25376)). Qed.
Lemma lem1102690 {_25376 : Type'} : term90 _25376.
Proof. exact (EQ_MP (@lem1102689 _25376) (@lem1102667 _25376)). Qed.
Lemma lem1102691 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : term64 _25376 _17991.
Proof. exact (h1). Qed.
Lemma lem1102692 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : term57 _25376 _17991.
Proof. exact (proj2 (@lem1102691 _25376 _17991 h1)). Qed.
Lemma lem1102693 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : (_17991 (@nil _25376)) = (term55 _25376).
Proof. exact (proj1 (@lem1102691 _25376 _17991 h1)). Qed.
Lemma lem1102694 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : term64 _25376 _17991.
Proof. exact (conj (@lem1102693 _25376 _17991 h1) (@lem1102692 _25376 _17991 h1)). Qed.
Lemma lem1102695 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : term90 _25376.
Proof. exact (ex_intro (term89 _25376) _17991 (@lem1102694 _25376 _17991 h1)). Qed.
Lemma lem1102696 {_25376 : Type'} (h1 : term90 _25376) : term90 _25376.
Proof. exact (h1). Qed.
Lemma lem1102697 {_25376 : Type'} (h1 : term90 _25376) : term90 _25376.
Proof. exact (ex_elim (@lem1102696 _25376 h1) (fun _17991 : type1136 _25376 => fun h0 : term89 _25376 _17991 => @lem1102695 _25376 _17991 h0)). Qed.
Lemma lem1102698 {_25376 : Type'} : (term90 _25376) = (term90 _25376).
Proof. exact (prop_ext (fun h1 : term90 _25376 => @lem1102697 _25376 h1) (fun h1 : term90 _25376 => @lem1102690 _25376)). Qed.
Lemma lem1102699 {_25376 : Type'} : term90 _25376.
Proof. exact (EQ_MP (@lem1102698 _25376) (@lem1102690 _25376)). Qed.
Lemma lem1102700 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term64 _25376 _17991) : term91 _25376.
Proof. exact (ex_intro (term92 _25376) _17991 (@lem1102659 _25376 _17991 h1)). Qed.
Lemma lem1102701 {_25376 : Type'} (h1 : term90 _25376) : term90 _25376.
Proof. exact (h1). Qed.
Lemma lem1102702 {_25376 : Type'} (h1 : term90 _25376) : term91 _25376.
Proof. exact (ex_elim (@lem1102701 _25376 h1) (fun _17991 : type1136 _25376 => fun h0 : term89 _25376 _17991 => @lem1102700 _25376 _17991 h0)). Qed.
Lemma lem1102703 {_25376 : Type'} : (term90 _25376) = (term91 _25376).
Proof. exact (prop_ext (fun h1 : term90 _25376 => @lem1102702 _25376 h1) (fun h1 : term91 _25376 => @lem1102699 _25376)). Qed.
Lemma lem1102704 {_25376 : Type'} : term91 _25376.
Proof. exact (EQ_MP (@lem1102703 _25376) (@lem1102699 _25376)). Qed.
Lemma lem1102705 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term54 _25376 _17991) : term54 _25376 _17991.
Proof. exact (h1). Qed.
Lemma lem1102706 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : MEM' = (term4 _25376 _17991)) : (term54 _25376 _17991) = (term53 _25376 MEM').
Proof. exact (SYM (@lem1102627 _25376 MEM' _17991 h1)). Qed.
Lemma lem1102707 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : term54 _25376 _17991) (h2 : MEM' = (term4 _25376 _17991)) : term53 _25376 MEM'.
Proof. exact (EQ_MP (@lem1102706 _25376 MEM' _17991 h2) (@lem1102705 _25376 _17991 h1)). Qed.
Lemma lem1102708 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : term54 _25376 _17991) (h2 : MEM' = (term4 _25376 _17991)) : term93 _25376.
Proof. exact (ex_intro (term94 _25376) MEM' (@lem1102707 _25376 MEM' _17991 h1 h2)). Qed.
Lemma lem1102709 {_25376 : Type'} (_17991 : type1136 _25376) : (term4 _25376 _17991) = (term4 _25376 _17991).
Proof. exact (eq_refl (term4 _25376 _17991)). Qed.
Lemma lem1102710 {_25376 : Type'} (MEM' : type1398 _25376) (_17991 : type1136 _25376) (h1 : term54 _25376 _17991) : term95 _25376 MEM' _17991.
Proof. exact (fun h0 : MEM' = (term4 _25376 _17991) => @lem1102708 _25376 MEM' _17991 h1 h0). Qed.
Lemma lem1102711 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term54 _25376 _17991) : term96 _25376 _17991.
Proof. exact (@lem1102710 _25376 (term4 _25376 _17991) _17991 h1). Qed.
Lemma lem1102712 {_25376 : Type'} (_17991 : type1136 _25376) (h1 : term54 _25376 _17991) : term93 _25376.
Proof. exact (@lem1102711 _25376 _17991 h1 (@lem1102709 _25376 _17991)). Qed.
Lemma lem1102713 {_25376 : Type'} (h1 : term91 _25376) : term91 _25376.
Proof. exact (h1). Qed.
Lemma lem1102714 {_25376 : Type'} (h1 : term91 _25376) : term93 _25376.
Proof. exact (ex_elim (@lem1102713 _25376 h1) (fun _17991 : type1136 _25376 => fun h0 : term92 _25376 _17991 => @lem1102712 _25376 _17991 h0)). Qed.
Lemma lem1102715 {_25376 : Type'} : (term91 _25376) = (term93 _25376).
Proof. exact (prop_ext (fun h1 : term91 _25376 => @lem1102714 _25376 h1) (fun h1 : term93 _25376 => @lem1102704 _25376)). Qed.
Lemma lem1102716 {_25376 : Type'} : term93 _25376.
Proof. exact (EQ_MP (@lem1102715 _25376) (@lem1102704 _25376)). Qed.
Lemma lem1102717 {_25376 : Type'} : term97 _25376.
Proof. exact (fun _17995 : type1674 => @lem1102716 _25376). Qed.
Lemma lem1102718 {A B : Type'} (P : type1413 A B) : term98 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1102719 {A B : Type'} (P : type1413 A B) : (term98 A B P) = ((term99 A B P) = (term100 A B P)).
Proof. exact (eq_refl (term98 A B P)). Qed.
Lemma lem1102722 {A B : Type'} (P : type1413 A B) : (term99 A B P) = (term100 A B P).
Proof. exact (EQ_MP (@lem1102719 A B P) (@lem1102718 A B P)). Qed.
Lemma lem1102723 {_25376 : Type'} (P : type1296 _25376) : (term101 _25376 P) = (term102 _25376 P).
Proof. exact (@lem1102722 type1674 (type1398 _25376) P). Qed.
Lemma lem1102724 {_25376 : Type'} : (term103 _25376) = (term104 _25376).
Proof. exact (@lem1102723 _25376 (term105 _25376)). Qed.
Lemma lem1102725 {_25376 : Type'} (_17995 : type1674) : (term106 _25376 _17995) = (term94 _25376).
Proof. exact (eq_refl (term106 _25376 _17995)). Qed.
Lemma lem1102726 {_25376 : Type'} (MEM' : type1398 _25376) : MEM' = MEM'.
Proof. exact (eq_refl MEM'). Qed.
Lemma lem1102727 {_25376 : Type'} (_17995 : type1674) (MEM' : type1398 _25376) : (term107 _25376 _17995 MEM') = (term108 _25376 MEM').
Proof. exact (MK_COMB (@lem1102725 _25376 _17995) (@lem1102726 _25376 MEM')). Qed.
Lemma lem1102728 {_25376 : Type'} (MEM' : type1398 _25376) : (term108 _25376 MEM') = (term53 _25376 MEM').
Proof. exact (eq_refl (term108 _25376 MEM')). Qed.
Lemma lem1102729 {_25376 : Type'} (_17995 : type1674) (MEM' : type1398 _25376) : (term107 _25376 _17995 MEM') = (term53 _25376 MEM').
Proof. exact (TRANS (@lem1102727 _25376 _17995 MEM') (@lem1102728 _25376 MEM')). Qed.
Lemma lem1102730 {_25376 : Type'} (_17995 : type1674) : (term109 _25376 _17995) = (term94 _25376).
Proof. exact (fun_ext (fun MEM' : type1398 _25376 => @lem1102729 _25376 _17995 MEM')). Qed.
Lemma lem1102731 {_25376 : Type'} : (@ex (_25376 -> (list _25376) -> Prop)) = (@ex (_25376 -> (list _25376) -> Prop)).
Proof. exact (eq_refl (@ex (_25376 -> (list _25376) -> Prop))). Qed.
Lemma lem1102732 {_25376 : Type'} (_17995 : type1674) : (term110 _25376 _17995) = (term93 _25376).
Proof. exact (MK_COMB (@lem1102731 _25376) (@lem1102730 _25376 _17995)). Qed.
Lemma lem1102733 {_25376 : Type'} : (term111 _25376) = (term112 _25376).
Proof. exact (fun_ext (fun _17995 : type1674 => @lem1102732 _25376 _17995)). Qed.
Lemma lem1102734 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem1102735 {_25376 : Type'} : (term103 _25376) = (term97 _25376).
Proof. exact (MK_COMB (@lem1102734) (@lem1102733 _25376)). Qed.
Lemma lem1102736 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1102737 {_25376 : Type'} : (term113 _25376) = (term114 _25376).
Proof. exact (MK_COMB (@lem1102736) (@lem1102735 _25376)). Qed.
Lemma lem1102738 {_25376 : Type'} (_17995 : type1674) : (term106 _25376 _17995) = (term94 _25376).
Proof. exact (eq_refl (term106 _25376 _17995)). Qed.
Lemma lem1102739 {_25376 : Type'} (MEM' : type1304 _25376) (_17995 : type1674) : (MEM' _17995) = (MEM' _17995).
Proof. exact (eq_refl (MEM' _17995)). Qed.
Lemma lem1102740 {_25376 : Type'} (MEM' : type1304 _25376) (_17995 : type1674) : (term115 _25376 MEM' _17995) = (term116 _25376 MEM' _17995).
Proof. exact (MK_COMB (@lem1102738 _25376 _17995) (@lem1102739 _25376 MEM' _17995)). Qed.
Lemma lem1102741 {_25376 : Type'} (MEM' : type1304 _25376) (_17995 : type1674) : (term116 _25376 MEM' _17995) = (term117 _25376 MEM' _17995).
Proof. exact (eq_refl (term116 _25376 MEM' _17995)). Qed.
Lemma lem1102742 {_25376 : Type'} (MEM' : type1304 _25376) (_17995 : type1674) : (term115 _25376 MEM' _17995) = (term117 _25376 MEM' _17995).
Proof. exact (TRANS (@lem1102740 _25376 MEM' _17995) (@lem1102741 _25376 MEM' _17995)). Qed.
Lemma lem1102743 {_25376 : Type'} (MEM' : type1304 _25376) : (term118 _25376 MEM') = (term119 _25376 MEM').
Proof. exact (fun_ext (fun _17995 : type1674 => @lem1102742 _25376 MEM' _17995)). Qed.
Lemma lem1102744 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem1102745 {_25376 : Type'} (MEM' : type1304 _25376) : (term120 _25376 MEM') = (term121 _25376 MEM').
Proof. exact (MK_COMB (@lem1102744) (@lem1102743 _25376 MEM')). Qed.
Lemma lem1102746 {_25376 : Type'} : (term122 _25376) = (term123 _25376).
Proof. exact (fun_ext (fun MEM' : type1304 _25376 => @lem1102745 _25376 MEM')). Qed.
Lemma lem1102747 {_25376 : Type'} : (@ex ((prod nat (prod nat nat)) -> _25376 -> (list _25376) -> Prop)) = (@ex ((prod nat (prod nat nat)) -> _25376 -> (list _25376) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> _25376 -> (list _25376) -> Prop))). Qed.
Lemma lem1102748 {_25376 : Type'} : (term104 _25376) = (term124 _25376).
Proof. exact (MK_COMB (@lem1102747 _25376) (@lem1102746 _25376)). Qed.
Lemma lem1102749 {_25376 : Type'} : ((term103 _25376) = (term104 _25376)) = ((term97 _25376) = (term124 _25376)).
Proof. exact (MK_COMB (@lem1102737 _25376) (@lem1102748 _25376)). Qed.
Lemma lem1102750 {_25376 : Type'} : (term97 _25376) = (term124 _25376).
Proof. exact (EQ_MP (@lem1102749 _25376) (@lem1102724 _25376)). Qed.
Lemma lem1102751 {_25376 : Type'} : term124 _25376.
Proof. exact (EQ_MP (@lem1102750 _25376) (@lem1102717 _25376)). Qed.
Lemma lem1102753 {A : Type'} : (@ex A) = (term125 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1102754 {_25376 : Type'} : (@ex ((prod nat (prod nat nat)) -> _25376 -> (list _25376) -> Prop)) = (term126 _25376).
Proof. exact (@lem1102753 (type1304 _25376)). Qed.
Lemma lem1102755 {_25376 : Type'} : (term123 _25376) = (term123 _25376).
Proof. exact (eq_refl (term123 _25376)). Qed.
Lemma lem1102756 {_25376 : Type'} : (term124 _25376) = (term127 _25376).
Proof. exact (MK_COMB (@lem1102754 _25376) (@lem1102755 _25376)). Qed.
Lemma lem1102757 {_25376 : Type'} : (term127 _25376) = (term128 _25376).
Proof. exact (eq_refl (term127 _25376)). Qed.
Lemma lem1102758 {_25376 : Type'} : (term124 _25376) = (term128 _25376).
Proof. exact (TRANS (@lem1102756 _25376) (@lem1102757 _25376)). Qed.
Lemma lem1102759 {_25376 : Type'} : term128 _25376.
Proof. exact (EQ_MP (@lem1102758 _25376) (@lem1102751 _25376)). Qed.
